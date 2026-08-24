/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProjectionTheory.code.UniformSet

open Finset Real

namespace UniformSet

/-- A real-valued set function `μ` is sub-additive if
`μ(A ∪ B) ≤ μ(A) + μ(B)` for all finite sets `A, B`. This is the
hypothesis used in the Uniformization Lemma (e.g. `μ(B) = |B|_δ`). -/
def IsSubAdditive {d : ℕ} (μ : Finset (Fin d → ℕ) → ℝ) : Prop :=
  ∀ A B : Finset (Fin d → ℕ), μ (A ∪ B) ≤ μ A + μ B

/-- A real-valued set function `μ` is monotone if `A ⊆ B` implies `μ A ≤ μ B`. -/
def IsMonotoneSetFn {d : ℕ} (μ : Finset (Fin d → ℕ) → ℝ) : Prop :=
  ∀ A B : Finset (Fin d → ℕ), A ⊆ B → μ A ≤ μ B

/-- `IsUniformFrom N m d k X` is the "partial" uniformity property used in the
inductive proof of the Uniformization Lemma: the set `X` is required to be
`(Δ, m)`-uniform only at scales `j ∈ {k, k+1, …, m-1}`. Taking `k = 0` recovers
the full `IsUniform` predicate; `k = m` is automatic. -/
def IsUniformFrom (N m d : ℕ) (k : ℕ) (X : Finset (Fin d → ℕ)) : Prop :=
  ∀ j : ℕ, k ≤ j → j < m →
    ∃ R : ℕ, ∀ Q : Fin d → ℕ,
      (X.filter (fun p => cubeOf N m j p = Q)).Nonempty →
      subcubeCovering N m j d X Q = R

/-- Full `(Δ, m)`-uniformity is the same as `IsUniformFrom` starting at scale `0`. -/
theorem isUniform_iff_uniformFrom_zero (N m d : ℕ) (X : Finset (Fin d → ℕ)) :
    IsUniform N m d X ↔ IsUniformFrom N m d 0 X :=
  ⟨fun h j _ hj => h j hj, fun h j hj => h j (Nat.zero_le _) hj⟩

/-- Every set is vacuously `IsUniformFrom` at the top scale `k = m`,
since there are no indices `j` satisfying `m ≤ j < m`. This is the base
case for the inductive proof of the Uniformization Lemma. -/
theorem isUniformFrom_m (N m d : ℕ) (X : Finset (Fin d → ℕ)) :
    IsUniformFrom N m d m X :=
  fun _ hj hj' => absurd (Nat.lt_of_lt_of_le hj' hj) (lt_irrefl _)


/-- Pigeon-hole bound: at any fixed scale `k`, the number of distinct
branching values `R_j` taken by the sub-cube counts across the cubes of `X`
is at most `2 d log(N)`. This is the loss factor that appears at each scale
in the Uniformization Lemma. -/
theorem dyadic_range_card_bound (N m d : ℕ) (hN : N ≥ 2) (hd : d ≥ 1)
    (k : ℕ) (hk : k < m)
    (X : Finset (Fin d → ℕ)) (hX : X.Nonempty) :
    ((X.image (fun p => subcubeCovering N m k d X (cubeOf N m k p))).card : ℝ) ≤
      2 * (d : ℝ) * Real.log (N : ℝ) := by sorry

/-- **One inductive step of the Uniformization Lemma.** If `X` is already
uniform at every scale `j ≥ k + 1`, then by pigeon-holing the branching
factor at scale `k` we can pass to a subset `Y ⊆ X` which is uniform from
scale `k` onward, while losing only a factor of `(2 d log N)⁻¹` in the
sub-additive measure `μ`. -/
theorem one_step_uniformization (N m d : ℕ) (hN : N ≥ 2) (hd : d ≥ 1)
    (k : ℕ) (hk : k < m)
    (X : Finset (Fin d → ℕ)) (hX : X.Nonempty)
    (hXunif : IsUniformFrom N m d (k + 1) X)
    (μ : Finset (Fin d → ℕ) → ℝ)
    (hμ_sub : IsSubAdditive μ)
    (hμ_mono : IsMonotoneSetFn μ)
    (hμ_nonneg : ∀ S : Finset (Fin d → ℕ), 0 ≤ μ S) :
    ∃ Y : Finset (Fin d → ℕ),
      Y ⊆ X ∧
      Y.Nonempty ∧
      IsUniformFrom N m d k Y ∧
      μ Y ≥ (2 * (d : ℝ) * Real.log (N : ℝ))⁻¹ * μ X := by
  classical
  let branchFn : (Fin d → ℕ) → ℕ := fun p => subcubeCovering N m k d X (cubeOf N m k p)
  let branchValues : Finset ℕ := X.image branchFn
  have hbv_ne : branchValues.Nonempty := Finset.Nonempty.image hX _
  obtain ⟨R₀, hR₀_mem, hR₀_max⟩ := Finset.exists_max_image branchValues
    (fun R => μ (X.filter (fun p => branchFn p = R))) hbv_ne
  refine ⟨X.filter (fun p => branchFn p = R₀), Finset.filter_subset _ X, ?_, ?_, ?_⟩

  · rw [Finset.mem_image] at hR₀_mem
    obtain ⟨p, hp, hpeq⟩ := hR₀_mem
    exact ⟨p, Finset.mem_filter.mpr ⟨hp, hpeq⟩⟩

  · intro j hj hjm
    by_cases hjk : j = k
    · subst hjk
      use R₀; intro Q hQ
      have hfilt_eq : (X.filter (fun p => branchFn p = R₀)).filter
          (fun p => cubeOf N m j p = Q) = X.filter (fun p => cubeOf N m j p = Q) := by
        ext p; simp only [Finset.mem_filter]; constructor
        · exact fun ⟨⟨hp, _⟩, hpQ⟩ => ⟨hp, hpQ⟩
        · intro ⟨hp, hpQ⟩
          obtain ⟨q, hq⟩ := hQ
          simp only [Finset.mem_filter] at hq
          refine ⟨⟨hp, ?_⟩, hpQ⟩
          show branchFn p = R₀
          have : branchFn q = R₀ := hq.1.2
          simp only [branchFn] at this ⊢
          rw [hpQ, ← hq.2]; exact this
      unfold subcubeCovering; rw [hfilt_eq]
      obtain ⟨q, hq⟩ := hQ
      simp only [Finset.mem_filter] at hq
      have := hq.1.2
      simp only [branchFn, subcubeCovering] at this
      rw [hq.2] at this; exact this
    · have hj_ge : k + 1 ≤ j := by omega
      obtain ⟨R', hR'⟩ := hXunif j hj_ge hjm
      use R'; intro Q hQ
      have hfilt_eq : (X.filter (fun p => branchFn p = R₀)).filter
          (fun p => cubeOf N m j p = Q) = X.filter (fun p => cubeOf N m j p = Q) := by
        ext p; simp only [Finset.mem_filter]; constructor
        · exact fun ⟨⟨hp, _⟩, hpQ⟩ => ⟨hp, hpQ⟩
        · intro ⟨hp, hpQ⟩
          obtain ⟨q, hq⟩ := hQ
          simp only [Finset.mem_filter] at hq
          refine ⟨⟨hp, ?_⟩, hpQ⟩
          show branchFn p = R₀
          have hq_branch : branchFn q = R₀ := hq.1.2
          simp only [branchFn]
          have hcube_k_eq : cubeOf N m k p = cubeOf N m k q := by
            ext i; simp only [cubeOf]
            have hpj := congr_fun hpQ i
            have hqj := congr_fun hq.2 i
            simp only [cubeOf] at hpj hqj
            have hmk_eq : N ^ (m - k) = N ^ (m - j) * N ^ (j - k) := by
              rw [← Nat.pow_add]; congr 1; omega
            rw [hmk_eq]
            simp only [← Nat.div_div_eq_div_mul]
            congr 1
            linarith
          simp only [branchFn] at hq_branch
          rw [hcube_k_eq]; exact hq_branch
      unfold subcubeCovering; rw [hfilt_eq]
      exact hR' Q (by obtain ⟨q, hq⟩ := hQ; simp only [Finset.mem_filter] at hq;
                      exact ⟨q, Finset.mem_filter.mpr ⟨hq.1.1, hq.2⟩⟩)

  · have hC_pos : (0 : ℝ) < 2 * (d : ℝ) * Real.log (N : ℝ) := by
      have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hN
      have : (0 : ℝ) < Real.log (N : ℝ) := Real.log_pos this
      have : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (by omega)
      positivity
    have hX_eq : X = branchValues.biUnion
        (fun R => X.filter (fun p => branchFn p = R)) := by
      ext p; simp only [branchValues, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_image]
      exact ⟨fun hp => ⟨_, ⟨p, hp, rfl⟩, hp, rfl⟩, fun ⟨_, _, hp, _⟩ => hp⟩
    have hμ_sum : μ X ≤ ∑ R ∈ branchValues, μ (X.filter (fun p => branchFn p = R)) := by
      conv_lhs => rw [hX_eq]
      refine Finset.Nonempty.cons_induction ?_ ?_ hbv_ne
      · intro a; simp
      · intro a t ha _ ih
        rw [Finset.cons_eq_insert, Finset.biUnion_insert, Finset.sum_insert ha]
        linarith [hμ_sub (X.filter (fun p => branchFn p = a))
          (t.biUnion fun R => X.filter (fun p => branchFn p = R)), ih]
    have hcard_μ : (branchValues.card : ℝ) *
        μ (X.filter (fun p => branchFn p = R₀)) ≥ μ X := by
      calc (branchValues.card : ℝ) * μ (X.filter (fun p => branchFn p = R₀))
          = ∑ _ ∈ branchValues, μ (X.filter (fun p => branchFn p = R₀)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≥ ∑ R ∈ branchValues, μ (X.filter (fun p => branchFn p = R)) :=
            Finset.sum_le_sum (fun R hR => hR₀_max R hR)
        _ ≥ μ X := hμ_sum
    have hbv_pos : (0 : ℝ) < (branchValues.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hbv_ne

    have hY_bound : μ (X.filter (fun p => branchFn p = R₀)) ≥
        μ X / (branchValues.card : ℝ) := by
      rw [ge_iff_le, div_le_iff₀ hbv_pos]
      linarith [hcard_μ]
    have hcard_le : (branchValues.card : ℝ) ≤ 2 * (d : ℝ) * Real.log (N : ℝ) :=
      dyadic_range_card_bound N m d hN hd k hk X hX

    calc μ (X.filter (fun p => branchFn p = R₀))
        ≥ μ X / (branchValues.card : ℝ) := hY_bound
      _ ≥ (2 * (d : ℝ) * Real.log (N : ℝ))⁻¹ * μ X := by
          rw [inv_mul_eq_div]
          exact div_le_div_of_nonneg_left (hμ_nonneg X) hbv_pos hcard_le

/-- **Uniformization Lemma (Bourgain).** Let `δ = Δ^m = N^{-m}`, let
`X ⊂ {0, …, N^m - 1}^d`, and let `μ` be any non-negative, monotone,
sub-additive set function with `μ ∅ = 0`. Then there is a subset
`Y ⊆ X` that is `(Δ, m)`-uniform and satisfies
$$\mu(Y) \ge \big[2 d \ln(1/\Delta)\big]^{-m} \, \mu(X)
       = \delta^{-\sigma}\, \mu(X),
\qquad \sigma = \frac{\ln(2 \ln(1/\Delta))}{\ln(1/\Delta)}.$$
The proof iterates `one_step_uniformization` for `m` scales,
losing the factor `(2 d log N)⁻¹` at each one. -/
theorem uniformization_lemma (N m d : ℕ) (hN : N ≥ 2) (hd : d ≥ 1) (hm : m ≥ 1)
    (X : Finset (Fin d → ℕ)) (hX : X.Nonempty)
    (μ : Finset (Fin d → ℕ) → ℝ)
    (hμ_sub : IsSubAdditive μ)
    (hμ_mono : IsMonotoneSetFn μ)
    (hμ_empty : μ ∅ = 0)
    (hμ_nonneg : ∀ S : Finset (Fin d → ℕ), 0 ≤ μ S) :
    ∃ Y : Finset (Fin d → ℕ),
      Y ⊆ X ∧
      Y.Nonempty ∧
      IsUniform N m d Y ∧
      μ Y ≥ (2 * (d : ℝ) * Real.log (N : ℝ))⁻¹ ^ m * μ X := by
  classical
  set C := (2 * (d : ℝ) * Real.log (N : ℝ))⁻¹ with hC_def
  have hC_pos : (0 : ℝ) < C := by
    rw [hC_def]; apply inv_pos.mpr
    have : (1 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hN
    have : (0 : ℝ) < Real.log (N : ℝ) := Real.log_pos this
    have : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hd)
    positivity

  suffices h : ∀ k : ℕ, k ≤ m →
      ∃ Z : Finset (Fin d → ℕ),
        Z ⊆ X ∧ Z.Nonempty ∧ IsUniformFrom N m d k Z ∧ μ Z ≥ C ^ (m - k) * μ X by
    obtain ⟨Y, hYX, hYne, hYunif, hYμ⟩ := h 0 (Nat.zero_le m)
    exact ⟨Y, hYX, hYne, (isUniform_iff_uniformFrom_zero N m d Y).mpr hYunif,
           by simpa using hYμ⟩

  intro k hk

  have key : ∀ n : ℕ, n ≤ m → ∃ Z : Finset (Fin d → ℕ),
      Z ⊆ X ∧ Z.Nonempty ∧ IsUniformFrom N m d (m - n) Z ∧ μ Z ≥ C ^ n * μ X := by
    intro n hn
    induction n with
    | zero =>
      exact ⟨X, Finset.Subset.refl X, hX, isUniformFrom_m N m d X, by simp⟩
    | succ n ih =>
      obtain ⟨Z, hZX, hZne, hZunif, hZμ⟩ := ih (Nat.le_of_succ_le hn)
      have hlt : m - (n + 1) < m := by omega
      have heq : m - (n + 1) + 1 = m - n := by omega
      have hZunif' : IsUniformFrom N m d (m - (n + 1) + 1) Z := by rwa [heq]
      obtain ⟨Y, hYZ, hYne, hYunif, hYμ⟩ :=
        one_step_uniformization N m d hN hd (m - (n + 1)) hlt Z hZne hZunif'
          μ hμ_sub hμ_mono hμ_nonneg
      refine ⟨Y, Finset.Subset.trans hYZ hZX, hYne, hYunif, ?_⟩
      calc μ Y ≥ C * μ Z := hYμ
        _ ≥ C * (C ^ n * μ X) := by
            apply mul_le_mul_of_nonneg_left hZμ (le_of_lt hC_pos)
        _ = C ^ (n + 1) * μ X := by ring
  have hkey := key (m - k) (by omega)
  have hmk : m - (m - k) = k := by omega
  rw [hmk] at hkey
  exact hkey

end UniformSet
