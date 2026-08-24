/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open Finset NNReal ENNReal

namespace SpaceFillingCurve

/-- The unit square $[0,1]^2 \subseteq \mathbb{R}^2$. -/
def unitSquare : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | ∀ j : Fin 2, p j ∈ Set.Icc (0 : ℝ) 1}

/-- Cyclic successor on `Fin n`: $i \mapsto (i + 1) \bmod n$. -/
def cyclicSucc {n : ℕ} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩

/-- Existence of a Hilbert-curve-like surjection from $[0,1]$ to the unit square with the
dyadic distance bound $\mathrm{dist}(x, y) \le 2 \cdot 4^{-n} \Rightarrow
\mathrm{dist}(H(x), H(y)) \le C \cdot 2^{-n}$. -/
theorem hilbertCurve_dyadic_property :
  ∃ (H : Set.Icc (0:ℝ) 1 → EuclideanSpace ℝ (Fin 2)) (C_diad : ℝ),
    C_diad > 0 ∧
    (∀ p ∈ unitSquare, ∃ t : Set.Icc (0:ℝ) 1, H t = p) ∧
    (∀ (x y : Set.Icc (0:ℝ) 1) (n : ℕ),
      dist (x : ℝ) (y : ℝ) ≤ 2 * (4:ℝ)⁻¹ ^ n →
      dist (H x) (H y) ≤ C_diad * (2:ℝ)⁻¹ ^ n) := by sorry

/-- The Hilbert curve $H : [0,1] \to [0,1]^2$ extracted from `hilbertCurve_dyadic_property`. -/
def hilbertCurve : Set.Icc (0:ℝ) 1 → EuclideanSpace ℝ (Fin 2) :=
  hilbertCurve_dyadic_property.choose

/-- The dyadic constant $C$ extracted from `hilbertCurve_dyadic_property`. -/
def C_diad : ℝ := hilbertCurve_dyadic_property.choose_spec.choose

/-- The dyadic constant $C$ is strictly positive. -/
lemma C_diad_pos : C_diad > 0 :=
  hilbertCurve_dyadic_property.choose_spec.choose_spec.1

/-- The Hilbert curve is surjective onto the unit square. -/
theorem hilbertCurve_surjective :
    ∀ p ∈ unitSquare, ∃ t : Set.Icc (0:ℝ) 1, hilbertCurve t = p :=
  hilbertCurve_dyadic_property.choose_spec.choose_spec.2.1

/-- Dyadic bound for the Hilbert curve: if $|x - y| \le 2 \cdot 4^{-n}$, then
$\mathrm{dist}(H(x), H(y)) \le C \cdot 2^{-n}$. -/
theorem hilbertCurve_dyadic_bound (x y : Set.Icc (0:ℝ) 1) (n : ℕ)
    (h : dist (x : ℝ) (y : ℝ) ≤ 2 * (4:ℝ)⁻¹ ^ n) :
    dist (hilbertCurve x) (hilbertCurve y) ≤ C_diad * (2:ℝ)⁻¹ ^ n :=
  hilbertCurve_dyadic_property.choose_spec.choose_spec.2.2 x y n h

/-- A distance bound $\mathrm{dist}(f(x), f(y)) \le C \cdot \mathrm{dist}(x, y)^r$ on a
pseudometric space upgrades to the mathlib `HolderWith` predicate. -/
lemma holderWith_of_dist_bound {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (C : ℝ≥0) (r : ℝ≥0) (f : X → Y)
    (h : ∀ x y, dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (r : ℝ)) :
    HolderWith C r f := by
  intro x y
  rw [edist_nndist, edist_nndist,
      ← ENNReal.coe_rpow_of_nonneg _ (NNReal.coe_nonneg r), ← ENNReal.coe_mul]
  exact ENNReal.coe_le_coe.mpr
    (by rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_rpow, coe_nndist, coe_nndist]
        exact h x y)

/-- Hölder-$1/2$ distance bound for the Hilbert curve:
$\mathrm{dist}(H(x), H(y)) \le 2 C \cdot |x - y|^{1/2}$. -/
theorem hilbertCurve_dist_holder (x y : Set.Icc (0:ℝ) 1) :
    dist (hilbertCurve x) (hilbertCurve y) ≤
      2 * C_diad * dist (x : ℝ) (y : ℝ) ^ ((1:ℝ)/2) := by
  by_cases hxy : (x : ℝ) = (y : ℝ)
  · have hxy' : x = y := Subtype.ext hxy
    subst hxy'
    simp [dist_self]
  · have hd_pos : 0 < dist (x : ℝ) (y : ℝ) := by rw [dist_pos]; exact hxy
    have hd_le : dist (x : ℝ) (y : ℝ) ≤ 1 := by
      rw [Real.dist_eq]
      exact abs_sub_le_iff.mpr ⟨by linarith [x.prop.2, y.prop.1],
                                  by linarith [y.prop.2, x.prop.1]⟩
    set d := dist (x : ℝ) (y : ℝ)

    have h_tend : ∃ N : ℕ, (4:ℝ)⁻¹ ^ N < d :=
      exists_pow_lt_of_lt_one hd_pos (by norm_num : (4:ℝ)⁻¹ < 1)
    set n₀ := Nat.find h_tend
    have hn₀_spec : (4:ℝ)⁻¹ ^ n₀ < d := Nat.find_spec h_tend
    have hn₀_ne : n₀ ≠ 0 := by intro h; simp [h] at hn₀_spec; linarith
    have h_prev : ¬ (4:ℝ)⁻¹ ^ (n₀ - 1) < d := Nat.find_min h_tend (by omega)
    simp only [not_lt] at h_prev
    set n := n₀ - 1

    have hd_upper : d ≤ 2 * (4:ℝ)⁻¹ ^ n := by
      linarith [show (0:ℝ) < (4:ℝ)⁻¹ ^ n from by positivity]

    have h4n_lower : (4:ℝ)⁻¹ ^ n < 4 * d := by
      have h_split : (4:ℝ)⁻¹ ^ n₀ = (4:ℝ)⁻¹ * (4:ℝ)⁻¹ ^ n := by
        show (4:ℝ)⁻¹ ^ n₀ = (4:ℝ)⁻¹ * (4:ℝ)⁻¹ ^ (n₀ - 1)
        conv_lhs => rw [show n₀ = (n₀ - 1) + 1 from by omega, pow_succ, mul_comm]
      linarith

    have h_bound := hilbertCurve_dyadic_bound x y n hd_upper

    have h2n_pos : (0:ℝ) < (2:ℝ)⁻¹ ^ n := by positivity
    have h4_eq : (4:ℝ)⁻¹ ^ n = ((2:ℝ)⁻¹ ^ n) ^ 2 := by
      have : (4:ℝ)⁻¹ ^ n = ((2:ℝ)⁻¹ ^ 2) ^ n := by norm_num
      rw [this, ← pow_mul, mul_comm, pow_mul]
    have h_sq : ((2:ℝ)⁻¹ ^ n) ^ 2 < 4 * d := by rw [← h4_eq]; exact h4n_lower
    have h_sqrt_bound : (2:ℝ)⁻¹ ^ n ≤ 2 * d ^ ((1:ℝ)/2) := by
      rw [← Real.sqrt_eq_rpow]
      have h1 : (2:ℝ)⁻¹ ^ n ≤ Real.sqrt (4 * d) := by
        rw [← Real.sqrt_sq h2n_pos.le]; exact Real.sqrt_le_sqrt h_sq.le
      have h2 : Real.sqrt (4 * d) = 2 * Real.sqrt d := by
        rw [show (4:ℝ) * d = 2^2 * d from by ring, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2^2)]
        simp [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
      linarith

    calc dist (hilbertCurve x) (hilbertCurve y)
        ≤ C_diad * (2:ℝ)⁻¹ ^ n := h_bound
      _ ≤ C_diad * (2 * d ^ ((1:ℝ)/2)) := by
          apply mul_le_mul_of_nonneg_left h_sqrt_bound (le_of_lt C_diad_pos)
      _ = 2 * C_diad * d ^ ((1:ℝ)/2) := by ring

/-- Theorem 9.6.7 (Hilbert curve is Hölder-$1/2$). The Hilbert curve $H : [0,1] \to [0,1]^2$
is Hölder continuous of exponent $1/2$. -/
theorem hilbert_curve_holder_half :
    ∃ C : ℝ≥0, HolderWith C (2⁻¹ : ℝ≥0) hilbertCurve := by
  refine ⟨⟨2 * C_diad, by linarith [C_diad_pos]⟩, ?_⟩
  apply holderWith_of_dist_bound
  intro x y
  simp only [NNReal.coe_mk]
  have : ((2⁻¹ : ℝ≥0) : ℝ) = (1:ℝ)/2 := by norm_num
  rw [this]
  exact hilbertCurve_dist_holder x y

/-- Existence of a Hilbert-curve-like map: a surjection from $[0,1]$ onto the unit square
that is Hölder continuous of exponent $1/2$. -/
theorem hilbert_curve_exists :
    ∃ (H : Set.Icc (0:ℝ) 1 → EuclideanSpace ℝ (Fin 2)) (C : ℝ≥0),
      (∀ p ∈ unitSquare, ∃ t : Set.Icc (0:ℝ) 1, H t = p) ∧
      HolderWith C (2⁻¹ : ℝ≥0) H := by
  obtain ⟨C, hC⟩ := hilbert_curve_holder_half
  exact ⟨hilbertCurve, C, hilbertCurve_surjective, hC⟩

/-- Squaring the Hölder-$1/2$ bound: $\mathrm{dist}(f(x), f(y))^2 \le C^2 \mathrm{dist}(x, y)$. -/
lemma holder_half_sq_bound {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {C : ℝ≥0} {f : X → Y} (hf : HolderWith C (2⁻¹ : ℝ≥0) f) (x y : X) :
    dist (f x) (f y) ^ 2 ≤ (C : ℝ) ^ 2 * dist x y := by
  have h := hf.dist_le x y
  have hr : ((2⁻¹ : ℝ≥0) : ℝ) = (1/2 : ℝ) := by norm_num
  rw [hr] at h
  have hdist : (0 : ℝ) ≤ dist x y := dist_nonneg
  calc dist (f x) (f y) ^ 2
      ≤ (↑C * dist x y ^ (1/2 : ℝ)) ^ 2 := by
        apply sq_le_sq'
        · linarith [dist_nonneg (α := Y) (x := f x) (y := f y)]
        · exact h
    _ = C ^ 2 * (dist x y ^ (1/2 : ℝ)) ^ 2 := by ring
    _ = C ^ 2 * dist x y ^ (2 * (1/2 : ℝ)) := by
        rw [← Real.rpow_natCast (dist x y ^ (1/2 : ℝ)) 2, ← Real.rpow_mul hdist]; norm_num
    _ = C ^ 2 * dist x y := by norm_num

/-- Telescoping sum over `Fin m`:
$\sum_{i=0}^{m-1} (f(i+1) - f(i)) = f(m) - f(0)$. -/
lemma fin_telescoping_sum (m : ℕ) (f : Fin (m + 1) → ℝ) :
    ∑ i : Fin m, (f ⟨i.val + 1, by omega⟩ - f ⟨i.val, by omega⟩) =
    f ⟨m, by omega⟩ - f ⟨0, by omega⟩ := by
  set g : ℕ → ℝ := fun k => if h : k < m + 1 then f ⟨k, h⟩ else 0
  have hg : ∀ k (hk : k < m + 1), g k = f ⟨k, hk⟩ := fun k hk => dif_pos hk
  have hsum : ∑ i : Fin m, (f ⟨i.val + 1, by omega⟩ - f ⟨i.val, by omega⟩) =
    ∑ i : Fin m, (g (↑i + 1) - g ↑i) := by
    congr 1; ext i; rw [hg (↑i + 1) (by omega), hg ↑i (by omega)]
  rw [hsum, Fin.sum_univ_eq_sum_range (fun k => g (k + 1) - g k) m,
      Finset.sum_range_sub g m, hg m (by omega), hg 0 (by omega)]

/-- For a monotone sequence valued in $[0,1]$, the total cyclic variation
$\sum_i |f(i) - f(i+1 \bmod n)|$ is at most $2$. -/
lemma monotone_cyclic_sum_le_two {n : ℕ} (f : Fin n → ℝ)
    (hf_mono : Monotone f) (hf_lo : ∀ i, 0 ≤ f i) (hf_hi : ∀ i, f i ≤ 1) :
    ∑ i : Fin n, |f i - f ⟨(i.val + 1) % n, Nat.mod_lt _ (Fin.pos i)⟩| ≤ 2 := by
  rcases n with _ | m
  · simp
  suffices h : ∑ i : Fin (m + 1),
      |f i - f ⟨(i.val + 1) % (m + 1), Nat.mod_lt _ (by omega)⟩| =
      2 * (f ⟨m, by omega⟩ - f ⟨0, by omega⟩) by
    rw [h]; linarith [hf_hi ⟨m, by omega⟩, hf_lo ⟨0, by omega⟩]
  have h_abs : ∀ i : Fin (m + 1),
      |f i - f ⟨(i.val + 1) % (m + 1), Nat.mod_lt _ (by omega)⟩| =
      if h : i.val < m then f ⟨i.val + 1, by omega⟩ - f i
      else f ⟨m, by omega⟩ - f ⟨0, by omega⟩ := by
    intro i; split_ifs with hi
    · have heq : (⟨(i.val + 1) % (m + 1), Nat.mod_lt _ (by omega)⟩ : Fin (m + 1)) =
          ⟨i.val + 1, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
      rw [heq, abs_sub_comm, abs_of_nonneg]
      linarith [hf_mono (show i ≤ (⟨i.val + 1, by omega⟩ : Fin (m + 1)) from
        Fin.mk_le_mk.mpr (by omega))]
    · have him : i.val = m := by omega
      rw [show (⟨(i.val + 1) % (m + 1), _⟩ : Fin (m + 1)) = ⟨0, by omega⟩ from
        Fin.ext (by simp [him]),
        show f i = f ⟨m, by omega⟩ from congr_arg f (Fin.ext him), abs_of_nonneg]
      linarith [hf_mono (show (⟨0, by omega⟩ : Fin (m + 1)) ≤ ⟨m, by omega⟩ from
        Fin.mk_le_mk.mpr (by omega))]
  simp_rw [h_abs]; rw [Fin.sum_univ_castSucc]
  have h_last : (if h : (Fin.last m).val < m then
      f ⟨(Fin.last m).val + 1, by omega⟩ - f (Fin.last m)
      else f ⟨m, by omega⟩ - f ⟨0, by omega⟩) = f ⟨m, by omega⟩ - f ⟨0, by omega⟩ := by
    simp [Fin.last]
  rw [h_last]
  have h_int : ∀ i : Fin m,
      (if h : (Fin.castSucc i).val < m then
        f ⟨(Fin.castSucc i).val + 1, by omega⟩ - f (Fin.castSucc i)
      else f ⟨m, by omega⟩ - f ⟨0, by omega⟩) =
      f ⟨i.val + 1, by omega⟩ - f ⟨i.val, by omega⟩ := by
    intro i; split_ifs with hi
    · simp only [Fin.val_castSucc] at hi ⊢; rfl
    · exfalso; exact hi i.isLt
  simp_rw [h_int]; linarith [fin_telescoping_sum m f]

/-- Lemma 9.6.9 (space-filling curve heuristic for TSP). There exists an absolute constant
$C$ such that for any $n$ points in the unit square one can find a Hamilton cycle (i.e. a
permutation $\sigma$) with
$\sum_{i=1}^{n} \| x_{\sigma(i)} - x_{\sigma(i+1)} \|^2 \le C$. -/
theorem space_filling_curve_heuristic :
    ∃ (C : ℝ), ∀ (n : ℕ) (x : Fin n → EuclideanSpace ℝ (Fin 2)),
      (∀ i, x i ∈ unitSquare) →
      ∃ σ : Equiv.Perm (Fin n),
        ∑ i : Fin n, ‖x (σ i) - x (σ (cyclicSucc i))‖ ^ 2 ≤ C := by
  obtain ⟨H, CH, hH_surj, hH_holder⟩ := hilbert_curve_exists
  refine ⟨2 * (CH : ℝ) ^ 2, fun n x hx => ?_⟩
  choose t ht using fun i => hH_surj (x i) (hx i)
  set f : Fin n → ℝ := fun i => (t i).val
  set σ := Tuple.sort f
  refine ⟨σ, ?_⟩
  have hσ_mono : Monotone (f ∘ ⇑σ) := Tuple.monotone_sort f
  have hx_eq : ∀ i : Fin n, x (σ i) = H (t (σ i)) := fun i => (ht (σ i)).symm
  simp_rw [hx_eq]
  calc ∑ i : Fin n, ‖H (t (σ i)) - H (t (σ (cyclicSucc i)))‖ ^ 2
      = ∑ i : Fin n, dist (H (t (σ i))) (H (t (σ (cyclicSucc i)))) ^ 2 := by
        simp_rw [dist_eq_norm]
      _ ≤ ∑ i : Fin n, ((CH : ℝ) ^ 2 * dist (t (σ i)) (t (σ (cyclicSucc i)))) := by
        apply Finset.sum_le_sum; intro i _
        exact holder_half_sq_bound hH_holder _ _
      _ = (CH : ℝ) ^ 2 * ∑ i : Fin n, dist (t (σ i)) (t (σ (cyclicSucc i))) := by
        rw [← Finset.mul_sum]
      _ ≤ (CH : ℝ) ^ 2 * 2 := by
        apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
        simp_rw [Subtype.dist_eq, Real.dist_eq, cyclicSucc]
        exact monotone_cyclic_sum_le_two (f ∘ ⇑σ) hσ_mono
          (fun i => (t (σ i)).prop.1) (fun i => (t (σ i)).prop.2)
      _ = 2 * (CH : ℝ) ^ 2 := by ring

end SpaceFillingCurve
