/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.FourierInversion
import Atlas.DifferentialAnalysis.code.TemperedDistributions

open scoped SchwartzMap FourierTransform
open SobolevSpace TemperedDistributions TestFunctions MeasureTheory

noncomputable section

namespace SobolevSpace

variable (n : ℕ)

/-- The order `|α| = ∑ α i` of a multi-index `α : Fin n → ℕ`. -/
def multiIndexOrder (α : Fin n → ℕ) : ℕ := ∑ i, α i

/-- Iterated distributional partial derivative in the `i`-th coordinate, applied `k` times. -/
def iteratedPartialDerivDistrib (i : Fin n) (k : ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (fun v => distribDerivCLM (F := ℂ) (EuclideanSpace.single i (1 : ℝ)) v)^[k] u

/-- The multi-index distributional derivative `D^α u`, applied coordinate by coordinate. -/
def iteratedDistribDeriv (α : Fin n → ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (List.finRange n).foldr (fun i acc => iteratedPartialDerivDistrib n i (α i) acc) u

/-- Characterization of `H^m` (for integer `m ≥ 0`): every multi-index derivative `D^α u` with `|α| ≤ m` lies in `L²`. -/
def AllDerivMemL2 (m : ℕ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∀ (α : Fin n → ℕ), multiIndexOrder n α ≤ m → MemHs n 0 (iteratedDistribDeriv n α u)

/-- The iterated coordinate distributional derivative agrees with `FourierInversion.iterDistribDerivCoord`. -/
lemma iteratedPartialDerivDistrib_eq {n : ℕ} (i : Fin n) (k : ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    iteratedPartialDerivDistrib n i k u =
      FourierInversion.iterDistribDerivCoord i k u := by
  simp only [iteratedPartialDerivDistrib, FourierInversion.iterDistribDerivCoord,
    distribDerivCLM, LineDeriv.lineDerivOpCLM_apply]

/-- The multi-index distributional derivative agrees with `FourierInversion.iterDistribDeriv`. -/
lemma iteratedDistribDeriv_eq {n : ℕ} (α : Fin n → ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    iteratedDistribDeriv n α u = FourierInversion.iterDistribDeriv α u := by
  unfold iteratedDistribDeriv FourierInversion.iterDistribDeriv
  induction (List.finRange n) generalizing u with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldr_cons]
    rw [iteratedPartialDerivDistrib_eq]; exact congrArg _ (ih _)


/-- The absolute value of `⟨ξ, e_j⟩` is bounded by `⟨ξ⟩ = sqrt(1 + ‖ξ‖²)`. -/
lemma abs_inner_single_le_japaneseBracket {n : ℕ} (j : Fin n)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    |@inner ℝ _ _ ξ (EuclideanSpace.single j (1 : ℝ))| ≤ japaneseBracket n ξ := by
  have : |@inner ℝ _ _ ξ (EuclideanSpace.single j (1 : ℝ))| ≤ ‖ξ‖ := by
    calc |@inner ℝ _ _ ξ (EuclideanSpace.single j (1 : ℝ))|
        ≤ ‖ξ‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ := abs_real_inner_le_norm _ _
      _ = ‖ξ‖ := by rw [PiLp.norm_single, norm_one, mul_one]
  calc |@inner ℝ _ _ ξ (EuclideanSpace.single j (1 : ℝ))|
      ≤ ‖ξ‖ := this
    _ ≤ Real.sqrt (1 + ‖ξ‖ ^ 2) := by
        rw [Real.le_sqrt (norm_nonneg _) (by positivity)]
        nlinarith [sq_nonneg ‖ξ‖]
    _ = japaneseBracket n ξ := rfl


/-- The complex norm of `2π i` equals `2π`. -/
lemma norm_two_pi_I : ‖(2 * ↑Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
  rw [show (2 : ℂ) * ↑Real.pi * Complex.I = ↑(2 * Real.pi) * Complex.I by push_cast; ring]
  rw [Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
      Real.norm_of_nonneg (by positivity)]

set_option maxHeartbeats 400000 in
/-- Differentiation lowers Sobolev regularity by one: if `u ∈ H^s`, then `∂_j u ∈ H^{s-1}`. -/
theorem memHs_distribDeriv {n : ℕ} {s : ℝ} (j : Fin n)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (hu : MemHs n s u) :
    MemHs n (s - 1) (distribDerivCLM (F := ℂ) (EuclideanSpace.single j (1 : ℝ)) u) := by
  obtain ⟨g, hg_mem, hg_eq⟩ := hu
  set ej := EuclideanSpace.single j (1 : ℝ)

  set m : EuclideanSpace ℝ (Fin n) → ℂ := fun ξ =>
    (2 * ↑Real.pi * Complex.I) * ↑(@inner ℝ _ _ ξ ej) *
    (↑(japaneseBracket n ξ))⁻¹
  refine ⟨fun ξ => m ξ * g ξ, ?_, ?_⟩
  ·
    have hm_bound : ∀ ξ : EuclideanSpace ℝ (Fin n), ‖m ξ‖ ≤ 2 * Real.pi := by
      intro ξ
      show ‖(2 * ↑Real.pi * Complex.I) * ↑(@inner ℝ _ _ ξ ej) *
        (↑(japaneseBracket n ξ))⁻¹‖ ≤ 2 * Real.pi
      have hjb_pos := japaneseBracket_pos n ξ
      have h_inner_le := abs_inner_single_le_japaneseBracket j ξ
      rw [norm_mul, norm_mul, norm_two_pi_I,
          Complex.norm_real, Real.norm_eq_abs,
          norm_inv, Complex.norm_real, Real.norm_of_nonneg hjb_pos.le]
      calc (2 * Real.pi) * |@inner ℝ _ _ ξ ej| * (japaneseBracket n ξ)⁻¹
          ≤ (2 * Real.pi) * japaneseBracket n ξ * (japaneseBracket n ξ)⁻¹ := by gcongr
        _ = 2 * Real.pi := by rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hjb_pos)]; ring
    have hle : ∀ ξ : EuclideanSpace ℝ (Fin n),
        ‖m ξ * g ξ‖ ≤ (2 * Real.pi) * ‖g ξ‖ := by
      intro ξ; rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hm_bound ξ) (norm_nonneg _)
    have hm_cont : Continuous m := by
      show Continuous (fun ξ => (2 * ↑Real.pi * Complex.I) * ↑(@inner ℝ _ _ ξ ej) *
        (↑(japaneseBracket n ξ))⁻¹)
      refine Continuous.mul (Continuous.mul continuous_const ?_) ?_
      · exact Complex.continuous_ofReal.comp (Continuous.inner continuous_id continuous_const)
      · refine Continuous.inv₀ (Complex.continuous_ofReal.comp ?_) ?_
        · show Continuous (japaneseBracket n)
          unfold japaneseBracket; fun_prop
        · intro ξ; exact Complex.ofReal_ne_zero.mpr (japaneseBracket_ne_zero n ξ)
    exact hg_mem.of_le_mul
      (hm_cont.aestronglyMeasurable.mul hg_mem.1)
      (Filter.Eventually.of_forall hle)
  ·
    intro φ


    have heval : (𝓕 (distribDerivCLM (F := ℂ) ej u)) φ =
        (2 * ↑Real.pi * Complex.I) *
        ((𝓕 u) (SchwartzMap.smulLeftCLM ℂ (fun ξ => (↑(@inner ℝ _ _ ξ ej) : ℂ)) φ)) := by
      change (𝓕 (LineDeriv.lineDerivOpCLM ℂ _ ej u)) φ = _
      rw [show (LineDeriv.lineDerivOpCLM ℂ (𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) ej u) =
        LineDeriv.lineDerivOp ej u from rfl]
      have := TemperedDistribution.fourier_lineDerivOp_eq u ej
      rw [this]; rfl
    rw [heval, hg_eq]


    dsimp only []

    simp_rw [← smul_eq_mul (a := (2 * ↑Real.pi * Complex.I)), ← integral_smul]
    congr 1; ext ξ; simp only [smul_eq_mul]


    have htemp : Function.HasTemperateGrowth (fun ξ : EuclideanSpace ℝ (Fin n) =>
        (↑(@inner ℝ _ _ ξ ej) : ℂ)) :=
      (Complex.ofRealCLM.comp ((innerSL ℝ).flip ej)).hasTemperateGrowth
    rw [SchwartzMap.smulLeftCLM_apply_apply htemp]; simp only [smul_eq_mul]
    have hjb_pos := japaneseBracket_pos n ξ
    have hjb_ne : (japaneseBracket n ξ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hjb_pos)
    simp only [sobolevWeight]

    have hws : ((japaneseBracket n ξ ^ (s - 1) : ℝ) : ℂ)⁻¹ *
        ((japaneseBracket n ξ : ℝ) : ℂ)⁻¹ =
        ((japaneseBracket n ξ ^ s : ℝ) : ℂ)⁻¹ := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
          ← Complex.ofReal_inv]
      congr 1
      rw [← Real.rpow_neg hjb_pos.le, ← Real.rpow_neg hjb_pos.le,
          show (japaneseBracket n ξ)⁻¹ = japaneseBracket n ξ ^ ((-1 : ℝ)) from
            (Real.rpow_neg_one (japaneseBracket n ξ)).symm,
          ← Real.rpow_add hjb_pos]
      congr 1; linarith

    rw [← hws]; ring

/-- Iterated coordinate differentiation lowers Sobolev regularity by `k`: `H^s → H^{s-k}` for `∂_j^k`. -/
lemma memHs_iteratedPartialDeriv {n : ℕ} {s : ℝ} (j : Fin n) (k : ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (hu : MemHs n s u) :
    MemHs n (s - ↑k) (iteratedPartialDerivDistrib n j k u) := by
  induction k with
  | zero =>
    simp only [iteratedPartialDerivDistrib, Function.iterate_zero, id_eq,
      Nat.cast_zero, sub_zero]
    exact hu
  | succ k ih =>
    simp only [iteratedPartialDerivDistrib, Function.iterate_succ', Function.comp]
    have h := memHs_distribDeriv j _ ih
    convert h using 1
    push_cast; ring

/-- Sobolev regularity loss for a fold over a list of coordinates: lowering by the sum of orders along the list. -/
lemma memHs_foldr_iteratedPartialDeriv {n : ℕ} {s : ℝ}
    (l : List (Fin n)) (α : Fin n → ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (hu : MemHs n s u) :
    MemHs n (s - ↑(l.map (fun j => α j)).sum)
      (l.foldr (fun j acc => iteratedPartialDerivDistrib n j (α j) acc) u) := by
  induction l with
  | nil =>
    simp only [List.foldr_nil, List.map_nil, List.sum_nil, Nat.cast_zero, sub_zero]
    exact hu
  | cons j l ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    have hstep := memHs_iteratedPartialDeriv j (α j) _ ih
    convert hstep using 1
    push_cast; ring

/-- Melrose Proposition 10.2: `D^α : H^s → H^{s - |α|}`. -/
lemma memHs_iteratedDistribDeriv {n : ℕ} {s : ℝ} (α : Fin n → ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (hu : MemHs n s u) :
    MemHs n (s - ↑(multiIndexOrder n α)) (iteratedDistribDeriv n α u) := by
  unfold iteratedDistribDeriv multiIndexOrder
  exact memHs_foldr_iteratedPartialDeriv (List.finRange n) α u hu

/-- The zero multi-index derivative `D^0` is the identity. -/
lemma iteratedDistribDeriv_zero {n : ℕ}
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    iteratedDistribDeriv n (fun _ : Fin n => 0) u = u := by
  unfold iteratedDistribDeriv
  induction (List.finRange n) with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldr_cons, iteratedPartialDerivDistrib, Function.iterate_zero, id_eq]
    exact ih

/-- Demotion: if all derivatives up to order `m + 1` lie in `L^2`, then so do all derivatives up to order `m`. -/
lemma allDerivMemL2_of_succ {n : ℕ} {m : ℕ}
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (hu : AllDerivMemL2 n (m + 1) u) :
    AllDerivMemL2 n m u :=
  fun α hα => hu α (Nat.le_succ_of_le hα)

/-- Distributional partial derivatives in different directions commute. -/
lemma distribDeriv_comm {n : ℕ} (v w : EuclideanSpace ℝ (Fin n))
    (T : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    distribDerivCLM (F := ℂ) v (distribDerivCLM (F := ℂ) w T) =
    distribDerivCLM (F := ℂ) w (distribDerivCLM (F := ℂ) v T) := by
  ext φ
  simp only [distribDerivCLM_apply, map_neg, neg_neg]
  congr 1
  exact (SchwartzRepresentation.schwartz_lineDerivOp_comm v w φ).symm

/-- The iterated partial derivative in coordinate `i` commutes with `∂_j`. -/
lemma iteratedPartialDerivDistrib_distribDeriv_comm {n : ℕ} (i : Fin n) (k : ℕ)
    (j : Fin n) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    iteratedPartialDerivDistrib n i k
      (distribDerivCLM (F := ℂ) (EuclideanSpace.single j 1) u) =
    distribDerivCLM (F := ℂ) (EuclideanSpace.single j 1)
      (iteratedPartialDerivDistrib n i k u) := by
  induction k generalizing u with
  | zero => simp [iteratedPartialDerivDistrib]
  | succ k ih =>
    simp only [iteratedPartialDerivDistrib, Function.iterate_succ, Function.comp_apply]
    rw [distribDeriv_comm (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) u]
    exact ih (distribDerivCLM (F := ℂ) (EuclideanSpace.single i 1) u)

/-- A foldr of iterated partial derivatives commutes with an additional `∂_j`. -/
lemma foldr_iterPartialDeriv_distribDeriv_comm {n : ℕ} (l : List (Fin n))
    (α : Fin n → ℕ) (j : Fin n) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    l.foldr (fun i acc => iteratedPartialDerivDistrib n i (α i) acc)
      (distribDerivCLM (F := ℂ) (EuclideanSpace.single j 1) u) =
    distribDerivCLM (F := ℂ) (EuclideanSpace.single j 1)
      (l.foldr (fun i acc => iteratedPartialDerivDistrib n i (α i) acc) u) := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact iteratedPartialDerivDistrib_distribDeriv_comm i (α i) j _

/-- If `j` does not appear in `l`, updating `α` at `j` does not affect the fold over `l`. -/
lemma foldr_update_eq {n : ℕ} (l : List (Fin n)) (α : Fin n → ℕ)
    (j : Fin n) (hj : j ∉ l) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    l.foldr (fun k acc => iteratedPartialDerivDistrib n k
          (Function.update α j (α j + 1) k) acc) u =
    l.foldr (fun k acc => iteratedPartialDerivDistrib n k (α k) acc) u := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons]
    have hne : i ≠ j := fun h => hj (h ▸ .head l)
    rw [Function.update_of_ne hne, ih (fun hm => hj (List.mem_cons_of_mem i hm))]

/-- Applying `D^α` after one further `∂_j` equals applying `D^{α with α_j ↦ α_j + 1}`. -/
lemma iteratedDistribDeriv_distribDeriv {n : ℕ} (α : Fin n → ℕ) (j : Fin n)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    iteratedDistribDeriv n α
      (distribDerivCLM (F := ℂ) (EuclideanSpace.single j 1) u) =
    iteratedDistribDeriv n (Function.update α j (α j + 1)) u := by
  unfold iteratedDistribDeriv
  rw [foldr_iterPartialDeriv_distribDeriv_comm]
  suffices h : ∀ (l : List (Fin n)), l.Nodup → j ∈ l →
      distribDerivCLM (F := ℂ) (EuclideanSpace.single j 1)
        (l.foldr (fun i acc => iteratedPartialDerivDistrib n i (α i) acc) u) =
      l.foldr (fun i acc => iteratedPartialDerivDistrib n i
        (Function.update α j (α j + 1) i) acc) u by
    exact h _ (List.nodup_finRange n) (List.mem_finRange j)
  intro l hnd hmem
  induction l with
  | nil => simp at hmem
  | cons i l ih =>
    simp only [List.foldr_cons]
    obtain ⟨hni, hndl⟩ := List.nodup_cons.mp hnd
    by_cases hij : i = j
    · subst hij
      simp only [Function.update_self]
      rw [foldr_update_eq l α i hni]


      show distribDerivCLM (F := ℂ) (EuclideanSpace.single i 1)
        (iteratedPartialDerivDistrib n i (α i) _) = iteratedPartialDerivDistrib n i (α i + 1) _
      simp only [iteratedPartialDerivDistrib, Function.iterate_succ', Function.comp_apply]
    · have hmem_l : j ∈ l := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h.symm hij
        · exact h
      rw [(iteratedPartialDerivDistrib_distribDeriv_comm i (α i) j _).symm,
          Function.update_of_ne hij]
      congr 1
      exact ih hndl hmem_l

/-- Incrementing `α j` increases the multi-index order by exactly one. -/
lemma multiIndexOrder_update {n : ℕ} (α : Fin n → ℕ) (j : Fin n) :
    multiIndexOrder n (Function.update α j (α j + 1)) = multiIndexOrder n α + 1 := by
  simp only [multiIndexOrder]
  have hne : ∀ i, i ≠ j → Function.update α j (α j + 1) i = α i :=
    fun i hi => Function.update_of_ne hi _ _
  calc ∑ i, Function.update α j (α j + 1) i
      = Function.update α j (α j + 1) j +
        ∑ x ∈ Finset.univ.erase j, Function.update α j (α j + 1) x := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    _ = (α j + 1) + ∑ x ∈ Finset.univ.erase j, α x := by
          rw [Function.update_self]
          congr 1
          exact Finset.sum_congr rfl (fun i hi => hne i (Finset.ne_of_mem_erase hi))
    _ = (α j + ∑ x ∈ Finset.univ.erase j, α x) + 1 := by omega
    _ = ∑ i, α i + 1 := by rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]

/-- If all derivatives of order `≤ m + 1` of `u` lie in `L²`, then `∂_j u` has all derivatives of order `≤ m` in `L²`. -/
lemma allDerivMemL2_distribDeriv {n : ℕ} {m : ℕ} (j : Fin n)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (hu : AllDerivMemL2 n (m + 1) u) :
    AllDerivMemL2 n m (distribDerivCLM (F := ℂ) (EuclideanSpace.single j 1) u) := by
  intro α hα
  rw [iteratedDistribDeriv_distribDeriv]
  exact hu _ (by rw [multiIndexOrder_update]; omega)

end SobolevSpace
end


section SobolevWeightL2
open scoped SchwartzMap FourierTransform
open SobolevSpace TemperedDistributions TestFunctions MeasureTheory
variable {n : ℕ}
/-- Multiplying the Fourier-side `L²` representative by the Sobolev weight `⟨·⟩` stays in `L²`, given derivative regularity. -/
theorem sobolevWeight_mul_memLp (m : ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (g₀ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hg₀_mem : MemLp g₀ 2 volume)
    (hg₀_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (𝓕 u) φ = ∫ ξ, (sobolevWeight n (↑m) ξ : ℂ)⁻¹ * g₀ ξ * φ ξ)
    (hj : ∀ j : Fin n, MemHs n (m : ℝ)
      (distribDerivCLM (F := ℂ) (EuclideanSpace.single j 1) u)) :
    MemLp (fun ξ => (sobolevWeight n 1 ξ : ℂ) * g₀ ξ) 2 volume := by sorry
end SobolevWeightL2

noncomputable section
open scoped SchwartzMap FourierTransform
open SobolevSpace TemperedDistributions TestFunctions MeasureTheory
namespace SobolevSpace

/-- Inductive step: if `u ∈ H^m` and every `∂_j u ∈ H^m`, then `u ∈ H^{m+1}`. -/
lemma memHs_succ_of_memHs_and_deriv {n : ℕ} (m : ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hu : MemHs n (m : ℝ) u)
    (hj : ∀ j : Fin n, MemHs n (m : ℝ)
      (distribDerivCLM (F := ℂ) (EuclideanSpace.single j 1) u)) :
    MemHs n ((m + 1 : ℕ) : ℝ) u := by
  obtain ⟨g₀, hg₀_mem, hg₀_eq⟩ := hu
  refine ⟨fun ξ => (sobolevWeight n 1 ξ : ℂ) * g₀ ξ, ?_, ?_⟩
  · exact sobolevWeight_mul_memLp (n := n) m u g₀ hg₀_mem hg₀_eq hj

  · intro φ
    rw [hg₀_eq]
    congr 1
    ext ξ
    simp only [sobolevWeight]
    have hjb_pos := japaneseBracket_pos n ξ
    have h_rpow_key : (japaneseBracket n ξ ^ ((↑(m + 1 : ℕ) : ℝ)))⁻¹ *
        japaneseBracket n ξ ^ (1 : ℝ) =
        (japaneseBracket n ξ ^ ((↑m : ℝ)))⁻¹ := by
      rw [← Real.rpow_neg hjb_pos.le, ← Real.rpow_add hjb_pos,
          ← Real.rpow_neg hjb_pos.le]
      congr 1
      push_cast
      ring
    have h_cast : ((↑(japaneseBracket n ξ ^ (↑m : ℝ)))⁻¹ : ℂ) =
        ((↑(japaneseBracket n ξ ^ (↑(m + 1 : ℕ) : ℝ)))⁻¹ : ℂ) *
        ((↑(japaneseBracket n ξ ^ (1 : ℝ))) : ℂ) := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_mul]
      congr 1
      exact h_rpow_key.symm
    rw [h_cast]
    ring

/-- If all multi-index derivatives of `u` up to order `m` lie in `L²`, then `u ∈ H^m`. -/
theorem allDerivMemL2_imp_memHs {n : ℕ} (m : ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (hu : AllDerivMemL2 n m u) :
    MemHs n (m : ℝ) u := by
  induction m generalizing u with
  | zero =>
    have h0 := hu (fun _ => 0) (by simp [multiIndexOrder])
    rw [iteratedDistribDeriv_zero] at h0
    simpa using h0
  | succ m ih =>
    have hu_Hm := ih u (allDerivMemL2_of_succ u hu)
    have hj_Hm := fun j => ih _ (allDerivMemL2_distribDeriv j u hu)
    exact memHs_succ_of_memHs_and_deriv m u hu_Hm hj_Hm

/-- Melrose Lemma 9.4 (integer case): `u ∈ H^m ↔` all `D^α u` with `|α| ≤ m` lie in `L²`. -/
theorem sobolev_integer_iff_deriv_memL2 (m : ℕ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    MemHs n (m : ℝ) u ↔ AllDerivMemL2 n m u := by
  constructor
  · intro hu α hα
    have h := memHs_iteratedDistribDeriv α u hu
    have hle : (0 : ℝ) ≤ ↑m - ↑(multiIndexOrder n α) :=
      sub_nonneg.mpr (Nat.cast_le (α := ℝ).mpr hα)
    exact memHs_of_le (by linarith) _ h
  · exact allDerivMemL2_imp_memHs m u

end SobolevSpace
end
