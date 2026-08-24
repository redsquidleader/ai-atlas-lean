/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.Data.Fin.Basic

open InnerProductSpace Submodule Set

namespace SpaceCurves

theorem gram_schmidt_orthonormalization {n k : ℕ} (_hk : k ≤ n)
    (v : Fin k → EuclideanSpace ℝ (Fin n))
    (hli : LinearIndependent ℝ v) :
    ∃ (e : Fin k → EuclideanSpace ℝ (Fin n)),
      Orthonormal ℝ e ∧
      (∀ (i : Fin k),
        Submodule.span ℝ (Set.range (fun j : Fin (i.val + 1) => e ⟨j, by omega⟩)) =
        Submodule.span ℝ (Set.range (fun j : Fin (i.val + 1) => v ⟨j, by omega⟩))) ∧
      (∀ i : Fin k, (0 : ℝ) < @inner ℝ _ _ (e i) (v i)) := by
  refine ⟨gramSchmidtNormed ℝ v, gramSchmidtNormed_orthonormal hli, fun i => ?_, fun i => ?_⟩
  ·
    have heq_e : Set.range (fun j : Fin (i.val + 1) => gramSchmidtNormed ℝ v ⟨j, by omega⟩) =
        gramSchmidtNormed ℝ v '' Set.Iic i := by
      ext x
      simp only [Set.mem_range, Set.mem_image, Set.mem_Iic]
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨⟨j.val, by omega⟩, Fin.mk_le_mk.mpr (by omega), rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨j.val, by omega⟩, rfl⟩
    have heq_v : Set.range (fun j : Fin (i.val + 1) => v ⟨j, by omega⟩) =
        v '' Set.Iic i := by
      ext x
      simp only [Set.mem_range, Set.mem_image, Set.mem_Iic]
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨⟨j.val, by omega⟩, Fin.mk_le_mk.mpr (by omega), rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨⟨j.val, by omega⟩, rfl⟩
    rw [heq_e, heq_v, span_gramSchmidtNormed, span_gramSchmidt_Iic]
  ·
    simp only [gramSchmidtNormed, inner_smul_left]
    apply mul_pos
    · exact inv_pos.mpr (norm_pos_iff.mpr (gramSchmidt_ne_zero i hli))
    · have key : @inner ℝ _ _ (gramSchmidt ℝ v i) (v i) = ‖gramSchmidt ℝ v i‖ ^ 2 := by
        conv_rhs => rw [← real_inner_self_eq_norm_sq]
        have hdef := gramSchmidt_def' ℝ v i
        conv_lhs => rw [hdef]
        rw [inner_add_right, inner_sum]
        suffices h : ∑ x ∈ Finset.Iio i,
            @inner ℝ _ _ (gramSchmidt ℝ v i) ((ℝ ∙ gramSchmidt ℝ v x).starProjection (v i)) = 0 by
          linarith
        apply Finset.sum_eq_zero
        intro j hj
        rw [starProjection_singleton, inner_smul_right]
        have hne : (i : Fin k) ≠ j :=
          Ne.symm (Finset.mem_Iio.mp hj).ne
        rw [gramSchmidt_orthogonal ℝ v hne]
        simp
      rw [key]
      exact pow_pos (norm_pos_iff.mpr (gramSchmidt_ne_zero i hli)) 2

theorem gram_schmidt_orthonormalization_unique
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {k : ℕ} (v : Fin k → E)
    (e₁ e₂ : Fin k → E)
    (hon₁ : Orthonormal ℝ e₁) (hon₂ : Orthonormal ℝ e₂)
    (hspan₁ : ∀ i : Fin k, span ℝ (e₁ '' Iic i) = span ℝ (v '' Iic i))
    (hspan₂ : ∀ i : Fin k, span ℝ (e₂ '' Iic i) = span ℝ (v '' Iic i))
    (hpos₁ : ∀ i, (0 : ℝ) < @inner ℝ _ _ (e₁ i) (v i))
    (hpos₂ : ∀ i, (0 : ℝ) < @inner ℝ _ _ (e₂ i) (v i)) :
    e₁ = e₂ := by
  suffices h : ∀ j : Fin k, e₁ j = e₂ j from funext h
  intro j
  apply Fin.strong_induction_on (motive := fun j => e₁ j = e₂ j)
  intro i ih
  have hmem : e₂ i ∈ span ℝ (e₁ '' Iic i) := by
    rw [hspan₁, ← hspan₂]
    exact subset_span (Set.mem_image_of_mem e₂ (Set.mem_Iic.mpr le_rfl))
  have hort : ∀ m : Fin k, m < i → @inner ℝ _ _ (e₁ m) (e₂ i) = 0 := by
    intro m hm
    rw [ih m hm]
    exact hon₂.2 (ne_of_lt hm)
  set c := @inner ℝ _ _ (e₁ i) (e₂ i) with hc_def
  have hd_zero : e₂ i - c • e₁ i = 0 := by
    have hd_in : e₂ i - c • e₁ i ∈ span ℝ (e₁ '' Iic i) :=
      sub_mem hmem (smul_mem _ _ (subset_span (Set.mem_image_of_mem e₁ (Set.mem_Iic.mpr le_rfl))))
    have hd_ort : e₂ i - c • e₁ i ∈ (span ℝ (e₁ '' Iic i))ᗮ := by
      rw [Submodule.mem_orthogonal']
      intro u hu
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
      · rintro x ⟨m, hm_le, rfl⟩
        rw [Set.mem_Iic] at hm_le
        simp only [inner_sub_left, inner_smul_left, RCLike.conj_to_real]
        rcases eq_or_lt_of_le hm_le with heq_m | hlt
        · have hmi : m = i := heq_m
          rw [hmi]
          have : @inner ℝ _ _ (e₂ i) (e₁ i) = c := by
            rw [hc_def, real_inner_comm]
          rw [this, show @inner ℝ _ _ (e₁ i) (e₁ i) = (1 : ℝ) from by
            rw [real_inner_self_eq_norm_sq, hon₁.1 i, one_pow]]
          ring
        · rw [show @inner ℝ _ _ (e₂ i) (e₁ m) = (0 : ℝ) from by
            rw [real_inner_comm]; exact hort m hlt]
          rw [show @inner ℝ _ _ (e₁ i) (e₁ m) = (0 : ℝ) from hon₁.2 (ne_of_gt hlt)]
          ring
      · simp
      · intro x y _ _ hx hy; rw [inner_add_right, hx, hy, add_zero]
      · intro a x _ hx; rw [inner_smul_right, hx, mul_zero]
    exact Submodule.disjoint_def.mp (Submodule.orthogonal_disjoint _) _ hd_in hd_ort
  have heq : e₂ i = c • e₁ i := sub_eq_zero.mp hd_zero
  have hc_one : c = 1 := by
    have hc_abs : |c| = 1 := by
      have h1 : ‖e₂ i‖ = 1 := hon₂.1 i
      rw [heq, norm_smul, hon₁.1 i, mul_one, Real.norm_eq_abs] at h1
      exact h1
    have hc_pos : (0 : ℝ) < c := by
      have h2 := hpos₂ i
      rw [heq, inner_smul_left, RCLike.conj_to_real] at h2
      exact (mul_pos_iff.mp h2).elim (fun h => h.1)
        (fun h => absurd h.2 (not_lt.mpr (le_of_lt (hpos₁ i))))
    linarith [abs_eq_self.mpr (le_of_lt hc_pos)]
  rw [heq, hc_one, one_smul]

end SpaceCurves

namespace SpaceCurves

lemma OrderedFinpartition.partSize_eq_one_of_length_eq
    {m : ℕ} (p : OrderedFinpartition m) (h : p.length = m) (i : Fin p.length) :
    p.partSize i = 1 := by
  have hcard : Fintype.card ((k : Fin p.length) × Fin (p.partSize k)) = m :=
    (Fintype.card_congr p.equivSigma).trans (Fintype.card_fin m)
  rw [Fintype.card_sigma] at hcard
  simp only [Fintype.card_fin] at hcard
  have hle : ∀ k : Fin p.length, 1 ≤ p.partSize k := fun k => p.partSize_pos k
  have hdecomp : ∑ k : Fin p.length, p.partSize k =
      p.partSize i + ∑ k ∈ Finset.univ.erase i, p.partSize k := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have hrest : p.length - 1 ≤ ∑ k ∈ Finset.univ.erase i, p.partSize k := by
    have hcard_erase : (Finset.univ.erase i).card = p.length - 1 := by
      simp [Finset.card_erase_of_mem (Finset.mem_univ i)]
    calc (p.length - 1 : ℕ) = ∑ _k ∈ Finset.univ.erase i, 1 := by
            simp [Finset.sum_const, hcard_erase]
      _ ≤ ∑ k ∈ Finset.univ.erase i, p.partSize k :=
            Finset.sum_le_sum (fun k hk => hle k)
  have hpi := hle i
  have hkey : m = p.partSize i + ∑ k ∈ Finset.univ.erase i, p.partSize k := by
    linarith [hcard, hdecomp]
  omega

theorem span_iteratedDeriv_comp_ge {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (φ : ℝ → ℝ) (hc : ContDiff ℝ ⊤ c) (hφ : ContDiff ℝ ⊤ φ)
    (hφ' : ∀ t, 0 < deriv φ t) (t : ℝ) (j : ℕ) (hj : j < n - 1) :
    iteratedDeriv (j + 1) c (φ t) ∈
      Submodule.span ℝ (Set.range (fun k : Fin (j + 1) =>
        iteratedDeriv (k.val + 1) (c ∘ φ) t)) := by
  induction j using Nat.strongRecOn with
  | ind j ih =>

  have hfdb : iteratedDeriv (j + 1) (c ∘ φ) t =
      ∑ p : OrderedFinpartition (j + 1),
        (∏ m : Fin p.length, iteratedDeriv (p.partSize m) φ t) •
        iteratedDeriv p.length c (φ t) :=
    iteratedDeriv_scomp_eq_sum_orderedFinpartition
      (hc.contDiffAt) (hφ.contDiffAt) (by simp)
  set S := Submodule.span ℝ (Set.range (fun k : Fin (j + 1) =>
      iteratedDeriv (k.val + 1) (c ∘ φ) t))
  have hcomp_in_S : iteratedDeriv (j + 1) (c ∘ φ) t ∈ S :=
    Submodule.subset_span ⟨⟨j, by omega⟩, rfl⟩

  set F := Finset.univ.filter (fun p : OrderedFinpartition (j + 1) => p.length = j + 1)
  set L := Finset.univ.filter (fun p : OrderedFinpartition (j + 1) => p.length ≠ j + 1)

  have hcoeff_eq : ∀ p : OrderedFinpartition (j + 1), p.length = j + 1 →
      (∏ k : Fin p.length, iteratedDeriv (p.partSize k) φ t) = (deriv φ t) ^ (j + 1) := by
    intro p hp
    have hall := fun i => OrderedFinpartition.partSize_eq_one_of_length_eq p hp i
    calc ∏ k : Fin p.length, iteratedDeriv (p.partSize k) φ t
        = ∏ k : Fin p.length, iteratedDeriv 1 φ t := by
          congr 1; ext k; rw [hall k]
      _ = ∏ k : Fin p.length, deriv φ t := by simp [iteratedDeriv_one]
      _ = (deriv φ t) ^ p.length := by rw [Finset.prod_const, Finset.card_fin]
      _ = (deriv φ t) ^ (j + 1) := by rw [hp]

  have hatomic_in_F : OrderedFinpartition.atomic (j + 1) ∈ F := by
    simp [F, Finset.mem_filter, OrderedFinpartition.atomic_length]

  have hF_sum : ∑ p ∈ F, (∏ k : Fin p.length, iteratedDeriv (p.partSize k) φ t) •
      iteratedDeriv p.length c (φ t) =
      ((F.card : ℝ) * (deriv φ t) ^ (j + 1)) • iteratedDeriv (j + 1) c (φ t) := by
    have heach : ∀ p ∈ F, (∏ k : Fin p.length, iteratedDeriv (p.partSize k) φ t) •
        iteratedDeriv p.length c (φ t) =
        (deriv φ t) ^ (j + 1) • iteratedDeriv (j + 1) c (φ t) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      rw [hcoeff_eq p hp.2, hp.2]
    rw [Finset.sum_congr rfl heach, Finset.sum_const]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]

  have hlower_in_S : ∑ p ∈ L, (∏ k : Fin p.length, iteratedDeriv (p.partSize k) φ t) •
      iteratedDeriv p.length c (φ t) ∈ S := by
    apply Submodule.sum_mem
    intro p hp
    rw [Finset.mem_filter] at hp
    apply Submodule.smul_mem
    have hlen_lt : p.length < j + 1 := by
      have := p.length_le; omega
    have hlen_pos : 0 < p.length :=
      OrderedFinpartition.length_pos p (by omega : 0 < j + 1)
    have hj' : p.length - 1 < j := by omega
    have hj'_bound : p.length - 1 < n - 1 := by omega
    have ih_applied := ih (p.length - 1) hj' hj'_bound
    have hrw : p.length - 1 + 1 = p.length := Nat.sub_add_cancel hlen_pos
    rw [hrw] at ih_applied
    exact Submodule.span_le.mpr (fun x hx => by
      obtain ⟨⟨k, hk⟩, rfl⟩ := hx
      exact Submodule.subset_span ⟨⟨k, by omega⟩, rfl⟩) ih_applied

  have hcoeff_ne : (F.card : ℝ) * (deriv φ t) ^ (j + 1) ≠ 0 := by
    apply mul_ne_zero
    · exact Nat.cast_ne_zero.mpr (Finset.card_pos.mpr ⟨_, hatomic_in_F⟩).ne'
    · exact pow_ne_zero _ (ne_of_gt (hφ' t))

  have hsplit : iteratedDeriv (j + 1) (c ∘ φ) t =
      (∑ p ∈ L, (∏ k : Fin p.length, iteratedDeriv (p.partSize k) φ t) •
        iteratedDeriv p.length c (φ t)) +
      ((F.card : ℝ) * (deriv φ t) ^ (j + 1)) • iteratedDeriv (j + 1) c (φ t) := by
    rw [← hF_sum, ← Finset.sum_union, hfdb]
    · congr 1
      ext p; simp [F, L, Finset.mem_filter]; tauto
    · exact Finset.disjoint_filter.mpr (fun p _ h1 h2 => h1 h2)

  suffices h : ((F.card : ℝ) * (deriv φ t) ^ (j + 1)) • iteratedDeriv (j + 1) c (φ t) ∈ S by
    exact (Submodule.smul_mem_iff S hcoeff_ne).mp h
  have hkey : ((F.card : ℝ) * (deriv φ t) ^ (j + 1)) • iteratedDeriv (j + 1) c (φ t) =
      iteratedDeriv (j + 1) (c ∘ φ) t -
      ∑ p ∈ L, (∏ k : Fin p.length, iteratedDeriv (p.partSize k) φ t) •
        iteratedDeriv p.length c (φ t) := by
    rw [hsplit, add_sub_cancel_left]
  rw [hkey]
  exact Submodule.sub_mem S hcomp_in_S hlower_in_S

end SpaceCurves

open scoped Matrix.Norms.Operator

theorem orthogonal_deriv_skew {n : ℕ} (E : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hE : ContDiff ℝ ⊤ E)
    (horth : ∀ t, E t ∈ Matrix.orthogonalGroup (Fin n) ℝ)
    (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ t, deriv E t = E t * A t) (t : ℝ) :
    (A t).transpose = - A t := by

  have hEEt : E t * (E t).transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp (horth t)
  have hEtE : (E t).transpose * E t = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).mp (horth t)

  have hEdiff : DifferentiableAt ℝ E t :=
    (hE.differentiable WithTop.top_ne_zero).differentiableAt
  let L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    (Matrix.transposeLinearEquiv (Fin n) (Fin n) ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap
  have hEtdiff : DifferentiableAt ℝ (fun s => (E s).transpose) t :=
    L.differentiableAt.comp t hEdiff

  have hconst : (fun s => E s * (E s).transpose) = Function.const ℝ 1 := by
    funext s; exact (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp (horth s)
  have hderiv_zero : deriv (fun s => E s * (E s).transpose) t = 0 := by
    rw [hconst]; exact deriv_const t 1

  have hprod : deriv (fun s => E s * (E s).transpose) t =
    deriv E t * (E t).transpose + E t * deriv (fun s => (E s).transpose) t :=
    deriv_mul hEdiff hEtdiff

  have hderiv_transpose : deriv (fun s => (E s).transpose) t = (deriv E t).transpose := by
    have hfun : (fun s => (E s).transpose) = L ∘ E := rfl
    rw [hfun, fderiv_comp_deriv t L.differentiableAt hEdiff, ContinuousLinearMap.fderiv]
    rfl

  have key : deriv E t * (E t).transpose + E t * (deriv E t).transpose = 0 := by
    rw [← hderiv_transpose, ← hprod]; exact hderiv_zero

  rw [hA t] at key
  rw [Matrix.transpose_mul] at key
  rw [← Matrix.mul_assoc (E t) ((A t).transpose) _] at key
  rw [← add_mul, ← mul_add] at key


  have hU : IsUnit (E t) := ⟨⟨E t, (E t).transpose, hEEt, hEtE⟩, rfl⟩
  have hUt : IsUnit ((E t).transpose) := ⟨⟨(E t).transpose, E t, hEtE, hEEt⟩, rfl⟩
  have h1 : (A t + (A t).transpose) * (E t).transpose = 0 := by
    apply hU.mul_left_cancel
    rw [mul_zero, ← Matrix.mul_assoc]
    exact key
  have h2 : A t + (A t).transpose = 0 :=
    hUt.mul_right_cancel (c := 0) (by rw [zero_mul]; exact h1)

  have : (A t).transpose = -A t + (A t + (A t).transpose) := by abel
  rw [h2, add_zero] at this
  exact this

namespace SpaceCurves

def IsFrenetCurve {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ContDiff ℝ ⊤ c ∧
  ∀ t, LinearIndependent ℝ (fun i : Fin (n - 1) =>
    iteratedDeriv (i.val + 1) c t)

noncomputable def frenetFrame {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (_hc : IsFrenetCurve c) (t : ℝ) : Fin n → EuclideanSpace ℝ (Fin n) :=
  gramSchmidtOrthonormalBasis finrank_euclideanSpace (fun i : Fin n =>
    if _h : i.val < n - 1 then iteratedDeriv (i.val + 1) c t
    else 0)

noncomputable def frenetCurvature {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (i : Fin (n - 1)) (t : ℝ) : ℝ :=
  @inner ℝ _ _ (frenetFrame c hc t ⟨i.val + 1, by omega⟩)
    (deriv (fun s => frenetFrame c hc s ⟨i.val, by omega⟩) t) /
  ‖deriv c t‖

noncomputable def frenetSerretMatrix {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j : Fin n =>
    if h : j.val = i.val + 1 ∧ i.val < n - 1 then
      -(frenetCurvature c hc ⟨i.val, h.2⟩ t)
    else if h : i.val = j.val + 1 ∧ j.val < n - 1 then
      frenetCurvature c hc ⟨j.val, h.2⟩ t
    else 0)

theorem frenetFrame_differentiableAt {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (t : ℝ) (i : Fin n) :
    DifferentiableAt ℝ (fun s => frenetFrame c hc s i) t := by sorry


theorem frenetFrame_deriv_mem_span {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (t : ℝ) (j : Fin n) (hj : j.val < n - 1) :
    deriv (fun s => frenetFrame c hc s j) t ∈
      Submodule.span ℝ (Set.range (fun i : Fin (j.val + 2) => frenetFrame c hc t ⟨i.val, by omega⟩)) := by
  set b := gramSchmidtOrthonormalBasis (𝕜 := ℝ) finrank_euclideanSpace
    (fun i : Fin n => if _ : i.val < n - 1 then iteratedDeriv (i.val + 1) c t else 0)
  have horthon : ∀ s, Orthonormal ℝ (frenetFrame c hc s) := fun s =>
    (gramSchmidtOrthonormalBasis (𝕜 := ℝ) finrank_euclideanSpace
      (fun i : Fin n => if _ : i.val < n - 1 then iteratedDeriv (i.val + 1) c s
        else 0)).orthonormal
  set v := deriv (fun s => frenetFrame c hc s j) t
  have expansion : v = ∑ k : Fin n, @inner ℝ _ _ (b k) v • (b k) :=
    (b.sum_repr' v).symm

  suffices hvanish : ∀ k : Fin n, k.val > j.val + 1 →
      @inner ℝ _ _ (frenetFrame c hc t k) v = 0 by
    rw [expansion]
    apply Submodule.sum_mem
    intro k _
    by_cases hk : k.val ≤ j.val + 1
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨⟨k.val, by omega⟩, by simp only [frenetFrame]; congr 1⟩
    · push Not at hk
      have hcoeff : @inner ℝ _ _ (b k) v = 0 := by
        show @inner ℝ _ _ (frenetFrame c hc t k) v = 0
        exact hvanish k hk
      rw [hcoeff, zero_smul]
      exact Submodule.zero_mem _

  intro k hk
  have hdk : DifferentiableAt ℝ (fun s => frenetFrame c hc s k) t :=
    frenetFrame_differentiableAt c hc t k
  have hdj : DifferentiableAt ℝ (fun s => frenetFrame c hc s j) t :=
    frenetFrame_differentiableAt c hc t j

  have hkj_ne : k ≠ j := by intro heq; omega
  have hort_kj : (fun s => @inner ℝ _ _ (frenetFrame c hc s k) (frenetFrame c hc s j)) =
      fun _ => (0 : ℝ) := funext (fun s => (horthon s).2 hkj_ne)
  have hdi_kj := HasDerivAt.inner ℝ hdk.hasDerivAt hdj.hasDerivAt
  have hd0_kj : HasDerivAt (fun s => @inner ℝ _ _ (frenetFrame c hc s k) (frenetFrame c hc s j))
      0 t := by rw [hort_kj]; exact hasDerivAt_const t 0
  have heq_kj : @inner ℝ _ _ (frenetFrame c hc t k) v +
      @inner ℝ _ _ (deriv (fun s => frenetFrame c hc s k) t) (frenetFrame c hc t j) = 0 :=
    hdi_kj.unique hd0_kj

  suffices hzero : @inner ℝ _ _ (deriv (fun s => frenetFrame c hc s k) t)
      (frenetFrame c hc t j) = 0 by linarith


  set S := Submodule.span ℝ (Set.range (fun i : Fin (j.val + 1) => iteratedDeriv (i.val + 1) c t))

  have hej_in_S : frenetFrame c hc t j ∈ S := by
    set f := (fun i : Fin n => if _ : i.val < n - 1 then iteratedDeriv (i.val + 1) c t else 0)
    have hmem := gramSchmidt_mem_span (𝕜 := ℝ) f (le_refl j)
    have hli : LinearIndependent ℝ (fun i : Fin (n - 1) => iteratedDeriv (i.val + 1) c t) := hc.2 t
    have hgsne : gramSchmidt ℝ f j ≠ 0 := by
      apply gramSchmidt_ne_zero_coe (𝕜 := ℝ) j
      have hcomp : f ∘ ((↑) : Set.Iic j → Fin n) =
          (fun i : Fin (n - 1) => iteratedDeriv (i.val + 1) c t) ∘
            (fun m : Set.Iic j => ⟨m.val.val, by
              have hle := m.prop; simp only [Set.mem_Iic, Fin.le_def] at hle; omega⟩) := by
        ext ⟨m, hm⟩
        simp only [Function.comp] at *
        simp only [f, dif_pos (show m.val < n - 1 from by
          have := Fin.le_def.mp (Set.mem_Iic.mp hm); omega)]
      rw [hcomp]
      exact LinearIndependent.comp hli _ (fun ⟨a, _⟩ ⟨b', _⟩ heq => by
        have h := congr_arg Fin.val heq
        simp only [Fin.val_mk] at h
        exact Subtype.ext (Fin.ext h))
    have hgsNormed_ne : gramSchmidtNormed ℝ f j ≠ 0 := by
      simp only [gramSchmidtNormed]
      exact smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hgsne)) hgsne
    have hframe_eq : frenetFrame c hc t j = gramSchmidtNormed ℝ f j :=
      gramSchmidtOrthonormalBasis_apply (𝕜 := ℝ) finrank_euclideanSpace hgsNormed_ne
    rw [hframe_eq, gramSchmidtNormed]
    apply Submodule.smul_mem
    exact Submodule.span_le.mpr (fun x hx => by
      obtain ⟨m, hm, rfl⟩ := hx
      simp only [Set.mem_Iic, Fin.le_def] at hm
      simp only [f, dif_pos (show m.val < n - 1 by omega)]
      exact Submodule.subset_span ⟨⟨m.val, by omega⟩, rfl⟩) hmem

  have hek_ort_derivs : ∀ i : Fin (j.val + 1),
      @inner ℝ _ _ (deriv (fun s => frenetFrame c hc s k) t) (iteratedDeriv (i.val + 1) c t) = 0 := by
    intro ⟨i, hi⟩

    have hi_lt_k : (⟨i, by omega⟩ : Fin n) < k := by
      simp only [Fin.lt_def]; omega
    have hort_ki : ∀ s, @inner ℝ _ _ (frenetFrame c hc s k) (iteratedDeriv (i + 1) c s) = 0 := by
      intro s
      have := gramSchmidtOrthonormalBasis_inv_triangular (𝕜 := ℝ) finrank_euclideanSpace
        (fun m : Fin n => if _ : m.val < n - 1 then iteratedDeriv (m.val + 1) c s else 0) hi_lt_k
      simp only [frenetFrame, dif_pos (show i < n - 1 by omega)] at this ⊢
      exact this

    have hv_diff : DifferentiableAt ℝ (fun s => iteratedDeriv (i + 1) c s) t :=
      (hc.1.differentiable_iteratedDeriv _ (by simp)).differentiableAt
    have hconst_ki : (fun s => @inner ℝ _ _ (frenetFrame c hc s k)
        (iteratedDeriv (i + 1) c s)) = fun _ => (0 : ℝ) := funext hort_ki
    have hdi_ki := HasDerivAt.inner ℝ hdk.hasDerivAt hv_diff.hasDerivAt
    have hd0_ki : HasDerivAt (fun s => @inner ℝ _ _ (frenetFrame c hc s k)
        (iteratedDeriv (i + 1) c s)) 0 t := by rw [hconst_ki]; exact hasDerivAt_const t 0
    have heq_ki := hdi_ki.unique hd0_ki


    have hderiv_iter : deriv (fun s => iteratedDeriv (i + 1) c s) t =
        iteratedDeriv (i + 2) c t :=
      (congrFun (@iteratedDeriv_succ ℝ _ _ _ _ (n := i + 1) (f := c)) t).symm
    have hi2_lt_k : (⟨i + 1, by omega⟩ : Fin n) < k := by
      simp only [Fin.lt_def]; omega
    have hort_ki2 : @inner ℝ _ _ (frenetFrame c hc t k) (iteratedDeriv (i + 2) c t) = 0 := by
      have := gramSchmidtOrthonormalBasis_inv_triangular (𝕜 := ℝ) finrank_euclideanSpace
        (fun m : Fin n => if _ : m.val < n - 1 then iteratedDeriv (m.val + 1) c t else 0) hi2_lt_k
      simp only [frenetFrame, dif_pos (show i + 1 < n - 1 by omega)] at this ⊢
      exact this
    rw [hderiv_iter] at heq_ki
    linarith [hort_ki2]

  have hek_ort_S : frenetFrame c hc t j ∈ S ∧
      deriv (fun s => frenetFrame c hc s k) t ∈ Sᗮ :=
    ⟨hej_in_S, by
      rw [Submodule.mem_orthogonal']
      intro u hu
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
      · rintro x ⟨⟨i, hi⟩, rfl⟩
        exact hek_ort_derivs ⟨i, hi⟩
      · exact inner_zero_right _
      · intro x y _ _ hx hy; rw [inner_add_right, hx, hy, add_zero]
      · intro a x _ hx; rw [inner_smul_right, hx, mul_zero]⟩

  exact Submodule.inner_left_of_mem_orthogonal hek_ort_S.1 hek_ort_S.2


theorem frenetFrame_inner_deriv_vanish {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (t : ℝ) (hn : 2 ≤ n) (hc' : ‖deriv c t‖ ≠ 0)
    (k j : Fin n) (h1 : ¬(j.val = k.val + 1 ∧ k.val < n - 1))
    (h2 : ¬(k.val = j.val + 1 ∧ j.val < n - 1)) :
    @inner ℝ _ _ (frenetFrame c hc t k)
      (deriv (fun s => frenetFrame c hc s j) t) = 0 := by

  have horthon : ∀ s, Orthonormal ℝ (frenetFrame c hc s) := fun s =>
    (gramSchmidtOrthonormalBasis (𝕜 := ℝ) finrank_euclideanSpace
      (fun i : Fin n => if _ : i.val < n - 1 then iteratedDeriv (i.val + 1) c s
        else 0)).orthonormal
  by_cases hkj : k = j
  ·
    rw [hkj]
    have hnorm : ∀ s, @inner ℝ _ _ (frenetFrame c hc s j) (frenetFrame c hc s j) = 1 := by
      intro s; rw [real_inner_self_eq_norm_sq, (horthon s).1 j, one_pow]
    have hconst : (fun s => @inner ℝ _ _ (frenetFrame c hc s j) (frenetFrame c hc s j)) =
        fun _ => (1 : ℝ) := funext hnorm
    have hdj : DifferentiableAt ℝ (fun s => frenetFrame c hc s j) t :=
      frenetFrame_differentiableAt c hc t j
    have hdi : HasDerivAt (fun s => @inner ℝ _ _ (frenetFrame c hc s j) (frenetFrame c hc s j))
        (@inner ℝ _ _ (frenetFrame c hc t j) (deriv (fun s => frenetFrame c hc s j) t) +
         @inner ℝ _ _ (deriv (fun s => frenetFrame c hc s j) t) (frenetFrame c hc t j)) t :=
      HasDerivAt.inner ℝ hdj.hasDerivAt hdj.hasDerivAt
    have hd1 : HasDerivAt (fun s => @inner ℝ _ _ (frenetFrame c hc s j) (frenetFrame c hc s j))
        0 t := by rw [hconst]; exact hasDerivAt_const t 1
    have heq := hdi.unique hd1
    linarith [real_inner_comm (deriv (fun s => frenetFrame c hc s j) t) (frenetFrame c hc t j)]
  ·


    have hkj_val : k.val ≠ j.val := fun h => hkj (Fin.ext h)
    have h1' : j.val ≠ k.val + 1 ∨ ¬(k.val < n - 1) := by
      by_contra hall; push Not at hall; exact h1 ⟨hall.1, hall.2⟩
    have h2' : k.val ≠ j.val + 1 ∨ ¬(j.val < n - 1) := by
      by_contra hall; push Not at hall; exact h2 ⟨hall.1, hall.2⟩

    rcases Nat.lt_or_ge k.val j.val with hlt_kj | hge_kj
    ·
      have hk_lt_nm1 : k.val < n - 1 := by omega
      have hj_ne_kp1 : j.val ≠ k.val + 1 := by
        rcases h1' with h | h
        · exact h
        · exact absurd hk_lt_nm1 h
      have hj_gt_kp1 : j.val > k.val + 1 := by omega

      have hspan := frenetFrame_deriv_mem_span c hc t k hk_lt_nm1

      have hort_const : (fun s => @inner ℝ _ _ (frenetFrame c hc s k) (frenetFrame c hc s j)) =
          fun _ => (0 : ℝ) := funext (fun s => (horthon s).2 hkj)
      have hdk := (frenetFrame_differentiableAt c hc t k).hasDerivAt
      have hdj := (frenetFrame_differentiableAt c hc t j).hasDerivAt
      have hdi := HasDerivAt.inner ℝ hdk hdj
      have hd0 : HasDerivAt (fun s => @inner ℝ _ _ (frenetFrame c hc s k) (frenetFrame c hc s j))
          0 t := by rw [hort_const]; exact hasDerivAt_const t 0
      have heq := hdi.unique hd0


      suffices h : @inner ℝ _ _ (deriv (fun s => frenetFrame c hc s k) t) (frenetFrame c hc t j) = 0 by
        linarith

      have hmem := hspan
      rw [show @inner ℝ _ _ (deriv (fun s => frenetFrame c hc s k) t) (frenetFrame c hc t j) =
          @inner ℝ _ _ (frenetFrame c hc t j) (deriv (fun s => frenetFrame c hc s k) t) from
          real_inner_comm _ _]

      apply Submodule.inner_left_of_mem_orthogonal hmem
      rw [Submodule.mem_orthogonal']
      intro u hu
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
      · rintro x ⟨⟨i, hi⟩, rfl⟩
        have hne : j ≠ (⟨i, by omega⟩ : Fin n) := by
          intro heq; have := congr_arg Fin.val heq; simp at this; omega
        exact (horthon t).2 hne
      · simp
      · intro x y _ _ hx hy; rw [inner_add_right, hx, hy, add_zero]
      · intro a x _ hx; rw [inner_smul_right, hx, mul_zero]
    ·
      have hk_gt_j : k.val > j.val := by omega
      have hj_lt_nm1 : j.val < n - 1 := by
        by_contra h; push Not at h

        have : j.val = n - 1 := by omega
        have : k.val ≥ n := by omega
        exact absurd (Nat.lt_of_lt_of_le k.isLt (Nat.le_refl n)) (by omega)
      have hk_ne_jp1 : k.val ≠ j.val + 1 := by
        rcases h2' with h | h
        · exact h
        · exact absurd hj_lt_nm1 h
      have hk_gt_jp1 : k.val > j.val + 1 := by omega

      have hspan := frenetFrame_deriv_mem_span c hc t j hj_lt_nm1

      apply Submodule.inner_left_of_mem_orthogonal hspan
      rw [Submodule.mem_orthogonal']
      intro u hu
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
      · rintro x ⟨⟨i, hi⟩, rfl⟩
        have hne : k ≠ (⟨i, by omega⟩ : Fin n) := by
          intro heq; have := congr_arg Fin.val heq; simp at this; omega
        exact (horthon t).2 hne
      · simp
      · intro x y _ _ hx hy; rw [inner_add_right, hx, hy, add_zero]
      · intro a x _ hx; rw [inner_smul_right, hx, mul_zero]

theorem frenetFrame_inner_deriv_super {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (t : ℝ) (hn : 2 ≤ n) (hc' : ‖deriv c t‖ ≠ 0)
    (k j : Fin n) (h : j.val = k.val + 1 ∧ k.val < n - 1) :
    @inner ℝ _ _ (frenetFrame c hc t k)
      (deriv (fun s => frenetFrame c hc s j) t) =
    ‖deriv c t‖ * -(frenetCurvature c hc ⟨k.val, h.2⟩ t) := by
  unfold frenetCurvature
  rw [mul_neg, mul_div_cancel₀ _ hc']

  have hj_fin : frenetFrame c hc t ⟨k.val + 1, by omega⟩ = frenetFrame c hc t j := by
    congr 1; ext; exact h.1.symm
  have hk_fun : (fun s => frenetFrame c hc s ⟨k.val, by omega⟩) =
      (fun s => frenetFrame c hc s k) := by
    funext s; congr 1
  rw [hj_fin, hk_fun]

  set ek := fun s => frenetFrame c hc s k
  set ej := fun s => frenetFrame c hc s j

  have hort : ∀ s, @inner ℝ _ _ (ek s) (ej s) = 0 := by
    intro s
    have hne : k ≠ j := by intro heq; have := congr_arg Fin.val heq; omega
    exact (gramSchmidtOrthonormalBasis (𝕜 := ℝ) finrank_euclideanSpace
      (fun i : Fin n => if _ : i.val < n - 1 then iteratedDeriv (i.val + 1) c s
        else 0)).orthonormal.2 hne
  have hconst : (fun s => @inner ℝ _ _ (ek s) (ej s)) = fun _ => (0 : ℝ) :=
    funext hort

  have hdk : DifferentiableAt ℝ ek t := frenetFrame_differentiableAt c hc t k
  have hdj : DifferentiableAt ℝ ej t := frenetFrame_differentiableAt c hc t j

  have hdi : HasDerivAt (fun s => @inner ℝ _ _ (ek s) (ej s))
      (@inner ℝ _ _ (ek t) (deriv ej t) + @inner ℝ _ _ (deriv ek t) (ej t)) t :=
    HasDerivAt.inner ℝ hdk.hasDerivAt hdj.hasDerivAt
  have hd0 : HasDerivAt (fun s => @inner ℝ _ _ (ek s) (ej s)) 0 t := by
    rw [hconst]; exact hasDerivAt_const t 0
  have heq : @inner ℝ _ _ (ek t) (deriv ej t) +
      @inner ℝ _ _ (deriv ek t) (ej t) = 0 := hdi.unique hd0
  linarith [real_inner_comm (deriv ek t) (ej t)]


theorem frenetFrame_inner_deriv_sub {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (t : ℝ) (hn : 2 ≤ n) (hc' : ‖deriv c t‖ ≠ 0)
    (k j : Fin n) (h1 : ¬(j.val = k.val + 1 ∧ k.val < n - 1))
    (h : k.val = j.val + 1 ∧ j.val < n - 1) :
    @inner ℝ _ _ (frenetFrame c hc t k)
      (deriv (fun s => frenetFrame c hc s j) t) =
    ‖deriv c t‖ * frenetCurvature c hc ⟨j.val, h.2⟩ t := by
  unfold frenetCurvature
  rw [mul_div_cancel₀ _ hc']
  congr 1
  · congr 1
    exact Fin.ext h.1

theorem frenetSerret_equation {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (t : ℝ) (hn : 2 ≤ n)
    (hc' : ‖deriv c t‖ ≠ 0) (j : Fin n) :
    deriv (fun s => frenetFrame c hc s j) t =
    ‖deriv c t‖ • (∑ k : Fin n,
      frenetSerretMatrix c hc t k j • frenetFrame c hc t k) := by
  let b := gramSchmidtOrthonormalBasis (𝕜 := ℝ) finrank_euclideanSpace
    (fun i : Fin n => if _ : i.val < n - 1 then iteratedDeriv (i.val + 1) c t else 0)
  set v := deriv (fun s => frenetFrame c hc s j) t with hv_def
  have expansion : v = ∑ k : Fin n, @inner ℝ _ _ (b k) v • (b k) :=
    (b.sum_repr' v).symm
  have coeff_eq : ∀ k : Fin n, @inner ℝ _ _ (frenetFrame c hc t k) v =
      ‖deriv c t‖ * frenetSerretMatrix c hc t k j := by
    intro k
    simp only [frenetSerretMatrix, Matrix.of_apply]
    split_ifs with h1 h2
    · exact frenetFrame_inner_deriv_super c hc t hn hc' k j h1
    · exact frenetFrame_inner_deriv_sub c hc t hn hc' k j h1 h2
    · rw [frenetFrame_inner_deriv_vanish c hc t hn hc' k j h1 h2, mul_zero]
  rw [expansion, Finset.smul_sum]
  simp_rw [frenetFrame, smul_smul]
  congr 1
  funext k
  congr 1
  have := coeff_eq k
  simp only [frenetFrame, hv_def] at this
  exact this
theorem frenetCurvature_eq_inner_div_norm {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (i : Fin (n - 1)) (t : ℝ) :
    frenetCurvature c hc i t =
    @inner ℝ _ _ (frenetFrame c hc t ⟨i.val + 1, by omega⟩)
      (deriv (fun s => frenetFrame c hc s ⟨i.val, by omega⟩) t) /
    ‖deriv c t‖ := by
  rfl


set_option maxHeartbeats 800000 in
theorem frenetCurvature_pos {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (i : Fin (n - 1)) (hi : i.val < n - 2) (t : ℝ)
    (hc' : ‖deriv c t‖ ≠ 0) :
    0 < frenetCurvature c hc i t := by
  have hn : 2 ≤ n := by omega

  set f : Fin n → EuclideanSpace ℝ (Fin n) := fun k =>
    if _h : k.val < n - 1 then iteratedDeriv (k.val + 1) c t else 0

  have hframe : frenetFrame c hc t = gramSchmidtOrthonormalBasis finrank_euclideanSpace f := rfl

  have hgsn_ne : ∀ (j : Fin n), j.val < n - 1 → gramSchmidtNormed ℝ f j ≠ 0 := by
    intro j hj
    have hli_restrict : LinearIndependent ℝ (f ∘ ((↑) : Set.Iic j → Fin n)) := by
      have hfun : ∀ (x : Set.Iic j),
          (f ∘ ((↑) : Set.Iic j → Fin n)) x =
          (fun m : Fin (n - 1) => iteratedDeriv (m.val + 1) c t)
            ⟨(↑x : Fin n).val, by
              have hle : (↑x : Fin n) ≤ j := Set.mem_Iic.mp x.prop
              exact lt_of_le_of_lt (Fin.val_le_of_le hle) hj⟩ := by
        intro ⟨x, hx⟩
        simp only [Function.comp, f]
        have hxlt : x.val < n - 1 := lt_of_le_of_lt (Fin.val_le_of_le (Set.mem_Iic.mp hx)) hj
        rw [dif_pos hxlt]
      rw [show f ∘ ((↑) : Set.Iic j → Fin n) =
        (fun m : Fin (n - 1) => iteratedDeriv (m.val + 1) c t) ∘
        (fun x : Set.Iic j => ⟨(↑x : Fin n).val, by
          have hle : (↑x : Fin n) ≤ j := Set.mem_Iic.mp x.prop
          exact lt_of_le_of_lt (Fin.val_le_of_le hle) hj⟩) from funext hfun]
      apply LinearIndependent.comp (hc.2 t)
      intro ⟨a, ha⟩ ⟨b, hb⟩ hab
      exact Subtype.ext (Fin.ext (Fin.mk.inj hab))
    have hgs_ne : gramSchmidt ℝ f j ≠ 0 := gramSchmidt_ne_zero_coe j hli_restrict
    exact fun h => hgs_ne (by
      rw [gramSchmidtNormed] at h
      exact (smul_eq_zero.mp h).resolve_left
        (inv_ne_zero (by exact_mod_cast norm_ne_zero_iff.mpr hgs_ne)))

  have hgs_pos : ∀ (j : Fin n), j.val < n - 1 →
      (0 : ℝ) < @inner ℝ _ _ (gramSchmidtOrthonormalBasis finrank_euclideanSpace f j) (f j) := by
    intro j hj
    have hne := hgsn_ne j hj
    rw [gramSchmidtOrthonormalBasis_apply finrank_euclideanSpace hne]
    simp only [gramSchmidtNormed, inner_smul_left, RCLike.conj_to_real]
    have hgs_ne : gramSchmidt ℝ f j ≠ 0 := fun h => hne (by
      simp only [gramSchmidtNormed, h, smul_zero])
    apply mul_pos
    · exact inv_pos.mpr (norm_pos_iff.mpr hgs_ne)
    · have key : @inner ℝ _ _ (gramSchmidt ℝ f j) (f j) = ‖gramSchmidt ℝ f j‖ ^ 2 := by
        conv_rhs => rw [← real_inner_self_eq_norm_sq]
        have hdef := gramSchmidt_def' ℝ f j
        conv_lhs => rw [hdef]
        rw [inner_add_right, inner_sum]
        suffices h : ∑ x ∈ Finset.Iio j,
            @inner ℝ _ _ (gramSchmidt ℝ f j)
              ((ℝ ∙ gramSchmidt ℝ f x).starProjection (f j)) = 0 by
          linarith
        apply Finset.sum_eq_zero
        intro k hk
        rw [starProjection_singleton, inner_smul_right]
        have hne' : (j : Fin n) ≠ k := Ne.symm (Finset.mem_Iio.mp hk).ne
        rw [gramSchmidt_orthogonal ℝ f hne']
        simp
      rw [key]
      exact pow_pos (norm_pos_iff.mpr hgs_ne) 2

  have hzero : ∀ s, @inner ℝ _ _ (frenetFrame c hc s ⟨i.val + 1, by omega⟩)
      (iteratedDeriv (i.val + 1) c s) = 0 := by
    intro s
    show @inner ℝ _ _ (gramSchmidtOrthonormalBasis finrank_euclideanSpace
      (fun k : Fin n => if _ : k.val < n - 1 then iteratedDeriv (k.val + 1) c s else 0)
      ⟨i.val + 1, by omega⟩) _ = 0
    set g : Fin n → EuclideanSpace ℝ (Fin n) := fun k =>
      if _h : k.val < n - 1 then iteratedDeriv (k.val + 1) c s else 0
    show @inner ℝ _ _ (gramSchmidtOrthonormalBasis finrank_euclideanSpace g ⟨i.val + 1, by omega⟩)
      (iteratedDeriv (i.val + 1) c s) = 0
    have hgi : g ⟨i.val, by omega⟩ = iteratedDeriv (i.val + 1) c s := by
      simp only [g, dif_pos (show i.val < n - 1 from by omega)]
    rw [← hgi]
    exact gramSchmidtOrthonormalBasis_inv_triangular finrank_euclideanSpace g
      (show (⟨i.val, by omega⟩ : Fin n) < ⟨i.val + 1, by omega⟩ from by
        simp only [Fin.lt_def]; omega)

  set e_ip1 := fun s => frenetFrame c hc s ⟨i.val + 1, by omega⟩
  set v := fun s => iteratedDeriv (i.val + 1) c s
  have hf_diff : DifferentiableAt ℝ e_ip1 t := frenetFrame_differentiableAt c hc t _
  have hg_diff : DifferentiableAt ℝ v t :=
    (hc.1.differentiable_iteratedDeriv _ (by simp)).differentiableAt
  have hderiv_eq : @inner ℝ _ _ (e_ip1 t) (deriv v t) +
      @inner ℝ _ _ (deriv e_ip1 t) (v t) = 0 := by
    have h0 : deriv (fun s => @inner ℝ _ _ (e_ip1 s) (v s)) t = 0 := by
      have : (fun s => @inner ℝ _ _ (e_ip1 s) (v s)) = fun _ => (0 : ℝ) := by
        ext s; exact hzero s
      rw [this, deriv_const]
    have hexp := deriv_inner_apply (𝕜 := ℝ) hf_diff hg_diff
    linarith
  have hiter : iteratedDeriv (i.val + 2) c t = deriv v t :=
    congrFun (@iteratedDeriv_succ ℝ _ _ _ _ (n := i.val + 1) (f := c)) t

  have hkey : @inner ℝ _ _ (frenetFrame c hc t ⟨i.val + 1, by omega⟩)
      (iteratedDeriv (i.val + 2) c t) = -@inner ℝ _ _ (deriv e_ip1 t) (v t) := by
    rw [hiter]; linarith

  have expand_inner : @inner ℝ _ _ (deriv e_ip1 t) (v t) =
      ∑ j : Fin n, @inner ℝ _ _ (frenetFrame c hc t j) (deriv e_ip1 t) *
        @inner ℝ _ _ (frenetFrame c hc t j) (v t) := by
    let b := gramSchmidtOrthonormalBasis (𝕜 := ℝ) finrank_euclideanSpace
      (fun k : Fin n => if _ : k.val < n - 1 then iteratedDeriv (k.val + 1) c t else 0)
    have hexp : deriv e_ip1 t = ∑ j : Fin n, @inner ℝ _ _ (b j) (deriv e_ip1 t) • (b j) :=
      (b.sum_repr' (deriv e_ip1 t)).symm
    conv_lhs => rw [hexp]
    rw [sum_inner]
    congr 1; ext j
    simp only [frenetFrame, inner_smul_left, RCLike.conj_to_real, b]

  have sum_eq : ∑ j : Fin n, @inner ℝ _ _ (frenetFrame c hc t j) (deriv e_ip1 t) *
      @inner ℝ _ _ (frenetFrame c hc t j) (v t) =
      @inner ℝ _ _ (frenetFrame c hc t ⟨i.val, by omega⟩) (deriv e_ip1 t) *
        @inner ℝ _ _ (frenetFrame c hc t ⟨i.val, by omega⟩) (v t) := by
    apply Finset.sum_eq_single (⟨i.val, by omega⟩ : Fin n)
    · intro j _ hji
      by_cases hj_gt : j.val > i.val
      ·
        have : @inner ℝ _ _ (frenetFrame c hc t j) (v t) = 0 := by
          show @inner ℝ _ _ (frenetFrame c hc t j) (iteratedDeriv (i.val + 1) c t) = 0
          rw [hframe]
          have hfi : f ⟨i.val, by omega⟩ = iteratedDeriv (i.val + 1) c t := by
            simp only [f, dif_pos (show i.val < n - 1 from by omega)]
          rw [← hfi]
          exact gramSchmidtOrthonormalBasis_inv_triangular finrank_euclideanSpace f
            (show (⟨i.val, by omega⟩ : Fin n) < j from by simp [Fin.lt_def]; exact hj_gt)
        rw [this, mul_zero]
      ·
        have hj_lt : j.val < i.val := by
          have hne : j ≠ ⟨i.val, by omega⟩ := hji
          simp [Fin.ext_iff] at hne
          omega
        have hvanish := frenetFrame_inner_deriv_vanish c hc t hn hc' j ⟨i.val + 1, by omega⟩
          (by intro ⟨h1, _⟩; simp [Fin.val_mk] at h1; omega)
          (by intro ⟨h1, _⟩; simp [Fin.val_mk] at h1; omega)
        rw [hvanish, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h

  have hsuper : @inner ℝ _ _ (frenetFrame c hc t ⟨i.val, by omega⟩) (deriv e_ip1 t) =
      ‖deriv c t‖ * -(frenetCurvature c hc ⟨i.val, by omega⟩ t) := by
    exact frenetFrame_inner_deriv_super c hc t hn hc' ⟨i.val, by omega⟩ ⟨i.val + 1, by omega⟩
      ⟨by rfl, i.isLt⟩

  have hpos_i : (0 : ℝ) < @inner ℝ _ _ (frenetFrame c hc t ⟨i.val, by omega⟩) (v t) := by
    show (0 : ℝ) < @inner ℝ _ _ (frenetFrame c hc t ⟨i.val, by omega⟩) (iteratedDeriv (i.val + 1) c t)
    rw [hframe]
    have hfi : f ⟨i.val, by omega⟩ = iteratedDeriv (i.val + 1) c t := by
      simp only [f, dif_pos (show i.val < n - 1 from by omega)]
    rw [← hfi]
    exact hgs_pos ⟨i.val, by omega⟩ (show i.val < n - 1 from by omega)

  have hpos_ip1 : (0 : ℝ) < @inner ℝ _ _ (frenetFrame c hc t ⟨i.val + 1, by omega⟩)
      (iteratedDeriv (i.val + 2) c t) := by
    rw [hframe]
    have hfi : f ⟨i.val + 1, by omega⟩ = iteratedDeriv (i.val + 2) c t := by
      simp only [f, dif_pos (show i.val + 1 < n - 1 from by omega)]
    rw [← hfi]
    exact hgs_pos ⟨i.val + 1, by omega⟩ (show i.val + 1 < n - 1 from by omega)

  have hc'_pos : (0 : ℝ) < ‖deriv c t‖ := by positivity
  have heq : @inner ℝ _ _ (frenetFrame c hc t ⟨i.val + 1, by omega⟩)
      (iteratedDeriv (i.val + 2) c t) =
      ‖deriv c t‖ * frenetCurvature c hc ⟨i.val, by omega⟩ t *
      @inner ℝ _ _ (frenetFrame c hc t ⟨i.val, by omega⟩) (v t) := by
    rw [hkey, expand_inner, sum_eq, hsuper]; ring

  have hmul_pos : 0 < ‖deriv c t‖ * frenetCurvature c hc ⟨i.val, by omega⟩ t *
      @inner ℝ _ _ (frenetFrame c hc t ⟨i.val, by omega⟩) (v t) := by linarith
  have hdenom_pos : 0 < ‖deriv c t‖ * @inner ℝ _ _ (frenetFrame c hc t ⟨i.val, by omega⟩) (v t) :=
    mul_pos hc'_pos hpos_i
  have hκ_pos : 0 < frenetCurvature c hc ⟨i.val, by omega⟩ t := by
    by_contra h
    push_neg at h
    have : ‖deriv c t‖ * frenetCurvature c hc ⟨i.val, by omega⟩ t ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hc'_pos) h
    have : ‖deriv c t‖ * frenetCurvature c hc ⟨i.val, by omega⟩ t *
        @inner ℝ _ _ (frenetFrame c hc t ⟨i.val, by omega⟩) (v t) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg this (le_of_lt hpos_i)
    linarith
  exact hκ_pos

theorem frenetSerret_theorem {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (t : ℝ) (hn : 2 ≤ n) (hc' : ‖deriv c t‖ ≠ 0) :

    (∀ j : Fin n, deriv (fun s => frenetFrame c hc s j) t =
      ‖deriv c t‖ • ∑ k : Fin n,
        frenetSerretMatrix c hc t k j • frenetFrame c hc t k) ∧

    (∀ i : Fin (n - 1), i.val < n - 2 → 0 < frenetCurvature c hc i t) ∧

    (∀ i : Fin (n - 1), frenetCurvature c hc i t =
      @inner ℝ _ _ (frenetFrame c hc t ⟨i.val + 1, by omega⟩)
        (deriv (fun s => frenetFrame c hc s ⟨i.val, by omega⟩) t) / ‖deriv c t‖) :=
  ⟨fun j => frenetSerret_equation c hc t hn hc' j,
   fun i hi => frenetCurvature_pos c hc i hi t hc',
   fun i => frenetCurvature_eq_inner_div_norm c hc i t⟩


theorem frenetFrame_orthogonal_higher_iteratedDeriv {n : ℕ}
    (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (s : ℝ) (i : Fin n) (j : Fin n)
    (hij : i.val < j.val) (hi : i.val < n - 1) :
    @inner ℝ _ _ (frenetFrame c hc s j) (iteratedDeriv (i.val + 1) c s) = 0 := by sorry

theorem frenet_diagonal_entry_succ {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (t : ℝ) (hn : 2 ≤ n) (hc' : ‖deriv c t‖ ≠ 0)
    (i : Fin n) (hi : i.val + 1 < n) :
    @inner ℝ _ _ (frenetFrame c hc t ⟨i.val + 1, by omega⟩) (iteratedDeriv (i.val + 2) c t) =
    ‖deriv c t‖ * frenetCurvature c hc ⟨i.val, by omega⟩ t *
    @inner ℝ _ _ (frenetFrame c hc t i) (iteratedDeriv (i.val + 1) c t) := by

  set ip1 : Fin n := ⟨i.val + 1, hi⟩
  set e_ip1 := fun s => frenetFrame c hc s ip1
  set v := fun s => iteratedDeriv (i.val + 1) c s

  have hzero : ∀ s, @inner ℝ _ _ (e_ip1 s) (v s) = 0 := by
    intro s
    exact frenetFrame_orthogonal_higher_iteratedDeriv c hc s i ip1
      (by simp [ip1]) (by omega)

  have hf_diff : DifferentiableAt ℝ e_ip1 t := frenetFrame_differentiableAt c hc t ip1
  have hg_diff : DifferentiableAt ℝ v t :=
    (hc.1.differentiable_iteratedDeriv _ (by simp)).differentiableAt
  have hderiv_eq : @inner ℝ _ _ (e_ip1 t) (deriv v t) +
      @inner ℝ _ _ (deriv e_ip1 t) (v t) = 0 := by
    have h0 : deriv (fun s => @inner ℝ _ _ (e_ip1 s) (v s)) t = 0 := by
      have : (fun s => @inner ℝ _ _ (e_ip1 s) (v s)) = fun _ => (0 : ℝ) := by
        ext s; exact hzero s
      rw [this, deriv_const]
    have hexp := deriv_inner_apply (𝕜 := ℝ) hf_diff hg_diff
    linarith

  have hiter : iteratedDeriv (i.val + 2) c t = deriv v t :=
    congrFun (@iteratedDeriv_succ ℝ _ _ _ _ (n := i.val + 1) (f := c)) t

  have key : @inner ℝ _ _ (frenetFrame c hc t ip1) (iteratedDeriv (i.val + 2) c t) =
      -@inner ℝ _ _ (deriv e_ip1 t) (v t) := by
    rw [hiter]; linarith


  have expand_inner : @inner ℝ _ _ (deriv e_ip1 t) (v t) =
      ∑ j : Fin n, @inner ℝ _ _ (frenetFrame c hc t j) (deriv e_ip1 t) *
        @inner ℝ _ _ (frenetFrame c hc t j) (v t) := by
    let b := gramSchmidtOrthonormalBasis (𝕜 := ℝ) finrank_euclideanSpace
      (fun i : Fin n => if _ : i.val < n - 1 then iteratedDeriv (i.val + 1) c t else 0)
    have hexp : deriv e_ip1 t = ∑ j : Fin n, @inner ℝ _ _ (b j) (deriv e_ip1 t) • (b j) :=
      (b.sum_repr' (deriv e_ip1 t)).symm
    conv_lhs => rw [hexp]
    rw [sum_inner]
    congr 1; ext j
    simp only [frenetFrame, inner_smul_left, RCLike.conj_to_real, b]


  have sum_eq : ∑ j : Fin n, @inner ℝ _ _ (frenetFrame c hc t j) (deriv e_ip1 t) *
      @inner ℝ _ _ (frenetFrame c hc t j) (v t) =
      @inner ℝ _ _ (frenetFrame c hc t i) (deriv e_ip1 t) *
        @inner ℝ _ _ (frenetFrame c hc t i) (v t) := by
    apply Finset.sum_eq_single i
    · intro j _ hji
      by_cases hj_gt : j.val > i.val
      ·
        have := frenetFrame_orthogonal_higher_iteratedDeriv c hc t i j hj_gt (by omega)
        rw [this, mul_zero]
      ·
        have hj_lt : j.val < i.val := by omega
        have hvanish := frenetFrame_inner_deriv_vanish c hc t hn hc' j ip1
          (by intro ⟨h1, _⟩; simp [ip1] at h1; omega)
          (by intro ⟨h1, _⟩; simp [ip1] at h1; omega)
        rw [hvanish, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h

  have hsuper : @inner ℝ _ _ (frenetFrame c hc t i) (deriv e_ip1 t) =
      ‖deriv c t‖ * -(frenetCurvature c hc ⟨i.val, by omega⟩ t) := by
    exact frenetFrame_inner_deriv_super c hc t hn hc' i ip1 ⟨by simp [ip1], by omega⟩

  rw [key, expand_inner, sum_eq, hsuper]
  ring


theorem frenet_diagonal_entry_zero {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (t : ℝ) (hn : 2 ≤ n) (hc' : ‖deriv c t‖ ≠ 0) :
    @inner ℝ _ _ (frenetFrame c hc t ⟨0, by omega⟩) (iteratedDeriv 1 c t) =
    ‖deriv c t‖ := by
  haveI : NeZero n := ⟨by omega⟩

  set f : Fin n → EuclideanSpace ℝ (Fin n) := fun i =>
    if _h : i.val < n - 1 then iteratedDeriv (i.val + 1) c t else 0 with hf_def
  have hf0 : f ⟨0, by omega⟩ = iteratedDeriv 1 c t := by
    simp [f, show (0 : ℕ) < n - 1 from by omega]

  have hgs0 : gramSchmidt ℝ f ⟨0, by omega⟩ = f ⟨0, by omega⟩ := by
    have hempty : Finset.Iio (⟨0, by omega⟩ : Fin n) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro ⟨x, hx⟩
      simp only [Finset.mem_Iio, Fin.lt_def, not_lt, Nat.zero_le]
    rw [gramSchmidt_def, hempty, Finset.sum_empty, sub_zero]
  have hf0_ne : f ⟨0, by omega⟩ ≠ 0 := by
    rw [hf0, iteratedDeriv_one]
    exact fun h => hc' (norm_eq_zero.mpr h)
  have hgsn_ne : gramSchmidtNormed ℝ f ⟨0, by omega⟩ ≠ 0 := by
    simp only [gramSchmidtNormed, hgs0]
    intro h
    have := smul_eq_zero.mp h
    rcases this with hinv | hzero
    · exact absurd (inv_eq_zero.mp hinv) (norm_ne_zero_iff.mpr hf0_ne)
    · exact hf0_ne hzero
  have hframe : frenetFrame c hc t ⟨0, by omega⟩ = gramSchmidtNormed ℝ f ⟨0, by omega⟩ :=
    gramSchmidtOrthonormalBasis_apply finrank_euclideanSpace hgsn_ne
  have hgsn_eq : gramSchmidtNormed ℝ f ⟨0, by omega⟩ = (‖f ⟨0, by omega⟩‖⁻¹ : ℝ) • f ⟨0, by omega⟩ := by
    simp only [gramSchmidtNormed, hgs0]
    norm_cast
  rw [hframe, hgsn_eq, hf0, inner_smul_left, iteratedDeriv_one, real_inner_self_eq_norm_sq]
  simp only [starRingEnd_apply, star_trivial]
  rw [sq, ← mul_assoc, inv_mul_cancel₀ hc', one_mul]

theorem frenet_diagonal_entry {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (t : ℝ) (hn : 2 ≤ n) (hc' : ‖deriv c t‖ ≠ 0)
    (i : Fin n) :
    @inner ℝ _ _ (frenetFrame c hc t i) (iteratedDeriv (i.val + 1) c t) =
    ‖deriv c t‖ ^ (i.val + 1) * ∏ k : Fin i.val,
      frenetCurvature c hc ⟨k.val, by omega⟩ t := by
  obtain ⟨m, hm⟩ := i
  induction m with
  | zero =>
    simp only [Fin.val_mk, Finset.univ_eq_empty, Finset.prod_empty, mul_one,
      show 0 + 1 = 1 from rfl, pow_one]
    exact frenet_diagonal_entry_zero c hc t hn hc'
  | succ m ih =>

    have hstep := frenet_diagonal_entry_succ c hc t hn hc' ⟨m, by omega⟩ (by omega : m + 1 < n)

    have hih := ih (by omega : m < n)

    simp only [Fin.val_mk] at hstep hih ⊢
    rw [hstep, hih]

    rw [show m + 1 + 1 = m + 2 from rfl]
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.last, Fin.val_mk]
    ring


lemma prod_fin_triangular {M : Type*} [CommMonoid M] (n : ℕ) (f : Fin (n - 1) → M) :
    ∏ i : Fin n, ∏ k : Fin i.val, f ⟨k.val, by omega⟩ =
    ∏ k : Fin (n - 1), f k ^ (n - 1 - k.val) := by
  let g : ℕ → M := fun k => if h : k < n - 1 then f ⟨k, h⟩ else 1
  have hlhs : ∏ i : Fin n, ∏ k : Fin i.val, f ⟨k.val, by omega⟩ =
      ∏ i ∈ Finset.range n, ∏ k ∈ Finset.range i, g k := by
    rw [← Fin.prod_univ_eq_prod_range]
    congr 1; ext i
    rw [← Fin.prod_univ_eq_prod_range]
    congr 1; ext k
    simp only [g]
    rw [dif_pos (by omega : k.val < n - 1)]
  have hrhs : ∏ k : Fin (n - 1), f k ^ (n - 1 - k.val) =
      ∏ k ∈ Finset.range (n - 1), g k ^ (n - 1 - k) := by
    rw [← Fin.prod_univ_eq_prod_range]
    congr 1; ext k
    simp only [g]
    rw [dif_pos k.isLt]
  rw [hlhs, hrhs]
  have swap : ∏ i ∈ Finset.range n, ∏ k ∈ Finset.range i, g k =
      ∏ k ∈ Finset.range (n - 1), ∏ i ∈ (Finset.range n).filter (fun i => k < i), g k := by
    apply Finset.prod_comm'
    intro x y
    simp only [Finset.mem_range, Finset.mem_filter]
    omega
  rw [swap]
  congr 1; ext k
  rw [Finset.prod_const]
  congr 1
  have h : Finset.filter (fun i => k < i) (Finset.range n) = Finset.Ico (k + 1) n := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [h, Nat.card_Ico]
  omega

theorem frenet_product_reindex {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (t : ℝ) (hn : 2 ≤ n) :
    ∏ i : Fin n, ∏ k : Fin i.val,
      frenetCurvature c hc ⟨k.val, by omega⟩ t =
    ∏ i : Fin (n - 1), frenetCurvature c hc i t ^ (n - 1 - i.val) :=
  prod_fin_triangular n (fun k => frenetCurvature c hc k t)


theorem frenet_frame_det_one {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (t : ℝ) (hn : 2 ≤ n) (hc' : ‖deriv c t‖ ≠ 0) :
    Matrix.det (Matrix.of (fun k j : Fin n => (frenetFrame c hc t k) j)) = 1 := by sorry


set_option maxHeartbeats 800000 in
theorem frenet_det_factored {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (t : ℝ) (hn : 2 ≤ n) (hc' : ‖deriv c t‖ ≠ 0) :
    Matrix.det (Matrix.of (fun i j : Fin n => iteratedDeriv (i.val + 1) c t j)) =
    ∏ i : Fin n, @inner ℝ _ _ (frenetFrame c hc t i) (iteratedDeriv (i.val + 1) c t) := by
  set b := gramSchmidtOrthonormalBasis (𝕜 := ℝ) finrank_euclideanSpace
    (fun i : Fin n => if _ : i.val < n - 1 then iteratedDeriv (i.val + 1) c t else 0)
  set g : Fin n → EuclideanSpace ℝ (Fin n) := fun i => iteratedDeriv (i.val + 1) c t
  have hframe : ∀ i, frenetFrame c hc t i = b i := fun _ => rfl

  set A : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun i k => @inner ℝ _ _ (b k) (g i))

  set E : Matrix (Fin n) (Fin n) ℝ := Matrix.of (fun k j => (b k) j)

  have hfactor : Matrix.of (fun i j : Fin n => g i j) = A * E := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, A, E]
    have hexp : g i = ∑ k : Fin n, @inner ℝ _ _ (b k) (g i) • (b k) :=
      (b.sum_repr' (g i)).symm
    have h1 : (g i).ofLp j = (∑ k : Fin n, @inner ℝ _ _ (b k) (g i) • (b k)).ofLp j :=
      congrArg (·.ofLp j) hexp
    rw [h1]
    simp [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

  have hdet_mul : Matrix.det (Matrix.of (fun i j : Fin n => g i j)) =
      Matrix.det A * Matrix.det E := by
    rw [hfactor, Matrix.det_mul]

  have hA_lower : A.BlockTriangular OrderDual.toDual := by
    intro i k hki
    simp only [Matrix.of_apply, A]
    have hki' : i.val < k.val := hki
    by_cases hi : i.val < n - 1
    · exact frenetFrame_orthogonal_higher_iteratedDeriv c hc t i k hki' hi
    · exfalso; omega
  have hdet_A : Matrix.det A = ∏ i : Fin n, A i i :=
    Matrix.det_of_lowerTriangular A hA_lower

  have hA_diag : ∀ i : Fin n, A i i =
      @inner ℝ _ _ (frenetFrame c hc t i) (iteratedDeriv (i.val + 1) c t) := by
    intro i; simp only [Matrix.of_apply, A, g, hframe]

  have hdet_E : Matrix.det E = 1 := by
    convert frenet_frame_det_one c hc t hn hc' using 2


  calc Matrix.det (Matrix.of (fun i j : Fin n => iteratedDeriv (i.val + 1) c t j))
      = Matrix.det (Matrix.of (fun i j : Fin n => g i j)) := rfl
    _ = Matrix.det A * Matrix.det E := hdet_mul
    _ = (∏ i : Fin n, A i i) * 1 := by rw [hdet_A, hdet_E]
    _ = ∏ i : Fin n, A i i := by ring
    _ = ∏ i : Fin n, @inner ℝ _ _ (frenetFrame c hc t i) (iteratedDeriv (i.val + 1) c t) :=
        Finset.prod_congr rfl (fun i _ => hA_diag i)

theorem frenet_det_formula {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (t : ℝ) (hn : 2 ≤ n) :
    Matrix.det (Matrix.of (fun i j : Fin n => iteratedDeriv (i.val + 1) c t j)) /
    ‖deriv c t‖ ^ (n * (n + 1) / 2) =
    ∏ i : Fin (n - 1), frenetCurvature c hc i t ^ (n - 1 - i.val) := by
  have hc' : ‖deriv c t‖ ≠ 0 := by
    intro heq
    have hli := hc.2 t
    have hzero : iteratedDeriv 1 c t = 0 := by
      rw [iteratedDeriv_one]; exact norm_eq_zero.mp heq
    exact hli.ne_zero ⟨0, by omega⟩ (by simpa using hzero)
  rw [frenet_det_factored c hc t hn hc']
  simp_rw [frenet_diagonal_entry c hc t hn hc']
  rw [Finset.prod_mul_distrib]
  have hpow : ∏ x : Fin n, ‖deriv c t‖ ^ (x.val + 1) =
      ‖deriv c t‖ ^ (n * (n + 1) / 2) := by
    have h1 : (∑ x : Fin n, (x.val + 1)) = n * (n + 1) / 2 := by
      have haux : ∀ m, 2 * ∑ x : Fin m, (x.val + 1) = m * (m + 1) := by
        intro m; induction m with
        | zero => simp
        | succ k ih =>
          rw [Fin.sum_univ_castSucc]; simp only [Fin.coe_castSucc, Fin.val_last]; linarith [ih]
      have := haux n
      omega
    rw [← h1, Finset.prod_pow_eq_pow_sum]
  rw [hpow, frenet_product_reindex c hc t hn]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ hc')

lemma linearIndependent_of_span_eq {V : Type*} [AddCommGroup V] [Module ℝ V] {k : ℕ}
    (v w : Fin k → V)
    (hv : LinearIndependent ℝ v)
    (heq : Submodule.span ℝ (Set.range w) = Submodule.span ℝ (Set.range v)) :
    LinearIndependent ℝ w := by
  set S := Submodule.span ℝ (Set.range v)
  have hfinrank_S : Module.finrank ℝ S = k := by
    rw [finrank_span_eq_card hv, Fintype.card_fin]
  have hw_mem : ∀ i, w i ∈ S := fun i => by
    have : w i ∈ Submodule.span ℝ (Set.range w) := Submodule.subset_span ⟨i, rfl⟩
    rwa [heq] at this
  set w' : Fin k → S := fun i => ⟨w i, hw_mem i⟩
  have hspan_top : ⊤ ≤ Submodule.span ℝ (Set.range w') := by
    suffices h : ∀ x : S, x ∈ Submodule.span ℝ (Set.range w') from fun x _ => h x
    intro ⟨x, hx⟩
    have hx_in_w : x ∈ Submodule.span ℝ (Set.range w) := heq ▸ hx
    have hrange_le : Set.range w ⊆ S.subtype '' (Set.range w') := by
      rintro y ⟨i, rfl⟩
      exact ⟨w' i, Set.mem_range.mpr ⟨i, rfl⟩, rfl⟩
    have hmono : Submodule.span ℝ (Set.range w) ≤
        (Submodule.span ℝ (Set.range w')).map S.subtype := by
      apply Submodule.span_le.mpr
      intro y hy
      obtain ⟨z, hz, rfl⟩ := hrange_le hy
      exact Submodule.mem_map.mpr ⟨z, Submodule.subset_span hz, rfl⟩
    have hx_mapped := hmono hx_in_w
    rw [Submodule.mem_map] at hx_mapped
    obtain ⟨z, hz, hze⟩ := hx_mapped
    have : z = ⟨x, hx⟩ := Subtype.ext hze
    rw [← this]
    exact hz
  have hli' : LinearIndependent ℝ w' :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan_top
      (by rw [Fintype.card_fin, hfinrank_S])
  exact hli'.map' S.subtype (Submodule.ker_subtype S)

theorem frenet_reparametrization_isFrenet {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (φ : ℝ → ℝ) (hc : IsFrenetCurve c) (hφ : ContDiff ℝ ⊤ φ)
    (hφ' : ∀ t, 0 < deriv φ t) :
    IsFrenetCurve (c ∘ φ) := by
  refine ⟨hc.1.comp hφ, fun t => ?_⟩
  set w := fun i : Fin (n - 1) => iteratedDeriv (i.val + 1) (c ∘ φ) t
  set v := fun i : Fin (n - 1) => iteratedDeriv (i.val + 1) c (φ t)
  have hv_li : LinearIndependent ℝ v := hc.2 (φ t)

  have hle : Submodule.span ℝ (Set.range w) ≤ Submodule.span ℝ (Set.range v) := by
    apply Submodule.span_le.mpr
    rintro x ⟨⟨k, hk⟩, rfl⟩
    show iteratedDeriv (k + 1) (c ∘ φ) t ∈ _
    have hfdb : iteratedDeriv (k + 1) (c ∘ φ) t =
        ∑ p : OrderedFinpartition (k + 1),
          (∏ m : Fin p.length, iteratedDeriv (p.partSize m) φ t) •
          iteratedDeriv p.length c (φ t) :=
      iteratedDeriv_scomp_eq_sum_orderedFinpartition
        (hc.1.contDiffAt) (hφ.contDiffAt) (by simp)
    rw [hfdb]
    apply Submodule.sum_mem
    intro p _
    apply Submodule.smul_mem
    have hlen_pos : 0 < p.length :=
      OrderedFinpartition.length_pos p (by omega : 0 < k + 1)
    have hlen_le : p.length ≤ k + 1 := p.length_le
    exact Submodule.subset_span ⟨⟨p.length - 1, by omega⟩,
      by simp only [v, Nat.sub_one_add_one_eq_of_pos hlen_pos]⟩

  have hge : Submodule.span ℝ (Set.range v) ≤ Submodule.span ℝ (Set.range w) := by
    apply Submodule.span_le.mpr
    rintro x ⟨⟨k, hk⟩, rfl⟩
    show iteratedDeriv (k + 1) c (φ t) ∈ _
    have h := span_iteratedDeriv_comp_ge c φ hc.1 hφ hφ' t k hk
    exact Submodule.span_le.mpr (fun y hy => by
      obtain ⟨⟨j, hj⟩, rfl⟩ := hy
      exact Submodule.subset_span ⟨⟨j, by omega⟩, rfl⟩) h
  exact linearIndependent_of_span_eq v w hv_li (le_antisymm hle hge)


theorem frenetFrame_span_eq {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (t : ℝ) (i : Fin (n - 1)) :
    span ℝ ((fun j : Fin (n - 1) => frenetFrame c hc t ⟨j.val, by omega⟩) '' Iic i) =
    span ℝ ((fun j : Fin (n - 1) => iteratedDeriv (j.val + 1) c t) '' Iic i) := by sorry


theorem frenetFrame_inner_pos {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (hc : IsFrenetCurve c) (t : ℝ) (i : Fin (n - 1)) :
    (0 : ℝ) < @inner ℝ _ _ (frenetFrame c hc t ⟨i.val, by omega⟩)
      (iteratedDeriv (i.val + 1) c t) := by sorry


set_option maxHeartbeats 800000 in
theorem span_iteratedDeriv_comp_eq_Iic {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (φ : ℝ → ℝ) (hc : ContDiff ℝ ⊤ c) (hφ : ContDiff ℝ ⊤ φ)
    (hφ' : ∀ t, 0 < deriv φ t) (t : ℝ) (i : Fin (n - 1)) :
    span ℝ ((fun j : Fin (n - 1) => iteratedDeriv (j.val + 1) (c ∘ φ) t) '' Iic i) =
    span ℝ ((fun j : Fin (n - 1) => iteratedDeriv (j.val + 1) c (φ t)) '' Iic i) := by
  apply le_antisymm
  ·
    apply Submodule.span_le.mpr
    rintro x ⟨k, hk, rfl⟩
    have hk_le := Fin.le_iff_val_le_val.mp (Set.mem_Iic.mp hk)


    show iteratedDeriv (k.val + 1) (c ∘ φ) t ∈ _
    have hfdb : iteratedDeriv (k.val + 1) (c ∘ φ) t =
        ∑ p : OrderedFinpartition (k.val + 1),
          (∏ m : Fin p.length, iteratedDeriv (p.partSize m) φ t) •
          iteratedDeriv p.length c (φ t) :=
      iteratedDeriv_scomp_eq_sum_orderedFinpartition (hc.contDiffAt) (hφ.contDiffAt) (by simp)
    rw [hfdb]
    apply Submodule.sum_mem
    intro p _
    apply Submodule.smul_mem
    have hlen_pos : 0 < p.length := OrderedFinpartition.length_pos p (by omega : 0 < k.val + 1)
    have hlen_le : p.length ≤ k.val + 1 := p.length_le
    apply Submodule.subset_span
    refine ⟨⟨p.length - 1, by omega⟩, Set.mem_Iic.mpr (Fin.mk_le_mk.mpr (by omega)), ?_⟩
    simp only [Nat.sub_one_add_one_eq_of_pos hlen_pos]
  ·
    apply Submodule.span_le.mpr
    rintro x ⟨k, hk, rfl⟩
    have hk_le := Fin.le_iff_val_le_val.mp (Set.mem_Iic.mp hk)
    show iteratedDeriv (k.val + 1) c (φ t) ∈ _
    have h := span_iteratedDeriv_comp_ge c φ hc hφ hφ' t k.val k.isLt


    exact Submodule.span_le.mpr (fun y hy => by
      obtain ⟨⟨j, hj⟩, rfl⟩ := hy
      apply Submodule.subset_span
      exact ⟨⟨j, by omega⟩, Set.mem_Iic.mpr (Fin.mk_le_mk.mpr (by omega)), rfl⟩) h


theorem frenetFrame_inner_pos_reparametrized {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (φ : ℝ → ℝ) (hc : IsFrenetCurve c) (hφ : ContDiff ℝ ⊤ φ)
    (hφ' : ∀ t, 0 < deriv φ t) (t : ℝ) (i : Fin (n - 1)) :
    (0 : ℝ) < @inner ℝ _ _ (frenetFrame c hc (φ t) ⟨i.val, by omega⟩)
      (iteratedDeriv (i.val + 1) (c ∘ φ) t) := by sorry


theorem orthonormalBasis_eq_of_agree_on_prefix {n : ℕ}
    (b₁ b₂ : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
    (h : ∀ i : Fin n, i.val < n - 1 → b₁ i = b₂ i) :
    ∀ i : Fin n, b₁ i = b₂ i := by sorry

set_option maxHeartbeats 400000 in
theorem frenet_frame_reparametrization_invariant {n : ℕ} (c : ℝ → EuclideanSpace ℝ (Fin n))
    (φ : ℝ → ℝ) (hc : IsFrenetCurve c) (hφ : ContDiff ℝ ⊤ φ)
    (hφ' : ∀ t, 0 < deriv φ t) (t : ℝ) :
    frenetFrame (c ∘ φ) (frenet_reparametrization_isFrenet c φ hc hφ hφ') t =
    frenetFrame c hc (φ t) := by
  set hcφ := frenet_reparametrization_isFrenet c φ hc hφ hφ'
  set e₁ : Fin (n - 1) → EuclideanSpace ℝ (Fin n) :=
    fun i => frenetFrame (c ∘ φ) hcφ t ⟨i.val, by omega⟩
  set e₂ : Fin (n - 1) → EuclideanSpace ℝ (Fin n) :=
    fun i => frenetFrame c hc (φ t) ⟨i.val, by omega⟩
  set v : Fin (n - 1) → EuclideanSpace ℝ (Fin n) :=
    fun i => iteratedDeriv (i.val + 1) (c ∘ φ) t
  have hon₁ : Orthonormal ℝ e₁ := by
    have hb := (gramSchmidtOrthonormalBasis finrank_euclideanSpace
      (fun i : Fin n => if _h : i.val < n - 1 then iteratedDeriv (i.val + 1) (c ∘ φ) t else 0)).orthonormal
    exact hb.comp (fun i : Fin (n - 1) => ⟨i.val, by omega⟩)
      (fun a b h => Fin.ext (Fin.mk.inj h))
  have hon₂ : Orthonormal ℝ e₂ := by
    have hb := (gramSchmidtOrthonormalBasis finrank_euclideanSpace
      (fun i : Fin n => if _h : i.val < n - 1 then iteratedDeriv (i.val + 1) c (φ t) else 0)).orthonormal
    exact hb.comp (fun i : Fin (n - 1) => ⟨i.val, by omega⟩)
      (fun a b h => Fin.ext (Fin.mk.inj h))
  have hspan₁ : ∀ i : Fin (n - 1), span ℝ (e₁ '' Iic i) = span ℝ (v '' Iic i) :=
    fun i => frenetFrame_span_eq (c ∘ φ) hcφ t i
  have hspan₂ : ∀ i : Fin (n - 1), span ℝ (e₂ '' Iic i) = span ℝ (v '' Iic i) := by
    intro i
    rw [show e₂ = fun j : Fin (n - 1) => frenetFrame c hc (φ t) ⟨j.val, by omega⟩ from rfl]
    rw [frenetFrame_span_eq c hc (φ t) i]
    exact (span_iteratedDeriv_comp_eq_Iic c φ hc.1 hφ hφ' t i).symm
  have hpos₁ : ∀ i : Fin (n - 1), (0 : ℝ) < @inner ℝ _ _ (e₁ i) (v i) :=
    fun i => frenetFrame_inner_pos (c ∘ φ) hcφ t i
  have hpos₂ : ∀ i : Fin (n - 1), (0 : ℝ) < @inner ℝ _ _ (e₂ i) (v i) :=
    fun i => frenetFrame_inner_pos_reparametrized c φ hc hφ hφ' t i
  have heq_restricted : e₁ = e₂ :=
    gram_schmidt_orthonormalization_unique v e₁ e₂ hon₁ hon₂ hspan₁ hspan₂ hpos₁ hpos₂

  funext i
  exact orthonormalBasis_eq_of_agree_on_prefix
    (gramSchmidtOrthonormalBasis finrank_euclideanSpace
      (fun j : Fin n => if _h : j.val < n - 1 then iteratedDeriv (j.val + 1) (c ∘ φ) t else 0))
    (gramSchmidtOrthonormalBasis finrank_euclideanSpace
      (fun j : Fin n => if _h : j.val < n - 1 then iteratedDeriv (j.val + 1) c (φ t) else 0))
    (fun j hj => congr_fun heq_restricted ⟨j.val, hj⟩) i

end SpaceCurves
