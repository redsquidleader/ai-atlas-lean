/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Convex.Body
open MeasureTheory

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open scoped NNReal

namespace HighDimensional

def IsCLipschitz {α : Type*} {β : Type*} [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]
    (c : ℝ) (f : α → β) : Prop :=
  ∀ u v : α, ‖f u - f v‖ ≤ c * ‖u - v‖

structure IsDEmbedding {X : Type*} [MetricSpace X] [Fintype X] {k : ℕ}
    (D : ℝ) (f : X → EuclideanSpace ℝ (Fin k)) : Prop where
  one_lipschitz : ∀ x y : X, ‖f x - f y‖ ≤ dist x y
  distortion_bound : ∀ x y : X, dist x y ≤ D * ‖f x - f y‖


abbrev UnitSphere (n : ℕ) : Type :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)

instance (n : ℕ) : MeasurableSpace (UnitSphere n) := inferInstance

noncomputable def sphereMeasure (n : ℕ) : Measure (UnitSphere n) :=
  (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere

noncomputable def uniformSphereMeasure (n : ℕ) : Measure (UnitSphere n) :=
  (sphereMeasure n Set.univ)⁻¹ • sphereMeasure n

def IsMedian {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (M : ℝ) : Prop :=
  μ {x | f x ≤ M} ≥ μ Set.univ / 2 ∧ μ {x | f x ≥ M} ≥ μ Set.univ / 2

noncomputable def projFirstK (n k : ℕ) (hk : k ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin k) :=
  (WithLp.equiv 2 (Fin k → ℝ)).symm (fun i => x (Fin.castLE hk i))

noncomputable def normProjFirstK (n k : ℕ) (hk : k ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖projFirstK n k hk x‖

noncomputable def sphereProjNorm (n k : ℕ) (hk : k ≤ n) :
    UnitSphere n → ℝ :=
  fun x => normProjFirstK n k hk (x : EuclideanSpace ℝ (Fin n))

theorem projFirstK_lipschitz (n k : ℕ) (hk : k ≤ n)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ‖projFirstK n k hk x - projFirstK n k hk y‖ ≤ ‖x - y‖ := by
  simp only [EuclideanSpace.norm_eq, projFirstK]
  apply Real.sqrt_le_sqrt
  have hLHS : ∀ i : Fin k,
    (((WithLp.equiv 2 (Fin k → ℝ)).symm fun j => x (Fin.castLE hk j)) -
     (WithLp.equiv 2 (Fin k → ℝ)).symm fun j => y (Fin.castLE hk j)).ofLp i =
    x (Fin.castLE hk i) - y (Fin.castLE hk i) := by
    intro i; simp [WithLp.equiv, PiLp.sub_apply]
  have hRHS : ∀ j : Fin n, (x - y).ofLp j = x j - y j := by
    intro j; simp [PiLp.sub_apply]
  simp_rw [hLHS, hRHS]
  have h1 : ∑ i : Fin k, ‖x (Fin.castLE hk i) - y (Fin.castLE hk i)‖ ^ 2 =
    ∑ j ∈ Finset.univ.map (Fin.castLEEmb hk), ‖x j - y j‖ ^ 2 := by
    rw [Finset.sum_map]; simp [Fin.castLEEmb]
  rw [h1]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.subset_univ _
  · intro i _ _; positivity

theorem sphereProjNorm_lipschitzWith (n k : ℕ) (hk : k ≤ n) :
    LipschitzWith 1 (sphereProjNorm n k hk) := by
  apply LipschitzWith.mk_one
  intro x y
  simp only [sphereProjNorm, normProjFirstK]
  rw [Real.dist_eq]
  calc |‖projFirstK n k hk ↑x‖ - ‖projFirstK n k hk ↑y‖|
      ≤ ‖projFirstK n k hk ↑x - projFirstK n k hk ↑y‖ := abs_norm_sub_norm_le _ _
    _ ≤ ‖(↑x : EuclideanSpace ℝ (Fin n)) - ↑y‖ := projFirstK_lipschitz n k hk ↑x ↑y
    _ = dist x y := by rw [Subtype.dist_eq, dist_eq_norm]


theorem isoperimetric_sphere_one_sided
  (n : ℕ) (ε : ℝ) (hε : 0 < ε)
  (A : Set (UnitSphere n))
  (hA : uniformSphereMeasure n A ≥ uniformSphereMeasure n Set.univ / 2) :
  uniformSphereMeasure n (Metric.cthickening ε A)ᶜ ≤
    ENNReal.ofReal (Real.exp (-(↑n * ε ^ 2 / 2))) := by sorry

theorem cthickening_sublevel_of_lipschitz {α : Type*} [PseudoMetricSpace α]
    (f : α → ℝ) (hf : LipschitzWith 1 f)
    (M ε : ℝ) (hε : 0 ≤ ε)
    (hne : {x | f x ≤ M}.Nonempty) :
    Metric.cthickening ε {x | f x ≤ M} ⊆ {x | f x ≤ M + ε} := by
  intro y hy
  simp only [Set.mem_setOf_eq]
  have hinfDist : Metric.infDist y {x | f x ≤ M} ≤ ε := by
    rw [Metric.mem_cthickening_iff] at hy
    have h1 : Metric.infEDist y {x | f x ≤ M} ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy
    calc Metric.infDist y {x | f x ≤ M}
        = (Metric.infEDist y {x | f x ≤ M}).toReal := rfl
      _ ≤ (ENNReal.ofReal ε).toReal :=
          (ENNReal.toReal_le_toReal h1 ENNReal.ofReal_ne_top).mpr hy
      _ = ε := ENNReal.toReal_ofReal hε
  have hbound : f y ≤ M + Metric.infDist y {x | f x ≤ M} := by
    have hNonempty : Nonempty ↥{x | f x ≤ M} := hne.to_subtype
    rw [Metric.infDist_eq_iInf]
    suffices h : ∀ a : ↥{x | f x ≤ M}, f y - M ≤ dist y (a : α) by
      linarith [le_ciInf h]
    intro ⟨a, ha⟩
    simp only [Set.mem_setOf_eq] at ha
    have hLip : dist (f y) (f a) ≤ dist y a := by
      have := hf.dist_le_mul y a; simp at this; exact this
    linarith [show f y - f a ≤ dist y a from
      (le_abs_self _).trans ((Real.dist_eq _ _).symm ▸ hLip)]
  linarith

theorem cthickening_superlevel_of_lipschitz {α : Type*} [PseudoMetricSpace α]
    (f : α → ℝ) (hf : LipschitzWith 1 f)
    (M ε : ℝ) (hε : 0 ≤ ε)
    (hne : {x | f x ≥ M}.Nonempty) :
    Metric.cthickening ε {x | f x ≥ M} ⊆ {x | f x ≥ M - ε} := by
  intro y hy
  simp only [Set.mem_setOf_eq]
  have hinfDist : Metric.infDist y {x | f x ≥ M} ≤ ε := by
    rw [Metric.mem_cthickening_iff] at hy
    have h1 : Metric.infEDist y {x | f x ≥ M} ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hy
    calc Metric.infDist y {x | f x ≥ M}
        = (Metric.infEDist y {x | f x ≥ M}).toReal := rfl
      _ ≤ (ENNReal.ofReal ε).toReal :=
          (ENNReal.toReal_le_toReal h1 ENNReal.ofReal_ne_top).mpr hy
      _ = ε := ENNReal.toReal_ofReal hε
  have hbound : f y ≥ M - Metric.infDist y {x | f x ≥ M} := by
    have hNonempty : Nonempty ↥{x | f x ≥ M} := hne.to_subtype
    rw [Metric.infDist_eq_iInf]
    suffices h : ∀ a : ↥{x | f x ≥ M}, M - f y ≤ dist y (a : α) by
      linarith [le_ciInf h]
    intro ⟨a, ha⟩
    simp only [Set.mem_setOf_eq] at ha
    have hLip : dist (f y) (f a) ≤ dist y a := by
      have := hf.dist_le_mul y a; simp at this; exact this
    linarith [show f a - f y ≤ dist y a from
      (show f a - f y ≤ |f y - f a| by linarith [neg_abs_le (f y - f a)]).trans
        ((Real.dist_eq _ _).symm ▸ hLip)]
  linarith

theorem concentration_lipschitz_sphere (n : ℕ) (f : UnitSphere n → ℝ)
    (hf : LipschitzWith 1 f) (M : ℝ)
    (hM : IsMedian (uniformSphereMeasure n) f M)
    (ε : ℝ) (hε : 0 < ε)
    (hne_low : {x : UnitSphere n | f x ≤ M}.Nonempty)
    (hne_high : {x : UnitSphere n | f x ≥ M}.Nonempty) :
    uniformSphereMeasure n {x | ε < |f x - M|} ≤
      ENNReal.ofReal (2 * Real.exp (-(↑n * ε ^ 2 / 2))) := by

  have hsub : {x : UnitSphere n | ε < |f x - M|} ⊆
      {x | M + ε < f x} ∪ {x | f x < M - ε} := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rcases abs_cases (f x - M) with ⟨h1, _⟩ | ⟨h1, _⟩
    · left; linarith
    · right; linarith

  have hup : uniformSphereMeasure n {x | M + ε < f x} ≤
      ENNReal.ofReal (Real.exp (-(↑n * ε ^ 2 / 2))) := by
    have hsub2 : {x : UnitSphere n | M + ε < f x} ⊆
        (Metric.cthickening ε {x | f x ≤ M})ᶜ := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hx ⊢
      intro habs
      have := cthickening_sublevel_of_lipschitz f hf M ε hε.le hne_low habs
      simp only [Set.mem_setOf_eq] at this
      linarith
    calc uniformSphereMeasure n {x | M + ε < f x}
        ≤ uniformSphereMeasure n (Metric.cthickening ε {x | f x ≤ M})ᶜ :=
          measure_mono hsub2
      _ ≤ ENNReal.ofReal (Real.exp (-(↑n * ε ^ 2 / 2))) :=
          isoperimetric_sphere_one_sided n ε hε _ hM.1

  have hlow : uniformSphereMeasure n {x | f x < M - ε} ≤
      ENNReal.ofReal (Real.exp (-(↑n * ε ^ 2 / 2))) := by
    have hsub3 : {x : UnitSphere n | f x < M - ε} ⊆
        (Metric.cthickening ε {x | f x ≥ M})ᶜ := by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hx ⊢
      intro habs
      have := cthickening_superlevel_of_lipschitz f hf M ε hε.le hne_high habs
      simp only [Set.mem_setOf_eq] at this
      linarith
    calc uniformSphereMeasure n {x | f x < M - ε}
        ≤ uniformSphereMeasure n (Metric.cthickening ε {x | f x ≥ M})ᶜ :=
          measure_mono hsub3
      _ ≤ ENNReal.ofReal (Real.exp (-(↑n * ε ^ 2 / 2))) :=
          isoperimetric_sphere_one_sided n ε hε _ hM.2

  have hexp_pos : (0 : ℝ) ≤ Real.exp (-(↑n * ε ^ 2 / 2)) := Real.exp_nonneg _
  calc uniformSphereMeasure n {x | ε < |f x - M|}
      ≤ uniformSphereMeasure n ({x | M + ε < f x} ∪ {x | f x < M - ε}) :=
        measure_mono hsub
    _ ≤ uniformSphereMeasure n {x | M + ε < f x} +
        uniformSphereMeasure n {x | f x < M - ε} :=
        measure_union_le _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(↑n * ε ^ 2 / 2))) +
        ENNReal.ofReal (Real.exp (-(↑n * ε ^ 2 / 2))) :=
        add_le_add hup hlow
    _ = ENNReal.ofReal (2 * Real.exp (-(↑n * ε ^ 2 / 2))) := by
        rw [two_mul, ENNReal.ofReal_add hexp_pos hexp_pos]

theorem concentration_projection_sphere
  (n k : ℕ) (hk : k ≤ n)
  (M : ℝ) (hM : IsMedian (uniformSphereMeasure n) (sphereProjNorm n k hk) M)
  (t : ℝ) (ht : 0 < t)
  (hne_low : {x : UnitSphere n | sphereProjNorm n k hk x ≤ M}.Nonempty)
  (hne_high : {x : UnitSphere n | sphereProjNorm n k hk x ≥ M}.Nonempty) :
  uniformSphereMeasure n {x | t < |sphereProjNorm n k hk x - M|} ≤
    ENNReal.ofReal (2 * Real.exp (-(t ^ 2 * ↑n / 2))) := by
  have hlip := sphereProjNorm_lipschitzWith n k hk
  have h := concentration_lipschitz_sphere n (sphereProjNorm n k hk) hlip M hM t ht
    hne_low hne_high
  convert h using 2
  ring_nf


theorem sphere_shell_bm_bound
    (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (A : Set (UnitSphere n))
    (hA : uniformSphereMeasure n A ≠ 0)
    (hA_small : uniformSphereMeasure n A < uniformSphereMeasure n Set.univ / 2) :
    uniformSphereMeasure n (Metric.thickening ε A)ᶜ ≤
      ENNReal.ofReal (2 * Real.exp (-(↑n * ε ^ 2 / 16))) /
      uniformSphereMeasure n A := by sorry

theorem isoperimetric_sphere_weak
    (n : ℕ) (ε : ℝ) (hε : 0 < ε)
    (A : Set (UnitSphere n))
    (hA : uniformSphereMeasure n A ≠ 0) :
    uniformSphereMeasure n (Metric.thickening ε A)ᶜ ≤
      ENNReal.ofReal (2 * Real.exp (-(↑n * ε ^ 2 / 16))) /
      uniformSphereMeasure n A := by
  set μ := uniformSphereMeasure n

  by_cases hA_large : μ A ≥ μ Set.univ / 2
  ·


    have h_one_sided := isoperimetric_sphere_one_sided n (ε / 2) (half_pos hε) A hA_large

    have h_subset : Metric.cthickening (ε / 2) A ⊆ Metric.thickening ε A :=
      Metric.cthickening_subset_thickening' hε (by linarith) A
    have h_compl : (Metric.thickening ε A)ᶜ ⊆ (Metric.cthickening (ε / 2) A)ᶜ :=
      Set.compl_subset_compl.mpr h_subset

    have h_meas_le : μ (Metric.thickening ε A)ᶜ ≤
        ENNReal.ofReal (Real.exp (-(↑n * (ε / 2) ^ 2 / 2))) :=
      (measure_mono h_compl).trans h_one_sided


    calc μ (Metric.thickening ε A)ᶜ
        ≤ ENNReal.ofReal (Real.exp (-(↑n * (ε / 2) ^ 2 / 2))) := h_meas_le
      _ ≤ ENNReal.ofReal (2 * Real.exp (-(↑n * ε ^ 2 / 16))) / μ A := by
          rw [ENNReal.le_div_iff_mul_le (Or.inl hA) (Or.inr ENNReal.ofReal_ne_top)]


          have hμA_le : μ A ≤ 1 := by
            have hfin : IsFiniteMeasure (sphereMeasure n) :=
              inferInstanceAs (IsFiniteMeasure (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
            have h_ne_top : sphereMeasure n Set.univ ≠ ⊤ := (hfin.measure_univ_lt_top).ne
            have : μ A ≤ μ Set.univ := measure_mono (Set.subset_univ _)
            calc μ A ≤ μ Set.univ := this
              _ = (sphereMeasure n Set.univ)⁻¹ * sphereMeasure n Set.univ := by
                  show ((sphereMeasure n Set.univ)⁻¹ • sphereMeasure n) Set.univ = _
                  simp [Measure.smul_apply]
              _ ≤ 1 := by
                  by_cases h0 : sphereMeasure n Set.univ = 0
                  · simp [h0]
                  · rw [ENNReal.inv_mul_cancel h0 h_ne_top]
          have h_real_le : Real.exp (-(↑n * (ε / 2) ^ 2 / 2)) ≤
              2 * Real.exp (-(↑n * ε ^ 2 / 16)) := by
            have h_eq : ↑n * (ε / 2) ^ 2 / 2 = ↑n * ε ^ 2 / 8 := by ring
            rw [h_eq]
            have h_exp_le : Real.exp (-(↑n * ε ^ 2 / 8)) ≤
                Real.exp (-(↑n * ε ^ 2 / 16)) := by
              apply Real.exp_le_exp.mpr
              have : (0 : ℝ) ≤ ↑n * ε ^ 2 := by positivity
              linarith
            linarith [Real.exp_pos (-(↑n * ε ^ 2 / 16))]
          calc ENNReal.ofReal (Real.exp (-(↑n * (ε / 2) ^ 2 / 2))) * μ A
              ≤ ENNReal.ofReal (Real.exp (-(↑n * (ε / 2) ^ 2 / 2))) * 1 := by
                gcongr
            _ = ENNReal.ofReal (Real.exp (-(↑n * (ε / 2) ^ 2 / 2))) := mul_one _
            _ ≤ ENNReal.ofReal (2 * Real.exp (-(↑n * ε ^ 2 / 16))) :=
                ENNReal.ofReal_le_ofReal h_real_le
  ·
    exact sphere_shell_bm_bound n ε hε A hA (not_le.mp hA_large)


theorem jl_probabilistic_method
    (d n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (S : Fin n → EuclideanSpace ℝ (Fin d))
    (hd : 72 * ε⁻¹ ^ 2 * Real.log ↑n + 1 < (d : ℝ)) :
    ∃ (k : ℕ),
    (k : ℝ) ≤ 72 * ε⁻¹ ^ 2 * Real.log ↑n + 1 ∧
    ∃ (f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)),
    ∀ i j : Fin n,
      ‖S i - S j‖ ≤ ‖f (S i) - f (S j)‖ ∧
      ‖f (S i) - f (S j)‖ ≤ (1 + ε) * ‖S i - S j‖ := by sorry

theorem johnson_lindenstrauss
    (d n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (S : Fin n → EuclideanSpace ℝ (Fin d)) :
    ∃ (k : ℕ),
    (k : ℝ) ≤ 72 * ε⁻¹ ^ 2 * Real.log ↑n + 1 ∧
    ∃ (f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)),
    ∀ i j : Fin n,
      ‖S i - S j‖ ≤ ‖f (S i) - f (S j)‖ ∧
      ‖f (S i) - f (S j)‖ ≤ (1 + ε) * ‖S i - S j‖ := by

  by_cases hd : (d : ℝ) ≤ 72 * ε⁻¹ ^ 2 * Real.log ↑n + 1
  ·
    refine ⟨d, hd, LinearMap.id, fun i j => ⟨le_refl _, ?_⟩⟩
    simp only [LinearMap.id_apply]
    have h_norm := norm_nonneg (S i - S j)
    nlinarith
  ·
    push Not at hd
    exact jl_probabilistic_method d n hn ε hε hε1 S hd


theorem dvoretzky_theorem :
  ∃ c : ℝ, c > 0 ∧ ∀ (n : ℕ) (hn : 2 ≤ n) (ε : ℝ) (hε : 0 < ε)
    (C : ConvexBody (EuclideanSpace ℝ (Fin n)))
    (hC_symm : ∀ x ∈ (C : Set (EuclideanSpace ℝ (Fin n))),
      -x ∈ (C : Set (EuclideanSpace ℝ (Fin n)))),
    ∃ (k : ℕ) (S : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
      (hS : Module.finrank ℝ S = k)
      (T : S ≃ₗ[ℝ] EuclideanSpace ℝ (Fin k)),
      (Metric.closedBall 0 1 : Set (EuclideanSpace ℝ (Fin k))) ⊆
        T '' (Subtype.val ⁻¹' (C : Set (EuclideanSpace ℝ (Fin n)))) ∧
      T '' (Subtype.val ⁻¹' (C : Set (EuclideanSpace ℝ (Fin n)))) ⊆
        Metric.closedBall 0 (1 + ε) ∧
      (k : ℝ) ≥ c * ε ^ 2 / Real.log (1 + ε⁻¹) * Real.log n := by sorry

end HighDimensional

open ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace ChernoffHoeffding

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]


def IsBoundedUnitInterval (X : Ω → ℝ) (μ : Measure Ω) : Prop :=
  Measurable X ∧ ∀ᵐ ω ∂μ, 0 ≤ X ω ∧ X ω ≤ 1


theorem chernoff_bound_unit_interval
  {n : ℕ}
  (X : Fin n → Ω → ℝ)
  (hBound : ∀ i, IsBoundedUnitInterval (X i) μ)
  (hIndep : iIndepFun X μ)
  (ε : ℝ) (hε : 0 < ε) :
  ∃ c : ℝ, c > 0 ∧
    μ {ω | |∑ i : Fin n, X i ω - ∫ ω', ∑ i : Fin n, X i ω' ∂μ| ≥
       ε * (∑ i : Fin n, X i ω)} ≤
      ENNReal.ofReal (2 * Real.exp (-c * ε ^ 2 * (∫ ω', ∑ i : Fin n, X i ω' ∂μ))) := by sorry

end ChernoffHoeffding

open scoped InnerProductSpace
open Finset
