/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialGeometry.code.PlaneCurves
import Atlas.DifferentialGeometry.code.Reparametrization
import Atlas.DifferentialGeometry.code.DegreeTheory

noncomputable section

open Finset BigOperators MeasureTheory

namespace ClosedCurves

structure IsClosedCurve (c : ℝ → Fin 2 → ℝ) (T : ℝ) : Prop where
  smooth : ContDiff ℝ ⊤ c
  period_pos : T > 0
  periodic : ∀ t, c (t + T) = c t
  regular : ∀ t, deriv c t ≠ 0

def IsSimpleClosedCurve (c : ℝ → Fin 2 → ℝ) (T : ℝ) : Prop :=
  IsClosedCurve c T ∧ ∀ s t, 0 ≤ s → s < t → t < T → c s ≠ c t

def IsConvexCurve (c : ℝ → Fin 2 → ℝ) (T : ℝ) : Prop :=
  IsSimpleClosedCurve c T ∧
  ∀ (a : Fin 2 → ℝ) (b : ℝ) (t₀ : ℝ),

    (∑ i, a i * c t₀ i) = b →

    (∑ i, a i * deriv c t₀ i) = 0 →

    (∀ t, (∑ i, a i * c t i) ≤ b) ∨ (∀ t, (∑ i, a i * c t i) ≥ b)

def toEuclidean (c : ℝ → Fin 2 → ℝ) : ℝ → EuclideanSpace ℝ (Fin 2) :=
  fun t => (EuclideanSpace.equiv (Fin 2) ℝ).symm (c t)

def curvature (c : ℝ → Fin 2 → ℝ) (t : ℝ) : ℝ :=
  PlaneCurves.curvature (toEuclidean c) t

def totalCurvature (c : ℝ → Fin 2 → ℝ) (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, curvature c t * ‖deriv (toEuclidean c) t‖

theorem jordan_curve_theorem :
  ∀ (c : ℝ → Fin 2 → ℝ) (T : ℝ),
    IsSimpleClosedCurve c T →
    ∃ (U V : Set (Fin 2 → ℝ)),
      IsOpen U ∧ IsOpen V ∧
      IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧
      U ∪ V = (Set.range c)ᶜ ∧
      Bornology.IsBounded U ∧ ¬Bornology.IsBounded V := by sorry


theorem toEuclidean_deriv_norm (c : ℝ → Fin 2 → ℝ) (hc : ContDiff ℝ ⊤ c) (t : ℝ) :
    ‖deriv (toEuclidean c) t‖ = ‖deriv c t‖ := by sorry


theorem curvature_comp_reparam (c : ℝ → Fin 2 → ℝ) (φ : ℝ → ℝ)
    (hc : ContDiff ℝ ⊤ c) (hφ : ContDiff ℝ ⊤ φ)
    (hφ_pos : ∀ t, 0 < deriv φ t)
    (hreg : ∀ t, deriv c (φ t) ≠ 0) (t : ℝ) :
    curvature (c ∘ φ) t = curvature c (φ t) := by sorry


theorem totalCurvature_integrand_periodic (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : ContDiff ℝ ⊤ c) (hperiodic : ∀ t, c (t + T) = c t) :
    Function.Periodic (fun t => curvature c t * ‖deriv (toEuclidean c) t‖) T := by sorry


theorem curvature_comp_continuous (c : ℝ → Fin 2 → ℝ) (φ : ℝ → ℝ)
    (hc : ContDiff ℝ ⊤ c) (hφ : ContDiff ℝ ⊤ φ)
    (hreg : ∀ s, deriv c (φ s) ≠ 0) :
    Continuous (fun s => curvature c (φ s)) := by sorry

theorem totalCurvature_reparam_eq
    (c : ℝ → Fin 2 → ℝ) (φ ψ : ℝ → ℝ) (T : ℝ)
    (hc_smooth : ContDiff ℝ ⊤ c) (hφ_smooth : ContDiff ℝ ⊤ φ)
    (hψ_smooth : ContDiff ℝ ⊤ ψ)
    (hφ_left : Function.LeftInverse φ ψ)
    (hφ_right : Function.RightInverse φ ψ)
    (hψ_deriv : ∀ t, deriv ψ t = ‖deriv c t‖)
    (hψ_pos : ∀ t, 0 < deriv ψ t)
    (hψ_periodic_shift : ∀ t, ψ (t + T) = ψ t + (∫ u in (0 : ℝ)..T, ‖deriv c u‖))
    (hd_unit : ∀ t, ‖deriv (c ∘ φ) t‖ = 1)
    (hc_periodic : ∀ t, c (t + T) = c t) :
    totalCurvature (c ∘ φ) (∫ u in (0 : ℝ)..T, ‖deriv c u‖) = totalCurvature c T := by
  set L := ∫ u in (0 : ℝ)..T, ‖deriv c u‖

  have hφ_pos : ∀ s, 0 < deriv φ s := by
    intro s
    have h1 : ψ (φ s) = s := hφ_right s
    have hψ_diff : DifferentiableAt ℝ ψ (φ s) :=
      (hψ_smooth.differentiable (by simp)).differentiableAt
    have hφ_diff : DifferentiableAt ℝ φ s :=
      (hφ_smooth.differentiable (by simp)).differentiableAt
    have hchain : deriv ψ (φ s) * deriv φ s = 1 := by
      have hid : deriv (ψ ∘ φ) s = 1 := by
        have : (ψ ∘ φ) = id := funext hφ_right
        rw [this, deriv_id']
      have hcomp : deriv (ψ ∘ φ) s = deriv φ s • deriv ψ (φ s) :=
        deriv.scomp s hψ_diff hφ_diff
      rw [hcomp, smul_eq_mul, mul_comm] at hid
      exact hid
    have h3 : deriv ψ (φ s) > 0 := hψ_pos (φ s)
    nlinarith [mul_pos_iff.mp (by linarith : (0:ℝ) < deriv ψ (φ s) * deriv φ s)]

  have hreg : ∀ s, deriv c (φ s) ≠ 0 := by
    intro s h
    have := hd_unit s
    have hc_diff : DifferentiableAt ℝ c (φ s) :=
      (hc_smooth.differentiable (by simp)).differentiableAt
    have hφ_diff : DifferentiableAt ℝ φ s :=
      (hφ_smooth.differentiable (by simp)).differentiableAt
    rw [show deriv (c ∘ φ) s = deriv φ s • deriv c (φ s) from
      deriv.scomp s hc_diff hφ_diff, h, smul_zero, norm_zero] at this
    linarith


  have hunit_eucl : ∀ s, ‖deriv (toEuclidean (c ∘ φ)) s‖ = 1 := by
    intro s
    rw [toEuclidean_deriv_norm (c ∘ φ) (hc_smooth.comp hφ_smooth) s]
    exact hd_unit s

  have hLHS_eq : ∀ s, curvature (c ∘ φ) s * ‖deriv (toEuclidean (c ∘ φ)) s‖ =
      curvature c (φ s) := by
    intro s
    rw [hunit_eucl s, mul_one, curvature_comp_reparam c φ hc_smooth hφ_smooth hφ_pos hreg s]

  have hLHS : totalCurvature (c ∘ φ) L = ∫ s in (0:ℝ)..L, curvature c (φ s) := by
    unfold totalCurvature
    congr 1; ext s; exact hLHS_eq s


  have hRHS_integrand : ∀ t, curvature c t * ‖deriv (toEuclidean c) t‖ =
      (fun s => curvature c (φ s)) (ψ t) * deriv ψ t := by
    intro t
    simp only [Function.comp, hφ_left t]
    rw [toEuclidean_deriv_norm c hc_smooth t, hψ_deriv]

  have hψ0 : ψ (φ 0) = 0 := hφ_right 0
  have hψT : ψ (φ 0 + T) = L := by
    have := hψ_periodic_shift (φ 0); rw [hψ0] at this; linarith

  have hperiodic := totalCurvature_integrand_periodic c T hc_smooth hc_periodic
  have hshift : (∫ t in (0:ℝ)..T, curvature c t * ‖deriv (toEuclidean c) t‖) =
      ∫ t in φ 0..φ 0 + T, curvature c t * ‖deriv (toEuclidean c) t‖ := by
    have h := hperiodic.intervalIntegral_add_eq (φ 0) 0
    simp only [zero_add] at h; exact h.symm

  have hsubst : (∫ t in φ 0..φ 0 + T, curvature c t * ‖deriv (toEuclidean c) t‖) =
      ∫ s in (0:ℝ)..L, curvature c (φ s) := by
    have hcov := intervalIntegral.integral_comp_mul_deriv
      (f := ψ) (f' := deriv ψ) (g := fun s => curvature c (φ s))
      (a := φ 0) (b := φ 0 + T)
      (fun x _ => (hψ_smooth.differentiable (by simp)).differentiableAt.hasDerivAt)
      (hψ_smooth.continuous_deriv (by simp) |>.continuousOn)
      (by exact curvature_comp_continuous c φ hc_smooth hφ_smooth hreg)
    simp only [Function.comp, hφ_left] at hcov
    conv_lhs =>
      rw [show (∫ t in φ 0..φ 0 + T, curvature c t * ‖deriv (toEuclidean c) t‖) =
          ∫ t in φ 0..φ 0 + T, (fun s => curvature c (φ s)) (ψ t) * deriv ψ t from by
        congr 1; ext t; exact hRHS_integrand t]
    rw [hcov, hψ0, hψT]

  rw [hLHS]
  unfold totalCurvature
  rw [hshift, hsubst]

lemma deriv_periodic_of_closed (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsClosedCurve c T) : ∀ t, deriv c (t + T) = deriv c t := by
  intro t
  have heq : (fun s => c (s + T)) = c := by
    funext s; exact hc.periodic s
  have hcdiff : Differentiable ℝ c := hc.smooth.differentiable (by simp)
  have h1 : deriv (fun s => c (s + T)) t = deriv c (t + T) := by
    have hd : HasDerivAt (fun s => c (s + T)) (deriv c (t + T)) t := by
      have hc_at : HasDerivAt c (deriv c (t + T)) (t + T) := hcdiff.differentiableAt.hasDerivAt
      have hadd : HasDerivAt (· + T) 1 t := (hasDerivAt_id t).add_const T
      have hcomp := hc_at.scomp t hadd
      simpa [Function.comp] using hcomp
    exact hd.deriv
  rw [← h1, heq]

lemma norm_deriv_periodic_of_closed (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsClosedCurve c T) : ∀ t, ‖deriv c (t + T)‖ = ‖deriv c t‖ := by
  intro t; rw [deriv_periodic_of_closed c T hc t]

theorem unit_speed_reparam_closed (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsClosedCurve c T) :
    let L := ∫ t in (0 : ℝ)..T, ‖deriv c t‖
    ∃ (d : ℝ → Fin 2 → ℝ), IsClosedCurve d L ∧
      (∀ t, ‖deriv d t‖ = 1) ∧
      totalCurvature d L = totalCurvature c T := by
  intro L

  have hreg : ∀ t, deriv c t ≠ 0 := hc.regular
  obtain ⟨ψ, hψ_smooth, hψ_deriv⟩ :=
    Reparametrization.exists_smooth_arclength c hc.smooth hreg

  have hψ_pos : ∀ t, 0 < deriv ψ t := by
    intro t; rw [hψ_deriv]; exact norm_pos_iff.mpr (hreg t)

  obtain ⟨hinj, φ, hφ_left, hφ_right, hφ_smooth, hφ_deriv⟩ :=
    Reparametrization.smooth_increasing_has_smooth_inverse_global ψ hψ_smooth hψ_pos

  set d := c ∘ φ

  have hd_unit : ∀ t, ‖deriv d t‖ = 1 := by
    intro t
    have hc_diff : DifferentiableAt ℝ c (φ t) :=
      (hc.smooth.differentiable (by simp)).differentiableAt
    have hφ_diff : DifferentiableAt ℝ φ t :=
      (hφ_smooth.differentiable (by simp)).differentiableAt
    show ‖deriv (c ∘ φ) t‖ = 1
    rw [deriv.scomp t hc_diff hφ_diff, norm_smul]
    have h_eq : deriv φ t = ‖deriv c (φ t)‖⁻¹ := by
      conv_lhs => rw [show t = ψ (φ t) from (hφ_right t).symm]
      rw [hφ_deriv, hψ_deriv]
    rw [h_eq, Real.norm_eq_abs, abs_of_pos (inv_pos_of_pos (norm_pos_iff.mpr (hreg _)))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hreg _))


  have hψ_periodic_shift : ∀ t, ψ (t + T) = ψ t + L := by

    set g : ℝ → ℝ := fun t => ψ (t + T) - ψ t
    have hg_diff : Differentiable ℝ g := by
      intro x
      exact ((hψ_smooth.differentiable (by simp)).comp
        (differentiable_id.add (differentiable_const T))).differentiableAt.sub
        (hψ_smooth.differentiable (by simp)).differentiableAt
    have hg_deriv_zero : ∀ x, deriv g x = 0 := by
      intro x
      have hd1 : HasDerivAt (fun t => ψ (t + T)) (deriv ψ (x + T)) x := by
        have hψ_at : HasDerivAt ψ (deriv ψ (x + T)) (x + T) :=
          (hψ_smooth.differentiable (by simp)).differentiableAt.hasDerivAt
        have hadd : HasDerivAt (· + T) 1 x := (hasDerivAt_id x).add_const T
        have hcomp := hψ_at.comp x hadd
        simpa [Function.comp] using hcomp

      have hd2 : HasDerivAt ψ (deriv ψ x) x :=
        (hψ_smooth.differentiable (by simp)).differentiableAt.hasDerivAt
      have hd3 : HasDerivAt g (deriv ψ (x + T) - deriv ψ x) x := hd1.sub hd2
      rw [hψ_deriv, hψ_deriv, norm_deriv_periodic_of_closed c T hc x, sub_self] at hd3
      exact hd3.deriv

    have hg_const : ∀ a b, g a = g b := is_const_of_deriv_eq_zero hg_diff hg_deriv_zero


    intro t
    have hg_eq : g t = g 0 := hg_const t 0

    show ψ (t + T) = ψ t + L
    have hgt : g t = ψ (t + T) - ψ t := rfl
    have hg0 : g 0 = ψ T - ψ 0 := by simp [g]

    have hftc : ∫ u in (0 : ℝ)..T, deriv ψ u = ψ T - ψ 0 := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => (hψ_smooth.differentiable (by simp)).differentiableAt.hasDerivAt)
        ((hψ_smooth.continuous_deriv (by simp)).intervalIntegrable 0 T)

    have hL_eq : L = ψ T - ψ 0 := by
      have : L = ∫ u in (0 : ℝ)..T, ‖deriv c u‖ := rfl
      rw [this, show (∫ u in (0 : ℝ)..T, ‖deriv c u‖) = ∫ u in (0 : ℝ)..T, deriv ψ u from by
        congr 1; ext u; exact (hψ_deriv u).symm]
      exact hftc
    linarith [hg_eq, hgt, hg0, hL_eq]

  have hφ_periodic_shift : ∀ s, φ (s + L) = φ s + T := by
    intro s
    have h1 : ψ (φ s + T) = ψ (φ s) + L := hψ_periodic_shift (φ s)
    have h2 : ψ (φ s) = s := hφ_right s
    have h3 : ψ (φ s + T) = s + L := by linarith
    have h4 : ψ (φ (s + L)) = s + L := hφ_right (s + L)
    exact hinj (h4.trans h3.symm)

  have hd_periodic : ∀ s, d (s + L) = d s := by
    intro s
    show c (φ (s + L)) = c (φ s)
    rw [hφ_periodic_shift s]
    exact hc.periodic (φ s)

  have hL_pos : L > 0 := by
    have hψ_strict_mono : StrictMono ψ := strictMono_of_deriv_pos hψ_pos
    have h_lt : ψ 0 < ψ T := hψ_strict_mono hc.period_pos
    have h_shift := hψ_periodic_shift 0
    simp at h_shift
    linarith

  have hd_smooth : ContDiff ℝ ⊤ d := hc.smooth.comp hφ_smooth

  have hd_regular : ∀ t, deriv d t ≠ 0 := by
    intro t h
    have := hd_unit t
    rw [h, norm_zero] at this
    exact one_ne_zero this.symm

  have hd_closed : IsClosedCurve d L := ⟨hd_smooth, hL_pos, hd_periodic, hd_regular⟩


  have hd_curvature : totalCurvature d L = totalCurvature c T := by


    exact totalCurvature_reparam_eq c φ ψ T hc.smooth hφ_smooth hψ_smooth
      hφ_left hφ_right hψ_deriv hψ_pos hψ_periodic_shift hd_unit hc.periodic

  exact ⟨d, hd_closed, hd_unit, hd_curvature⟩

def unitTangent (c : ℝ → Fin 2 → ℝ) (t : ℝ) : Fin 2 → ℝ :=
  (‖deriv (toEuclidean c) t‖⁻¹) • deriv c t

def rotationNumber (c : ℝ → Fin 2 → ℝ) (T : ℝ) : ℝ :=
  totalCurvature c T / (2 * Real.pi)


theorem curvature_speed_eq_det2_unitTangent (c : ℝ → Fin 2 → ℝ) (t : ℝ)
    (hsmooth : ContDiff ℝ ⊤ c) (hc' : deriv c t ≠ 0) :
    curvature c t * ‖deriv (toEuclidean c) t‖ =
    DegreeTheory.det2 (unitTangent c t) (deriv (unitTangent c) t) := by

  have hce_smooth : ContDiff ℝ ⊤ (toEuclidean c) := by
    unfold toEuclidean
    exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearEquiv.contDiff.comp hsmooth


  set L : (Fin 2 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearEquiv : (Fin 2 → ℝ) ≃L[ℝ] _).toContinuousLinearMap


  have hL : ∀ s, deriv (toEuclidean c) s = L (deriv c s) := by
    intro s; unfold toEuclidean
    exact (L.hasFDerivAt.comp_hasDerivAt s
      ((hsmooth.differentiable (by simp)).differentiableAt.hasDerivAt)).deriv

  have hce_ne : deriv (toEuclidean c) t ≠ 0 := by
    rw [hL t]; intro h
    apply hc'

    exact (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearEquiv.injective h

  have hnorm_ne : ‖deriv (toEuclidean c) t‖ ≠ 0 := norm_ne_zero_iff.mpr hce_ne

  have hdc_E : ContDiff ℝ ⊤ (deriv (toEuclidean c)) := by
    have : ContDiff ℝ (⊤ + 1) (toEuclidean c) := by
      simp [WithTop.top_add]; exact hce_smooth
    exact this.deriv'

  have hdiff_dc_E : DifferentiableAt ℝ (deriv (toEuclidean c)) t :=
    (hdc_E.differentiable (by simp)).differentiableAt
  have hdiff_inv : DifferentiableAt ℝ (fun s => (‖deriv (toEuclidean c) s‖⁻¹ : ℝ)) t := by
    apply DifferentiableAt.inv
    · exact hdiff_dc_E.norm (𝕜 := ℝ) hce_ne
    · exact hnorm_ne

  have hT_eq_L : ∀ s,
      (‖deriv (toEuclidean c) s‖⁻¹ : ℝ) • deriv (toEuclidean c) s = L (unitTangent c s) := by
    intro s; unfold unitTangent; rw [map_smul, hL s]


  have hdc : ContDiff ℝ ⊤ (deriv c) := by
    have : ContDiff ℝ (⊤ + 1) c := by simp [WithTop.top_add]; exact hsmooth
    exact this.deriv'
  have hdiff_dc : DifferentiableAt ℝ (deriv c) t :=
    (hdc.differentiable (by simp)).differentiableAt

  have hU_diff : DifferentiableAt ℝ (unitTangent c) t := by
    unfold unitTangent
    exact hdiff_inv.smul hdiff_dc


  set T_E : ℝ → EuclideanSpace ℝ (Fin 2) :=
    fun s => (‖deriv (toEuclidean c) s‖⁻¹) • deriv (toEuclidean c) s
  have hT_diff : DifferentiableAt ℝ T_E t := hdiff_inv.smul hdiff_dc_E

  have hT_fun_eq : T_E = L ∘ (unitTangent c) := by
    funext s; exact hT_eq_L s


  have hderiv_T_eq : deriv T_E t = L (deriv (unitTangent c) t) := by
    rw [hT_fun_eq]
    exact (L.hasFDerivAt.comp_hasDerivAt t hU_diff.hasDerivAt).deriv


  have hdet2_eq : PlaneCurves.det2 (T_E t) (deriv T_E t) =
      DegreeTheory.det2 (unitTangent c t) (deriv (unitTangent c) t) := by
    rw [show T_E t = L (unitTangent c t) from hT_eq_L t, hderiv_T_eq]
    simp only [PlaneCurves.det2, DegreeTheory.det2]

    rfl

  rw [← hdet2_eq]

  have hderiv_T : deriv T_E t =
    (‖deriv (toEuclidean c) t‖⁻¹) • deriv (deriv (toEuclidean c)) t +
    deriv (fun s => ‖deriv (toEuclidean c) s‖⁻¹) t • deriv (toEuclidean c) t :=
    deriv_smul hdiff_inv hdiff_dc_E
  rw [hderiv_T]
  have key := PlaneCurves.det2_unit_tangent_deriv (deriv (toEuclidean c) t)
    (deriv (deriv (toEuclidean c)) t)
    (deriv (fun s => ‖deriv (toEuclidean c) s‖⁻¹) t) hnorm_ne


  unfold curvature PlaneCurves.curvature


  have hN_ne : (‖deriv (toEuclidean c) t‖ : ℝ) ≠ 0 := hnorm_ne

  have key' : PlaneCurves.det2 (‖deriv (toEuclidean c) t‖⁻¹ • deriv (toEuclidean c) t)
    (‖deriv (toEuclidean c) t‖⁻¹ • deriv (deriv (toEuclidean c)) t +
     deriv (fun s => ‖deriv (toEuclidean c) s‖⁻¹) t • deriv (toEuclidean c) t) =
    PlaneCurves.det2 (deriv (toEuclidean c) t) (deriv (deriv (toEuclidean c)) t) /
      ‖deriv (toEuclidean c) t‖ ^ 3 * ‖deriv (toEuclidean c) t‖ := by
    have := key
    field_simp at this ⊢
    linarith
  linarith [key']

theorem total_curvature_eq_two_pi_degree (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsClosedCurve c T) :
    totalCurvature c T = 2 * Real.pi * DegreeTheory.degreeReal (unitTangent c) T := by
  suffices h : totalCurvature c T =
      ∫ t in (0 : ℝ)..T, DegreeTheory.det2 (unitTangent c t) (deriv (unitTangent c) t) by
    rw [h]
    unfold DegreeTheory.degreeReal
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    field_simp
  unfold totalCurvature
  congr 1
  ext t
  exact curvature_speed_eq_det2_unitTangent c t hc.smooth (hc.regular t)

theorem rotationNumber_eq_degree (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsClosedCurve c T) :
    rotationNumber c T = DegreeTheory.degreeReal (unitTangent c) T := by
  unfold rotationNumber
  rw [total_curvature_eq_two_pi_degree c T hc]
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  field_simp


theorem unitTangent_smooth (c : ℝ → Fin 2 → ℝ) (hc : ContDiff ℝ ⊤ c)
    (hreg : ∀ t, deriv c t ≠ 0) :
    ContDiff ℝ ⊤ (unitTangent c) := by sorry

lemma unitTangent_on_unit_circle (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsClosedCurve c T) :
    DegreeTheory.OnUnitCircle (unitTangent c) := by
  intro t
  unfold unitTangent toEuclidean
  set v := deriv c t
  have hreg : v ≠ 0 := hc.regular t


  have hderiv_toE : deriv (fun s => (EuclideanSpace.equiv (Fin 2) ℝ).symm (c s)) t =
      (EuclideanSpace.equiv (Fin 2) ℝ).symm v := by
    have hcdiff : DifferentiableAt ℝ c t :=
      (hc.smooth.differentiable (by simp)).differentiableAt
    set L := (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hL : HasFDerivAt (fun x => (EuclideanSpace.equiv (Fin 2) ℝ).symm x) L (c t) :=
      L.hasFDerivAt
    have hf : HasDerivAt c (deriv c t) t := hcdiff.hasDerivAt
    have hcomp := hL.comp_hasDerivAt t hf
    exact hcomp.deriv


  rw [hderiv_toE]
  set r := ‖(EuclideanSpace.equiv (Fin 2) ℝ).symm v‖
  have hr_pos : r > 0 := by
    simp only [r]
    refine norm_pos_iff.mpr ?_
    intro h
    have : (EuclideanSpace.equiv (Fin 2) ℝ) ((EuclideanSpace.equiv (Fin 2) ℝ).symm v) =
      (EuclideanSpace.equiv (Fin 2) ℝ) 0 := congr_arg _ h
    simp at this
    exact hreg this
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos

  simp only [Pi.smul_apply, smul_eq_mul]

  have hrsq : (v 0) ^ 2 + (v 1) ^ 2 = r ^ 2 := by
    simp only [r, EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
    simp [Fin.sum_univ_two]
  rw [mul_pow, mul_pow, ← mul_add, hrsq, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hr_ne)]

lemma unitTangent_periodic (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsClosedCurve c T) :
    ∀ t, unitTangent c (t + T) = unitTangent c t := by
  intro t
  unfold unitTangent
  have hderiv_per := deriv_periodic_of_closed c T hc t

  conv_lhs => rw [hderiv_per]

  congr 1

  unfold toEuclidean
  have hcdiff : Differentiable ℝ c := hc.smooth.differentiable (by simp)
  have hderiv_toE : ∀ s, deriv (fun u => (EuclideanSpace.equiv (Fin 2) ℝ).symm (c u)) s =
      (EuclideanSpace.equiv (Fin 2) ℝ).symm (deriv c s) := by
    intro s
    have hcs : DifferentiableAt ℝ c s := hcdiff.differentiableAt
    set L := (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hL : HasFDerivAt (fun x => (EuclideanSpace.equiv (Fin 2) ℝ).symm x) L (c s) :=
      L.hasFDerivAt
    have hf : HasDerivAt c (deriv c s) s := hcs.hasDerivAt
    exact (hL.comp_hasDerivAt s hf).deriv
  rw [hderiv_toE (t + T), hderiv_toE t, hderiv_per]

theorem rotationNumber_is_integer (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsClosedCurve c T) :
    ∃ k : ℤ, rotationNumber c T = k := by
  rw [rotationNumber_eq_degree c T hc]
  exact DegreeTheory.degree_is_integer (unitTangent c)
    (unitTangent_smooth c hc.smooth hc.regular)
    (unitTangent_on_unit_circle c T hc)
    T
    (unitTangent_periodic c T hc)

lemma det2_unitTangent_deriv_eq_curvature_speed (c : ℝ → Fin 2 → ℝ) (t : ℝ)
    (p : Fin 2 → ℝ)
    (hsmooth : ContDiff ℝ ⊤ c) (hc' : deriv c t ≠ 0)
    (hfp : unitTangent c t = p) :
    DegreeTheory.det2 p (deriv (unitTangent c) t) =
    curvature c t * ‖deriv (toEuclidean c) t‖ := by
  rw [← hfp]
  exact (curvature_speed_eq_det2_unitTangent c t hsmooth hc').symm

lemma norm_deriv_toEuclidean_pos (c : ℝ → Fin 2 → ℝ) (t : ℝ)
    (hsmooth : ContDiff ℝ ⊤ c) (hc' : deriv c t ≠ 0) :
    ‖deriv (toEuclidean c) t‖ > 0 := by
  have hderiv_eq : deriv (toEuclidean c) t = (EuclideanSpace.equiv (Fin 2) ℝ).symm (deriv c t) := by
    unfold toEuclidean
    have hcdiff : DifferentiableAt ℝ c t :=
      (hsmooth.differentiable (by simp)).differentiableAt
    set L := (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap
    exact (L.hasFDerivAt.comp_hasDerivAt t hcdiff.hasDerivAt).deriv
  rw [hderiv_eq]
  exact norm_pos_iff.mpr (by
    intro h
    have : (EuclideanSpace.equiv (Fin 2) ℝ) ((EuclideanSpace.equiv (Fin 2) ℝ).symm (deriv c t)) =
      (EuclideanSpace.equiv (Fin 2) ℝ) 0 := congr_arg _ h
    simp at this
    exact hc' this)

lemma sign_det2_unitTangent_eq_sign_curvature (c : ℝ → Fin 2 → ℝ) (t : ℝ)
    (p : Fin 2 → ℝ)
    (hsmooth : ContDiff ℝ ⊤ c) (hc' : deriv c t ≠ 0)
    (hfp : unitTangent c t = p) :
    Real.sign (DegreeTheory.det2 p (deriv (unitTangent c) t)) =
    Real.sign (curvature c t) := by
  rw [det2_unitTangent_deriv_eq_curvature_speed c t p hsmooth hc' hfp]

  have hnorm_pos : ‖deriv (toEuclidean c) t‖ > 0 := norm_deriv_toEuclidean_pos c t hsmooth hc'

  rcases lt_trichotomy (curvature c t) 0 with hk | hk | hk
  · rw [Real.sign_of_neg hk, Real.sign_of_neg (mul_neg_of_neg_of_pos hk hnorm_pos)]
  · simp [hk, Real.sign_zero]
  · rw [Real.sign_of_pos hk, Real.sign_of_pos (mul_pos hk hnorm_pos)]

lemma unitTangent_eq_e1_iff (c : ℝ → Fin 2 → ℝ) (t : ℝ)
    (hsmooth : ContDiff ℝ ⊤ c) (hc' : deriv c t ≠ 0) :
    unitTangent c t = (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) ↔
    ((deriv c t) 1 = 0 ∧ (deriv c t) 0 > 0) := by
  unfold unitTangent
  set v := deriv c t
  have hr_pos : ‖deriv (toEuclidean c) t‖ > 0 := norm_deriv_toEuclidean_pos c t hsmooth hc'
  set r := ‖deriv (toEuclidean c) t‖
  have hr_ne : r ≠ 0 := ne_of_gt hr_pos
  have hderiv_eq : deriv (toEuclidean c) t = (EuclideanSpace.equiv (Fin 2) ℝ).symm v := by
    unfold toEuclidean
    have hcdiff : DifferentiableAt ℝ c t :=
      (hsmooth.differentiable (by simp)).differentiableAt
    set L := (EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap
    exact (L.hasFDerivAt.comp_hasDerivAt t hcdiff.hasDerivAt).deriv

  have hr_eq_norm : r = Real.sqrt ((v 0) ^ 2 + (v 1) ^ 2) := by
    simp only [r, hderiv_eq]
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, sq_abs]

  constructor
  · intro h

    have h0 : r⁻¹ * v 0 = 1 := by
      have := congr_fun h ⟨0, by omega⟩; simpa [Pi.smul_apply, smul_eq_mul] using this
    have h1 : r⁻¹ * v 1 = 0 := by
      have := congr_fun h ⟨1, by omega⟩; simpa [Pi.smul_apply, smul_eq_mul] using this
    constructor
    · exact (mul_eq_zero.mp h1).resolve_left (inv_ne_zero hr_ne)
    · have hv0_eq : v 0 = r := by field_simp at h0; linarith
      linarith
  · intro ⟨hv1, hv0⟩


    have hr_eq_v0 : r = v 0 := by
      rw [hr_eq_norm, hv1]; simp; rw [Real.sqrt_sq (le_of_lt hv0)]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    by_cases hi : i = 0
    · simp only [hi, ite_true]
      rw [hr_eq_v0, inv_mul_cancel₀ (ne_of_gt hv0)]
    · simp only [hi, ite_false]
      have : i = 1 := by omega
      rw [this, hv1, mul_zero]

theorem rotation_number_eq_signed_curvature_sum (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsClosedCurve c T)
    (specialPts : Finset ℝ)

    (hpts_range : ∀ t ∈ specialPts, 0 ≤ t ∧ t < T)

    (hpts_cond : ∀ t ∈ specialPts, (deriv c t) 1 = 0 ∧ (deriv c t) 0 > 0)

    (hpts_complete : ∀ t, 0 ≤ t → t < T → (deriv c t) 1 = 0 → (deriv c t) 0 > 0 →
      t ∈ specialPts)

    (hcurv_ne : ∀ t ∈ specialPts, curvature c t ≠ 0) :
    rotationNumber c T = ∑ t ∈ specialPts, Real.sign (curvature c t) := by

  rw [rotationNumber_eq_degree c T hc]

  set p : Fin 2 → ℝ := fun i => if i = 0 then 1 else 0
  have hp : p 0 ^ 2 + p 1 ^ 2 = 1 := by simp [p]

  have hpre : ∀ t ∈ specialPts, 0 ≤ t ∧ t < T ∧ unitTangent c t = p := by
    intro t ht
    obtain ⟨hge, hlt⟩ := hpts_range t ht
    obtain ⟨hv1, hv0⟩ := hpts_cond t ht
    refine ⟨hge, hlt, ?_⟩
    exact (unitTangent_eq_e1_iff c t hc.smooth (hc.regular t)).mpr ⟨hv1, hv0⟩
  have hcomplete : ∀ t, 0 ≤ t → t < T → unitTangent c t = p → t ∈ specialPts := by
    intro t hge hlt hfp
    have hcond := (unitTangent_eq_e1_iff c t hc.smooth (hc.regular t)).mp hfp
    exact hpts_complete t hge hlt hcond.1 hcond.2


  have hregular : ∀ t ∈ specialPts, deriv (unitTangent c) t ≠ 0 := by
    intro t ht hderiv_zero
    have hfp : unitTangent c t = p := (hpre t ht).2.2
    have hdet_zero : DegreeTheory.det2 p (deriv (unitTangent c) t) = 0 := by
      rw [hderiv_zero]; simp [DegreeTheory.det2]
    have hcurv_speed_zero : curvature c t * ‖deriv (toEuclidean c) t‖ = 0 := by
      rw [← det2_unitTangent_deriv_eq_curvature_speed c t p hc.smooth (hc.regular t) hfp]
      exact hdet_zero
    have hnorm_pos : ‖deriv (toEuclidean c) t‖ > 0 :=
      norm_deriv_toEuclidean_pos c t hc.smooth (hc.regular t)
    have := mul_eq_zero.mp hcurv_speed_zero
    cases this with
    | inl h => exact hcurv_ne t ht h
    | inr h => linarith

  have hdeg := DegreeTheory.degree_as_signed_count
    (unitTangent c) T hc.period_pos
    (unitTangent_smooth c hc.smooth hc.regular)
    (unitTangent_on_unit_circle c T hc)
    (unitTangent_periodic c T hc)
    p hp specialPts hpre hcomplete hregular

  rw [hdeg]
  apply Finset.sum_congr rfl
  intro t ht
  exact sign_det2_unitTangent_eq_sign_curvature c t p hc.smooth (hc.regular t) (hpre t ht).2.2

theorem convex_iff_curvature_no_sign_change
    (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsSimpleClosedCurve c T) :
    IsConvexCurve c T ↔ (∀ t, curvature c t ≥ 0) ∨ (∀ t, curvature c t ≤ 0) := by sorry

def det2 (a b : Fin 2 → ℝ) : ℝ := DegreeTheory.det2 a b

theorem whitney_formula (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsClosedCurve c T)
    (hmin : ∀ t, c 0 1 ≤ c t 1)
    (crossings : Finset (ℝ × ℝ))
    (hcross : ∀ p ∈ crossings, 0 ≤ p.1 ∧ p.1 < p.2 ∧ p.2 < T ∧ c p.1 = c p.2)
    (hcross_complete : ∀ s t, 0 ≤ s → s < t → t < T → c s = c t → (s, t) ∈ crossings)
    (hnormal : ∀ p ∈ crossings, det2 (deriv c p.1) (deriv c p.2) ≠ 0) :
    totalCurvature c T / (2 * Real.pi) =
    Real.sign ((deriv c 0) 0) - ∑ p ∈ crossings, Real.sign (det2 (deriv c p.1) (deriv c p.2)) := by sorry

lemma totalCurvature_shift (c : ℝ → Fin 2 → ℝ) (T t₀ : ℝ)
    (hc : IsClosedCurve c T) :
    totalCurvature (fun t => c (t + t₀)) T = totalCurvature c T := by
  have hperiodic := totalCurvature_integrand_periodic c T hc.smooth hc.periodic
  unfold totalCurvature

  have heq : ∀ t, curvature (fun s => c (s + t₀)) t * ‖deriv (toEuclidean (fun s => c (s + t₀))) t‖ =
      (fun s => curvature c s * ‖deriv (toEuclidean c) s‖) (t + t₀) := by
    intro t
    have hcurv : curvature (fun s => c (s + t₀)) t = curvature c (t + t₀) := by
      have h := curvature_comp_reparam c (· + t₀) hc.smooth
        (contDiff_id.add contDiff_const)
        (fun s => by simp [deriv_add_const]) (fun s => hc.regular (s + t₀)) t
      simp [Function.comp] at h
      exact h
    have hnorm : ‖deriv (toEuclidean (fun s => c (s + t₀))) t‖ =
        ‖deriv (toEuclidean c) (t + t₀)‖ := by
      congr 1
      have hte : toEuclidean (fun s => c (s + t₀)) = (toEuclidean c) ∘ (· + t₀) := by
        ext s; simp [toEuclidean]
      rw [hte]
      have hd2 : DifferentiableAt ℝ (toEuclidean c) (t + t₀) := by
        unfold toEuclidean
        exact ((EuclideanSpace.equiv (Fin 2) ℝ).symm.toContinuousLinearEquiv.contDiff.comp
          hc.smooth).differentiable WithTop.top_ne_zero |>.differentiableAt
      have hda : DifferentiableAt ℝ (· + t₀ : ℝ → ℝ) t :=
        (differentiableAt_id.add (differentiableAt_const t₀))
      rw [deriv.scomp t hd2 hda, show deriv (· + t₀ : ℝ → ℝ) t = 1 from by simp, one_smul]
    rw [hcurv, hnorm]

  have hlhs : (∫ t in (0 : ℝ)..T, curvature (fun s => c (s + t₀)) t *
      ‖deriv (toEuclidean (fun s => c (s + t₀))) t‖) =
      ∫ t in (0 : ℝ)..T, (fun s => curvature c s * ‖deriv (toEuclidean c) s‖) (t + t₀) := by
    apply intervalIntegral.integral_congr
    intro t _
    exact heq t
  rw [hlhs]


  set f := fun s => curvature c s * ‖deriv (toEuclidean c) s‖

  show ∫ t in (0 : ℝ)..T, f (t + t₀) = ∫ t in (0 : ℝ)..T, f t
  rw [intervalIntegral.integral_comp_add_right]

  simp only [zero_add]

  rw [show T + t₀ = t₀ + T from add_comm T t₀]

  rw [show (∫ t in (0 : ℝ)..T, f t) = ∫ t in (0 : ℝ)..(0 + T), f t from by rw [zero_add]]
  exact hperiodic.intervalIntegral_add_eq t₀ 0

lemma periodic_global_min_of_minOn {f : ℝ → ℝ} {T t₀ : ℝ}
    (hT : 0 < T) (hper : Function.Periodic f T)
    (hmin : IsMinOn f (Set.Icc 0 T) t₀) :
    ∀ s, f t₀ ≤ f s := by
  intro s

  obtain ⟨y, hy_mem, hy_eq⟩ := hper.exists_mem_Ico₀ hT s
  rw [hy_eq]

  exact hmin (Set.Ico_subset_Icc_self hy_mem)

theorem hopf_umlaufsatz (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsSimpleClosedCurve c T) :
    rotationNumber c T = 1 ∨ rotationNumber c T = -1 := by
  have hclosed := hc.1

  have hcont1 : ContinuousOn (fun t => c t 1) (Set.Icc 0 T) :=
    ((continuous_apply 1).comp hclosed.smooth.continuous).continuousOn
  obtain ⟨t₀, ht₀_mem, ht₀_min⟩ := IsCompact.exists_isMinOn
    isCompact_Icc ⟨0, Set.left_mem_Icc.mpr (le_of_lt hclosed.period_pos)⟩ hcont1

  set c' : ℝ → Fin 2 → ℝ := fun t => c (t + t₀)

  have hc'_closed : IsClosedCurve c' T := by
    refine ⟨hclosed.smooth.comp (contDiff_id.add contDiff_const), hclosed.period_pos, ?_, ?_⟩
    · intro t
      show c (t + T + t₀) = c (t + t₀)
      rw [show t + T + t₀ = (t + t₀) + T from by ring]
      exact hclosed.periodic (t + t₀)
    · intro t
      show deriv (fun s => c (s + t₀)) t ≠ 0
      have hd : DifferentiableAt ℝ c (t + t₀) :=
        (hclosed.smooth.differentiable WithTop.top_ne_zero).differentiableAt
      have hda : DifferentiableAt ℝ (· + t₀ : ℝ → ℝ) t :=
        differentiableAt_id.add (differentiableAt_const t₀)
      rw [show (fun s => c (s + t₀)) = c ∘ (· + t₀) from rfl, deriv.scomp t hd hda,
        show deriv (· + t₀ : ℝ → ℝ) t = 1 from by simp, one_smul]
      exact hclosed.regular (t + t₀)

  have hper1 : Function.Periodic (fun x => c x 1) T :=
    fun x => congr_fun (hclosed.periodic x) 1
  have hglobal_min : ∀ s, c t₀ 1 ≤ c s 1 :=
    periodic_global_min_of_minOn hclosed.period_pos hper1 ht₀_min
  have hmin : ∀ t, c' 0 1 ≤ c' t 1 := by
    intro t
    show c (0 + t₀) 1 ≤ c (t + t₀) 1
    simp only [zero_add]
    exact hglobal_min (t + t₀)


  have hc'_simple : ∀ s t, 0 ≤ s → s < t → t < T → c' s ≠ c' t := by
    intro s t hs hst htT heq


    have hper : Function.Periodic c T := hclosed.periodic
    set s₀ := toIcoMod hclosed.period_pos 0 (s + t₀)
    set t₀' := toIcoMod hclosed.period_pos 0 (t + t₀)
    have hcs : c s₀ = c (s + t₀) := by
      have h := toIcoMod_add_toIcoDiv_zsmul hclosed.period_pos 0 (s + t₀)
      conv_rhs => rw [← h]
      exact (hper.zsmul (toIcoDiv hclosed.period_pos 0 (s + t₀)) s₀).symm
    have hct : c t₀' = c (t + t₀) := by
      have h := toIcoMod_add_toIcoDiv_zsmul hclosed.period_pos 0 (t + t₀)
      conv_rhs => rw [← h]
      exact (hper.zsmul (toIcoDiv hclosed.period_pos 0 (t + t₀)) t₀').symm
    have heq' : c s₀ = c t₀' := by rw [hcs, hct]; exact heq
    have hs₀_mem := toIcoMod_mem_Ico hclosed.period_pos 0 (s + t₀)
    have ht₀'_mem := toIcoMod_mem_Ico hclosed.period_pos 0 (t + t₀)
    simp only [zero_add] at hs₀_mem ht₀'_mem
    rcases lt_trichotomy s₀ t₀' with h | h | h
    · exact hc.2 s₀ t₀' hs₀_mem.1 h ht₀'_mem.2 heq'
    · rw [show s₀ = toIcoMod hclosed.period_pos 0 (s + t₀) from rfl,
          show t₀' = toIcoMod hclosed.period_pos 0 (t + t₀) from rfl] at h
      rw [toIcoMod_eq_toIcoMod] at h
      obtain ⟨n, hn⟩ := h
      have htms : t - s = n • T := by linarith
      have hn_pos : (0 : ℤ) < n := by
        by_contra h_le
        push Not at h_le
        have hle : (n : ℝ) ≤ 0 := Int.cast_nonpos.mpr h_le
        have : n • T ≤ 0 := by
          rw [zsmul_eq_mul]
          exact mul_nonpos_of_nonpos_of_nonneg hle (le_of_lt hclosed.period_pos)
        linarith
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
      have hT_le : T ≤ n • T := by
        rw [zsmul_eq_mul]
        exact le_mul_of_one_le_left (le_of_lt hclosed.period_pos) h1
      linarith
    · exact hc.2 t₀' s₀ ht₀'_mem.1 h hs₀_mem.2 heq'.symm
  have hwhitney := whitney_formula c' T hc'_closed hmin ∅
    (fun p hp => absurd hp (by simp))
    (fun s t hs hst htT heq => absurd heq (hc'_simple s t hs hst htT))
    (fun p hp => absurd hp (by simp))
  simp only [Finset.sum_empty, sub_zero] at hwhitney

  have htc_eq : totalCurvature c' T = totalCurvature c T :=
    totalCurvature_shift c T t₀ hclosed

  unfold rotationNumber
  rw [← htc_eq, hwhitney]


  have hderiv_c'_0 : deriv c' 0 = deriv c t₀ := by
    show deriv (fun s => c (s + t₀)) 0 = deriv c t₀
    have hd : DifferentiableAt ℝ c (0 + t₀) :=
      (hclosed.smooth.differentiable WithTop.top_ne_zero).differentiableAt
    have hda : DifferentiableAt ℝ (· + t₀ : ℝ → ℝ) 0 :=
      differentiableAt_id.add (differentiableAt_const t₀)
    rw [show (fun s => c (s + t₀)) = c ∘ (· + t₀) from rfl, deriv.scomp 0 (by simpa using hd) hda,
      show deriv (· + t₀ : ℝ → ℝ) 0 = 1 from by simp, one_smul]
    simp
  rw [hderiv_c'_0]

  have hy_zero : (deriv c t₀) 1 = 0 := by

    have hsmooth1 : ContDiff ℝ ⊤ (fun s => c s 1) := (contDiff_pi.mp hclosed.smooth) 1
    have hdiff1 : DifferentiableAt ℝ (fun s => c s 1) t₀ :=
      (hsmooth1.differentiable WithTop.top_ne_zero).differentiableAt
    have hmin_global : IsMinOn (fun s => c s 1) Set.univ t₀ := fun s _ => hglobal_min s
    have hloc : IsLocalMin (fun s => c s 1) t₀ :=
      hmin_global.isLocalMin (Filter.univ_mem)
    have hzero := hloc.hasDerivAt_eq_zero hdiff1.hasDerivAt

    have hdc : DifferentiableAt ℝ c t₀ :=
      (hclosed.smooth.differentiable WithTop.top_ne_zero).differentiableAt
    have key : HasDerivAt c (deriv c t₀) t₀ := hdc.hasDerivAt
    rw [hasDerivAt_pi] at key
    have h1 := (key 1).deriv

    linarith
  have hx_ne_zero : (deriv c t₀) 0 ≠ 0 := by
    intro h0
    have : deriv c t₀ = 0 := by
      ext i; fin_cases i <;> simp_all
    exact hclosed.regular t₀ this

  rcases lt_or_gt_of_ne hx_ne_zero with h | h
  · right; exact Real.sign_of_neg h
  · left; exact Real.sign_of_pos h

theorem totalCurvature_simple_closed_eq_pm_two_pi (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsSimpleClosedCurve c T) :
    totalCurvature c T = 2 * Real.pi ∨ totalCurvature c T = -(2 * Real.pi) := by
  have hrot := hopf_umlaufsatz c T hc
  unfold rotationNumber at hrot
  have hpi_pos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpi_ne : (2 * Real.pi) ≠ 0 := ne_of_gt hpi_pos
  cases hrot with
  | inl h =>
    left
    rw [div_eq_iff hpi_ne] at h
    linarith
  | inr h =>
    right
    rw [div_eq_iff hpi_ne] at h
    linarith


theorem rotationNumber_ne_zero_general (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsClosedCurve c T) :
    rotationNumber c T ≠ 0 := by sorry

theorem total_absolute_curvature_ge_two_pi (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsClosedCurve c T) :
    ∫ t in (0 : ℝ)..T, |curvature c t| * ‖deriv (toEuclidean c) t‖ ≥ 2 * Real.pi := by

  obtain ⟨k, hk_eq⟩ := rotationNumber_is_integer c T hc
  have hk_ne : k ≠ 0 := by
    intro h
    have : rotationNumber c T = 0 := by rw [hk_eq, h]; simp
    exact rotationNumber_ne_zero_general c T hc this


  have htot : totalCurvature c T = 2 * Real.pi * k := by
    unfold rotationNumber at hk_eq
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    field_simp at hk_eq
    linarith

  have habs_tot : |totalCurvature c T| ≥ 2 * Real.pi := by
    rw [htot, abs_mul, abs_of_pos (by positivity : (2 : ℝ) * Real.pi > 0)]
    have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by exact_mod_cast Int.one_le_abs hk_ne
    nlinarith [Real.pi_pos]

  have htri : ∫ t in (0 : ℝ)..T, |curvature c t| * ‖deriv (toEuclidean c) t‖ ≥
      |totalCurvature c T| := by
    have hab : (0 : ℝ) ≤ T := le_of_lt hc.period_pos
    have h := intervalIntegral.norm_integral_le_integral_norm
      (μ := volume) hab (f := fun t => curvature c t * ‖deriv (toEuclidean c) t‖)
    simp only [Real.norm_eq_abs] at h
    have heq : ∀ t, |curvature c t * ‖deriv (toEuclidean c) t‖| =
        |curvature c t| * ‖deriv (toEuclidean c) t‖ := by
      intro t
      rw [abs_mul, abs_of_nonneg (norm_nonneg _)]
    simp_rw [heq] at h
    unfold totalCurvature
    linarith
  linarith


theorem curvature_integrand_continuous (c : ℝ → Fin 2 → ℝ)
    (hc : ContDiff ℝ ⊤ c) (hreg : ∀ t, deriv c t ≠ 0) :
    Continuous (fun t => curvature c t * ‖deriv (toEuclidean c) t‖) := by sorry


theorem toEuclidean_deriv_eq_zero (c : ℝ → Fin 2 → ℝ)
    (hc : ContDiff ℝ ⊤ c) (t : ℝ) :
    deriv (toEuclidean c) t = 0 ↔ deriv c t = 0 := by sorry


theorem unitTangent_onUnitCircle (c : ℝ → Fin 2 → ℝ)
    (hc : ContDiff ℝ ⊤ c) (hreg : ∀ t, deriv c t ≠ 0) :
    DegreeTheory.OnUnitCircle (unitTangent c) := by sorry


theorem angle_function_hasDerivAt_angularVelocity (c : ℝ → Fin 2 → ℝ)
    (θ : ℝ → ℝ) (hc : ContDiff ℝ ⊤ c) (hreg : ∀ t, deriv c t ≠ 0)
    (hθ : DegreeTheory.IsAngleFunction (unitTangent c) θ) (t : ℝ) :
    HasDerivAt θ (DegreeTheory.angularVelocity (unitTangent c) t) t := by sorry


theorem angularVelocity_unitTangent_pos (c : ℝ → Fin 2 → ℝ) (t : ℝ)
    (hc : ContDiff ℝ ⊤ c) (hreg : ∀ t, deriv c t ≠ 0)
    (hκ_pos : curvature c t > 0) :
    DegreeTheory.angularVelocity (unitTangent c) t > 0 := by sorry


theorem angle_function_period_shift (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (θ : ℝ → ℝ) (hc : IsClosedCurve c T)
    (hpos : ∀ t, curvature c t > 0)
    (hθ : DegreeTheory.IsAngleFunction (unitTangent c) θ)
    (htc : totalCurvature c T = 2 * Real.pi) :
    ∀ t, θ (t + T) = θ t + 2 * Real.pi := by sorry


theorem angle_reparam_inverse_period (φ θ : ℝ → ℝ) (T : ℝ)
    (hleft : Function.LeftInverse φ θ) (hright : Function.RightInverse φ θ)
    (hθ_shift : ∀ t, θ (t + T) = θ t + 2 * Real.pi)
    {t : ℝ} :
    φ (t + 2 * Real.pi) = φ t + T := by sorry


theorem angle_reparam_inverse_deriv_pos (θ φ : ℝ → ℝ)
    (hθ_pos : ∀ t, 0 < deriv θ t)
    (hleft : Function.LeftInverse φ θ) (hright : Function.RightInverse φ θ)
    (hderiv : ∀ t, deriv φ (θ t) = (deriv θ t)⁻¹) (t : ℝ) :
    deriv φ t > 0 := by sorry


theorem comp_deriv_ne_zero (c : ℝ → Fin 2 → ℝ) (φ : ℝ → ℝ)
    (hc : ContDiff ℝ ⊤ c) (hφ : ContDiff ℝ ⊤ φ)
    {t : ℝ} (hreg : deriv c (φ t) ≠ 0) (hφ_ne : deriv φ t ≠ 0) :
    deriv (c ∘ φ) t ≠ 0 := by sorry


theorem unit_tangent_angle_reparam (c : ℝ → Fin 2 → ℝ) (φ θ : ℝ → ℝ) (t : ℝ)
    (hc : ContDiff ℝ ⊤ c) (hφ : ContDiff ℝ ⊤ φ)
    (hreg : ∀ s, deriv c s ≠ 0)
    (hφ_pos : ∀ s, deriv φ s > 0)
    (hθ : DegreeTheory.IsAngleFunction (unitTangent c) θ)
    (hleft : Function.LeftInverse φ θ) :
    (‖deriv (c ∘ φ) t‖⁻¹) • deriv (c ∘ φ) t = ![Real.cos t, Real.sin t] := by sorry


theorem curvature_eq_inv_speed_of_angle_param (d : ℝ → Fin 2 → ℝ) (t : ℝ)
    (hd : ContDiff ℝ ⊤ d) (hreg : deriv d t ≠ 0)
    (hunit : (‖deriv d t‖⁻¹) • deriv d t = ![Real.cos t, Real.sin t]) :
    curvature d t = ‖deriv d t‖⁻¹ := by sorry

end ClosedCurves

end
