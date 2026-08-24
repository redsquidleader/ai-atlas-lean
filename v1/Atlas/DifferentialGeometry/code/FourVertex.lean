/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.DifferentialGeometry.code.ClosedCurves

open MeasureTheory Real Set Filter Topology

namespace SturmHurwitz

lemma sin_half_diff_ne_zero {t₁ t₂ : ℝ} (ht₁ : t₁ ∈ Ico 0 (2 * π)) (ht₂ : t₂ ∈ Ico 0 (2 * π))
    (hne : t₁ ≠ t₂) : sin ((t₁ - t₂) / 2) ≠ 0 := by
  rw [sin_ne_zero_iff]
  intro n hn
  have hn0 : n = 0 := by
    have : (-1 : ℤ) < n := by
      by_contra h; push Not at h
      have : (n : ℝ) ≤ -1 := by exact_mod_cast h
      nlinarith [ht₁.1, ht₂.2, pi_pos]
    have : n < (1 : ℤ) := by
      by_contra h; push Not at h
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      nlinarith [ht₁.2, ht₂.1, pi_pos]
    omega
  simp [hn0] at hn; exact hne (by linarith)

theorem sturm_hurwitz
    (f : ℝ → ℝ) (hcont : Continuous f)
    (hper : ∀ t, f (t + 2 * Real.pi) = f t)
    (h0 : ∫ t in (0 : ℝ)..(2 * Real.pi), f t = 0)
    (hcos : ∫ t in (0 : ℝ)..(2 * Real.pi), f t * Real.cos t = 0)
    (hsin : ∫ t in (0 : ℝ)..(2 * Real.pi), f t * Real.sin t = 0) :
    ∃ (t₁ t₂ t₃ t₄ : ℝ), 0 ≤ t₁ ∧ t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < t₄ ∧ t₄ < 2 * Real.pi ∧
      f t₁ = 0 ∧ f t₂ = 0 ∧ f t₃ = 0 ∧ f t₄ = 0 := by sorry

lemma periodic_deriv (g : ℝ → ℝ) (hdiff : Differentiable ℝ g)
    (hper : ∀ t, g (t + 2 * Real.pi) = g t) :
    ∀ t, deriv g (t + 2 * Real.pi) = deriv g t := by
  intro t
  have lhs : HasDerivAt (fun s => g (s + 2 * π)) (deriv g (t + 2 * π)) t :=
    ((hdiff (t + 2 * π)).hasDerivAt.comp t ((hasDerivAt_id t).add_const (2 * π))).congr_deriv
      (by ring) |>.congr_of_eventuallyEq (by filter_upwards with s; simp [Function.comp])
  rw [show (fun s => g (s + 2 * π)) = g from funext hper] at lhs
  exact lhs.unique (hdiff t).hasDerivAt

lemma ibp_deriv_cos (g : ℝ → ℝ) (hdiff : Differentiable ℝ g)
    (hcont_g' : Continuous (deriv g)) (hcont_g : Continuous g)
    (hper : ∀ t, g (t + 2 * Real.pi) = g t) :
    ∫ t in (0:ℝ)..(2*π), deriv g t * cos t = ∫ t in (0:ℝ)..(2*π), g t * sin t := by
  have ibp := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x _ => hdiff.differentiableAt.hasDerivAt)
    (fun (x : ℝ) _ => hasDerivAt_cos x)
    (hcont_g'.intervalIntegrable 0 (2*π))
    (continuous_sin.neg.intervalIntegrable 0 (2*π))
  simp only [cos_two_pi, cos_zero, mul_one] at ibp
  have hper0 : g (2 * π) = g 0 := by have := hper 0; simp only [zero_add] at this; exact this
  rw [hper0, sub_self] at ibp
  have hsplit : ∫ x in (0:ℝ)..(2*π), deriv g x * cos x + g x * (-sin x) =
    (∫ x in (0:ℝ)..(2*π), deriv g x * cos x) + (∫ x in (0:ℝ)..(2*π), g x * (-sin x)) :=
    intervalIntegral.integral_add
      ((hcont_g'.mul continuous_cos).intervalIntegrable 0 (2*π))
      ((hcont_g.mul continuous_sin.neg).intervalIntegrable 0 (2*π))
  have hneg : ∫ x in (0:ℝ)..(2*π), g x * (-sin x) = -(∫ x in (0:ℝ)..(2*π), g x * sin x) := by
    have : (fun x => g x * (-sin x)) = fun x => -(g x * sin x) := by ext; ring
    rw [this, intervalIntegral.integral_neg]
  linarith [hsplit, hneg]

lemma ibp_deriv_sin (g : ℝ → ℝ) (hdiff : Differentiable ℝ g)
    (hcont_g' : Continuous (deriv g)) (hcont_g : Continuous g) :
    ∫ t in (0:ℝ)..(2*π), deriv g t * sin t = -(∫ t in (0:ℝ)..(2*π), g t * cos t) := by
  have ibp := intervalIntegral.integral_deriv_mul_eq_sub
    (fun x _ => hdiff.differentiableAt.hasDerivAt)
    (fun (x : ℝ) _ => hasDerivAt_sin x)
    (hcont_g'.intervalIntegrable 0 (2*π))
    (continuous_cos.intervalIntegrable 0 (2*π))
  simp only [sin_two_pi, sin_zero, mul_zero, sub_zero] at ibp
  have hsplit : ∫ x in (0:ℝ)..(2*π), deriv g x * sin x + g x * cos x =
    (∫ x in (0:ℝ)..(2*π), deriv g x * sin x) + (∫ x in (0:ℝ)..(2*π), g x * cos x) :=
    intervalIntegral.integral_add
      ((hcont_g'.mul continuous_sin).intervalIntegrable 0 (2*π))
      ((hcont_g.mul continuous_cos).intervalIntegrable 0 (2*π))
  linarith [hsplit]

theorem h_plus_h''_four_critical_points (h : ℝ → ℝ) (hsmooth : ContDiff ℝ ⊤ h)
    (hper : ∀ t, h (t + 2 * Real.pi) = h t) :
    ∃ (t₁ t₂ t₃ t₄ : ℝ), 0 ≤ t₁ ∧ t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < t₄ ∧ t₄ < 2 * Real.pi ∧
      deriv (fun t => h t + deriv (deriv h) t) t₁ = 0 ∧
      deriv (fun t => h t + deriv (deriv h) t) t₂ = 0 ∧
      deriv (fun t => h t + deriv (deriv h) t) t₃ = 0 ∧
      deriv (fun t => h t + deriv (deriv h) t) t₄ = 0 := by

  have hcd : ContDiff ℝ (↑(⊤ : ℕ∞)) h := hsmooth.of_le le_top
  have hdiff : Differentiable ℝ h := (contDiff_infty_iff_deriv.mp hcd).1
  have hcd' := (contDiff_infty_iff_deriv.mp hcd).2
  have hdiff' : Differentiable ℝ (deriv h) := (contDiff_infty_iff_deriv.mp hcd').1
  have hcd'' := (contDiff_infty_iff_deriv.mp hcd').2
  have hdiff'' : Differentiable ℝ (deriv (deriv h)) := (contDiff_infty_iff_deriv.mp hcd'').1
  have hcd''' := (contDiff_infty_iff_deriv.mp hcd'').2
  have hcont_h : Continuous h := hsmooth.continuous
  have hcont_h' : Continuous (deriv h) := hcd'.continuous
  have hcont_h'' : Continuous (deriv (deriv h)) := hcd''.continuous
  have hcont_h''' : Continuous (deriv (deriv (deriv h))) := hcd'''.continuous

  have hper' := periodic_deriv h hdiff hper
  have hper'' := periodic_deriv (deriv h) hdiff' hper'

  set f := fun t => deriv h t + deriv (deriv (deriv h)) t

  have hderiv_eq : ∀ t, deriv (fun t => h t + deriv (deriv h) t) t = f t :=
    fun t => ((hdiff t).hasDerivAt.add (hdiff'' t).hasDerivAt).deriv

  have hcont_f : Continuous f := hcont_h'.add hcont_h'''

  have hper_f : ∀ t, f (t + 2 * π) = f t := by
    intro t
    show deriv h (t + 2*π) + deriv (deriv (deriv h)) (t + 2*π) =
         deriv h t + deriv (deriv (deriv h)) t
    rw [hper' t, periodic_deriv (deriv (deriv h)) hdiff'' hper'' t]

  have hint_zero : ∫ t in (0:ℝ)..(2*π), f t = 0 := by
    have hsplit : ∫ t in (0:ℝ)..(2*π), f t =
      (∫ t in (0:ℝ)..(2*π), deriv h t) + (∫ t in (0:ℝ)..(2*π), deriv (deriv (deriv h)) t) :=
      intervalIntegral.integral_add (hcont_h'.intervalIntegrable 0 (2*π))
        (hcont_h'''.intervalIntegrable 0 (2*π))
    rw [hsplit,
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hdiff.differentiableAt.hasDerivAt) (hcont_h'.intervalIntegrable 0 (2*π)),
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hdiff''.differentiableAt.hasDerivAt) (hcont_h'''.intervalIntegrable 0 (2*π))]
    have h1 : h (2*π) = h 0 := by have := hper 0; simp only [zero_add] at this; exact this
    have h2 : deriv (deriv h) (2*π) = deriv (deriv h) 0 := by
      have := hper'' 0; simp only [zero_add] at this; exact this
    linarith

  have hint_cos : ∫ t in (0:ℝ)..(2*π), f t * cos t = 0 := by
    have hsplit : ∫ t in (0:ℝ)..(2*π), f t * cos t =
      (∫ t in (0:ℝ)..(2*π), deriv h t * cos t) +
      (∫ t in (0:ℝ)..(2*π), deriv (deriv (deriv h)) t * cos t) := by
      have : (fun t => f t * cos t) =
        fun t => deriv h t * cos t + deriv (deriv (deriv h)) t * cos t := by
        ext t; show (deriv h t + deriv (deriv (deriv h)) t) * cos t = _; ring
      rw [this]; exact intervalIntegral.integral_add
        ((hcont_h'.mul continuous_cos).intervalIntegrable 0 (2*π))
        ((hcont_h'''.mul continuous_cos).intervalIntegrable 0 (2*π))
    have e1 := ibp_deriv_cos h hdiff hcont_h' hcont_h hper
    have e2 := ibp_deriv_cos (deriv (deriv h)) hdiff'' hcont_h''' hcont_h'' hper''
    have e3 := ibp_deriv_sin (deriv h) hdiff' hcont_h'' hcont_h'
    linarith [hsplit, e1, e2, e3]

  have hint_sin : ∫ t in (0:ℝ)..(2*π), f t * sin t = 0 := by
    have hsplit : ∫ t in (0:ℝ)..(2*π), f t * sin t =
      (∫ t in (0:ℝ)..(2*π), deriv h t * sin t) +
      (∫ t in (0:ℝ)..(2*π), deriv (deriv (deriv h)) t * sin t) := by
      have : (fun t => f t * sin t) =
        fun t => deriv h t * sin t + deriv (deriv (deriv h)) t * sin t := by
        ext t; show (deriv h t + deriv (deriv (deriv h)) t) * sin t = _; ring
      rw [this]; exact intervalIntegral.integral_add
        ((hcont_h'.mul continuous_sin).intervalIntegrable 0 (2*π))
        ((hcont_h'''.mul continuous_sin).intervalIntegrable 0 (2*π))
    have e1 := ibp_deriv_sin h hdiff hcont_h' hcont_h
    have e2 := ibp_deriv_sin (deriv (deriv h)) hdiff'' hcont_h''' hcont_h''
    have e3 := ibp_deriv_cos (deriv h) hdiff' hcont_h'' hcont_h' hper'
    linarith [hsplit, e1, e2, e3]

  obtain ⟨t₁, t₂, t₃, t₄, h1, h2, h3, h4, h5, hz1, hz2, hz3, hz4⟩ :=
    sturm_hurwitz f hcont_f hper_f hint_zero hint_cos hint_sin
  exact ⟨t₁, t₂, t₃, t₄, h1, h2, h3, h4, h5,
    by rw [hderiv_eq]; exact hz1,
    by rw [hderiv_eq]; exact hz2,
    by rw [hderiv_eq]; exact hz3,
    by rw [hderiv_eq]; exact hz4⟩

end SturmHurwitz

namespace FourVertex

open Real ClosedCurves


theorem angle_parametrization (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsSimpleClosedCurve c T) (hpos : ∀ t, curvature c t > 0) :
    ∃ (d : ℝ → Fin 2 → ℝ), IsClosedCurve d (2 * Real.pi) ∧
      (∀ t, curvature d t > 0) ∧
      (∀ t, (‖deriv d t‖⁻¹) • deriv d t = ![Real.cos t, Real.sin t]) ∧
      (∀ t, curvature d t = ‖deriv d t‖⁻¹) := by

  have hclosed : IsClosedCurve c T := hc.1
  have hsmooth : ContDiff ℝ ⊤ c := hclosed.smooth
  have hT_pos : T > 0 := hclosed.period_pos
  have hperiodic : ∀ t, c (t + T) = c t := hclosed.periodic
  have hreg : ∀ t, deriv c t ≠ 0 := hclosed.regular

  have hrot := hopf_umlaufsatz c T hc

  have hintegrand_pos : ∀ t, curvature c t * ‖deriv (toEuclidean c) t‖ > 0 := by
    intro t
    have hκ := hpos t
    have hnorm : ‖deriv (toEuclidean c) t‖ > 0 :=
      norm_pos_iff.mpr ((toEuclidean_deriv_eq_zero c hsmooth t).not.mpr (hreg t))
    exact mul_pos hκ hnorm
  have htc_pos : totalCurvature c T > 0 := by
    unfold totalCurvature
    have hcont : ContinuousOn (fun t => curvature c t * ‖deriv (toEuclidean c) t‖)
        (Set.Icc 0 T) :=
      (curvature_integrand_continuous c hsmooth hreg).continuousOn
    exact intervalIntegral.integral_pos hT_pos hcont
      (fun x _ => le_of_lt (hintegrand_pos x))
      ⟨0, Set.left_mem_Icc.mpr (le_of_lt hT_pos), hintegrand_pos 0⟩

  have hrot_one : rotationNumber c T = 1 := by
    cases hrot with
    | inl h => exact h
    | inr h =>
      exfalso
      have : totalCurvature c T = rotationNumber c T * (2 * π) := by
        unfold rotationNumber
        field_simp
      linarith [mul_neg_of_neg_of_pos (show rotationNumber c T < 0 from by linarith)
        (show (2 : ℝ) * π > 0 from by positivity)]

  have htc_eq : totalCurvature c T = 2 * π := by
    have : totalCurvature c T = rotationNumber c T * (2 * π) := by
      unfold rotationNumber; field_simp
    rw [this, hrot_one, one_mul]

  have hut_smooth : ContDiff ℝ ⊤ (unitTangent c) :=
    unitTangent_smooth c hsmooth hreg
  have hut_circle : DegreeTheory.OnUnitCircle (unitTangent c) :=
    unitTangent_onUnitCircle c hsmooth hreg
  obtain ⟨θ, hθ_af⟩ := DegreeTheory.angle_function_exists
    (unitTangent c) hut_smooth hut_circle
  have hθ_smooth : ContDiff ℝ ⊤ θ := hθ_af.1


  have hθ_deriv_pos : ∀ t, 0 < deriv θ t := by
    intro t
    have hθ_hasderiv : HasDerivAt θ (DegreeTheory.angularVelocity (unitTangent c) t) t :=
      angle_function_hasDerivAt_angularVelocity c θ hsmooth hreg hθ_af t
    rw [hθ_hasderiv.deriv]
    exact angularVelocity_unitTangent_pos c t hsmooth hreg (hpos t)

  obtain ⟨_, φ, hφ_left, hφ_right, hφ_smooth, hφ_deriv⟩ :=
    Reparametrization.smooth_increasing_has_smooth_inverse_global θ hθ_smooth hθ_deriv_pos


  have hθ_period : ∀ t, θ (t + T) = θ t + 2 * π :=
    angle_function_period_shift c T θ hclosed hpos hθ_af htc_eq

  set d := c ∘ φ

  have hd_periodic : ∀ t, d (t + 2 * π) = d t := by
    intro t
    show c (φ (t + 2 * π)) = c (φ t)

    have hφ_period : φ (t + 2 * π) = φ t + T :=
      angle_reparam_inverse_period φ θ T hφ_left hφ_right hθ_period (t := t)
    rw [hφ_period]
    exact hperiodic (φ t)

  have hd_smooth : ContDiff ℝ ⊤ d := hsmooth.comp hφ_smooth

  have hd_reg : ∀ t, deriv d t ≠ 0 := by
    intro t

    have hφ_deriv_pos : deriv φ t > 0 :=
      angle_reparam_inverse_deriv_pos θ φ hθ_deriv_pos hφ_left hφ_right hφ_deriv t
    exact comp_deriv_ne_zero c φ hsmooth hφ_smooth (hreg (φ t)) (ne_of_gt hφ_deriv_pos)

  have hd_closed : IsClosedCurve d (2 * π) :=
    ⟨hd_smooth, by positivity, hd_periodic, hd_reg⟩

  have hd_curv_pos : ∀ t, curvature d t > 0 := by
    intro t
    have hφ_pos : ∀ s, 0 < deriv φ s :=
      fun s => angle_reparam_inverse_deriv_pos θ φ hθ_deriv_pos hφ_left hφ_right hφ_deriv s
    have heq := curvature_comp_reparam c φ hsmooth hφ_smooth hφ_pos (fun s => hreg (φ s)) t


    show curvature (c ∘ φ) t > 0
    rw [heq]
    exact hpos (φ t)

  have hd_unit_tangent : ∀ t, (‖deriv d t‖⁻¹) • deriv d t = ![cos t, sin t] := by
    intro t


    exact unit_tangent_angle_reparam c φ θ t hsmooth hφ_smooth hreg
      (fun s => angle_reparam_inverse_deriv_pos θ φ hθ_deriv_pos hφ_left hφ_right hφ_deriv s)
      hθ_af hφ_left

  have hd_curv_eq : ∀ t, curvature d t = ‖deriv d t‖⁻¹ := by
    intro t
    exact curvature_eq_inv_speed_of_angle_param d t hd_smooth (hd_reg t) (hd_unit_tangent t)
  exact ⟨d, hd_closed, hd_curv_pos, hd_unit_tangent, hd_curv_eq⟩


theorem four_vertex_from_lemmas (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (d : ℝ → Fin 2 → ℝ) (hc : IsSimpleClosedCurve c T)
    (hpos : ∀ t, curvature c t > 0)
    (hsmooth_κ : ContDiff ℝ ⊤ (curvature c))
    (hd_closed : IsClosedCurve d (2 * Real.pi))
    (hd_pos : ∀ t, curvature d t > 0)
    (hd_unit : ∀ t, (‖deriv d t‖⁻¹) • deriv d t = ![Real.cos t, Real.sin t])
    (hd_κ : ∀ t, curvature d t = ‖deriv d t‖⁻¹) :
    ∃ (t₁ t₂ t₃ t₄ : ℝ), 0 ≤ t₁ ∧ t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < t₄ ∧ t₄ < T ∧
      deriv (curvature c) t₁ = 0 ∧ deriv (curvature c) t₂ = 0 ∧
      deriv (curvature c) t₃ = 0 ∧ deriv (curvature c) t₄ = 0 := by sorry

theorem four_vertex_theorem (c : ℝ → Fin 2 → ℝ) (T : ℝ)
    (hc : IsSimpleClosedCurve c T) (hpos : ∀ t, curvature c t > 0)
    (hsmooth_κ : ContDiff ℝ ⊤ (curvature c)) :
    ∃ (t₁ t₂ t₃ t₄ : ℝ), 0 ≤ t₁ ∧ t₁ < t₂ ∧ t₂ < t₃ ∧ t₃ < t₄ ∧ t₄ < T ∧
      deriv (curvature c) t₁ = 0 ∧ deriv (curvature c) t₂ = 0 ∧
      deriv (curvature c) t₃ = 0 ∧ deriv (curvature c) t₄ = 0 := by

  obtain ⟨d, hd_closed, hd_pos, hd_unit, hd_κ⟩ :=
    angle_parametrization c T hc hpos

  exact four_vertex_from_lemmas c T d hc hpos hsmooth_κ hd_closed hd_pos hd_unit hd_κ

end FourVertex
