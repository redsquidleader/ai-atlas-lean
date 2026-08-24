/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open MeasureTheory intervalIntegral Real

namespace DegreeTheory

noncomputable def det2 (a b : Fin 2 → ℝ) : ℝ := a 0 * b 1 - a 1 * b 0

def OnUnitCircle (f : ℝ → Fin 2 → ℝ) : Prop := ∀ t, (f t 0) ^ 2 + (f t 1) ^ 2 = 1

noncomputable def angularVelocity (f : ℝ → Fin 2 → ℝ) (t : ℝ) : ℝ := det2 (f t) (deriv f t)

def IsAngleFunction (f : ℝ → Fin 2 → ℝ) (θ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ⊤ θ ∧ ∀ t, f t 0 = cos (θ t) ∧ f t 1 = sin (θ t)

theorem exists_angle_of_unit_circle (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ∃ θ₀ : ℝ, a = cos θ₀ ∧ b = sin θ₀ := by
  have habs : a ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> nlinarith [sq_nonneg b]
  have hsin_nn : 0 ≤ sin (arccos a) :=
    sin_nonneg_of_nonneg_of_le_pi (arccos_nonneg a) (arccos_le_pi a)
  have hsin_sq : sin (arccos a) ^ 2 = b ^ 2 := by
    have := sin_sq (arccos a); rw [cos_arccos habs.1 habs.2] at this; linarith
  by_cases hb : b ≥ 0
  · exact ⟨arccos a, (cos_arccos habs.1 habs.2).symm,
      by nlinarith [sq_nonneg (sin (arccos a) - b)]⟩
  · exact ⟨-(arccos a), by rw [cos_neg]; exact (cos_arccos habs.1 habs.2).symm,
      by rw [sin_neg]; nlinarith [sq_nonneg (sin (arccos a) + b), not_le.mp hb]⟩

theorem smooth_angular_velocity (f : ℝ → Fin 2 → ℝ) (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (angularVelocity f) := by
  have hfi : ∀ i : Fin 2, ContDiff ℝ ⊤ (fun t => f t i) :=
    fun i => (contDiff_apply ℝ ℝ i).comp hf
  have hfi' : ∀ i : Fin 2, ContDiff ℝ ⊤ (fun t => deriv (fun s => f s i) t) := by
    intro i; apply AnalyticOn.contDiff; intro x _
    exact ((hfi i).contDiffAt (x := x)).analyticAt.deriv.analyticWithinAt
  have heq : angularVelocity f = fun t =>
      (fun t => f t 0) t * (fun t => deriv (fun s => f s 1) t) t -
      (fun t => f t 1) t * (fun t => deriv (fun s => f s 0) t) t := by
    ext t; simp only [angularVelocity, det2]
    have hd := deriv_pi (fun i => ((hfi i).differentiable (by norm_num)).differentiableAt (x := t))
    congr 1 <;> congr 1 <;> exact congr_fun hd _
  rw [heq]
  exact ((hfi 0).mul (hfi' 1)).sub ((hfi 1).mul (hfi' 0))


theorem contDiff_infty_integral (ω : ℝ → ℝ) (c : ℝ) (hω : ContDiff ℝ ⊤ ω) :
    ContDiff ℝ ⊤ (fun t => c + ∫ τ in (0 : ℝ)..t, ω τ) := by sorry

theorem ode_uniqueness (f : ℝ → Fin 2 → ℝ) (θ : ℝ → ℝ)
    (hf : ContDiff ℝ ⊤ f) (hcirc : OnUnitCircle f) (hθ : ContDiff ℝ ⊤ θ)
    (hderiv : ∀ t, HasDerivAt θ (angularVelocity f t) t)
    (hinit0 : f 0 0 = cos (θ 0)) (hinit1 : f 0 1 = sin (θ 0)) :
    ∀ t, f t 0 = cos (θ t) ∧ f t 1 = sin (θ t) := by
  set g : ℝ → ℝ := fun t => f t 0 * cos (θ t) + f t 1 * sin (θ t)
  have hf0 : ContDiff ℝ ⊤ (fun t => f t 0) := (contDiff_apply ℝ ℝ 0).comp hf
  have hf1 : ContDiff ℝ ⊤ (fun t => f t 1) := (contDiff_apply ℝ ℝ 1).comp hf
  have g_diff : Differentiable ℝ g :=
    (hf0.differentiable (by norm_num)).mul (hθ.cos.differentiable (by norm_num)) |>.add
      ((hf1.differentiable (by norm_num)).mul (hθ.sin.differentiable (by norm_num)))
  have hcirc_deriv : ∀ t, f t 0 * deriv (fun s => f s 0) t +
      f t 1 * deriv (fun s => f s 1) t = 0 := by
    intro t
    have hd : HasDerivAt (fun s => (f s 0) ^ 2 + (f s 1) ^ 2) 0 t := by
      have : (fun s => (f s 0) ^ 2 + (f s 1) ^ 2) = fun _ => (1 : ℝ) := by ext s; exact hcirc s
      rw [this]; exact hasDerivAt_const t 1
    have hd2 : HasDerivAt (fun s => (f s 0) ^ 2 + (f s 1) ^ 2)
      (2 * f t 0 * deriv (fun s => f s 0) t + 2 * f t 1 * deriv (fun s => f s 1) t) t := by
      have h0 := ((hf0.differentiable (by norm_num)).differentiableAt (x := t)).hasDerivAt
      have h1 := ((hf1.differentiable (by norm_num)).differentiableAt (x := t)).hasDerivAt
      convert (h0.pow 2).add (h1.pow 2) using 1; ring
    linarith [hd.unique hd2]
  have g_deriv_zero : ∀ t, deriv g t = 0 := by
    intro t
    have ha := ((hf0.differentiable (by norm_num)).differentiableAt (x := t)).hasDerivAt
    have hb := ((hf1.differentiable (by norm_num)).differentiableAt (x := t)).hasDerivAt
    have hθt := hderiv t
    have hg_deriv : HasDerivAt g
      (deriv (fun s => f s 0) t * cos (θ t) - f t 0 * sin (θ t) * angularVelocity f t +
       deriv (fun s => f s 1) t * sin (θ t) + f t 1 * cos (θ t) * angularVelocity f t) t := by
      convert ha.mul hθt.cos |>.add (hb.mul hθt.sin) using 1; ring
    rw [hg_deriv.deriv]
    have hd_eq : ∀ i : Fin 2, deriv f t i = deriv (fun s => f s i) t :=
      fun i => congr_fun (deriv_pi (fun i => ((contDiff_apply ℝ ℝ i).comp hf |>.differentiable
        (by norm_num)).differentiableAt (x := t))) i
    have hω : angularVelocity f t = f t 0 * deriv (fun s => f s 1) t -
        f t 1 * deriv (fun s => f s 0) t := by
      simp only [angularVelocity, det2]; rw [hd_eq 0, hd_eq 1]
    rw [hω]
    have hunit := hcirc_deriv t
    have huc := hcirc t
    have key : deriv (fun s => f s 0) t * cos (θ t) -
        f t 0 * sin (θ t) * (f t 0 * deriv (fun s => f s 1) t -
          f t 1 * deriv (fun s => f s 0) t) +
        deriv (fun s => f s 1) t * sin (θ t) +
        f t 1 * cos (θ t) * (f t 0 * deriv (fun s => f s 1) t -
          f t 1 * deriv (fun s => f s 0) t) =
      (f t 0 * deriv (fun s => f s 0) t + f t 1 * deriv (fun s => f s 1) t) *
        (f t 0 * cos (θ t) + f t 1 * sin (θ t)) +
      (deriv (fun s => f s 0) t * cos (θ t) + deriv (fun s => f s 1) t * sin (θ t)) *
        (1 - (f t 0)^2 - (f t 1)^2) := by ring
    linarith [key, mul_eq_zero_of_left hunit (f t 0 * cos (θ t) + f t 1 * sin (θ t)),
              mul_eq_zero_of_right
                (deriv (fun s => f s 0) t * cos (θ t) + deriv (fun s => f s 1) t * sin (θ t))
                (show (1 - (f t 0)^2 - (f t 1)^2) = 0 by linarith)]
  have g_const : ∀ t, g t = g 0 :=
    fun t => is_const_of_deriv_eq_zero g_diff g_deriv_zero 0 t |>.symm
  have g_init : g 0 = 1 := by
    simp only [g]; rw [hinit0, hinit1]
    nlinarith [sin_sq_add_cos_sq (θ 0)]
  intro t
  have hgt : f t 0 * cos (θ t) + f t 1 * sin (θ t) = 1 := by
    have := g_const t; simp only [g] at this; linarith [g_init]
  have huc := hcirc t
  have hcs : cos (θ t) ^ 2 + sin (θ t) ^ 2 = 1 := by linarith [sin_sq_add_cos_sq (θ t)]
  have h : (f t 0 - cos (θ t)) ^ 2 + (f t 1 - sin (θ t)) ^ 2 = 0 := by nlinarith
  exact ⟨by nlinarith [sq_nonneg (f t 0 - cos (θ t)), sq_nonneg (f t 1 - sin (θ t))],
         by nlinarith [sq_nonneg (f t 0 - cos (θ t)), sq_nonneg (f t 1 - sin (θ t))]⟩

theorem angle_function_exists (f : ℝ → Fin 2 → ℝ) (hf : ContDiff ℝ ⊤ f)
    (hcirc : OnUnitCircle f) : ∃ θ : ℝ → ℝ, IsAngleFunction f θ := by
  obtain ⟨θ₀, hcos₀, hsin₀⟩ := exists_angle_of_unit_circle (f 0 0) (f 0 1) (hcirc 0)
  set ω : ℝ → ℝ := angularVelocity f
  set θ : ℝ → ℝ := fun t => θ₀ + ∫ τ in (0 : ℝ)..t, ω τ
  have hω_smooth : ContDiff ℝ ⊤ ω := smooth_angular_velocity f hf
  have hθ_smooth : ContDiff ℝ ⊤ θ := contDiff_infty_integral ω θ₀ hω_smooth
  have hθ_deriv : ∀ t, HasDerivAt θ (ω t) t := by
    intro t
    have hω_cont : Continuous ω := hω_smooth.continuous
    exact (intervalIntegral.integral_hasDerivAt_right
      (hω_cont.intervalIntegrable 0 t)
      (hω_cont.stronglyMeasurableAtFilter _ _)
      hω_cont.continuousAt).const_add θ₀
  have hθ_init : θ 0 = θ₀ := by simp [θ]
  refine ⟨θ, hθ_smooth, ?_⟩
  exact ode_uniqueness f θ hf hcirc hθ_smooth hθ_deriv
    (by rw [hθ_init]; exact hcos₀) (by rw [hθ_init]; exact hsin₀)

theorem angle_function_unique (f : ℝ → Fin 2 → ℝ) (θ₁ θ₂ : ℝ → ℝ)
    (h1 : IsAngleFunction f θ₁) (h2 : IsAngleFunction f θ₂) :
    ∃ k : ℤ, ∀ t, θ₂ t - θ₁ t = 2 * π * k := by

  obtain ⟨hθ1_smooth, hθ1_eq⟩ := h1
  obtain ⟨hθ2_smooth, hθ2_eq⟩ := h2

  have hdiff_smooth : ContDiff ℝ ⊤ (fun t => θ₂ t - θ₁ t) := hθ2_smooth.sub hθ1_smooth

  have hcos_eq_one : ∀ t, cos (θ₂ t - θ₁ t) = 1 := by
    intro t
    rw [cos_sub]
    have ⟨h1a, h1b⟩ := hθ1_eq t
    have ⟨h2a, h2b⟩ := hθ2_eq t
    rw [← h1a, ← h1b, ← h2a, ← h2b]
    have hcs := sin_sq_add_cos_sq (θ₁ t)
    have : f t 0 * f t 0 + f t 1 * f t 1 = sin (θ₁ t) ^ 2 + cos (θ₁ t) ^ 2 := by
      rw [← h1a, ← h1b]; ring
    linarith

  have hint : ∀ t, ∃ k : ℤ, (θ₂ t - θ₁ t) = ↑k * (2 * π) := by
    intro t
    obtain ⟨k, hk⟩ := (cos_eq_one_iff (θ₂ t - θ₁ t)).mp (hcos_eq_one t)
    exact ⟨k, hk.symm⟩


  have hderiv_eq : ∀ t, deriv (fun s => θ₂ s - θ₁ s) t = 0 := by
    intro t

    have hθ1_diff : DifferentiableAt ℝ θ₁ t :=
      (hθ1_smooth.differentiable (by norm_num)).differentiableAt
    have hθ2_diff : DifferentiableAt ℝ θ₂ t :=
      (hθ2_smooth.differentiable (by norm_num)).differentiableAt
    have : deriv (fun s => θ₂ s - θ₁ s) t = deriv θ₂ t - deriv θ₁ t :=
      deriv_sub hθ2_diff hθ1_diff
    rw [this]


    have hf0_eq1 : (fun s => f s 0) = (fun s => cos (θ₁ s)) := funext (fun s => (hθ1_eq s).1)
    have hf1_eq1 : (fun s => f s 1) = (fun s => sin (θ₁ s)) := funext (fun s => (hθ1_eq s).2)
    have hd_θ1 := hθ1_diff.hasDerivAt
    have hd0_1 : HasDerivAt (fun s => f s 0) (-sin (θ₁ t) * deriv θ₁ t) t := by
      rw [hf0_eq1]; exact hd_θ1.cos
    have hd1_1 : HasDerivAt (fun s => f s 1) (cos (θ₁ t) * deriv θ₁ t) t := by
      rw [hf1_eq1]; exact hd_θ1.sin
    have hf0_eq2 : (fun s => f s 0) = (fun s => cos (θ₂ s)) := funext (fun s => (hθ2_eq s).1)
    have hf1_eq2 : (fun s => f s 1) = (fun s => sin (θ₂ s)) := funext (fun s => (hθ2_eq s).2)
    have hd_θ2 := hθ2_diff.hasDerivAt
    have hd0_2 : HasDerivAt (fun s => f s 0) (-sin (θ₂ t) * deriv θ₂ t) t := by
      rw [hf0_eq2]; exact hd_θ2.cos
    have hd1_2 : HasDerivAt (fun s => f s 1) (cos (θ₂ t) * deriv θ₂ t) t := by
      rw [hf1_eq2]; exact hd_θ2.sin

    have heq0 : -sin (θ₁ t) * deriv θ₁ t = -sin (θ₂ t) * deriv θ₂ t :=
      hd0_1.unique hd0_2

    have heq1 : cos (θ₁ t) * deriv θ₁ t = cos (θ₂ t) * deriv θ₂ t :=
      hd1_1.unique hd1_2

    have hceq : cos (θ₁ t) = cos (θ₂ t) := by
      rw [← (hθ1_eq t).1, ← (hθ2_eq t).1]
    have hseq : sin (θ₁ t) = sin (θ₂ t) := by
      rw [← (hθ1_eq t).2, ← (hθ2_eq t).2]


    have h_eq_deriv : deriv θ₂ t = deriv θ₁ t := by
      have h1 : cos (θ₁ t) * deriv θ₁ t = cos (θ₁ t) * deriv θ₂ t := by
        rw [heq1, hceq]
      have h2 : sin (θ₁ t) * deriv θ₁ t = sin (θ₁ t) * deriv θ₂ t := by
        have heq0' := heq0
        rw [← hseq] at heq0'
        linarith
      have hc : cos (θ₁ t) * (deriv θ₁ t - deriv θ₂ t) = 0 := by linarith
      have hs : sin (θ₁ t) * (deriv θ₁ t - deriv θ₂ t) = 0 := by linarith
      have hkey : (deriv θ₁ t - deriv θ₂ t) = 0 := by
        have hsum : cos (θ₁ t) ^ 2 + sin (θ₁ t) ^ 2 = 1 := by
          linarith [sin_sq_add_cos_sq (θ₁ t)]
        nlinarith [sq_abs (cos (θ₁ t)), sq_abs (sin (θ₁ t)),
                   sq_abs (deriv θ₁ t - deriv θ₂ t),
                   mul_self_nonneg (cos (θ₁ t) * (deriv θ₁ t - deriv θ₂ t)),
                   mul_self_nonneg (sin (θ₁ t) * (deriv θ₁ t - deriv θ₂ t)),
                   hc, hs, hsum]
      linarith
    linarith

  have hconst : ∀ t, (θ₂ t - θ₁ t) = (θ₂ 0 - θ₁ 0) := by
    intro t
    exact is_const_of_deriv_eq_zero (hdiff_smooth.differentiable (by norm_num)) hderiv_eq 0 t |>.symm

  obtain ⟨k, hk⟩ := hint 0
  refine ⟨k, fun t => ?_⟩
  rw [hconst t, hk]; ring

theorem angle_function_exists_unique (f : ℝ → Fin 2 → ℝ) (hf : ContDiff ℝ ⊤ f)
    (hcirc : OnUnitCircle f) :
    (∃ θ : ℝ → ℝ, IsAngleFunction f θ) ∧
    (∀ θ₁ θ₂ : ℝ → ℝ, IsAngleFunction f θ₁ → IsAngleFunction f θ₂ →
      ∃ k : ℤ, ∀ t, θ₂ t - θ₁ t = 2 * π * k) :=
  ⟨angle_function_exists f hf hcirc, fun θ₁ θ₂ h1 h2 => angle_function_unique f θ₁ θ₂ h1 h2⟩

noncomputable def degreeReal (f : ℝ → Fin 2 → ℝ) (T : ℝ) : ℝ :=
  (1 / (2 * Real.pi)) * ∫ t in (0 : ℝ)..T, det2 (f t) (deriv f t)

theorem degree_is_integer (f : ℝ → Fin 2 → ℝ) (hf : ContDiff ℝ ⊤ f)
    (hcirc : OnUnitCircle f) (T : ℝ) (hper : ∀ t, f (t + T) = f t) :
    ∃ k : ℤ, degreeReal f T = k := by

  obtain ⟨θ, hθ_smooth, hθ_eq⟩ := angle_function_exists f hf hcirc

  have hcos_eq : cos (θ T) = cos (θ 0) := by
    have h1 := (hθ_eq T).1
    have h2 := (hθ_eq 0).1
    have hfT : f T 0 = f 0 0 := by
      have := hper 0; simp at this; exact congr_fun this 0
    linarith
  have hsin_eq : sin (θ T) = sin (θ 0) := by
    have h1 := (hθ_eq T).2
    have h2 := (hθ_eq 0).2
    have hfT : f T 1 = f 0 1 := by
      have := hper 0; simp at this; exact congr_fun this 1
    linarith

  have hcos_diff : cos (θ T - θ 0) = 1 := by
    rw [cos_sub, hcos_eq, hsin_eq]
    have := sin_sq_add_cos_sq (θ 0)
    nlinarith [sq_nonneg (cos (θ 0)), sq_nonneg (sin (θ 0))]
  obtain ⟨k, hk⟩ := (cos_eq_one_iff (θ T - θ 0)).mp hcos_diff


  suffices h : ∫ t in (0 : ℝ)..T, det2 (f t) (deriv f t) = θ T - θ 0 by
    use k
    unfold degreeReal
    rw [h, ← hk]
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    field_simp

  have hθ_deriv : ∀ t, HasDerivAt θ (det2 (f t) (deriv f t)) t := by
    intro t
    have hθ_diff : DifferentiableAt ℝ θ t :=
      (hθ_smooth.differentiable (by norm_num)).differentiableAt
    have hd_θ := hθ_diff.hasDerivAt
    have hf0_eq : (fun s => f s 0) = (fun s => cos (θ s)) := funext (fun s => (hθ_eq s).1)
    have hf1_eq : (fun s => f s 1) = (fun s => sin (θ s)) := funext (fun s => (hθ_eq s).2)
    have hd0 : HasDerivAt (fun s => f s 0) (-sin (θ t) * deriv θ t) t := by
      rw [hf0_eq]; exact hd_θ.cos
    have hd1 : HasDerivAt (fun s => f s 1) (cos (θ t) * deriv θ t) t := by
      rw [hf1_eq]; exact hd_θ.sin
    have hfi : ∀ i : Fin 2, ContDiff ℝ ⊤ (fun t => f t i) :=
      fun i => (contDiff_apply ℝ ℝ i).comp hf
    have hd_pi := deriv_pi (fun i => ((hfi i).differentiable (by norm_num)).differentiableAt (x := t))
    have hdet_eq : det2 (f t) (deriv f t) = deriv θ t := by
      have hderiv_0 : deriv f t 0 = deriv (fun s => f s 0) t := congr_fun hd_pi 0
      have hderiv_1 : deriv f t 1 = deriv (fun s => f s 1) t := congr_fun hd_pi 1
      unfold det2
      rw [hderiv_0, hderiv_1, hd0.deriv, hd1.deriv, (hθ_eq t).1, (hθ_eq t).2]
      have hcs : sin (θ t) ^ 2 + cos (θ t) ^ 2 = 1 := sin_sq_add_cos_sq (θ t)
      have h1 : cos (θ t) * (cos (θ t) * deriv θ t) - sin (θ t) * (-sin (θ t) * deriv θ t) =
          (sin (θ t) ^ 2 + cos (θ t) ^ 2) * deriv θ t := by ring
      rw [h1, hcs, one_mul]
    rw [hdet_eq]
    exact hd_θ

  have hθ_cont : Continuous (fun t => det2 (f t) (deriv f t)) := by
    have hfi : ∀ i : Fin 2, ContDiff ℝ ⊤ (fun t => f t i) :=
      fun i => (contDiff_apply ℝ ℝ i).comp hf
    have hfi' : ∀ i : Fin 2, ContDiff ℝ ⊤ (fun t => deriv (fun s => f s i) t) := by
      intro i; apply AnalyticOn.contDiff; intro x _
      exact ((hfi i).contDiffAt (x := x)).analyticAt.deriv.analyticWithinAt
    have heq : (fun t => det2 (f t) (deriv f t)) = fun t =>
        (fun t => f t 0) t * (fun t => deriv (fun s => f s 1) t) t -
        (fun t => f t 1) t * (fun t => deriv (fun s => f s 0) t) t := by
      ext t; simp only [det2]
      have hd := deriv_pi (fun i => ((hfi i).differentiable (by norm_num)).differentiableAt (x := t))
      congr 1 <;> congr 1 <;> exact congr_fun hd _
    rw [heq]
    exact (((hfi 0).mul (hfi' 1)).sub ((hfi 1).mul (hfi' 0))).continuous

  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hθ_deriv t)
    (hθ_cont.intervalIntegrable 0 T)

theorem degree_eq_zero_of_not_surjective (f : ℝ → Fin 2 → ℝ) (T : ℝ) (hT : T > 0)
    (hf : ContDiff ℝ ⊤ f) (hcirc : OnUnitCircle f) (hper : ∀ t, f (t + T) = f t)
    (q : Fin 2 → ℝ) (hq : q 0 ^ 2 + q 1 ^ 2 = 1) (hmiss : ∀ t, f t ≠ q) :
    degreeReal f T = 0 := by

  obtain ⟨θ, hθ_smooth, hθ_eq⟩ := angle_function_exists f hf hcirc

  obtain ⟨α₀, hqcos, hqsin⟩ := exists_angle_of_unit_circle (q 0) (q 1) hq

  have hθ_avoids : ∀ t, ∀ k : ℤ, θ t ≠ α₀ + 2 * π * k := by
    intro t k habs
    apply hmiss t
    have hf0 : f t 0 = q 0 := by
      rw [(hθ_eq t).1, habs]
      rw [show α₀ + 2 * π * ↑k = α₀ + ↑k * (2 * π) from by ring]
      rw [cos_add_int_mul_two_pi α₀ k, hqcos]
    have hf1 : f t 1 = q 1 := by
      rw [(hθ_eq t).2, habs]
      rw [show α₀ + 2 * π * ↑k = α₀ + ↑k * (2 * π) from by ring]
      rw [sin_add_int_mul_two_pi α₀ k, hqsin]
    funext i; fin_cases i <;> assumption

  have hcos_eq : cos (θ T) = cos (θ 0) := by
    have h1 := (hθ_eq T).1; have h2 := (hθ_eq 0).1
    have hfT : f T 0 = f 0 0 := by
      have := hper 0; simp at this; exact congr_fun this 0
    linarith
  have hsin_eq : sin (θ T) = sin (θ 0) := by
    have h1 := (hθ_eq T).2; have h2 := (hθ_eq 0).2
    have hfT : f T 1 = f 0 1 := by
      have := hper 0; simp at this; exact congr_fun this 1
    linarith
  have hcos_diff : cos (θ T - θ 0) = 1 := by
    rw [cos_sub, hcos_eq, hsin_eq]
    nlinarith [sin_sq_add_cos_sq (θ 0)]
  obtain ⟨k, hk⟩ := (cos_eq_one_iff (θ T - θ 0)).mp hcos_diff


  suffices hk_zero : k = 0 by
    unfold degreeReal
    suffices h : ∫ t in (0 : ℝ)..T, det2 (f t) (deriv f t) = θ T - θ 0 by
      rw [h, ← hk, hk_zero]
      simp

    have hθ_deriv : ∀ t, HasDerivAt θ (det2 (f t) (deriv f t)) t := by
      intro t
      have hθ_diff : DifferentiableAt ℝ θ t :=
        (hθ_smooth.differentiable (by norm_num)).differentiableAt
      have hd_θ := hθ_diff.hasDerivAt
      have hf0_eq : (fun s => f s 0) = (fun s => cos (θ s)) := funext (fun s => (hθ_eq s).1)
      have hf1_eq : (fun s => f s 1) = (fun s => sin (θ s)) := funext (fun s => (hθ_eq s).2)
      have hd0 : HasDerivAt (fun s => f s 0) (-sin (θ t) * deriv θ t) t := by
        rw [hf0_eq]; exact hd_θ.cos
      have hd1 : HasDerivAt (fun s => f s 1) (cos (θ t) * deriv θ t) t := by
        rw [hf1_eq]; exact hd_θ.sin
      have hfi : ∀ i : Fin 2, ContDiff ℝ ⊤ (fun t => f t i) :=
        fun i => (contDiff_apply ℝ ℝ i).comp hf
      have hd_pi := deriv_pi (fun i => ((hfi i).differentiable (by norm_num)).differentiableAt (x := t))
      have hdet_eq : det2 (f t) (deriv f t) = deriv θ t := by
        have hderiv_0 : deriv f t 0 = deriv (fun s => f s 0) t := congr_fun hd_pi 0
        have hderiv_1 : deriv f t 1 = deriv (fun s => f s 1) t := congr_fun hd_pi 1
        unfold det2
        rw [hderiv_0, hderiv_1, hd0.deriv, hd1.deriv, (hθ_eq t).1, (hθ_eq t).2]
        have hcs : sin (θ t) ^ 2 + cos (θ t) ^ 2 = 1 := sin_sq_add_cos_sq (θ t)
        have h1 : cos (θ t) * (cos (θ t) * deriv θ t) - sin (θ t) * (-sin (θ t) * deriv θ t) =
            (sin (θ t) ^ 2 + cos (θ t) ^ 2) * deriv θ t := by ring
        rw [h1, hcs, one_mul]
      rw [hdet_eq]; exact hd_θ
    have hθ_cont : Continuous (fun t => det2 (f t) (deriv f t)) :=
      (smooth_angular_velocity f hf).continuous
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hθ_deriv t) (hθ_cont.intervalIntegrable 0 T)


  by_contra hk_ne
  have hk_ne_zero : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk_ne

  have hθT : θ T = θ 0 + ↑k * (2 * π) := by linarith [hk.symm]


  have hθ0_avoids : ∀ n : ℤ, θ 0 ≠ α₀ + 2 * π * n := hθ_avoids 0


  have hpi_pos : (0 : ℝ) < 2 * π := by positivity

  have hdiff_large : |θ T - θ 0| ≥ 2 * π := by
    have heq : θ T - θ 0 = ↑k * (2 * π) := by linarith [hk.symm]
    rw [heq, abs_mul, abs_of_pos hpi_pos]
    have : |(k : ℝ)| ≥ 1 := by
      have h1 : (1 : ℤ) ≤ |k| := Int.one_le_abs hk_ne
      exact_mod_cast h1
    nlinarith


  set a := min (θ 0) (θ T)
  set b := max (θ 0) (θ T)
  have hab : b - a ≥ 2 * π := by
    simp only [a, b]; rw [max_sub_min_eq_abs]; exact hdiff_large
  have hab_le : a ≤ b := min_le_max

  set n : ℤ := ⌈(a - α₀) / (2 * π)⌉
  have hn_lb : α₀ + 2 * π * ↑n ≥ a := by
    have h1 := Int.le_ceil ((a - α₀) / (2 * π))

    have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hpi_pos)
    rw [div_mul_cancel₀ _ (ne_of_gt hpi_pos)] at h2
    linarith
  have hn_ub : α₀ + 2 * π * ↑n ≤ b := by
    have h1 := Int.ceil_lt_add_one ((a - α₀) / (2 * π))

    have h2 : (↑n : ℝ) * (2 * π) < (a - α₀) + 2 * π := by
      have h3 : (↑n : ℝ) < (a - α₀) / (2 * π) + 1 := h1
      have h4 : (↑n : ℝ) * (2 * π) < ((a - α₀) / (2 * π) + 1) * (2 * π) :=
        mul_lt_mul_of_pos_right h3 hpi_pos
      have hne : (2 * π : ℝ) ≠ 0 := ne_of_gt hpi_pos
      nlinarith [div_mul_cancel₀ (a - α₀) hne]
    linarith


  have hθ_cont : ContinuousOn θ (Set.Icc 0 T) :=
    hθ_smooth.continuous.continuousOn
  have hT_le : (0 : ℝ) ≤ T := le_of_lt hT

  have hmem : α₀ + 2 * π * ↑n ∈ Set.uIcc (θ 0) (θ T) := by
    rw [Set.mem_uIcc]
    by_cases h : θ 0 ≤ θ T
    · left; exact ⟨by linarith [min_eq_left h], by linarith [max_eq_right h]⟩
    · right
      push_neg at h
      exact ⟨by linarith [min_eq_right (le_of_lt h)], by linarith [max_eq_left (le_of_lt h)]⟩
  have hIVT := intermediate_value_uIcc
    (hθ_cont.mono (Set.uIcc_subset_Icc ⟨le_refl _, hT_le⟩ ⟨hT_le, le_refl _⟩))
  have hval_in_image : α₀ + 2 * π * ↑n ∈ θ '' Set.uIcc 0 T := hIVT hmem
  obtain ⟨s, hs_mem, hs_eq⟩ := hval_in_image
  exact hθ_avoids s n hs_eq

theorem surjective_of_degree_ne_zero (f : ℝ → Fin 2 → ℝ) (T : ℝ) (hT : T > 0)
    (hf : ContDiff ℝ ⊤ f) (hcirc : OnUnitCircle f) (hper : ∀ t, f (t + T) = f t)
    (hdeg : degreeReal f T ≠ 0) :
    ∀ q : Fin 2 → ℝ, q 0 ^ 2 + q 1 ^ 2 = 1 → ∃ t, f t = q := by
  intro q hq
  by_contra hmiss
  push_neg at hmiss
  exact hdeg (degree_eq_zero_of_not_surjective f T hT hf hcirc hper q hq hmiss)


theorem level_crossing_identity (θ : ℝ → ℝ) (T : ℝ) (hT : T > 0)
    (hθ_smooth : ContDiff ℝ ⊤ θ)
    (α : ℝ) (preimages : Finset ℝ)
    (hpre_bounds : ∀ t ∈ preimages, 0 ≤ t ∧ t < T)
    (hpre_val : ∀ t ∈ preimages, ∃ k : ℤ, θ t - α = 2 * π * k)
    (hcomplete : ∀ t, 0 ≤ t → t < T → (∃ k : ℤ, θ t - α = 2 * π * k) → t ∈ preimages)
    (hregular : ∀ t ∈ preimages, deriv θ t ≠ 0)
    (hperiodic : ∃ k : ℤ, θ T - θ 0 = 2 * π * k) :
    (θ T - θ 0) / (2 * π) = ∑ t ∈ preimages, Real.sign (deriv θ t) := by sorry

theorem degree_as_signed_count (f : ℝ → Fin 2 → ℝ) (T : ℝ) (hT : T > 0)
    (hf : ContDiff ℝ ⊤ f) (hcirc : OnUnitCircle f) (hper : ∀ t, f (t + T) = f t)
    (p : Fin 2 → ℝ) (hp : p 0 ^ 2 + p 1 ^ 2 = 1)
    (preimages : Finset ℝ)
    (hpre : ∀ t ∈ preimages, 0 ≤ t ∧ t < T ∧ f t = p)
    (hcomplete : ∀ t, 0 ≤ t → t < T → f t = p → t ∈ preimages)
    (hregular : ∀ t ∈ preimages, deriv f t ≠ 0) :
    degreeReal f T = ∑ t ∈ preimages, Real.sign (det2 p (deriv f t)) := by

  obtain ⟨θ, hθ_smooth, hθ_eq⟩ := angle_function_exists f hf hcirc

  obtain ⟨α, hpcos, hpsin⟩ := exists_angle_of_unit_circle (p 0) (p 1) hp

  have hdeg_eq : degreeReal f T = (θ T - θ 0) / (2 * π) := by
    unfold degreeReal
    have hθ_deriv : ∀ t, HasDerivAt θ (det2 (f t) (deriv f t)) t := by
      intro t
      have hθ_diff : DifferentiableAt ℝ θ t :=
        (hθ_smooth.differentiable (by norm_num)).differentiableAt
      have hd_θ := hθ_diff.hasDerivAt
      have hf0_eq : (fun s => f s 0) = (fun s => cos (θ s)) := funext (fun s => (hθ_eq s).1)
      have hf1_eq : (fun s => f s 1) = (fun s => sin (θ s)) := funext (fun s => (hθ_eq s).2)
      have hd0 : HasDerivAt (fun s => f s 0) (-sin (θ t) * deriv θ t) t := by
        rw [hf0_eq]; exact hd_θ.cos
      have hd1 : HasDerivAt (fun s => f s 1) (cos (θ t) * deriv θ t) t := by
        rw [hf1_eq]; exact hd_θ.sin
      have hfi : ∀ i : Fin 2, ContDiff ℝ ⊤ (fun t => f t i) :=
        fun i => (contDiff_apply ℝ ℝ i).comp hf
      have hd_pi := deriv_pi (fun i => ((hfi i).differentiable (by norm_num)).differentiableAt (x := t))
      have hdet_eq : det2 (f t) (deriv f t) = deriv θ t := by
        have hderiv_0 : deriv f t 0 = deriv (fun s => f s 0) t := congr_fun hd_pi 0
        have hderiv_1 : deriv f t 1 = deriv (fun s => f s 1) t := congr_fun hd_pi 1
        unfold det2
        rw [hderiv_0, hderiv_1, hd0.deriv, hd1.deriv, (hθ_eq t).1, (hθ_eq t).2]
        have hcs : sin (θ t) ^ 2 + cos (θ t) ^ 2 = 1 := sin_sq_add_cos_sq (θ t)
        have h1 : cos (θ t) * (cos (θ t) * deriv θ t) - sin (θ t) * (-sin (θ t) * deriv θ t) =
            (sin (θ t) ^ 2 + cos (θ t) ^ 2) * deriv θ t := by ring
        rw [h1, hcs, one_mul]

      rw [hdet_eq]; exact hd_θ
    have hθ_cont : Continuous (fun t => det2 (f t) (deriv f t)) :=
      (smooth_angular_velocity f hf).continuous
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ => hθ_deriv t) (hθ_cont.intervalIntegrable 0 T)
    rw [hint]
    ring

  have hpre_angle : ∀ t ∈ preimages, ∃ k : ℤ, θ t - α = 2 * π * k := by
    intro t ht
    obtain ⟨_, _, hft⟩ := hpre t ht
    have hcos_eq : cos (θ t) = cos α := by
      rw [← (hθ_eq t).1, ← hpcos]; exact congr_fun hft 0
    have hsin_eq : sin (θ t) = sin α := by
      rw [← (hθ_eq t).2, ← hpsin]; exact congr_fun hft 1
    have hcos_diff : cos (θ t - α) = 1 := by
      rw [cos_sub, hcos_eq, hsin_eq]
      nlinarith [sin_sq_add_cos_sq α]
    obtain ⟨k, hk⟩ := (cos_eq_one_iff (θ t - α)).mp hcos_diff
    exact ⟨k, by linarith⟩

  have hcomplete_angle : ∀ t, 0 ≤ t → t < T → (∃ k : ℤ, θ t - α = 2 * π * k) → t ∈ preimages := by
    intro t h0 hT' ⟨k, hk⟩
    apply hcomplete t h0 hT'
    have hθval : θ t = α + 2 * π * k := by linarith
    have hf0 : f t 0 = p 0 := by
      rw [(hθ_eq t).1, hθval]
      rw [show α + 2 * π * ↑k = α + ↑k * (2 * π) from by ring]
      rw [cos_add_int_mul_two_pi α k, hpcos]
    have hf1 : f t 1 = p 1 := by
      rw [(hθ_eq t).2, hθval]
      rw [show α + 2 * π * ↑k = α + ↑k * (2 * π) from by ring]
      rw [sin_add_int_mul_two_pi α k, hpsin]
    funext i; fin_cases i <;> [exact hf0; exact hf1]

  have hsign_eq : ∀ t ∈ preimages, Real.sign (det2 p (deriv f t)) = Real.sign (deriv θ t) := by
    intro t ht
    obtain ⟨_, _, hft⟩ := hpre t ht
    have hfi : ∀ i : Fin 2, ContDiff ℝ ⊤ (fun t => f t i) :=
      fun i => (contDiff_apply ℝ ℝ i).comp hf
    have hd_pi := deriv_pi (fun i => ((hfi i).differentiable (by norm_num)).differentiableAt (x := t))
    have hθ_diff : DifferentiableAt ℝ θ t :=
      (hθ_smooth.differentiable (by norm_num)).differentiableAt
    have hd_θ := hθ_diff.hasDerivAt
    have hf0_eq : (fun s => f s 0) = (fun s => cos (θ s)) := funext (fun s => (hθ_eq s).1)
    have hf1_eq : (fun s => f s 1) = (fun s => sin (θ s)) := funext (fun s => (hθ_eq s).2)
    have hd0 : HasDerivAt (fun s => f s 0) (-sin (θ t) * deriv θ t) t := by
      rw [hf0_eq]; exact hd_θ.cos
    have hd1 : HasDerivAt (fun s => f s 1) (cos (θ t) * deriv θ t) t := by
      rw [hf1_eq]; exact hd_θ.sin
    have hdet_eq : det2 p (deriv f t) = deriv θ t := by
      unfold det2
      have hderiv_0 : deriv f t 0 = deriv (fun s => f s 0) t := congr_fun hd_pi 0
      have hderiv_1 : deriv f t 1 = deriv (fun s => f s 1) t := congr_fun hd_pi 1
      rw [hderiv_0, hderiv_1, hd0.deriv, hd1.deriv]
      have hp0 : p 0 = cos (θ t) := by rw [← (hθ_eq t).1, ← congr_fun hft 0]
      have hp1 : p 1 = sin (θ t) := by rw [← (hθ_eq t).2, ← congr_fun hft 1]
      rw [hp0, hp1]
      have hcs : sin (θ t) ^ 2 + cos (θ t) ^ 2 = 1 := sin_sq_add_cos_sq (θ t)
      have h1 : cos (θ t) * (cos (θ t) * deriv θ t) - sin (θ t) * (-sin (θ t) * deriv θ t) =
          (sin (θ t) ^ 2 + cos (θ t) ^ 2) * deriv θ t := by ring
      rw [h1, hcs, one_mul]
    rw [hdet_eq]

  have hperiodic : ∃ k : ℤ, θ T - θ 0 = 2 * π * k := by
    have hcos_eq : cos (θ T) = cos (θ 0) := by
      have h1 := (hθ_eq T).1; have h2 := (hθ_eq 0).1
      have hfT : f T 0 = f 0 0 := by
        have := hper 0; simp at this; exact congr_fun this 0
      linarith
    have hsin_eq : sin (θ T) = sin (θ 0) := by
      have h1 := (hθ_eq T).2; have h2 := (hθ_eq 0).2
      have hfT : f T 1 = f 0 1 := by
        have := hper 0; simp at this; exact congr_fun this 1
      linarith
    have hcos_diff : cos (θ T - θ 0) = 1 := by
      rw [cos_sub, hcos_eq, hsin_eq]
      nlinarith [sin_sq_add_cos_sq (θ 0)]
    obtain ⟨k, hk⟩ := (cos_eq_one_iff (θ T - θ 0)).mp hcos_diff
    exact ⟨k, by linarith⟩

  rw [hdeg_eq]
  have hlci := level_crossing_identity θ T hT hθ_smooth α preimages
    (fun t ht => ⟨(hpre t ht).1, (hpre t ht).2.1⟩)
    hpre_angle hcomplete_angle
    (by intro t ht
        have hfi : ∀ i : Fin 2, ContDiff ℝ ⊤ (fun t => f t i) :=
          fun i => (contDiff_apply ℝ ℝ i).comp hf
        have hd_pi := deriv_pi (fun i => ((hfi i).differentiable (by norm_num)).differentiableAt (x := t))
        have hθ_diff : DifferentiableAt ℝ θ t :=
          (hθ_smooth.differentiable (by norm_num)).differentiableAt
        have hd_θ := hθ_diff.hasDerivAt
        have hf0_eq : (fun s => f s 0) = (fun s => cos (θ s)) := funext (fun s => (hθ_eq s).1)
        have hf1_eq : (fun s => f s 1) = (fun s => sin (θ s)) := funext (fun s => (hθ_eq s).2)
        have hd0 : HasDerivAt (fun s => f s 0) (-sin (θ t) * deriv θ t) t := by
          rw [hf0_eq]; exact hd_θ.cos
        have hd1 : HasDerivAt (fun s => f s 1) (cos (θ t) * deriv θ t) t := by
          rw [hf1_eq]; exact hd_θ.sin
        have hdet_eq : det2 (f t) (deriv f t) = deriv θ t := by
          have hderiv_0 : deriv f t 0 = deriv (fun s => f s 0) t := congr_fun hd_pi 0
          have hderiv_1 : deriv f t 1 = deriv (fun s => f s 1) t := congr_fun hd_pi 1
          unfold det2
          rw [hderiv_0, hderiv_1, hd0.deriv, hd1.deriv, (hθ_eq t).1, (hθ_eq t).2]
          have hcs : sin (θ t) ^ 2 + cos (θ t) ^ 2 = 1 := sin_sq_add_cos_sq (θ t)
          have h1 : cos (θ t) * (cos (θ t) * deriv θ t) - sin (θ t) * (-sin (θ t) * deriv θ t) =
              (sin (θ t) ^ 2 + cos (θ t) ^ 2) * deriv θ t := by ring
          rw [h1, hcs, one_mul]
        intro h_zero
        have hd0v : deriv (fun s => f s 0) t = 0 := by
          rw [hd0.deriv, h_zero, mul_zero]
        have hd1v : deriv (fun s => f s 1) t = 0 := by
          rw [hd1.deriv, h_zero, mul_zero]
        have : deriv f t = 0 := by
          rw [hd_pi]; ext i; simp only [Pi.zero_apply]
          fin_cases i <;> assumption
        exact hregular t ht this)
    hperiodic
  rw [hlci]
  exact Finset.sum_congr rfl (fun t ht => (hsign_eq t ht).symm)

end DegreeTheory
