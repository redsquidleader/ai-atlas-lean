/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Atlas.IntroductionToPartialDifferentialEquations.code.CM11.Wave1D

set_option maxHeartbeats 3200000

noncomputable section

open Matrix Real MeasureTheory Filter intervalIntegral

namespace WaveEquation3D

/-- Shorthand for $3$-dimensional Euclidean space $\mathbb{R}^3$ used as the
spatial domain for the wave equation. -/
abbrev E3 := EuclideanSpace ℝ (Fin 3)

/-- Predicate stating that $u : \mathbb{R} \times \mathbb{R}^3 \to \mathbb{R}$
is a $C^2$ solution of the $3$-dimensional wave equation
$-\partial_t^2 u + \Delta u = 0$. -/
structure IsWaveSolution3D (u : ℝ → E3 → ℝ) : Prop where
  smooth : ContDiff ℝ 2 (fun p : ℝ × E3 => u p.1 p.2)
  wave_eq : ∀ t : ℝ, ∀ x : E3,
    fderiv ℝ (fun s => fderiv ℝ (fun s' => u s' x) s 1) t 1 =
    ∑ i : Fin 3,
      fderiv ℝ (fun y => fderiv ℝ (fun y' => u t y') y (EuclideanSpace.single i 1))
        x (EuclideanSpace.single i 1)

/-- Cauchy data for the $3$D wave equation: an initial position $f \in C^3(\mathbb{R}^3)$
and an initial velocity $g \in C^2(\mathbb{R}^3)$. -/
structure CauchyData3D where
  f : E3 → ℝ
  g : E3 → ℝ
  f_smooth : ContDiff ℝ 3 f
  g_smooth : ContDiff ℝ 2 g

/-- Conversion from spherical coordinates $(\theta, \varphi)$ on the unit sphere $S^2 \subset \mathbb{R}^3$
to Cartesian coordinates $(\sin\theta\cos\varphi, \sin\theta\sin\varphi, \cos\theta)$. -/
def sphericalToCart (θ φ : ℝ) : E3 :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm ![sin θ * cos φ, sin θ * sin φ, cos θ]

/-- The spherical mean of $h : \mathbb{R}^3 \to \mathbb{R}$ over the sphere
$\partial B_r(x)$ of radius $r$ centred at $x$, defined via the spherical
parametrization
$\frac{1}{4\pi}\int_0^\pi\!\!\int_0^{2\pi} h(x + r\,\omega(\theta,\varphi))\sin\theta\,d\varphi\,d\theta$. -/
noncomputable def SphericalMean (h : E3 → ℝ) (x : E3) (r : ℝ) : ℝ :=
  (1 / (4 * π)) *
    ∫ θ in (0 : ℝ)..π, ∫ φ in (0 : ℝ)..(2 * π),
      h (x + r • sphericalToCart θ φ) * sin θ

/-- Elementary computation: $\int_0^\pi \sin\theta\, d\theta = 2$. -/
lemma integral_sin_eq_two : ∫ θ in (0 : ℝ)..π, sin θ = 2 := by
  rw [integral_sin]; simp [Real.cos_pi, Real.cos_zero]; ring

/-- The spherical mean over a sphere of radius zero equals the value at the
centre: $\mathrm{SphericalMean}\,h\,x\,0 = h(x)$. -/
lemma sphericalMean_at_zero (h : E3 → ℝ) (x : E3) : SphericalMean h x 0 = h x := by
  unfold SphericalMean; simp only [zero_smul, add_zero]
  simp_rw [show ∀ (θ : ℝ), ∫ φ in (0 : ℝ)..(2 * π), h x * sin θ =
    h x * sin θ * (2 * π) from fun θ => by
      rw [intervalIntegral.integral_const]; simp [smul_eq_mul]; ring]
  rw [show (fun θ => h x * sin θ * (2 * π)) = (fun θ => h x * (2 * π) * sin θ) from by ext; ring]
  rw [intervalIntegral.integral_const_mul, integral_sin_eq_two]
  have hpi : (4 : ℝ) * π ≠ 0 := by positivity
  field_simp; ring

/-- The spherical-to-Cartesian map (viewed as a function of an outer parameter and
the angles $(\theta, \varphi)$) is continuous. -/
lemma sphericalToCart_continuous : Continuous (fun p : (ℝ × ℝ) × ℝ =>
    (EuclideanSpace.equiv (Fin 3) ℝ).symm
      ![sin p.1.2 * cos p.2, sin p.1.2 * sin p.2, cos p.1.2]) := by
  apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp
  apply continuous_pi; intro i
  fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  · exact (continuous_sin.comp (continuous_snd.comp continuous_fst)).mul
      (continuous_cos.comp continuous_snd)
  · exact (continuous_sin.comp (continuous_snd.comp continuous_fst)).mul
      (continuous_sin.comp continuous_snd)
  · exact continuous_cos.comp (continuous_snd.comp continuous_fst)

/-- If $h$ is continuous, then $r \mapsto \mathrm{SphericalMean}\,h\,x\,r$ is
continuous in the radius $r$. -/
lemma sphericalMean_continuous (h : E3 → ℝ) (hh : Continuous h) (x : E3) :
    Continuous (fun r => SphericalMean h x r) := by
  unfold SphericalMean
  apply Continuous.const_mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
  apply Continuous.mul
  · exact hh.comp (continuous_const.add ((continuous_fst.comp continuous_fst).smul
      sphericalToCart_continuous))
  · exact continuous_sin.comp (continuous_snd.comp continuous_fst)

/-- Definitional unfolding of `SphericalMean` as a parametric integral in spherical
coordinates. Used to expose the integral form after the definition is marked irreducible. -/
lemma SphericalMean_eq (h : E3 → ℝ) (x : E3) (r : ℝ) :
    SphericalMean h x r = (1 / (4 * π)) *
      ∫ θ in (0 : ℝ)..π, ∫ φ in (0 : ℝ)..(2 * π),
        h (x + r • sphericalToCart θ φ) * sin θ := rfl


attribute [irreducible] SphericalMean

/-- The surface integral $\int_{\partial B_r(x)} h\,d\sigma = 4\pi r^2 \cdot \mathrm{SphericalMean}\,h\,x\,r$
on the sphere of radius $r$ around $x$. -/
noncomputable def SphereIntegral (h : E3 → ℝ) (x : E3) (r : ℝ) : ℝ :=
  4 * π * r ^ 2 * SphericalMean h x r

/-- The integral over $\partial B_r(x)$ of the radial (outward normal) derivative of $h$,
expressed as $4\pi r^2$ times the radial derivative of the spherical mean. -/
noncomputable def SphereIntegralNormalDeriv (h : E3 → ℝ) (x : E3) (r : ℝ) : ℝ :=
  4 * π * r ^ 2 * deriv (fun ρ => SphericalMean h x ρ) r

/-- Leibniz / differentiation-under-the-integral for the second time derivative:
the iterated derivative of order $2$ commutes with the spherical integral. -/
theorem leibniz_sphericalCoord_iteratedDeriv2
    (u : ℝ → E3 → ℝ) (s r : ℝ) (x : E3)
    (hsmooth : ContDiff ℝ 2 (fun p : ℝ × E3 => u p.1 p.2)) :
    iteratedDeriv 2
      (fun s' => ∫ θ in (0 : ℝ)..π, ∫ φ in (0 : ℝ)..(2 * π),
        u s' (x + r • sphericalToCart θ φ) * sin θ) s =
    ∫ θ in (0 : ℝ)..π, ∫ φ in (0 : ℝ)..(2 * π),
      iteratedDeriv 2 (fun s' => u s' (x + r • sphericalToCart θ φ)) s * sin θ := by sorry

/-- Smoothness of the spherical-coordinate integral in the time parameter $s'$:
the map $s' \mapsto \int_{S^2} u(s', x + r\omega)\,d\sigma(\omega)$ is $C^2$. -/
theorem contDiffAt_sphericalCoord_integral
    (u : ℝ → E3 → ℝ) (s r : ℝ) (x : E3)
    (hsmooth : ContDiff ℝ 2 (fun p : ℝ × E3 => u p.1 p.2)) :
    ContDiffAt ℝ 2
      (fun s' => ∫ θ in (0 : ℝ)..π, ∫ φ in (0 : ℝ)..(2 * π),
        u s' (x + r • sphericalToCart θ φ) * sin θ) s := by sorry

/-- The second time derivative passes inside the spherical mean:
$\partial_t^2 \mathrm{SphericalMean}(u(t,\cdot))(x, r) = \mathrm{SphericalMean}(\partial_t^2 u(t,\cdot))(x, r)$. -/
theorem sphericalMean_leibniz_deriv2 (u : ℝ → E3 → ℝ) (s r : ℝ) (x : E3) (hu : IsWaveSolution3D u) : iteratedDeriv 2 (fun s' => SphericalMean (u s') x r) s = SphericalMean (fun y => iteratedDeriv 2 (fun s' => u s' y) s) x r := by

  conv_lhs =>
    rw [show (fun s' => SphericalMean (u s') x r) =
      (fun s' => (1 / (4 * π)) *
        ∫ θ in (0 : ℝ)..π, ∫ φ in (0 : ℝ)..(2 * π),
          u s' (x + r • sphericalToCart θ φ) * sin θ)
      from by ext s'; exact SphericalMean_eq (u s') x r]

  rw [iteratedDeriv_const_mul (1 / (4 * π))
    (contDiffAt_sphericalCoord_integral u s r x hu.smooth)]

  rw [leibniz_sphericalCoord_iteratedDeriv2 u s r x hu.smooth]

  rw [SphericalMean_eq]

/-- For a wave solution $u$, the spherical mean $s' \mapsto \mathrm{SphericalMean}(u(s',\cdot))(x,r)$
is differentiable at every time $s$. -/
theorem sphericalMean_differentiable_time (u : ℝ → E3 → ℝ) (r : ℝ) (x : E3) (hu : IsWaveSolution3D u) : ∀ s, DifferentiableAt ℝ (fun s' => SphericalMean (u s') x r) s := by
  intro s

  have heq : (fun s' => SphericalMean (u s') x r) =
    (fun s' => (1 / (4 * π)) * ∫ θ in (0:ℝ)..π, ∫ φ in (0:ℝ)..(2*π),
      u s' (x + r • sphericalToCart θ φ) * sin θ) := by
    ext s'; exact SphericalMean_eq (u s') x r
  rw [heq]

  apply DifferentiableAt.const_mul

  exact (contDiffAt_sphericalCoord_integral u s r x hu.smooth).differentiableAt (by norm_num)

/-- The first time derivative of the spherical mean is itself differentiable in time
when $u$ is a $C^2$ wave solution. -/
theorem sphericalMean_deriv_differentiable_time (u : ℝ → E3 → ℝ) (r : ℝ) (x : E3) (hu : IsWaveSolution3D u) : ∀ s, DifferentiableAt ℝ (fun s' => deriv (fun s'' => SphericalMean (u s'') x r) s') s := by
  intro s

  have heq : (fun s' => SphericalMean (u s') x r) =
    (fun s' => (1 / (4 * π)) * ∫ θ in (0:ℝ)..π, ∫ φ in (0:ℝ)..(2*π),
      u s' (x + r • sphericalToCart θ φ) * sin θ) := by
    ext s'; exact SphericalMean_eq (u s') x r


  have hC2 : ContDiff ℝ 2 (fun s' => SphericalMean (u s') x r) := by
    rw [heq]
    exact contDiff_const.mul
      (contDiff_iff_contDiffAt.mpr (fun s' =>
        contDiffAt_sphericalCoord_integral u s' r x hu.smooth))

  exact hC2.differentiable_deriv_two.differentiableAt

/-- Leibniz / differentiation-under-the-integral for the first time derivative
of the parametric spherical integral. -/
theorem leibniz_sphericalCoord_deriv1
    (u : ℝ → E3 → ℝ) (s r : ℝ) (x : E3)
    (hsmooth : ContDiff ℝ 2 (fun p : ℝ × E3 => u p.1 p.2)) :
    deriv
      (fun s' => ∫ θ in (0 : ℝ)..π, ∫ φ in (0 : ℝ)..(2 * π),
        u s' (x + r • sphericalToCart θ φ) * sin θ) s =
    ∫ θ in (0 : ℝ)..π, ∫ φ in (0 : ℝ)..(2 * π),
      deriv (fun s' => u s' (x + r • sphericalToCart θ φ)) s * sin θ := by sorry

/-- Fréchet-derivative form of differentiation under the spherical mean in time:
$\partial_t \mathrm{SphericalMean}(u(t,\cdot))(x,r) = \mathrm{SphericalMean}(\partial_t u(t,\cdot))(x,r)$. -/
theorem sphericalMean_leibniz_deriv1
    (u : ℝ → E3 → ℝ) (s : ℝ) (r : ℝ) (x : E3) (hu : IsWaveSolution3D u) :
    fderiv ℝ (fun s' => SphericalMean (u s') x r) s =
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      (SphericalMean (fun y => fderiv ℝ (fun s' => u s' y) s 1) x r) := by

  apply ContinuousLinearMap.ext_ring

  rw [fderiv_apply_one_eq_deriv]

  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul]

  simp_rw [fderiv_apply_one_eq_deriv]


  conv_lhs =>
    rw [show (fun s' => SphericalMean (u s') x r) =
      (fun s' => (1 / (4 * π)) *
        ∫ θ in (0 : ℝ)..π, ∫ φ in (0 : ℝ)..(2 * π),
          u s' (x + r • sphericalToCart θ φ) * sin θ)
      from by ext s'; exact SphericalMean_eq (u s') x r]

  rw [deriv_const_mul (1 / (4 * π))
    ((contDiffAt_sphericalCoord_integral u s r x hu.smooth).differentiableAt (by norm_num))]

  rw [leibniz_sphericalCoord_deriv1 u s r x hu.smooth]

  rw [SphericalMean_eq]

/-- For a $C^2$ function $f$, the spherical mean $\rho \mapsto \mathrm{SphericalMean}\,f\,x\,\rho$
has a derivative at every positive radius $r$. -/
theorem sphericalMean_radius_hasDerivAt
    (f : E3 → ℝ) (x : E3) (r : ℝ) (_hr : 0 < r)
    (hf : ContDiff ℝ 2 f) :
    HasDerivAt (fun ρ => SphericalMean f x ρ)
      (deriv (fun ρ => SphericalMean f x ρ) r) r := by

  suffices h : DifferentiableAt ℝ (fun ρ => SphericalMean f x ρ) r from h.hasDerivAt

  have heq : (fun ρ => SphericalMean f x ρ) = fun ρ => (1 / (4 * π)) *
      ∫ θ in (0 : ℝ)..π, ∫ φ in (0 : ℝ)..(2 * π),
        f (x + ρ • sphericalToCart θ φ) * sin θ := by
    ext ρ; exact SphericalMean_eq f x ρ
  rw [heq]

  apply DifferentiableAt.const_mul


  let u_aux : ℝ → E3 → ℝ := fun ρ y => f (x + ρ • y)
  have hsmooth : ContDiff ℝ 2 (fun p : ℝ × E3 => u_aux p.1 p.2) := by
    apply hf.comp
    exact contDiff_const.add (contDiff_fst.smul contDiff_snd)
  have h_contdiff := contDiffAt_sphericalCoord_integral u_aux r 1 0 hsmooth

  have h_diff := h_contdiff.differentiableAt (by norm_num)
  exact h_diff.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun ρ => by
      simp only [u_aux, zero_add, one_smul])

/-- Packaged Leibniz statement for second time derivatives of the spherical mean:
$\mathrm{SphericalMean}(u(\cdot,\cdot))$ is twice differentiable in $t$ and the
second derivative commutes with the spherical mean. -/
theorem leibniz_sphericalMean_tt
    (u : ℝ → E3 → ℝ) (hu : IsWaveSolution3D u)
    (r : ℝ) (_hr : 0 ≤ r) (x : E3) :
    (∀ s, DifferentiableAt ℝ (fun s' => SphericalMean (u s') x r) s) ∧
    (∀ s, DifferentiableAt ℝ
      (fun s' => fderiv ℝ (fun s'' => SphericalMean (u s'') x r) s' 1) s) ∧
    (∀ t, fderiv ℝ (fun s => fderiv ℝ (fun s' =>
        SphericalMean (u s') x r) s 1) t 1 =
      SphericalMean (fun y =>
        fderiv ℝ (fun s => fderiv ℝ (fun s' => u s' y) s 1) t 1) x r) := by
  refine ⟨?_, ?_, ?_⟩
  · exact sphericalMean_differentiable_time u r x hu
  · intro s
    simp only [fderiv_apply_one_eq_deriv]
    exact sphericalMean_deriv_differentiable_time u r x hu s
  · intro t
    simp only [fderiv_apply_one_eq_deriv]
    have h := sphericalMean_leibniz_deriv2 u t r x hu
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at h
    exact h

/-- Product-rule identity: for $f \in C^2$,
$\frac{d^2}{d\rho^2}(\rho f(\rho))\big|_{\rho = x} = x f''(x) + 2 f'(x)$. -/
lemma iteratedDeriv_two_mul_id (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x : ℝ) :
    iteratedDeriv 2 (fun ρ => ρ * f ρ) x = x * iteratedDeriv 2 f x + 2 * deriv f x := by
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have hf' : Differentiable ℝ f := hf.differentiable two_ne_zero
  have hf'' : Differentiable ℝ (deriv f) := hf.differentiable_deriv_two

  have h1 : ∀ y, HasDerivAt (fun ρ => ρ * f ρ) (f y + y * deriv f y) y := by
    intro y
    have h := (hasDerivAt_id y).mul (hf'.differentiableAt.hasDerivAt)
    convert h using 1; simp
  have h1_eq : ∀ y, deriv (fun ρ => ρ * f ρ) y = f y + y * deriv f y :=
    fun y => (h1 y).deriv

  have h2 : HasDerivAt (fun y => f y + y * deriv f y)
      (deriv f x + (deriv f x + x * deriv (deriv f) x)) x := by
    exact (hf'.differentiableAt.hasDerivAt).add (by
      have h := (hasDerivAt_id x).mul (hf''.differentiableAt.hasDerivAt)
      convert h using 1; simp)
  have : deriv (deriv fun ρ => ρ * f ρ) x = deriv (fun y => f y + y * deriv f y) x := by
    congr 1; exact funext h1_eq
  rw [this, h2.deriv]; ring

/-- For a wave solution $u$, the spherical mean $\rho \mapsto \mathrm{SphericalMean}(u(t,\cdot))(x, \rho)$
is $C^2$ as a function of the radius. -/
theorem sphericalMean_contDiff_radius (u : ℝ → E3 → ℝ) (hu : IsWaveSolution3D u)
    (t : ℝ) (x : E3) : ContDiff ℝ 2 (SphericalMean (u t) x) := by
  set w : ℝ → E3 → ℝ := fun ρ z => (u t) (x + ρ • z) with hw_def

  have hw_smooth : ContDiff ℝ 2 (fun p : ℝ × E3 => w p.1 p.2) := by
    show ContDiff ℝ 2 (fun p : ℝ × E3 => (u t) (x + p.1 • p.2))
    have hut : ContDiff ℝ 2 (u t) := by
      have : u t = (fun p : ℝ × E3 => u p.1 p.2) ∘ (fun y => (t, y)) := by ext y; simp
      rw [this]; exact hu.smooth.comp (contDiff_prodMk_right t)
    exact hut.comp ((contDiff_const.add (contDiff_fst.smul contDiff_snd)).of_le le_top)


  have heq : SphericalMean (u t) x = fun ρ => (1 / (4 * π)) *
      (∫ θ in (0 : ℝ)..π, ∫ φ in (0 : ℝ)..(2 * π),
        w ρ ((0 : E3) + (1 : ℝ) • sphericalToCart θ φ) * sin θ) := by
    ext ρ; rw [SphericalMean_eq]
    congr 1; congr 1; ext θ; congr 1; ext φ
    simp [hw_def]
  rw [heq]

  exact contDiff_const.mul
    (contDiff_iff_contDiffAt.mpr fun ρ =>
      contDiffAt_sphericalCoord_integral w ρ 1 0 hw_smooth)

/-- Darboux-type identity (via divergence theorem and the coarea formula):
$r \cdot \mathrm{SphericalMean}(\Delta f)(x, r) = r M_f''(r) + 2 M_f'(r)$,
where $M_f(r) = \mathrm{SphericalMean}\,f\,x\,r$. -/
theorem divergence_coarea_darboux_identity
    (f : E3 → ℝ) (x : E3) (r : ℝ)
    (hf : ContDiff ℝ 2 f) :
    r * SphericalMean (fun y => ∑ i : Fin 3,
      fderiv ℝ (fun z => fderiv ℝ f z (EuclideanSpace.single i 1))
        y (EuclideanSpace.single i 1)) x r =
    r * iteratedDeriv 2 (SphericalMean f x) r +
      2 * deriv (SphericalMean f x) r := by sorry

/-- Specialisation of the Darboux identity to a slice $u(t, \cdot)$ of a wave solution. -/
theorem darboux_sphericalMean_expanded (u : ℝ → E3 → ℝ) (hu : IsWaveSolution3D u)
    (t : ℝ) (x : E3) (r : ℝ) :
    r * SphericalMean (fun y => ∑ i : Fin 3,
      fderiv ℝ (fun z => fderiv ℝ (fun z' => u t z') z (EuclideanSpace.single i 1))
        y (EuclideanSpace.single i 1)) x r =
    r * iteratedDeriv 2 (SphericalMean (u t) x) r +
      2 * deriv (SphericalMean (u t) x) r := by
  have hut : ContDiff ℝ 2 (u t) := by
    have : u t = (fun p : ℝ × E3 => u p.1 p.2) ∘ (fun y => (t, y)) := by ext y; simp
    rw [this]; exact hu.smooth.comp (contDiff_prodMk_right t)
  exact divergence_coarea_darboux_identity (u t) x r hut

/-- Compact form of the Darboux identity, rewriting the right-hand side as
$\partial_\rho^2(\rho \cdot \mathrm{SphericalMean}(u(t,\cdot))(x,\rho))$. -/
theorem darboux_sphericalMean_core (u : ℝ → E3 → ℝ) (hu : IsWaveSolution3D u)
    (t : ℝ) (x : E3) (r : ℝ) :
    r * SphericalMean (fun y => ∑ i : Fin 3,
      fderiv ℝ (fun z => fderiv ℝ (fun z' => u t z') z (EuclideanSpace.single i 1))
        y (EuclideanSpace.single i 1)) x r =
    iteratedDeriv 2 (fun ρ => ρ * SphericalMean (u t) x ρ) r := by

  have h_expanded := darboux_sphericalMean_expanded u hu t x r

  have h_contdiff := sphericalMean_contDiff_radius u hu t x
  rw [iteratedDeriv_two_mul_id (SphericalMean (u t) x) h_contdiff r]

  exact h_expanded

/-- Decomposition relating the spherical mean of the Laplacian of $u(t,\cdot)$
to the radial second derivative of the spherical mean (expanded version). -/
theorem sphericalMean_laplacian_decomp (u : ℝ → E3 → ℝ) (hu : IsWaveSolution3D u)
    (t : ℝ) (x : E3) (r : ℝ) :
    r * SphericalMean (fun y => ∑ i : Fin 3,
      fderiv ℝ (fun z => fderiv ℝ (fun z' => u t z') z (EuclideanSpace.single i 1))
        y (EuclideanSpace.single i 1)) x r =
    r * iteratedDeriv 2 (SphericalMean (u t) x) r +
      2 * deriv (SphericalMean (u t) x) r := by

  have h_darboux := darboux_sphericalMean_core u hu t x r

  have h_contdiff := sphericalMean_contDiff_radius u hu t x
  rw [h_darboux, iteratedDeriv_two_mul_id (SphericalMean (u t) x) h_contdiff r]

/-- Equivalent compact form of the Darboux identity for $u(t,\cdot)$. -/
theorem darboux_sphericalMean_eq (u : ℝ → E3 → ℝ) (hu : IsWaveSolution3D u) (t : ℝ) (x : E3) (r : ℝ) : r * SphericalMean (fun y => ∑ i : Fin 3, fderiv ℝ (fun z => fderiv ℝ (fun z' => u t z') z (EuclideanSpace.single i 1)) y (EuclideanSpace.single i 1)) x r = iteratedDeriv 2 (fun ρ => ρ * SphericalMean (u t) x ρ) r := by

  have h_radial := sphericalMean_laplacian_decomp u hu t x r

  have h_contdiff := sphericalMean_contDiff_radius u hu t x
  rw [iteratedDeriv_two_mul_id (SphericalMean (u t) x) h_contdiff r]

  exact h_radial

/-- The Darboux identity rewritten with the second radial derivative expressed via `fderiv`:
$r \cdot \mathrm{SphericalMean}(\Delta u(t,\cdot))(x,r) = \partial_\rho^2(\rho \cdot M(\rho))|_{\rho=r}$. -/
theorem divergence_darboux_sphericalMean
    (u : ℝ → E3 → ℝ) (hu : IsWaveSolution3D u)
    (t r : ℝ) (_hr : 0 ≤ r) (x : E3) :
    r * SphericalMean (fun y =>
      ∑ i : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ (fun z' => u t z') z (EuclideanSpace.single i 1))
          y (EuclideanSpace.single i 1)) x r =
    fderiv ℝ (fun ρ => fderiv ℝ (fun ρ' =>
      ρ' * SphericalMean (u t) x ρ') ρ 1) r 1 := by
  simp only [fderiv_apply_one_eq_deriv]
  have h := darboux_sphericalMean_eq u hu t x r
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at h
  exact h

/-- The second time derivative commutes with multiplication by $r$ and with the spherical mean:
$\partial_t^2 (r \cdot \mathrm{SphericalMean}(u(\cdot,\cdot))(x,r)) = r \cdot \mathrm{SphericalMean}(\partial_t^2 u(\cdot,\cdot))(x,r)$. -/
theorem sphericalMean_commute_with_tt
    (u : ℝ → E3 → ℝ) (hu : IsWaveSolution3D u)
    (t r : ℝ) (hr : 0 ≤ r) (x : E3) :
    fderiv ℝ (fun s => fderiv ℝ (fun s' =>
      r * SphericalMean (u s') x r) s 1) t 1 =
    r * SphericalMean (fun y =>
      fderiv ℝ (fun s => fderiv ℝ (fun s' => u s' y) s 1) t 1) x r := by

  obtain ⟨hdiff1, hdiff2, hcomm⟩ := leibniz_sphericalMean_tt u hu r hr x


  have inner_eq : ∀ s, fderiv ℝ (fun s' => r * SphericalMean (u s') x r) s =
      r • fderiv ℝ (fun s' => SphericalMean (u s') x r) s := by
    intro s; exact fderiv_const_mul (hdiff1 s) r

  have fun_eq : (fun s => fderiv ℝ (fun s' => r * SphericalMean (u s') x r) s 1) =
      (fun s => r * fderiv ℝ (fun s' => SphericalMean (u s') x r) s 1) := by
    ext s; rw [inner_eq s, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [fun_eq]

  rw [show (fun s => r * fderiv ℝ (fun s' => SphericalMean (u s') x r) s 1) =
      (fun s => r * (fun s' => fderiv ℝ (fun s'' => SphericalMean (u s'') x r) s' 1) s) from rfl]
  rw [fderiv_const_mul (hdiff2 t) r, ContinuousLinearMap.smul_apply, smul_eq_mul]

  rw [hcomm t]

/-- Restates the Darboux identity in `fderiv` notation, identifying the spherical
mean of the Laplacian with a radial second-derivative expression. -/
theorem sphericalMean_laplacian_radial
    (u : ℝ → E3 → ℝ) (hu : IsWaveSolution3D u)
    (t r : ℝ) (hr : 0 ≤ r) (x : E3) :
    r * SphericalMean (fun y =>
      ∑ i : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ (fun z' => u t z') z (EuclideanSpace.single i 1))
          y (EuclideanSpace.single i 1)) x r =
    fderiv ℝ (fun ρ => fderiv ℝ (fun ρ' =>
      ρ' * SphericalMean (u t) x ρ') ρ 1) r 1 :=
  divergence_darboux_sphericalMean u hu t r hr x

/-- Key reduction: $w(t,r) := r \cdot \mathrm{SphericalMean}(u(t,\cdot))(x,r)$ satisfies the
$1+1$-dimensional wave equation $\partial_t^2 w = \partial_r^2 w$. -/
theorem sphericalMean_wave_reduction
    (u : ℝ → E3 → ℝ) (hu : IsWaveSolution3D u)
    (t r : ℝ) (hr : 0 ≤ r) (x : E3) :
    fderiv ℝ (fun s => fderiv ℝ (fun s' =>
      r * SphericalMean (u s') x r) s 1) t 1 =
    fderiv ℝ (fun ρ => fderiv ℝ (fun ρ' =>
      ρ' * SphericalMean (u t) x ρ') ρ 1) r 1 := by

  rw [sphericalMean_commute_with_tt u hu t r hr x]


  have wave_sub : (fun y =>
      fderiv ℝ (fun s => fderiv ℝ (fun s' => u s' y) s 1) t 1) =
    (fun y =>
      ∑ i : Fin 3,
        fderiv ℝ (fun z => fderiv ℝ (fun z' => u t z') z (EuclideanSpace.single i 1))
          y (EuclideanSpace.single i 1)) := by
    ext y; exact hu.wave_eq t y
  rw [wave_sub]

  exact sphericalMean_laplacian_radial u hu t r hr x

/-- Initial time derivative of $t \mapsto r \cdot \mathrm{SphericalMean}(u(t,\cdot))(x,r)$ at $t=0$
equals $r \cdot \mathrm{SphericalMean}(\partial_t u(0,\cdot))(x,r)$. -/
theorem sphericalMean_time_deriv
    (u : ℝ → E3 → ℝ) (hu : IsWaveSolution3D u)
    (r : ℝ) (_hr : 0 < r) (x : E3) :
    fderiv ℝ (fun t => r * SphericalMean (u t) x r) 0 1 =
      r * SphericalMean (fun y => fderiv ℝ (fun t => u t y) 0 1) x r := by
  have hdiff := sphericalMean_differentiable_time u r x hu
  rw [fderiv_const_mul (hdiff 0) r]
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [sphericalMean_leibniz_deriv1 u 0 r x hu]
  simp [ContinuousLinearMap.smulRight_apply]

/-- For a continuous $h$, the spherical mean tends to the centre value as the radius
shrinks to $0^+$: $\lim_{r \to 0^+} \mathrm{SphericalMean}\,h\,x\,r = h(x)$. -/
theorem sphericalMean_limit_zero (h : E3 → ℝ) (hh : Continuous h) (x : E3) :
    Tendsto (fun r => SphericalMean h x r) (nhdsWithin 0 (Set.Ioi 0)) (nhds (h x)) := by
  rw [← sphericalMean_at_zero h x]
  exact ((sphericalMean_continuous h hh x).continuousAt).continuousWithinAt.tendsto

/-- D'Alembert-style formula for the wave equation on the half-line $\{r \ge 0\}$
with Dirichlet boundary $w(t,0) = 0$, vanishing odd-extended initial data $F, G$ with
$F(0) = G(0) = 0$. For $r \le t$,
$w(t, r) = \tfrac12(F(r+t) - F(t-r)) + \tfrac12 \int_{t-r}^{r+t} G(\rho)\,d\rho$. -/
theorem dalembert_halfline_representation
    (w : ℝ → ℝ → ℝ) (F G : ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (hG : ContDiff ℝ 1 G)
    (hF0 : F 0 = 0) (hG0 : G 0 = 0)
    (hw_reg : ContDiff ℝ 2 (fun p : ℝ × ℝ => w p.1 p.2))
    (hw_wave : ∀ t r : ℝ, 0 ≤ r →
      deriv (fun t' => deriv (fun t'' => w t'' r) t') t =
      deriv (fun r' => deriv (fun r'' => w t r'') r') r)
    (hw_boundary : ∀ t : ℝ, w t 0 = 0)
    (hw_initial_pos : ∀ r : ℝ, 0 ≤ r → w 0 r = F r)
    (hw_initial_vel : ∀ r : ℝ, 0 < r → HasDerivAt (fun t => w t r) (G r) 0)
    (t r : ℝ) (ht : 0 ≤ t) (hr : 0 ≤ r) (hrt : r ≤ t) :
    w t r = (1 / 2) * (F (r + t) - F (t - r)) +
      (1 / 2) * ∫ ρ in (t - r)..(r + t), G ρ := by

  have h_uniq := WaveEquation1D.dAlembert_halfline_uniqueness F G w hF.contDiffOn hG.contDiffOn hF0 hG0
    hw_reg.contDiffOn (fun t r _ht hr => hw_wave t r hr) hw_boundary hw_initial_pos hw_initial_vel

  have hw_eq := h_uniq t r ht hr

  have h_formula := WaveEquation1D.dAlembert_halfline_formula_xtle F G hF.contDiffOn hG.contDiffOn hF0 hG0 t r ht hr hrt

  rw [hw_eq, h_formula]
  ring

/-- The "tilde" initial position: $\tilde F(r, x) := r \cdot \mathrm{SphericalMean}(f)(x, r)$,
the spatial profile of the auxiliary $1+1$-dimensional wave problem associated with $u$. -/
def F_tilde (data : CauchyData3D) (r : ℝ) (x : E3) : ℝ :=
  r * SphericalMean data.f x r

/-- The "tilde" initial velocity: $\tilde G(r, x) := r \cdot \mathrm{SphericalMean}(g)(x, r)$. -/
def G_tilde (data : CauchyData3D) (r : ℝ) (x : E3) : ℝ :=
  r * SphericalMean data.g x r

/-- The surface integral equals the area of the sphere times the spherical mean:
$\int_{\partial B_r(x)} h\,d\sigma = 4\pi r^2 \cdot \mathrm{SphericalMean}\,h\,x\,r$. -/
theorem sphere_integral_eq_area_times_mean
    (h : E3 → ℝ) (x : E3) (r : ℝ) :
    SphereIntegral h x r = 4 * π * r ^ 2 * SphericalMean h x r := by
  rfl

/-- The integral of the outward normal derivative is $4\pi t^2$ times the radial derivative
of the spherical mean. -/
theorem sphericalMean_normal_deriv_relation
    (f : E3 → ℝ) (x : E3) (t : ℝ) (_ht : 0 < t) :
    SphereIntegralNormalDeriv f x t =
      4 * π * t ^ 2 * deriv (fun r => SphericalMean f x r) t := by
  rfl

/-- Product-rule derivative of $\tilde F$: at $t > 0$,
$\frac{d}{dr}\big(r \cdot \mathrm{SphericalMean}\,f\,x\,r\big)\big|_{r=t} =
\mathrm{SphericalMean}\,f\,x\,t + t \cdot \partial_r\mathrm{SphericalMean}\,f\,x\,t$. -/
theorem F_tilde_hasDerivAt
    (f : E3 → ℝ) (x : E3) (t : ℝ) (ht : 0 < t)
    (hf : ContDiff ℝ 2 f) :
    HasDerivAt (fun r => r * SphericalMean f x r)
      (SphericalMean f x t + t * deriv (fun r => SphericalMean f x r) t) t := by
  have hd := sphericalMean_radius_hasDerivAt f x t ht hf
  have h1 : HasDerivAt (fun r => r) 1 t := hasDerivAt_id t
  have h2 := h1.mul hd
  convert h2 using 1
  ring

/-- The symmetric difference quotient $(f(t+h) - f(t-h))/(2h)$ tends to the derivative
$f'(t)$ as $h \to 0^+$, provided $f$ has a derivative $d$ at $t$. -/
theorem symmetric_derivative_tendsto (f : ℝ → ℝ) (t d : ℝ) (hf : HasDerivAt f d t) :
    Tendsto (fun h => (f (t + h) - f (t - h)) / (2 * h))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds d) := by

  have hfwd : Tendsto (fun h => h⁻¹ • (f (t + h) - f t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds d) :=
    hf.tendsto_slope_zero_right

  have hbwd_left : Tendsto (fun s => s⁻¹ • (f (t + s) - f t))
      (nhdsWithin 0 (Set.Iio 0)) (nhds d) :=
    hf.tendsto_slope_zero_left

  have hmap : Tendsto (fun h : ℝ => -h) (nhdsWithin (0:ℝ) (Set.Ioi 0))
      (nhdsWithin 0 (Set.Iio 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (by simpa using continuous_neg.tendsto (0 : ℝ) :
        Tendsto (fun h : ℝ => -h) (nhds 0) (nhds 0)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
      simp [Set.mem_Iio, hh]

  have hbwd : Tendsto (fun h => (-h)⁻¹ • (f (t + (-h)) - f t))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds d) :=
    hbwd_left.comp hmap

  have hbwd' : Tendsto (fun h => h⁻¹ • (f t - f (t - h)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds d) := by
    have : (fun h => h⁻¹ • (f t - f (t - h))) =
        (fun h => (-h)⁻¹ • (f (t + (-h)) - f t)) := by
      ext h; simp [inv_neg, smul_eq_mul, sub_eq_add_neg]; ring
    rw [this]; exact hbwd

  have hsum : Tendsto (fun h => h⁻¹ • (f (t + h) - f t) + h⁻¹ • (f t - f (t - h)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (d + d)) :=
    hfwd.add hbwd'

  have hdiv : Tendsto (fun h => (h⁻¹ • (f (t + h) - f t) + h⁻¹ • (f t - f (t - h))) / 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((d + d) / 2)) :=
    hsum.div_const 2
  rw [show (d + d) / 2 = d from by ring] at hdiv

  exact hdiv.congr (fun h => by
    simp [smul_eq_mul]
    by_cases hh : h = 0
    · simp [hh]
    · field_simp; ring)

/-- For a continuous $g$, the integral average over a shrinking symmetric interval
$\frac{1}{2h}\int_{t-h}^{t+h} g(\rho)\,d\rho$ tends to $g(t)$ as $h \to 0^+$. -/
theorem integral_average_tendsto (g : ℝ → ℝ) (t : ℝ) (hg : Continuous g) :
    Tendsto (fun h => (∫ ρ in (t - h)..(h + t), g ρ) / (2 * h))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (g t)) := by

  let G : ℝ → ℝ := fun u => ∫ x in t..u, g x

  have hG : HasDerivAt G (g t) t :=
    integral_hasDerivAt_right (hg.intervalIntegrable _ _)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt

  have heqf : (fun h => (∫ ρ in (t - h)..(h + t), g ρ) / (2 * h)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun h => (G (t + h) - G (t - h)) / (2 * h)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    congr 1
    show (∫ ρ in (t - h)..(h + t), g ρ) = G (t + h) - G (t - h)
    have h1 : IntervalIntegrable g volume (t - h) t := hg.intervalIntegrable _ _
    have h2 : IntervalIntegrable g volume t (t + h) := hg.intervalIntegrable _ _
    rw [show h + t = t + h from by ring]
    rw [← integral_add_adjacent_intervals h1 h2]
    rw [integral_symm t (t - h)]
    ring
  rw [Filter.tendsto_congr' heqf]
  exact symmetric_derivative_tendsto G t (g t) hG

/-- The spherical-to-Cartesian map $(\theta, \varphi) \mapsto \omega(\theta, \varphi)$
is $C^\infty$ smooth. -/
lemma contDiff_sphericalToCart_pair :
    ContDiff ℝ ⊤ (fun p : ℝ × ℝ => sphericalToCart p.1 p.2) := by
  unfold sphericalToCart
  apply (EuclideanSpace.equiv (Fin 3) ℝ).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  · exact (contDiff_sin.comp contDiff_fst).mul (contDiff_cos.comp contDiff_snd)
  · exact (contDiff_sin.comp contDiff_fst).mul (contDiff_sin.comp contDiff_snd)
  · exact contDiff_cos.comp contDiff_fst

/-- If $F(x, \theta, \varphi)$ is jointly $C^n$ in all three arguments, then the parametric
spherical integral $x \mapsto \int_0^\pi\!\!\int_0^{2\pi} F(x, \theta, \varphi)\,d\varphi\,d\theta$
is also $C^n$. -/
theorem contDiff_parametric_spherical_integral
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (F : H → ℝ → ℝ → ℝ) {n : ℕ∞}
    (hF : ContDiff ℝ n (fun p : H × ℝ × ℝ => F p.1 p.2.1 p.2.2)) :
    ContDiff ℝ n (fun x : H =>
      ∫ θ in (0 : ℝ)..π, ∫ φ in (0 : ℝ)..(2 * π), F x θ φ) := by sorry

/-- If $h$ is $C^n$, then $r \mapsto \mathrm{SphericalMean}\,h\,x\,r$ is $C^n$ in the radius. -/
theorem sphericalMean_contDiff_of_contDiff (h : E3 → ℝ) (x : E3)
    {n : ℕ∞} (hh : ContDiff ℝ n h) : ContDiff ℝ n (SphericalMean h x) := by
  have heq : SphericalMean h x = (fun r => (1 / (4 * π)) *
      ∫ θ in (0 : ℝ)..π, ∫ φ in (0 : ℝ)..(2 * π),
        h (x + r • sphericalToCart θ φ) * sin θ) := by
    ext r; exact SphericalMean_eq h x r
  rw [heq]
  apply contDiff_const.mul
  apply contDiff_parametric_spherical_integral
  apply ContDiff.mul
  · show ContDiff ℝ n (fun (p : ℝ × ℝ × ℝ) => h (x + p.1 • sphericalToCart p.2.1 p.2.2))
    apply hh.comp
    apply contDiff_const.add
    exact contDiff_fst.smul
      ((contDiff_sphericalToCart_pair.of_le le_top).comp contDiff_snd)
  · exact (contDiff_sin.comp (contDiff_fst.comp contDiff_snd)).of_le le_top

/-- Joint $C^2$ smoothness in $(t, r)$ of $(t, r) \mapsto \mathrm{SphericalMean}(u(t,\cdot))(x, r)$
when $u$ is a $C^2$ wave solution. -/
theorem sphericalMean_contDiff_pair (u : ℝ → E3 → ℝ) (hu : IsWaveSolution3D u) (x : E3) :
    ContDiff ℝ 2 (fun p : ℝ × ℝ => SphericalMean (u p.1) x p.2) := by
  have heq : (fun p : ℝ × ℝ => SphericalMean (u p.1) x p.2) =
    (fun p : ℝ × ℝ => (1 / (4 * π)) *
      ∫ θ in (0 : ℝ)..π, ∫ φ in (0 : ℝ)..(2 * π),
        u p.1 (x + p.2 • sphericalToCart θ φ) * sin θ) := by
    ext p; exact SphericalMean_eq (u p.1) x p.2
  rw [heq]
  apply contDiff_const.mul
  apply contDiff_parametric_spherical_integral
  apply ContDiff.mul
  · have heq2 : (fun (p : (ℝ × ℝ) × ℝ × ℝ) =>
      u p.1.1 (x + p.1.2 • sphericalToCart p.2.1 p.2.2)) =
      (fun p : ℝ × E3 => u p.1 p.2) ∘
      (fun (p : (ℝ × ℝ) × ℝ × ℝ) =>
        (p.1.1, x + p.1.2 • sphericalToCart p.2.1 p.2.2)) := by ext; simp
    rw [heq2]
    apply hu.smooth.comp
    apply ContDiff.prodMk
    · exact contDiff_fst.comp contDiff_fst
    · apply contDiff_const.add
      exact (contDiff_snd.comp contDiff_fst).smul
        ((contDiff_sphericalToCart_pair.of_le le_top).comp contDiff_snd)
  · exact (contDiff_sin.comp (contDiff_fst.comp contDiff_snd)).of_le le_top

/-- $\tilde F(\cdot, x)$ is $C^2$ in the radial variable, using $f \in C^3$. -/
theorem F_tilde_contDiff (data : CauchyData3D) (x : E3) :
    ContDiff ℝ 2 (fun r' => F_tilde data r' x) := by
  unfold F_tilde
  exact contDiff_id.mul
    ((sphericalMean_contDiff_of_contDiff data.f x data.f_smooth).of_le (by norm_num))

/-- $\tilde G(\cdot, x)$ is $C^1$ in the radial variable, using $g \in C^2$. -/
theorem G_tilde_contDiff (data : CauchyData3D) (x : E3) :
    ContDiff ℝ 1 (fun r' => G_tilde data r' x) := by
  unfold G_tilde
  exact contDiff_id.mul
    ((sphericalMean_contDiff_of_contDiff data.g x data.g_smooth).of_le (by norm_num))

/-- Taking $r \to 0^+$ in the d'Alembert formula for the auxiliary $1+1$-dimensional
problem recovers $u(t, x)$: $u(t, x) = \partial_r \tilde F(t, x) + \tilde G(t, x)$. -/
theorem limit_sphericalMean_dalembert
    (data : CauchyData3D) (u : ℝ → E3 → ℝ)
    (hu : IsWaveSolution3D u)
    (hf : ∀ x, u 0 x = data.f x)
    (hg : ∀ x, fderiv ℝ (fun t => u t x) 0 1 = data.g x)
    (t : ℝ) (ht : 0 < t) (x : E3) :
    u t x = fderiv ℝ (fun r => F_tilde data r x) t 1 + G_tilde data t x := by


  have hcont : Continuous (u t) := by
    have h2 := hu.smooth.continuous
    exact h2.comp (Continuous.prodMk_right t)
  have h_lhs : Tendsto (fun r => SphericalMean (u t) x r)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (u t x)) :=
    sphericalMean_limit_zero (u t) hcont x

  have hF_hasDerivAt := F_tilde_hasDerivAt data.f x t ht (data.f_smooth.of_le (by norm_num))

  have h_sym : Tendsto (fun r => (F_tilde data (r + t) x - F_tilde data (t - r) x) / (2 * r))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (fderiv ℝ (fun r => F_tilde data r x) t 1)) := by

    have : fderiv ℝ (fun r => F_tilde data r x) t 1 =
        SphericalMean data.f x t + t * deriv (fun r => SphericalMean data.f x r) t := by
      rw [fderiv_apply_one_eq_deriv]
      have : (fun r => F_tilde data r x) = (fun r => r * SphericalMean data.f x r) := by
        ext r; rfl
      rw [this]
      exact hF_hasDerivAt.deriv
    rw [this]
    exact (symmetric_derivative_tendsto (fun r => F_tilde data r x) t _
        hF_hasDerivAt).congr (fun h => by ring_nf)

  have hg_cont : Continuous (fun r => G_tilde data r x) := by
    unfold G_tilde
    exact continuous_id.mul (sphericalMean_continuous data.g data.g_smooth.continuous x)
  have h_int : Tendsto (fun r => (∫ ρ in (t - r)..(r + t), G_tilde data ρ x) / (2 * r))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (G_tilde data t x)) :=
    integral_average_tendsto (fun r => G_tilde data r x) t hg_cont

  have h_rhs : Tendsto
      (fun r => (F_tilde data (r + t) x - F_tilde data (t - r) x) / (2 * r) +
        (∫ ρ in (t - r)..(r + t), G_tilde data ρ x) / (2 * r))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (fderiv ℝ (fun r => F_tilde data r x) t 1 + G_tilde data t x)) :=
    h_sym.add h_int


  have h_eq_eventually : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0),
      SphericalMean (u t) x r =
        (F_tilde data (r + t) x - F_tilde data (t - r) x) / (2 * r) +
        (∫ ρ in (t - r)..(r + t), G_tilde data ρ x) / (2 * r) := by


    have h_mem : Set.Ioo 0 t ∈ nhdsWithin 0 (Set.Ioi 0) := by
      rw [← Set.Ioi_inter_Iio]
      exact inter_mem_nhdsWithin _ (Iio_mem_nhds ht)
    filter_upwards [h_mem] with r hr
    have hr_pos' : (0 : ℝ) < r := hr.1
    have hr_le_t : r ≤ t := le_of_lt hr.2


    have hF_cd : ContDiff ℝ 2 (fun ρ => F_tilde data ρ x) := F_tilde_contDiff data x
    have hG_cd : ContDiff ℝ 1 (fun ρ => G_tilde data ρ x) := G_tilde_contDiff data x
    have hF0 : F_tilde data 0 x = 0 := by unfold F_tilde; exact zero_mul _
    have hG0 : G_tilde data 0 x = 0 := by unfold G_tilde; exact zero_mul _
    have hw_reg : ContDiff ℝ 2 (fun p : ℝ × ℝ =>
        p.2 * SphericalMean (u p.1) x p.2) :=
      contDiff_snd.mul (sphericalMean_contDiff_pair u hu x)
    have hw_wave' : ∀ s ρ : ℝ, 0 ≤ ρ →
        deriv (fun t' => deriv (fun t'' => ρ * SphericalMean (u t'') x ρ) t') s =
        deriv (fun r' => deriv (fun r'' => r'' * SphericalMean (u s) x r'') r') ρ := by
      intro s' ρ' hρ'
      have h_fderiv := sphericalMean_wave_reduction u hu s' ρ' hρ' x
      simp only [fderiv_apply_one_eq_deriv] at h_fderiv
      exact h_fderiv
    have hw_boundary : ∀ s : ℝ, (0 : ℝ) * SphericalMean (u s) x 0 = 0 :=
      fun s => zero_mul _
    have hw_initial_pos : ∀ ρ : ℝ, 0 ≤ ρ →
        ρ * SphericalMean (u 0) x ρ = F_tilde data ρ x := by
      intro ρ _hρ
      unfold F_tilde; congr 1; congr 1; ext y; exact hf y
    have hw_initial_vel : ∀ ρ : ℝ, 0 < ρ →
        HasDerivAt (fun s => ρ * SphericalMean (u s) x ρ) (G_tilde data ρ x) 0 := by
      intro ρ hρ
      have hfderiv_val := sphericalMean_time_deriv u hu ρ hρ x


      have hg_eq : SphericalMean (fun y => fderiv ℝ (fun t₀ => u t₀ y) 0 1) x ρ =
          SphericalMean data.g x ρ := by
        congr 1; ext y; exact hg y
      rw [hg_eq] at hfderiv_val

      have hdiff : DifferentiableAt ℝ (fun s => ρ * SphericalMean (u s) x ρ) 0 :=
        (sphericalMean_differentiable_time u ρ x hu 0).const_mul ρ
      rw [show G_tilde data ρ x = ρ * SphericalMean data.g x ρ from rfl]
      rw [← hfderiv_val]
      exact hdiff.hasDerivAt

    have h_repr := dalembert_halfline_representation
        (fun s ρ => ρ * SphericalMean (u s) x ρ)
        (fun ρ => F_tilde data ρ x)
        (fun ρ => G_tilde data ρ x)
        hF_cd hG_cd hF0 hG0
        hw_reg hw_wave'
        hw_boundary hw_initial_pos hw_initial_vel
        t r (le_of_lt ht) (le_of_lt hr_pos') hr_le_t


    have hr_ne : r ≠ 0 := ne_of_gt hr_pos'
    field_simp at h_repr ⊢
    linarith

  have h_rhs_tendsto : Tendsto (fun r => SphericalMean (u t) x r)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (fderiv ℝ (fun r => F_tilde data r x) t 1 + G_tilde data t x)) :=
    h_rhs.congr' (EventuallyEq.symm h_eq_eventually)

  exact tendsto_nhds_unique h_lhs h_rhs_tendsto

/-- Restatement of `limit_sphericalMean_dalembert`: $u(t, x) = \partial_r \tilde F(t, x) + \tilde G(t, x)$. -/
theorem limit_gives_derivative_plus_G
    (data : CauchyData3D) (u : ℝ → E3 → ℝ)
    (hu : IsWaveSolution3D u)
    (hf : ∀ x, u 0 x = data.f x)
    (hg : ∀ x, fderiv ℝ (fun t => u t x) 0 1 = data.g x)
    (t : ℝ) (ht : 0 < t) (x : E3) :
    u t x = fderiv ℝ (fun r => F_tilde data r x) t 1 + G_tilde data t x :=
  limit_sphericalMean_dalembert data u hu hf hg t ht x

/-- Differentiation under the integral sign yields the two surface-integral terms
appearing in Kirchhoff's formula:
$\partial_r \tilde F(t, x) = \frac{1}{4\pi t^2}\int_{\partial B_t(x)} f\,d\sigma
+ \frac{1}{4\pi t}\int_{\partial B_t(x)} \nabla_{\hat N} f\,d\sigma$. -/
theorem differentiation_under_integral_kirchhoff
    (data : CauchyData3D) (t : ℝ) (ht : 0 < t) (x : E3) :
    fderiv ℝ (fun r => F_tilde data r x) t 1 =
      (1 / (4 * π * t ^ 2)) * SphereIntegral data.f x t
      + (1 / (4 * π * t)) * SphereIntegralNormalDeriv data.f x t := by

  unfold F_tilde

  have hd := F_tilde_hasDerivAt data.f x t ht (data.f_smooth.of_le (by norm_num))
  rw [hd.hasFDerivAt.fderiv]
  simp

  rw [sphere_integral_eq_area_times_mean]
  rw [sphericalMean_normal_deriv_relation data.f x t ht]

  have hpi : (π : ℝ) ≠ 0 := pi_ne_zero
  have ht' : (t : ℝ) ≠ 0 := ne_of_gt ht
  field_simp

/-- $\tilde G(t, x) = \frac{1}{4\pi t}\int_{\partial B_t(x)} g\,d\sigma$, the
last term of Kirchhoff's formula. -/
theorem G_tilde_equals_sphere_integral
    (data : CauchyData3D) (t : ℝ) (ht : 0 < t) (x : E3) :
    G_tilde data t x = (1 / (4 * π * t)) * SphereIntegral data.g x t := by
  unfold G_tilde
  rw [sphere_integral_eq_area_times_mean]
  have hpi : (π : ℝ) ≠ 0 := pi_ne_zero
  have ht' : (t : ℝ) ≠ 0 := ne_of_gt ht
  field_simp

/-- **Kirchhoff's formula** (Class Meeting #12, Theorem 1.1). The unique
$C^2$ solution of the $3$-dimensional Cauchy problem
$-\partial_t^2 u + \Delta u = 0$, $u(0,x) = f(x)$, $\partial_t u(0,x) = g(x)$
admits the representation
$u(t, x) = \frac{1}{4\pi t^2}\int_{\partial B_t(x)} f\,d\sigma
+ \frac{1}{4\pi t}\int_{\partial B_t(x)} \nabla_{\hat N} f\,d\sigma
+ \frac{1}{4\pi t}\int_{\partial B_t(x)} g\,d\sigma$ for $t > 0$. -/
theorem kirchhoff_formula (data : CauchyData3D) (u : ℝ → E3 → ℝ)
    (hu : IsWaveSolution3D u)
    (hf : ∀ x, u 0 x = data.f x)
    (hg : ∀ x, fderiv ℝ (fun t => u t x) 0 1 = data.g x)
    (t : ℝ) (ht : 0 < t) (x : E3) :
    u t x = (1 / (4 * π * t ^ 2)) * SphereIntegral data.f x t
          + (1 / (4 * π * t)) * SphereIntegralNormalDeriv data.f x t
          + (1 / (4 * π * t)) * SphereIntegral data.g x t := by


  have step3 := limit_gives_derivative_plus_G data u hu hf hg t ht x

  have step4 := differentiation_under_integral_kirchhoff data t ht x

  have step4b := G_tilde_equals_sphere_integral data t ht x

  rw [step3, step4, step4b]

/-- The spherical average $\mathrm{SphericalMean}(u(t,\cdot))(x, r)$ of a wave solution
$u$ at time $t$, centred at $x$ with radius $r$. -/
def sphericalAverage (u : ℝ → E3 → ℝ) (t r : ℝ) (x : E3) : ℝ :=
  SphericalMean (u t) x r

/-- The radius-weighted spherical average $r \cdot \mathrm{SphericalMean}(u(t,\cdot))(x, r)$,
which solves a $1+1$-dimensional half-line wave equation in $(t, r)$. -/
def sphericalAverage_tilde (u : ℝ → E3 → ℝ) (t r : ℝ) (x : E3) : ℝ :=
  r * sphericalAverage u t r x

/-- The weighted spherical average $\tilde A(t, r) := r \cdot \mathrm{SphericalMean}(u(t,\cdot))(x, r)$
solves the $1+1$-dimensional wave equation $\partial_t^2 \tilde A = \partial_r^2 \tilde A$. -/
theorem sphericalAverage_solves_1d_wave
    (data : CauchyData3D) (u : ℝ → E3 → ℝ)
    (hu : IsWaveSolution3D u)
    (_hf : ∀ x, u 0 x = data.f x)
    (_hg : ∀ x, fderiv ℝ (fun t => u t x) 0 1 = data.g x)
    (t r : ℝ) (hr : 0 ≤ r) (x : E3) :
    fderiv ℝ (fun s => fderiv ℝ (fun s' => sphericalAverage_tilde u s' r x) s 1) t 1 =
    fderiv ℝ (fun ρ => fderiv ℝ (fun ρ' => sphericalAverage_tilde u t ρ' x) ρ 1) r 1 := by


  unfold sphericalAverage_tilde sphericalAverage
  exact sphericalMean_wave_reduction u hu t r hr x

/-- Initial position of the weighted spherical average: $\tilde A(0, r, x) = \tilde F(r, x)$. -/
theorem sphericalAverage_tilde_initial_position
    (data : CauchyData3D) (u : ℝ → E3 → ℝ)
    (_hu : IsWaveSolution3D u)
    (hf : ∀ x, u 0 x = data.f x)
    (_hg : ∀ x, fderiv ℝ (fun t => u t x) 0 1 = data.g x)
    (r : ℝ) (_hr : 0 < r) (x : E3) :
    sphericalAverage_tilde u 0 r x = F_tilde data r x := by
  unfold sphericalAverage_tilde sphericalAverage F_tilde
  congr 1
  congr 1
  ext y
  exact hf y

/-- Initial velocity of the weighted spherical average: $\partial_t \tilde A(0, r, x) = \tilde G(r, x)$. -/
theorem sphericalAverage_tilde_initial_velocity
    (data : CauchyData3D) (u : ℝ → E3 → ℝ)
    (hu : IsWaveSolution3D u)
    (_hf : ∀ x, u 0 x = data.f x)
    (hg : ∀ x, fderiv ℝ (fun t => u t x) 0 1 = data.g x)
    (r : ℝ) (hr : 0 < r) (x : E3) :
    fderiv ℝ (fun t => sphericalAverage_tilde u t r x) 0 1 = G_tilde data r x := by

  unfold sphericalAverage_tilde sphericalAverage G_tilde

  rw [sphericalMean_time_deriv u hu r hr x]


  congr 1
  congr 1
  ext y
  exact hg y

/-- The map $(t, r) \mapsto \tilde A(t, r, x) = r \cdot \mathrm{SphericalMean}(u(t,\cdot))(x, r)$ is $C^2$. -/
theorem sphericalAverage_tilde_contDiff (u : ℝ → E3 → ℝ) (hu : IsWaveSolution3D u) (x : E3) :
    ContDiff ℝ 2 (fun p : ℝ × ℝ => sphericalAverage_tilde u p.1 p.2 x) := by
  unfold sphericalAverage_tilde sphericalAverage
  exact contDiff_snd.mul (sphericalMean_contDiff_pair u hu x)

/-- The weighted spherical average $\tilde A$ satisfies the $1+1$-dimensional wave
equation $\partial_t^2 \tilde A = \partial_r^2 \tilde A$ (stated in `deriv` form). -/
theorem sphericalAverage_tilde_wave_deriv
    (data : CauchyData3D) (u : ℝ → E3 → ℝ)
    (hu : IsWaveSolution3D u)
    (hf : ∀ x, u 0 x = data.f x)
    (hg : ∀ x, fderiv ℝ (fun t => u t x) 0 1 = data.g x)
    (x : E3) :
    ∀ t r : ℝ, 0 ≤ r →
      deriv (fun t' => deriv (fun t'' => sphericalAverage_tilde u t'' r x) t') t =
      deriv (fun r' => deriv (fun r'' => sphericalAverage_tilde u t r'' x) r') r := by
  intro t r hr
  have h := sphericalAverage_solves_1d_wave data u hu hf hg t r hr x
  simp only [fderiv_apply_one_eq_deriv] at h
  exact h

/-- At time $t = 0$, the weighted spherical average has time derivative equal to $\tilde G(r, x)$. -/
theorem sphericalAverage_tilde_hasDerivAt_initial
    (data : CauchyData3D) (u : ℝ → E3 → ℝ)
    (hu : IsWaveSolution3D u)
    (hf : ∀ x, u 0 x = data.f x)
    (hg : ∀ x, fderiv ℝ (fun t => u t x) 0 1 = data.g x)
    (x : E3) :
    ∀ r : ℝ, 0 < r →
      HasDerivAt (fun t => sphericalAverage_tilde u t r x) (G_tilde data r x) 0 := by
  intro r hr

  have hfderiv := sphericalAverage_tilde_initial_velocity data u hu hf hg r hr x

  have hdiff : DifferentiableAt ℝ (fun t => sphericalAverage_tilde u t r x) 0 := by
    unfold sphericalAverage_tilde sphericalAverage
    exact (sphericalMean_differentiable_time u r x hu 0).const_mul r

  rw [← hfderiv]
  exact hdiff.hasDerivAt

/-- D'Alembert representation for the weighted spherical average: for $0 \le r \le t$,
$\tilde A(t, r, x) = \tfrac12(\tilde F(r+t, x) - \tilde F(t-r, x)) + \tfrac12 \int_{t-r}^{r+t} \tilde G(\rho, x)\,d\rho$. -/
theorem sphericalAverage_tilde_dalembert
    (data : CauchyData3D) (u : ℝ → E3 → ℝ)
    (hu : IsWaveSolution3D u)
    (hf : ∀ x, u 0 x = data.f x)
    (hg : ∀ x, fderiv ℝ (fun t => u t x) 0 1 = data.g x)
    (t r : ℝ) (ht : 0 ≤ t) (hr : 0 ≤ r) (hrt : r ≤ t) (x : E3) :
    sphericalAverage_tilde u t r x =
      (1 / 2) * (F_tilde data (r + t) x - F_tilde data (t - r) x) +
      (1 / 2) * ∫ ρ in (t - r)..(r + t), G_tilde data ρ x := by


  have hw_boundary : ∀ t' : ℝ, sphericalAverage_tilde u t' 0 x = 0 := by
    intro t'; unfold sphericalAverage_tilde; ring
  have hw_initial_pos : ∀ r' : ℝ, 0 ≤ r' →
      sphericalAverage_tilde u 0 r' x = F_tilde data r' x := by
    intro r' hr'
    by_cases hr'_pos : 0 < r'
    · exact sphericalAverage_tilde_initial_position data u hu hf hg r' hr'_pos x
    · have hr'_zero : r' = 0 := le_antisymm (not_lt.mp hr'_pos) hr'
      subst hr'_zero
      unfold sphericalAverage_tilde F_tilde; ring
  exact dalembert_halfline_representation
    (fun t' r' => sphericalAverage_tilde u t' r' x)
    (fun r' => F_tilde data r' x)
    (fun r' => G_tilde data r' x)
    (F_tilde_contDiff data x)
    (G_tilde_contDiff data x)
    (by unfold F_tilde; simp [SphericalMean])
    (by unfold G_tilde; simp [SphericalMean])
    (sphericalAverage_tilde_contDiff u hu x)

    (sphericalAverage_tilde_wave_deriv data u hu hf hg x)
    hw_boundary
    hw_initial_pos
    (sphericalAverage_tilde_hasDerivAt_initial data u hu hf hg x)
    t r ht hr hrt

/-- Corollary 1.0.2: explicit d'Alembert representation for the weighted spherical
average $\tilde A(t, r, x)$ in terms of the initial data $\tilde F$ and $\tilde G$. -/
theorem corollary_1_0_2
    (data : CauchyData3D) (u : ℝ → E3 → ℝ)
    (hu : IsWaveSolution3D u)
    (hf : ∀ x, u 0 x = data.f x)
    (hg : ∀ x, fderiv ℝ (fun t => u t x) 0 1 = data.g x)
    (t r : ℝ) (ht : 0 ≤ t) (hr : 0 ≤ r) (hrt : r ≤ t) (x : E3) :
    sphericalAverage_tilde u t r x =
      (1 / 2) * (F_tilde data (r + t) x - F_tilde data (t - r) x) +
      (1 / 2) * ∫ ρ in (t - r)..(r + t), G_tilde data ρ x :=
  sphericalAverage_tilde_dalembert data u hu hf hg t r ht hr hrt x

/-- The Minkowski metric $m_{\mu\nu} = \mathrm{diag}(-1, 1, \dots, 1)$ on $\mathbb{R}^{1+n}$
as a matrix indexed by `Fin (n + 1)`. -/
def minkowskiMetric (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => if i = j then (if (i : ℕ) = 0 then -1 else 1) else 0

/-- The Minkowski inner product $m(X, Y) = X^\alpha m_{\alpha\beta} Y^\beta$
on $\mathbb{R}^{1+n}$. -/
def minkowskiInner (n : ℕ) (X Y : Fin (n + 1) → ℝ) : ℝ :=
  dotProduct X (minkowskiMetric n *ᵥ Y)

/-- The Minkowski inner product is symmetric: $m(X, Y) = m(Y, X)$. -/
theorem minkowskiInner_comm (n : ℕ) (X Y : Fin (n + 1) → ℝ) :
    minkowskiInner n X Y = minkowskiInner n Y X := by
  simp only [minkowskiInner, minkowskiMetric, dotProduct, mulVec, of_apply]
  simp [mul_comm]

/-- A vector $X \in \mathbb{R}^{1+n}$ is **timelike** if $m(X, X) < 0$
(Definition 2.0.1, case (1)). -/
def IsTimelike (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiInner n X X < 0

/-- A vector $X \in \mathbb{R}^{1+n}$ is **spacelike** if $m(X, X) > 0$
(Definition 2.0.1, case (2)). -/
def IsSpacelike (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiInner n X X > 0

/-- A vector $X \in \mathbb{R}^{1+n}$ is **null** if $m(X, X) = 0$
(Definition 2.0.1, case (3)). -/
def IsNull (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiInner n X X = 0

/-- A vector $X \in \mathbb{R}^{1+n}$ is **causal** if it is timelike or null,
equivalently $m(X, X) \le 0$ (Definition 2.0.1, case (4)). -/
def IsCausal (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  minkowskiInner n X X ≤ 0

/-- A vector $X \in \mathbb{R}^{1+n}$ is **future-directed** if its time component
satisfies $X^0 > 0$ (Definition 2.0.2). -/
def IsFutureDirected (n : ℕ) (X : Fin (n + 1) → ℝ) : Prop :=
  X 0 > 0

/-- A matrix $\Lambda$ is a **Lorentz transformation** if it preserves the Minkowski
metric: $\Lambda^T m \Lambda = m$ (Definition 2.1.1). -/
def IsLorentzTransformation (n : ℕ) (Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Prop :=
  Λᵀ * minkowskiMetric n * Λ = minkowskiMetric n

/-- A Lorentz transformation preserves the Minkowski inner product:
$m(\Lambda X, \Lambda Y) = m(X, Y)$. -/
theorem lorentz_preserves_inner {n : ℕ}
    {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hΛ : IsLorentzTransformation n Λ)
    (X Y : Fin (n + 1) → ℝ) :
    minkowskiInner n (Λ *ᵥ X) (Λ *ᵥ Y) = minkowskiInner n X Y := by
  simp only [minkowskiInner]


  rw [mulVec_mulVec]


  rw [dotProduct_mulVec (Λ *ᵥ X) (minkowskiMetric n * Λ) Y]


  rw [vecMul_mulVec Λ (minkowskiMetric n * Λ) X]


  rw [← Matrix.mul_assoc, hΛ]

  rw [← dotProduct_mulVec]

/-- Corollary 2.1.1 (timelike case): Lorentz transformations preserve timelike vectors. -/
theorem lorentz_preserves_timelike {n : ℕ}
    {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hΛ : IsLorentzTransformation n Λ)
    {X : Fin (n + 1) → ℝ}
    (hX : IsTimelike n X) :
    IsTimelike n (Λ *ᵥ X) := by
  unfold IsTimelike at *
  rw [lorentz_preserves_inner hΛ]
  exact hX

/-- Corollary 2.1.1 (spacelike case): Lorentz transformations preserve spacelike vectors. -/
theorem lorentz_preserves_spacelike {n : ℕ}
    {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hΛ : IsLorentzTransformation n Λ)
    {X : Fin (n + 1) → ℝ}
    (hX : IsSpacelike n X) :
    IsSpacelike n (Λ *ᵥ X) := by
  unfold IsSpacelike at *
  rw [lorentz_preserves_inner hΛ]
  exact hX

/-- Corollary 2.1.1 (null case): Lorentz transformations preserve null vectors. -/
theorem lorentz_preserves_null {n : ℕ}
    {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hΛ : IsLorentzTransformation n Λ)
    {X : Fin (n + 1) → ℝ}
    (hX : IsNull n X) :
    IsNull n (Λ *ᵥ X) := by
  unfold IsNull at *
  rw [lorentz_preserves_inner hΛ]
  exact hX

/-- Corollary 2.1.1 (causal case): Lorentz transformations preserve causal vectors. -/
theorem lorentz_preserves_causal {n : ℕ}
    {Λ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
    (hΛ : IsLorentzTransformation n Λ)
    {X : Fin (n + 1) → ℝ}
    (hX : IsCausal n X) :
    IsCausal n (Λ *ᵥ X) := by
  unfold IsCausal at *
  rw [lorentz_preserves_inner hΛ]
  exact hX

/-- A **null frame** on $\mathbb{R}^{1+n}$ (Definition 2.2.1):
a basis $\{L, \underline L, e_{(1)}, \dots, e_{(n-1)}\}$ where $L, \underline L$ are null
with $m(L, \underline L) = -2$, and the $e_{(i)}$ are $m$-orthonormal vectors $m$-orthogonal
to both $L$ and $\underline L$. The `completeness` field records the resulting expansion
$X = -\tfrac12 m(\underline L, X) L - \tfrac12 m(L, X)\underline L + \sum_i m(e_{(i)}, X) e_{(i)}$. -/
structure NullFrame (n : ℕ) where
  L : Fin (n + 1) → ℝ
  Lb : Fin (n + 1) → ℝ
  e : Fin (n - 1) → (Fin (n + 1) → ℝ)
  L_null : minkowskiInner n L L = 0
  Lb_null : minkowskiInner n Lb Lb = 0
  L_Lb_inner : minkowskiInner n L Lb = -2
  e_orthonormal : ∀ i j : Fin (n - 1),
    minkowskiInner n (e i) (e j) = if i = j then 1 else 0
  L_e_orthog : ∀ i : Fin (n - 1), minkowskiInner n L (e i) = 0
  Lb_e_orthog : ∀ i : Fin (n - 1), minkowskiInner n Lb (e i) = 0
  completeness : ∀ X : Fin (n + 1) → ℝ,
    X = (-(1/2) * minkowskiInner n Lb X) • L
      + (-(1/2) * minkowskiInner n L X) • Lb
      + ∑ i, (minkowskiInner n (e i) X) • (e i)

/-- The **angular metric** $h(X, Y) := \sum_i m(e_{(i)}, X) m(e_{(i)}, Y)$ associated
with a null frame; it is positive-definite on the $m$-orthogonal complement of
$\mathrm{span}(L, \underline L)$ and vanishes on $\mathrm{span}(L, \underline L)$. -/
def angularMetric (n : ℕ) (nf : NullFrame n) (X Y : Fin (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n - 1), minkowskiInner n (nf.e i) X * minkowskiInner n (nf.e i) Y

/-- **Proposition 2.2.1** (null-frame decomposition of $m$):
$m(X, Y) = -\tfrac12 m(L, X) m(\underline L, Y) - \tfrac12 m(\underline L, X) m(L, Y) + h(X, Y)$
where $h$ is the angular metric of the null frame. -/
theorem nullFrame_decomposition {n : ℕ} (nf : NullFrame n)
    (X Y : Fin (n + 1) → ℝ) :
    minkowskiInner n X Y =
      -(1 / 2) * minkowskiInner n nf.L X * minkowskiInner n nf.Lb Y
      - (1 / 2) * minkowskiInner n nf.Lb X * minkowskiInner n nf.L Y
      + angularMetric n nf X Y := by
  conv_lhs => rw [nf.completeness X]
  simp only [minkowskiInner, angularMetric]
  rw [add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct]
  rw [sum_dotProduct (Finset.univ)
    (fun i => (dotProduct (nf.e i) (minkowskiMetric n *ᵥ X)) • nf.e i)]
  simp only [smul_dotProduct, smul_eq_mul]
  ring

/-- The angular metric vanishes on $L$ in the first argument: $h(L, Y) = 0$. -/
theorem angularMetric_vanish_L {n : ℕ} (nf : NullFrame n) (Y : Fin (n + 1) → ℝ) :
    angularMetric n nf nf.L Y = 0 := by
  simp only [angularMetric]
  apply Finset.sum_eq_zero
  intro i _
  have h : minkowskiInner n (nf.e i) nf.L = 0 := by
    rw [minkowskiInner_comm]; exact nf.L_e_orthog i
  simp [h]

/-- The angular metric vanishes on $\underline L$ in the first argument: $h(\underline L, Y) = 0$. -/
theorem angularMetric_vanish_Lb {n : ℕ} (nf : NullFrame n) (Y : Fin (n + 1) → ℝ) :
    angularMetric n nf nf.Lb Y = 0 := by
  simp only [angularMetric]
  apply Finset.sum_eq_zero
  intro i _
  have h : minkowskiInner n (nf.e i) nf.Lb = 0 := by
    rw [minkowskiInner_comm]; exact nf.Lb_e_orthog i
  simp [h]

/-- The angular metric is symmetric: $h(X, Y) = h(Y, X)$. -/
theorem angularMetric_comm {n : ℕ} (nf : NullFrame n) (X Y : Fin (n + 1) → ℝ) :
    angularMetric n nf X Y = angularMetric n nf Y X := by
  simp only [angularMetric]
  congr 1; ext i; ring

/-- The angular metric vanishes on $L$ in the second argument: $h(X, L) = 0$. -/
theorem angularMetric_vanish_L_right {n : ℕ} (nf : NullFrame n) (X : Fin (n + 1) → ℝ) :
    angularMetric n nf X nf.L = 0 := by
  rw [angularMetric_comm]; exact angularMetric_vanish_L nf X

/-- The angular metric vanishes on $\underline L$ in the second argument: $h(X, \underline L) = 0$. -/
theorem angularMetric_vanish_Lb_right {n : ℕ} (nf : NullFrame n) (X : Fin (n + 1) → ℝ) :
    angularMetric n nf X nf.Lb = 0 := by
  rw [angularMetric_comm]; exact angularMetric_vanish_Lb nf X

/-- Values of the angular metric on the angular basis: $h(e_{(i)}, e_{(j)}) = \delta_{ij}$. -/
theorem angularMetric_on_e {n : ℕ} (nf : NullFrame n) (i j : Fin (n - 1)) :
    angularMetric n nf (nf.e i) (nf.e j) = if i = j then 1 else 0 := by
  simp only [angularMetric, nf.e_orthonormal]
  by_cases h : i = j
  · subst h
    simp [Finset.sum_ite_eq']
  · simp only [h, ite_false]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hki : k = i <;> by_cases hkj : k = j
    · subst hki; subst hkj; exact absurd rfl h
    · subst hki; simp [h]
    · simp [hki]
    · simp [hki]

/-- The angular metric is positive semidefinite: $h(X, X) \ge 0$. -/
theorem angularMetric_nonneg {n : ℕ} (nf : NullFrame n) (X : Fin (n + 1) → ℝ) :
    0 ≤ angularMetric n nf X X := by
  simp only [angularMetric]
  apply Finset.sum_nonneg
  intro i _
  exact mul_self_nonneg _

/-- The angular metric is positive-definite on the $m$-orthogonal complement of
$\mathrm{span}(L, \underline L)$: if $X \ne 0$ with $m(L, X) = m(\underline L, X) = 0$,
then $h(X, X) > 0$. -/
theorem angularMetric_pos_def {n : ℕ} (nf : NullFrame n)
    (X : Fin (n + 1) → ℝ) (hL : minkowskiInner n nf.L X = 0)
    (hLb : minkowskiInner n nf.Lb X = 0) (hX : X ≠ 0) :
    0 < angularMetric n nf X X := by
  simp only [angularMetric]
  apply Finset.sum_pos'
  · intro i _; exact mul_self_nonneg _
  · by_contra h_none
    push Not at h_none
    apply hX
    have h_zero : ∀ i : Fin (n - 1), minkowskiInner n (nf.e i) X = 0 := by
      intro i
      have h1 := h_none i (Finset.mem_univ i)
      have h2 := mul_self_nonneg (minkowskiInner n (nf.e i) X)
      exact mul_self_eq_zero.mp (le_antisymm h1 h2)
    have := nf.completeness X
    rw [hLb, hL] at this
    simp only [mul_zero, zero_smul, zero_add] at this
    rw [this]
    simp only [h_zero, zero_smul, Finset.sum_const_zero]

/-- The Minkowski metric is an involution: $m \cdot m = I$. -/
theorem minkowskiMetric_sq (n : ℕ) : minkowskiMetric n * minkowskiMetric n = 1 := by
  ext i j
  simp only [minkowskiMetric, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply,
    ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  by_cases hij : i = j
  · subst hij; by_cases hi : (i : ℕ) = 0 <;> simp [hi]
  · by_cases hj : (j : ℕ) = 0 <;> simp [hij, hj]

/-- The Minkowski metric is its own inverse: $m^{-1} = m$. -/
theorem minkowskiMetric_inv (n : ℕ) : (minkowskiMetric n)⁻¹ = minkowskiMetric n :=
  inv_eq_left_inv (minkowskiMetric_sq n)

/-- "Index-raising cancellation": $m(V, m \cdot W) = V \cdot W$ (Euclidean dot product). -/
theorem minkowskiInner_eta_cancel (n : ℕ) (V W : Fin (n + 1) → ℝ) :
    minkowskiInner n V (minkowskiMetric n *ᵥ W) = dotProduct V W := by
  simp only [minkowskiInner, mulVec_mulVec, minkowskiMetric_sq, one_mulVec]

/-- **Proposition 2.2.1** (raised-index version): the inverse Minkowski metric admits
the null-frame decomposition
$(m^{-1})^{\mu\nu} = -\tfrac12 L^\mu \underline L^\nu - \tfrac12 \underline L^\mu L^\nu + \sum_i e_{(i)}^\mu e_{(i)}^\nu$. -/
theorem nullFrame_inverse_decomposition {n : ℕ} (nf : NullFrame n)
    (μ ν : Fin (n + 1)) :
    (minkowskiMetric n)⁻¹ μ ν =
      -(1 / 2) * nf.L μ * nf.Lb ν
      - (1 / 2) * nf.Lb μ * nf.L ν
      + ∑ i : Fin (n - 1), nf.e i μ * nf.e i ν := by

  rw [minkowskiMetric_inv]

  have h_entry : minkowskiMetric n μ ν = (minkowskiMetric n *ᵥ Pi.single ν 1) μ := by
    simp [mulVec, dotProduct, minkowskiMetric, Matrix.of_apply, Pi.single_apply]
  rw [h_entry]

  have h_comp := nf.completeness (minkowskiMetric n *ᵥ Pi.single ν 1)

  have h_μ := congr_fun h_comp μ
  rw [h_μ]

  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
    minkowskiInner_eta_cancel,
    dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

  congr 1
  · ring
  · congr 1; ext i; ring

end WaveEquation3D
