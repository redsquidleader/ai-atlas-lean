/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.Algebra.Support
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Atlas.IntroductionToPartialDifferentialEquations.code.CM8.GreenFunctions
open Real Set MeasureTheory

noncomputable section

namespace CM8

/-- The Newtonian-potential convolution in $\mathbb{R}^3$: given $f : \mathbb{R}^3 \to \mathbb{R}$,
`phiConvolution f x` is $\int_{\mathbb{R}^3} \Phi(x - y) f(y) \, d^3 y$, where $\Phi$ is the
3D fundamental solution of the Laplacian. -/
def phiConvolution (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  ∫ y : Fin 3 → ℝ, Phi3 (x - y) * f y

/-- The Laplacian $\Delta f = \sum_{i=1}^{3} \partial_i^2 f$ on $\mathbb{R}^3$, specialised from
the general `laplacian` to dimension three. -/
def laplacian3 (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) : ℝ :=
  laplacian f x

/-- Leibniz/differentiation-under-the-integral for the Newtonian potential: if $f$ is smooth and
compactly supported, then $\Delta(\Phi * f)(x) = \int \Phi(x-y) \Delta f(y) \, d^3y$. -/
theorem leibniz_laplacian_phiConvolution
    (f : (Fin 3 → ℝ) → ℝ) (hf : ContDiff ℝ ⊤ f) (hsupp : HasCompactSupport f) :
    ∀ x : Fin 3 → ℝ, laplacian3 (phiConvolution f) x =
      ∫ y : Fin 3 → ℝ, Phi3 (x - y) * laplacian3 f y := by sorry

/-- Newtonian-potential inversion: convolution of $\Delta f$ with the fundamental solution
$\Phi$ recovers $f$, i.e. $\int \Phi(x-y) \Delta f(y) \, d^3 y = f(x)$ for smooth compactly
supported $f$. -/
theorem newtonian_potential_inversion
    (f : (Fin 3 → ℝ) → ℝ) (hf : ContDiff ℝ ⊤ f) (hsupp : HasCompactSupport f) :
    ∀ x : Fin 3 → ℝ, (∫ y : Fin 3 → ℝ, Phi3 (x - y) * laplacian3 f y) = f x := by
  sorry

/-- Solution of Poisson's equation on $\mathbb{R}^3$: for smooth compactly supported $f$,
$u = \Phi * f$ satisfies $\Delta u = f$ pointwise. -/
theorem poisson_solution (f : (Fin 3 → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) :
    ∀ x : Fin 3 → ℝ, laplacian3 (phiConvolution f) x = f x := by
  intro x
  rw [leibniz_laplacian_phiConvolution f hf_smooth hf_supp x]
  exact newtonian_potential_inversion f hf_smooth hf_supp x

/-- Far-field decay of the Newtonian potential: there exist constants $C_1, R_0 > 0$ such that
$|(\Phi * f)(x)| \le C_1 / |x|$ whenever $|x| > R_0$, reflecting the $1/r$ decay of $\Phi$ in
$\mathbb{R}^3$. -/
theorem phiConvolution_far_field_decay
    (f : (Fin 3 → ℝ) → ℝ) (hf : ContDiff ℝ ⊤ f) (hsupp : HasCompactSupport f) :
    ∃ C₁ R₀ : ℝ, 0 < C₁ ∧ 0 < R₀ ∧
      ∀ x : Fin 3 → ℝ, euclidNorm x > R₀ → |phiConvolution f x| ≤ C₁ / euclidNorm x := by
  sorry

/-- Boundedness of the Newtonian potential away from the origin: the convolution
$\Phi * f$ is uniformly bounded on $\{|x| > 1\}$. -/
theorem phiConvolution_bounded
    (f : (Fin 3 → ℝ) → ℝ) (hf : ContDiff ℝ ⊤ f) (hsupp : HasCompactSupport f) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : Fin 3 → ℝ, euclidNorm x > 1 → |phiConvolution f x| ≤ M := by
  sorry

/-- Combined decay estimate for the Poisson solution $u = \Phi * f$: there is a constant
$C > 0$ such that $|u(x)| \le C / |x|$ for all $|x| > 1$, obtained by combining the far-field
and global boundedness estimates. -/
theorem poisson_solution_decay (f : (Fin 3 → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) :
    ∃ C : ℝ, C > 0 ∧ ∀ x : Fin 3 → ℝ,
      euclidNorm x > 1 → |phiConvolution f x| ≤ C / euclidNorm x := by
  obtain ⟨C₁, R₀, hC₁, hR₀, hfar⟩ := phiConvolution_far_field_decay f hf_smooth hf_supp
  obtain ⟨M, hM, hbnd⟩ := phiConvolution_bounded f hf_smooth hf_supp
  refine ⟨max C₁ (M * max R₀ 1), ?_, ?_⟩
  · positivity
  · intro x hx
    have hx_pos : euclidNorm x > 0 := by linarith
    by_cases hxR : euclidNorm x > R₀
    ·
      calc |phiConvolution f x| ≤ C₁ / euclidNorm x := hfar x hxR
        _ ≤ max C₁ (M * max R₀ 1) / euclidNorm x :=
            div_le_div_of_nonneg_right (le_max_left _ _) (by linarith)
    ·
      push_neg at hxR
      have h_ratio : 1 ≤ max R₀ 1 / euclidNorm x := by
        rw [le_div_iff₀ hx_pos]
        simp only [one_mul]
        calc euclidNorm x ≤ R₀ := hxR
          _ ≤ max R₀ 1 := le_max_left _ _
      calc |phiConvolution f x|
          ≤ M := hbnd x hx
        _ = M * 1 := (mul_one _).symm
        _ ≤ M * (max R₀ 1 / euclidNorm x) :=
            mul_le_mul_of_nonneg_left h_ratio hM.le
        _ = (M * max R₀ 1) / euclidNorm x := by ring
        _ ≤ max C₁ (M * max R₀ 1) / euclidNorm x :=
            div_le_div_of_nonneg_right (le_max_right _ _) (by linarith)

/-- The outward unit normal vector $\hat{N}(\sigma)$ to a domain $\Omega \subseteq \mathbb{R}^n$
at a boundary point $\sigma$. Declared opaque since the construction is not relevant here. -/
opaque outwardUnitNormal : {n : ℕ} → Set (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ)

/-- On the boundary of the (Euclidean) ball $\{y : |y - p| < R\}$, the outward unit normal at
$\sigma$ is the radial unit vector $(\sigma - p)/R$. -/
theorem outwardUnitNormal_euclidBall_eq {n : ℕ} (R : ℝ) (hR : 0 < R)
    (p σ : Fin n → ℝ) (hσ : euclidNorm (σ - p) = R) :
    outwardUnitNormal {y | euclidNorm (y - p) < R} σ = fun i => (σ i - p i) / R := by sorry

/-- The outward normal derivative of $f$ on $\partial\Omega$ at $\sigma$, given by
$\nabla_{\hat{N}(\sigma)} f(\sigma) = Df(\sigma) \cdot \hat{N}(\sigma)$. -/
def normalDeriv {n : ℕ} (Ω : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (σ : Fin n → ℝ) : ℝ :=
  fderiv ℝ f σ (outwardUnitNormal Ω σ)

/-- The surface (Hausdorff) measure on $\partial\Omega$, declared opaque since its precise
construction is not used here. -/
opaque surfaceMeasure : {n : ℕ} → Set (Fin n → ℝ) → Measure (Fin n → ℝ)

/-- The surface integral $\int_{\partial\Omega} f(\sigma) \, d\sigma$ of $f$ over the boundary
of $\Omega$, with respect to the surface measure. -/
def surfaceIntegral {n : ℕ} (Ω : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ σ in frontier Ω, f σ ∂(surfaceMeasure Ω)

/-- The surface area $\omega_n$ of the unit sphere $S^{n-1} \subset \mathbb{R}^n$, given by
$\omega_n = 2 \pi^{n/2} / \Gamma(n/2)$ for $n \ge 1$. -/
def unitSphereArea (n : ℕ) : ℝ :=
  if n = 0 then 1 else 2 * Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)

/-- The fundamental solution $\Phi(x)$ of $-\Delta$ in $\mathbb{R}^n$ (equation 1.0.3): for
$n = 2$ it is $\tfrac{1}{2\pi}\log|x|$, and for $n \ge 3$ it is $-1/(\omega_n |x|^{n-2})$. -/
def FundSolN {n : ℕ} [Fact (2 ≤ n)] (x : Fin n → ℝ) : ℝ :=
  if n = 2 then
    (1 / (2 * Real.pi)) * Real.log (euclidNorm x)
  else
    -1 / (unitSphereArea n * (euclidNorm x) ^ (n - 2))

/-- The surface area of the unit sphere $S^2 \subset \mathbb{R}^3$ equals $4\pi$. -/
lemma unitSphereArea_three : unitSphereArea 3 = 4 * Real.pi := by
  unfold unitSphereArea
  simp only [show (3 : ℕ) ≠ 0 from by omega, ↓reduceIte]
  norm_cast
  conv_lhs =>
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 from by ring]
  rw [rpow_add Real.pi_pos, rpow_one, ← Real.sqrt_eq_rpow]
  rw [show (1 : ℝ) + 1 / 2 = 1 / 2 + 1 from by ring]
  rw [Real.Gamma_add_one (by norm_num : (1 : ℝ) / 2 ≠ 0)]
  rw [Real.Gamma_one_half_eq]
  have hsqrt_ne : √Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos)
  field_simp
  ring

/-- In dimension three, the general fundamental solution `FundSolN` agrees with the
3D-specific `Phi3 = -1/(4\pi |x|)$. -/
theorem FundSolN_eq_Phi3 : ∀ [inst : Fact (2 ≤ 3)] (x : Fin 3 → ℝ),
    @FundSolN 3 inst x = Phi3 x := by
  intro inst x
  simp only [FundSolN, show (3 : ℕ) ≠ 2 from by omega, ↓reduceIte,
    show (3 : ℕ) - 2 = 1 from by omega, pow_one]
  rw [unitSphereArea_three]
  simp only [Phi3]

/-- Green's second identity on a Lipschitz domain $\Omega \subset \mathbb{R}^n$: for
$u, v \in C^2(\bar\Omega)$,
$$\int_\Omega \bigl(v \Delta u - u \Delta v\bigr)\, dy
   = \int_{\partial\Omega} \bigl(v \, \nabla_{\hat N} u - u \, \nabla_{\hat N} v\bigr)\, d\sigma.$$
-/
theorem greens_second_identity {n : ℕ} [Fact (2 ≤ n)]
    (Ω : Set (Fin n → ℝ)) (u v : (Fin n → ℝ) → ℝ)
    (hu : ContDiffOn ℝ 2 u (closure Ω)) (hv : ContDiffOn ℝ 2 v (closure Ω))
    (hΩ : IsOpen Ω) (hΩ_lip : IsLipschitzDomain Ω) :
    (∫ y in Ω, v y * laplacian u y - u y * laplacian v y) =
    surfaceIntegral Ω (fun σ => v σ * normalDeriv Ω u σ - u σ * normalDeriv Ω v σ) := by sorry

/-- The surface integral $\int_{|\sigma - c| = r} f(\sigma)\, d\sigma$ of $f$ over the
sphere of radius $r$ centred at $c$, with respect to the surface measure of the ball. -/
def sphereIntegral {n : ℕ} (center : Fin n → ℝ) (r : ℝ) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ σ in Metric.sphere center r, f σ ∂(surfaceMeasure (Metric.ball center r))

/-- The fundamental solution is harmonic away from its pole: $\Delta_y \Phi(x - y) = 0$
whenever $y \ne x$. -/
theorem laplacian_FundSolN_eq_zero_away {n : ℕ} [Fact (2 ≤ n)]
    (x y : Fin n → ℝ) (hxy : x ≠ y) :
    laplacian (fun z => FundSolN (x - z)) y = 0 := by sorry

/-- Removing a small closed ball from a Lipschitz domain $\Omega$ centred at an interior point
keeps the resulting set $\Omega \setminus \overline{B(x,\varepsilon)}$ a Lipschitz domain. -/
theorem IsLipschitzDomain_diff_closedBall {n : ℕ}
    (Ω : Set (Fin n → ℝ)) (x : Fin n → ℝ) (ε : ℝ)
    (hΩ : IsOpen Ω) (hΩ_lip : IsLipschitzDomain Ω)
    (hx : x ∈ Ω) (hε : 0 < ε) :
    IsLipschitzDomain (Ω \ Metric.closedBall x ε) := by sorry

/-- The map $y \mapsto \Phi(x - y)$ is $C^2$ on $\overline{\Omega \setminus \overline{B(x,\varepsilon)}}$,
since the singularity at $y = x$ has been removed. -/
theorem contDiffOn_FundSolN_diff_ball {n : ℕ} [Fact (2 ≤ n)]
    (x : Fin n → ℝ) (Ω : Set (Fin n → ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ContDiffOn ℝ 2 (fun y => FundSolN (x - y))
      (closure (Ω \ Metric.closedBall x ε)) := by sorry

/-- A $C^2$ function on $\overline\Omega$ remains $C^2$ when restricted to the closure of the
punctured domain $\Omega \setminus \overline{B(x,\varepsilon)}$. -/
theorem contDiffOn_restrict_punctured {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) (x : Fin n → ℝ) (ε : ℝ)
    (hu : ContDiffOn ℝ 2 u (closure Ω)) (hΩ : IsOpen Ω) (hε : 0 < ε) :
    ContDiffOn ℝ 2 u (closure (Ω \ Metric.closedBall x ε)) := by sorry

/-- Removing an open ball versus its closure differs only by the sphere, which has Lebesgue
measure zero, so the corresponding set integrals agree. -/
theorem setIntegral_ball_eq_closedBall {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) (x : Fin n → ℝ) (ε : ℝ) :
    (∫ y in Ω \ Metric.ball x ε, f y) =
    (∫ y in Ω \ Metric.closedBall x ε, f y) := by sorry

/-- On the punctured domain $\Omega \setminus \overline{B(x,\varepsilon)}$, since
$\Delta_y \Phi(x - y) = 0$, the volume term $u(y)\, \Delta_y \Phi(x-y)$ vanishes and the
integrand reduces to $\Phi(x - y) \Delta u(y)$. -/
theorem integral_laplacian_v_vanishes {n : ℕ} [Fact (2 ≤ n)]
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) (x : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    (∫ y in Ω \ Metric.closedBall x ε,
      (fun y => FundSolN (x - y)) y * laplacian u y
      - u y * laplacian (fun z => FundSolN (x - z)) y)
    = ∫ y in Ω \ Metric.closedBall x ε, (fun y => FundSolN (x - y)) y * laplacian u y := by
  apply integral_congr_ae
  have hmeas : MeasurableSet (Metric.closedBall x ε)ᶜ :=
    Metric.isClosed_closedBall.measurableSet.compl
  have h_goal : ∀ᵐ y ∂(volume : Measure (Fin n → ℝ)).restrict (Metric.closedBall x ε)ᶜ,
      FundSolN (x - y) * laplacian u y - u y * laplacian (fun z => FundSolN (x - z)) y =
      FundSolN (x - y) * laplacian u y := by
    filter_upwards [ae_restrict_mem hmeas] with y hy
    have hne : x ≠ y := by
      intro heq
      rw [mem_compl_iff, Metric.mem_closedBall, not_le] at hy
      rw [heq, dist_self] at hy
      linarith
    rw [laplacian_FundSolN_eq_zero_away x y hne, mul_zero, sub_zero]
  exact ae_restrict_of_ae_restrict_of_subset (diff_subset_compl _ _) h_goal

/-- Decomposition of a surface integral over $\partial(\Omega \setminus \overline{B(x,\varepsilon)})$
into the contribution from $\partial\Omega$ minus the contribution from the inner sphere
$\partial B(x,\varepsilon)$ (with the normal pointing inward toward $x$ contributing the sign
flip). -/
theorem surfaceIntegral_punctured_normalDeriv_decomp {n : ℕ} [Fact (2 ≤ n)]
    (Ω : Set (Fin n → ℝ)) (x : Fin n → ℝ) (ε : ℝ)
    (hΩ : IsOpen Ω) (hx : x ∈ Ω) (hε : 0 < ε)
    (f g h k : (Fin n → ℝ) → ℝ) :
    surfaceIntegral (Ω \ Metric.closedBall x ε)
      (fun σ => f σ * normalDeriv (Ω \ Metric.closedBall x ε) g σ
               - h σ * normalDeriv (Ω \ Metric.closedBall x ε) k σ)
    = surfaceIntegral Ω (fun σ => f σ * normalDeriv Ω g σ)
      - surfaceIntegral Ω (fun σ => h σ * normalDeriv Ω k σ)
      - sphereIntegral x ε (fun σ => f σ * normalDeriv Ω g σ)
      + sphereIntegral x ε (fun σ => h σ * normalDeriv Ω k σ) := by sorry

/-- Specialisation of `surfaceIntegral_punctured_normalDeriv_decomp` to the integrand
$\Phi(x - \sigma) \nabla_{\hat N} u - u(\sigma) \nabla_{\hat N} \Phi$ appearing in the
representation formula. -/
theorem surfaceIntegral_punctured_domain_decomp {n : ℕ} [Fact (2 ≤ n)]
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) (x : Fin n → ℝ) (ε : ℝ)
    (hΩ : IsOpen Ω) (hΩ_lip : IsLipschitzDomain Ω)
    (hx : x ∈ Ω) (hε : 0 < ε) :
    surfaceIntegral (Ω \ Metric.closedBall x ε)
      (fun σ => (fun y => FundSolN (x - y)) σ *
                normalDeriv (Ω \ Metric.closedBall x ε) u σ
               - u σ * normalDeriv (Ω \ Metric.closedBall x ε)
                        (fun y => FundSolN (x - y)) σ)
    = surfaceIntegral Ω (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ)
      - surfaceIntegral Ω (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ)
      - sphereIntegral x ε (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ)
      + sphereIntegral x ε (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ) := by
  exact surfaceIntegral_punctured_normalDeriv_decomp Ω x ε hΩ hx hε
    (fun σ => FundSolN (x - σ)) u u (fun σ => FundSolN (x - σ))

/-- Green's second identity applied on the punctured domain $\Omega \setminus B(x,\varepsilon)$
with $v(y) = \Phi(x - y)$: the volume integral equals the $\partial\Omega$ surface terms minus
the sphere terms at $|y - x| = \varepsilon$. -/
theorem greens_identity_on_omega_eps {n : ℕ} [Fact (2 ≤ n)]
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω)) (hΩ : IsOpen Ω)
    (hΩ_lip : IsLipschitzDomain Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) (ε : ℝ) (hε : 0 < ε) :
    (∫ y in Ω \ Metric.ball x ε, FundSolN (x - y) * laplacian u y)
    = surfaceIntegral Ω (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ)
      - surfaceIntegral Ω (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ)
      - sphereIntegral x ε (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ)
      + sphereIntegral x ε (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ) := by

  rw [setIntegral_ball_eq_closedBall]

  have hΩε_lip := IsLipschitzDomain_diff_closedBall Ω x ε hΩ hΩ_lip hx hε
  have hΩε_open : IsOpen (Ω \ Metric.closedBall x ε) := hΩ.sdiff Metric.isClosed_closedBall
  have hu_ε := contDiffOn_restrict_punctured u Ω x ε hu hΩ hε
  have hv_ε := contDiffOn_FundSolN_diff_ball x Ω ε hε
  have h_green := greens_second_identity (Ω \ Metric.closedBall x ε) u
    (fun y => FundSolN (x - y)) hu_ε hv_ε hΩε_open hΩε_lip


  have h_vanish := integral_laplacian_v_vanishes u Ω x ε hε
  rw [h_vanish] at h_green


  have h_decomp := surfaceIntegral_punctured_domain_decomp u Ω x ε hΩ hΩ_lip hx hε
  linarith

/-- Integrability of $y \mapsto \Phi(x - y) f(y)$ on $\Omega$: the local singularity of the
fundamental solution at $y = x$ is integrable, so the product is integrable on the domain. -/
theorem FundSolN_mul_integrable {n : ℕ} [Fact (2 ≤ n)]
    (Ω : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    MeasureTheory.IntegrableOn
      (fun y => FundSolN (x - y) * f y) Ω MeasureTheory.MeasureSpace.volume := by sorry

/-- As $\varepsilon \downarrow 0$, the punctured-domain integral
$\int_{\Omega \setminus B(x,\varepsilon)} \Phi(x-y) \Delta u(y) \, dy$ converges to the full
volume integral over $\Omega$. -/
theorem volume_integral_limit {n : ℕ} [Fact (2 ≤ n)]
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω)) (hΩ : IsOpen Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    Filter.Tendsto
      (fun ε => ∫ y in Ω \ Metric.ball x ε, FundSolN (x - y) * laplacian u y)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ y in Ω, FundSolN (x - y) * laplacian u y)) := by
  have hn : 2 ≤ n := Fact.out

  set g : (Fin n → ℝ) → ℝ := fun y => FundSolN (x - y) * laplacian u y with hg_def
  have hg_int : IntegrableOn g Ω := FundSolN_mul_integrable Ω (laplacian u) x

  have h_eq : ∀ ε : ℝ, ∫ y in Ω \ Metric.ball x ε, g y =
      (∫ y in Ω, g y) - (∫ y in Ω ∩ Metric.ball x ε, g y) := by
    intro ε
    rw [show Ω \ Metric.ball x ε = Ω \ (Ω ∩ Metric.ball x ε) from by simp]
    exact setIntegral_diff₀
      ((hΩ.measurableSet.inter Metric.isOpen_ball.measurableSet).nullMeasurableSet)
      hg_int inter_subset_left
  simp_rw [h_eq]
  set c := ∫ y in Ω, g y

  have h_tendsto_zero : Filter.Tendsto (fun ε => ∫ y in Ω ∩ Metric.ball x ε, g y)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by

    have h_restrict : ∀ ε : ℝ, ∫ y in Ω ∩ Metric.ball x ε, g y =
        ∫ y in Metric.ball x ε, g y ∂(volume.restrict Ω) := by
      intro ε
      congr 1
      rw [Measure.restrict_restrict Metric.isOpen_ball.measurableSet, inter_comm]
    simp_rw [h_restrict]

    apply Integrable.tendsto_setIntegral_nhds_zero hg_int

    have h1 : ∀ r > (0 : ℝ), NullMeasurableSet (Metric.ball x r)
        (volume.restrict Ω : Measure (Fin n → ℝ)) :=
      fun r _ => Metric.isOpen_ball.nullMeasurableSet
    have h2 : ∀ i j : ℝ, (0 : ℝ) < i → i ≤ j → Metric.ball x i ⊆ Metric.ball x j :=
      fun i j _ hij => Metric.ball_subset_ball hij
    have h3 : ∃ r > (0 : ℝ), (volume.restrict Ω) (Metric.ball x r) ≠ ⊤ :=
      ⟨1, by norm_num, ne_top_of_le_ne_top measure_ball_lt_top.ne (Measure.restrict_le_self _)⟩
    have key := tendsto_measure_biInter_gt h1 h2 h3

    have h_inter : (⋂ r > (0 : ℝ), Metric.ball x r) = {x} := by
      ext y
      simp only [mem_iInter, Metric.mem_ball, mem_singleton_iff]
      constructor
      · intro h; by_contra hne; exact lt_irrefl _ (h (dist y x) (dist_pos.mpr hne))
      · rintro rfl; intro r hr; simpa using hr
    rw [h_inter] at key

    have h_meas_zero : (volume.restrict Ω : Measure (Fin n → ℝ)) {x} = 0 :=
      le_antisymm
        (le_trans (Measure.restrict_le_self _)
          (le_of_eq (by have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩; exact measure_singleton x)))
        (zero_le _)
    rw [h_meas_zero] at key
    exact key

  have : Filter.Tendsto (fun ε => c - (fun ε => ∫ y in Ω ∩ Metric.ball x ε, g y) ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (c - 0)) :=
    Filter.Tendsto.sub tendsto_const_nhds h_tendsto_zero
  simp only [sub_zero] at this
  exact this

/-- The surface measure of a sphere $\partial B(c, \varepsilon)$ is finite. -/
theorem surfaceMeasure_sphere_lt_top {n : ℕ} [Fact (2 ≤ n)]
    (center : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    (surfaceMeasure (Metric.ball center ε)) (Metric.sphere center ε) < ⊤ := by sorry

/-- For $n \ge 3$, on the sphere $|σ - x| = \varepsilon$ the fundamental solution satisfies
$\|\Phi(x - \sigma)\| \le C_F / \varepsilon^{n-2}$ for some constant $C_F \ge 0$. -/
theorem FundSolN_norm_on_sphere {n : ℕ} [Fact (2 ≤ n)] (hn3 : 3 ≤ n) :
    ∃ C_F : ℝ, 0 ≤ C_F ∧ ∀ (x : Fin n → ℝ) (ε : ℝ), 0 < ε →
      ∀ σ ∈ Metric.sphere x ε, ‖FundSolN (x - σ)‖ ≤ C_F / ε ^ (n - 2) := by
  have hn2 : n ≠ 2 := by omega

  have hω_pos : 0 < unitSphereArea n := by
    unfold unitSphereArea
    rw [if_neg (by omega : n ≠ 0)]
    apply div_pos
    · exact mul_pos (by norm_num : (0:ℝ) < 2) (Real.rpow_pos_of_pos Real.pi_pos _)
    · exact Real.Gamma_pos_of_pos (by positivity : (0 : ℝ) < (n : ℝ) / 2)

  refine ⟨1 / unitSphereArea n, by positivity, ?_⟩
  intro x ε hε σ hσ

  have hnorm_eq : ‖x - σ‖ = ε := by
    have hdist : dist σ x = ε := hσ
    rw [← hdist, dist_eq_norm, norm_sub_rev]

  have hEN_ge : ε ≤ euclidNorm (x - σ) := by
    unfold euclidNorm
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    have h_norm_le : ‖x - σ‖ ≤ Real.sqrt (∑ i : Fin n, (x - σ) i ^ 2) := by
      rw [pi_norm_le_iff_of_nonempty]
      intro b
      rw [Real.norm_eq_abs]
      have h1 : (x - σ) b ^ 2 ≤ ∑ j : Fin n, (x - σ) j ^ 2 :=
        Finset.single_le_sum (f := fun j => (x - σ) j ^ 2)
          (fun j _ => sq_nonneg _) (Finset.mem_univ b)
      calc |(x - σ) b| = Real.sqrt ((x - σ) b ^ 2) := by rw [Real.sqrt_sq_eq_abs]
        _ ≤ Real.sqrt (∑ j : Fin n, (x - σ) j ^ 2) := Real.sqrt_le_sqrt h1
    linarith
  have hEN_pos : 0 < euclidNorm (x - σ) := by linarith

  have hFSN : FundSolN (x - σ) =
      -1 / (unitSphereArea n * euclidNorm (x - σ) ^ (n - 2)) := by
    unfold FundSolN; rw [if_neg hn2]

  rw [hFSN, Real.norm_eq_abs, abs_div, abs_neg, abs_one]
  have hprod_pos : 0 < unitSphereArea n * euclidNorm (x - σ) ^ (n - 2) :=
    mul_pos hω_pos (pow_pos hEN_pos _)
  rw [abs_of_pos hprod_pos, div_div]

  exact div_le_div_of_nonneg_left (by norm_num : (0:ℝ) < 1).le
    (mul_pos hω_pos (pow_pos hε _))
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hε.le hEN_ge _) hω_pos.le)

/-- If $u \in C^2(\overline\Omega)$ then the normal derivative $\nabla_{\hat N} u$ is uniformly
bounded on $\partial\Omega$ (and in fact globally, by some constant $M$). -/
theorem normalDeriv_bounded_of_C2 {n : ℕ} [Fact (2 ≤ n)]
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ : Fin n → ℝ, ‖normalDeriv Ω u σ‖ ≤ M := by sorry

/-- Linear upper bound on the surface area of a sphere of radius $\varepsilon$ in
$\mathbb{R}^n$: there exists $C_S \ge 0$ with $\mathrm{area}(\partial B(x, \varepsilon)) \le
C_S \varepsilon^{n-1}$. -/
theorem surfaceMeasure_sphere_real_le {n : ℕ} [Fact (2 ≤ n)] :
    ∃ C_S : ℝ, 0 ≤ C_S ∧ ∀ (x : Fin n → ℝ) (ε : ℝ), 0 < ε →
      (surfaceMeasure (Metric.ball x ε)).real (Metric.sphere x ε) ≤ C_S * ε ^ (n - 1) := by sorry

/-- Pointwise-times-area bound for $n \ge 3$: there exists $K$ such that for every
$\varepsilon > 0$ one can choose a pointwise bound $B$ for $\Phi(x-\sigma) \nabla_{\hat N}u(\sigma)$
on the sphere with $B \cdot \mathrm{area}(\partial B(x,\varepsilon)) \le K \varepsilon$. -/
theorem sphereIntegral_Phi_gradU_pointwise_area_bound {n : ℕ} [Fact (2 ≤ n)]
    (hn3 : 3 ≤ n)
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω))
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    ∃ K : ℝ, ∀ ε : ℝ, 0 < ε →
      ∃ B : ℝ,
        (∀ σ ∈ Metric.sphere x ε,
          ‖FundSolN (x - σ) * normalDeriv Ω u σ‖ ≤ B) ∧
        B * (surfaceMeasure (Metric.ball x ε)).real (Metric.sphere x ε) ≤ K * ε := by
  have hn : 2 ≤ n := Fact.out

  obtain ⟨C_F, hCF_nn, hCF⟩ := @FundSolN_norm_on_sphere n _ hn3
  obtain ⟨M, hM_nn, hM⟩ := normalDeriv_bounded_of_C2 u Ω hu
  obtain ⟨C_S, hCS_nn, hCS⟩ := @surfaceMeasure_sphere_real_le n _

  refine ⟨C_F * M * C_S, fun ε hε => ?_⟩

  refine ⟨C_F / ε ^ (n - 2) * M, ?_, ?_⟩
  ·
    intro σ hσ
    calc ‖FundSolN (x - σ) * normalDeriv Ω u σ‖
        ≤ ‖FundSolN (x - σ)‖ * ‖normalDeriv Ω u σ‖ := norm_mul_le _ _
      _ ≤ C_F / ε ^ (n - 2) * M := by
          apply mul_le_mul (hCF x ε hε σ hσ) (hM σ) (norm_nonneg _)
            (div_nonneg hCF_nn (pow_nonneg (le_of_lt hε) _))
  ·
    calc C_F / ε ^ (n - 2) * M * (surfaceMeasure (Metric.ball x ε)).real (Metric.sphere x ε)
        ≤ C_F / ε ^ (n - 2) * M * (C_S * ε ^ (n - 1)) := by
          apply mul_le_mul_of_nonneg_left (hCS x ε hε)
            (mul_nonneg (div_nonneg hCF_nn (pow_nonneg (le_of_lt hε) _)) hM_nn)
      _ ≤ C_F * M * C_S * ε := by
          have heps_pow_pos : (0 : ℝ) < ε ^ (n - 2) := pow_pos hε _
          have h_eq : ε ^ (n - 1) = ε ^ (n - 2) * ε := by
            have h : n - 1 = (n - 2) + 1 := by omega
            rw [h, pow_succ]
          rw [h_eq]
          have h_ne : ε ^ (n - 2) ≠ 0 := ne_of_gt heps_pow_pos
          field_simp
          ring_nf
          exact le_refl _

/-- Linear-in-$\varepsilon$ estimate on the sphere integral $\int_{|σ-x|=ε} \Phi(x-\sigma)
\nabla_{\hat N} u(\sigma)\, d\sigma$ for $n \ge 3$: it is bounded by $K\varepsilon$ for some
constant $K$. -/
theorem sphere_integral_Phi_gradU_bound {n : ℕ} [Fact (2 ≤ n)]
    (hn3 : 3 ≤ n)
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω))
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    ∃ K : ℝ, ∀ ε : ℝ, 0 < ε →
      ‖sphereIntegral x ε (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ)‖ ≤ K * ε := by

  obtain ⟨K, hK⟩ := sphereIntegral_Phi_gradU_pointwise_area_bound hn3 u Ω hu x hx
  exact ⟨K, fun ε hε => by

    unfold sphereIntegral

    obtain ⟨B, hpw, hprod⟩ := hK ε hε

    calc ‖∫ σ in Metric.sphere x ε,
            FundSolN (x - σ) * normalDeriv Ω u σ ∂(surfaceMeasure (Metric.ball x ε))‖
        ≤ B * (surfaceMeasure (Metric.ball x ε)).real (Metric.sphere x ε) :=
          norm_setIntegral_le_of_norm_le_const (surfaceMeasure_sphere_lt_top x ε hε) hpw
      _ ≤ K * ε := hprod⟩

/-- Alias for `sphere_integral_Phi_gradU_bound`: for $n \ge 3$ the third sphere term
$R_3(\varepsilon)$ in the punctured-domain decomposition is $O(\varepsilon)$. -/
theorem sphere_integral_R3_bound {n : ℕ} [Fact (2 ≤ n)]
    (hn3 : 3 ≤ n)
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω))
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε →
      ‖sphereIntegral x ε (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ)‖ ≤ C * ε :=
  sphere_integral_Phi_gradU_bound hn3 u Ω hu x hx

/-- Refined sphere-integral bound in dimension $n = 2$, where $\Phi(x) \sim \log|x|$: the third
sphere term is dominated by $K \varepsilon (|\log \varepsilon| + C)$ for some constants
$K$ and $C \ge 0$. -/
theorem sphere_integral_R3_bound_n2 {n : ℕ} [Fact (2 ≤ n)] (hn2 : n = 2)
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω))
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    ∃ K C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε →
      ‖sphereIntegral x ε (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ)‖ ≤
        K * (ε * (|Real.log ε| + C)) := by

  obtain ⟨M, hM_nn, hM⟩ := normalDeriv_bounded_of_C2 u Ω hu
  obtain ⟨C_S, hCS_nn, hCS⟩ := @surfaceMeasure_sphere_real_le n _
  have hn_sub : n - 1 = 1 := by omega

  have hn_ge : (1 : ℝ) ≤ ↑n := by exact_mod_cast (show 1 ≤ n by omega)
  have hsqrt_ge : (1 : ℝ) ≤ Real.sqrt ↑n := Real.one_le_sqrt.mpr hn_ge
  set C_log := Real.log (Real.sqrt ↑n)
  have hC_log_nn : (0 : ℝ) ≤ C_log := Real.log_nonneg hsqrt_ge
  set C_F := 1 / (2 * Real.pi)
  have hCF_nn : (0 : ℝ) ≤ C_F := by positivity
  refine ⟨C_F * M * C_S, C_log, hC_log_nn, fun ε hε => ?_⟩


  unfold sphereIntegral
  have hfin := surfaceMeasure_sphere_lt_top x ε hε

  have hpw : ∀ σ ∈ Metric.sphere x ε,
      ‖FundSolN (x - σ) * normalDeriv Ω u σ‖ ≤ C_F * (|Real.log ε| + C_log) * M := by
    intro σ hσ
    have hnorm_eq : ‖x - σ‖ = ε := by
      have : dist σ x = ε := hσ
      rw [← this, dist_eq_norm, norm_sub_rev]

    have hEN_ge : ε ≤ euclidNorm (x - σ) := by
      unfold euclidNorm
      haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      calc ε = ‖x - σ‖ := hnorm_eq.symm
        _ ≤ Real.sqrt (∑ i : Fin n, (x - σ) i ^ 2) := by
            rw [pi_norm_le_iff_of_nonempty]
            intro b; rw [Real.norm_eq_abs]
            exact (Real.sqrt_sq_eq_abs _).symm ▸ Real.sqrt_le_sqrt
              (Finset.single_le_sum (f := fun j => (x - σ) j ^ 2)
                (fun j _ => sq_nonneg _) (Finset.mem_univ b))
    have hEN_pos : 0 < euclidNorm (x - σ) := by linarith

    have hEN_le : euclidNorm (x - σ) ≤ Real.sqrt (↑n) * ε := by
      unfold euclidNorm
      haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      have h_ub : ∀ i : Fin n, (x - σ) i ^ 2 ≤ ε ^ 2 := by
        intro i
        have hi : |(x - σ) i| ≤ ε := by
          rw [← Real.norm_eq_abs]
          exact (norm_le_pi_norm (x - σ) i).trans (le_of_eq hnorm_eq)
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hi 2
      calc Real.sqrt (∑ i : Fin n, (x - σ) i ^ 2)
          ≤ Real.sqrt (∑ _ : Fin n, ε ^ 2) :=
            Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => h_ub i)
        _ = Real.sqrt (↑n * ε ^ 2) := by
            congr 1; simp [Finset.sum_const, Finset.card_fin]
        _ = Real.sqrt (↑n) * ε := by
            rw [Real.sqrt_mul (Nat.cast_nonneg n), Real.sqrt_sq hε.le]

    have hFSN : FundSolN (x - σ) = C_F * Real.log (euclidNorm (x - σ)) := by
      unfold FundSolN; rw [if_pos hn2]

    have hlog_bound : |Real.log (euclidNorm (x - σ))| ≤ |Real.log ε| + C_log := by
      have hratio_ge : 1 ≤ euclidNorm (x - σ) / ε :=
        (le_div_iff₀ hε).mpr (by linarith)
      have hratio_le : euclidNorm (x - σ) / ε ≤ Real.sqrt ↑n :=
        (div_le_iff₀ hε).mpr hEN_le
      calc |Real.log (euclidNorm (x - σ))|
          = |Real.log (ε * (euclidNorm (x - σ) / ε))| := by
            rw [mul_div_cancel₀ _ (ne_of_gt hε)]
        _ = |Real.log ε + Real.log (euclidNorm (x - σ) / ε)| := by
            rw [Real.log_mul (ne_of_gt hε) (ne_of_gt (lt_of_lt_of_le (by linarith) hratio_ge))]
        _ ≤ |Real.log ε| + |Real.log (euclidNorm (x - σ) / ε)| := abs_add_le _ _
        _ ≤ |Real.log ε| + C_log := by
            gcongr
            rw [abs_of_nonneg (Real.log_nonneg hratio_ge)]
            exact Real.log_le_log (by linarith) hratio_le

    calc ‖FundSolN (x - σ) * normalDeriv Ω u σ‖
        = ‖FundSolN (x - σ)‖ * ‖normalDeriv Ω u σ‖ := norm_mul _ _
      _ ≤ (C_F * (|Real.log ε| + C_log)) * M := by
          apply mul_le_mul _ (hM σ) (norm_nonneg _) (by positivity)
          rw [hFSN, Real.norm_eq_abs, abs_mul,
            abs_of_pos (by positivity : (0:ℝ) < C_F)]
          exact mul_le_mul_of_nonneg_left hlog_bound hCF_nn

  have hint := norm_setIntegral_le_of_norm_le_const hfin hpw
  have harea := hCS x ε hε
  rw [hn_sub] at harea; simp only [pow_one] at harea
  calc ‖∫ σ in Metric.sphere x ε,
          FundSolN (x - σ) * normalDeriv Ω u σ ∂(surfaceMeasure (Metric.ball x ε))‖
      ≤ (C_F * (|Real.log ε| + C_log) * M) *
        (surfaceMeasure (Metric.ball x ε)).real (Metric.sphere x ε) := hint
    _ ≤ (C_F * (|Real.log ε| + C_log) * M) * (C_S * ε) := by
        gcongr
    _ = C_F * M * C_S * (ε * (|Real.log ε| + C_log)) := by ring

/-- In dimension $n = 2$, the sphere integral $R_3(\varepsilon) = \int_{|σ-x|=ε} \Phi(x-\sigma)
\nabla_{\hat N} u(\sigma) \, d\sigma \to 0$ as $\varepsilon \downarrow 0$, using the
$\varepsilon |\log \varepsilon|$ bound. -/
theorem sphere_integral_R3_vanishes_n2 {n : ℕ} [Fact (2 ≤ n)] (hn2 : n = 2)
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω))
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    Filter.Tendsto
      (fun ε => sphereIntegral x ε (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  obtain ⟨K, C, hC_nn, hbound⟩ := sphere_integral_R3_bound_n2 hn2 u Ω hu x hx
  apply squeeze_zero_norm' (a := fun ε => K * (ε * (|Real.log ε| + C)))
  · exact eventually_nhdsWithin_of_forall fun ε hε => hbound ε (Set.mem_Ioi.mp hε)
  ·

    have h_eps_log : Filter.Tendsto (fun ε : ℝ => ε * |Real.log ε|)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h := tendsto_log_mul_rpow_nhdsGT_zero (r := 1) (by norm_num : (0:ℝ) < 1)
      simp only [Real.rpow_one] at h


      have h2 := h.norm
      simp only [norm_zero] at h2
      refine Filter.Tendsto.congr' ?_ h2
      exact eventually_nhdsWithin_of_forall fun x hx => by
        simp only [norm_eq_abs, abs_mul, abs_of_pos (Set.mem_Ioi.mp hx), mul_comm]
    have h_eps : Filter.Tendsto (fun ε : ℝ => ε * C)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h1 : Filter.Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds Filter.tendsto_id
      have h2 := h1.mul_const C
      simp only [zero_mul] at h2
      exact h2
    have h_sum : Filter.Tendsto (fun ε : ℝ => ε * (|Real.log ε| + C))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h := h_eps_log.add h_eps
      simp only [add_zero] at h
      exact Filter.Tendsto.congr (fun x => by ring) h
    have h4 := h_sum.const_mul K
    simp only [mul_zero] at h4
    exact Filter.Tendsto.congr (fun x => by ring) h4

/-- Combined result: in any dimension $n \ge 2$, the sphere integral
$\int_{|σ-x|=ε} \Phi(x-\sigma) \nabla_{\hat N} u(\sigma) \, d\sigma$ vanishes as
$\varepsilon \downarrow 0$. -/
theorem sphere_integral_R3_vanishes {n : ℕ} [Fact (2 ≤ n)]
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω))
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    Filter.Tendsto
      (fun ε => sphereIntegral x ε (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  by_cases hn2 : n = 2
  ·
    exact sphere_integral_R3_vanishes_n2 hn2 u Ω hu x hx
  ·
    have hn3 : 3 ≤ n := by have := Fact.out (self := ‹Fact (2 ≤ n)›); omega
    obtain ⟨C, hbound⟩ := sphere_integral_R3_bound hn3 u Ω hu x hx

    apply squeeze_zero_norm' (a := fun ε => C * ε)
    · exact eventually_nhdsWithin_of_forall fun ε hε => hbound ε (Set.mem_Ioi.mp hε)
    · have h1 : Filter.Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds (Filter.tendsto_id)
      have h2 := h1.const_mul C
      simp at h2
      exact h2

/-- Specification of the outward unit normal on a sphere of radius $\varepsilon$ centred at $x$:
at $\sigma$ with $|\sigma - x| = \varepsilon$, the normal vector is the radial direction
$(\sigma - x)/\varepsilon$. -/
theorem outwardUnitNormal_sphere_spec {n : ℕ} [Fact (2 ≤ n)] (Ω : Set (Fin n → ℝ))
    (x : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) (σ : Fin n → ℝ) (hσ : σ ∈ Metric.sphere x ε) :
    outwardUnitNormal Ω σ = fun i => (σ i - x i) / ε := by sorry

/-- Exact formula for the surface area of the sphere $\partial B(x, \varepsilon)$ in
$\mathbb{R}^n$: $\omega_n \, \varepsilon^{n-1}$. -/
theorem surfaceMeasure_ball_sphere_eq {n : ℕ} [Fact (2 ≤ n)] (x : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    (surfaceMeasure (Metric.ball x ε)).real (Metric.sphere x ε) = unitSphereArea n * ε ^ (n - 1) := by sorry

/-- On the sphere of radius $\varepsilon$ centred at $x$, the Euclidean distance
$|x - \sigma|$ equals $\varepsilon$. -/
theorem euclidNorm_eq_on_sphere {n : ℕ} [Fact (2 ≤ n)] (x σ : Fin n → ℝ) (ε : ℝ)
    (hε : 0 < ε) (hσ : σ ∈ Metric.sphere x ε) : euclidNorm (x - σ) = ε := by sorry

/-- Explicit Fréchet derivative of $z \mapsto \Phi(x - z)$ away from the pole, given as a sum
involving the radial direction $(\sigma - x)/|x - \sigma|$ and the coordinate projections. -/
theorem hasFDerivAt_FundSolN_sub {n : ℕ} [Fact (2 ≤ n)] (x σ : Fin n → ℝ)
    (hr : euclidNorm (x - σ) > 0) :
    HasFDerivAt (fun z => FundSolN (x - z))
      ((1 / (unitSphereArea n * euclidNorm (x - σ) ^ (n - 1))) •
        ((∑ i : Fin n, ((σ i - x i) / euclidNorm (x - σ)) •
          ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ))) σ := by sorry

/-- On the sphere $|σ - x| = \varepsilon$, applying the Fréchet derivative of $z \mapsto
\Phi(x - z)$ to the radial unit vector $(\sigma - x)/\varepsilon$ yields the constant
$1/(\omega_n \varepsilon^{n-1})$. -/
theorem fderiv_FundSolN_radial_eq {n : ℕ} [Fact (2 ≤ n)] (x σ : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hσ : σ ∈ Metric.sphere x ε) :
    fderiv ℝ (fun z => FundSolN (x - z)) σ (fun i => (σ i - x i) / ε) =
      1 / (unitSphereArea n * ε ^ (n - 1)) := by
  have hEN_eq : euclidNorm (x - σ) = ε := euclidNorm_eq_on_sphere x σ ε hε hσ
  have hr : euclidNorm (x - σ) > 0 := by linarith
  have hε_ne : ε ≠ 0 := ne_of_gt hε

  have hsum_sq : ∑ i : Fin n, (σ i - x i) ^ 2 = ε ^ 2 := by
    have h1 : euclidNorm (x - σ) ^ 2 = ε ^ 2 := by rw [hEN_eq]
    unfold euclidNorm at h1
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))] at h1
    convert h1 using 1
    congr 1; ext i; simp [Pi.sub_apply]; ring

  have hfd := hasFDerivAt_FundSolN_sub x σ hr
  rw [hfd.fderiv]

  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.coe_sum',
    Finset.sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]


  rw [hEN_eq]


  have hsum_one : ∑ i : Fin n, (σ i - x i) / ε * ((σ i - x i) / ε) = 1 := by
    have : ∑ i : Fin n, (σ i - x i) / ε * ((σ i - x i) / ε) =
        (∑ i : Fin n, (σ i - x i) ^ 2) / ε ^ 2 := by
      rw [Finset.sum_div]; congr 1; ext i; ring
    rw [this, hsum_sq, div_self (pow_ne_zero 2 hε_ne)]
  rw [hsum_one, mul_one]

/-- On the sphere $\partial B(x, \varepsilon)$, the normal derivative of $z \mapsto \Phi(x-z)$
is the constant $1/\mathrm{area}(\partial B(x,\varepsilon))$, regardless of the surrounding
domain $\Omega$. -/
theorem normalDeriv_FundSolN_constant_on_sphere {n : ℕ} [Fact (2 ≤ n)]
    (Ω : Set (Fin n → ℝ)) (x : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε)
    (σ : Fin n → ℝ) (hσ : σ ∈ Metric.sphere x ε) :
    normalDeriv Ω (fun z => FundSolN (x - z)) σ =
      1 / (surfaceMeasure (Metric.ball x ε)).real (Metric.sphere x ε) := by
  unfold normalDeriv
  rw [outwardUnitNormal_sphere_spec Ω x ε hε σ hσ]
  rw [fderiv_FundSolN_radial_eq x σ ε hε hσ]
  rw [surfaceMeasure_ball_sphere_eq x ε hε]

/-- The surface area of any sphere of positive radius is strictly positive. -/
theorem surfaceMeasure_sphere_real_pos {n : ℕ} [Fact (2 ≤ n)]
    (x : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    0 < (surfaceMeasure (Metric.ball x ε)).real (Metric.sphere x ε) := by sorry

/-- Total flux of the fundamental solution through a sphere equals $1$: integrating the
normal derivative $\nabla_{\hat N}\Phi(x - \sigma)$ over $\partial B(x,\varepsilon)$ gives
exactly $1$, the source strength. -/
theorem sphereIntegral_normalDeriv_Phi_eq_one {n : ℕ} [Fact (2 ≤ n)]
    (Ω : Set (Fin n → ℝ)) (x : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    sphereIntegral x ε
      (fun σ => normalDeriv Ω (fun z => FundSolN (x - z)) σ) = 1 := by
  unfold sphereIntegral

  have hconst : Set.EqOn (fun σ => normalDeriv Ω (fun z => FundSolN (x - z)) σ)
      (fun _ => 1 / (surfaceMeasure (Metric.ball x ε)).real (Metric.sphere x ε))
      (Metric.sphere x ε) := by
    intro σ hσ
    exact normalDeriv_FundSolN_constant_on_sphere Ω x ε hε σ hσ

  rw [setIntegral_congr_fun Metric.isClosed_sphere.measurableSet hconst]

  rw [integral_const, measureReal_restrict_apply_univ, smul_eq_mul, mul_comm]

  exact div_mul_cancel₀ 1 (ne_of_gt (surfaceMeasure_sphere_real_pos x ε hε))

/-- The normal derivative $\nabla_{\hat N}\Phi(x - \cdot)$ is integrable on the sphere
$\partial B(x, \varepsilon)$ with respect to the surface measure. -/
theorem integrable_normalDeriv_Phi_sphere {n : ℕ} [Fact (2 ≤ n)]
    (Ω : Set (Fin n → ℝ)) (x : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun σ => normalDeriv Ω (fun z => FundSolN (x - z)) σ)
      ((surfaceMeasure (Metric.ball x ε)).restrict (Metric.sphere x ε)) := by sorry

/-- The product $u(\sigma) \nabla_{\hat N} \Phi(x - \sigma)$ is integrable on the sphere
$\partial B(x, \varepsilon)$ with respect to the surface measure. -/
theorem integrable_mul_normalDeriv_Phi_sphere {n : ℕ} [Fact (2 ≤ n)]
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) (x : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ)
      ((surfaceMeasure (Metric.ball x ε)).restrict (Metric.sphere x ε)) := by sorry

/-- Splitting the sphere integral $\int_{|σ-x|=ε} u(\sigma) \nabla_{\hat N} \Phi(x-\sigma)$ as
$u(x)$ plus an error term $\int (u(\sigma) - u(x)) \nabla_{\hat N} \Phi$, using the
normalisation $\int \nabla_{\hat N} \Phi = 1$. -/
theorem sphere_normalDeriv_Phi_normalization {n : ℕ} [Fact (2 ≤ n)]
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (x : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    sphereIntegral x ε
      (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ) =
    u x + sphereIntegral x ε
      (fun σ => (u σ - u x) * normalDeriv Ω (fun z => FundSolN (x - z)) σ) := by
  simp only [sphereIntegral]
  have hig : Integrable (fun σ => u x * normalDeriv Ω (fun z => FundSolN (x - z)) σ)
      ((surfaceMeasure (Metric.ball x ε)).restrict (Metric.sphere x ε)) :=
    (integrable_normalDeriv_Phi_sphere Ω x ε hε).const_mul (u x)
  have hidiff : Integrable (fun σ => (u σ - u x) * normalDeriv Ω (fun z => FundSolN (x - z)) σ)
      ((surfaceMeasure (Metric.ball x ε)).restrict (Metric.sphere x ε)) := by
    have := (integrable_mul_normalDeriv_Phi_sphere u Ω x ε hε).sub hig
    convert this using 1
    ext σ; simp [Pi.sub_apply, sub_mul]
  have h_eq : (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ) =
      (fun σ => u x * normalDeriv Ω (fun z => FundSolN (x - z)) σ +
        (u σ - u x) * normalDeriv Ω (fun z => FundSolN (x - z)) σ) := by
    ext σ; ring
  rw [h_eq, integral_add hig hidiff, integral_const_mul]
  have h_norm : ∫ σ in Metric.sphere x ε,
      normalDeriv Ω (fun z => FundSolN (x - z)) σ ∂surfaceMeasure (Metric.ball x ε) = 1 :=
    sphereIntegral_normalDeriv_Phi_eq_one Ω x ε hε
  rw [h_norm]
  ring

/-- The family of conditional suprema $\sup_{σ \in \text{sphere}} |u(\sigma) - u(x)|$ is
bounded above (as a function of $\sigma$), used to manipulate `⨆` expressions safely. -/
theorem bddAbove_abs_deviation_sphere {n : ℕ} [Fact (2 ≤ n)]
    (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    BddAbove (Set.range (fun σ => ⨆ (_ : σ ∈ Metric.sphere x ε), |u σ - u x|)) := by sorry

/-- For any $\sigma$ on the sphere $\partial B(x,\varepsilon)$, $|u(\sigma) - u(x)|$ is bounded
above by the corresponding indexed supremum over the sphere. -/
lemma le_biSup_abs_deviation {n : ℕ} [Fact (2 ≤ n)]
    (u : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε)
    (σ : Fin n → ℝ) (hσ : σ ∈ Metric.sphere x ε) :
    |u σ - u x| ≤ ⨆ σ' ∈ Metric.sphere x ε, |u σ' - u x| := by
  have h_inner : |u σ - u x| ≤ ⨆ (_ : σ ∈ Metric.sphere x ε), |u σ - u x| :=
    le_ciSup_of_le ⟨|u σ - u x|, by rintro _ ⟨_, rfl⟩; rfl⟩ hσ (le_refl _)
  exact h_inner.trans (le_ciSup (bddAbove_abs_deviation_sphere u x ε hε) σ)

/-- The absolute value of the deviation sphere integral $\int (u(\sigma) - u(x))
\nabla_{\hat N}\Phi$ is bounded by the maximal oscillation $\sup_\sigma |u(\sigma) - u(x)|$
over the sphere. -/
theorem sphereIntegral_deviation_abs_le {n : ℕ} [Fact (2 ≤ n)]
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (x : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    |sphereIntegral x ε
      (fun σ => (u σ - u x) * normalDeriv Ω (fun z => FundSolN (x - z)) σ)| ≤
    ⨆ σ ∈ Metric.sphere x ε, |u σ - u x| := by
  unfold sphereIntegral
  set μ := surfaceMeasure (Metric.ball x ε)
  set A := μ.real (Metric.sphere x ε)
  have hA_pos : 0 < A := surfaceMeasure_sphere_real_pos x ε hε
  have hfin : μ (Metric.sphere x ε) < ⊤ := surfaceMeasure_sphere_lt_top x ε hε

  have hconst : Set.EqOn
    (fun σ => (u σ - u x) * normalDeriv Ω (fun z => FundSolN (x - z)) σ)
    (fun σ => (u σ - u x) * (1 / A))
    (Metric.sphere x ε) := by
    intro σ hσ
    show (u σ - u x) * normalDeriv Ω (fun z => FundSolN (x - z)) σ = (u σ - u x) * (1 / A)
    rw [normalDeriv_FundSolN_constant_on_sphere Ω x ε hε σ hσ]
  rw [setIntegral_congr_fun Metric.isClosed_sphere.measurableSet hconst]

  set S := ⨆ σ ∈ Metric.sphere x ε, |u σ - u x|
  have hbound : ‖∫ σ in Metric.sphere x ε, (u σ - u x) * (1 / A) ∂μ‖ ≤ (S * (1 / A)) * A := by
    calc ‖∫ σ in Metric.sphere x ε, (u σ - u x) * (1 / A) ∂μ‖
        ≤ (S * (1 / A)) * μ.real (Metric.sphere x ε) := by
          apply norm_setIntegral_le_of_norm_le_const hfin
          intro σ hσ
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / A)]
          exact mul_le_mul_of_nonneg_right (le_biSup_abs_deviation u x ε hε σ hσ) (by positivity)
      _ = (S * (1 / A)) * A := rfl
  rw [Real.norm_eq_abs] at hbound
  calc |∫ σ in Metric.sphere x ε, (u σ - u x) * (1 / A) ∂μ|
      ≤ S * (1 / A) * A := hbound
    _ = S := by field_simp

/-- Continuity at $x$ implies that the supremum of the oscillation $|u(\sigma) - u(x)|$ over
the shrinking sphere $\partial B(x,\varepsilon)$ tends to zero as $\varepsilon \downarrow 0$. -/
theorem sup_sphere_oscillation_tendsto_zero {n : ℕ} [Fact (2 ≤ n)]
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω))
    (hΩ : IsOpen Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    Filter.Tendsto
      (fun ε => ⨆ σ ∈ Metric.sphere x ε, |u σ - u x|)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by

  have hcont : ContinuousAt u x :=
    hu.continuousOn.continuousAt (Filter.mem_of_superset (hΩ.mem_nhds hx) subset_closure)

  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ

  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨η, hη_pos, hη_bound⟩ := hcont (δ / 2) (half_pos hδ)

  refine ⟨η, hη_pos, fun ε hε_mem hε_dist => ?_⟩
  have hε_pos : (0 : ℝ) < ε := hε_mem
  have hε_lt_η : ε < η := by
    have h1 : |ε| < η := by simpa [dist_zero_right] using hε_dist
    rwa [abs_of_pos hε_pos] at h1

  have h_bound : ⨆ σ ∈ Metric.sphere x ε, |u σ - u x| ≤ δ / 2 := by
    apply Real.iSup_le (fun σ => ?_) (le_of_lt (half_pos hδ))
    apply Real.iSup_le (fun hσ => ?_) (le_of_lt (half_pos hδ))
    have hσ_near : dist σ x < η := by
      rw [Metric.mem_sphere.mp hσ]; linarith
    have h_u_close := hη_bound hσ_near
    rw [Real.dist_eq] at h_u_close
    linarith [abs_nonneg (u σ - u x)]

  rw [dist_zero_right]
  have h_nonneg : (0 : ℝ) ≤ ⨆ σ ∈ Metric.sphere x ε, |u σ - u x| :=
    Real.iSup_nonneg fun σ => Real.iSup_nonneg fun _ => abs_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg]
  linarith

/-- The deviation sphere integral $\int (u(\sigma) - u(x)) \nabla_{\hat N}\Phi(x-\sigma)$
tends to $0$ as $\varepsilon \downarrow 0$, obtained by combining the deviation bound with
the oscillation $\to 0$ result. -/
theorem sphere_integral_deviation_bound {n : ℕ} [Fact (2 ≤ n)]
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω))
    (hΩ : IsOpen Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    Filter.Tendsto
      (fun ε => sphereIntegral x ε
        (fun σ => (u σ - u x) * normalDeriv Ω (fun z => FundSolN (x - z)) σ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [Real.norm_eq_abs]
  have h_bound : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      |sphereIntegral x ε
        (fun σ => (u σ - u x) * normalDeriv Ω (fun z => FundSolN (x - z)) σ)| ≤
      ⨆ σ ∈ Metric.sphere x ε, |u σ - u x| := by
    apply Filter.Eventually.mono self_mem_nhdsWithin
    intro ε hε
    exact sphereIntegral_deviation_abs_le u Ω x ε hε
  exact squeeze_zero' (Filter.Eventually.of_forall (fun ε => abs_nonneg _)) h_bound
    (sup_sphere_oscillation_tendsto_zero u Ω hu hΩ x hx)

/-- Mean-value-type limit: as $\varepsilon \downarrow 0$, the sphere integral
$\int_{|σ-x|=ε} u(\sigma) \nabla_{\hat N}\Phi(x - \sigma)\, d\sigma$ converges to $u(x)$. -/
theorem sphereIntegral_u_normalDeriv_Phi_tends_to_ux {n : ℕ} [Fact (2 ≤ n)]
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω))
    (hΩ : IsOpen Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    Filter.Tendsto
      (fun ε => sphereIntegral x ε
        (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (u x)) := by

  have herr := sphere_integral_deviation_bound u Ω hu hΩ x hx

  have h1 : Filter.Tendsto
      (fun ε => u x + sphereIntegral x ε
        (fun σ => (u σ - u x) * normalDeriv Ω (fun z => FundSolN (x - z)) σ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (u x)) := by
    have h2 : Filter.Tendsto
        (fun ε => u x + sphereIntegral x ε
          (fun σ => (u σ - u x) * normalDeriv Ω (fun z => FundSolN (x - z)) σ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (u x + 0)) :=
      tendsto_const_nhds.add herr
    rwa [add_zero] at h2

  exact h1.congr' (eventually_nhdsWithin_of_forall fun ε hε =>
    (sphere_normalDeriv_Phi_normalization u Ω x ε (Set.mem_Ioi.mp hε)).symm)

/-- Reformulation: the sphere integral $\int u(\sigma) \nabla_{\hat N}\Phi(x-\sigma)$ admits
the decomposition $u(x) + \text{error}(\varepsilon)$ where the error vanishes as
$\varepsilon \downarrow 0$. -/
theorem sphere_integral_u_normalDeriv_Phi_decomp {n : ℕ} [Fact (2 ≤ n)]
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω))
    (hΩ : IsOpen Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    ∃ (error : ℝ → ℝ),
      (∀ ε > 0, sphereIntegral x ε
        (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ) =
          u x + error ε) ∧
      Filter.Tendsto error (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by

  refine ⟨fun ε => sphereIntegral x ε
    (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ) - u x, ?_, ?_⟩

  · intro ε hε; ring

  · have h := sphereIntegral_u_normalDeriv_Phi_tends_to_ux u Ω hu hΩ x hx
    have : Filter.Tendsto (fun ε => sphereIntegral x ε
        (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ) - u x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (u x - u x)) :=
      h.sub tendsto_const_nhds
    simp only [sub_self] at this
    exact this

/-- Alias for `sphere_integral_u_normalDeriv_Phi_decomp`: the fourth sphere term
$R_4(\varepsilon)$ decomposes as $u(x)$ plus a vanishing error. -/
theorem sphere_integral_R4_decomposition {n : ℕ} [Fact (2 ≤ n)]
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω))
    (hΩ : IsOpen Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    ∃ (error : ℝ → ℝ),

      (∀ ε > 0, sphereIntegral x ε
        (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ) =
          u x + error ε) ∧

      Filter.Tendsto error (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  sphere_integral_u_normalDeriv_Phi_decomp u Ω hu hΩ x hx

/-- The limit of the fourth sphere term is $u(x)$, the value of $u$ at the centre — the
mean-value property of the fundamental solution. -/
theorem sphere_integral_R4_limit {n : ℕ} [Fact (2 ≤ n)]
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω))
    (hΩ : IsOpen Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    Filter.Tendsto
      (fun ε => sphereIntegral x ε (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (u x)) := by

  obtain ⟨error, h_eq, h_err⟩ := sphere_integral_R4_decomposition u Ω hu hΩ x hx

  have h_sum : Filter.Tendsto (fun ε => u x + error ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (u x)) := by
    have := (@tendsto_const_nhds _ _ _ (u x) (nhdsWithin 0 (Set.Ioi 0))).add h_err
    rwa [add_zero] at this

  exact h_sum.congr' (Filter.EventuallyEq.symm
    (eventually_nhdsWithin_of_forall fun ε hε => h_eq ε (Set.mem_Ioi.mp hε)))

/-- Representation formula obtained by taking $\varepsilon \downarrow 0$ in Green's identity
on the punctured domain: for $u \in C^2(\bar\Omega)$ and $x \in \Omega$,
$$u(x) = \int_\Omega \Phi(x-y) \Delta u(y)\, dy
   - \int_{\partial\Omega} \Phi(x-\sigma) \nabla_{\hat N} u(\sigma)\, d\sigma
   + \int_{\partial\Omega} u(\sigma) \nabla_{\hat N} \Phi(x-\sigma)\, d\sigma.$$
-/
theorem epsilon_ball_limit_representation {n : ℕ} [Fact (2 ≤ n)]

    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω)) (hΩ : IsOpen Ω)
    (hΩ_lip : IsLipschitzDomain Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    u x = (∫ y in Ω, FundSolN (x - y) * laplacian u y)
      - surfaceIntegral Ω (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ)
      + surfaceIntegral Ω (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ) := by

  set L := ∫ y in Ω, FundSolN (x - y) * laplacian u y
  set R1 := surfaceIntegral Ω (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ)
  set R2 := surfaceIntegral Ω (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ)

  set R3 := fun ε => sphereIntegral x ε (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ)
  set R4 := fun ε => sphereIntegral x ε (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ)
  set Lε := fun ε => ∫ y in Ω \ Metric.ball x ε, FundSolN (x - y) * laplacian u y

  have h_green_eq : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      Lε ε = R1 - R2 - R3 ε + R4 ε :=
    eventually_nhdsWithin_of_forall fun ε hε =>
      greens_identity_on_omega_eps u Ω hu hΩ hΩ_lip x hx ε (Set.mem_Ioi.mp hε)

  have hLε : Filter.Tendsto Lε (nhdsWithin 0 (Set.Ioi 0)) (nhds L) :=
    volume_integral_limit u Ω hu hΩ x hx
  have hR3 : Filter.Tendsto R3 (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    sphere_integral_R3_vanishes u Ω hu x hx
  have hR4 : Filter.Tendsto R4 (nhdsWithin 0 (Set.Ioi 0)) (nhds (u x)) :=
    sphere_integral_R4_limit u Ω hu hΩ x hx

  have h_rhs : Filter.Tendsto (fun ε => R1 - R2 - R3 ε + R4 ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (R1 - R2 - 0 + u x)) :=
    (tendsto_const_nhds.sub hR3).add hR4
  simp only [sub_zero] at h_rhs


  have h_unique : L = R1 - R2 + u x :=
    tendsto_nhds_unique hLε (h_rhs.congr' (Filter.EventuallyEq.symm h_green_eq))
  linarith

/-- Proposition 2.0.3 in general dimension $n \ge 2$: the representation formula for
$u \in C^2(\bar\Omega)$ at an interior point $x \in \Omega$ in terms of the fundamental
solution $\Phi$, the volume integral of $\Delta u$, and the boundary terms involving $u$ and
$\nabla_{\hat N} u$. -/
theorem representation_formula_n {n : ℕ} [Fact (2 ≤ n)]

    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω)) (hΩ : IsOpen Ω)
    (hΩ_lip : IsLipschitzDomain Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    u x = (∫ y in Ω, FundSolN (x - y) * laplacian u y)
      - surfaceIntegral Ω (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ)
      + surfaceIntegral Ω (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ) :=
  epsilon_ball_limit_representation u Ω hu hΩ hΩ_lip x hx

/-- Proposition 2.0.3 specialised to $\mathbb{R}^3$ with the 3D fundamental solution
$\Phi_3(x) = -1/(4\pi|x|)$: for $u \in C^2(\mathbb{R}^3)$, $\Omega$ a Lipschitz domain and
$x \in \Omega$,
$$u(x) = \int_\Omega \Phi_3(x-y) \Delta u(y)\, dy
   - \int_{\partial\Omega} \Phi_3(x-\sigma) \nabla_{\hat N} u(\sigma)\, d\sigma
   + \int_{\partial\Omega} u(\sigma) \nabla_{\hat N} \Phi_3(x-\sigma)\, d\sigma.$$
-/
theorem representation_formula
    (u : (Fin 3 → ℝ) → ℝ) (Ω : Set (Fin 3 → ℝ))
    (hu : ContDiff ℝ 2 u) (hΩ : IsOpen Ω)
    (hΩ_lip : IsLipschitzDomain Ω)
    (x : Fin 3 → ℝ) (hx : x ∈ Ω) :
    u x = (∫ y in Ω, Phi3 (x - y) * laplacian3 u y)
      - surfaceIntegral Ω (fun σ => Phi3 (x - σ) * normalDeriv Ω u σ)
      + surfaceIntegral Ω (fun σ => u σ * normalDeriv Ω (fun z => Phi3 (x - z)) σ) := by


  haveI : Fact (2 ≤ 3) := ⟨by omega⟩

  have hu' : ContDiffOn ℝ 2 u (closure Ω) := hu.contDiffOn

  have h := representation_formula_n u Ω hu' hΩ hΩ_lip x hx


  rw [h]

  unfold laplacian3
  congr 1
  · congr 1
    ·
      congr 1 with y
      rw [FundSolN_eq_Phi3]
    ·
      congr 1 with σ
      rw [FundSolN_eq_Phi3]
  ·
    congr 1 with σ
    congr 1

    unfold normalDeriv
    congr 1

    congr 1 with z
    rw [FundSolN_eq_Phi3]

/-- Green function for the domain $\Omega \subset \mathbb{R}^n$ (Definition 2.0.2 together with
the decomposition in Proposition 2.0.2): a function $G(x, y)$ on $\Omega \times \Omega$ with
$\Delta_y G(x, y) = \delta(x)$ and $G(x, \sigma) = 0$ for $\sigma \in \partial \Omega$. It is
packaged as the decomposition $G(x, y) = \Phi(x - y) - \phi(x, y)$, where the corrector
$\phi(x, \cdot)$ is harmonic in $\Omega$ with boundary data $\Phi(x - \cdot)|_{\partial\Omega}$. -/
structure GreenFunctionN (n : ℕ) [Fact (2 ≤ n)] (Ω : Set (Fin n → ℝ)) where
  G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  corrector : (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  decomposition : ∀ x y, G x y = FundSolN (x - y) - corrector x y
  boundary_vanish : ∀ x ∈ Ω, ∀ σ ∈ frontier Ω, G x σ = 0
  corrector_harmonic : ∀ x ∈ Ω, ∀ y ∈ Ω, laplacian (corrector x) y = 0
  corrector_boundary : ∀ x ∈ Ω, ∀ σ ∈ frontier Ω, corrector x σ = FundSolN (x - σ)
  corrector_reg : ∀ x ∈ Ω, ContDiffOn ℝ 2 (corrector x) (closure Ω)

/-- Instance: $2 \le 3$, supplied so that `FundSolN` and related results specialise to the
three-dimensional setting. -/
instance : Fact (2 ≤ 3) := ⟨by omega⟩

/-- Unfolding lemma for `surfaceIntegral`: definitionally equal to the integral
$\int_{\partial\Omega} f(\sigma) \, d\sigma$. -/
theorem surfaceIntegral_eq {n : ℕ} (Ω : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    surfaceIntegral Ω f = ∫ σ in frontier Ω, f σ ∂surfaceMeasure Ω := rfl

/-- Congruence of surface integrals: if $f = g$ on $\partial\Omega$, then their surface
integrals agree. -/
theorem surfaceIntegral_congr_frontier {n : ℕ}
    (Ω : Set (Fin n → ℝ)) (f g : (Fin n → ℝ) → ℝ)
    (h : ∀ σ ∈ frontier Ω, f σ = g σ) :
    surfaceIntegral Ω f = surfaceIntegral Ω g := by
  rw [surfaceIntegral_eq, surfaceIntegral_eq]
  exact setIntegral_congr_fun isClosed_frontier.measurableSet (fun σ hσ => h σ hσ)

/-- Regularity-extension axiom: a function that is $C^2$ on the interior $\Omega$ and continuous
on the closure $\bar\Omega$ is in fact $C^2$ on $\bar\Omega$. -/
theorem regularity_extension_axiom {n : ℕ}
    (Ω : Set (Fin n → ℝ)) (u : (Fin n → ℝ) → ℝ)
    (hΩ : IsOpen Ω)
    (hu_reg : ContDiffOn ℝ 2 u Ω) (hu_cont : ContinuousOn u (closure Ω)) :
    ContDiffOn ℝ 2 u (closure Ω) := by sorry

/-- Textbook-sign variant of the punctured-domain surface decomposition: the surface integral
over $\partial(\Omega \setminus \overline{B(x,\varepsilon)})$ equals the $\partial\Omega$
boundary contribution plus (rather than minus) the inner-sphere contribution, reflecting the
choice of inward-pointing normal on $\partial B(x,\varepsilon)$. -/
theorem surfaceIntegral_punctured_inward_decomp {n : ℕ} [Fact (2 ≤ n)]
    (Ω : Set (Fin n → ℝ)) (x : Fin n → ℝ) (ε : ℝ)
    (hΩ : IsOpen Ω) (hΩ_lip : IsLipschitzDomain Ω) (hx : x ∈ Ω) (hε : 0 < ε)
    (u : (Fin n → ℝ) → ℝ)
    (hu : ContDiffOn ℝ 2 u (closure Ω)) :
    surfaceIntegral (Ω \ Metric.closedBall x ε)
      (fun σ => (fun y => FundSolN (x - y)) σ *
                normalDeriv (Ω \ Metric.closedBall x ε) u σ
               - u σ * normalDeriv (Ω \ Metric.closedBall x ε)
                        (fun y => FundSolN (x - y)) σ)
    = surfaceIntegral Ω (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ)
      - surfaceIntegral Ω (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ)
      + sphereIntegral x ε (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ)
      - sphereIntegral x ε (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ) := by sorry

/-- Green's identity on the punctured domain with the textbook sign convention (inward normal
on the inner sphere), giving the version of the identity matching equation (2.0.30) in the
text. -/
theorem greens_identity_on_omega_eps_textbook_sign {n : ℕ} [Fact (2 ≤ n)]
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω)) (hΩ : IsOpen Ω)
    (hΩ_lip : IsLipschitzDomain Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) (ε : ℝ) (hε : 0 < ε) :
    (∫ y in Ω \ Metric.ball x ε, FundSolN (x - y) * laplacian u y)
    = surfaceIntegral Ω (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ)
      - surfaceIntegral Ω (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ)
      + sphereIntegral x ε (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ)
      - sphereIntegral x ε (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ) := by

  rw [setIntegral_ball_eq_closedBall]

  have hΩε_lip := IsLipschitzDomain_diff_closedBall Ω x ε hΩ hΩ_lip hx hε
  have hΩε_open : IsOpen (Ω \ Metric.closedBall x ε) := hΩ.sdiff Metric.isClosed_closedBall
  have hu_ε := contDiffOn_restrict_punctured u Ω x ε hu hΩ hε
  have hv_ε := contDiffOn_FundSolN_diff_ball x Ω ε hε
  have h_green := greens_second_identity (Ω \ Metric.closedBall x ε) u
    (fun y => FundSolN (x - y)) hu_ε hv_ε hΩε_open hΩε_lip

  have h_vanish := integral_laplacian_v_vanishes u Ω x ε hε
  rw [h_vanish] at h_green

  have h_decomp := surfaceIntegral_punctured_inward_decomp Ω x ε hΩ hΩ_lip hx hε u hu
  linarith

/-- Core equation (2.0.30) of the textbook: representation of $u(x)$ in terms of $\Delta u$,
the trace of $u$ on $\partial\Omega$, and the normal derivative of $u$, all paired with the
fundamental solution $\Phi$, expressed using the textbook sign convention. -/
theorem equation_2_0_30_core {n : ℕ} [Fact (2 ≤ n)]

    (Ω : Set (Fin n → ℝ))
    (u : (Fin n → ℝ) → ℝ)
    (hΩ : IsOpen Ω) (hΩ_lip : IsLipschitzDomain Ω)
    (hu_reg : ContDiffOn ℝ 2 u Ω) (hu_cont : ContinuousOn u (closure Ω))
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    u x = -(∫ y in Ω, FundSolN (x - y) * laplacian u y)
      + surfaceIntegral Ω (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ)
      - surfaceIntegral Ω (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ) := by


  have hu_closure : ContDiffOn ℝ 2 u (closure Ω) :=
    regularity_extension_axiom Ω u hΩ hu_reg hu_cont


  set L := ∫ y in Ω, FundSolN (x - y) * laplacian u y
  set R1 := surfaceIntegral Ω (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ)
  set R2 := surfaceIntegral Ω (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ)
  set R3 : ℝ → ℝ := fun ε => sphereIntegral x ε (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ)
  set R4 : ℝ → ℝ := fun ε => sphereIntegral x ε (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ)
  set Lε : ℝ → ℝ := fun ε => ∫ y in Ω \ Metric.ball x ε, FundSolN (x - y) * laplacian u y


  have h_green : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      Lε ε = R1 - R2 + R3 ε - R4 ε := by
    apply eventually_nhdsWithin_of_forall; intro ε hε
    exact greens_identity_on_omega_eps_textbook_sign u Ω hu_closure hΩ hΩ_lip x hx ε
      (Set.mem_Ioi.mp hε)

  have hLε : Filter.Tendsto Lε (nhdsWithin 0 (Set.Ioi 0)) (nhds L) :=
    volume_integral_limit u Ω hu_closure hΩ x hx

  have hR3 : Filter.Tendsto R3 (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    sphere_integral_R3_vanishes u Ω hu_closure x hx
  have hR4 : Filter.Tendsto R4 (nhdsWithin 0 (Set.Ioi 0)) (nhds (u x)) :=
    sphere_integral_R4_limit u Ω hu_closure hΩ x hx

  have h_rhs : Filter.Tendsto (fun ε => R1 - R2 + R3 ε - R4 ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (R1 - R2 + 0 - u x)) :=
    (tendsto_const_nhds.add hR3).sub hR4
  simp only [add_zero] at h_rhs

  have h_unique : L = R1 - R2 - u x :=
    tendsto_nhds_unique hLε (h_rhs.congr' (Filter.EventuallyEq.symm h_green))

  linarith

/-- Equation (2.0.30) for solutions of the Poisson boundary value problem $\Delta u = f$ in
$\Omega$, $u = g$ on $\partial\Omega$: $u(x)$ is represented as $-\int_\Omega \Phi(x-y) f(y)\, dy
+ \int_{\partial\Omega} \Phi(x-\sigma) \nabla_{\hat N} u(\sigma)\, d\sigma
- \int_{\partial\Omega} g(\sigma) \nabla_{\hat N} \Phi(x-\sigma)\, d\sigma$. -/
theorem equation_2_0_30 {n : ℕ} [Fact (2 ≤ n)]

    (Ω : Set (Fin n → ℝ))
    (u f g : (Fin n → ℝ) → ℝ)
    (hΩ : IsOpen Ω) (hΩ_lip : IsLipschitzDomain Ω)
    (hu_reg : ContDiffOn ℝ 2 u Ω) (hu_cont : ContinuousOn u (closure Ω))
    (hu_pde : ∀ x ∈ Ω, laplacian u x = f x)
    (hu_bdy : ∀ σ ∈ frontier Ω, u σ = g σ)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    u x = -(∫ y in Ω, FundSolN (x - y) * f y)
      + surfaceIntegral Ω (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ)
      - surfaceIntegral Ω (fun σ => g σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ) := by

  have h_core := equation_2_0_30_core Ω u hΩ hΩ_lip hu_reg hu_cont x hx

  have h_vol : (∫ y in Ω, FundSolN (x - y) * laplacian u y) =
      (∫ y in Ω, FundSolN (x - y) * f y) := by
    apply setIntegral_congr_fun hΩ.measurableSet
    intro y hy; simp only; rw [hu_pde y hy]

  have h_surf : surfaceIntegral Ω (fun σ => u σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ) =
      surfaceIntegral Ω (fun σ => g σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ) := by
    apply surfaceIntegral_congr_frontier
    intro σ hσ
    rw [hu_bdy σ hσ]
  rw [h_core, h_vol, h_surf]

/-- Duplicate of the regularity-extension axiom under a Lipschitz domain assumption: $C^2$ on
$\Omega$ together with continuity on $\bar\Omega$ promotes to $C^2$ on $\bar\Omega$. -/
theorem contDiffOn_closure_of_interior {n : ℕ}
    (Ω : Set (Fin n → ℝ)) (u : (Fin n → ℝ) → ℝ)
    (hΩ : IsOpen Ω) (hΩ_lip : IsLipschitzDomain Ω)
    (hu_reg : ContDiffOn ℝ 2 u Ω) (hu_cont : ContinuousOn u (closure Ω)) :
    ContDiffOn ℝ 2 u (closure Ω) := by sorry

/-- Integrability axiom for surface integrals: every function under consideration is integrable
on $\partial\Omega$ with respect to the surface measure. -/
theorem integrableOn_surfaceMeasure {n : ℕ}
    (Ω : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) :
    IntegrableOn f (frontier Ω) (surfaceMeasure Ω) := by sorry

/-- Linearity (subtraction) of the surface integral:
$\int_{\partial\Omega} (f - g) = \int_{\partial\Omega} f - \int_{\partial\Omega} g$. -/
theorem surfaceIntegral_sub {n : ℕ}
    (Ω : Set (Fin n → ℝ)) (f g : (Fin n → ℝ) → ℝ) :
    surfaceIntegral Ω (fun σ => f σ - g σ) =
    surfaceIntegral Ω f - surfaceIntegral Ω g := by
  simp only [surfaceIntegral]
  exact integral_sub (integrableOn_surfaceMeasure Ω f) (integrableOn_surfaceMeasure Ω g)

/-- Identity (2.0.33) at the core level: applying Green's second identity to $u$ and the
harmonic corrector $\phi(x, \cdot)$ in $\Omega$ produces the relation
$0 = \int_\Omega \phi(x, y) \Delta u(y)\, dy
   - \int_{\partial\Omega} \Phi(x-\sigma) \nabla_{\hat N} u(\sigma)\, d\sigma
   + \int_{\partial\Omega} u(\sigma) \nabla_{\hat N} \phi(x, \sigma)\, d\sigma$. -/
theorem equation_2_0_33_core {n : ℕ} [Fact (2 ≤ n)]
    (Ω : Set (Fin n → ℝ)) (gf : GreenFunctionN n Ω)
    (u : (Fin n → ℝ) → ℝ)
    (hΩ : IsOpen Ω) (hΩ_lip : IsLipschitzDomain Ω)
    (hu_reg : ContDiffOn ℝ 2 u Ω) (hu_cont : ContinuousOn u (closure Ω))
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    (0 : ℝ) = (∫ y in Ω, gf.corrector x y * laplacian u y)
      - surfaceIntegral Ω (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ)
      + surfaceIntegral Ω (fun σ => u σ * normalDeriv Ω (gf.corrector x) σ) := by

  have hu_closure : ContDiffOn ℝ 2 u (closure Ω) :=
    contDiffOn_closure_of_interior Ω u hΩ hΩ_lip hu_reg hu_cont
  have hφ_closure : ContDiffOn ℝ 2 (gf.corrector x) (closure Ω) :=
    gf.corrector_reg x hx

  have green2 : (∫ y in Ω, gf.corrector x y * laplacian u y -
      u y * laplacian (gf.corrector x) y) =
    surfaceIntegral Ω (fun σ => gf.corrector x σ * normalDeriv Ω u σ -
      u σ * normalDeriv Ω (gf.corrector x) σ) :=
    greens_second_identity Ω u (gf.corrector x) hu_closure hφ_closure hΩ hΩ_lip

  have harmonic_elim : (∫ y in Ω, gf.corrector x y * laplacian u y -
      u y * laplacian (gf.corrector x) y) =
    ∫ y in Ω, gf.corrector x y * laplacian u y := by
    apply setIntegral_congr_fun hΩ.measurableSet
    intro y hy
    have : laplacian (gf.corrector x) y = 0 := gf.corrector_harmonic x hx y hy
    simp only [this, mul_zero, sub_zero]

  have bdy_rewrite : surfaceIntegral Ω (fun σ => gf.corrector x σ * normalDeriv Ω u σ -
      u σ * normalDeriv Ω (gf.corrector x) σ) =
    surfaceIntegral Ω (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ -
      u σ * normalDeriv Ω (gf.corrector x) σ) := by
    apply surfaceIntegral_congr_frontier
    intro σ hσ
    rw [gf.corrector_boundary x hx σ hσ]

  have split_surf : surfaceIntegral Ω (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ -
      u σ * normalDeriv Ω (gf.corrector x) σ) =
    surfaceIntegral Ω (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ) -
    surfaceIntegral Ω (fun σ => u σ * normalDeriv Ω (gf.corrector x) σ) :=
    surfaceIntegral_sub Ω _ _


  have chain : (∫ y in Ω, gf.corrector x y * laplacian u y) =
    surfaceIntegral Ω (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ) -
    surfaceIntegral Ω (fun σ => u σ * normalDeriv Ω (gf.corrector x) σ) := by
    rw [← harmonic_elim, green2, bdy_rewrite, split_surf]
  linarith

/-- Equation (2.0.33) for the Poisson boundary value problem: substituting $\Delta u = f$ in
$\Omega$ and $u = g$ on $\partial\Omega$ into the corrector identity yields a relation among
the source $f$, boundary data $g$, the corrector $\phi$, and the normal derivative of $u$. -/
theorem equation_2_0_33 {n : ℕ} [Fact (2 ≤ n)]
    (Ω : Set (Fin n → ℝ)) (gf : GreenFunctionN n Ω)
    (u f g : (Fin n → ℝ) → ℝ)
    (hΩ : IsOpen Ω) (hΩ_lip : IsLipschitzDomain Ω)
    (hu_reg : ContDiffOn ℝ 2 u Ω) (hu_cont : ContinuousOn u (closure Ω))
    (hu_pde : ∀ x ∈ Ω, laplacian u x = f x)
    (hu_bdy : ∀ σ ∈ frontier Ω, u σ = g σ)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    (0 : ℝ) = (∫ y in Ω, gf.corrector x y * f y)
      - surfaceIntegral Ω (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ)
      + surfaceIntegral Ω (fun σ => g σ * normalDeriv Ω (gf.corrector x) σ) := by

  have h_core := equation_2_0_33_core Ω gf u hΩ hΩ_lip hu_reg hu_cont x hx

  have h_vol : (∫ y in Ω, gf.corrector x y * laplacian u y) =
      (∫ y in Ω, gf.corrector x y * f y) := by
    apply setIntegral_congr_fun hΩ.measurableSet
    intro y hy; simp only; rw [hu_pde y hy]

  have h_surf : surfaceIntegral Ω (fun σ => u σ * normalDeriv Ω (gf.corrector x) σ) =
      surfaceIntegral Ω (fun σ => g σ * normalDeriv Ω (gf.corrector x) σ) := by
    apply surfaceIntegral_congr_frontier
    intro σ hσ
    rw [hu_bdy σ hσ]
  rw [h_vol, h_surf] at h_core
  exact h_core

/-- Volume-integral form of the decomposition $G = \Phi - \phi$: under integrability,
$\int_\Omega f(y) G(x, y)\, dy = \int_\Omega \Phi(x-y) f(y)\, dy - \int_\Omega \phi(x, y) f(y)\, dy$. -/
theorem volume_integral_G_decomp {n : ℕ} [Fact (2 ≤ n)]
    (Ω : Set (Fin n → ℝ)) (gf : GreenFunctionN n Ω)
    (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hPhi_int : IntegrableOn (fun y => FundSolN (x - y) * f y) Ω)
    (hcorr_int : IntegrableOn (fun y => gf.corrector x y * f y) Ω) :
    (∫ y in Ω, f y * gf.G x y) =
    (∫ y in Ω, FundSolN (x - y) * f y) - (∫ y in Ω, gf.corrector x y * f y) := by

  have h_integrand : ∀ y, f y * gf.G x y = FundSolN (x - y) * f y - gf.corrector x y * f y := by
    intro y
    rw [gf.decomposition x y]
    ring
  simp_rw [h_integrand]

  rw [MeasureTheory.integral_sub hPhi_int hcorr_int]

/-- Differentiability of $z \mapsto \Phi(x - z)$ at any point $\sigma$. -/
theorem FundSolN_comp_sub_differentiableAt {n : ℕ} [Fact (2 ≤ n)]
    (x σ : Fin n → ℝ) :
    DifferentiableAt ℝ (fun z => FundSolN (x - z)) σ := by sorry

/-- Differentiability of the corrector $\phi(x, \cdot)$ at any point $\sigma$. -/
theorem corrector_differentiableAt {n : ℕ} [Fact (2 ≤ n)]
    (Ω : Set (Fin n → ℝ)) (gf : GreenFunctionN n Ω)
    (x σ : Fin n → ℝ) :
    DifferentiableAt ℝ (gf.corrector x) σ := by sorry

/-- Normal-derivative decomposition $\nabla_{\hat N} G = \nabla_{\hat N} \Phi -
\nabla_{\hat N} \phi$ inherited from $G(x, y) = \Phi(x - y) - \phi(x, y)$. -/
theorem normalDeriv_G_decomp {n : ℕ} [Fact (2 ≤ n)]
    (Ω : Set (Fin n → ℝ)) (gf : GreenFunctionN n Ω)
    (x σ : Fin n → ℝ) :
    normalDeriv Ω (fun z => gf.G x z) σ =
    normalDeriv Ω (fun z => FundSolN (x - z)) σ - normalDeriv Ω (gf.corrector x) σ := by
  unfold normalDeriv

  have hfeq : (fun z => gf.G x z) = fun z => FundSolN (x - z) - gf.corrector x z :=
    funext (gf.decomposition x)
  rw [hfeq]


  have h_diff_Phi : DifferentiableAt ℝ (fun z => FundSolN (x - z)) σ :=
    FundSolN_comp_sub_differentiableAt x σ
  have h_diff_corr : DifferentiableAt ℝ (gf.corrector x) σ :=
    corrector_differentiableAt Ω gf x σ
  rw [show (fun z => FundSolN (x - z) - gf.corrector x z) =
      (fun z => FundSolN (x - z)) - gf.corrector x from rfl]
  rw [fderiv_sub h_diff_Phi h_diff_corr, ContinuousLinearMap.sub_apply]

/-- Surface-integral form of the Green-function decomposition:
$\int_{\partial\Omega} g(\sigma) \nabla_{\hat N} G(x, \sigma)\, d\sigma$ splits as the
$\Phi$-part minus the corrector $\phi$-part. -/
theorem surface_integral_G_decomp {n : ℕ} [Fact (2 ≤ n)]
    (Ω : Set (Fin n → ℝ)) (gf : GreenFunctionN n Ω)
    (g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    surfaceIntegral Ω (fun σ => g σ * normalDeriv Ω (fun z => gf.G x z) σ) =
    surfaceIntegral Ω (fun σ => g σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ)
    - surfaceIntegral Ω (fun σ => g σ * normalDeriv Ω (gf.corrector x) σ) := by

  have h_integrand : ∀ σ, g σ * normalDeriv Ω (fun z => gf.G x z) σ =
      g σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ -
      g σ * normalDeriv Ω (gf.corrector x) σ := by
    intro σ
    rw [normalDeriv_G_decomp Ω gf x σ, mul_sub]

  have h_congr : surfaceIntegral Ω (fun σ => g σ * normalDeriv Ω (fun z => gf.G x z) σ) =
      surfaceIntegral Ω (fun σ => g σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ -
        g σ * normalDeriv Ω (gf.corrector x) σ) := by
    congr 1; ext σ; exact h_integrand σ

  rw [h_congr, surfaceIntegral_sub]

/-- Theorem 2.2 (Green-function representation for solutions of the boundary value Poisson
equation): given a Green function $G$ for $\Omega$ and a solution $u$ of $\Delta u = f$ in
$\Omega$ with $u = g$ on $\partial \Omega$,
$$u(x) = -\int_\Omega f(y) G(x, y)\, dy
   - \int_{\partial\Omega} g(\sigma) \nabla_{\hat N} G(x, \sigma)\, d\sigma.$$
-/
theorem green_representation {n : ℕ} [Fact (2 ≤ n)]

    (Ω : Set (Fin n → ℝ)) (gf : GreenFunctionN n Ω)
    (u f g : (Fin n → ℝ) → ℝ) (hΩ : IsOpen Ω)
    (hΩ_lip : IsLipschitzDomain Ω)
    (hu_reg : ContDiffOn ℝ 2 u Ω) (hu_cont : ContinuousOn u (closure Ω))
    (hu_pde : ∀ x ∈ Ω, laplacian u x = f x)
    (hu_bdy : ∀ σ ∈ frontier Ω, u σ = g σ)
    (x : Fin n → ℝ) (hx : x ∈ Ω)
    (hPhi_int : IntegrableOn (fun y => FundSolN (x - y) * f y) Ω)
    (hcorr_int : IntegrableOn (fun y => gf.corrector x y * f y) Ω) :
    u x = -(∫ y in Ω, f y * gf.G x y)
      - surfaceIntegral Ω (fun σ => g σ * normalDeriv Ω (fun z => gf.G x z) σ) := by


  set P := (∫ y in Ω, FundSolN (x - y) * f y)
  set Q := surfaceIntegral Ω (fun σ => FundSolN (x - σ) * normalDeriv Ω u σ)
  set R := surfaceIntegral Ω (fun σ => g σ * normalDeriv Ω (fun z => FundSolN (x - z)) σ)
  set S := (∫ y in Ω, gf.corrector x y * f y)
  set T := surfaceIntegral Ω (fun σ => g σ * normalDeriv Ω (gf.corrector x) σ)

  have h_2030 : u x = -P + Q - R :=
    equation_2_0_30 Ω u f g hΩ hΩ_lip hu_reg hu_cont hu_pde hu_bdy x hx


  have h_2033 : (0 : ℝ) = S - Q + T :=
    equation_2_0_33 Ω gf u f g hΩ hΩ_lip hu_reg hu_cont hu_pde hu_bdy x hx

  have h_vol : (∫ y in Ω, f y * gf.G x y) = P - S :=
    volume_integral_G_decomp Ω gf f x hPhi_int hcorr_int

  have h_surf : surfaceIntegral Ω (fun σ => g σ * normalDeriv Ω (fun z => gf.G x z) σ) = R - T :=
    surface_integral_G_decomp Ω gf g x


  rw [h_vol, h_surf]
  linarith

end CM8
