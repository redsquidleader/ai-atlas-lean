/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Real Set MeasureTheory

noncomputable section

namespace CM17Lagrangian

/-- Spacetime $\mathbb{R}^{1+n}$ as the function type $\{0, 1, \ldots, n\} \to \mathbb{R}$.
The index $0$ is the time coordinate; indices $1, \ldots, n$ are spatial. -/
abbrev Spacetime (n : ℕ) := Fin (n + 1) → ℝ

/-- A scalar field on $\mathbb{R}^{1+n}$, i.e. a real-valued function
$\phi : \mathbb{R}^{1+n} \to \mathbb{R}$. -/
abbrev ScalarField (n : ℕ) := Spacetime n → ℝ

/-- A Lagrangian density $L(\phi, \partial \phi, x)$: a real-valued function of the field
value, the spacetime gradient (an $(n+1)$-tuple of partial derivatives), and the spacetime
point. -/
def Lagrangian (n : ℕ) := ℝ → (Fin (n + 1) → ℝ) → Spacetime n → ℝ

/-- The spacetime gradient $(\partial_{\mu} \phi)_{\mu = 0, \ldots, n}$ of a scalar field
$\phi$ at the point $x$, i.e. the $(n+1)$-tuple of partial derivatives. -/
def spacetimeGradient {n : ℕ} (φ : ScalarField n) (x : Spacetime n) : Fin (n + 1) → ℝ :=
  fun μ => fderiv ℝ φ x (Pi.single μ 1)

/-- The action functional $\mathcal{S}_K[\phi] = \int_K L(\phi(x), \partial \phi(x), x)\, dx$
of a scalar field $\phi$ on a region $K \subset \mathbb{R}^{1+n}$. -/
def action {n : ℕ} (L : Lagrangian n) (φ : ScalarField n) (K : Set (Spacetime n)) : ℝ :=
  ∫ x in K, L (φ x) (spacetimeGradient φ x) x

/-- A variation $\psi$ supported in $K$: a smooth ($C^{\infty}$) scalar field whose support
is contained in the region $K$. This is the class of admissible test perturbations of
$\phi$. -/
def IsVariation {n : ℕ} (K : Set (Spacetime n)) (ψ : ScalarField n) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) ψ ∧ Function.support ψ ⊆ K

/-- The one-parameter perturbation $\phi_{\varepsilon}(x) = \phi(x) + \varepsilon \psi(x)$
used to define the first variation of the action. -/
def perturbedField {n : ℕ} (φ ψ : ScalarField n) (ε : ℝ) : ScalarField n :=
  fun x => φ x + ε * ψ x

/-- A scalar field $\phi$ is a stationary point of the action: for every compact region $K$
and every variation $\psi$ supported in $K$, the first variation of the action vanishes,
$\left. \frac{d}{d\varepsilon} \right|_{\varepsilon = 0}
\mathcal{S}_K[\phi + \varepsilon \psi] = 0$. -/
def IsStationaryPoint {n : ℕ} (L : Lagrangian n) (φ : ScalarField n) : Prop :=
  ∀ (K : Set (Spacetime n)) (_hK : IsCompact K) (ψ : ScalarField n),
    IsVariation K ψ →
      deriv (fun ε => action L (perturbedField φ ψ ε) K) 0 = 0

/-- Partial derivative of the Lagrangian with respect to the field value $\phi$:
$\partial L / \partial \phi$ evaluated at $(\phi(x), \partial \phi(x), x)$. -/
def dL_dφ {n : ℕ} (L : Lagrangian n) (φ : ScalarField n) (x : Spacetime n) : ℝ :=
  deriv (fun v => L v (spacetimeGradient φ x) x) (φ x)

/-- Partial derivative of the Lagrangian with respect to the $\alpha$-th component of the
gradient: $\partial L / \partial(\partial_{\alpha} \phi)$ evaluated at
$(\phi(x), \partial \phi(x), x)$. -/
def dL_dgrad {n : ℕ} (L : Lagrangian n) (φ : ScalarField n)
    (x : Spacetime n) (α : Fin (n + 1)) : ℝ :=
  fderiv ℝ (fun p => L (φ x) p x) (spacetimeGradient φ x) (Pi.single α 1)

/-- The Euler-Lagrange operator applied to $\phi$ at $x$:
$\mathrm{EL}[\phi](x) = \dfrac{\partial L}{\partial \phi}
- \sum_{\alpha} \partial_{\alpha} \!\left( \dfrac{\partial L}{\partial(\partial_{\alpha} \phi)} \right)$.
A scalar field is stationary iff this operator vanishes identically. -/
def eulerLagrangeOperator {n : ℕ} (L : Lagrangian n) (φ : ScalarField n)
    (x : Spacetime n) : ℝ :=
  dL_dφ L φ x - ∑ α : Fin (n + 1),
    fderiv ℝ (fun y => dL_dgrad L φ y α) x (Pi.single α 1)

/-- Fundamental lemma of the calculus of variations: if $f$ is continuous and
$\int_K f \psi \, dx = 0$ for every compact $K$ and every smooth variation $\psi$ supported
in $K$, then $f \equiv 0$. -/
theorem ibp_fundamental_lemma {n : ℕ}
    (f : Spacetime n → ℝ)
    (hf_cont : Continuous f)
    (hf : ∀ (K : Set (Spacetime n)), IsCompact K →
      ∀ (ψ : ScalarField n), IsVariation K ψ →
        ∫ x in K, f x * ψ x = 0) :
    ∀ x : Spacetime n, f x = 0 := by
  set_option maxHeartbeats 800000 in
  by_contra h
  push Not at h
  obtain ⟨x₀, hx₀⟩ := h


  have hcont_at := hf_cont.continuousAt (x := x₀)

  have habs_pos : 0 < |f x₀| := abs_pos.mpr hx₀


  obtain ⟨δ, hδ_pos, hδ_ball⟩ :=
    Metric.continuousAt_iff.mp hcont_at (|f x₀|) habs_pos

  set rIn := δ / 4 with _hrIn_def
  set rOut := δ / 2 with _hrOut_def
  have hrIn_pos : 0 < rIn := by positivity
  have hrIn_lt_rOut : rIn < rOut := by linarith
  set b : ContDiffBump x₀ := ⟨rIn, rOut, hrIn_pos, hrIn_lt_rOut⟩

  have hb_smooth : ContDiff ℝ (⊤ : ℕ∞) (b : Spacetime n → ℝ) := b.contDiff
  have hb_supp_eq : Function.support (b : Spacetime n → ℝ) = Metric.ball x₀ rOut := b.support_eq
  have hb_supp_sub_delta : Function.support (b : Spacetime n → ℝ) ⊆ Metric.ball x₀ δ := by
    rw [hb_supp_eq]; exact Metric.ball_subset_ball (by linarith)
  have hb_compact : HasCompactSupport (b : Spacetime n → ℝ) := b.hasCompactSupport
  have hb_nonneg : ∀ y, 0 ≤ (b : Spacetime n → ℝ) y := fun y => b.nonneg
  have hb_x₀ : (b : Spacetime n → ℝ) x₀ = 1 := by
    apply b.one_of_mem_closedBall
    simp [Metric.mem_closedBall, dist_self]
    exact le_of_lt hrIn_pos


  have hf_sign : ∀ y ∈ Metric.ball x₀ δ, f x₀ * f y > 0 := by
    intro y hy
    have hclose := hδ_ball hy
    rw [Real.dist_eq] at hclose
    rcases lt_or_gt_of_ne hx₀ with hneg | hpos
    ·
      have : f y < 0 := by
        have := abs_lt.mp hclose
        linarith [abs_of_neg hneg]
      exact mul_pos_of_neg_of_neg hneg this
    ·
      have : f y > 0 := by
        have := abs_lt.mp hclose
        linarith [abs_of_pos hpos]
      exact mul_pos hpos this


  set ψ := fun y => f x₀ * (b : Spacetime n → ℝ) y with hψ_def

  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ := hb_smooth.const_smul (f x₀)

  have hψ_supp : Function.support ψ = Function.support (b : Spacetime n → ℝ) := by
    simp [hψ_def, Function.support, hx₀]

  set K := Metric.closedBall x₀ δ
  have hK : IsCompact K := isCompact_closedBall x₀ δ
  have hψ_var : IsVariation K ψ := by
    constructor
    · exact hψ_smooth
    · rw [hψ_supp]
      exact hb_supp_sub_delta.trans Metric.ball_subset_closedBall

  have hint := hf K hK ψ hψ_var


  rw [setIntegral_eq_integral_of_forall_compl_eq_zero] at hint
  ·


    have heq : ∫ x, f x * ψ x = f x₀ * ∫ x, f x * (b : Spacetime n → ℝ) x := by
      simp only [hψ_def]
      rw [show (fun x => f x * (f x₀ * (b : Spacetime n → ℝ) x)) =
        (fun x => f x₀ • (f x * (b : Spacetime n → ℝ) x)) from by ext; rw [smul_eq_mul]; ring]
      rw [integral_smul, smul_eq_mul]
    rw [heq] at hint


    have hint' : ∫ x, f x * (b : Spacetime n → ℝ) x = 0 :=
      (mul_eq_zero.mp hint).resolve_left hx₀


    have hg_cont : Continuous (fun x => f x₀ * f x * (b : Spacetime n → ℝ) x) :=
      (continuous_const.mul hf_cont).mul b.continuous
    have hg_compact : HasCompactSupport (fun x => f x₀ * f x * (b : Spacetime n → ℝ) x) := by
      have : (fun x => f x₀ * f x * (b : Spacetime n → ℝ) x) =
        (fun x => (f x₀ * f x) * (b : Spacetime n → ℝ) x) := by ext; ring
      rw [this]
      exact hb_compact.mul_left
    have hg_nonneg : 0 ≤ (fun x => f x₀ * f x * (b : Spacetime n → ℝ) x) := by
      intro x
      by_cases hxb : (b : Spacetime n → ℝ) x = 0
      · simp [hxb]
      · have hx_supp : x ∈ Function.support (b : Spacetime n → ℝ) := Function.mem_support.mpr hxb
        have hx_ball : x ∈ Metric.ball x₀ δ := hb_supp_sub_delta hx_supp
        exact mul_nonneg (le_of_lt (hf_sign x hx_ball)) (hb_nonneg x)
    have hg_x₀ : (fun x => f x₀ * f x * (b : Spacetime n → ℝ) x) x₀ ≠ 0 := by
      simp [hb_x₀]
      exact hx₀
    have hg_pos := @Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      _ _ _ _ (volume : Measure (Spacetime n)) _ _ _ x₀
      hg_cont hg_compact hg_nonneg hg_x₀


    have hg_eq : ∫ x, (fun x => f x₀ * f x * (b : Spacetime n → ℝ) x) x =
        f x₀ * ∫ x, f x * (b : Spacetime n → ℝ) x := by
      rw [show (fun x => f x₀ * f x * (b : Spacetime n → ℝ) x) =
        (fun x => f x₀ • (f x * (b : Spacetime n → ℝ) x)) from by ext; rw [smul_eq_mul]; ring]
      rw [integral_smul, smul_eq_mul]
    rw [hg_eq, hint'] at hg_pos
    simp at hg_pos
  ·
    intro x hx
    simp only [hψ_def]
    have : (b : Spacetime n → ℝ) x = 0 := by
      by_contra hbx
      have : x ∈ Function.support (b : Spacetime n → ℝ) := Function.mem_support.mpr hbx
      have : x ∈ K := (hb_supp_sub_delta.trans Metric.ball_subset_closedBall) this
      exact hx this
    simp [this]

/-- Smooth differentiation under the integral sign on a compact domain: if at $\varepsilon_0$
the parameter derivative $\partial_{\varepsilon} F(\varepsilon, x)$ exists pointwise with
limit $F'(x)$ and both $F(\varepsilon, \cdot)$ and $F'$ are continuous on $K$, then the
parameterized integral $\varepsilon \mapsto \int_K F(\varepsilon, x) \, dx$ has derivative
$\int_K F'(x) \, dx$ at $\varepsilon_0$. -/
theorem leibniz_smooth {n : ℕ}
    (F : ℝ → Spacetime n → ℝ) (F' : Spacetime n → ℝ)
    (K : Set (Spacetime n)) (ε₀ : ℝ)
    (hK : IsCompact K)
    (hpw : ∀ x ∈ K, HasDerivAt (F · x) (F' x) ε₀)
    (hF_cont : ∀ ε, ContinuousOn (F ε) K)
    (hF'_cont : ContinuousOn F' K) :
    HasDerivAt (fun ε => ∫ x in K, F ε x) (∫ x in K, F' x) ε₀ := by sorry

/-- Chain rule for the Lagrangian along a perturbation: at $\varepsilon = 0$, the
derivative of $\varepsilon \mapsto L(\phi + \varepsilon \psi, \partial(\phi + \varepsilon \psi), x)$
equals $\partial_{\phi} L \cdot \psi + \sum_{\alpha} \partial_{(\partial_{\alpha} \phi)} L
\cdot \partial_{\alpha} \psi$. -/
theorem lagrangian_chain_rule {n : ℕ} (L : Lagrangian n)
    (φ ψ : ScalarField n) (x : Spacetime n)
    (hL : ContDiff ℝ 2 (fun p : ℝ × (Fin (n + 1) → ℝ) × Spacetime n =>
      L p.1 p.2.1 p.2.2))
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    HasDerivAt (fun ε => L (φ x + ε * ψ x)
        (spacetimeGradient (perturbedField φ ψ ε) x) x)
      (dL_dφ L φ x * ψ x +
        ∑ α : Fin (n + 1), dL_dgrad L φ x α * spacetimeGradient ψ x α)
      0 := by sorry

/-- Continuity hypotheses needed to apply differentiation under the integral: both the
parameter-dependent Lagrangian integrand $L(\phi_{\varepsilon}, \partial \phi_{\varepsilon}, x)$
and the limit integrand $\partial_{\phi} L \cdot \psi + \sum_{\alpha} \partial_{(\partial_{\alpha} \phi)} L
\cdot \partial_{\alpha} \psi$ are continuous on $K$. -/
theorem lagrangian_integrand_continuous {n : ℕ} (L : Lagrangian n)
    (φ ψ : ScalarField n) (K : Set (Spacetime n))
    (hL : ContDiff ℝ 2 (fun p : ℝ × (Fin (n + 1) → ℝ) × Spacetime n =>
      L p.1 p.2.1 p.2.2))
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    (∀ ε, ContinuousOn (fun x => L (φ x + ε * ψ x)
      (spacetimeGradient (perturbedField φ ψ ε) x) x) K) ∧
    ContinuousOn (fun x => dL_dφ L φ x * ψ x +
      ∑ α : Fin (n + 1), dL_dgrad L φ x α * spacetimeGradient ψ x α) K := by sorry

/-- Integration by parts in a single coordinate direction: for $\psi$ compactly supported
in $K$ and $f$ of class $C^1$,
$\int_K f \, \partial_{\alpha} \psi \, dx = -\int_K (\partial_{\alpha} f) \, \psi \, dx$.
The boundary term vanishes because $\psi$ is supported in $K$. -/
theorem ibp_single_coordinate {n : ℕ}
    (f : Spacetime n → ℝ) (ψ : ScalarField n) (K : Set (Spacetime n))
    (α : Fin (n + 1))
    (hK : IsCompact K) (hψ : IsVariation K ψ)
    (hf : ContDiff ℝ 1 f) :
    ∫ x in K, f x * spacetimeGradient ψ x α =
    ∫ x in K, (-(fderiv ℝ f x (Pi.single α 1))) * ψ x := by sorry

/-- Integrability of all terms appearing in the Euler-Lagrange expansion: each piece of
$\partial_{\phi} L \cdot \psi$, $\sum_{\alpha} \partial_{(\partial_{\alpha} \phi)} L \cdot \partial_{\alpha} \psi$,
the integration-by-parts substitute $\sum_{\alpha} (-\partial_{\alpha} \partial_{(\partial_{\alpha} \phi)} L)
\cdot \psi$, and their per-coordinate components are integrable on $K$. -/
theorem el_terms_integrable {n : ℕ} (L : Lagrangian n)
    (φ ψ : ScalarField n) (K : Set (Spacetime n))
    (hK : IsCompact K) (hψ : IsVariation K ψ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × (Fin (n + 1) → ℝ) × Spacetime n =>
      L p.1 p.2.1 p.2.2))
    (hφ : ContDiff ℝ 2 φ) :
    IntegrableOn (fun x => dL_dφ L φ x * ψ x) K ∧
    IntegrableOn (fun x => ∑ α : Fin (n + 1),
      dL_dgrad L φ x α * spacetimeGradient ψ x α) K ∧
    IntegrableOn (fun x => ∑ α : Fin (n + 1),
      (-(fderiv ℝ (fun y => dL_dgrad L φ y α) x (Pi.single α 1))) * ψ x) K ∧
    (∀ α : Fin (n + 1),
      IntegrableOn (fun x => dL_dgrad L φ x α * spacetimeGradient ψ x α) K) ∧
    (∀ α : Fin (n + 1),
      IntegrableOn (fun x =>
        (-(fderiv ℝ (fun y => dL_dgrad L φ y α) x (Pi.single α 1))) * ψ x) K) := by sorry

/-- Smoothness of the gradient-derivative of the Lagrangian: if $L$ is $C^2$ in its
arguments and $\phi$ is $C^2$, then $x \mapsto \partial_{(\partial_{\alpha} \phi)} L (\phi(x),
\partial \phi(x), x)$ is $C^1$. -/
theorem dL_dgrad_contDiff {n : ℕ} (L : Lagrangian n)
    (φ : ScalarField n) (α : Fin (n + 1))
    (hL : ContDiff ℝ 2 (fun p : ℝ × (Fin (n + 1) → ℝ) × Spacetime n =>
      L p.1 p.2.1 p.2.2))
    (hφ : ContDiff ℝ 2 φ) :
    ContDiff ℝ 1 (fun x => dL_dgrad L φ x α) := by sorry

/-- Per-coordinate integration by parts applied to the gradient term: the integral
$\int_K \sum_{\alpha} \partial_{(\partial_{\alpha} \phi)} L \cdot \partial_{\alpha} \psi \, dx$
equals
$\int_K \sum_{\alpha} \bigl(-\partial_{\alpha} \partial_{(\partial_{\alpha} \phi)} L\bigr) \cdot \psi \, dx$,
together with the integrability of all involved terms. -/
theorem ibp_per_coordinate_sum {n : ℕ} (L : Lagrangian n)
    (φ ψ : ScalarField n) (K : Set (Spacetime n))
    (hK : IsCompact K) (hψ : IsVariation K ψ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × (Fin (n + 1) → ℝ) × Spacetime n =>
      L p.1 p.2.1 p.2.2))
    (hφ : ContDiff ℝ 2 φ) :
    ∫ x in K, ∑ α : Fin (n + 1), dL_dgrad L φ x α * spacetimeGradient ψ x α =
    ∫ x in K, ∑ α : Fin (n + 1),
      (-(fderiv ℝ (fun y => dL_dgrad L φ y α) x (Pi.single α 1))) * ψ x ∧
    IntegrableOn (fun x => dL_dφ L φ x * ψ x) K ∧
    IntegrableOn (fun x => ∑ α : Fin (n + 1),
      dL_dgrad L φ x α * spacetimeGradient ψ x α) K ∧
    IntegrableOn (fun x => ∑ α : Fin (n + 1),
      (-(fderiv ℝ (fun y => dL_dgrad L φ y α) x (Pi.single α 1))) * ψ x) K := by
  obtain ⟨hint_dφ, hint_grad, hint_neg, hint_grad_α, hint_neg_α⟩ :=
    el_terms_integrable L φ ψ K hK hψ hL hφ
  refine ⟨?_, hint_dφ, hint_grad, hint_neg⟩

  rw [integral_finset_sum _ (fun α _ => (hint_grad_α α).integrable)]
  rw [integral_finset_sum _ (fun α _ => (hint_neg_α α).integrable)]
  congr 1; ext α
  exact ibp_single_coordinate (fun x => dL_dgrad L φ x α) ψ K α hK hψ
    (dL_dgrad_contDiff L φ α hL hφ)

/-- Combining the pointwise chain rule with differentiation under the integral, the first
variation of the action equals the integral of the linearized integrand:
$\left. \frac{d}{d\varepsilon} \right|_{\varepsilon = 0} \mathcal{S}_K[\phi + \varepsilon \psi]
= \int_K \left( \partial_{\phi} L \cdot \psi + \sum_{\alpha} \partial_{(\partial_{\alpha} \phi)} L
\cdot \partial_{\alpha} \psi \right) dx$. -/
theorem leibniz_chain_rule {n : ℕ} (L : Lagrangian n)
    (φ ψ : ScalarField n) (K : Set (Spacetime n))
    (hK : IsCompact K)
    (hL : ContDiff ℝ 2 (fun p : ℝ × (Fin (n + 1) → ℝ) × Spacetime n =>
      L p.1 p.2.1 p.2.2))
    (hφ : ContDiff ℝ 2 φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    deriv (fun ε => action L (perturbedField φ ψ ε) K) 0 =
      ∫ x in K, (dL_dφ L φ x * ψ x +
        ∑ α : Fin (n + 1), dL_dgrad L φ x α * spacetimeGradient ψ x α) := by

  have heq : (fun ε => action L (perturbedField φ ψ ε) K) =
    (fun ε => ∫ x in K, L (φ x + ε * ψ x)
      (spacetimeGradient (perturbedField φ ψ ε) x) x) := by
    ext ε; simp only [action, perturbedField]
  rw [heq]

  obtain ⟨hF_cont, hF'_cont⟩ := lagrangian_integrand_continuous L φ ψ K hL hφ hψ

  exact (leibniz_smooth
    (fun ε x => L (φ x + ε * ψ x) (spacetimeGradient (perturbedField φ ψ ε) x) x)
    (fun x => dL_dφ L φ x * ψ x +
      ∑ α : Fin (n + 1), dL_dgrad L φ x α * spacetimeGradient ψ x α)
    K 0 hK
    (fun x _hx => lagrangian_chain_rule L φ ψ x hL hφ hψ)
    hF_cont hF'_cont).deriv

/-- Integrating by parts reorganizes the linearized integrand as the Euler-Lagrange
operator times $\psi$:
$\int_K \left( \partial_{\phi} L \cdot \psi + \sum_{\alpha} \partial_{(\partial_{\alpha} \phi)} L
\cdot \partial_{\alpha} \psi \right) dx = \int_K \mathrm{EL}[\phi] \cdot \psi \, dx$. -/
theorem ibp_euler_lagrange {n : ℕ} (L : Lagrangian n)
    (φ ψ : ScalarField n) (K : Set (Spacetime n))
    (hK : IsCompact K) (hψ : IsVariation K ψ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × (Fin (n + 1) → ℝ) × Spacetime n =>
      L p.1 p.2.1 p.2.2))
    (hφ : ContDiff ℝ 2 φ) :
    ∫ x in K, (dL_dφ L φ x * ψ x +
      ∑ α : Fin (n + 1), dL_dgrad L φ x α * spacetimeGradient ψ x α) =
    ∫ x in K, eulerLagrangeOperator L φ x * ψ x := by
  obtain ⟨h_ibp, h_int_dφ, h_int_grad, h_int_neg⟩ :=
    ibp_per_coordinate_sum L φ ψ K hK hψ hL hφ
  simp only [eulerLagrangeOperator]
  rw [integral_add h_int_dφ h_int_grad, h_ibp]
  rw [show (fun x => (dL_dφ L φ x -
      ∑ α, fderiv ℝ (fun y => dL_dgrad L φ y α) x (Pi.single α 1)) * ψ x) =
      (fun x => dL_dφ L φ x * ψ x +
        ∑ α, (-(fderiv ℝ (fun y => dL_dgrad L φ y α) x (Pi.single α 1))) * ψ x) from by
    ext x; simp [sub_mul, Finset.sum_mul, neg_mul]; ring]
  rw [integral_add h_int_dφ h_int_neg]

/-- First-variation formula: combining the Leibniz/chain rule and the integration by parts,
the first variation of the action equals the $L^2$-pairing of the Euler-Lagrange operator
with the test variation,
$\left. \frac{d}{d\varepsilon} \right|_{\varepsilon = 0} \mathcal{S}_K[\phi + \varepsilon \psi]
= \int_K \mathrm{EL}[\phi](x) \cdot \psi(x) \, dx$. -/
theorem first_variation_expansion {n : ℕ} (L : Lagrangian n)
    (φ : ScalarField n) (K : Set (Spacetime n))
    (hK : IsCompact K) (ψ : ScalarField n) (hψ : IsVariation K ψ)
    (hL : ContDiff ℝ 2 (fun p : ℝ × (Fin (n + 1) → ℝ) × Spacetime n =>
      L p.1 p.2.1 p.2.2))
    (hφ : ContDiff ℝ 2 φ) :
    deriv (fun ε => action L (perturbedField φ ψ ε) K) 0 =
      ∫ x in K, eulerLagrangeOperator L φ x * ψ x := by
  rw [leibniz_chain_rule L φ ψ K hK hL hφ hψ.1]
  exact ibp_euler_lagrange L φ ψ K hK hψ hL hφ

/-- Euler-Lagrange equations: a sufficiently regular field $\phi$ is a stationary point of
the action if and only if it satisfies the Euler-Lagrange equation
$\mathrm{EL}[\phi](x) = \dfrac{\partial L}{\partial \phi}
- \sum_{\alpha} \partial_{\alpha} \!\left( \dfrac{\partial L}{\partial(\partial_{\alpha} \phi)} \right)
= 0$ for all $x$. -/
theorem euler_lagrange_equation {n : ℕ} (L : Lagrangian n)
    (φ : ScalarField n)
    (hL : ContDiff ℝ 2 (fun p : ℝ × (Fin (n + 1) → ℝ) × Spacetime n =>
      L p.1 p.2.1 p.2.2))
    (hφ : ContDiff ℝ 2 φ)
    (hEL_cont : Continuous (eulerLagrangeOperator L φ)) :
    IsStationaryPoint L φ ↔ ∀ x : Spacetime n, eulerLagrangeOperator L φ x = 0 := by
  constructor
  ·


    intro hstat
    apply ibp_fundamental_lemma _ hEL_cont
    intro K hK ψ hψ
    rw [← first_variation_expansion L φ K hK ψ hψ hL hφ]
    exact hstat K hK ψ hψ
  ·
    intro hEL K hK ψ hψ
    rw [first_variation_expansion L φ K hK ψ hψ hL hφ]
    apply MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero
    intro x _
    rw [hEL x]
    ring

end CM17Lagrangian
