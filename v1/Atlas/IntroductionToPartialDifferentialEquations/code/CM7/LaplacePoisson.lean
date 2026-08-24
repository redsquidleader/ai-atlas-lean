/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic
import Atlas.IntroductionToPartialDifferentialEquations.code.CM9.PoissonHarnackLiouville

open Real Set MeasureTheory Filter

noncomputable section

namespace LaplacePoisson

/-- A bounded Lipschitz domain in $\mathbb{R}^n$: an open, bounded, nonempty,
connected set whose boundary can be locally straightened by bi-Lipschitz maps.
This is the natural class of domains for the Poisson Dirichlet problem. -/
structure IsLipschitzDomain {n : ℕ} (Ω : Set (Fin n → ℝ)) : Prop where
  isOpen : IsOpen Ω
  isBounded : Bornology.IsBounded Ω
  nonempty : Set.Nonempty Ω
  isConnected : IsConnected Ω
  frontier_nonempty : Set.Nonempty (frontier Ω)
  lipschitz_boundary : ∀ x ∈ frontier Ω, ∃ (U : Set (Fin n → ℝ)),
    IsOpen U ∧ x ∈ U ∧
    ∃ (φ : (Fin n → ℝ) → (Fin n → ℝ)),
      LipschitzWith 1 φ ∧
      ∃ (ψ : (Fin n → ℝ) → (Fin n → ℝ)),
        LipschitzWith 1 ψ ∧
        (∀ y ∈ U, ψ (φ y) = y) ∧ (∀ z ∈ φ '' U, φ (ψ z) = z)

/-- Euclidean norm on $\mathbb{R}^n$ written as $|x| = \sqrt{\sum_i (x^i)^2}$,
for vectors represented as `Fin n → ℝ` (the `LP` suffix marks the L^p-style
function space presentation). -/
def euclidNormLP {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

/-- The Euclidean norm is invariant under negation: $|-x| = |x|$. -/
lemma euclidNormLP_neg {n : ℕ} (x : Fin n → ℝ) : euclidNormLP (-x) = euclidNormLP x := by
  unfold euclidNormLP
  congr 1; congr 1; ext i; simp

/-- The custom `euclidNormLP` agrees with the Mathlib L^2 norm on `Fin n → ℝ`
via the `WithLp 2` equivalence. -/
lemma euclidNormLP_eq_norm_withLp {n : ℕ} (v : Fin n → ℝ) :
    euclidNormLP v = ‖(WithLp.equiv 2 (Fin n → ℝ)).symm v‖ := by
  unfold euclidNormLP
  rw [EuclideanSpace.norm_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [WithLp.equiv_symm_apply_ofLp]
  simp [sq_abs]

/-- The Euclidean norm is nonnegative: $|x| \ge 0$. -/
lemma euclidNormLP_nonneg {n : ℕ} (x : Fin n → ℝ) : euclidNormLP x ≥ 0 := by
  unfold euclidNormLP
  exact Real.sqrt_nonneg _

/-- Reverse triangle inequality for the Euclidean norm: $|a| - |b| \le |a - b|$. -/
lemma euclidNormLP_sub_le {n : ℕ} (a b : Fin n → ℝ) :
    euclidNormLP a - euclidNormLP b ≤ euclidNormLP (a - b) := by
  rw [euclidNormLP_eq_norm_withLp a, euclidNormLP_eq_norm_withLp b,
      euclidNormLP_eq_norm_withLp (a - b)]
  have h : (WithLp.equiv 2 (Fin n → ℝ)).symm (a - b) =
      (WithLp.equiv 2 (Fin n → ℝ)).symm a - (WithLp.equiv 2 (Fin n → ℝ)).symm b := by
    ext i
    simp
  rw [h]
  exact norm_sub_norm_le _ _

/-- Surface area $\omega_n$ of the unit sphere in $\mathbb{R}^n$,
defined via the Gamma function: $\omega_n = 2\pi^{n/2}/\Gamma(n/2)$ for $n \ge 1$.
For example $\omega_3 = 4\pi$. The convention $\omega_0 = 1$ is taken here. -/
def unitSphereArea (n : ℕ) : ℝ :=
  if n = 0 then 1 else 2 * Real.pi ^ ((n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2)

/-- The unit sphere area $\omega_n$ is strictly positive for every $n$. -/
theorem unitSphereArea_pos : ∀ n, unitSphereArea n > 0 := by
  intro n
  unfold unitSphereArea
  split
  · norm_num
  · rename_i hn
    apply div_pos
    · apply mul_pos (by norm_num : (2:ℝ) > 0)
      exact Real.rpow_pos_of_pos Real.pi_pos ((n : ℝ) / 2)
    · apply Real.Gamma_pos_of_pos
      apply div_pos
      · exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      · norm_num

/-- Classical formula: the area of the unit $2$-sphere in $\mathbb{R}^3$
is $\omega_3 = 4\pi$. -/
theorem unitSphereArea_three : unitSphereArea 3 = 4 * Real.pi := by
  unfold unitSphereArea; simp
  have hG32 : Real.Gamma (3 / 2 : ℝ) = (1 / 2) * Real.Gamma (1 / 2) := by
    have h := Real.Gamma_add_one (s := (1:ℝ)/2) (by norm_num)
    linarith
  have hG12 : Real.Gamma (1 / 2 : ℝ) = Real.sqrt Real.pi := Real.Gamma_one_half_eq
  have hsqrt : Real.sqrt Real.pi = Real.pi ^ ((1:ℝ)/2) := Real.sqrt_eq_rpow Real.pi
  have hpow : Real.pi ^ ((3:ℝ)/2) = Real.pi * Real.pi ^ ((1:ℝ)/2) := by
    rw [show (3:ℝ)/2 = 1 + 1/2 from by ring]
    rw [Real.rpow_add Real.pi_pos]
    rw [Real.rpow_one]
  rw [hG32, hG12, hsqrt, hpow]
  have hpi12_ne : Real.pi ^ ((1:ℝ)/2) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)
  field_simp
  ring

/-- The fundamental solution $\Phi$ for the Laplacian $\Delta$ in $\mathbb{R}^n$
(Definition 1.0.1 of CM7):
$\Phi(x) = \frac{1}{2\pi} \ln|x|$ for $n=2$, and
$\Phi(x) = -\frac{1}{\omega_n |x|^{n-2}}$ for $n \ge 3$,
where $\omega_n$ is the surface area of the unit sphere in $\mathbb{R}^n$. -/
def fundamentalSolution (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  if n = 2 then
    (1 / (2 * Real.pi)) * Real.log (euclidNormLP x)
  else
    -1 / (unitSphereArea n * (euclidNormLP x) ^ (n - 2))

/-- The fundamental solution is radially symmetric: $\Phi(-x) = \Phi(x)$. -/
lemma fundamentalSolution_neg {n : ℕ} (x : Fin n → ℝ) :
    fundamentalSolution n (-x) = fundamentalSolution n x := by
  unfold fundamentalSolution
  rw [euclidNormLP_neg]

/-- The Laplacian $\Delta f(x) = \sum_{i=1}^n \partial_i^2 f(x)$ on $\mathbb{R}^n$,
expressed in terms of `fderiv` applied twice in coordinate directions. -/
def laplacianLP {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n,
    fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single i 1)

/-- A function $u$ is harmonic on $\Omega$ when $\Delta u = 0$ pointwise on $\Omega$. -/
def IsHarmonicLP {n : ℕ} (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ)) : Prop :=
  ∀ x ∈ Ω, laplacianLP u x = 0

/-- Convolution of the fundamental solution with $f$:
$(\Phi * f)(x) = \int_{\mathbb{R}^n} \Phi(x - y)\,f(y)\,d^n y$.
This is the candidate solution of $\Delta u = f$ in Theorem 1.1 of CM7. -/
def phiConvolutionLP (n : ℕ) (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ y : Fin n → ℝ, fundamentalSolution n (x - y) * f y

/-- Outward unit normal vector field on the boundary of $\Omega \subset \mathbb{R}^n$,
treated abstractly via an opaque declaration. -/
opaque outwardUnitNormal {n : ℕ} (Ω : Set (Fin n → ℝ)) : (Fin n → ℝ) → (Fin n → ℝ)

/-- The $(n-1)$-dimensional surface (Hausdorff) measure attached to the boundary
of $\Omega$, treated abstractly via an opaque declaration. -/
opaque surfaceMeasure {n : ℕ} (Ω : Set (Fin n → ℝ)) : Measure (Fin n → ℝ)

/-- The outward unit normal is zero off the boundary of $\Omega$. -/
theorem outwardUnitNormal_zero_off_frontier {n : ℕ} (Ω : Set (Fin n → ℝ))
    (σ : Fin n → ℝ) (hσ : σ ∉ frontier Ω) :
    outwardUnitNormal Ω σ = 0 := by sorry

/-- Each component of the outward unit normal has absolute value at most $1$. -/
theorem outwardUnitNormal_component_le_one {n : ℕ} (Ω : Set (Fin n → ℝ))
    (σ : Fin n → ℝ) (i : Fin n) :
    |outwardUnitNormal Ω σ i| ≤ 1 := by sorry

/-- A $C^2$ function on the closure of a bounded set has uniformly bounded
Fréchet derivative on that closure. -/
theorem fderiv_bounded_on_compact_closure {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω))
    (hΩb : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ closure Ω, ‖fderiv ℝ u σ‖ ≤ C := by sorry

/-- Outer normal derivative $\partial_\nu f(\sigma) = \nabla f(\sigma) \cdot \nu(\sigma)$
on the boundary of $\Omega$. -/
def normalDerivLP {n : ℕ} (Ω : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (σ : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, fderiv ℝ f σ (Pi.single i 1) * outwardUnitNormal Ω σ i

/-- Surface integral $\int_{\partial \Omega} f \, dS$ of $f$ over the boundary
of $\Omega$ with respect to the surface measure. -/
def surfaceIntegralLP {n : ℕ} (Ω : Set (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ σ in frontier Ω, f σ ∂(surfaceMeasure Ω)

/-- On the inner sphere $|z| = \varepsilon$ bounding the exterior region
$\{|z| \ge \varepsilon\}$, the outward unit normal points toward the origin:
$\nu_i(\sigma) = -\sigma_i / |\sigma|$. -/
theorem outwardUnitNormal_exterior_sphere_spec {n : ℕ} (ε : ℝ) (hε : 0 < ε)
    (σ : Fin n → ℝ) (hσ : euclidNormLP σ = ε) (i : Fin n) :
    outwardUnitNormal {z : Fin n → ℝ | euclidNormLP z ≥ ε} σ i = -(σ i) / euclidNormLP σ := by sorry

/-- Pointwise computation: the inward normal derivative of $\Phi$ on the sphere
$|\sigma| = \varepsilon$ equals the constant $-1/(\omega_n \varepsilon^{n-1})$
(here $n \ge 3$). -/
theorem pointwise_normalDerivLP_fundamentalSolution_on_sphere {n : ℕ} (hn : n ≥ 3)
    (ε : ℝ) (hε : 0 < ε) (σ : Fin n → ℝ) (hσ : euclidNormLP σ = ε) :
    normalDerivLP {z : Fin n → ℝ | euclidNormLP z ≥ ε} (fundamentalSolution n) σ =
      -1 / (unitSphereArea n * ε ^ (n - 1)) := by sorry

/-- Almost-everywhere version of the pointwise computation: on the boundary of
$\{|z| = \varepsilon\}$ the normal derivative of $\Phi$ is constantly
$-1/(\omega_n \varepsilon^{n-1})$ with respect to surface measure. -/
theorem normalDerivLP_fundamentalSolution_sphere_ae {n : ℕ} (hn : n ≥ 3) (ε : ℝ) (hε : 0 < ε) :
    (fun σ => normalDerivLP {z | euclidNormLP z ≥ ε} (fundamentalSolution n) σ) =ᵐ[
      (surfaceMeasure {z : Fin n → ℝ | euclidNormLP z = ε}).restrict
        (frontier {z : Fin n → ℝ | euclidNormLP z = ε})]
    (fun _ => -1 / (unitSphereArea n * ε ^ (n - 1))) := by


  have hcont_norm : Continuous (fun x : Fin n → ℝ => euclidNormLP x) :=
    Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => (continuous_apply i).pow 2)
  have hclosed : IsClosed {z : Fin n → ℝ | euclidNormLP z = ε} :=
    isClosed_eq hcont_norm continuous_const
  have hfrontier_sub : frontier {z : Fin n → ℝ | euclidNormLP z = ε} ⊆
      {z : Fin n → ℝ | euclidNormLP z = ε} :=
    frontier_subset_closure.trans hclosed.closure_eq.subset


  apply Filter.Eventually.mono (ae_restrict_mem measurableSet_frontier)
  intro σ hσ
  exact pointwise_normalDerivLP_fundamentalSolution_on_sphere hn ε hε σ (hfrontier_sub hσ)

/-- The total surface measure of the sphere $\{|z| = \varepsilon\}$ in
$\mathbb{R}^n$ equals $\omega_n \varepsilon^{n-1}$. -/
theorem surfaceMeasure_sphere_measureReal {n : ℕ} (hn : n ≥ 3) (ε : ℝ) (hε : 0 < ε) :
    (surfaceMeasure {z : Fin n → ℝ | euclidNormLP z = ε}).real
        (frontier {z : Fin n → ℝ | euclidNormLP z = ε}) =
      unitSphereArea n * ε ^ (n - 1) := by sorry

/-- The Fréchet derivative of $y \mapsto \sum_j y_j^2$ at $x$ is the linear
functional $v \mapsto \sum_j 2 x_j \, v_j$. -/
lemma hasFDerivAt_sum_sq {n : ℕ} (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => ∑ j : Fin n, y j ^ 2)
      (∑ j : Fin n, (2 * x j) •
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j))
      x := by
  have hfderiv : ∀ j ∈ Finset.univ, HasFDerivAt (fun y : Fin n → ℝ => y j ^ 2)
      ((2 * x j) •
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j)) x := by
    intro j _
    convert (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin n => ℝ) j).hasFDerivAt.pow 2 using 1
    ext v; simp [mul_comm, smul_eq_mul]
  convert HasFDerivAt.sum hfderiv using 1; ext y; simp [Finset.sum_apply]

/-- If $x \ne 0$ in $\mathbb{R}^n$ then $\sum_j x_j^2 > 0$. -/
lemma sum_sq_pos_of_ne_zero {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) :
    ∑ j : Fin n, x j ^ 2 > 0 := by
  have : ∃ i, x i ≠ 0 := by by_contra h; push Not at h; exact hx (funext h)
  obtain ⟨i, hi⟩ := this
  calc ∑ j, x j ^ 2
      ≥ x i ^ 2 := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    _ > 0 := by positivity

/-- Away from the origin the Euclidean norm is differentiable; its Fréchet
derivative is computed via the chain rule from $|x| = \sqrt{\sum_j x_j^2}$. -/
lemma hasFDerivAt_euclidNormLP {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) :
    HasFDerivAt (euclidNormLP (n := n))
      ((1 / (2 * euclidNormLP x)) •
        (∑ j : Fin n, (2 * x j) •
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) j)))
      x := by
  unfold euclidNormLP
  exact (hasFDerivAt_sum_sq x).sqrt (ne_of_gt (sum_sq_pos_of_ne_zero x hx))

/-- The Euclidean norm is strictly positive at nonzero points: $x \ne 0 \Rightarrow |x| > 0$. -/
theorem euclidNormLP_pos {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) : euclidNormLP x > 0 := by
  unfold euclidNormLP
  apply Real.sqrt_pos_of_pos
  have : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  obtain ⟨i, hi⟩ := this
  calc ∑ j, x j ^ 2 ≥ x i ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    _ > 0 := by positivity

/-- Near a nonzero point $x$, the $i$-th partial derivative of a radial
function $g(|z|)$ equals $g'(|y|)\,(y_i/|y|)$ by the chain rule. -/
lemma first_partial_eq_near {n : ℕ} (g : ℝ → ℝ) (hg : ContDiffOn ℝ 2 g (Set.Ioi 0))
    (x : Fin n → ℝ) (hx : x ≠ 0) (i : Fin n) :
    (fun y => fderiv ℝ (fun z => g (euclidNormLP z)) y (Pi.single i 1)) =ᶠ[nhds x]
    (fun y => fderiv ℝ g (euclidNormLP y) 1 * (y i / euclidNormLP y)) := by
  apply Filter.eventuallyEq_iff_exists_mem.mpr
  refine ⟨{y | y ≠ 0}, isOpen_ne.mem_nhds hx, fun y hy => ?_⟩
  have hr_pos : euclidNormLP y > 0 := euclidNormLP_pos y hy
  have hg_diff : DifferentiableAt ℝ g (euclidNormLP y) :=
    (hg.differentiableOn two_ne_zero).differentiableAt (Ioi_mem_nhds hr_pos)
  have hchain := hg_diff.hasFDerivAt.comp y (hasFDerivAt_euclidNormLP y hy)
  show fderiv ℝ (fun z => g (euclidNormLP z)) y (Pi.single i 1) = _
  change fderiv ℝ (g ∘ euclidNormLP) y (Pi.single i 1) = _
  rw [hchain.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_eq_mul, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.proj_apply,
    Pi.single_apply]
  have harg : 1 / (2 * euclidNormLP y) * ∑ x : Fin n, 2 * y x * (if x = i then (1 : ℝ) else 0)
      = y i / euclidNormLP y := by
    simp [Finset.sum_ite_eq', Finset.mem_univ]; field_simp
  rw [harg]
  have : (fderiv ℝ g (euclidNormLP y)) (y i / euclidNormLP y) =
      (y i / euclidNormLP y) * (fderiv ℝ g (euclidNormLP y)) 1 := by
    conv_lhs => rw [show y i / euclidNormLP y = (y i / euclidNormLP y) • (1 : ℝ) from by simp]
    rw [map_smul, smul_eq_mul]
  rw [this, mul_comm]

/-- Away from the origin, the function $y \mapsto y_i / |y|$ is differentiable. -/
lemma differentiableAt_coord_over_norm {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) (i : Fin n) :
    DifferentiableAt ℝ (fun y : Fin n → ℝ => y i / euclidNormLP y) x := by
  have : (fun y : Fin n → ℝ => y i / euclidNormLP y) = (fun y => y i * (euclidNormLP y)⁻¹) := by
    ext y; rw [div_eq_mul_inv]
  rw [this]
  exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).differentiableAt).mul
    ((hasFDerivAt_euclidNormLP x hx).differentiableAt.inv (ne_of_gt (euclidNormLP_pos x hx)))

/-- The partial derivative of $y \mapsto y_i/|y|$ in the direction $e_i$ is
$\partial_i (y_i/|y|) = 1/|y| - y_i^2 / |y|^3$ at points $x \ne 0$. -/
lemma fderiv_coord_over_norm_single {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) (i : Fin n) :
    fderiv ℝ (fun y : Fin n → ℝ => y i / euclidNormLP y) x (Pi.single i 1) =
    1 / euclidNormLP x - x i ^ 2 / euclidNormLP x ^ 3 := by
  have hr_ne : euclidNormLP x ≠ 0 := ne_of_gt (euclidNormLP_pos x hx)
  have heq : (fun y : Fin n → ℝ => y i / euclidNormLP y) =
      (fun y => y i * (euclidNormLP y)⁻¹) := by ext y; rw [div_eq_mul_inv]
  rw [heq]
  have h1 : DifferentiableAt ℝ (fun y : Fin n → ℝ => y i) x :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).differentiableAt
  have h2 : DifferentiableAt ℝ (fun y : Fin n → ℝ => (euclidNormLP y)⁻¹) x :=
    ((hasFDerivAt_euclidNormLP x hx).differentiableAt).inv hr_ne
  rw [fderiv_fun_mul h1 h2]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hproj : fderiv ℝ (fun y : Fin n → ℝ => y i) x (Pi.single i 1) = 1 := by
    have : (fun y : Fin n → ℝ => y i) =
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i) := rfl
    rw [this, ContinuousLinearMap.fderiv]; simp
  rw [hproj]
  rw [show fderiv ℝ (fun y : Fin n → ℝ => (euclidNormLP y)⁻¹) x =
      fderiv ℝ (Inv.inv ∘ euclidNormLP) x from rfl,
    ((hasFDerivAt_inv' (𝕜 := ℝ) hr_ne).comp x (hasFDerivAt_euclidNormLP x hx)).fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, smul_eq_mul, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.proj_apply,
    Pi.single_apply]
  simp [Finset.sum_ite_eq', Finset.mem_univ]
  field_simp
  ring

/-- Away from the origin, $y \mapsto g'(|y|)$ is differentiable for $g \in C^2$
on $(0, \infty)$. -/
lemma differentiableAt_gprime_comp_norm {n : ℕ} (g : ℝ → ℝ) (hg : ContDiffOn ℝ 2 g (Set.Ioi 0))
    (x : Fin n → ℝ) (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun y : Fin n → ℝ => fderiv ℝ g (euclidNormLP y) 1) x := by
  have hfderiv_cd : ContDiffOn ℝ 1 (fderiv ℝ g) (Set.Ioi 0) :=
    hg.fderiv_of_isOpen isOpen_Ioi (by norm_cast)
  have hfderiv_diff : DifferentiableOn ℝ (fderiv ℝ g) (Set.Ioi 0) :=
    hfderiv_cd.differentiableOn one_ne_zero
  have hphi_diff : DifferentiableOn ℝ (fun s => fderiv ℝ g s 1) (Set.Ioi 0) :=
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).differentiable.comp_differentiableOn hfderiv_diff
  exact (hphi_diff.differentiableAt (Ioi_mem_nhds (euclidNormLP_pos x hx))).comp x
    (hasFDerivAt_euclidNormLP x hx).differentiableAt

/-- Chain rule for $\partial_i [g'(|y|)] = g''(|y|) \, (y_i / |y|)$ at $x \ne 0$. -/
lemma fderiv_gprime_comp_norm_single {n : ℕ} (g : ℝ → ℝ) (hg : ContDiffOn ℝ 2 g (Set.Ioi 0))
    (x : Fin n → ℝ) (hx : x ≠ 0) (i : Fin n) :
    fderiv ℝ (fun y : Fin n → ℝ => fderiv ℝ g (euclidNormLP y) 1) x (Pi.single i 1) =
    fderiv ℝ (fun s => fderiv ℝ g s 1) (euclidNormLP x) 1 * (x i / euclidNormLP x) := by
  set phi := (fun s : ℝ => fderiv ℝ g s 1) with hphi_def
  have hfderiv_cd : ContDiffOn ℝ 1 (fderiv ℝ g) (Set.Ioi 0) :=
    hg.fderiv_of_isOpen isOpen_Ioi (by norm_cast)
  have hfderiv_diff : DifferentiableOn ℝ (fderiv ℝ g) (Set.Ioi 0) :=
    hfderiv_cd.differentiableOn one_ne_zero
  have hphi_diff : DifferentiableOn ℝ phi (Set.Ioi 0) :=
    (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)).differentiable.comp_differentiableOn hfderiv_diff
  have hphi_diffAt : DifferentiableAt ℝ phi (euclidNormLP x) :=
    hphi_diff.differentiableAt (Ioi_mem_nhds (euclidNormLP_pos x hx))
  have hchain := hphi_diffAt.hasFDerivAt.comp x (hasFDerivAt_euclidNormLP x hx)
  show fderiv ℝ (fun y => phi (euclidNormLP y)) x (Pi.single i 1) = _
  change fderiv ℝ (phi ∘ euclidNormLP) x (Pi.single i 1) = _
  rw [hchain.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, Pi.single_apply]
  simp [Finset.sum_ite_eq', Finset.mem_univ]
  have hr_ne : euclidNormLP x ≠ 0 := ne_of_gt (euclidNormLP_pos x hx)
  field_simp

/-- Second partial derivative of a radial function:
$\partial_i^2 [g(|x|)] = g''(|x|) (x_i/|x|)^2 + g'(|x|)(1/|x| - x_i^2/|x|^3)$
at points $x \ne 0$. -/
theorem axm_second_partial_comp_norm {n : ℕ} (g : ℝ → ℝ) (hg : ContDiffOn ℝ 2 g (Set.Ioi 0))
    (x : Fin n → ℝ) (hx : x ≠ 0) (i : Fin n) :
    let r := euclidNormLP x
    fderiv ℝ (fun y => fderiv ℝ (fun z => g (euclidNormLP z)) y (Pi.single i 1)) x (Pi.single i 1) =
      fderiv ℝ (fun s => fderiv ℝ g s 1) r 1 * (x i / r) ^ 2 +
      fderiv ℝ g r 1 * (1 / r - x i ^ 2 / r ^ 3) := by
  intro r

  rw [(first_partial_eq_near g hg x hx i).fderiv_eq]

  rw [fderiv_fun_mul (differentiableAt_gprime_comp_norm g hg x hx)
    (differentiableAt_coord_over_norm x hx i)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

  rw [fderiv_gprime_comp_norm_single g hg x hx i,
      fderiv_coord_over_norm_single x hx i]

  ring

/-- The Euclidean norm $x \mapsto |x|$ is continuous on $\mathbb{R}^n$. -/
lemma continuous_euclidNormLP {n : ℕ} : Continuous (fun x : Fin n → ℝ => euclidNormLP x) := by
  unfold euclidNormLP
  exact Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => (continuous_apply i).pow 2)

/-- The squared components of the unit vector $x/|x|$ sum to $1$:
$\sum_i (x_i/|x|)^2 = 1$ for $x \ne 0$. -/
lemma norm_sum_div_sq {n : ℕ} (x : Fin n → ℝ) (hx : x ≠ 0) :
    ∑ i : Fin n, (x i / euclidNormLP x) ^ 2 = 1 := by
  have hr := euclidNormLP_pos x hx
  have hr_ne : euclidNormLP x ≠ 0 := ne_of_gt hr
  simp_rw [div_pow]
  rw [← Finset.sum_div]
  have : ∑ i : Fin n, x i ^ 2 = (euclidNormLP x) ^ 2 := by
    unfold euclidNormLP
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i))]
  rw [this, div_self (pow_ne_zero 2 hr_ne)]

/-- Radial form of the Laplacian: for a radial function $u(x) = g(|x|)$ in
$\mathbb{R}^n$ with $n \ge 2$ and $x \ne 0$,
$\Delta u(x) = g''(r) + \frac{n-1}{r} g'(r)$ where $r = |x|$. -/
theorem spherical_laplacian_identity {n : ℕ} (hn : n ≥ 2)
    (g : ℝ → ℝ) (hg : ContDiffOn ℝ 2 g (Set.Ioi 0))
    (x : Fin n → ℝ) (hx : x ≠ 0) :
    let r := euclidNormLP x
    laplacianLP (fun y => g (euclidNormLP y)) x =
      fderiv ℝ (fun s => fderiv ℝ g s 1) r 1 + (↑(n - 1) / r) * fderiv ℝ g r 1 := by
  simp only
  set r := euclidNormLP x with hr_def
  have hr := euclidNormLP_pos x hx
  have hr_ne : r ≠ 0 := ne_of_gt hr

  unfold laplacianLP

  simp_rw [axm_second_partial_comp_norm g hg x hx]

  rw [Finset.sum_add_distrib]

  rw [← Finset.mul_sum, norm_sum_div_sq x hx, mul_one]

  rw [← Finset.mul_sum]

  suffices h : ∑ i : Fin n, (1 / r - x i ^ 2 / r ^ 3) = ↑(n - 1) / r by
    rw [h]; ring

  have h1 : ∀ i : Fin n, (1 / r - x i ^ 2 / r ^ 3) = (r ^ 2 - x i ^ 2) / r ^ 3 := by
    intro i; field_simp
  simp_rw [h1]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]

  have hr2 : ∑ i : Fin n, x i ^ 2 = r ^ 2 := by
    rw [hr_def]; unfold euclidNormLP
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (x i))]
  rw [hr2]

  have h_cast : (↑(n - 1) : ℝ) = ↑n - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_cast
  rw [h_cast]
  field_simp

/-- For $n \ge 3$, the radial profile $r \mapsto -1/(\omega_n r^{n-2})$ of the
fundamental solution is $C^2$ on $(0, \infty)$. -/
theorem radial_fundamental_smooth (n : ℕ) (_hn : n ≥ 3) :
    ContDiffOn ℝ 2 (fun r : ℝ => -1 / (unitSphereArea n * r ^ (n - 2))) (Set.Ioi 0) := by
  set k := n - 2
  set ω := unitSphereArea n
  have hω_ne : ω ≠ 0 := ne_of_gt (unitSphereArea_pos n)
  have hfun_eq : (fun r : ℝ => -1 / (ω * r ^ k)) = (fun r => (-1 / ω) * (r ^ k)⁻¹) := by
    funext r; field_simp
  rw [hfun_eq]
  exact (ContDiffOn.inv (contDiff_id.pow k).contDiffOn
    (fun x hx => pow_ne_zero k (ne_of_gt hx))).const_smul (-1 / ω)

/-- First derivative of the radial profile of $\Phi$ for $n \ge 3$:
$\frac{d}{dr}\!\left(-\frac{1}{\omega_n r^{n-2}}\right) = \frac{n-2}{\omega_n r^{n-1}}$. -/
theorem power_radial_first_deriv (n : ℕ) (hn : n ≥ 3) (r : ℝ) (hr : r > 0) :
    fderiv ℝ (fun s : ℝ => -1 / (unitSphereArea n * s ^ (n - 2))) r 1 =
      (↑(n - 2) : ℝ) / (unitSphereArea n * r ^ (n - 1)) := by
  rw [fderiv_apply_one_eq_deriv]
  set k := n - 2 with hk_def
  set ω := unitSphereArea n with hω_def
  have hω_ne : ω ≠ 0 := ne_of_gt (unitSphereArea_pos n)
  have hr_ne : r ≠ 0 := ne_of_gt hr
  have hk1 : k + 1 = n - 1 := by omega
  have hfun_eq : (fun s : ℝ => -1 / (ω * s ^ k)) = (fun s => (-1/ω) * s ^ (-(k : ℤ))) := by
    funext s; simp [zpow_neg, zpow_natCast, div_eq_mul_inv]; ring
  rw [hfun_eq, (hasDerivAt_zpow (-(k : ℤ)) r (Or.inl hr_ne)).const_mul (-1/ω) |>.deriv]
  simp only [Int.cast_neg, Int.cast_natCast]
  rw [show -(k : ℤ) - 1 = -((k : ℤ) + 1) from by ring, zpow_neg,
      show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) from by push_cast; ring,
      zpow_natCast, hk1]
  field_simp

/-- Second derivative of the radial profile of $\Phi$ for $n \ge 3$:
$\frac{d^2}{dr^2}\!\left(-\frac{1}{\omega_n r^{n-2}}\right) =
-\frac{(n-2)(n-1)}{\omega_n r^n}$. -/
theorem power_radial_second_deriv (n : ℕ) (hn : n ≥ 3) (r : ℝ) (hr : r > 0) :
    fderiv ℝ (fun s => fderiv ℝ (fun t : ℝ => -1 / (unitSphereArea n * t ^ (n - 2))) s 1) r 1 =
      -(↑(n - 2) : ℝ) * (↑(n - 1) : ℝ) / (unitSphereArea n * r ^ n) := by
  set k := n - 2 with hk_def
  set ω := unitSphereArea n with hω_def
  have hω_ne : ω ≠ 0 := ne_of_gt (unitSphereArea_pos n)
  have hr_ne : r ≠ 0 := ne_of_gt hr
  have hk1 : k + 1 = n - 1 := by omega
  have hk2 : k + 2 = n := by omega
  have heq : (fun s => fderiv ℝ (fun t : ℝ => -1 / (ω * t ^ k)) s 1) =
    (fun s => deriv (fun t : ℝ => -1 / (ω * t ^ k)) s) := by
    ext s; exact fderiv_apply_one_eq_deriv
  rw [heq, fderiv_apply_one_eq_deriv]
  have hfun_eq : (fun s : ℝ => -1 / (ω * s ^ k)) = (fun s => (-1/ω) * s ^ (-(k : ℤ))) := by
    funext s; simp [zpow_neg, zpow_natCast, div_eq_mul_inv]; ring
  have hderiv_eq : ∀ᶠ s in nhds r, deriv (fun t : ℝ => -1 / (ω * t ^ k)) s =
      (↑k / ω) * s ^ (-((k : ℤ) + 1)) := by
    filter_upwards [eventually_gt_nhds (by linarith : (0 : ℝ) < r)] with s hs
    rw [hfun_eq, (hasDerivAt_zpow (-(k : ℤ)) s (Or.inl (ne_of_gt hs))).const_mul (-1/ω) |>.deriv]
    simp only [Int.cast_neg, Int.cast_natCast]
    rw [show -(k : ℤ) - 1 = -((k : ℤ) + 1) from by ring]
    field_simp
  rw [Filter.EventuallyEq.deriv_eq hderiv_eq,
      (hasDerivAt_zpow (-((k : ℤ) + 1)) r (Or.inl hr_ne)).const_mul (↑k / ω) |>.deriv]
  simp only [Int.cast_neg, Int.cast_add, Int.cast_natCast, Int.cast_one]
  rw [show -((k : ℤ) + 1) - 1 = -(((k : ℤ) + 1) + 1) from by ring, zpow_neg,
      show ((k : ℤ) + 1) + 1 = ((k + 2 : ℕ) : ℤ) from by push_cast; ring,
      zpow_natCast, hk2]
  have : (k : ℝ) + 1 = ↑(n - 1) := by rw [← hk1]; push_cast; ring
  rw [this]; field_simp

/-- Lemma 1.0.1 of CM7: the fundamental solution is harmonic away from the
origin. That is, $\Delta \Phi(x) = 0$ for $x \ne 0$ (here $n \ge 3$). -/
theorem fundamental_solution_harmonic_away {n : ℕ} (hn : n ≥ 3)
    (x : Fin n → ℝ) (hx : x ≠ 0) :
    laplacianLP (fundamentalSolution n) x = 0 := by

  have hn2 : n ≠ 2 := by omega
  let g : ℝ → ℝ := fun s => -1 / (unitSphereArea n * s ^ (n - 2))
  have hfg : fundamentalSolution n = fun y => g (euclidNormLP y) := by
    ext y; simp only [fundamentalSolution, hn2, ite_false, g]
  rw [hfg]

  have hn2' : n ≥ 2 := by omega
  have hg_smooth := radial_fundamental_smooth n hn
  rw [spherical_laplacian_identity hn2' g hg_smooth x hx]

  have hr := euclidNormLP_pos x hx
  rw [power_radial_second_deriv n hn (euclidNormLP x) hr,
      power_radial_first_deriv n hn (euclidNormLP x) hr]

  set r := euclidNormLP x
  have h1 : r * r ^ (n - 1) = r ^ n := by
    calc r * r ^ (n - 1) = r ^ 1 * r ^ (n - 1) := by ring
      _ = r ^ (1 + (n - 1)) := by rw [pow_add]
      _ = r ^ n := by congr 1; omega
  have key : (↑(n - 1) : ℝ) / r * ((↑(n - 2) : ℝ) / (unitSphereArea n * r ^ (n - 1))) =
    (↑(n - 2) : ℝ) * (↑(n - 1) : ℝ) / (unitSphereArea n * (r * r ^ (n - 1))) := by ring
  rw [key, h1]
  ring

/-- Green's second identity for sufficiently regular $u, v$ on a bounded open
$\Omega$: $\int_\Omega (v \Delta u - u \Delta v) = \int_{\partial \Omega}
(v \, \partial_\nu u - u \, \partial_\nu v)\,dS$. -/
theorem greens_second_identity {n : ℕ}
    (Ω : Set (Fin n → ℝ)) (u v : (Fin n → ℝ) → ℝ)
    (hu : ContDiffOn ℝ 2 u (closure Ω)) (hv : ContDiffOn ℝ 2 v (closure Ω))
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) :
    (∫ x in Ω, v x * laplacianLP u x - u x * laplacianLP v x) =
      surfaceIntegralLP Ω (fun σ => v σ * normalDerivLP Ω u σ - u σ * normalDerivLP Ω v σ) := by sorry

/-- Differentiation under the integral sign: the Laplacian commutes with the
$\Phi$-convolution against a smooth compactly supported $f$. -/
theorem leibniz_laplacian_under_integral {n : ℕ} (_hn : n ≥ 3)
    (f : (Fin n → ℝ) → ℝ)
    (_hf_smooth : ContDiff ℝ ⊤ f) (_hf_supp : HasCompactSupport f)
    (x : Fin n → ℝ) :
    laplacianLP (fun x' => ∫ y, fundamentalSolution n y * f (x' - y)) x =
      ∫ y, fundamentalSolution n y * laplacianLP (fun x' => f (x' - y)) x := by sorry

/-- Substitution $y \mapsto x - y$ in the convolution integral:
$\int \Phi(x - y) f(y)\,dy = \int \Phi(y) f(x - y)\,dy$. -/
theorem convolution_substitution {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    (∫ y, fundamentalSolution n (x - y) * f y) =
      ∫ y, fundamentalSolution n y * f (x - y) := by
  have key : ∀ y : Fin n → ℝ,
    fundamentalSolution n (x - y) * f y =
    (fun z => fundamentalSolution n z * f (x - z)) (x - y) := by
    intro y; simp [sub_sub_cancel]
  simp_rw [key]
  exact MeasureTheory.integral_sub_left_eq_self
    (fun z : Fin n → ℝ => fundamentalSolution n z * f (x - z))
    (volume : Measure (Fin n → ℝ)) x

/-- Chain rule for $z \mapsto g(x - z)$: its derivative at $z'$ is the negative
of the derivative of $g$ at $x - z'$. -/
lemma fderiv_comp_const_sub_LP {n : ℕ} (g : (Fin n → ℝ) → ℝ) (x z' : Fin n → ℝ)
    (hg : DifferentiableAt ℝ g (x - z')) :
    fderiv ℝ (fun z => g (x - z)) z' = -(fderiv ℝ g (x - z')) := by
  rw [show (fun z => g (x - z)) = g ∘ (fun z => x - z) from rfl,
      fderiv_comp z' hg ((differentiableAt_const x).sub differentiableAt_id)]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply]
  have : fderiv ℝ (fun z : Fin n → ℝ => x - z) z' = -ContinuousLinearMap.id ℝ _ := by
    rw [fderiv_const_sub x]; simp
  rw [this]; simp

/-- Variable swap for the Laplacian under translation: the Laplacian of
$x' \mapsto f(x' - y)$ at $x$ equals the Laplacian of $z \mapsto f(x - z)$ at $y$,
since each equals $\Delta f(x - y)$. -/
theorem laplacianLP_chain_rule_sub {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (_hf : ContDiff ℝ ⊤ f)
    (x y : Fin n → ℝ) :
    laplacianLP (fun x' => f (x' - y)) x = laplacianLP (fun z => f (x - z)) y := by


  suffices h_lhs : laplacianLP (fun x' => f (x' - y)) x = laplacianLP f (x - y) by
    suffices h_rhs : laplacianLP (fun z => f (x - z)) y = laplacianLP f (x - y) by
      rw [h_lhs, h_rhs]

    unfold laplacianLP
    congr 1; ext i
    have hf_diff : ∀ z', DifferentiableAt ℝ f (x - z') :=
      fun z' => (_hf.differentiable WithTop.top_ne_zero).differentiableAt
    have h_func_eq : (fun z' => fderiv ℝ (fun z => f (x - z)) z' (Pi.single i 1))
      = (fun z' => -(fderiv ℝ f (x - z') (Pi.single i 1))) := by
      ext z'; rw [fderiv_comp_const_sub_LP f x z' (hf_diff z')]; simp
    rw [h_func_eq, fderiv_fun_neg]
    simp only [ContinuousLinearMap.neg_apply]
    have hg_diff : DifferentiableAt ℝ (fun w => fderiv ℝ f w (Pi.single i 1)) (x - y) := by
      rw [show (fun w => fderiv ℝ f w (Pi.single i 1)) =
        (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)) ∘ (fderiv ℝ f) from rfl]
      exact DifferentiableAt.comp _
        (ContinuousLinearMap.apply ℝ ℝ (Pi.single i 1)).differentiableAt
        ((_hf.fderiv_right le_top).differentiable WithTop.top_ne_zero |>.differentiableAt)
    rw [fderiv_comp_const_sub_LP (fun w => fderiv ℝ f w (Pi.single i 1)) x y hg_diff]
    simp

  unfold laplacianLP
  congr 1; ext i
  rw [show (fun z => fderiv ℝ (fun x' => f (x' - y)) z (Pi.single i 1))
    = (fun z => fderiv ℝ f (z - y) (Pi.single i 1)) from by ext z; rw [fderiv_comp_sub y]]
  rw [show (fun z => fderiv ℝ f (z - y) (Pi.single i 1))
    = (fun z => (fun w => fderiv ℝ f w (Pi.single i 1)) (z - y)) from rfl]
  exact @fderiv_comp_sub ℝ _ (Fin n → ℝ) _ _ ℝ _ _
    (fun w => fderiv ℝ f w (Pi.single i 1)) x y ▸ rfl

/-- Combining the substitution and Leibniz rules:
$\Delta_x (\Phi * f)(x) = \int \Phi(y) \, \Delta_z f(x - z)|_{z = y}\,dy$. -/
theorem laplacian_convolution_eq_integral {n : ℕ} (hn : n ≥ 3)
    (f : (Fin n → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f)
    (x : Fin n → ℝ) :
    laplacianLP (phiConvolutionLP n f) x =
      ∫ y, fundamentalSolution n y * laplacianLP (fun z => f (x - z)) y := by


  have h_conv : phiConvolutionLP n f = fun x' => ∫ y, fundamentalSolution n y * f (x' - y) := by
    ext x'; exact convolution_substitution f x'
  rw [h_conv]

  rw [leibniz_laplacian_under_integral hn f hf_smooth hf_supp x]

  congr 1; ext y
  rw [laplacianLP_chain_rule_sub f hf_smooth x y]

/-- The Laplacian of a smooth, compactly supported function is uniformly bounded. -/
theorem laplacianLP_bounded_of_smooth_compactSupport {n : ℕ}
    (g : (Fin n → ℝ) → ℝ)
    (_hg_smooth : ContDiff ℝ ⊤ g) (_hg_supp : HasCompactSupport g) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : Fin n → ℝ, |laplacianLP g y| ≤ M := by

  have h_summand_supp : ∀ i : Fin n,
      HasCompactSupport (fun x => fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x (Pi.single i 1)) := by
    intro i
    exact (_hg_supp.fderiv_apply (𝕜 := ℝ) (Pi.single i 1)).fderiv_apply (𝕜 := ℝ) (Pi.single i 1)

  have h_summand_cont : ∀ i : Fin n,
      Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x (Pi.single i 1)) := by
    intro i
    have h_inner_smooth : ContDiff ℝ ⊤ (fun y => fderiv ℝ g y (Pi.single i 1)) :=
      (_hg_smooth.fderiv_right le_top).clm_apply contDiff_const
    exact (h_inner_smooth.continuous_fderiv (by simp)).clm_apply continuous_const

  have h_summand_bound : ∀ i : Fin n, ∃ C : ℝ, ∀ x, ‖(fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) x (Pi.single i 1))‖ ≤ C := by
    intro i
    exact (h_summand_supp i).exists_bound_of_continuous (h_summand_cont i)

  choose Cs hCs using h_summand_bound

  refine ⟨∑ i : Fin n, |Cs i|, Finset.sum_nonneg (fun i _ => abs_nonneg _), fun y => ?_⟩
  unfold laplacianLP
  calc |∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) y (Pi.single i 1)|
      ≤ ∑ i : Fin n, |fderiv ℝ (fun y => fderiv ℝ g y (Pi.single i 1)) y (Pi.single i 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin n, |Cs i| := by
        apply Finset.sum_le_sum
        intro i _
        have := hCs i y
        rw [Real.norm_eq_abs] at this
        exact this.trans (le_abs_self _)

/-- Polar/coarea formula identification: the integral of $|\Phi|$ over the
Euclidean ball of radius $\varepsilon$ equals the 1D integral $\int_0^\varepsilon r\,dr$. -/
theorem coarea_euclidBall_abs_fundamentalSolution_eq {n : ℕ} (_hn : n ≥ 3)
    (ε : ℝ) (_hε : 0 < ε) :
    ∫ y in {z : Fin n → ℝ | euclidNormLP z < ε},
      |fundamentalSolution n y| = ∫ r in (0:ℝ)..ε, r := by sorry

/-- Bound on $\int_{|y|<\varepsilon} |\Phi(y)|\,dy \le \varepsilon^2/2$
for $n \ge 3$. -/
theorem euclidBall_integral_fundamentalSolution_abs_le {n : ℕ} (hn : n ≥ 3)
    (ε : ℝ) (hε : 0 < ε) :
    ∫ y in {z : Fin n → ℝ | euclidNormLP z < ε},
      |fundamentalSolution n y| ≤ ε ^ 2 / 2 := by
  rw [coarea_euclidBall_abs_fundamentalSolution_eq hn ε hε]
  rw [integral_id]
  linarith [sq_nonneg ε]

/-- Crude lower bound on the surface area of the unit sphere: $n - 2 \le \omega_n$
for $n \ge 3$. -/
theorem unitSphereArea_ge_dim_sub_two {n : ℕ} (_hn : n ≥ 3) :
    (↑n : ℝ) - 2 ≤ unitSphereArea n := by sorry


/-- Polar-coordinate bound on $\int_{|y|<\varepsilon} |\Phi(y)|\,dy \le
\omega_n / (2(n-2)) \cdot \varepsilon^2$ for $n \ge 3$. -/
theorem polar_coord_radial_integral {n : ℕ} (hn : n ≥ 3)
    (ε : ℝ) (hε : 0 < ε) :
    ∫ y in {z : Fin n → ℝ | euclidNormLP z < ε},
      |fundamentalSolution n y| ≤ unitSphereArea n / (2 * (↑n - 2)) * ε ^ 2 := by
  have hint := euclidBall_integral_fundamentalSolution_abs_le hn ε hε
  have hω := unitSphereArea_ge_dim_sub_two hn
  have hn2 : (0 : ℝ) < (↑n : ℝ) - 2 := by
    have : (3 : ℝ) ≤ (↑n : ℝ) := by exact_mod_cast hn
    linarith
  have h2n2 : (0 : ℝ) < 2 * ((↑n : ℝ) - 2) := by positivity
  calc ∫ y in {z : Fin n → ℝ | euclidNormLP z < ε}, |fundamentalSolution n y|
      ≤ ε ^ 2 / 2 := hint
    _ ≤ unitSphereArea n / (2 * (↑n - 2)) * ε ^ 2 := by
        rw [div_mul_eq_mul_div]
        rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 2) h2n2]
        nlinarith [sq_nonneg ε]

/-- Restatement of `polar_coord_radial_integral` used downstream. -/
theorem fundamentalSolution_integral_near_origin_bound {n : ℕ} (hn : n ≥ 3)
    (ε : ℝ) (hε : 0 < ε) :
    ∫ y in {z : Fin n → ℝ | euclidNormLP z < ε},
      |fundamentalSolution n y| ≤ unitSphereArea n / (2 * (↑n - 2)) * ε ^ 2 :=
  polar_coord_radial_integral hn ε hε

/-- $|\Phi|$ is integrable on the Euclidean ball of radius $\varepsilon$ for $n \ge 3$. -/
theorem fundamentalSolution_abs_integrableOn_ball {n : ℕ} (_hn : n ≥ 3)
    (ε : ℝ) (_hε : 0 < ε) :
    MeasureTheory.IntegrableOn (fun y => |fundamentalSolution n y|)
      {z : Fin n → ℝ | euclidNormLP z < ε} := by sorry

/-- For a bounded function $g$, the product $\Phi \cdot g$ is integrable on the
Euclidean ball of radius $\varepsilon$ for $n \ge 3$. -/
theorem fundamentalSolution_mul_bounded_integrableOn_ball {n : ℕ} (_hn : n ≥ 3)
    (g : (Fin n → ℝ) → ℝ) (ε : ℝ) (_hε : 0 < ε)
    (_hg_bound : ∃ M : ℝ, ∀ y, |g y| ≤ M) :
    MeasureTheory.IntegrableOn (fun y => fundamentalSolution n y * g y)
      {z : Fin n → ℝ | euclidNormLP z < ε} := by sorry

/-- The fundamental solution $\Phi$ is locally integrable on $\mathbb{R}^n$
for $n \ge 2$. -/
theorem fundamentalSolution_locallyIntegrable {n : ℕ} (_hn : n ≥ 2) :
    MeasureTheory.LocallyIntegrable (fundamentalSolution n)
      (volume : Measure (Fin n → ℝ)) := by sorry

/-- Near-origin estimate: the integral of $\Phi(y) \, \Delta_z f(x - z)|_y$
over the ball of radius $\varepsilon$ is $O(\varepsilon^2)$. -/
theorem near_field_spherical_bound {n : ℕ} (hn : n ≥ 3)
    (f : (Fin n → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f)
    (x : Fin n → ℝ) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε →
      ‖∫ y in {z : Fin n → ℝ | euclidNormLP z < ε},
        fundamentalSolution n y * laplacianLP (fun z => f (x - z)) y‖ ≤ C * ε ^ 2 := by


  have hfx_smooth : ContDiff ℝ ⊤ (fun z => f (x - z)) :=
    hf_smooth.comp (contDiff_const.sub contDiff_id)
  have hfx_supp : HasCompactSupport (fun z => f (x - z)) :=
    hf_supp.comp_homeomorph (Homeomorph.subLeft x)
  obtain ⟨M, hM_nn, hM_bound⟩ :=
    laplacianLP_bounded_of_smooth_compactSupport (fun z => f (x - z)) hfx_smooth hfx_supp


  exact ⟨M * (unitSphereArea n / (2 * (↑n - 2))), fun ε hε => by
    have h_bound := fundamentalSolution_integral_near_origin_bound hn ε hε
    have hg_int := fundamentalSolution_mul_bounded_integrableOn_ball hn
      (laplacianLP (fun z => f (x - z))) ε hε ⟨M, hM_bound⟩
    have h_abs_int := fundamentalSolution_abs_integrableOn_ball hn ε hε

    have h1 := norm_integral_le_integral_norm
      (μ := volume.restrict {z : Fin n → ℝ | euclidNormLP z < ε})
      (fun y => fundamentalSolution n y * laplacianLP (fun z => f (x - z)) y)

    have h2 : ∫ y in {z : Fin n → ℝ | euclidNormLP z < ε},
        ‖fundamentalSolution n y * laplacianLP (fun z => f (x - z)) y‖ ≤
      ∫ y in {z : Fin n → ℝ | euclidNormLP z < ε}, |fundamentalSolution n y| * M := by
      apply MeasureTheory.setIntegral_mono_on hg_int.norm
        (h_abs_int.mul_const M)
        (isOpen_lt continuous_euclidNormLP continuous_const).measurableSet
      intro y _
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hM_bound y) (abs_nonneg _)

    have h3 : ∫ y in {z : Fin n → ℝ | euclidNormLP z < ε},
        |fundamentalSolution n y| * M =
      M * ∫ y in {z : Fin n → ℝ | euclidNormLP z < ε}, |fundamentalSolution n y| := by
      rw [show (fun y => |fundamentalSolution n y| * M) =
        (fun y => M * |fundamentalSolution n y|) from by ext y; ring,
        show (∫ y in {z : Fin n → ℝ | euclidNormLP z < ε}, M * |fundamentalSolution n y|) =
          M * (∫ y in {z : Fin n → ℝ | euclidNormLP z < ε}, |fundamentalSolution n y|) from
        MeasureTheory.integral_const_mul M _]

    calc ‖∫ y in {z | euclidNormLP z < ε}, fundamentalSolution n y *
          laplacianLP (fun z => f (x - z)) y‖
        ≤ ∫ y in {z | euclidNormLP z < ε},
          ‖fundamentalSolution n y * laplacianLP (fun z => f (x - z)) y‖ := h1
      _ ≤ ∫ y in {z | euclidNormLP z < ε}, |fundamentalSolution n y| * M := h2
      _ = M * ∫ y in {z | euclidNormLP z < ε}, |fundamentalSolution n y| := h3
      _ ≤ M * (unitSphereArea n / (2 * (↑n - 2)) * ε ^ 2) :=
          mul_le_mul_of_nonneg_left h_bound hM_nn
      _ = M * (unitSphereArea n / (2 * (↑n - 2))) * ε ^ 2 := by ring⟩

/-- The near-origin contribution to the convolution integral vanishes as
$\varepsilon \to 0^+$. -/
theorem near_field_integral_vanishes {n : ℕ} (hn : n ≥ 3)
    (f : (Fin n → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f)
    (x : Fin n → ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ y in {z : Fin n → ℝ | euclidNormLP z < ε},
        fundamentalSolution n y * laplacianLP (fun z => f (x - z)) y)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by

  obtain ⟨C, hbound⟩ := near_field_spherical_bound hn f hf_smooth hf_supp x

  apply squeeze_zero_norm' (a := fun ε => C * ε ^ 2)
  · exact eventually_nhdsWithin_of_forall fun ε hε => hbound ε (Set.mem_Ioi.mp hε)
  · have h1 : Filter.Tendsto (fun ε : ℝ => ε ^ 2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have := (continuous_pow 2).tendsto (0 : ℝ)
      simp at this
      exact this.mono_left nhdsWithin_le_nhds
    have h2 := h1.const_mul C
    simp at h2
    exact h2

/-- Green's second identity on the exterior $\{|z| \ge \varepsilon\}$, using
that $u$ is compactly supported (so boundary contributions at infinity vanish)
and that $v$ is harmonic in this region. -/
theorem greens_second_identity_exterior_compactSupp {n : ℕ} (hn : n ≥ 3)
    (u : (Fin n → ℝ) → ℝ) (v : (Fin n → ℝ) → ℝ)
    (hu_smooth : ContDiff ℝ ⊤ u) (hu_supp : HasCompactSupport u)
    (ε : ℝ) (hε : 0 < ε)
    (hv_harmonic : ∀ y : Fin n → ℝ, euclidNormLP y ≥ ε → laplacianLP v y = 0) :
    (∫ y in {z : Fin n → ℝ | euclidNormLP z ≥ ε},
      v y * laplacianLP u y) =
    surfaceIntegralLP {z : Fin n → ℝ | euclidNormLP z = ε}
      (fun σ => v σ * normalDerivLP {z | euclidNormLP z ≥ ε} u σ -
        u σ * normalDerivLP {z | euclidNormLP z ≥ ε} v σ) := by sorry

/-- Application of Green's identity in the exterior region to the pair
$(\text{f-translated},\, \Phi)$: the exterior volume integral becomes a surface
integral over $\{|z| = \varepsilon\}$. -/
theorem greens_identity_annular_reduction {n : ℕ} (_hn : n ≥ 3)
    (f : (Fin n → ℝ) → ℝ)
    (_hf_smooth : ContDiff ℝ ⊤ f) (_hf_supp : HasCompactSupport f)
    (x : Fin n → ℝ) (ε : ℝ) (_hε : 0 < ε) :
    (∫ y in {z : Fin n → ℝ | euclidNormLP z ≥ ε},
      fundamentalSolution n y * laplacianLP (fun z => f (x - z)) y) =
    surfaceIntegralLP {z : Fin n → ℝ | euclidNormLP z = ε}
      (fun σ => fundamentalSolution n σ * normalDerivLP {z | euclidNormLP z ≥ ε}
        (fun z => f (x - z)) σ -
        f (x - σ) * normalDerivLP {z | euclidNormLP z ≥ ε}
          (fundamentalSolution n) σ) := by


  have h_harmonic : ∀ y : Fin n → ℝ, euclidNormLP y ≥ ε →
      laplacianLP (fundamentalSolution n) y = 0 := fun y hy => by
    apply fundamental_solution_harmonic_away _hn
    intro h0; simp [h0, euclidNormLP] at hy; linarith

  have hu_smooth : ContDiff ℝ ⊤ (fun z => f (x - z)) :=
    _hf_smooth.comp (contDiff_const.sub contDiff_id)
  have hu_supp : HasCompactSupport (fun z => f (x - z)) :=
    _hf_supp.comp_homeomorph (Homeomorph.subLeft x)

  exact greens_second_identity_exterior_compactSupp _hn
    (fun z => f (x - z)) (fundamentalSolution n)
    hu_smooth hu_supp ε _hε h_harmonic

/-- The surface measure of the sphere $\{|z| = \varepsilon\}$ is finite. -/
theorem surfaceMeasure_sphere_finite {n : ℕ} (ε : ℝ) (_hε : 0 < ε) :
    (surfaceMeasure {z : Fin n → ℝ | euclidNormLP z = ε}) (frontier {z : Fin n → ℝ | euclidNormLP z = ε}) < ⊤ := by sorry

/-- Crude upper bound on the surface measure of $\{|z| = \varepsilon\}$:
$\le n \omega_n \varepsilon^{n-1}$. -/
theorem surfaceMeasure_sphere_real_le {n : ℕ} (ε : ℝ) (hε : 0 < ε) :
    (surfaceMeasure {z : Fin n → ℝ | euclidNormLP z = ε}).real
      (frontier {z : Fin n → ℝ | euclidNormLP z = ε}) ≤ ↑n * unitSphereArea n * ε ^ (n - 1) := by sorry

/-- The normal derivative of a smooth compactly supported function admits a
uniform bound that is independent of the domain $\Omega$ and point $\sigma$. -/
theorem normalDerivLP_uniform_bound_of_smooth_compactSupport {n : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (_hf_smooth : ContDiff ℝ ⊤ f) (_hf_supp : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (Ω : Set (Fin n → ℝ)) (σ : Fin n → ℝ), |normalDerivLP Ω f σ| ≤ M := by sorry

/-- The boundary integral $\int_{|z| = \varepsilon} \Phi(\sigma)\,
\partial_\nu f(x - \sigma)\,dS$ is bounded by $C \varepsilon$ for some
constant $C$ independent of $\varepsilon$. -/
theorem surface_gradient_term_bounded {n : ℕ} (_hn : n ≥ 3)
    (f : (Fin n → ℝ) → ℝ)
    (_hf_smooth : ContDiff ℝ ⊤ f) (_hf_supp : HasCompactSupport f)
    (x : Fin n → ℝ) :
    ∃ C, ∀ ε > 0, ‖surfaceIntegralLP {z : Fin n → ℝ | euclidNormLP z = ε}
      (fun σ => fundamentalSolution n σ *
        normalDerivLP {z | euclidNormLP z ≥ ε} (fun z => f (x - z)) σ)‖ ≤ C * ε := by

  have hfx_smooth : ContDiff ℝ ⊤ (fun z => f (x - z)) :=
    _hf_smooth.comp (contDiff_const.sub contDiff_id)
  have hfx_supp : HasCompactSupport (fun z => f (x - z)) :=
    _hf_supp.comp_homeomorph (Homeomorph.subLeft x)
  obtain ⟨M, hM_nn, hM_bound⟩ :=
    normalDerivLP_uniform_bound_of_smooth_compactSupport
      (fun z => f (x - z)) hfx_smooth hfx_supp

  refine ⟨↑n * M, fun ε hε => ?_⟩

  have h_surf := surfaceMeasure_sphere_finite (n := n) ε hε
  have h_area := surfaceMeasure_sphere_real_le (n := n) ε hε

  have h_integ_bound : ∀ σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε},
      ‖fundamentalSolution n σ *
        normalDerivLP {z | euclidNormLP z ≥ ε} (fun z => f (x - z)) σ‖ ≤
        1 / (unitSphereArea n * ε ^ (n - 2)) * M := by
    intro σ hσ

    have hσ_on_sphere : euclidNormLP σ = ε := by
      have : frontier {z : Fin n → ℝ | euclidNormLP z = ε} ⊆
          {z : Fin n → ℝ | euclidNormLP z = ε} :=
        frontier_subset_closure.trans
          (closure_eq_iff_isClosed.mpr
            (isClosed_eq continuous_euclidNormLP continuous_const)).le
      exact this hσ

    have hn_ne_2 : n ≠ 2 := by omega
    have h_phi : fundamentalSolution n σ = -1 / (unitSphereArea n * ε ^ (n - 2)) := by
      unfold fundamentalSolution
      rw [if_neg hn_ne_2, hσ_on_sphere]
    rw [h_phi, Real.norm_eq_abs, abs_mul]
    have hω_pos : unitSphereArea n > 0 := unitSphereArea_pos n
    have hε_pow_pos : ε ^ (n - 2) > 0 := pow_pos hε (n - 2)
    have hdenom_pos : unitSphereArea n * ε ^ (n - 2) > 0 := mul_pos hω_pos hε_pow_pos
    rw [abs_div, abs_neg, abs_one, abs_of_pos hdenom_pos]
    exact mul_le_mul_of_nonneg_left
      (hM_bound {z | euclidNormLP z ≥ ε} σ)
      (div_nonneg zero_le_one (le_of_lt hdenom_pos))

  show ‖surfaceIntegralLP {z : Fin n → ℝ | euclidNormLP z = ε}
      (fun σ => fundamentalSolution n σ *
        normalDerivLP {z | euclidNormLP z ≥ ε} (fun z => f (x - z)) σ)‖ ≤ ↑n * M * ε
  unfold surfaceIntegralLP
  have h_norm_bound := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (f := fun σ => fundamentalSolution n σ *
        normalDerivLP {z | euclidNormLP z ≥ ε} (fun z => f (x - z)) σ)
    (s := frontier {z : Fin n → ℝ | euclidNormLP z = ε})
    (μ := surfaceMeasure {z : Fin n → ℝ | euclidNormLP z = ε})
    (C := 1 / (unitSphereArea n * ε ^ (n - 2)) * M)
    h_surf h_integ_bound
  calc ‖∫ σ in frontier {z : Fin n → ℝ | euclidNormLP z = ε},
        (fun σ => fundamentalSolution n σ *
          normalDerivLP {z | euclidNormLP z ≥ ε} (fun z => f (x - z)) σ) σ
        ∂surfaceMeasure {z : Fin n → ℝ | euclidNormLP z = ε}‖
      ≤ 1 / (unitSphereArea n * ε ^ (n - 2)) * M *
        (surfaceMeasure {z : Fin n → ℝ | euclidNormLP z = ε}).real
          (frontier {z : Fin n → ℝ | euclidNormLP z = ε}) := h_norm_bound
    _ ≤ 1 / (unitSphereArea n * ε ^ (n - 2)) * M *
        (↑n * unitSphereArea n * ε ^ (n - 1)) := by
        apply mul_le_mul_of_nonneg_left h_area
        exact mul_nonneg (div_nonneg zero_le_one
          (le_of_lt (mul_pos (unitSphereArea_pos n) (pow_pos hε (n - 2))))) hM_nn
    _ = ↑n * M * ε := by
        have hω_pos : unitSphereArea n > 0 := unitSphereArea_pos n
        have hε_pow_pos : ε ^ (n - 2) > 0 := pow_pos hε (n - 2)
        have hdenom_ne : unitSphereArea n * ε ^ (n - 2) ≠ 0 :=
          ne_of_gt (mul_pos hω_pos hε_pow_pos)
        have hn_sub : n - 1 = (n - 2) + 1 := by omega
        rw [hn_sub, pow_succ]
        field_simp

/-- Normalization identity: $\int_{|σ|=\varepsilon} \partial_\nu \Phi(\sigma)\,dS = -1$
for $n \ge 3$. This is the key fact that produces $f(x)$ in the Poisson formula. -/
theorem surfaceIntegralLP_normalDeriv_Phi_origin_eq_neg_one {n : ℕ} (hn : n ≥ 3) (ε : ℝ) (hε : 0 < ε) :
    surfaceIntegralLP {z : Fin n → ℝ | euclidNormLP z = ε}
      (fun σ => normalDerivLP {z | euclidNormLP z ≥ ε} (fundamentalSolution n) σ) = -1 := by
  unfold surfaceIntegralLP
  rw [MeasureTheory.integral_congr_ae
    (normalDerivLP_fundamentalSolution_sphere_ae hn ε hε)]
  rw [MeasureTheory.setIntegral_const]
  rw [surfaceMeasure_sphere_measureReal hn ε hε]
  rw [smul_eq_mul]
  have hω_pos := unitSphereArea_pos n
  have h_ne : unitSphereArea n * ε ^ (n - 1) ≠ 0 :=
    mul_ne_zero (ne_of_gt hω_pos) (ne_of_gt (pow_pos hε _))
  field_simp

/-- Technical auxiliary: the supremum-indicator family $\sigma \mapsto
\sup_{\sigma \in \partial S} |g(\sigma)|$ is bounded above when $g$ is
integrable on the sphere. -/
theorem surfaceIntegralLP_origin_bddAbove_aux {n : ℕ} (hn : n ≥ 3)
    (g : (Fin n → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hint : IntegrableOn g (frontier {z : Fin n → ℝ | euclidNormLP z = ε})
      (surfaceMeasure {z : Fin n → ℝ | euclidNormLP z = ε})) :
    BddAbove (Set.range (fun σ => ⨆ (_ : σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε}), |g σ|)) := by sorry

/-- Oscillation bound: the surface integral $\int_{|\sigma|=\varepsilon} g(\sigma)\,
\partial_\nu \Phi(\sigma)\,dS$ is bounded by the supremum of $|g|$ over the sphere. This
uses the identity $\partial_\nu \Phi = -\frac{1}{\omega_n \varepsilon^{n-1}}$ together with
the area of the sphere being $\omega_n \varepsilon^{n-1}$. -/
theorem surfaceIntegralLP_origin_oscillation_bound {n : ℕ} (hn : n ≥ 3)
    (g : (Fin n → ℝ) → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ‖surfaceIntegralLP {z : Fin n → ℝ | euclidNormLP z = ε}
      (fun σ => g σ * normalDerivLP {z | euclidNormLP z ≥ ε} (fundamentalSolution n) σ)‖ ≤
    ⨆ σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε}, |g σ| := by
  set S := {z : Fin n → ℝ | euclidNormLP z = ε}
  set c := -1 / (unitSphereArea n * ε ^ (n - 1))
  set μ := surfaceMeasure S
  have hω_pos := unitSphereArea_pos n
  have hε_pow_pos : ε ^ (n - 1) > 0 := pow_pos hε _
  have h_denom_pos : unitSphereArea n * ε ^ (n - 1) > 0 := mul_pos hω_pos hε_pow_pos
  have h_denom_ne : unitSphereArea n * ε ^ (n - 1) ≠ 0 := ne_of_gt h_denom_pos
  have hc_ne : c ≠ 0 := by
    simp only [c, neg_div, neg_ne_zero, one_div, ne_eq, inv_eq_zero]
    exact h_denom_ne
  unfold surfaceIntegralLP
  have h_ae := normalDerivLP_fundamentalSolution_sphere_ae hn ε hε
  have h_congr : (fun σ => g σ * normalDerivLP {z | euclidNormLP z ≥ ε} (fundamentalSolution n) σ)
      =ᵐ[μ.restrict (frontier S)] (fun σ => g σ * c) := by
    exact h_ae.mono fun σ hσ => congrArg (g σ * ·) hσ

  by_cases hint : IntegrableOn
      (fun σ => g σ * normalDerivLP {z | euclidNormLP z ≥ ε} (fundamentalSolution n) σ)
      (frontier S) μ
  ·
    rw [integral_congr_ae h_congr, integral_mul_const]
    have h_finite := surfaceMeasure_sphere_finite (n := n) ε hε
    have h_meas_real := surfaceMeasure_sphere_measureReal hn ε hε
    have hint_gc : IntegrableOn (fun σ => g σ * c) (frontier S) μ :=
      hint.congr h_congr
    have hint_g : IntegrableOn g (frontier S) μ :=
      ((integrable_mul_const_iff (IsUnit.mk0 c hc_ne)) g).mp hint_gc
    set M := ⨆ σ ∈ frontier S, |g σ|
    have hc_abs : |c| = 1 / (unitSphereArea n * ε ^ (n - 1)) := by
      simp only [c, abs_div, abs_neg, abs_one, abs_of_pos h_denom_pos]
    rw [Real.norm_eq_abs, abs_mul, hc_abs]
    suffices h : |∫ σ in frontier S, g σ ∂μ| ≤ M * (unitSphereArea n * ε ^ (n - 1)) by
      calc |∫ σ in frontier S, g σ ∂μ| * (1 / (unitSphereArea n * ε ^ (n - 1)))
          ≤ M * (unitSphereArea n * ε ^ (n - 1)) *
            (1 / (unitSphereArea n * ε ^ (n - 1))) := by
            apply mul_le_mul_of_nonneg_right h; positivity
        _ = M := by field_simp
    rw [← h_meas_real, ← Real.norm_eq_abs]
    apply norm_setIntegral_le_of_norm_le_const h_finite
    intro σ hσ
    rw [Real.norm_eq_abs]
    have hbdd := surfaceIntegralLP_origin_bddAbove_aux hn g ε hε hint_g
    have h1 : (⨆ (_ : σ ∈ frontier S), |g σ|) ≤ M := le_ciSup hbdd σ
    rw [ciSup_pos hσ] at h1
    exact h1
  ·
    rw [integral_undef hint, norm_zero]
    exact Real.iSup_nonneg fun σ => Real.iSup_nonneg fun _ => abs_nonneg _

/-- The sup-norm on $\mathbb{R}^n$ is dominated by the Euclidean L² norm:
$\|\sigma\|_\infty \le \|\sigma\|_2$. -/
lemma norm_le_euclidNormLP {n : ℕ} (σ : Fin n → ℝ) : ‖σ‖ ≤ euclidNormLP σ := by
  unfold euclidNormLP
  have h_comp : ∀ i : Fin n, |σ i| ≤ Real.sqrt (∑ j, σ j ^ 2) := by
    intro i
    have h1 : σ i ^ 2 ≤ ∑ j, σ j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (σ j)) (Finset.mem_univ i)
    calc |σ i| = Real.sqrt (σ i ^ 2) := by rw [Real.sqrt_sq_eq_abs]
      _ ≤ Real.sqrt (∑ j, σ j ^ 2) := Real.sqrt_le_sqrt h1
  exact pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr h_comp

/-- Continuity at $x$ implies that the oscillation
$\sup_{|\sigma|=\varepsilon} |f(x-\sigma) - f(x)|$ tends to $0$ as $\varepsilon \to 0^+$. -/
theorem oscillation_origin_sphere_tendsto_zero {n : ℕ}
    (f : (Fin n → ℝ) → ℝ) (hf : Continuous f) (x : Fin n → ℝ) :
    Filter.Tendsto
      (fun ε => ⨆ σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε}, |f (x - σ) - f x|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  have hδ2 : (0 : ℝ) < δ / 2 := half_pos hδ
  have hcont := hf.continuousAt (x := x)
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨η, hη_pos, hη⟩ := hcont (δ / 2) hδ2
  refine ⟨η, hη_pos, fun ε hε_mem hε_dist => ?_⟩
  have hε_pos : (0 : ℝ) < ε := hε_mem
  have hε_lt_η : ε < η := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hε_pos] at hε_dist
    exact hε_dist
  have hfrontier_sub : frontier {z : Fin n → ℝ | euclidNormLP z = ε} ⊆
      {z | euclidNormLP z = ε} := by
    have hclosed : IsClosed {z : Fin n → ℝ | euclidNormLP z = ε} :=
      IsClosed.preimage
        (Continuous.sqrt (continuous_finset_sum _ (fun i _ => (continuous_apply i).pow 2)))
        isClosed_singleton
    exact frontier_subset_closure.trans hclosed.closure_eq.subset
  have hbound : ∀ σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε},
      |f (x - σ) - f x| ≤ δ / 2 := by
    intro σ hσ_frontier
    have hσ_norm : euclidNormLP σ = ε := hfrontier_sub hσ_frontier
    have h_dist : dist (x - σ) x < η := by
      calc dist (x - σ) x = ‖(x - σ) - x‖ := dist_eq_norm _ _
        _ = ‖-σ‖ := by ring_nf
        _ = ‖σ‖ := norm_neg σ
        _ ≤ euclidNormLP σ := norm_le_euclidNormLP σ
        _ = ε := hσ_norm
        _ < η := hε_lt_η
    have h_f_dist := hη h_dist
    rw [Real.dist_eq] at h_f_dist
    exact h_f_dist.le
  have h_bisup_le : (⨆ σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε},
      |f (x - σ) - f x|) ≤ δ / 2 := by
    apply ciSup_le
    intro σ
    by_cases hσ : σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε}
    · haveI : Nonempty (σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε}) := ⟨hσ⟩
      exact ciSup_le (fun _ => hbound σ hσ)
    · haveI : IsEmpty (σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε}) :=
        isEmpty_Prop.mpr hσ
      rw [Real.iSup_of_isEmpty]
      exact hδ2.le
  have h_bisup_nn : 0 ≤ (⨆ σ ∈ frontier {z : Fin n → ℝ | euclidNormLP z = ε},
      |f (x - σ) - f x|) := by
    apply Real.sSup_nonneg
    intro y hy
    obtain ⟨σ, rfl⟩ := mem_range.mp hy
    apply Real.sSup_nonneg
    intro z hz
    obtain ⟨_, rfl⟩ := mem_range.mp hz
    exact abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h_bisup_nn]
  linarith

/-- Integrability on the boundary $\partial\Omega$: every function is integrable
against the (auxiliary) surface measure used in this development. -/
theorem surfaceIntegral_integrable_LP_early {n : ℕ} (Ω : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) :
    MeasureTheory.IntegrableOn f (frontier Ω) (surfaceMeasure Ω) := by sorry


/-- Decomposition of the surface integral of $f(x-\sigma)\,\partial_\nu \Phi(\sigma)$:
this equals $-f(x)$ plus an error term that vanishes as $\varepsilon \to 0^+$. -/
theorem surface_fvalue_decomposition {n : ℕ} (hn : n ≥ 3)
    (f : (Fin n → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f)
    (x : Fin n → ℝ) :
    ∃ (error : ℝ → ℝ),
      (∀ ε > 0, -surfaceIntegralLP {z : Fin n → ℝ | euclidNormLP z = ε}
          (fun σ => f (x - σ) *
            normalDerivLP {z | euclidNormLP z ≥ ε} (fundamentalSolution n) σ) =
        f x + error ε) ∧
      Filter.Tendsto error (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by

  refine ⟨fun ε => -(surfaceIntegralLP {z : Fin n → ℝ | euclidNormLP z = ε}
    (fun σ => (f (x - σ) - f x) *
      normalDerivLP {z | euclidNormLP z ≥ ε} (fundamentalSolution n) σ)), ?_, ?_⟩
  ·
    intro ε hε

    have hsplit : (fun σ => f (x - σ) *
        normalDerivLP {z | euclidNormLP z ≥ ε} (fundamentalSolution n) σ) =
      (fun σ => f x * normalDerivLP {z | euclidNormLP z ≥ ε} (fundamentalSolution n) σ +
        (f (x - σ) - f x) * normalDerivLP {z | euclidNormLP z ≥ ε} (fundamentalSolution n) σ) := by
      ext σ; ring
    rw [hsplit]

    unfold surfaceIntegralLP
    rw [MeasureTheory.integral_add
      (surfaceIntegral_integrable_LP_early _ _)
      (surfaceIntegral_integrable_LP_early _ _)]

    rw [show (fun σ => f x * normalDerivLP {z | euclidNormLP z ≥ ε}
        (fundamentalSolution n) σ) =
      (fun σ => f x • (normalDerivLP {z | euclidNormLP z ≥ ε}
        (fundamentalSolution n) σ)) from by ext σ; simp [smul_eq_mul]]
    rw [MeasureTheory.integral_smul]

    have h_norm := surfaceIntegralLP_normalDeriv_Phi_origin_eq_neg_one hn ε hε
    unfold surfaceIntegralLP at h_norm
    rw [h_norm]
    simp [smul_eq_mul]
    ring
  ·


    have h_pos : Filter.Tendsto
        (fun ε => surfaceIntegralLP {z : Fin n → ℝ | euclidNormLP z = ε}
          (fun σ => (f (x - σ) - f x) *
            normalDerivLP {z | euclidNormLP z ≥ ε} (fundamentalSolution n) σ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      apply squeeze_zero_norm'
      · exact eventually_nhdsWithin_of_forall fun ε hε => by
          exact surfaceIntegralLP_origin_oscillation_bound hn
            (fun σ => f (x - σ) - f x) ε (mem_Ioi.mp hε)
      · exact oscillation_origin_sphere_tendsto_zero f hf_smooth.continuous x
    have h_neg := h_pos.neg
    rwa [neg_zero] at h_neg

/-- Pointwise limit: $-\int_{|\sigma|=\varepsilon} f(x-\sigma)\,\partial_\nu \Phi(\sigma)\,
dS \to f(x)$ as $\varepsilon \to 0^+$. This is the source of the Dirac delta in the
Poisson formula. -/
theorem surface_fvalue_term_limit {n : ℕ} (hn : n ≥ 3)
    (f : (Fin n → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f)
    (x : Fin n → ℝ) :
    Filter.Tendsto
      (fun ε => -surfaceIntegralLP {z : Fin n → ℝ | euclidNormLP z = ε}
        (fun σ => f (x - σ) *
          normalDerivLP {z | euclidNormLP z ≥ ε} (fundamentalSolution n) σ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by
  obtain ⟨error, h_eq, h_err⟩ := surface_fvalue_decomposition hn f hf_smooth hf_supp x
  have h_sum : Filter.Tendsto (fun ε => f x + error ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by
    have := (@tendsto_const_nhds _ _ _ (f x) (nhdsWithin 0 (Set.Ioi 0))).add h_err
    rwa [add_zero] at this
  exact h_sum.congr' (Filter.EventuallyEq.symm
    (eventually_nhdsWithin_of_forall fun ε hε => h_eq ε (mem_Ioi.mp hε)))

/-- Far-field Green's identity computation: the volume integral
$\int_{|z|\ge \varepsilon} \Phi(y)\,\Delta f(x-y)\,dy$ decomposes as a "gradient term"
that is $O(\varepsilon)$ plus an "$f$-term" that converges to $f(x)$. -/
theorem far_field_greens_computation {n : ℕ} (hn : n ≥ 3)
    (f : (Fin n → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f)
    (x : Fin n → ℝ) :
    ∃ (gradient_term f_term : ℝ → ℝ),

      (∀ ε > 0, (∫ y in {z : Fin n → ℝ | euclidNormLP z ≥ ε},
        fundamentalSolution n y * laplacianLP (fun z => f (x - z)) y) =
          gradient_term ε + f_term ε) ∧

      (∃ C, ∀ ε > 0, ‖gradient_term ε‖ ≤ C * ε) ∧

      Filter.Tendsto f_term (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by

  set grad := fun ε => surfaceIntegralLP {z : Fin n → ℝ | euclidNormLP z = ε}
      (fun σ => fundamentalSolution n σ *
        normalDerivLP {z | euclidNormLP z ≥ ε} (fun z => f (x - z)) σ)
  set fterm := fun ε => -(surfaceIntegralLP {z : Fin n → ℝ | euclidNormLP z = ε}
      (fun σ => f (x - σ) *
        normalDerivLP {z | euclidNormLP z ≥ ε} (fundamentalSolution n) σ))
  refine ⟨grad, fterm, ?_, ?_, ?_⟩
  ·
    intro ε hε
    have h := greens_identity_annular_reduction hn f hf_smooth hf_supp x ε hε


    have h_split : surfaceIntegralLP {z : Fin n → ℝ | euclidNormLP z = ε}
        (fun σ => fundamentalSolution n σ * normalDerivLP {z | euclidNormLP z ≥ ε}
          (fun z => f (x - z)) σ -
          f (x - σ) * normalDerivLP {z | euclidNormLP z ≥ ε}
            (fundamentalSolution n) σ) = grad ε + fterm ε := by
      unfold surfaceIntegralLP
      rw [MeasureTheory.integral_sub
        (surfaceIntegral_integrable_LP_early _ _)
        (surfaceIntegral_integrable_LP_early _ _)]
      simp [grad, fterm, surfaceIntegralLP]; ring
    linarith
  ·
    exact surface_gradient_term_bounded hn f hf_smooth hf_supp x
  ·
    exact surface_fvalue_term_limit hn f hf_smooth hf_supp x

/-- Stronger version of the far-field decomposition: the "gradient term" actually
tends to $0$ (rather than merely being $O(\varepsilon)$). -/
theorem far_field_greens_identity_decomposition {n : ℕ} (hn : n ≥ 3)
    (f : (Fin n → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f)
    (x : Fin n → ℝ) :
    ∃ (gradient_term f_term : ℝ → ℝ),

      (∀ ε > 0, (∫ y in {z : Fin n → ℝ | euclidNormLP z ≥ ε},
        fundamentalSolution n y * laplacianLP (fun z => f (x - z)) y) =
          gradient_term ε + f_term ε) ∧

      Filter.Tendsto gradient_term (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧

      Filter.Tendsto f_term (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by

  obtain ⟨grad_term, f_term, h_eq, ⟨C, h_bound⟩, h_f⟩ :=
    far_field_greens_computation hn f hf_smooth hf_supp x
  refine ⟨grad_term, f_term, h_eq, ?_, h_f⟩

  apply squeeze_zero_norm'
  · exact eventually_nhdsWithin_of_forall fun ε hε => h_bound ε (Set.mem_Ioi.mp hε)
  · have h1 : Filter.Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have h2 := h1.const_mul C
    simp at h2
    exact h2

/-- The far-field integral converges to $f(x)$: $\int_{|y|\ge\varepsilon}
\Phi(y)\,\Delta f(x-y)\,dy \to f(x)$ as $\varepsilon \to 0^+$. -/
theorem far_field_integral_limit {n : ℕ} (hn : n ≥ 3)
    (f : (Fin n → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f)
    (x : Fin n → ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ y in {z : Fin n → ℝ | euclidNormLP z ≥ ε},
        fundamentalSolution n y * laplacianLP (fun z => f (x - z)) y)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by

  obtain ⟨grad_term, f_term, h_eq, h_grad, h_f⟩ :=
    far_field_greens_identity_decomposition hn f hf_smooth hf_supp x

  have h_sum : Filter.Tendsto (fun ε => grad_term ε + f_term ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by
    have := h_grad.add h_f
    rwa [zero_add] at this

  exact h_sum.congr' (Filter.EventuallyEq.symm
    (eventually_nhdsWithin_of_forall fun ε hε => h_eq ε (Set.mem_Ioi.mp hε)))

/-- Integrability of the convolution kernel: $y \mapsto \Phi(x - y)\,\Delta u(y)$ is
integrable on $\Omega$ when $u$ is $C^2$ on $\overline{\Omega}$. -/
theorem fundamentalSolution_laplacian_integrableOn {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω)) (hΩ : IsOpen Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    IntegrableOn (fun y => fundamentalSolution n (x - y) * laplacianLP u y) Ω := by sorry

/-- Integrability of the convolution integrand $y \mapsto \Phi(y)\,\Delta f(x-y)$ on
$\mathbb{R}^n$, for smooth compactly supported $f$. -/
theorem convolution_integrand_integrable {n : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f)
    (x : Fin n → ℝ) :
    Integrable (fun y => fundamentalSolution n y * laplacianLP (fun z => f (x - z)) y) := by

  have hfun_eq : (fun y => fundamentalSolution n y * laplacianLP (fun z => f (x - z)) y) =
      (fun y => fundamentalSolution n (0 - y) * laplacianLP (fun z => f (x - z)) y) := by
    ext y; rw [zero_sub, fundamentalSolution_neg]
  rw [hfun_eq]

  rw [← integrableOn_univ]
  have hu : ContDiffOn ℝ 2 (fun z => f (x - z)) (closure Set.univ) := by
    rw [closure_univ]
    exact ((hf_smooth.comp (contDiff_const.sub contDiff_id)).of_le le_top).contDiffOn
  exact fundamentalSolution_laplacian_integrableOn (fun z => f (x - z)) Set.univ
    hu isOpen_univ 0 (mem_univ 0)

/-- Decomposition of an integral on $\mathbb{R}^n$ as a sum of an integral over the
open ball $\{|y|<\varepsilon\}$ and over its complement $\{|y|\ge\varepsilon\}$. -/
theorem integral_split_ball_complement {n : ℕ}
    (g : (Fin n → ℝ) → ℝ) (ε : ℝ) (_hε : ε > 0)
    (hg : Integrable g) :
    ∫ y, g y = (∫ y in {z : Fin n → ℝ | euclidNormLP z < ε}, g y) +
      (∫ y in {z : Fin n → ℝ | euclidNormLP z ≥ ε}, g y) := by
  have hms : MeasurableSet {z : Fin n → ℝ | euclidNormLP z < ε} :=
    (isOpen_lt continuous_euclidNormLP continuous_const).measurableSet
  have hcompl : {z : Fin n → ℝ | euclidNormLP z < ε}ᶜ =
      {z : Fin n → ℝ | euclidNormLP z ≥ ε} := by
    ext z; simp [not_lt]
  rw [← hcompl]
  exact (integral_add_compl hms hg).symm

/-- Core PDE identity for $n \ge 3$ (Theorem 1.1): the Laplacian of the convolution
$u = \Phi * f$ recovers $f$, i.e.\ $\Delta(\Phi * f) = f$ on $\mathbb{R}^n$. -/
theorem poisson_convolution_laplacian {n : ℕ} (hn : n ≥ 3)
    (f : (Fin n → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f)
    (x : Fin n → ℝ) :
    laplacianLP (phiConvolutionLP n f) x = f x := by

  have h_eq := laplacian_convolution_eq_integral hn f hf_smooth hf_supp x

  set g := fun y => fundamentalSolution n y * laplacianLP (fun z => f (x - z)) y with hg_def

  have hg_int : Integrable g := convolution_integrand_integrable f hf_smooth hf_supp x


  have h_near := near_field_integral_vanishes hn f hf_smooth hf_supp x
  have h_far := far_field_integral_limit hn f hf_smooth hf_supp x


  have h_sum_limit : Filter.Tendsto
      (fun ε : ℝ => (∫ y in {z | euclidNormLP z < ε}, g y) +
        (∫ y in {z | euclidNormLP z ≥ ε}, g y))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 + f x)) := by
    exact Filter.Tendsto.add h_near h_far
  simp only [zero_add] at h_sum_limit

  have h_sum_eq : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (∫ y in {z | euclidNormLP z < ε}, g y) +
      (∫ y in {z | euclidNormLP z ≥ ε}, g y) = ∫ y, g y := by
    apply eventually_nhdsWithin_of_forall
    intro ε hε
    rw [Set.mem_Ioi] at hε
    exact (integral_split_ball_complement g ε hε hg_int).symm

  have h_integral_eq : ∫ y, g y = f x := by
    have h_const : Filter.Tendsto (fun _ : ℝ => ∫ y, g y)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ y, g y)) :=
      tendsto_const_nhds
    exact tendsto_nhds_unique
      (Filter.Tendsto.congr' (Filter.EventuallyEq.symm h_sum_eq) h_const)
      h_sum_limit

  rw [h_eq, h_integral_eq]

/-- Universal-quantifier form: for $n \ge 3$, $u = \Phi * f$ solves
$\Delta u = f$ everywhere on $\mathbb{R}^n$. -/
theorem poisson_equation_solution {n : ℕ} (hn : n ≥ 3)
    (f : (Fin n → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) :
    ∀ x : Fin n → ℝ, laplacianLP (phiConvolutionLP n f) x = f x := by
  intro x
  exact poisson_convolution_laplacian hn f hf_smooth hf_supp x

/-- $n = 2$ variant of `laplacian_convolution_eq_integral`: the Laplacian of the
convolution $\Phi * f$ equals $\int \Phi(y)\,\Delta f(x-y)\,dy$. -/
theorem laplacian_convolution_eq_integral_n2
    (f : (Fin 2 → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f)
    (x : Fin 2 → ℝ) :
    laplacianLP (phiConvolutionLP 2 f) x =
      ∫ y, fundamentalSolution 2 y * laplacianLP (fun z => f (x - z)) y := by sorry

/-- $n = 2$ near-field bound: $\bigl|\int_{|y|<\varepsilon} \Phi(y)\,
\Delta f(x-y)\,dy\bigr| \le C\,\varepsilon^2\,|\log \varepsilon|$ for $0 < \varepsilon < 1$. -/
theorem near_field_spherical_bound_n2
    (f : (Fin 2 → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f)
    (x : Fin 2 → ℝ) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ‖∫ y in {z : Fin 2 → ℝ | euclidNormLP z < ε},
        fundamentalSolution 2 y * laplacianLP (fun z => f (x - z)) y‖ ≤
          C * (ε ^ 2 * |Real.log ε|) := by sorry

/-- Auxiliary limit for $n = 2$: $\varepsilon^2\,|\log \varepsilon| \to 0$ as
$\varepsilon \to 0^+$. -/
theorem eps_sq_abs_log_tendsto_zero :
    Filter.Tendsto (fun ε : ℝ => ε ^ 2 * |Real.log ε|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h1 := tendsto_log_mul_rpow_nhdsGT_zero (by positivity : (0 : ℝ) < 2)
  rw [tendsto_zero_iff_abs_tendsto_zero] at h1
  refine h1.congr' ?_
  apply eventually_nhdsWithin_of_forall
  intro x hx
  rw [Set.mem_Ioi] at hx
  simp only [Function.comp_apply]
  rw [abs_mul, abs_of_nonneg (rpow_nonneg hx.le 2)]
  rw [show x ^ (2:ℝ) = (x:ℝ) ^ (2:ℕ) from by norm_cast]
  ring

/-- $n = 2$ near-field vanishing: the integral over the small ball vanishes as
$\varepsilon \to 0^+$. -/
theorem near_field_integral_vanishes_n2
    (f : (Fin 2 → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f)
    (x : Fin 2 → ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ y in {z : Fin 2 → ℝ | euclidNormLP z < ε},
        fundamentalSolution 2 y * laplacianLP (fun z => f (x - z)) y)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  obtain ⟨C, hbound⟩ := near_field_spherical_bound_n2 f hf_smooth hf_supp x
  apply squeeze_zero_norm' (a := fun ε => C * (ε ^ 2 * |Real.log ε|))
  ·
    have h_both : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), ε > 0 ∧ ε < 1 := by
      apply Filter.Eventually.and
      · exact eventually_nhdsWithin_of_forall fun ε hε => Set.mem_Ioi.mp hε
      · exact Filter.Eventually.filter_mono nhdsWithin_le_nhds
            (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))
    exact h_both.mono fun ε ⟨hε_pos, hε_lt1⟩ => hbound ε hε_pos hε_lt1
  · have h2 := eps_sq_abs_log_tendsto_zero.const_mul C
    simp at h2
    exact h2

/-- $n = 2$ far-field Green's identity decomposition: same shape as the $n \ge 3$
case but with the logarithmic fundamental solution. -/
theorem far_field_greens_identity_decomposition_n2
    (f : (Fin 2 → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f)
    (x : Fin 2 → ℝ) :
    ∃ (gradient_term f_term : ℝ → ℝ),
      (∀ ε > 0, (∫ y in {z : Fin 2 → ℝ | euclidNormLP z ≥ ε},
        fundamentalSolution 2 y * laplacianLP (fun z => f (x - z)) y) =
          gradient_term ε + f_term ε) ∧
      Filter.Tendsto gradient_term (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto f_term (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by sorry

/-- $n = 2$ far-field integral limit: $\int_{|y|\ge\varepsilon} \Phi(y)\,
\Delta f(x-y)\,dy \to f(x)$ as $\varepsilon \to 0^+$. -/
theorem far_field_integral_limit_n2
    (f : (Fin 2 → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f)
    (x : Fin 2 → ℝ) :
    Filter.Tendsto
      (fun ε : ℝ => ∫ y in {z : Fin 2 → ℝ | euclidNormLP z ≥ ε},
        fundamentalSolution 2 y * laplacianLP (fun z => f (x - z)) y)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by
  obtain ⟨grad_term, f_term, h_eq, h_grad, h_f⟩ :=
    far_field_greens_identity_decomposition_n2 f hf_smooth hf_supp x
  have h_sum : Filter.Tendsto (fun ε => grad_term ε + f_term ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x)) := by
    have := h_grad.add h_f
    rwa [zero_add] at this
  exact h_sum.congr' (Filter.EventuallyEq.symm
    (eventually_nhdsWithin_of_forall fun ε hε => h_eq ε (Set.mem_Ioi.mp hε)))

/-- $n = 2$ version of the Poisson formula: $\Delta(\Phi * f) = f$ on $\mathbb{R}^2$. -/
theorem poisson_convolution_laplacian_n2
    (f : (Fin 2 → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f)
    (x : Fin 2 → ℝ) :
    laplacianLP (phiConvolutionLP 2 f) x = f x := by

  have h_eq := laplacian_convolution_eq_integral_n2 f hf_smooth hf_supp x
  set g := fun y => fundamentalSolution 2 y * laplacianLP (fun z => f (x - z)) y with hg_def

  have hg_int : Integrable g := convolution_integrand_integrable f hf_smooth hf_supp x

  have h_near := near_field_integral_vanishes_n2 f hf_smooth hf_supp x
  have h_far := far_field_integral_limit_n2 f hf_smooth hf_supp x

  have h_sum_limit : Filter.Tendsto
      (fun ε : ℝ => (∫ y in {z | euclidNormLP z < ε}, g y) +
        (∫ y in {z | euclidNormLP z ≥ ε}, g y))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (0 + f x)) := by
    exact Filter.Tendsto.add h_near h_far
  simp only [zero_add] at h_sum_limit
  have h_sum_eq : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (∫ y in {z | euclidNormLP z < ε}, g y) +
      (∫ y in {z | euclidNormLP z ≥ ε}, g y) = ∫ y, g y := by
    apply eventually_nhdsWithin_of_forall
    intro ε hε
    rw [Set.mem_Ioi] at hε
    exact (integral_split_ball_complement g ε hε hg_int).symm
  have h_integral_eq : ∫ y, g y = f x := by
    have h_const : Filter.Tendsto (fun _ : ℝ => ∫ y, g y)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ y, g y)) :=
      tendsto_const_nhds
    exact tendsto_nhds_unique
      (Filter.Tendsto.congr' (Filter.EventuallyEq.symm h_sum_eq) h_const)
      h_sum_limit
  rw [h_eq, h_integral_eq]

/-- Smoothness of convolution: convolution of a locally integrable kernel $K$ with
a smooth compactly supported function $g$ is smooth, $K * g \in C^\infty$. -/
theorem contDiff_convolution_locallyIntegrable_compactSupport {n : ℕ} (_hn : n ≥ 2)
    (K : (Fin n → ℝ) → ℝ)
    (_hK : MeasureTheory.LocallyIntegrable K (volume : Measure (Fin n → ℝ)))
    (g : (Fin n → ℝ) → ℝ)
    (_hg_smooth : ContDiff ℝ ⊤ g) (_hg_supp : HasCompactSupport g) :
    ContDiff ℝ ⊤ (fun x => ∫ y, K (x - y) * g y) := by sorry

/-- The Poisson solution $u = \Phi * f$ is smooth: $u \in C^\infty(\mathbb{R}^n)$
whenever $f \in C_c^\infty(\mathbb{R}^n)$. -/
theorem poisson_solution_smooth {n : ℕ} (hn : n ≥ 2)
    (f : (Fin n → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) :
    ContDiff ℝ ⊤ (phiConvolutionLP n f) :=
  contDiff_convolution_locallyIntegrable_compactSupport hn
    (fundamentalSolution n) (fundamentalSolution_locallyIntegrable hn)
    f hf_smooth hf_supp

/-- Pointwise decay estimate at infinity for $n \ge 3$: there exists $C > 0$ such
that $|(\Phi * f)(x)| \le C / |x|^{n-2}$ for $|x| \ge 1$. -/
theorem poisson_solution_decay_nge3 {n : ℕ} (hn : n ≥ 3)
    (f : (Fin n → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) :
    ∃ C : ℝ, C > 0 ∧ ∀ x : Fin n → ℝ, euclidNormLP x ≥ 1 →
      |phiConvolutionLP n f x| ≤ C / (euclidNormLP x) ^ (n - 2) := by
  have hn2_ne : n ≠ 2 := by omega
  have hn2 : n ≥ 2 := Nat.le_of_succ_le hn
  have hω_pos := unitSphereArea_pos n
  have hu_cont : Continuous (phiConvolutionLP n f) :=
    (poisson_solution_smooth hn2 f hf_smooth hf_supp).continuous
  have hf_integrable : Integrable f := hf_smooth.continuous.integrable_of_hasCompactSupport hf_supp

  obtain ⟨R, hR_pos, hR_bd⟩ : ∃ R : ℝ, R > 0 ∧ ∀ y, y ∈ tsupport f → euclidNormLP y ≤ R := by
    have himg := hf_supp.isCompact.image continuous_euclidNormLP
    obtain ⟨M, hM⟩ := himg.isBounded.exists_norm_le
    refine ⟨|M| + 1, by positivity, fun y hy => ?_⟩
    have hmem := hM (euclidNormLP y) (Set.mem_image_of_mem euclidNormLP hy)
    simp [Real.norm_eq_abs] at hmem
    rw [abs_of_nonneg (GE.ge.le (euclidNormLP_nonneg y))] at hmem

    linarith [le_abs_self M]
  set K := 2 * R + 1
  have hK_pos : K > 0 := by positivity

  have hS_compact : IsCompact {x : Fin n → ℝ | 1 ≤ euclidNormLP x ∧ euclidNormLP x ≤ K} :=
    (isCompact_closedBall (0 : Fin n → ℝ) K).of_isClosed_subset
      (IsClosed.inter (isClosed_le continuous_const continuous_euclidNormLP)
        (isClosed_le continuous_euclidNormLP continuous_const))
      (fun x ⟨_, hxK⟩ => by
        simp [Metric.closedBall]
        exact le_trans (norm_le_euclidNormLP x) hxK)
  obtain ⟨B, hB_bd⟩ := hS_compact.exists_bound_of_continuousOn hu_cont.continuousOn
  set If := ∫ y, ‖f y‖
  have hIf_nonneg : (0 : ℝ) ≤ If := integral_nonneg (fun _ => norm_nonneg _)

  set C := (|B| + 1) * K ^ (n - 2) + 2 ^ (n - 2) * If / unitSphereArea n + 1
  have hC_pos : C > 0 := by
    have : (|B| + 1) * K ^ (n - 2) ≥ 0 := by positivity
    have : (2 : ℝ) ^ (n - 2) * If / unitSphereArea n ≥ 0 :=
      div_nonneg (mul_nonneg (by positivity) hIf_nonneg) (le_of_lt hω_pos)
    linarith
  exact ⟨C, hC_pos, fun x hx => by
    have hx_pos : euclidNormLP x > 0 := lt_of_lt_of_le one_pos hx
    have hxm_pos : euclidNormLP x ^ (n - 2) > 0 := pow_pos hx_pos (n - 2)
    by_cases hxK : euclidNormLP x ≤ K
    ·
      have h1 : |phiConvolutionLP n f x| ≤ |B| + 1 := by
        rw [← Real.norm_eq_abs]; linarith [le_abs_self B, hB_bd x ⟨hx, hxK⟩]
      calc |phiConvolutionLP n f x| ≤ |B| + 1 := h1
        _ ≤ C / euclidNormLP x ^ (n - 2) := by
            rw [le_div_iff₀ hxm_pos]
            calc (|B| + 1) * euclidNormLP x ^ (n - 2)
                ≤ (|B| + 1) * K ^ (n - 2) :=
                  mul_le_mul_of_nonneg_left
                    (pow_le_pow_left₀ (le_of_lt hx_pos) hxK (n - 2)) (by positivity)
              _ ≤ C := by
                  show _ ≤ (|B| + 1) * K ^ (n - 2) + 2 ^ (n - 2) * If / unitSphereArea n + 1
                  linarith [div_nonneg (mul_nonneg (pow_nonneg (by norm_num : (2:ℝ) ≥ 0) (n - 2))
                    hIf_nonneg) (le_of_lt hω_pos)]
    ·
      simp only [not_le] at hxK

      have pointwise : ∀ y, ‖fundamentalSolution n (x - y) * f y‖ ≤
          2 ^ (n - 2) / (unitSphereArea n * euclidNormLP x ^ (n - 2)) * ‖f y‖ := by
        intro y
        by_cases hfy : f y = 0
        · simp [hfy]
        · have hy_R : euclidNormLP y ≤ R :=
            hR_bd y (subset_tsupport f (Function.mem_support.mpr hfy))
          have hxy_lower : euclidNormLP (x - y) ≥ euclidNormLP x / 2 := by
            linarith [euclidNormLP_sub_le x y]
          have hxy_pos : euclidNormLP (x - y) > 0 := by
            linarith [ge_iff_le.mp (euclidNormLP_nonneg (x - y))]
          rw [norm_mul, show fundamentalSolution n (x - y) =
            -1 / (unitSphereArea n * euclidNormLP (x - y) ^ (n - 2)) from by
            unfold fundamentalSolution; simp [hn2_ne],
            Real.norm_eq_abs, abs_div, abs_neg, abs_one,
            abs_of_pos (mul_pos hω_pos (pow_pos hxy_pos (n - 2)))]
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [div_le_div_iff₀ (mul_pos hω_pos (pow_pos hxy_pos (n - 2)))
                               (mul_pos hω_pos (pow_pos hx_pos (n - 2)))]
          nlinarith [mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by linarith : euclidNormLP x / 2 ≥ 0) hxy_lower (n - 2))
            (show (2 : ℝ) ^ (n - 2) ≥ 0 from by positivity),
            show 2 ^ (n - 2) * (euclidNormLP x / 2) ^ (n - 2) = euclidNormLP x ^ (n - 2) from by
              rw [div_pow]; field_simp]

      have hint : ∫ y, ‖fundamentalSolution n (x - y) * f y‖ ≤
          2 ^ (n - 2) / (unitSphereArea n * euclidNormLP x ^ (n - 2)) * If := by
        have h1 := integral_mono_of_nonneg
          (Filter.Eventually.of_forall (fun y => norm_nonneg (fundamentalSolution n (x - y) * f y)))
          ((hf_integrable.norm).const_mul (2 ^ (n - 2) / (unitSphereArea n * euclidNormLP x ^ (n - 2))))
          (Filter.Eventually.of_forall pointwise)
        rwa [integral_const_mul] at h1

      have h_abs_le : |phiConvolutionLP n f x| ≤
          2 ^ (n - 2) / (unitSphereArea n * euclidNormLP x ^ (n - 2)) * If :=
        le_trans (le_trans (le_of_eq ((Real.norm_eq_abs _).symm)) (norm_integral_le_integral_norm _)) hint

      have h' : 2 ^ (n - 2) * If ≤ C * unitSphereArea n := by
        have : 2 ^ (n - 2) * If / unitSphereArea n ≤ C := by
          show _ ≤ (|B| + 1) * K ^ (n - 2) + 2 ^ (n - 2) * If / unitSphereArea n + 1
          linarith [mul_nonneg (pow_nonneg (show K ≥ (0 : ℝ) from by positivity) (n - 2))
            (show |B| + 1 ≥ 0 from by positivity)]
        rwa [div_le_iff₀ hω_pos] at this
      calc |phiConvolutionLP n f x|
          ≤ 2 ^ (n - 2) / (unitSphereArea n * euclidNormLP x ^ (n - 2)) * If := h_abs_le
        _ ≤ C / euclidNormLP x ^ (n - 2) := by
            rw [div_mul_eq_mul_div]
            rw [div_le_div_iff₀ (mul_pos hω_pos hxm_pos) hxm_pos]
            nlinarith⟩

/-- Decay at infinity (consequence of the $1/|x|^{n-2}$ bound): for $n \ge 3$,
$(\Phi * f)(x) \to 0$ as $|x| \to \infty$. -/
theorem poisson_solution_tendsto_zero_nge3 {n : ℕ} (hn : n ≥ 3)
    (f : (Fin n → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) :
    Filter.Tendsto (phiConvolutionLP n f) (Filter.cocompact (Fin n → ℝ)) (nhds 0) := by

  obtain ⟨C, hC_pos, hC_bd⟩ := poisson_solution_decay_nge3 hn f hf_smooth hf_supp

  have h_euclid_tendsto : Tendsto (fun x : Fin n → ℝ => euclidNormLP x) (cocompact _) atTop :=
    tendsto_atTop_mono (fun x => norm_le_euclidNormLP x) tendsto_norm_cocompact_atTop

  have hn2_ne : n - 2 ≠ 0 := by omega
  have h_pow_tendsto : Tendsto (fun x : Fin n → ℝ => (euclidNormLP x) ^ (n - 2))
      (cocompact _) atTop :=
    (tendsto_pow_atTop hn2_ne).comp h_euclid_tendsto

  have h_bound_tendsto : Tendsto (fun x : Fin n → ℝ => C / (euclidNormLP x) ^ (n - 2))
      (cocompact _) (nhds 0) := by
    have h_inv : Tendsto (fun x : Fin n → ℝ => ((euclidNormLP x) ^ (n - 2))⁻¹)
        (cocompact _) (nhds 0) :=
      tendsto_inv_atTop_zero.comp h_pow_tendsto
    have heq : (fun x : Fin n → ℝ => C / (euclidNormLP x) ^ (n - 2)) =
        (fun x => C * ((euclidNormLP x) ^ (n - 2))⁻¹) := by
      ext x; rw [div_eq_mul_inv]
    rw [heq]
    exact (mul_zero C) ▸ tendsto_const_nhds.mul h_inv

  have h_euclid_ge : ∀ᶠ x in cocompact (Fin n → ℝ), euclidNormLP x ≥ 1 :=
    (tendsto_norm_cocompact_atTop.eventually_ge_atTop 1).mono
      (fun x hx => le_trans hx (norm_le_euclidNormLP x))
  have h_bound_ev : ∀ᶠ x in cocompact (Fin n → ℝ),
      ‖phiConvolutionLP n f x‖ ≤ C / (euclidNormLP x) ^ (n - 2) :=
    h_euclid_ge.mono (fun x hx => by
      simp only [Real.norm_eq_abs]
      exact hC_bd x hx)
  exact squeeze_zero_norm' h_bound_ev h_bound_tendsto

/-- Uniqueness for Poisson's equation under decay at infinity (Liouville-type
argument): two smooth solutions of $\Delta u = f$ that both vanish at infinity must
agree, for $n \ge 3$. -/
theorem poisson_solution_unique_nge3 {n : ℕ} (hn : n ≥ 3)
    (u₁ u₂ : (Fin n → ℝ) → ℝ) (f : (Fin n → ℝ) → ℝ)
    (hu₁_smooth : ContDiff ℝ ⊤ u₁) (hu₂_smooth : ContDiff ℝ ⊤ u₂)
    (hu₁_pde : ∀ x, laplacianLP u₁ x = f x)
    (hu₂_pde : ∀ x, laplacianLP u₂ x = f x)
    (hu₁_decay : Filter.Tendsto u₁ (Filter.cocompact (Fin n → ℝ)) (nhds 0))
    (hu₂_decay : Filter.Tendsto u₂ (Filter.cocompact (Fin n → ℝ)) (nhds 0)) :
    u₁ = u₂ := by

  ext x
  suffices h : u₁ x - u₂ x = 0 by linarith

  set w : (Fin n → ℝ) → ℝ := fun y => u₁ y - u₂ y

  have hw_laplacian : ∀ y, laplacianLP w y = 0 := by
    intro y
    have hlin : laplacianLP w y = laplacianLP u₁ y - laplacianLP u₂ y := by
      simp only [laplacianLP, w]
      rw [← Finset.sum_sub_distrib]
      congr 1; ext i

      have heq : (fun z => fderiv ℝ (fun t => u₁ t - u₂ t) z (Pi.single i 1)) =
          (fun z => fderiv ℝ u₁ z (Pi.single i 1) - fderiv ℝ u₂ z (Pi.single i 1)) := by
        ext z
        have hd₁z : DifferentiableAt ℝ u₁ z :=
          hu₁_smooth.contDiffAt.differentiableAt (hn := by simp)
        have hd₂z : DifferentiableAt ℝ u₂ z :=
          hu₂_smooth.contDiffAt.differentiableAt (hn := by simp)

        have h := fderiv_sub hd₁z hd₂z
        simp only [ContinuousLinearMap.sub_apply] at h
        rw [show fderiv ℝ (fun t => u₁ t - u₂ t) z = fderiv ℝ u₁ z - fderiv ℝ u₂ z from
          fderiv_sub hd₁z hd₂z]
        simp [ContinuousLinearMap.sub_apply]
      rw [heq]

      have hd₁' : DifferentiableAt ℝ (fun z => fderiv ℝ u₁ z (Pi.single i 1)) y :=
        ((hu₁_smooth.fderiv_right (m := ⊤) le_top).clm_apply contDiff_const).contDiffAt.differentiableAt
          (hn := by simp)
      have hd₂' : DifferentiableAt ℝ (fun z => fderiv ℝ u₂ z (Pi.single i 1)) y :=
        ((hu₂_smooth.fderiv_right (m := ⊤) le_top).clm_apply contDiff_const).contDiffAt.differentiableAt
          (hn := by simp)

      rw [show fderiv ℝ (fun z => fderiv ℝ u₁ z (Pi.single i 1) - fderiv ℝ u₂ z (Pi.single i 1)) y =
        fderiv ℝ (fun z => fderiv ℝ u₁ z (Pi.single i 1)) y -
        fderiv ℝ (fun z => fderiv ℝ u₂ z (Pi.single i 1)) y from
        fderiv_sub hd₁' hd₂']
      simp [ContinuousLinearMap.sub_apply]

    rw [hlin, hu₁_pde y, hu₂_pde y, sub_self]

  have hw_harmonic : CM7.IsHarmonic w Set.univ :=
    ⟨((hu₁_smooth.sub hu₂_smooth).of_le le_top).contDiffOn, fun y _ => hw_laplacian y⟩


  have hw_smooth2 : ContDiff ℝ 2 w :=
    (hu₁_smooth.sub hu₂_smooth).of_le le_top

  have hw_decay : Filter.Tendsto w (Filter.cocompact (Fin n → ℝ)) (nhds 0) := by
    have h := hu₁_decay.sub hu₂_decay
    simp only [sub_zero] at h
    exact h


  have hw_cont : Continuous w := (hu₁_smooth.sub hu₂_smooth).continuous
  have hw_bdd : ∃ M : ℝ, ∀ y, w y ≤ M := by

    have hcpt : IsCompact (insert (0 : ℝ) (Set.range w)) :=
      hw_decay.isCompact_insert_range_of_cocompact hw_cont
    have hbdd : Bornology.IsBounded (Set.range w) :=
      (hcpt.isBounded.subset (Set.subset_insert _ _))
    rw [Metric.isBounded_iff_subset_ball 0] at hbdd
    obtain ⟨r, hr⟩ := hbdd
    exact ⟨r, fun y => by
      have hwy : w y ∈ Set.range w := Set.mem_range_self y
      have := hr hwy
      rw [Metric.mem_ball, Real.dist_eq] at this
      linarith [abs_lt.mp this |>.2]⟩

  obtain ⟨M, hM⟩ := hw_bdd
  obtain ⟨c, hc⟩ := PoissonHarnack.liouville_theorem w hw_harmonic hw_smooth2 M (Or.inr hM)

  have hc_zero : c = 0 := by

    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    haveI : Nontrivial (Fin n → ℝ) := Function.nontrivial
    haveI : NoncompactSpace (Fin n → ℝ) := inferInstance


    have hw_eq_c : w = Function.const _ c := funext hc
    have htends_c : Filter.Tendsto w (Filter.cocompact (Fin n → ℝ)) (nhds c) := by
      rw [hw_eq_c]; exact tendsto_const_nhds
    exact (tendsto_nhds_unique hw_decay htends_c).symm

  have := hc x
  linarith [hc_zero]

/-- **Theorem 1.1** (CM7). For $n \ge 3$ and $f \in C_c^\infty(\mathbb{R}^n)$, the
convolution $u = \Phi * f$ is the unique smooth solution to Poisson's equation
$\Delta u = f$ that vanishes at infinity, with the explicit decay rate
$|u(x)| \lesssim |x|^{2-n}$. -/
theorem poisson_theorem_1_1 {n : ℕ} (hn : n ≥ 3)
    (f : (Fin n → ℝ) → ℝ)
    (hf_smooth : ContDiff ℝ ⊤ f) (hf_supp : HasCompactSupport f) :
    (∀ x, laplacianLP (phiConvolutionLP n f) x = f x) ∧
    ContDiff ℝ ⊤ (phiConvolutionLP n f) ∧
    (∃ C > 0, ∀ x : Fin n → ℝ, euclidNormLP x ≥ 1 →
      |phiConvolutionLP n f x| ≤ C / (euclidNormLP x) ^ (n - 2)) ∧
    Filter.Tendsto (phiConvolutionLP n f) (Filter.cocompact (Fin n → ℝ)) (nhds 0) ∧
    (∀ u₁ u₂ : (Fin n → ℝ) → ℝ,
      ContDiff ℝ ⊤ u₁ → ContDiff ℝ ⊤ u₂ →
      (∀ x, laplacianLP u₁ x = f x) → (∀ x, laplacianLP u₂ x = f x) →
      Filter.Tendsto u₁ (Filter.cocompact (Fin n → ℝ)) (nhds 0) →
      Filter.Tendsto u₂ (Filter.cocompact (Fin n → ℝ)) (nhds 0) →
      u₁ = u₂) := by
  have hn2 : n ≥ 2 := Nat.le_of_succ_le hn
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact poisson_equation_solution hn f hf_smooth hf_supp
  · exact poisson_solution_smooth hn2 f hf_smooth hf_supp
  · obtain ⟨C, hCpos, hCbd⟩ := poisson_solution_decay_nge3 hn f hf_smooth hf_supp
    exact ⟨C, hCpos, hCbd⟩
  · exact poisson_solution_tendsto_zero_nge3 hn f hf_smooth hf_supp
  · intro u₁ u₂ hu₁s hu₂s hu₁p hu₂p hu₁d hu₂d
    exact poisson_solution_unique_nge3 hn u₁ u₂ f hu₁s hu₂s hu₁p hu₂p hu₁d hu₂d

/-- Basic existence and uniqueness for the Dirichlet problem on a bounded Lipschitz
domain: for given $f$ (interior) and continuous boundary data $g$, there is a unique
$C^2$ solution $u$ of $\Delta u = f$ in $\Omega$ with $u = g$ on $\partial\Omega$. -/
theorem dirichlet_basic_existence {n : ℕ}
    (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hΩ_lip : IsLipschitzDomain Ω)
    (f : (Fin n → ℝ) → ℝ) (g : (Fin n → ℝ) → ℝ) (hg : ContinuousOn g (frontier Ω)) :
    ∃ u : (Fin n → ℝ) → ℝ,
      ContDiffOn ℝ 2 u Ω ∧
      ContinuousOn u (closure Ω) ∧
      (∀ x ∈ Ω, laplacianLP u x = f x) ∧
      (∀ σ ∈ frontier Ω, u σ = g σ) ∧
      (∀ u' : (Fin n → ℝ) → ℝ,
        ContDiffOn ℝ 2 u' Ω →
        ContinuousOn u' (closure Ω) →
        (∀ x ∈ Ω, laplacianLP u' x = f x) →
        (∀ σ ∈ frontier Ω, u' σ = g σ) →
        ∀ x ∈ closure Ω, u' x = u x) := by sorry

/-- Uniqueness for the Dirichlet problem on a bounded connected Lipschitz domain via
the maximum principle: if $u_1, u_2$ both solve $\Delta u = f$ in $\Omega$ with the
same boundary data $g$, then $u_1 = u_2$ on $\overline{\Omega}$. -/
theorem dirichlet_uniqueness {n : ℕ} (hn : 0 < n)
    (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω) (hΩc : IsConnected Ω)
    (hΩb : Bornology.IsBounded Ω)
    (u₁ u₂ : (Fin n → ℝ) → ℝ) (f g : (Fin n → ℝ) → ℝ)
    (hu₁_reg : ContDiffOn ℝ 2 u₁ Ω) (hu₁_cont : ContinuousOn u₁ (closure Ω))
    (hu₂_reg : ContDiffOn ℝ 2 u₂ Ω) (hu₂_cont : ContinuousOn u₂ (closure Ω))
    (hu₁_pde : ∀ x ∈ Ω, laplacianLP u₁ x = f x)
    (hu₂_pde : ∀ x ∈ Ω, laplacianLP u₂ x = f x)
    (hu₁_bdy : ∀ σ ∈ frontier Ω, u₁ σ = g σ)
    (hu₂_bdy : ∀ σ ∈ frontier Ω, u₂ σ = g σ) :
    ∀ x ∈ closure Ω, u₁ x = u₂ x := by

  have hw_harm : CM7.IsHarmonic (fun x => u₁ x - u₂ x) Ω := by
    constructor
    · exact hu₁_reg.sub hu₂_reg
    · intro x hx

      have hsub := CM7.laplacian_sub hΩ hu₁_reg hu₂_reg hx


      change CM7.Laplacian n (fun x => u₁ x - u₂ x) x = 0
      rw [hsub]
      have h1 : CM7.Laplacian n u₁ x = f x := hu₁_pde x hx
      have h2 : CM7.Laplacian n u₂ x = f x := hu₂_pde x hx
      linarith

  have hbdy : ∀ x ∈ frontier Ω, u₁ x = u₂ x := by
    intro x hx
    rw [hu₁_bdy x hx, hu₂_bdy x hx]

  have h_on_Ω : ∀ x ∈ Ω, u₁ x = u₂ x := by
    have h := @CM7.dirichlet_uniqueness n hn Ω hΩ hΩc hΩb
      (fun x => u₁ x - u₂ x) (fun _ => (0 : ℝ))
      hw_harm
      ⟨contDiffOn_const, fun x _ => by simp [CM7.Laplacian]⟩
      (fun x hx => by simp [hbdy x hx])
      (hu₁_cont.sub hu₂_cont)
      continuousOn_const
    intro x hx
    have := h x hx
    linarith


  intro x hx
  have h_cases : x ∈ Ω ∨ x ∈ frontier Ω := by
    rw [closure_eq_interior_union_frontier] at hx
    rwa [hΩ.interior_eq] at hx
  rcases h_cases with hxΩ | hxF
  · exact h_on_Ω x hxΩ
  · exact hbdy x hxF

/-- Bundled Green's function for the Dirichlet Laplacian on a domain $\Omega$:
$G(x, \cdot)$ vanishes on $\partial\Omega$, satisfies the distributional identity
$\Delta_y G(x, y) = -\delta_x$ (here stated against test functions), and comes with
the integrability data needed for Green's representation formula. -/
structure GreenFunctionLP (n : ℕ) (Ω : Set (Fin n → ℝ)) where
  G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ
  domain_open : IsOpen Ω
  boundary_zero : ∀ x ∈ Ω, ∀ σ ∈ frontier Ω, G x σ = 0
  distributional_pde : ∀ x ∈ Ω, ∀ φ : (Fin n → ℝ) → ℝ,
    ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    ∫ y, G x y * laplacianLP φ y = φ x
  G_differentiable : ∀ x ∈ Ω, ∀ σ, DifferentiableAt ℝ (G x) σ
  Phi_differentiable : ∀ x : Fin n → ℝ, ∀ σ,
    DifferentiableAt ℝ (fun y => fundamentalSolution n (x - y)) σ
  G_mul_integrableOn : ∀ x ∈ Ω, ∀ f : (Fin n → ℝ) → ℝ,
    Bornology.IsBounded Ω →
    IntegrableOn (fun y => G x y * f y) Ω
  Phi_mul_integrableOn : ∀ x : Fin n → ℝ, ∀ f : (Fin n → ℝ) → ℝ,
    Bornology.IsBounded Ω →
    IntegrableOn (fun y => fundamentalSolution n (x - y) * f y) Ω
  G_normalDeriv_integrableOn : ∀ x ∈ Ω, ∀ g : (Fin n → ℝ) → ℝ,
    IntegrableOn (fun σ => g σ * normalDerivLP Ω (G x) σ)
      (frontier Ω) (surfaceMeasure Ω)
  Phi_normalDeriv_integrableOn : ∀ x : Fin n → ℝ, ∀ g : (Fin n → ℝ) → ℝ,
    IntegrableOn (fun σ => g σ * normalDerivLP Ω (fun y => fundamentalSolution n (x - y)) σ)
      (frontier Ω) (surfaceMeasure Ω)

/-- **Weyl's lemma**: a function whose integral against $\Delta\psi$ vanishes for
every test function $\psi$ supported in $\Omega$ is necessarily smooth and harmonic
on $\Omega$. -/
theorem weyl_lemma_LP {n : ℕ} (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω)
    (u : (Fin n → ℝ) → ℝ)
    (h_dist : ∀ ψ : (Fin n → ℝ) → ℝ,
      ContDiff ℝ ⊤ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ∫ y, u y * laplacianLP ψ y = 0) :
    IsHarmonicLP u Ω := by sorry

/-- Distributional identity $\Delta \Phi = \delta_0$: for any test function $\psi$,
$\int \Phi(x - y)\,\Delta\psi(y)\,dy = \psi(x)$. -/
theorem fundamental_solution_distributional_delta_LP {n : ℕ}
    (hn : n ≥ 2)
    (x : Fin n → ℝ) (ψ : (Fin n → ℝ) → ℝ)
    (hψ : ContDiff ℝ ⊤ ψ) (hψs : HasCompactSupport ψ) :
    ∫ y, fundamentalSolution n (x - y) * laplacianLP ψ y = ψ x := by

  rw [convolution_substitution (laplacianLP ψ) x]


  have h_refl : ∀ y, laplacianLP ψ (x - y) = laplacianLP (fun z => ψ (x - z)) y := by
    intro y
    have := laplacianLP_chain_rule_sub ψ hψ x y


    rw [← this]


    symm
    unfold laplacianLP
    congr 1; ext i
    have hd : ∀ z, fderiv ℝ (fun x' => ψ (x' - y)) z = fderiv ℝ ψ (z - y) := by
      intro z; exact fderiv_comp_sub y
    rw [show (fun z => fderiv ℝ (fun x' => ψ (x' - y)) z (Pi.single i 1))
      = (fun z => fderiv ℝ ψ (z - y) (Pi.single i 1)) from by ext z; rw [hd z]]
    rw [show (fun z => fderiv ℝ ψ (z - y) (Pi.single i 1))
      = (fun z => (fun w => fderiv ℝ ψ w (Pi.single i 1)) (z - y)) from rfl]
    exact @fderiv_comp_sub ℝ _ (Fin n → ℝ) _ _ ℝ _ _
      (fun w => fderiv ℝ ψ w (Pi.single i 1)) x y ▸ rfl
  simp_rw [h_refl]


  rcases Nat.lt_or_ge n 3 with h_lt | h_ge
  ·
    have hn2 : n = 2 := by omega
    subst hn2
    have h_eq := laplacian_convolution_eq_integral_n2 ψ hψ hψs x
    rw [← h_eq]
    exact poisson_convolution_laplacian_n2 ψ hψ hψs x
  ·
    have h_eq := laplacian_convolution_eq_integral h_ge ψ hψ hψs x
    rw [← h_eq]
    exact poisson_convolution_laplacian h_ge ψ hψ hψs x

/-- Global integrability of $y \mapsto \Phi(x - y)\,\Delta\psi(y)$ when $\psi$ is
$C^2$ with compact support. -/
theorem fundamentalSolution_laplacian_integrable {n : ℕ}
    (x : Fin n → ℝ) (ψ : (Fin n → ℝ) → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (hψs : HasCompactSupport ψ) :
    Integrable (fun y => fundamentalSolution n (x - y) * laplacianLP ψ y) := by
  rw [← integrableOn_univ]
  exact fundamentalSolution_laplacian_integrableOn ψ Set.univ
    (by rw [closure_univ]; exact hψ.contDiffOn) isOpen_univ x (mem_univ x)

/-- Global integrability of $y \mapsto G(x, y)\,\Delta\psi(y)$, where $G$ is a Green
function and $\psi$ is a $C^2$ compactly supported test function. -/
theorem green_function_laplacian_integrable {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (gf : GreenFunctionLP n Ω) (x : Fin n → ℝ)
    (ψ : (Fin n → ℝ) → ℝ) (hψ : ContDiff ℝ 2 ψ) (hψs : HasCompactSupport ψ) :
    Integrable (fun y => gf.G x y * laplacianLP ψ y) := by sorry

/-- Joint integrability used when subtracting $\Phi$ and $G$ to obtain the corrector. -/
theorem corrector_integrand_integrable_LP {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (gf : GreenFunctionLP n Ω) (x : Fin n → ℝ)
    (ψ : (Fin n → ℝ) → ℝ) (hψ : ContDiff ℝ 2 ψ) (hψs : HasCompactSupport ψ) :
    Integrable (fun y => fundamentalSolution n (x - y) * laplacianLP ψ y) ∧
    Integrable (fun y => gf.G x y * laplacianLP ψ y) :=
  ⟨fundamentalSolution_laplacian_integrable x ψ hψ hψs,
   green_function_laplacian_integrable gf x ψ hψ hψs⟩

/-- The Green corrector $h(y) = \Phi(x - y) - G(x, y)$ is harmonic on $\Omega$: this
follows from Weyl's lemma since $\Delta_y(\Phi(x - y) - G(x, y)) = \delta_x - \delta_x = 0$
distributionally on $\Omega$. -/
theorem green_corrector_harmonic {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (hn : n ≥ 2)
    (gf : GreenFunctionLP n Ω) (x : Fin n → ℝ) (hx : x ∈ Ω) :
    IsHarmonicLP (fun y => fundamentalSolution n (x - y) - gf.G x y) Ω := by

  apply weyl_lemma_LP Ω gf.domain_open
  intro ψ hψ hψs hψΩ

  have hψ₂ : ContDiff ℝ 2 ψ := hψ.of_le le_top
  have h_phi := fundamental_solution_distributional_delta_LP hn x ψ hψ hψs
  have h_G := gf.distributional_pde x hx ψ hψ₂ hψs hψΩ
  have h_int := corrector_integrand_integrable_LP gf x ψ hψ₂ hψs

  have h_eq : (fun y => (fundamentalSolution n (x - y) - gf.G x y) * laplacianLP ψ y) =
    (fun y => fundamentalSolution n (x - y) * laplacianLP ψ y - gf.G x y * laplacianLP ψ y) := by
    ext y; ring

  rw [h_eq, integral_sub h_int.1 h_int.2, h_phi, h_G, sub_self]

/-- Classical Green-function decomposition: $G(x, y) = \Phi(x - y) - h(x, y)$, where
$h(x, \cdot)$ is harmonic on $\Omega$ and matches $\Phi(x - \cdot)$ on the boundary
$\partial\Omega$. -/
theorem green_function_decomposition {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (hn : n ≥ 2)
    (gf : GreenFunctionLP n Ω) :
    ∃ corrector : (Fin n → ℝ) → (Fin n → ℝ) → ℝ,
      (∀ x ∈ Ω, ∀ σ ∈ frontier Ω,
        corrector x σ = fundamentalSolution n (x - σ)) ∧
      (∀ x ∈ Ω, IsHarmonicLP (corrector x) Ω) ∧
      (∀ x y, gf.G x y = fundamentalSolution n (x - y) - corrector x y) := by

  refine ⟨fun x y => fundamentalSolution n (x - y) - gf.G x y, ?_, ?_, ?_⟩
  ·
    intro x hx σ hσ
    simp only
    rw [gf.boundary_zero x hx σ hσ]
    ring
  ·
    intro x hx
    exact green_corrector_harmonic hn gf x hx
  ·
    intro x y
    ring

/-- Finiteness of the surface measure of the sphere $\partial B(x, \varepsilon)$. -/
theorem surfaceMeasure_ball_sphere_finite {n : ℕ} (x : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    (surfaceMeasure (Metric.ball x ε)) (Metric.sphere x ε) < ⊤ := by sorry

/-- Upper bound on the surface measure of $\partial B(x, \varepsilon)$:
$\le n\,\omega_n\,\varepsilon^{n-1}$. -/
theorem surfaceMeasure_ball_sphere_real_le {n : ℕ} (x : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    (surfaceMeasure (Metric.ball x ε)).real (Metric.sphere x ε) ≤ ↑n * unitSphereArea n * ε ^ (n - 1) := by sorry

/-- The Euclidean L² norm of $x - \sigma$ coincides with the metric distance
$\operatorname{dist}(x, \sigma)$. -/
theorem euclidNormLP_eq_dist_LP {n : ℕ} (x σ : Fin n → ℝ) : euclidNormLP (x - σ) = dist x σ := by sorry

/-- On the sphere $\{|v| = \varepsilon\}$, the fundamental solution is bounded by
$1 / (\omega_n \varepsilon^{n-2})$ in absolute value. -/
theorem fundamentalSolution_abs_le_on_sphere (n : ℕ) (v : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hv : euclidNormLP v = ε) :
    |fundamentalSolution n v| ≤ 1 / (unitSphereArea n * ε ^ (n - 2)) := by sorry

/-- The surface integral of $f$ over the sphere $\partial B(x, \varepsilon)$. -/
noncomputable def sphereIntegralLP {n : ℕ} (x : Fin n → ℝ) (ε : ℝ) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∫ σ in frontier (Metric.ball x ε), f σ ∂(surfaceMeasure (Metric.ball x ε))

/-- Integrability axiom (used as glue): all functions are integrable against the
auxiliary surface measure on $\partial \Omega$ for this development. -/
theorem surfaceIntegral_integrable_LP {n : ℕ} (Ω : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) :
    MeasureTheory.IntegrableOn f (frontier Ω) (surfaceMeasure Ω) := by sorry

/-- Linearity (subtraction) of the surface integral on $\partial\Omega$. -/
theorem surfaceIntegralLP_sub {n : ℕ} (Ω : Set (Fin n → ℝ))
    (f g : (Fin n → ℝ) → ℝ) :
    surfaceIntegralLP Ω (fun σ => f σ - g σ) =
      surfaceIntegralLP Ω f - surfaceIntegralLP Ω g := by
  simp only [surfaceIntegralLP]
  exact MeasureTheory.integral_sub
    (surfaceIntegral_integrable_LP Ω f) (surfaceIntegral_integrable_LP Ω g)

/-- Linearity (subtraction) of the sphere integral over $\partial B(x, \varepsilon)$. -/
theorem sphereIntegralLP_sub {n : ℕ} (x : Fin n → ℝ) (ε : ℝ)
    (f g : (Fin n → ℝ) → ℝ) :
    sphereIntegralLP x ε (fun σ => f σ - g σ) =
      sphereIntegralLP x ε f - sphereIntegralLP x ε g := by
  simp only [sphereIntegralLP]
  exact MeasureTheory.integral_sub
    (surfaceIntegral_integrable_LP (Metric.ball x ε) f)
    (surfaceIntegral_integrable_LP (Metric.ball x ε) g)

/-- Combined Green's identity on $\Omega \setminus B(x, \varepsilon)$: the volume
integral on the punctured domain equals the surface integral over $\partial\Omega$
minus the one over the small sphere $\partial B(x, \varepsilon)$. -/
theorem greens_identity_on_omega_eps_combined {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω)) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) (ε : ℝ) (hε : 0 < ε) :
    (∫ y in Ω \ Metric.ball x ε, fundamentalSolution n (x - y) * laplacianLP u y)
    = surfaceIntegralLP Ω (fun σ =>
        fundamentalSolution n (x - σ) * normalDerivLP Ω u σ
        - u σ * normalDerivLP Ω (fun z => fundamentalSolution n (x - z)) σ)
      - sphereIntegralLP x ε (fun σ =>
        fundamentalSolution n (x - σ) * normalDerivLP Ω u σ
        - u σ * normalDerivLP Ω (fun z => fundamentalSolution n (x - z)) σ) := by sorry

/-- Algebraic cancellation
$\frac{1}{\omega_n \varepsilon^{n-2}} \cdot (n \omega_n \varepsilon^{n-1}) = n \varepsilon$. -/
theorem sphere_area_cancellation (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    1 / (unitSphereArea n * ε ^ (n - 2)) * (↑n * unitSphereArea n * ε ^ (n - 1)) = ↑n * ε := by sorry

/-- Bound on the sphere integral of $\Phi(x - \sigma)\,g(\sigma)$: $\le n\,M\,\varepsilon$
when $|g| \le M$ on the sphere. -/
theorem sphereIntegralLP_phi_bound {n : ℕ} (x : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε)
    (g : (Fin n → ℝ) → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hg_bound : ∀ σ : Fin n → ℝ, euclidNormLP (x - σ) = ε → |g σ| ≤ M) :
    ‖sphereIntegralLP x ε (fun σ => fundamentalSolution n (x - σ) * g σ)‖ ≤ ↑n * M * ε := by
  simp only [sphereIntegralLP]
  rw [frontier_ball x (ne_of_gt hε)]
  have h_surf := surfaceMeasure_ball_sphere_finite x ε hε
  have h_area := surfaceMeasure_ball_sphere_real_le x ε hε
  have h_integ_bound : ∀ σ ∈ Metric.sphere x ε,
      ‖fundamentalSolution n (x - σ) * g σ‖ ≤
        1 / (unitSphereArea n * ε ^ (n - 2)) * M := by
    intro σ hσ
    have hσ_norm : euclidNormLP (x - σ) = ε := by
      rw [euclidNormLP_eq_dist_LP]; rw [← dist_comm]; exact Metric.mem_sphere.mp hσ
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul
      (fundamentalSolution_abs_le_on_sphere n (x - σ) ε hε hσ_norm)
      (hg_bound σ hσ_norm) (abs_nonneg _)
      (div_nonneg zero_le_one (le_of_lt (mul_pos (unitSphereArea_pos n) (pow_pos hε (n - 2)))))
  have h_norm_bound := MeasureTheory.norm_setIntegral_le_of_norm_le_const
    (f := fun σ => fundamentalSolution n (x - σ) * g σ)
    (s := Metric.sphere x ε) (μ := surfaceMeasure (Metric.ball x ε))
    (C := 1 / (unitSphereArea n * ε ^ (n - 2)) * M) h_surf h_integ_bound
  calc ‖∫ σ in Metric.sphere x ε, fundamentalSolution n (x - σ) * g σ
        ∂surfaceMeasure (Metric.ball x ε)‖
      ≤ 1 / (unitSphereArea n * ε ^ (n - 2)) * M *
        (surfaceMeasure (Metric.ball x ε)).real (Metric.sphere x ε) := h_norm_bound
    _ ≤ 1 / (unitSphereArea n * ε ^ (n - 2)) * M *
        (↑n * unitSphereArea n * ε ^ (n - 1)) := by
        apply mul_le_mul_of_nonneg_left h_area
        exact mul_nonneg (div_nonneg zero_le_one
          (le_of_lt (mul_pos (unitSphereArea_pos n) (pow_pos hε (n - 2))))) hM
    _ = ↑n * M * ε := by
        have := sphere_area_cancellation n ε hε
        nlinarith [mul_pos (unitSphereArea_pos n) (pow_pos hε (n - 2))]

/-- Uniform bound on the normal derivative $\partial_\nu u$ over all of $\mathbb{R}^n$:
$|\partial_\nu u| \le n \cdot C$ where $C$ bounds $\|\nabla u\|$ on $\overline{\Omega}$. -/
theorem normalDerivLP_globally_bounded {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω))
    (hΩb : Bornology.IsBounded Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ : Fin n → ℝ, |normalDerivLP Ω u σ| ≤ M := by

  obtain ⟨C, hC_nn, hC_bound⟩ := fderiv_bounded_on_compact_closure u Ω hu hΩb

  refine ⟨↑n * C, mul_nonneg (Nat.cast_nonneg n) hC_nn, fun σ => ?_⟩
  by_cases hσ : σ ∈ frontier Ω
  ·
    have hσ_cl : σ ∈ closure Ω := frontier_subset_closure hσ
    unfold normalDerivLP
    calc |∑ i : Fin n, fderiv ℝ u σ (Pi.single i 1) * outwardUnitNormal Ω σ i|
        ≤ ∑ i : Fin n, |fderiv ℝ u σ (Pi.single i 1) * outwardUnitNormal Ω σ i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i : Fin n, |fderiv ℝ u σ (Pi.single i 1)| * |outwardUnitNormal Ω σ i| := by
          congr 1; ext i; exact abs_mul _ _
      _ ≤ ∑ i : Fin n, |fderiv ℝ u σ (Pi.single i 1)| * 1 := by
          gcongr with i _; exact outwardUnitNormal_component_le_one Ω σ i
      _ = ∑ i : Fin n, |fderiv ℝ u σ (Pi.single i 1)| := by simp [mul_one]
      _ ≤ ∑ _i : Fin n, C := by
          gcongr with i _
          have h1 : |fderiv ℝ u σ ((Pi.single i (1:ℝ) : Fin n → ℝ))| =
              ‖fderiv ℝ u σ ((Pi.single i (1:ℝ) : Fin n → ℝ))‖ := (Real.norm_eq_abs _).symm
          rw [h1]
          have h2 := (fderiv ℝ u σ).le_opNorm (Pi.single i (1:ℝ) : Fin n → ℝ)
          have h3 : ‖(Pi.single i (1 : ℝ) : Fin n → ℝ)‖ ≤ 1 := by
            rw [pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)]
            intro j; simp [Pi.single_apply]; split <;> simp
          calc ‖fderiv ℝ u σ ((Pi.single i (1:ℝ) : Fin n → ℝ))‖
              ≤ ‖fderiv ℝ u σ‖ * ‖(Pi.single i (1:ℝ) : Fin n → ℝ)‖ := h2
            _ ≤ C * 1 := by gcongr; exact hC_bound σ hσ_cl
            _ = C := mul_one C
      _ = ↑n * C := by simp [Finset.sum_const]
  ·
    unfold normalDerivLP
    have h := outwardUnitNormal_zero_off_frontier Ω σ hσ
    have : (∑ i : Fin n, fderiv ℝ u σ (Pi.single i 1) * outwardUnitNormal Ω σ i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp [show outwardUnitNormal Ω σ i = 0 from by rw [h]; rfl]
    rw [this, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg n) hC_nn

/-- Expanded form of Green's identity on $\Omega \setminus B(x, \varepsilon)$,
splitting each surface integral into its $\Phi \partial_\nu u$ and
$u \partial_\nu \Phi$ pieces. -/
theorem greens_identity_on_omega_eps_LP {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω)) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) (ε : ℝ) (hε : 0 < ε) :
    (∫ y in Ω \ Metric.ball x ε, fundamentalSolution n (x - y) * laplacianLP u y)
    = surfaceIntegralLP Ω (fun σ => fundamentalSolution n (x - σ) * normalDerivLP Ω u σ)
      - surfaceIntegralLP Ω (fun σ => u σ * normalDerivLP Ω (fun z => fundamentalSolution n (x - z)) σ)
      - sphereIntegralLP x ε (fun σ => fundamentalSolution n (x - σ) * normalDerivLP Ω u σ)
      + sphereIntegralLP x ε (fun σ => u σ * normalDerivLP Ω (fun z => fundamentalSolution n (x - z)) σ) := by


  have h_combined := greens_identity_on_omega_eps_combined u Ω hu hΩ hΩb x hx ε hε

  rw [surfaceIntegralLP_sub] at h_combined

  rw [sphereIntegralLP_sub] at h_combined

  linarith

/-- Convergence of the volume integral over $\Omega \setminus B(x, \varepsilon)$ to
the integral over $\Omega$ as $\varepsilon \to 0^+$ (since $B(x, \varepsilon)$ has
vanishing volume). -/
theorem volume_integral_limit_LP {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω)) (hΩ : IsOpen Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    Filter.Tendsto
      (fun ε => ∫ y in Ω \ Metric.ball x ε, fundamentalSolution n (x - y) * laplacianLP u y)
      (nhdsWithin 0 (Ioi 0))
      (nhds (∫ y in Ω, fundamentalSolution n (x - y) * laplacianLP u y)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    have hzero : ∀ y : Fin 0 → ℝ,
        fundamentalSolution 0 (x - y) * laplacianLP u y = 0 := by
      intro y; simp [laplacianLP, Finset.univ_eq_empty, mul_zero]
    simp_rw [hzero, integral_zero]
    exact tendsto_const_nhds
  ·
    set f := fun y => fundamentalSolution n (x - y) * laplacianLP u y with hf_def
    have hfi : IntegrableOn f Ω :=
      fundamentalSolution_laplacian_integrableOn u Ω hu hΩ x hx

    have heq : ∀ ε : ℝ, ∫ y in Ω \ Metric.ball x ε, f y =
        (∫ y in Ω, f y) - ∫ y in Ω ∩ Metric.ball x ε, f y := by
      intro ε
      rw [show Ω \ Metric.ball x ε = Ω \ (Ω ∩ Metric.ball x ε) from by
        ext y; simp [and_comm]]
      exact setIntegral_diff (hΩ.measurableSet.inter measurableSet_ball) hfi inter_subset_left

    suffices htend : Tendsto (fun ε => ∫ y in Ω ∩ Metric.ball x ε, f y)
        (nhdsWithin 0 (Ioi 0)) (nhds 0) by
      have := (tendsto_const_nhds.sub htend).congr (fun ε => (heq ε).symm)
      simpa only [sub_zero] using this

    have hrewrite : (fun ε => ∫ y in Ω ∩ Metric.ball x ε, f y) =
        (fun ε => ∫ y in Metric.ball x ε, f y ∂(volume.restrict Ω)) := by
      ext ε; rw [Measure.restrict_restrict measurableSet_ball, inter_comm]
    rw [hrewrite]
    apply hfi.tendsto_setIntegral_nhds_zero

    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    haveI : Fact (Fintype.card (Fin n) ≥ 1) := ⟨by simp [Fintype.card_fin]; omega⟩
    have hvol : Tendsto (fun ε => volume (Metric.ball x ε))
        (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
      simp_rw [← Metric.thickening_singleton]
      have h := tendsto_measure_thickening (μ := (volume : Measure (Fin n → ℝ)))
        (s := ({x} : Set (Fin n → ℝ)))
        ⟨1, one_pos, by rw [Metric.thickening_singleton]; exact measure_ball_lt_top.ne⟩
      rw [closure_singleton, measure_singleton] at h
      exact h
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hvol
    · intro ε; exact zero_le _
    · intro ε; exact Measure.restrict_le_self _

/-- Bound on the "$R_3$" sphere integral $\int_{\partial B(x,\varepsilon)}
\Phi(x - \sigma)\,\partial_\nu u(\sigma)\,dS \le C\,\varepsilon$. -/
theorem sphere_integral_R3_bound_LP {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω))
    (hΩb : Bornology.IsBounded Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε →
      ‖sphereIntegralLP x ε (fun σ => fundamentalSolution n (x - σ) * normalDerivLP Ω u σ)‖ ≤ C * ε := by

  obtain ⟨M', hM'_nn, hM'_bound⟩ := normalDerivLP_globally_bounded u Ω hu hΩb x hx


  refine ⟨↑n * M', fun ε hε => ?_⟩

  have h := sphereIntegralLP_phi_bound x ε hε (normalDerivLP Ω u) M' hM'_nn
    (fun σ _ => hM'_bound σ)

  linarith

/-- Linearity (addition) of the sphere integral. -/
theorem sphereIntegralLP_add {n : ℕ} (x : Fin n → ℝ) (ε : ℝ)
    (f g : (Fin n → ℝ) → ℝ) :
    sphereIntegralLP x ε (fun σ => f σ + g σ) =
      sphereIntegralLP x ε f + sphereIntegralLP x ε g := by
  simp only [sphereIntegralLP]
  exact MeasureTheory.integral_add
    (surfaceIntegral_integrable_LP (Metric.ball x ε) f)
    (surfaceIntegral_integrable_LP (Metric.ball x ε) g)

/-- Scalar homogeneity of the sphere integral. -/
theorem sphereIntegralLP_const_mul {n : ℕ} (x : Fin n → ℝ) (ε : ℝ)
    (c : ℝ) (f : (Fin n → ℝ) → ℝ) :
    sphereIntegralLP x ε (fun σ => c * f σ) = c * sphereIntegralLP x ε f := by
  simp only [sphereIntegralLP]
  rw [show (fun σ : Fin n → ℝ => c * f σ) = (fun σ => c • f σ) from by ext σ; rfl]
  rw [MeasureTheory.integral_smul]
  rfl

/-- Pointwise congruence: if $f = g$ on the sphere $\partial B(x, \varepsilon)$,
then their sphere integrals agree. -/
theorem sphereIntegralLP_congr_on_sphere {n : ℕ} (x : Fin n → ℝ) (ε : ℝ)
    (f g : (Fin n → ℝ) → ℝ)
    (h : ∀ σ, σ ∈ Metric.sphere x ε → f σ = g σ) :
    sphereIntegralLP x ε f = sphereIntegralLP x ε g := by
  simp only [sphereIntegralLP]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_frontier
    (fun σ hσ => h σ (Metric.frontier_ball_subset_sphere hσ))

/-- Explicit pointwise value of the normal derivative of $\Phi(x - \cdot)$ on the
sphere $\partial B(x, \varepsilon)$: $\partial_\nu \Phi = 1/(\omega_n \varepsilon^{n-1})$. -/
theorem normalDerivLP_Phi_on_sphere_eq {n : ℕ} (Ω : Set (Fin n → ℝ))
    (x σ : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) (hσ : σ ∈ Metric.sphere x ε) :
    normalDerivLP Ω (fun z => fundamentalSolution n (x - z)) σ =
      1 / (unitSphereArea n * ε ^ (n - 1)) := by sorry

/-- The total surface area of the sphere $\partial B(x, \varepsilon)$ is
$\omega_n \varepsilon^{n-1}$. -/
theorem sphereIntegralLP_one_eq {n : ℕ} (x : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    sphereIntegralLP x ε (fun _ => 1) = unitSphereArea n * ε ^ (n - 1) := by sorry

/-- Packaged form: the normal derivative of $\Phi(x - \cdot)$ takes a constant value
$c = 1/(\omega_n \varepsilon^{n-1}) > 0$ on the sphere $\partial B(x, \varepsilon)$, and
$c$ times the area of the sphere equals $1$. -/
theorem normalDerivLP_Phi_const_on_sphere {n : ℕ} (Ω : Set (Fin n → ℝ))
    (x : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧
      (∀ σ ∈ Metric.sphere x ε,
        normalDerivLP Ω (fun z => fundamentalSolution n (x - z)) σ = c) ∧
      c * sphereIntegralLP x ε (fun _ => 1) = 1 := by
  refine ⟨1 / (unitSphereArea n * ε ^ (n - 1)), ?_, ?_, ?_⟩
  ·
    exact div_pos one_pos (mul_pos (unitSphereArea_pos n) (pow_pos hε (n - 1)))
  ·
    intro σ hσ
    exact normalDerivLP_Phi_on_sphere_eq Ω x σ ε hε hσ
  ·
    rw [sphereIntegralLP_one_eq x ε hε, div_mul_cancel₀]
    exact ne_of_gt (mul_pos (unitSphereArea_pos n) (pow_pos hε (n - 1)))

/-- Weighted bound: if $g \ge 0$ on the sphere and $\int g\,dS = A$, then
$\bigl|\int f g\,dS\bigr| \le (\sup |f|) \cdot A$. -/
theorem sphereIntegralLP_weighted_bound {n : ℕ} (x : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε)
    (f g : (Fin n → ℝ) → ℝ)
    (hg_nn : ∀ σ ∈ Metric.sphere x ε, 0 ≤ g σ)
    (A : ℝ) (hA : sphereIntegralLP x ε g = A) :
    ‖sphereIntegralLP x ε (fun σ => f σ * g σ)‖ ≤ (⨆ σ ∈ Metric.sphere x ε, |f σ|) * A := by sorry

/-- Normalisation: $\int_{\partial B(x, \varepsilon)} \partial_\nu \Phi(x-\sigma)\,
dS = 1$. This is the analogue of the $-1$ normalisation at the origin, used in the
sphere version of the representation formula. -/
theorem sphereIntegralLP_normalDeriv_Phi_eq_one {n : ℕ}
    (Ω : Set (Fin n → ℝ)) (x : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    sphereIntegralLP x ε
      (fun σ => normalDerivLP Ω (fun z => fundamentalSolution n (x - z)) σ) = 1 := by

  obtain ⟨c, _, hc_eq, hc_norm⟩ := normalDerivLP_Phi_const_on_sphere Ω x ε hε

  rw [sphereIntegralLP_congr_on_sphere x ε _ (fun _ => c) hc_eq]

  rw [show (fun (_ : Fin n → ℝ) => c) = (fun σ => c * (fun (_ : Fin n → ℝ) => (1 : ℝ)) σ) from by ext; simp]
  rw [sphereIntegralLP_const_mul]

  exact hc_norm

/-- Error bound: the sphere integral of $(u - u(x))\,\partial_\nu \Phi$ is bounded
by the oscillation $\sup |u - u(x)|$ on the sphere. -/
theorem sphereIntegralLP_error_bound {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (x : Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    ‖sphereIntegralLP x ε
      (fun σ => (u σ - u x) * normalDerivLP Ω (fun z => fundamentalSolution n (x - z)) σ)‖ ≤
      ⨆ σ ∈ Metric.sphere x ε, |u σ - u x| := by

  obtain ⟨c, hc_pos, hc_eq, hc_norm⟩ := normalDerivLP_Phi_const_on_sphere Ω x ε hε

  have hg_nn : ∀ σ ∈ Metric.sphere x ε,
      0 ≤ normalDerivLP Ω (fun z => fundamentalSolution n (x - z)) σ := by
    intro σ hσ; rw [hc_eq σ hσ]; exact le_of_lt hc_pos

  have hg_int : sphereIntegralLP x ε
      (fun σ => normalDerivLP Ω (fun z => fundamentalSolution n (x - z)) σ) = 1 :=
    sphereIntegralLP_normalDeriv_Phi_eq_one Ω x ε hε

  have h := sphereIntegralLP_weighted_bound x ε hε
    (fun σ => u σ - u x)
    (fun σ => normalDerivLP Ω (fun z => fundamentalSolution n (x - z)) σ)
    hg_nn 1 hg_int
  linarith [h]

/-- Continuity at $x$ implies that $\sup_{\sigma \in \partial B(x,\varepsilon)}
|u(\sigma) - u(x)| \to 0$ as $\varepsilon \to 0^+$. -/
theorem oscillation_sphere_tendsto_zero {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω))
    (hΩ : IsOpen Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    Filter.Tendsto (fun ε => ⨆ σ ∈ Metric.sphere x ε, |u σ - u x|)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by

  have hcont : ContinuousOn u (closure Ω) := hu.continuousOn
  have hx_nhds : closure Ω ∈ nhds x :=
    _root_.mem_nhds_iff.mpr ⟨Ω, subset_closure, hΩ, hx⟩
  have hca : ContinuousAt u x := hcont.continuousAt hx_nhds

  rw [Metric.tendsto_nhdsWithin_nhds]
  intro δ hδ
  rw [Metric.continuousAt_iff] at hca
  obtain ⟨η, hη, hηu⟩ := hca (δ / 2) (by linarith)
  refine ⟨η, hη, fun ε hε_mem hε_dist => ?_⟩
  rw [mem_Ioi] at hε_mem
  simp [abs_of_pos hε_mem] at hε_dist
  rw [Real.dist_eq, sub_zero]

  have hnn : 0 ≤ ⨆ σ ∈ Metric.sphere x ε, |u σ - u x| :=
    Real.iSup_nonneg (fun σ => Real.iSup_nonneg (fun _ => abs_nonneg _))
  rw [abs_of_nonneg hnn]

  have hbnd : ∀ σ : Fin n → ℝ, ⨆ (_ : σ ∈ Metric.sphere x ε), |u σ - u x| ≤ δ / 2 := by
    intro σ
    by_cases hσ : σ ∈ Metric.sphere x ε
    ·
      haveI : Unique (σ ∈ Metric.sphere x ε) := ⟨⟨hσ⟩, fun _ => Subsingleton.elim _ _⟩
      rw [ciSup_unique]
      rw [Metric.mem_sphere] at hσ
      have hdist : dist σ x < η := by rw [hσ]; exact hε_dist
      have := hηu hdist
      rw [Real.dist_eq] at this
      linarith
    ·
      haveI : IsEmpty (σ ∈ Metric.sphere x ε) := isEmpty_iff.mpr hσ
      rw [Real.iSup_of_isEmpty]
      linarith

  calc ⨆ σ ∈ Metric.sphere x ε, |u σ - u x|
      ≤ δ / 2 := ciSup_le hbnd
    _ < δ := by linarith

/-- Decomposition of the "$R_4$" sphere integral: $\int_{\partial B(x,\varepsilon)}
u\,\partial_\nu \Phi\,dS = u(x) + \text{error}(\varepsilon)$, with $\text{error}(\varepsilon)
\to 0$ as $\varepsilon \to 0^+$. -/
theorem sphere_integral_R4_decomposition_LP {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω))
    (hΩ : IsOpen Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    ∃ (error : ℝ → ℝ),
      (∀ ε > 0, sphereIntegralLP x ε
        (fun σ => u σ * normalDerivLP Ω (fun z => fundamentalSolution n (x - z)) σ) =
          u x + error ε) ∧
      Filter.Tendsto error (nhdsWithin 0 (Ioi 0)) (nhds 0) := by

  refine ⟨fun ε => sphereIntegralLP x ε
    (fun σ => (u σ - u x) * normalDerivLP Ω (fun z => fundamentalSolution n (x - z)) σ), ?_, ?_⟩
  ·

    intro ε hε
    have hsplit : (fun σ => u σ * normalDerivLP Ω (fun z => fundamentalSolution n (x - z)) σ) =
        (fun σ => u x * normalDerivLP Ω (fun z => fundamentalSolution n (x - z)) σ +
                  (u σ - u x) * normalDerivLP Ω (fun z => fundamentalSolution n (x - z)) σ) := by
      ext σ; ring

    rw [hsplit, sphereIntegralLP_add, sphereIntegralLP_const_mul,
        sphereIntegralLP_normalDeriv_Phi_eq_one Ω x ε hε, mul_one]
  ·

    apply squeeze_zero_norm'
    · exact eventually_nhdsWithin_of_forall fun ε hε =>
        sphereIntegralLP_error_bound u Ω x ε (mem_Ioi.mp hε)
    · exact oscillation_sphere_tendsto_zero u Ω hu hΩ x hx

/-- The "$R_3$" sphere integral $\int_{\partial B(x,\varepsilon)} \Phi(x-\sigma)\,
\partial_\nu u\,dS$ vanishes as $\varepsilon \to 0^+$. -/
theorem sphere_integral_R3_vanishes_LP {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω))
    (hΩb : Bornology.IsBounded Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    Filter.Tendsto
      (fun ε => sphereIntegralLP x ε (fun σ => fundamentalSolution n (x - σ) * normalDerivLP Ω u σ))
      (nhdsWithin 0 (Ioi 0))
      (nhds 0) := by
  obtain ⟨C, hbound⟩ := sphere_integral_R3_bound_LP u Ω hu hΩb x hx

  apply squeeze_zero_norm' (a := fun ε => C * ε)
  · exact eventually_nhdsWithin_of_forall fun ε hε => hbound ε (mem_Ioi.mp hε)
  · have h1 : Filter.Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds Filter.tendsto_id
    have h2 := h1.const_mul C
    simp at h2
    exact h2

/-- The "$R_4$" sphere integral $\int_{\partial B(x,\varepsilon)}
u\,\partial_\nu \Phi(x-\cdot)\,dS$ converges to $u(x)$ as $\varepsilon \to 0^+$. -/
theorem sphere_integral_R4_limit_LP {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω))
    (hΩ : IsOpen Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    Filter.Tendsto
      (fun ε => sphereIntegralLP x ε
        (fun σ => u σ * normalDerivLP Ω (fun z => fundamentalSolution n (x - z)) σ))
      (nhdsWithin 0 (Ioi 0))
      (nhds (u x)) := by
  obtain ⟨error, h_eq, h_err⟩ := sphere_integral_R4_decomposition_LP u Ω hu hΩ x hx
  have h_sum : Filter.Tendsto (fun ε => u x + error ε)
      (nhdsWithin 0 (Ioi 0)) (nhds (u x)) := by
    have := (@tendsto_const_nhds _ _ _ (u x) (nhdsWithin 0 (Ioi 0))).add h_err
    rwa [add_zero] at this
  exact h_sum.congr' (Filter.EventuallyEq.symm
    (eventually_nhdsWithin_of_forall fun ε hε => h_eq ε (mem_Ioi.mp hε)))

/-- Auxiliary form of the Green-Phi representation formula: $u(x) = (\Phi *
\Delta u) - \int_{\partial\Omega} \Phi\,\partial_\nu u + \int_{\partial\Omega}
u\,\partial_\nu \Phi$. Proved by passing to the limit in Green's identity on
$\Omega \setminus B(x, \varepsilon)$. -/
theorem representation_formula_u_aux {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω)) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    u x = (∫ y in Ω, fundamentalSolution n (x - y) * laplacianLP u y)
      - surfaceIntegralLP Ω (fun σ => fundamentalSolution n (x - σ) * normalDerivLP Ω u σ)
      + surfaceIntegralLP Ω (fun σ => u σ * normalDerivLP Ω (fun z => fundamentalSolution n (x - z)) σ) := by

  set L := ∫ y in Ω, fundamentalSolution n (x - y) * laplacianLP u y
  set R1 := surfaceIntegralLP Ω (fun σ => fundamentalSolution n (x - σ) * normalDerivLP Ω u σ)
  set R2 := surfaceIntegralLP Ω (fun σ => u σ * normalDerivLP Ω (fun z => fundamentalSolution n (x - z)) σ)

  set R3 := fun ε => sphereIntegralLP x ε (fun σ => fundamentalSolution n (x - σ) * normalDerivLP Ω u σ)
  set R4 := fun ε => sphereIntegralLP x ε (fun σ => u σ * normalDerivLP Ω (fun z => fundamentalSolution n (x - z)) σ)
  set Lε := fun ε => ∫ y in Ω \ Metric.ball x ε, fundamentalSolution n (x - y) * laplacianLP u y

  have h_green_eq : ∀ᶠ ε in nhdsWithin 0 (Ioi 0),
      Lε ε = R1 - R2 - R3 ε + R4 ε :=
    eventually_nhdsWithin_of_forall fun ε hε =>
      greens_identity_on_omega_eps_LP u Ω hu hΩ hΩb x hx ε (mem_Ioi.mp hε)

  have hLε : Filter.Tendsto Lε (nhdsWithin 0 (Ioi 0)) (nhds L) :=
    volume_integral_limit_LP u Ω hu hΩ x hx
  have hR3 : Filter.Tendsto R3 (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    sphere_integral_R3_vanishes_LP u Ω hu hΩb x hx
  have hR4 : Filter.Tendsto R4 (nhdsWithin 0 (Ioi 0)) (nhds (u x)) :=
    sphere_integral_R4_limit_LP u Ω hu hΩ x hx

  have h_rhs : Filter.Tendsto (fun ε => R1 - R2 - R3 ε + R4 ε)
      (nhdsWithin 0 (Ioi 0)) (nhds (R1 - R2 - 0 + u x)) :=
    (tendsto_const_nhds.sub hR3).add hR4
  simp only [sub_zero] at h_rhs


  have h_unique : L = R1 - R2 + u x :=
    tendsto_nhds_unique hLε (h_rhs.congr' (Filter.EventuallyEq.symm h_green_eq))
  linarith

/-- **Green's representation formula** (with $\Phi$): for any $C^2$ function $u$ on
$\overline{\Omega}$ and $x \in \Omega$,
$u(x) = \int_\Omega \Phi(x - y)\,\Delta u(y)\,dy
  - \int_{\partial\Omega} \Phi(x - \sigma)\,\partial_\nu u(\sigma)\,dS
  + \int_{\partial\Omega} u(\sigma)\,\partial_\nu \Phi(x - \sigma)\,dS$. -/
theorem representation_formula_u {n : ℕ}
    (u : (Fin n → ℝ) → ℝ) (Ω : Set (Fin n → ℝ))
    (hu : ContDiffOn ℝ 2 u (closure Ω)) (hΩ : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    u x = (∫ y in Ω, fundamentalSolution n (x - y) * laplacianLP u y)
      - surfaceIntegralLP Ω (fun σ => fundamentalSolution n (x - σ) * normalDerivLP Ω u σ)
      + surfaceIntegralLP Ω (fun σ => u σ * normalDerivLP Ω (fun z => fundamentalSolution n (x - z)) σ) := by
  exact representation_formula_u_aux u Ω hu hΩ hΩb x hx

/-- A solution of $\Delta u = f$ on $\Omega$ is automatically $C^2$ up to the
boundary, given enough regularity of $f$ and $\partial\Omega$ (axiom). -/
theorem pde_solution_smooth {n : ℕ}
    (Ω : Set (Fin n → ℝ)) (u f : (Fin n → ℝ) → ℝ)
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hu_pde : ∀ x ∈ Ω, laplacianLP u x = f x) :
    ContDiffOn ℝ 2 u (closure Ω) := by sorry

/-- Smoothness of the Green corrector $h(y) = \Phi(x - y) - G(x, y)$ up to
$\overline{\Omega}$. -/
theorem corrector_smooth {n : ℕ}
    (Ω : Set (Fin n → ℝ)) (gf : GreenFunctionLP n Ω)
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    ContDiffOn ℝ 2 (fun y => fundamentalSolution n (x - y) - gf.G x y) (closure Ω) := by sorry

/-- Products of bounded measurable functions are integrable on $\partial\Omega$
(axiom used as glue). -/
theorem surface_integrand_integrableOn {n : ℕ}
    (Ω : Set (Fin n → ℝ)) (h₁ h₂ : (Fin n → ℝ) → ℝ)
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) :
    MeasureTheory.IntegrableOn (fun σ => h₁ σ * h₂ σ) (frontier Ω) (surfaceMeasure Ω) := by sorry

/-- Apply Green's second identity to the harmonic corrector $\varphi = \Phi - G$:
the resulting identity expresses how the corrector "absorbs" the singular part of
$\Phi$, leaving a clean integral identity used to derive Green's representation
formula in terms of $G$. -/
theorem green_identity_corrector {n : ℕ}
    (hn : n ≥ 2)
    (Ω : Set (Fin n → ℝ)) (gf : GreenFunctionLP n Ω)
    (u f g : (Fin n → ℝ) → ℝ) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hu_pde : ∀ x ∈ Ω, laplacianLP u x = f x)
    (hu_bdy : ∀ σ ∈ frontier Ω, u σ = g σ)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    let Φ : (Fin n → ℝ) → ℝ := fun y => fundamentalSolution n (x - y)
    let φ : (Fin n → ℝ) → ℝ := fun y => Φ y - gf.G x y
    (0 : ℝ) = (∫ y in Ω, φ y * f y)
      - surfaceIntegralLP Ω (fun σ => Φ σ * normalDerivLP Ω u σ)
      + surfaceIntegralLP Ω (fun σ => g σ * normalDerivLP Ω φ σ) := by
  intro Φ φ

  have hφ_harm := green_corrector_harmonic hn gf x hx

  have φ_eq_Φ_bdy : ∀ σ ∈ frontier Ω, φ σ = Φ σ := by
    intro σ hσ; show Φ σ - gf.G x σ = Φ σ
    rw [gf.boundary_zero x hx σ hσ]; ring

  have green2 : (∫ y in Ω, φ y * laplacianLP u y - u y * laplacianLP φ y) =
    surfaceIntegralLP Ω (fun σ => φ σ * normalDerivLP Ω u σ - u σ * normalDerivLP Ω φ σ) :=
    greens_second_identity Ω u φ (pde_solution_smooth Ω u f hΩ hΩb hu_pde)
      (corrector_smooth Ω gf hΩ hΩb x hx) hΩ hΩb

  have harmonic_elim : (∫ y in Ω, φ y * laplacianLP u y - u y * laplacianLP φ y) =
    ∫ y in Ω, φ y * laplacianLP u y := by
    apply setIntegral_congr_fun hΩ.measurableSet
    intro y hy
    have : laplacianLP φ y = 0 := hφ_harm y hy
    simp only [this, mul_zero, sub_zero]

  have vol_sub : (∫ y in Ω, φ y * laplacianLP u y) = ∫ y in Ω, φ y * f y :=
    setIntegral_congr_fun hΩ.measurableSet (fun y hy => by rw [hu_pde y hy])

  have vol_eq_bdy : (∫ y in Ω, φ y * f y) =
    surfaceIntegralLP Ω (fun σ => φ σ * normalDerivLP Ω u σ - u σ * normalDerivLP Ω φ σ) := by
    rw [← vol_sub, ← harmonic_elim]; exact green2

  have bdy_congr : surfaceIntegralLP Ω (fun σ => φ σ * normalDerivLP Ω u σ - u σ * normalDerivLP Ω φ σ) =
    surfaceIntegralLP Ω (fun σ => Φ σ * normalDerivLP Ω u σ - g σ * normalDerivLP Ω φ σ) := by
    unfold surfaceIntegralLP
    apply setIntegral_congr_fun measurableSet_frontier
    intro σ hσ
    simp only []
    rw [φ_eq_Φ_bdy σ hσ, hu_bdy σ hσ]

  have bdy_split : surfaceIntegralLP Ω (fun σ => Φ σ * normalDerivLP Ω u σ - g σ * normalDerivLP Ω φ σ) =
    surfaceIntegralLP Ω (fun σ => Φ σ * normalDerivLP Ω u σ) -
    surfaceIntegralLP Ω (fun σ => g σ * normalDerivLP Ω φ σ) := by
    unfold surfaceIntegralLP
    exact MeasureTheory.integral_sub
      (surface_integrand_integrableOn Ω Φ (normalDerivLP Ω u) hΩ hΩb)
      (surface_integrand_integrableOn Ω g (normalDerivLP Ω φ) hΩ hΩb)

  have bdy_rewrite : surfaceIntegralLP Ω (fun σ => φ σ * normalDerivLP Ω u σ - u σ * normalDerivLP Ω φ σ) =
    surfaceIntegralLP Ω (fun σ => Φ σ * normalDerivLP Ω u σ) -
    surfaceIntegralLP Ω (fun σ => g σ * normalDerivLP Ω φ σ) := by
    rw [bdy_congr, bdy_split]

  linarith [vol_eq_bdy, bdy_rewrite]

/-- Adapted form of the representation formula in which the volume integral uses
$f = \Delta u$ and the boundary value uses $g = u|_{\partial \Omega}$. -/
theorem adapted_representation_formula {n : ℕ}
    (Ω : Set (Fin n → ℝ)) (gf : GreenFunctionLP n Ω)
    (u f g : (Fin n → ℝ) → ℝ) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hu_pde : ∀ x ∈ Ω, laplacianLP u x = f x)
    (hu_bdy : ∀ σ ∈ frontier Ω, u σ = g σ)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    let Φ : (Fin n → ℝ) → ℝ := fun y => fundamentalSolution n (x - y)
    u x = (∫ y in Ω, Φ y * f y)
      - surfaceIntegralLP Ω (fun σ => Φ σ * normalDerivLP Ω u σ)
      + surfaceIntegralLP Ω (fun σ => g σ * normalDerivLP Ω Φ σ) := by
  intro Φ

  have hu_smooth := pde_solution_smooth Ω u f hΩ hΩb hu_pde
  have h_repr := representation_formula_u_aux u Ω hu_smooth hΩ hΩb x hx


  have vol_rw : (∫ y in Ω, fundamentalSolution n (x - y) * laplacianLP u y) =
    ∫ y in Ω, Φ y * f y :=
    setIntegral_congr_fun hΩ.measurableSet (fun y hy => by rw [hu_pde y hy])

  have bdy_rw : surfaceIntegralLP Ω (fun σ => u σ * normalDerivLP Ω (fun z => fundamentalSolution n (x - z)) σ) =
    surfaceIntegralLP Ω (fun σ => g σ * normalDerivLP Ω Φ σ) := by
    unfold surfaceIntegralLP
    apply setIntegral_congr_fun measurableSet_frontier
    intro σ hσ; simp only []; rw [hu_bdy σ hσ]

  linarith [h_repr, vol_rw, bdy_rw]

/-- Volume integral combination: $-\int \Phi f + \int (\Phi - G) f = -\int f G$, by
linearity. -/
theorem volume_integral_combination {n : ℕ}
    (Ω : Set (Fin n → ℝ)) (gf : GreenFunctionLP n Ω)
    (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hΦf : IntegrableOn (fun y => fundamentalSolution n (x - y) * f y) Ω)
    (hGf : IntegrableOn (fun y => gf.G x y * f y) Ω) :
    let Φ : (Fin n → ℝ) → ℝ := fun y => fundamentalSolution n (x - y)
    let φ : (Fin n → ℝ) → ℝ := fun y => Φ y - gf.G x y
    (-(∫ y in Ω, Φ y * f y) + (∫ y in Ω, φ y * f y) =
    -(∫ y in Ω, f y * gf.G x y)) := by
  intro Φ φ

  have integrand_eq : (∫ y in Ω, φ y * f y) = ∫ y in Ω, (Φ y * f y - gf.G x y * f y) := by
    congr 1; ext y; show (Φ y - gf.G x y) * f y = Φ y * f y - gf.G x y * f y; ring
  rw [integrand_eq]

  rw [MeasureTheory.integral_sub hΦf hGf]

  have h_comm : (∫ y in Ω, gf.G x y * f y) = ∫ y in Ω, f y * gf.G x y := by
    congr 1; ext y; ring
  linarith [h_comm]

/-- Surface integral combination: the analogue of `volume_integral_combination` but
for boundary integrals of $g\,\partial_\nu \cdot$, using linearity of the normal
derivative on $\Phi - G$. -/
theorem surface_integral_combination {n : ℕ}
    (Ω : Set (Fin n → ℝ)) (gf : GreenFunctionLP n Ω)
    (g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hΦ_diff : ∀ σ, DifferentiableAt ℝ (fun y => fundamentalSolution n (x - y)) σ)
    (hG_diff : ∀ σ, DifferentiableAt ℝ (fun z => gf.G x z) σ)
    (h1_int : IntegrableOn (fun σ => g σ * normalDerivLP Ω (fun y => fundamentalSolution n (x - y)) σ) (frontier Ω) (surfaceMeasure Ω))
    (h2_int : IntegrableOn (fun σ => g σ * normalDerivLP Ω (fun z => gf.G x z) σ) (frontier Ω) (surfaceMeasure Ω)) :
    let Φ : (Fin n → ℝ) → ℝ := fun y => fundamentalSolution n (x - y)
    let φ : (Fin n → ℝ) → ℝ := fun y => Φ y - gf.G x y
    (-(surfaceIntegralLP Ω (fun σ => g σ * normalDerivLP Ω Φ σ))
    + surfaceIntegralLP Ω (fun σ => g σ * normalDerivLP Ω φ σ) =
    -(surfaceIntegralLP Ω (fun σ => g σ * normalDerivLP Ω (fun z => gf.G x z) σ))) := by
  intro Φ φ


  have normalDeriv_split : ∀ σ, normalDerivLP Ω φ σ =
      normalDerivLP Ω Φ σ - normalDerivLP Ω (fun z => gf.G x z) σ := by
    intro σ
    unfold normalDerivLP


    change (∑ i : Fin n, (fderiv ℝ (fun y => fundamentalSolution n (x - y) - gf.G x y) σ) (Pi.single i 1) * outwardUnitNormal Ω σ i) =
      (∑ i : Fin n, (fderiv ℝ (fun y => fundamentalSolution n (x - y)) σ) (Pi.single i 1) * outwardUnitNormal Ω σ i) -
      (∑ i : Fin n, (fderiv ℝ (fun z => gf.G x z) σ) (Pi.single i 1) * outwardUnitNormal Ω σ i)
    have heq : (fun y => fundamentalSolution n (x - y) - gf.G x y) = (fun y => fundamentalSolution n (x - y)) - (fun z => gf.G x z) := by
      ext; simp [Pi.sub_apply]
    rw [heq, fderiv_sub (hΦ_diff σ) (hG_diff σ)]
    simp only [ContinuousLinearMap.sub_apply]
    rw [← Finset.sum_sub_distrib]
    congr 1; ext i; ring

  have integrand_eq : surfaceIntegralLP Ω (fun σ => g σ * normalDerivLP Ω φ σ) =
      surfaceIntegralLP Ω (fun σ => g σ * normalDerivLP Ω Φ σ - g σ * normalDerivLP Ω (fun z => gf.G x z) σ) := by
    unfold surfaceIntegralLP
    apply setIntegral_congr_fun measurableSet_frontier
    intro σ _; simp only []; rw [normalDeriv_split σ]; ring
  rw [integrand_eq]

  unfold surfaceIntegralLP
  rw [MeasureTheory.integral_sub h1_int h2_int]
  ring

/-- Green's representation formula derived from the corrector identity: combining the
$\Phi$-version of the representation formula with the harmonic-corrector identity
$\varphi = \Phi - G$ yields the clean Green-function formula
$u(x) = \int_\Omega f \cdot G(x, \cdot) + \int_{\partial \Omega} g \cdot \partial_\nu G(x, \cdot)$. -/
theorem green_representation_from_corrector {n : ℕ}
    (hn : n ≥ 2)
    (Ω : Set (Fin n → ℝ)) (gf : GreenFunctionLP n Ω)
    (u f g : (Fin n → ℝ) → ℝ) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hu_pde : ∀ x ∈ Ω, laplacianLP u x = f x)
    (hu_bdy : ∀ σ ∈ frontier Ω, u σ = g σ)
    (x : Fin n → ℝ) (hx : x ∈ Ω)
    (hΦ_diff : ∀ σ, DifferentiableAt ℝ (fun y => fundamentalSolution n (x - y)) σ)
    (hG_diff : ∀ σ, DifferentiableAt ℝ (fun z => gf.G x z) σ)
    (h1_int : IntegrableOn (fun σ => g σ * normalDerivLP Ω (fun y => fundamentalSolution n (x - y)) σ) (frontier Ω) (surfaceMeasure Ω))
    (h2_int : IntegrableOn (fun σ => g σ * normalDerivLP Ω (fun z => gf.G x z) σ) (frontier Ω) (surfaceMeasure Ω))
    (hΦf_int : IntegrableOn (fun y => fundamentalSolution n (x - y) * f y) Ω)
    (hGf_int : IntegrableOn (fun y => gf.G x y * f y) Ω) :
    u x = (∫ y in Ω, f y * gf.G x y)
      + surfaceIntegralLP Ω (fun σ => g σ * normalDerivLP Ω (fun z => gf.G x z) σ) := by

  set Φ : (Fin n → ℝ) → ℝ := fun y => fundamentalSolution n (x - y) with hΦ_def
  set φ : (Fin n → ℝ) → ℝ := fun y => Φ y - gf.G x y with hφ_def

  set A := ∫ y in Ω, Φ y * f y
  set B := surfaceIntegralLP Ω (fun σ => Φ σ * normalDerivLP Ω u σ)
  set C := surfaceIntegralLP Ω (fun σ => g σ * normalDerivLP Ω Φ σ)
  set D := ∫ y in Ω, φ y * f y
  set E := surfaceIntegralLP Ω (fun σ => g σ * normalDerivLP Ω φ σ)

  have repr : u x = A - B + C :=
    adapted_representation_formula Ω gf u f g hΩ hΩb hu_pde hu_bdy x hx

  have green_corr : (0 : ℝ) = D - B + E :=
    green_identity_corrector hn Ω gf u f g hΩ hΩb hu_pde hu_bdy x hx

  have combine_vol : -A + D = -(∫ y in Ω, f y * gf.G x y) :=
    volume_integral_combination Ω gf f x hΦf_int hGf_int

  have combine_surf : -C + E =
      -(surfaceIntegralLP Ω (fun σ => g σ * normalDerivLP Ω (fun z => gf.G x z) σ)) :=
    surface_integral_combination Ω gf g x hΦ_diff hG_diff h1_int h2_int


  linarith

/-- **Green's representation formula** for the Dirichlet problem $\Delta u = f$ in
$\Omega$ with $u = g$ on $\partial\Omega$:
$u(x) = \int_\Omega f(y)\,G(x, y)\,dy + \int_{\partial\Omega} g(\sigma)\,
\partial_\nu G(x, \sigma)\,dS$. -/
theorem green_representation_formula {n : ℕ}
    (hn : n ≥ 2)
    (Ω : Set (Fin n → ℝ)) (gf : GreenFunctionLP n Ω)
    (u f g : (Fin n → ℝ) → ℝ) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hu_pde : ∀ x ∈ Ω, laplacianLP u x = f x)
    (hu_bdy : ∀ σ ∈ frontier Ω, u σ = g σ)
    (x : Fin n → ℝ) (hx : x ∈ Ω) :
    u x = (∫ y in Ω, f y * gf.G x y)
      + surfaceIntegralLP Ω (fun σ => g σ * normalDerivLP Ω (fun z => gf.G x z) σ) := by

  have hΦ_diff : ∀ σ, DifferentiableAt ℝ (fun y => fundamentalSolution n (x - y)) σ :=
    gf.Phi_differentiable x
  have hG_diff : ∀ σ, DifferentiableAt ℝ (fun z => gf.G x z) σ :=
    gf.G_differentiable x hx
  have h1_int : IntegrableOn (fun σ => g σ * normalDerivLP Ω (fun y => fundamentalSolution n (x - y)) σ) (frontier Ω) (surfaceMeasure Ω) :=
    gf.Phi_normalDeriv_integrableOn x g
  have h2_int : IntegrableOn (fun σ => g σ * normalDerivLP Ω (fun z => gf.G x z) σ) (frontier Ω) (surfaceMeasure Ω) :=
    gf.G_normalDeriv_integrableOn x hx g
  have hΦf_int : IntegrableOn (fun y => fundamentalSolution n (x - y) * f y) Ω :=
    gf.Phi_mul_integrableOn x f hΩb
  have hGf_int : IntegrableOn (fun y => gf.G x y * f y) Ω :=
    gf.G_mul_integrableOn x hx f hΩb
  exact green_representation_from_corrector hn Ω gf u f g hΩ hΩb hu_pde hu_bdy x hx
    hΦ_diff hG_diff h1_int h2_int hΦf_int hGf_int

/-- Laplacian on `EuclideanSpace ℝ (Fin n)` (i.e.\ Mathlib's L²-normed $\mathbb{R}^n$).
Defined as $\Delta f(x) = \sum_i \partial_{x_i}^2 f(x)$ using standard basis vectors. -/
def laplacianE {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n,
    fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1)

/-- A function $u$ on `EuclideanSpace ℝ (Fin n)` is harmonic on $\Omega$ iff
$\Delta u = 0$ on $\Omega$. -/
def IsHarmonicE {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x ∈ Ω, laplacianE u x = 0

/-- Opaque outward unit normal on $\partial\Omega$, valued in `EuclideanSpace ℝ (Fin n)`. -/
opaque outwardUnitNormalE {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)

/-- Explicit form of the outward unit normal on a ball in $\mathbb{R}^3$:
$\nu(\sigma) = (\sigma - p)/R$ for $\sigma$ on the sphere of radius $R$ about $p$. -/
theorem outwardUnitNormalE_ball_spec (R : ℝ) (hR : 0 < R)
    (p σ : EuclideanSpace ℝ (Fin 3)) (hσ : σ ∈ Metric.sphere p R) :
    outwardUnitNormalE (Metric.ball p R) σ = fun i => (σ i - p i) / R := by sorry

/-- Opaque surface (Hausdorff) measure on $\partial\Omega \subseteq$
`EuclideanSpace ℝ (Fin n)`. -/
opaque surfaceMeasureE {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Measure (EuclideanSpace ℝ (Fin n))

/-- Normal derivative $\partial_\nu f$ at $\sigma \in \partial\Omega$ on
`EuclideanSpace`, defined as $\sum_i (\partial_i f)(\sigma) \cdot \nu_i(\sigma)$. -/
def normalDerivE {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (σ : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, fderiv ℝ f σ (EuclideanSpace.single i 1) * outwardUnitNormalE Ω σ i

/-- Surface integral $\int_{\partial \Omega} f\,dS$ on `EuclideanSpace`. -/
def surfaceIntegralE {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ :=
  ∫ σ in frontier Ω, f σ ∂(surfaceMeasureE Ω)

/-- Bundled Green's function for the Dirichlet Laplacian on $\Omega \subseteq$
`EuclideanSpace ℝ (Fin n)`. Same defining properties as `GreenFunctionLP` but on the
Euclidean (rather than $L^p$) model of $\mathbb{R}^n$. -/
structure GreenFunctionE (n : ℕ) (Ω : Set (EuclideanSpace ℝ (Fin n))) where
  G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → ℝ
  domain_open : IsOpen Ω
  boundary_zero : ∀ x ∈ Ω, ∀ σ ∈ frontier Ω, G x σ = 0
  distributional_pde : ∀ x ∈ Ω, ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
    ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    ∫ y, G x y * laplacianE φ y = φ x

/-- Squared `EuclideanSpace` norm: $\|v\|^2 = \sum_i v_i^2$ in dimension $3$. -/
lemma euclideanSpace_norm_sq (v : EuclideanSpace ℝ (Fin 3)) :
    ‖v‖ ^ 2 = ∑ i : Fin 3, v i ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  congr 1; ext i; simp [Real.norm_eq_abs, sq_abs]

/-- Componentwise restatement of `outwardUnitNormalE_ball_spec`:
$\nu_i(\sigma) = (\sigma_i - p_i)/R$. -/
theorem outwardUnitNormalE_ball_eq (R : ℝ) (hR : 0 < R)
    (p σ : EuclideanSpace ℝ (Fin 3)) (hσ : σ ∈ Metric.sphere p R) (i : Fin 3) :
    outwardUnitNormalE (Metric.ball p R) σ i = (σ i - p i) / R := by
  have h := outwardUnitNormalE_ball_spec R hR p σ hσ
  rw [show (outwardUnitNormalE (Metric.ball p R) σ i) = (outwardUnitNormalE (Metric.ball p R) σ) i from rfl]
  rw [h]

/-- Uniqueness of the Green's function on a ball in $\mathbb{R}^3$: any two
$\mathtt{GreenFunctionE\ 3}$ structures on $B(p, R)$ coincide pointwise. -/
theorem greenFunctionE_ball_unique
    (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ) (hR : 0 < R)
    (gf₁ gf₂ : GreenFunctionE 3 (Metric.ball p R))
    (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ Metric.ball p R)
    (y : EuclideanSpace ℝ (Fin 3)) :
    gf₁.G x y = gf₂.G x y := by sorry

/-- An explicit Green's function on the ball $B(p, R) \subseteq \mathbb{R}^3$, built
from the classical Kelvin image construction. -/
noncomputable def greenBallExplicit_exists
    (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ) (hR : 0 < R) :
    GreenFunctionE 3 (Metric.ball p R) := by sorry

/-- Explicit componentwise formula for the boundary derivative of the explicit ball
Green's function in $\mathbb{R}^3$: this is the classical Poisson-kernel weight. -/
theorem fderiv_greenBallExplicit_eq
    (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ) (hR : 0 < R)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ Metric.ball p R)
    (σ : EuclideanSpace ℝ (Fin 3)) (hσ : σ ∈ Metric.sphere p R)
    (i : Fin 3) :
    fderiv ℝ (fun z => (greenBallExplicit_exists p R hR).G x z) σ (EuclideanSpace.single i 1) =
      -(1 - ‖x - p‖ ^ 2 / R ^ 2) / (4 * Real.pi * ‖x - σ‖ ^ 3) * (σ i - p i) := by sorry

/-- By uniqueness, the derivative formula `fderiv_greenBallExplicit_eq` applies to
*every* `GreenFunctionE 3 (Metric.ball p R)`. -/
theorem fderiv_greenFunctionE_ball_spec
    (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ) (hR : 0 < R)
    (gf : GreenFunctionE 3 (Metric.ball p R))
    (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ Metric.ball p R)
    (σ : EuclideanSpace ℝ (Fin 3)) (hσ : σ ∈ Metric.sphere p R)
    (i : Fin 3) :
    fderiv ℝ (fun z => gf.G x z) σ (EuclideanSpace.single i 1) =
      -(1 - ‖x - p‖ ^ 2 / R ^ 2) / (4 * Real.pi * ‖x - σ‖ ^ 3) * (σ i - p i) := by
  have h_eq : (fun z => gf.G x z) = (fun z => (greenBallExplicit_exists p R hR).G x z) := by
    ext z; exact greenFunctionE_ball_unique p R hR gf (greenBallExplicit_exists p R hR) x hx z
  rw [h_eq]
  exact fderiv_greenBallExplicit_eq p R hR x hx σ hσ i

/-- Equational form of `fderiv_greenFunctionE_ball_spec`. -/
theorem fderiv_greenFunctionE_ball_eq
    (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ) (hR : 0 < R)
    (gf : GreenFunctionE 3 (Metric.ball p R))
    (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ Metric.ball p R)
    (σ : EuclideanSpace ℝ (Fin 3)) (hσ : σ ∈ Metric.sphere p R)
    (i : Fin 3) :
    fderiv ℝ (fun z => gf.G x z) σ (EuclideanSpace.single i 1) =
      -(1 - ‖x - p‖ ^ 2 / R ^ 2) / (4 * Real.pi * ‖x - σ‖ ^ 3) * (σ i - p i) := by
  exact fderiv_greenFunctionE_ball_spec p R hR gf x hx σ hσ i

/-- Dirichlet uniqueness on `EuclideanSpace`: transferred from the $L^p$
formulation `dirichlet_uniqueness` via the `EuclideanSpace.equiv` linear isometry. -/
theorem dirichlet_uniquenessE {n : ℕ} (hn : 0 < n)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (hΩc : IsConnected Ω) (hΩb : Bornology.IsBounded Ω)

    (u₁ u₂ : EuclideanSpace ℝ (Fin n) → ℝ)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu₁_reg : ContDiffOn ℝ 2 u₁ Ω) (hu₁_cont : ContinuousOn u₁ (closure Ω))
    (hu₂_reg : ContDiffOn ℝ 2 u₂ Ω) (hu₂_cont : ContinuousOn u₂ (closure Ω))
    (hu₁_pde : ∀ x ∈ Ω, laplacianE u₁ x = f x)
    (hu₂_pde : ∀ x ∈ Ω, laplacianE u₂ x = f x)
    (hu₁_bdy : ∀ σ ∈ frontier Ω, u₁ σ = g σ)
    (hu₂_bdy : ∀ σ ∈ frontier Ω, u₂ σ = g σ) :
    ∀ x ∈ closure Ω, u₁ x = u₂ x := by

  set e := EuclideanSpace.equiv (Fin n) ℝ with he_def

  have h_lap : ∀ (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)),
      laplacianLP (u ∘ ⇑e.symm) (e x) = laplacianE u x := by
    intro u x
    simp only [laplacianLP, laplacianE]
    congr 1; ext i


    have h_single : e.symm (Pi.single i (1 : ℝ)) = EuclideanSpace.single i (1 : ℝ) := by
      apply e.injective
      simp only [ContinuousLinearEquiv.apply_symm_apply]


      rfl
    have h_inner : (fun z => fderiv ℝ (u ∘ ⇑e.symm) z (Pi.single i 1)) =
        (fun z => fderiv ℝ u z (EuclideanSpace.single i 1)) ∘ ⇑e.symm := by
      ext z
      rw [Function.comp_apply, e.symm.comp_right_fderiv (f := u)]
      simp [ContinuousLinearMap.comp_apply, h_single]
    rw [h_inner, e.symm.comp_right_fderiv]
    simp [ContinuousLinearMap.comp_apply, h_single, ContinuousLinearEquiv.symm_apply_apply]

  have h_uniq := dirichlet_uniqueness hn
    (e '' Ω)
    (e.toHomeomorph.isOpenMap _ hΩ)
    (hΩc.image _ e.continuous.continuousOn)
    (e.lipschitz.isBounded_image hΩb)

    (u₁ ∘ ⇑e.symm) (u₂ ∘ ⇑e.symm) (f ∘ ⇑e.symm) (g ∘ ⇑e.symm)
    (hu₁_reg.comp e.symm.contDiff.contDiffOn (by
      intro z hz; simp [Set.mem_image] at hz; obtain ⟨w, hw, rfl⟩ := hz; simpa))
    (hu₁_cont.comp e.symm.continuousOn (by
      intro z hz
      have : e.symm z ∈ closure Ω := by
        rw [show closure (e '' Ω) = e '' closure Ω from (e.toHomeomorph.image_closure Ω).symm] at hz
        obtain ⟨w, hw, hwz⟩ := hz
        rw [← hwz]; simp
        exact hw
      exact this))
    (hu₂_reg.comp e.symm.contDiff.contDiffOn (by
      intro z hz; simp [Set.mem_image] at hz; obtain ⟨w, hw, rfl⟩ := hz; simpa))
    (hu₂_cont.comp e.symm.continuousOn (by
      intro z hz
      have : e.symm z ∈ closure Ω := by
        rw [show closure (e '' Ω) = e '' closure Ω from (e.toHomeomorph.image_closure Ω).symm] at hz
        obtain ⟨w, hw, hwz⟩ := hz
        rw [← hwz]; simp
        exact hw
      exact this))
    (fun z hz => by
      simp [Set.mem_image] at hz; obtain ⟨y, hy, rfl⟩ := hz
      simp only [Function.comp, ContinuousLinearEquiv.symm_apply_apply]
      rw [h_lap u₁ y]; exact hu₁_pde y hy)
    (fun z hz => by
      simp [Set.mem_image] at hz; obtain ⟨y, hy, rfl⟩ := hz
      simp only [Function.comp, ContinuousLinearEquiv.symm_apply_apply]
      rw [h_lap u₂ y]; exact hu₂_pde y hy)
    (fun σ hσ => by
      have hfr : frontier (⇑e '' Ω) = ⇑e '' frontier Ω :=
        (e.toHomeomorph.image_frontier Ω).symm
      rw [hfr] at hσ
      simp [Set.mem_image] at hσ; obtain ⟨y, hy, rfl⟩ := hσ
      simp only [Function.comp, ContinuousLinearEquiv.symm_apply_apply]
      exact hu₁_bdy y hy)
    (fun σ hσ => by
      have hfr : frontier (⇑e '' Ω) = ⇑e '' frontier Ω :=
        (e.toHomeomorph.image_frontier Ω).symm
      rw [hfr] at hσ
      simp [Set.mem_image] at hσ; obtain ⟨y, hy, rfl⟩ := hσ
      simp only [Function.comp, ContinuousLinearEquiv.symm_apply_apply]
      exact hu₂_bdy y hy)

  intro x hx
  have hx' : e x ∈ closure (⇑e '' Ω) := by
    have hcl : closure (⇑e '' Ω) = ⇑e '' closure Ω :=
      (e.toHomeomorph.image_closure Ω).symm
    rw [hcl]; exact Set.mem_image_of_mem e hx
  have h := h_uniq (e x) hx'
  simp only [Function.comp, ContinuousLinearEquiv.symm_apply_apply] at h
  exact h

/-- $\Delta \Phi = \delta_x$ distributionally on `EuclideanSpace ℝ (Fin 3)`: for any
$C^2$ test function $\varphi$ with compact support,
$\int -1/(4\pi |y - x|)\,\Delta \varphi(y)\,dy = \varphi(x)$. -/
theorem fundamental_solution_distributional_delta_E
    (x : EuclideanSpace ℝ (Fin 3)) (φ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hφs : HasCompactSupport φ) :
    ∫ y, (-1 / (4 * Real.pi * ‖y - x‖)) * laplacianE φ y = φ x := by sorry

/-- **Kelvin image** of $x$ with respect to the sphere $\partial B(p, R)$ in
$\mathbb{R}^3$: $x^* = p + (R/\|x - p\|)^2 (x - p)$. -/
def kelvinImageE (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  p + (R / ‖x - p‖) ^ 2 • (x - p)

/-- The Kelvin image of an interior point $x \ne p$ of $B(p, R)$ lies *outside* the
ball, which is the property that makes the Kelvin image useful for constructing
Green's functions on the ball. -/
theorem kelvinImageE_not_in_ball (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ) (hR : 0 < R)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ Metric.ball p R) (hxp : x ≠ p) :
    kelvinImageE p R x ∉ Metric.ball p R := by
  have hxp_pos : (0 : ℝ) < ‖x - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxp)
  have hxp_lt_R : ‖x - p‖ < R := by rwa [Metric.mem_ball, dist_eq_norm] at hx
  rw [Metric.mem_ball, not_lt, dist_eq_norm]
  have h1 : kelvinImageE p R x - p = (R / ‖x - p‖) ^ 2 • (x - p) := by
    simp only [kelvinImageE, add_sub_cancel_left]
  rw [h1, norm_smul, Real.norm_of_nonneg (sq_nonneg _)]
  have hxp_ne : ‖x - p‖ ≠ 0 := ne_of_gt hxp_pos
  have h2 : (R / ‖x - p‖) ^ 2 * ‖x - p‖ = R ^ 2 / ‖x - p‖ := by field_simp
  rw [h2]
  rw [le_div_iff₀ hxp_pos]
  nlinarith [sq_nonneg (R - ‖x - p‖)]

/-- Key Kelvin-image identity: for $\sigma$ on the sphere $\partial B(p, R)$,
$\|x^* - \sigma\| = (R/\|x - p\|)\,\|x - \sigma\|$. This produces the boundary
cancellation of $G$ on $\partial B(p, R)$. -/
theorem kelvinImageE_norm_identity
    (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ) (hR : 0 < R)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ Metric.ball p R) (hxp : x ≠ p)
    (σ : EuclideanSpace ℝ (Fin 3)) (hσ : σ ∈ Metric.sphere p R) :
    ‖kelvinImageE p R x - σ‖ = (R / ‖x - p‖) * ‖x - σ‖ := by sorry

/-- Explicit Green's function on the ball $B(p, R) \subseteq \mathbb{R}^3$
constructed by the Kelvin-image method: $G(x, y) = -\frac{1}{4\pi|y-x|}
+ \frac{R/\|x-p\|}{4\pi|y - x^*|}$, where $x^*$ is the Kelvin image of $x$. The
center case $x = p$ is handled separately. -/
def greenBallFunctionE (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ)
    (x y : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  if x = p then
    -1 / (4 * Real.pi * ‖y - p‖) + 1 / (4 * Real.pi * R)
  else
    -1 / (4 * Real.pi * ‖y - x‖) +
      (R / ‖x - p‖) * (1 / (4 * Real.pi * ‖y - kelvinImageE p R x‖))

/-- Boundary vanishing of the explicit Green's function on the ball: for every
$x \in B(p, R)$ and every $\sigma \in \partial B(p, R)$, $G(x, \sigma) = 0$.
This relies on the Kelvin-image norm identity to balance the two terms. -/
theorem greenBallFunctionE_boundary_zero
    (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ) (hR : 0 < R)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ Metric.ball p R)
    (σ : EuclideanSpace ℝ (Fin 3)) (hσ : σ ∈ frontier (Metric.ball p R)) :
    greenBallFunctionE p R x σ = 0 := by
  have hR_ne : R ≠ 0 := ne_of_gt hR
  have hσ_sphere : σ ∈ Metric.sphere p R := by
    rwa [frontier_ball p hR_ne] at hσ
  have hσ_norm : ‖σ - p‖ = R := by
    have := Metric.mem_sphere.mp hσ_sphere
    rwa [dist_eq_norm] at this
  by_cases hxp : x = p
  ·
    have hG : greenBallFunctionE p R x σ =
      -1 / (4 * Real.pi * ‖σ - p‖) + 1 / (4 * Real.pi * R) := by
      simp [greenBallFunctionE, hxp]
    rw [hG, hσ_norm]
    ring
  ·
    have hxp_pos : (0 : ℝ) < ‖x - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxp)
    have hkelvin : ‖kelvinImageE p R x - σ‖ = (R / ‖x - p‖) * ‖x - σ‖ :=
      kelvinImageE_norm_identity p R hR x hx hxp σ hσ_sphere
    have hσx : σ ≠ x := by
      intro heq
      rw [heq] at hσ_sphere
      have hx_sphere := Metric.mem_sphere.mp hσ_sphere
      rw [dist_eq_norm] at hx_sphere
      have hx_ball := Metric.mem_ball.mp hx
      rw [dist_eq_norm] at hx_ball
      linarith
    have hxσ_pos : (0 : ℝ) < ‖x - σ‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero.mpr (Ne.symm hσx)
    have hG : greenBallFunctionE p R x σ =
      -1 / (4 * Real.pi * ‖σ - x‖) +
        (R / ‖x - p‖) * (1 / (4 * Real.pi * ‖σ - kelvinImageE p R x‖)) := by
      simp [greenBallFunctionE, hxp]
    rw [hG, norm_sub_rev σ (kelvinImageE p R x), hkelvin, norm_sub_rev σ x]
    field_simp
    ring

/-- The integral of the Laplacian of any compactly supported $C^2$ function on
$\mathbb{R}^3$ vanishes: $\int_{\mathbb{R}^3} \Delta \varphi = 0$. This follows from
the divergence theorem applied to a large ball containing $\operatorname{supp} \varphi$. -/
theorem integral_laplacianE_compactSupport_eq_zero
    (φ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hφs : HasCompactSupport φ) :
    ∫ y, laplacianE φ y = 0 := by sorry

/-- Integrability of $\Phi(y - x) \, \Delta \varphi(y)$ on $\mathbb{R}^3$ when
$\varphi \in C^2_c$. The product is locally integrable because $\Phi$ has only a
weak $1/r$ singularity in three dimensions and $\Delta \varphi$ has compact support. -/
theorem integrable_fundamentalSol_mul_laplacianE
    (x : EuclideanSpace ℝ (Fin 3))
    (φ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hφs : HasCompactSupport φ) :
    Integrable (fun y => (-1 / (4 * Real.pi * ‖y - x‖)) * laplacianE φ y) := by sorry

/-- Integrability of $c \cdot \Delta \varphi$ for any constant $c$ when
$\varphi \in C^2_c$. Used to handle the constant correction term in the
ball Green's function. -/
theorem integrable_const_mul_laplacianE
    (c : ℝ)
    (φ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hφs : HasCompactSupport φ) :
    Integrable (fun y => c * laplacianE φ y) := by sorry

/-- Integrability of the Kelvin-image corrector term
$\frac{R}{\|x-p\|} \cdot \frac{1}{4\pi \|y - x^*\|} \cdot \Delta \varphi(y)$
against a $C^2_c$ test function, used in proving the distributional PDE
for the ball Green's function. -/
theorem integrable_corrector_mul_laplacianE
    (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) (hxp : x ≠ p)
    (φ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hφs : HasCompactSupport φ) :
    Integrable (fun y => (R / ‖x - p‖) * (1 / (4 * Real.pi * ‖y - kelvinImageE p R x‖)) * laplacianE φ y) := by sorry

/-- Distributional Green's identity for the explicit ball Green's function: for any
$\varphi \in C^2_c$ with $\operatorname{supp} \varphi \subseteq B(p, R)$ and
$x \in B(p, R)$,
$$\int_{\mathbb{R}^3} G(x, y) \, \Delta \varphi(y) \, dy = \varphi(x).$$
This expresses $\Delta_y G(x, \cdot) = \delta_x$ in the sense of distributions and
uses that the Kelvin image $x^*$ lies outside $B(p, R)$. -/
theorem greenBallFunctionE_distributional_pde
    (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ) (hR : 0 < R)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ Metric.ball p R)
    (φ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hφ : ContDiff ℝ 2 φ) (hφs : HasCompactSupport φ)
    (hφsupp : tsupport φ ⊆ Metric.ball p R) :
    ∫ y, greenBallFunctionE p R x y * laplacianE φ y = φ x := by
  by_cases hxp : x = p
  ·
    subst hxp
    have h_unfold : (fun y => greenBallFunctionE x R x y * laplacianE φ y) =
        (fun y => (-1 / (4 * Real.pi * ‖y - x‖)) * laplacianE φ y +
                  (1 / (4 * Real.pi * R)) * laplacianE φ y) := by
      ext y
      simp only [greenBallFunctionE, if_pos rfl, ite_true]
      ring
    rw [h_unfold]
    rw [integral_add (integrable_fundamentalSol_mul_laplacianE x φ hφ hφs)
        (integrable_const_mul_laplacianE (1 / (4 * Real.pi * R)) φ hφ hφs)]
    rw [fundamental_solution_distributional_delta_E x φ hφ hφs]
    rw [integral_const_mul]
    rw [integral_laplacianE_compactSupport_eq_zero φ hφ hφs]
    ring
  ·
    have h_unfold : (fun y => greenBallFunctionE p R x y * laplacianE φ y) =
        (fun y => (-1 / (4 * Real.pi * ‖y - x‖)) * laplacianE φ y +
                  (R / ‖x - p‖) * (1 / (4 * Real.pi * ‖y - kelvinImageE p R x‖)) * laplacianE φ y) := by
      ext y
      simp only [greenBallFunctionE, if_neg hxp]
      ring
    rw [h_unfold]
    rw [integral_add (integrable_fundamentalSol_mul_laplacianE x φ hφ hφs)
        (integrable_corrector_mul_laplacianE p R x hxp φ hφ hφs)]
    rw [fundamental_solution_distributional_delta_E x φ hφ hφs]


    have h_corrector : ∫ y, (R / ‖x - p‖) * (1 / (4 * Real.pi * ‖y - kelvinImageE p R x‖)) *
        laplacianE φ y = 0 := by
      have h_rewrite : (fun y => (R / ‖x - p‖) * (1 / (4 * Real.pi * ‖y - kelvinImageE p R x‖)) *
          laplacianE φ y) =
          (fun y => (R / ‖x - p‖) * ((1 / (4 * Real.pi * ‖y - kelvinImageE p R x‖)) * laplacianE φ y)) := by
        ext y; ring
      rw [h_rewrite, integral_const_mul]
      have h_neg : (fun y => (1 / (4 * Real.pi * ‖y - kelvinImageE p R x‖)) * laplacianE φ y) =
          (fun y => -((-1 / (4 * Real.pi * ‖y - kelvinImageE p R x‖)) * laplacianE φ y)) := by
        ext y; ring
      rw [h_neg, integral_neg]
      rw [fundamental_solution_distributional_delta_E (kelvinImageE p R x) φ hφ hφs]

      have hx_star_not_in_ball : kelvinImageE p R x ∉ Metric.ball p R :=
        kelvinImageE_not_in_ball p R hR x hx hxp
      have hx_star_not_in_tsupport : kelvinImageE p R x ∉ tsupport φ := by
        intro h_mem
        exact hx_star_not_in_ball (hφsupp h_mem)
      rw [image_eq_zero_of_notMem_tsupport hx_star_not_in_tsupport]
      ring
    rw [h_corrector]
    ring

/-- Existence of the Green's function on the ball $B(p, R) \subseteq \mathbb{R}^3$,
packaged as a `GreenFunctionE` structure built from `greenBallFunctionE`,
`greenBallFunctionE_boundary_zero`, and `greenBallFunctionE_distributional_pde`. -/
noncomputable def green_ball_existsE_spec (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ) (hR : 0 < R) :
  GreenFunctionE 3 (Metric.ball p R) :=
  { G := greenBallFunctionE p R
    domain_open := Metric.isOpen_ball
    boundary_zero := fun x hx σ hσ => greenBallFunctionE_boundary_zero p R hR x hx σ hσ
    distributional_pde := fun x hx φ hφ hφs hφsupp =>
      greenBallFunctionE_distributional_pde p R hR x hx φ hφ hφs hφsupp }

/-- The Green's function on the ball $B(p, R)$, exposed as a `GreenFunctionE` term.
This is the abstract witness consumed by the Poisson-formula proof. -/
noncomputable def green_ball_existsE (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ) (hR : 0 < R) :
  GreenFunctionE 3 (Metric.ball p R) := green_ball_existsE_spec p R hR

/-- Green's second identity applied to a Green's function `gf` for the bounded
open domain $\Omega$: if $\Delta u = h$ in $\Omega$ and $u = g$ on $\partial \Omega$,
then
$$u(x) + \int_{\Omega} h(y) \, G(x, y) \, dy
  + \int_{\partial \Omega} g(\sigma) \, \partial_\nu G(x, \sigma) \, dS(\sigma) = 0.$$
This is the integration-by-parts cornerstone of the representation formula. -/
theorem greens_second_identity_representation_E {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (gf : GreenFunctionE n Ω)
    (u h g : (EuclideanSpace ℝ (Fin n)) → ℝ)
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hu_pde : ∀ x ∈ Ω, laplacianE u x = h x)
    (hu_bdy : ∀ σ ∈ frontier Ω, u σ = g σ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω) :
    u x + (∫ y in Ω, h y * gf.G x y)
      + surfaceIntegralE Ω (fun σ => g σ * normalDerivE Ω (fun z => gf.G x z) σ) = 0 := by sorry

/-- Green's representation formula: a solution of the Dirichlet problem
$\Delta u = h$ in $\Omega$ with $u = g$ on $\partial \Omega$ admits the explicit
representation
$$u(x) = -\int_{\Omega} h(y) \, G(x, y) \, dy
  - \int_{\partial \Omega} g(\sigma) \, \partial_\nu G(x, \sigma) \, dS(\sigma).$$
Obtained immediately by rearranging Green's second identity. -/
theorem green_representation_formulaE {n : ℕ}
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (gf : GreenFunctionE n Ω)
    (u h g : (EuclideanSpace ℝ (Fin n)) → ℝ)
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hu_pde : ∀ x ∈ Ω, laplacianE u x = h x)
    (hu_bdy : ∀ σ ∈ frontier Ω, u σ = g σ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Ω) :
    u x = -(∫ y in Ω, h y * gf.G x y)
      - surfaceIntegralE Ω (fun σ => g σ * normalDerivE Ω (fun z => gf.G x z) σ) := by
  linarith [greens_second_identity_representation_E Ω gf u h g hΩ hΩb hu_pde hu_bdy x hx]

/-- Explicit normal derivative of the ball Green's function on the sphere
$\partial B(p, R) \subseteq \mathbb{R}^3$:
$$\partial_\nu G(x, \sigma) = -\frac{R^2 - \|x - p\|^2}{4 \pi R \, \|x - \sigma\|^3}.$$
This is the Poisson kernel (up to sign) that appears in the Poisson integral formula. -/
theorem normal_deriv_green_ball
    (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ) (hR : 0 < R)
    (gf : GreenFunctionE 3 (Metric.ball p R))
    (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ Metric.ball p R)
    (σ : EuclideanSpace ℝ (Fin 3)) (hσ : σ ∈ Metric.sphere p R) :
    normalDerivE (Metric.ball p R) (fun z => gf.G x z) σ =
      -(R ^ 2 - ‖x - p‖ ^ 2) / (4 * Real.pi * R * ‖x - σ‖ ^ 3) := by

  unfold normalDerivE

  simp_rw [fderiv_greenFunctionE_ball_eq p R hR gf x hx σ hσ]
  simp_rw [outwardUnitNormalE_ball_eq R hR p σ hσ]

  have hR_ne : R ≠ 0 := ne_of_gt hR
  have hσ_norm : ‖σ - p‖ = R := by
    rw [Metric.mem_sphere, dist_eq_norm] at hσ; exact hσ

  have hfactor : ∀ i : Fin 3,
      (-(1 - ‖x - p‖ ^ 2 / R ^ 2) / (4 * Real.pi * ‖x - σ‖ ^ 3) * (σ i - p i)) *
        ((σ i - p i) / R) =
      (-(1 - ‖x - p‖ ^ 2 / R ^ 2) / (4 * Real.pi * ‖x - σ‖ ^ 3 * R)) * ((σ i - p i) ^ 2) := by
    intro i; ring
  simp_rw [hfactor]
  rw [← Finset.mul_sum]

  have hsum : ∑ i : Fin 3, ((σ : EuclideanSpace ℝ (Fin 3)) i -
      (p : EuclideanSpace ℝ (Fin 3)) i) ^ 2 = ‖σ - p‖ ^ 2 := by
    rw [euclideanSpace_norm_sq]; congr 1
  rw [hsum, hσ_norm]
  field_simp

/-- **Poisson integral formula on the ball $B(p, R) \subseteq \mathbb{R}^3$.**
If $u \in C^2(B(p, R)) \cap C(\overline{B(p, R)})$ is harmonic in $B(p, R)$ and
$u = f$ on $\partial B(p, R)$, then for every $x \in B(p, R)$
$$u(x) = \frac{R^2 - \|x - p\|^2}{4 \pi R}
  \int_{\partial B(p, R)} \frac{f(\sigma)}{\|x - \sigma\|^3} \, dS(\sigma),$$
and $u$ is the unique such function (uniqueness from the maximum principle via
`dirichlet_uniquenessE`). This is the explicit solution of the Dirichlet problem
on the ball. -/
theorem poisson_formula
    (p : EuclideanSpace ℝ (Fin 3)) (R : ℝ) (hR : 0 < R)
    (f : EuclideanSpace ℝ (Fin 3) → ℝ) (_hf : ContinuousOn f (Metric.sphere p R))
    (u : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hu_reg : ContDiffOn ℝ 2 u (Metric.ball p R))
    (hu_cont : ContinuousOn u (Metric.closedBall p R))
    (hu_harm : IsHarmonicE u (Metric.ball p R))
    (hu_bdy : ∀ σ ∈ Metric.sphere p R, u σ = f σ)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ Metric.ball p R) :

    u x = (R ^ 2 - ‖x - p‖ ^ 2) / (4 * Real.pi * R) *
      surfaceIntegralE (Metric.ball p R) (fun σ => f σ / ‖x - σ‖ ^ 3)

    ∧ (∀ v : EuclideanSpace ℝ (Fin 3) → ℝ,
        ContDiffOn ℝ 2 v (Metric.ball p R) →
        ContinuousOn v (Metric.closedBall p R) →
        IsHarmonicE v (Metric.ball p R) →
        (∀ σ ∈ Metric.sphere p R, v σ = f σ) →
        ∀ y ∈ Metric.closedBall p R, v y = u y) := by
  constructor
  ·

    have hR_ne : R ≠ 0 := ne_of_gt hR
    have hfrontier : frontier (Metric.ball p R) = Metric.sphere p R :=
      frontier_ball p hR_ne

    let gf := green_ball_existsE p R hR

    have green_rep := green_representation_formulaE (Metric.ball p R) gf u (fun _ => 0) f
      Metric.isOpen_ball Metric.isBounded_ball
      (fun y hy => by rw [hu_harm y hy])
      (fun σ hσ => hu_bdy σ (hfrontier ▸ hσ)) x hx

    simp only [zero_mul, integral_zero, neg_zero, zero_sub] at green_rep

    rw [green_rep]

    unfold surfaceIntegralE
    rw [hfrontier]


    have h_nd_eq : ∀ σ ∈ Metric.sphere p R,
        f σ * normalDerivE (Metric.ball p R) (fun z => gf.G x z) σ =
        -(R ^ 2 - ‖x - p‖ ^ 2) / (4 * Real.pi * R) * (f σ / ‖x - σ‖ ^ 3) := by
      intro σ hσ
      rw [normal_deriv_green_ball p R hR gf x hx σ hσ]
      ring
    rw [setIntegral_congr_fun (Metric.isClosed_sphere.measurableSet) h_nd_eq]
    rw [integral_const_mul]
    simp only [neg_div, neg_mul, neg_neg]

  ·
    intro v hv_reg hv_cont hv_harm hv_bdy y hy
    have hR_ne : R ≠ 0 := ne_of_gt hR

    have hclosure : closure (Metric.ball p R) = Metric.closedBall p R :=
      closure_ball p hR_ne

    have hfrontier : frontier (Metric.ball p R) = Metric.sphere p R :=
      frontier_ball p hR_ne
    exact dirichlet_uniquenessE (by norm_num : (0 : ℕ) < 3) (Metric.ball p R) Metric.isOpen_ball
      ((convex_ball p R).isConnected ⟨p, Metric.mem_ball_self hR⟩) Metric.isBounded_ball v u

      (fun _ => 0) f hv_reg (hclosure ▸ hv_cont) hu_reg (hclosure ▸ hu_cont)
      hv_harm hu_harm
      (fun σ hσ => hv_bdy σ (hfrontier ▸ hσ))
      (fun σ hσ => hu_bdy σ (hfrontier ▸ hσ))
      y (hclosure ▸ hy)

end LaplacePoisson
