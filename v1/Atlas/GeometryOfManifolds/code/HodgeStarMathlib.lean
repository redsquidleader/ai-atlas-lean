/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.Algebra.Module.Alternating.Basic
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped Manifold ComplexConjugate
open MeasureTheory
set_option autoImplicit false

noncomputable section

namespace HodgeStarMathlib

/-- A smooth complex-valued $k$-form on $M$ modelled on $\mathbb{C}^n$: a pointwise alternating
$\mathbb{C}$-multilinear $k$-form on $\mathbb{C}^n$. -/
def SmoothForm (n : ℕ) (M : Type*) [TopologicalSpace M] (k : ℕ) : Type _ :=
  M → (EuclideanSpace ℂ (Fin n)) [⋀^Fin k]→L[ℂ] ℂ

/-- Pointwise additive group structure on smooth $k$-forms. -/
instance instAddCommGroupSmoothForm {n : ℕ} {M : Type*} [TopologicalSpace M] {k : ℕ} :
    AddCommGroup (SmoothForm n M k) := Pi.addCommGroup

/-- Pointwise $\mathbb{C}$-module structure on smooth $k$-forms. -/
instance instModuleSmoothForm {n : ℕ} {M : Type*} [TopologicalSpace M] {k : ℕ} :
    Module ℂ (SmoothForm n M k) := Pi.module _ _ _

/-- Bochner integral $\int_M f \, d\mu$ of a complex-valued function against a measure $\mu$. -/
def integrateScalar {M : Type*} [MeasurableSpace M] (μ : Measure M) (f : M → ℂ) : ℂ :=
  ∫ x, f x ∂μ

/-- Wedge product of smooth forms: $\alpha \wedge \beta$ takes a $k$-form and an $l$-form to a
$(k+l)$-form. -/
noncomputable def wedgeProduct {n : ℕ} {M : Type*} [TopologicalSpace M] {k l : ℕ} :
    SmoothForm n M k → SmoothForm n M l → SmoothForm n M (k + l) := by sorry


/-- Hodge star operator $\ast : \Omega^k \to \Omega^{2n-k}$ on smooth forms on an $n$-complex-
dimensional (real $2n$) manifold. On Kähler manifolds it restricts to
$\bigwedge^{p,q} \to \bigwedge^{n-q, n-p}$. -/
noncomputable def hodgeStar {n : ℕ} {M : Type*} [TopologicalSpace M] {k : ℕ} :
    SmoothForm n M k → SmoothForm n M (2 * n - k) := by sorry


/-- Pointwise complex conjugation $\bar{\alpha}$ of a smooth $k$-form. -/
noncomputable def conjForm {n : ℕ} {M : Type*} [TopologicalSpace M] {k : ℕ} :
    SmoothForm n M k → SmoothForm n M k := by sorry


/-- $L^2$ inner product of smooth $k$-forms: $\langle \alpha, \beta \rangle =
\int_M \alpha \wedge \ast \bar{\beta}$. -/
def L2InnerProduct {n : ℕ} {M : Type*} [TopologicalSpace M] [MeasurableSpace M]
    {k : ℕ} (μ : Measure M) (α β : SmoothForm n M k) : ℂ :=
  integrateScalar μ fun x =>
    (@wedgeProduct n M _ k (2 * n - k) α (@hodgeStar n M _ k (@conjForm n M _ k β))) x
      (fun _ => 0)

/-- Exterior derivative $d : \Omega^k \to \Omega^{k+1}$ on smooth complex forms. -/
noncomputable def extD {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M] {k : ℕ} :
    SmoothForm n M k → SmoothForm n M (k + 1) := by sorry


/-- Codifferential $d^\ast : \Omega^{k+1} \to \Omega^k$, the formal $L^2$-adjoint of $d$. -/
noncomputable def codifferential {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M] {k : ℕ} :
    SmoothForm n M (k + 1) → SmoothForm n M k := by sorry

/-- Hodge–de Rham Laplacian $\Delta = d d^\ast + d^\ast d$ acting on $k$-forms. -/
noncomputable def laplacianForm {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M] {k : ℕ} :
    SmoothForm n M k → SmoothForm n M k := by sorry

/-- The Laplacian annihilates the zero form: $\Delta 0 = 0$. -/
theorem laplacianForm_zero {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M] {k : ℕ} :
    @laplacianForm n M _ _ _ k 0 = 0 := by sorry

/-- A $k$-form $\alpha$ is harmonic iff $\Delta \alpha = 0$. -/
def IsHarmonicForm {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M] {k : ℕ}
    (α : SmoothForm n M k) : Prop :=
  @laplacianForm n M _ _ _ k α = 0

/-- Hodge decomposition: on a compact complex manifold, every smooth $(k+1)$-form decomposes
uniquely as $\alpha = h + d\beta + d^\ast \gamma$ with $h$ harmonic. -/
theorem hodge_decomposition {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M]
    [CompactSpace M] [MeasurableSpace M]
    {k : ℕ} (α : SmoothForm n M (k + 1)) :
    ∃ (h : SmoothForm n M (k + 1)) (β : SmoothForm n M k)
      (γ : SmoothForm n M (k + 1 + 1)),
      @IsHarmonicForm n M _ _ _ (k + 1) h ∧
        α = h + @extD n M _ _ _ k β + @codifferential n M _ _ _ (k + 1) γ := by sorry

end HodgeStarMathlib
