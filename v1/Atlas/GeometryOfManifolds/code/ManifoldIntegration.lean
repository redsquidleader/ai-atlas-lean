/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.Integration
import Atlas.GeometryOfManifolds.code.ManifoldDFS

set_option autoImplicit false

open DifferentialFormSpace

open scoped Manifold ContDiff


/-- A smooth manifold $M$ is compact and oriented: it carries a compact topology together with
an (abstractly recorded) orientation, the standard hypothesis under which Stokes-type integration
is defined. -/
class IsCompactOrientedManifold
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] : Prop where
  compact : CompactSpace M
  oriented : True

/-- Projects out the underlying `CompactSpace` structure of a compact oriented manifold. -/
theorem IsCompactOrientedManifold.compactSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M]
    (h : IsCompactOrientedManifold I M) : CompactSpace M :=
  h.compact


/-- For a compact oriented smooth manifold $(M, I)$, this produces the Stokes-style integration
data on its differential form space: the integration map $\int_M : \Omega^{\dim M}(M) \to \mathbb{R}$
and associated pairings used to formulate Stokes' theorem. -/
noncomputable def manifoldStokesIntegration
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [IsCompactOrientedManifold I M] :
    @StokesIntegration (ManifoldΩ I M) (ManifoldVF I M) (instManifoldDFS I M) := by sorry


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [IsCompactOrientedManifold I M]

/-- The dimension $\dim M$ of the manifold $M$, as recorded by its Stokes integration data. -/
noncomputable def manifoldDim : ℕ :=
  (manifoldStokesIntegration I M).n

/-- The top-degree integration map $\int_M : \Omega^{\dim M}(M) \to \mathbb{R}$ on a compact
oriented smooth manifold. -/
noncomputable def manifoldIntegrate :
    ManifoldΩ I M (manifoldDim I M) → ℝ :=
  (manifoldStokesIntegration I M).integrate


/-- The period pairing $\Omega^p(M) \times \Omega^p(M) \to \mathbb{R}$ induced by integration on
$M$, generalising $\langle \alpha, \beta \rangle = \int_M \alpha \wedge \star \beta$. -/
noncomputable def manifold_period_pairing
    (p : ℕ) :
    ManifoldΩ I M p → ManifoldΩ I M p → ℝ :=
  (manifoldStokesIntegration I M).inner_prod p
