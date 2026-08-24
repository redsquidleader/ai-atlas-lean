/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.FourManifoldsSW

set_option autoImplicit false


/-- The transition map between two charts $e, e'$ of a charted space, given by $e^{-1}$ followed by $e'$. -/
def chartTransition
    {d : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) N]
    (e e' : atlas (EuclideanSpace ℝ (Fin d)) N) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)) :=
  e.1.symm.trans e'.1

/-- A chart transition preserves orientation iff its Jacobian determinant is positive everywhere on its source. -/
def chartTransitionPreservesOrientation
    {d : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) N]
    (e e' : atlas (EuclideanSpace ℝ (Fin d)) N) : Prop :=
  ∀ x ∈ (chartTransition e e').source,
    0 < (fderivWithin ℝ (chartTransition e e') (chartTransition e e').source x).det

/-- A $d$-dimensional charted space is orientable when every pair of chart transitions has positive Jacobian determinant. -/
def IsOrientableManifold
    (d : ℕ) (N : Type*) [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) N] : Prop :=
  ∀ (e e' : atlas (EuclideanSpace ℝ (Fin d)) N),
    chartTransitionPreservesOrientation e e'


/-- A generic pair $(g, \mu)$ ensures that the Seiberg–Witten linearization is surjective at irreducible solutions, the cokernel dimension is zero, and the Fredholm index equals $\tfrac{1}{4}(c_1(L)^2 \cdot [X] - (2\chi + 3\sigma))$. -/
class IsGenericPair
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ⊤ M]
    [CompactSpace M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    [htop : Has4ManifoldTopology M]
    (spinc : SpinCStructure M Ω1 Ω2) where
  cokerDim : SWSolution spinc → ℕ
  fredholmIndex : SWSolution spinc → ℤ
  fredholmIndex_eq : ∀ (sol : SWSolution spinc),
    fredholmIndex sol * 4 = spinc.c₁_L - (2 * htop.euler + 3 * htop.Q.signature)
  linearised_surjective : ∀ (sol : SWSolution spinc), ¬sol.isReducible → cokerDim sol = 0
  no_reducible_solutions : htop.Q.b₂_plus ≥ 1 → ∀ (sol : SWSolution spinc), ¬sol.isReducible


/-- Two SW solutions are gauge-equivalent if some element $f \in \mathcal{G}$ of the gauge group maps one to the other. -/
def SWGaugeEquivalent
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gauge : GaugeActionData spinc)
    (sol₁ sol₂ : SWSolution spinc) : Prop :=
  ∃ (f : gauge.GaugeGroup), gauge.gauge_action f sol₁ = sol₂

/-- Gauge equivalence is reflexive: every SW solution is gauge-equivalent to itself via the identity gauge transformation. -/
theorem SWGaugeEquivalent.refl
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    {spinc : SpinCStructure M Ω1 Ω2}
    (gauge : GaugeActionData spinc)
    (sol : SWSolution spinc) :
    SWGaugeEquivalent gauge sol sol :=
  ⟨1, gauge.gauge_action_one sol⟩

/-- Definition 2: a smooth-manifold structure on the SW moduli space $\mathcal{M}(S, g, \mu) = \{\text{SW solutions}\}/\mathcal{G}$, with the quotient projection identifying gauge orbits with points. -/
structure SWModuliSmoothManifold
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ⊤ M]
    [CompactSpace M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    (spinc : SpinCStructure M Ω1 Ω2)
    [htop : Has4ManifoldTopology M]
    [IsGenericPair spinc] where
  dimension : ℕ
  carrier : Type
  topologicalSpace : TopologicalSpace carrier
  chartedSpace : @ChartedSpace (EuclideanSpace ℝ (Fin dimension)) _ carrier topologicalSpace
  isManifold : letI := topologicalSpace; letI := chartedSpace;
    IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin dimension))) ⊤ carrier
  orientable : letI := topologicalSpace; letI := chartedSpace;
    IsOrientableManifold dimension carrier
  gauge : GaugeActionData spinc
  quotientProj : SWSolution spinc → carrier
  proj_identifies_orbits : ∀ (sol₁ sol₂ : SWSolution spinc),
    SWGaugeEquivalent gauge sol₁ sol₂ → quotientProj sol₁ = quotientProj sol₂
  proj_injective : ∀ (sol₁ sol₂ : SWSolution spinc),
    quotientProj sol₁ = quotientProj sol₂ → SWGaugeEquivalent gauge sol₁ sol₂

/-- The SW moduli space packaged as a compact smooth manifold (smooth manifold structure plus compactness). -/
structure SWModuliManifold
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ⊤ M]
    [CompactSpace M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    (spinc : SpinCStructure M Ω1 Ω2)
    [htop : Has4ManifoldTopology M]
    [IsGenericPair spinc] where
  smooth : SWModuliSmoothManifold spinc
  compactSpace : letI := smooth.topologicalSpace; CompactSpace smooth.carrier


/-- Axiomatic input: for a generic pair, the SW moduli space carries a smooth manifold structure whose dimension equals the Fredholm index. -/
theorem sw_moduli_smooth_structure_axiom
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ⊤ M]
    [CompactSpace M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    [htop : Has4ManifoldTopology M]
    (spinc : SpinCStructure M Ω1 Ω2)
    [hgeneric : IsGenericPair spinc] :
    ∃ (sm : SWModuliSmoothManifold spinc),

      (∀ (sol : SWSolution spinc), (sm.dimension : ℤ) = hgeneric.fredholmIndex sol) ∧

      (Nonempty sm.carrier → Nonempty (SWSolution spinc)) := by sorry

/-- Axiomatic input: the SW moduli space is compact (Uhlenbeck-type a priori estimates). -/
theorem sw_moduli_compactness_axiom
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ⊤ M]
    [CompactSpace M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    [htop : Has4ManifoldTopology M]
    (spinc : SpinCStructure M Ω1 Ω2)
    [hgeneric : IsGenericPair spinc]
    (sm : SWModuliSmoothManifold spinc) :
    letI := sm.topologicalSpace; CompactSpace sm.carrier := by sorry

/-- Dimension formula: $4 \cdot \dim \mathcal{M} = c_1(L)^2 \cdot [X] - (2\chi + 3\sigma)$, obtained by combining the Fredholm index identity with $\dim \mathcal{M} = \mathrm{ind}$. -/
theorem sw_moduli_dimension_formula
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ⊤ M]
    [CompactSpace M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    [htop : Has4ManifoldTopology M]
    (spinc : SpinCStructure M Ω1 Ω2)
    [hgeneric : IsGenericPair spinc]
    (sm : SWModuliSmoothManifold spinc)
    (hdim_eq_index : ∀ (sol : SWSolution spinc), (sm.dimension : ℤ) = hgeneric.fredholmIndex sol)
    (sol : SWSolution spinc) :
    (sm.dimension : ℤ) * 4 = spinc.c₁_L - (2 * htop.euler + 3 * htop.Q.signature) := by

  have hdim : (sm.dimension : ℤ) = hgeneric.fredholmIndex sol := hdim_eq_index sol

  have hindex : hgeneric.fredholmIndex sol * 4 =
    spinc.c₁_L - (2 * htop.euler + 3 * htop.Q.signature) :=
    hgeneric.fredholmIndex_eq sol

  linarith

/-- Theorem 1: for generic $(g, \mu)$, the SW moduli space $\mathcal{M}$ is a smooth, compact, orientable manifold of dimension $d(S) = \tfrac{1}{4}(c_1(L)^2 \cdot [X] - (2\chi + 3\sigma))$. -/
theorem sw_moduli_space_theorem1
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ⊤ M]
    [CompactSpace M]
    {Ω1 Ω2 : Type*} [AddCommGroup Ω1] [Module ℝ Ω1] [AddCommGroup Ω2] [Module ℝ Ω2]
    [htop : Has4ManifoldTopology M]
    (spinc : SpinCStructure M Ω1 Ω2)
    [hgeneric : IsGenericPair spinc] :
    ∃ (Mod : SWModuliManifold spinc),
      Nonempty Mod.smooth.carrier →
        (letI := Mod.smooth.topologicalSpace; letI := Mod.smooth.chartedSpace;
          IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin Mod.smooth.dimension)))
            ⊤ Mod.smooth.carrier) ∧
        (letI := Mod.smooth.topologicalSpace; CompactSpace Mod.smooth.carrier) ∧
        (letI := Mod.smooth.topologicalSpace; letI := Mod.smooth.chartedSpace;
          IsOrientableManifold Mod.smooth.dimension Mod.smooth.carrier) ∧
        (Mod.smooth.dimension : ℤ) * 4 =
          spinc.c₁_L - (2 * htop.euler + 3 * htop.Q.signature) := by

  obtain ⟨sm, hdim_eq_index, hne_sols⟩ := sw_moduli_smooth_structure_axiom spinc

  have hcompact : letI := sm.topologicalSpace; CompactSpace sm.carrier :=
    sw_moduli_compactness_axiom spinc sm

  let Mod : SWModuliManifold spinc := ⟨sm, hcompact⟩
  refine ⟨Mod, fun hne => ⟨?_, ?_, ?_, ?_⟩⟩

  · exact sm.isManifold

  · exact hcompact

  · exact sm.orientable

  ·
    have hsol_ne : Nonempty (SWSolution spinc) := hne_sols hne

    exact sw_moduli_dimension_formula spinc sm hdim_eq_index (Classical.choice hsol_ne)
