/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.ManifoldDFS
import Atlas.GeometryOfManifolds.code.SymplecticManifolds

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff
open DifferentialFormSpace


/-- The cotangent bundle $T^*M$ as the disjoint union $\bigsqcup_{x \in M} T^*_x M$ of cotangent spaces. -/
def CotangentBundle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] : Type _ :=
  Σ (x : M), (TangentSpace I x →ₗ[ℝ] ℝ)

namespace CotangentBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
variable [ChartedSpace H M]

/-- The bundle projection $\pi : T^*M \to M$, $(x, \xi) \mapsto x$. -/
def proj (p : CotangentBundle I M) : M := p.1

/-- Builds a cotangent vector at $x \in M$ from a covector $\xi \in T^*_x M$. -/
def mk (x : M) (ξ : TangentSpace I x →ₗ[ℝ] ℝ) : CotangentBundle I M := ⟨x, ξ⟩

/-- Projection of a built cotangent vector returns its basepoint. -/
@[simp] theorem proj_mk (x : M) (ξ : TangentSpace I x →ₗ[ℝ] ℝ) :
    proj I M (mk I M x ξ) = x := rfl

end CotangentBundle


universe u

section CotangentBundleManifold

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type u} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

/-- The natural topology on $T^*M$ making the projection continuous (axiomatized). -/
noncomputable instance instTopologicalSpaceCotangentBundle :
    TopologicalSpace (CotangentBundle I M) := by
  exact sorry

/-- $T^*M$ inherits a charted space structure with model $H \times E$ (axiomatized). -/
noncomputable instance instChartedSpaceCotangentBundle :
    ChartedSpace (ModelProd H E) (CotangentBundle I M) := by
  exact sorry

/-- $T^*M$ is a smooth manifold with model $I \times \mathrm{id}_E$ (axiomatized). -/
noncomputable instance instIsManifoldCotangentBundle :
    IsManifold (I.prod (modelWithCornersSelf ℝ E)) ∞ (CotangentBundle I M) := by
  exact sorry

end CotangentBundleManifold


section CotangentBundleDFSTypes

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type u} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

/-- The model-with-corners for $T^*M$, namely $I \times \mathrm{id}_E$. -/
noncomputable abbrev cotangentBundleModel :
    ModelWithCorners ℝ (E × E) (ModelProd H E) :=
  I.prod (modelWithCornersSelf ℝ E)

/-- The space of differential $p$-forms on the cotangent bundle $T^*M$. -/
noncomputable abbrev CotangentBundleΩ (p : ℕ) : Type _ :=
  ManifoldΩ (cotangentBundleModel I) (CotangentBundle I M) p

/-- The space of vector fields on the cotangent bundle $T^*M$. -/
noncomputable abbrev CotangentBundleVF : Type _ :=
  ManifoldVF (cotangentBundleModel I) (CotangentBundle I M)

/-- The `DifferentialFormSpace` structure on $T^*M$, induced from its manifold structure. -/
@[reducible]
noncomputable def cotangentBundleDFSInst :
    DifferentialFormSpace (CotangentBundleΩ I M) (CotangentBundleVF I M) :=
  manifoldDFS (cotangentBundleModel I) (CotangentBundle I M)


/-- Instance witness for the differential form space structure on the cotangent bundle. -/
noncomputable instance instCotangentBundleDFS_DFS :
    DifferentialFormSpace (CotangentBundleΩ I M) (CotangentBundleVF I M) :=
  cotangentBundleDFSInst I M

end CotangentBundleDFSTypes


section CotangentBundleDFSInstance

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
variable {H : Type u} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

/-- The canonical (Liouville/tautological) $1$-form $\theta$ on $T^*M$, defined locally by $\theta_{(x,\xi)} = \xi \circ d\pi$. -/
noncomputable def liouvilleForm : CotangentBundleΩ I M 1 := by
  exact sorry

/-- The canonical symplectic form $-d\theta$ on $T^*M$ is nondegenerate as a pairing on vector fields. -/
lemma cotangent_symplectic_nondegenerate :
    Function.Injective (fun (X : CotangentBundleVF I M) =>
      (cotangentBundleDFSInst I M).ι X
        ((cotangentBundleDFSInst I M).d (liouvilleForm I M))) := by
  exact sorry

/-- The cotangent bundle $T^*M$ equipped with its canonical symplectic structure $\omega_0 = d\theta$. -/
noncomputable def cotangentSymplecticManifold :
    SymplecticManifold (CotangentBundleΩ I M) (CotangentBundleVF I M) :=
  ⟨(cotangentBundleDFSInst I M).d (liouvilleForm I M),
   (cotangentBundleDFSInst I M).d_squared (liouvilleForm I M),
   cotangent_symplectic_nondegenerate I M⟩

/-- The zero section $M \hookrightarrow T^*M$, $x \mapsto (x, 0)$, as a DFS-morphism. -/
noncomputable def zeroSectionMorphism :
    @DFSMorphism (ManifoldΩ I M) (ManifoldVF I M) (CotangentBundleΩ I M) (CotangentBundleVF I M)
      (manifoldDFS I M) (cotangentBundleDFSInst I M) := by
  exact sorry

/-- The Liouville form pulls back to zero along the zero section: $0^*\theta = 0$. -/
lemma liouville_zero_section_eq :
    (zeroSectionMorphism I M).pullback (liouvilleForm I M) =
      (0 : ManifoldΩ I M 1) := by
  exact sorry

/-- Assembles all the data above into a `CotangentBundleDFS` structure for $T^*M$. -/
noncomputable instance instCotangentBundleDFS :
    @CotangentBundleDFS
      (ManifoldΩ I M) (ManifoldVF I M)
      (CotangentBundleΩ I M) (CotangentBundleVF I M)
      (manifoldDFS I M) (cotangentBundleDFSInst I M) where
  dimX := Module.finrank ℝ E
  dimX_pos := Module.finrank_pos
  liouville := liouvilleForm I M
  canonical_symplectic := cotangentSymplecticManifold I M
  symplectic_eq_d_liouville := by


    exact sorry
  zeroSection := zeroSectionMorphism I M
  liouville_zero_section := liouville_zero_section_eq I M

end CotangentBundleDFSInstance


section Theorems

variable {EI : Type u} [NormedAddCommGroup EI] [NormedSpace ℝ EI]
  [FiniteDimensional ℝ EI] [Nontrivial EI]
variable {HI : Type u} [TopologicalSpace HI]
variable (I : ModelWithCorners ℝ EI HI)
variable (M : Type u) [TopologicalSpace M] [ChartedSpace HI M]
variable [IsManifold I ∞ M]

/-- Convenience abbreviation for the `CotangentBundleDFS` structure of $T^*M$. -/
noncomputable abbrev cotangentBDFS :
    @CotangentBundleDFS
      (ManifoldΩ I M) (ManifoldVF I M)
      (CotangentBundleΩ I M) (CotangentBundleVF I M)
      (manifoldDFS I M) (cotangentBundleDFSInst I M) :=
  instCotangentBundleDFS I M

/-- The canonical symplectic $2$-form $\omega_0$ on $T^*M$. -/
noncomputable def cotangentOmega :
    CotangentBundleΩ I M 2 :=
  (cotangentBDFS I M).canonical_symplectic.ω

/-- The canonical Liouville $1$-form $\theta$ on $T^*M$. -/
noncomputable def cotangentLiouville :
    CotangentBundleΩ I M 1 :=
  (cotangentBDFS I M).liouville

/-- The canonical symplectic form on $T^*M$ is exact, $\omega_0 = d\theta$. -/
theorem cotangentBundle_symplectic_eq_d_liouville :
    cotangentOmega I M =
      @DifferentialFormSpace.d _ _ (cotangentBundleDFSInst I M) 1
        (cotangentLiouville I M) := by
  unfold cotangentOmega cotangentLiouville
  exact (cotangentBDFS I M).symplectic_eq_d_liouville

end Theorems
