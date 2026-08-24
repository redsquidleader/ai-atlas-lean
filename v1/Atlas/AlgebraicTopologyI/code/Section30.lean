/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicTopologyI.code.Section26
import Atlas.AlgebraicTopologyI.code.Section33
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Projection

open Matrix

namespace SymmetricBilinearForms

/-- Two square matrices `M`, `N` over a commutative ring are *congruent* if
there exists an invertible matrix `A` such that `A * M * Aᵀ = N`. This is the
matrix-level equivalence relation underlying isometry of bilinear forms. -/
def MatrixCongruent {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (M N : Matrix n n R) : Prop :=
  ∃ A : Matrix n n R, IsUnit A.det ∧ A * M * Aᵀ = N

/-- The matrix `H ⊕ ⟨1⟩` over `F₂`, formed by the hyperbolic plane and a
rank-one form with diagonal entry `1`. This is the model form used in
Claim 30.7. -/
def hyperbolicPlusIdentity : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

/-- Claim 30.7: the form `H ⊕ ⟨1⟩` is congruent over `F₂` to the identity
form `⟨1⟩ ⊕ ⟨1⟩ ⊕ ⟨1⟩`. -/
theorem hyperbolicPlusIdentity_matrixCongruent_one :
    MatrixCongruent hyperbolicPlusIdentity (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  refine ⟨!![1, 1, 1; 1, 0, 1; 0, 1, 1], ?_, ?_⟩
  ·
    decide
  ·
    decide

end SymmetricBilinearForms

namespace AlgebraicTopologyI

/-- Definition 30.1: a *topological manifold* is a Hausdorff space that is
locally homeomorphic to some Euclidean space at every point (the dimension
may a priori depend on the point). -/
class IsTopologicalManifold (M : Type*) [TopologicalSpace M] : Prop where
  hausdorff : T2Space M
  locally_euclidean : ∀ x : M, ∃ n : ℕ, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
    Nonempty (U ≃ₜ EuclideanSpace ℝ (Fin n))

/-- A *topological `n`-manifold*: a Hausdorff space equipped with a charted
space structure modelled on `ℝⁿ`. This is the dimension-fixed variant of
`IsTopologicalManifold`. -/
class TopologicalManifold (n : ℕ) (M : Type*) [TopologicalSpace M]
    extends ChartedSpace (EuclideanSpace ℝ (Fin n)) M where
  [hausdorff : T2Space M]

attribute [instance] TopologicalManifold.hausdorff

/-- A Hausdorff charted space modelled on `ℝⁿ` automatically gets the
`TopologicalManifold n` instance. -/
instance (priority := 100) instTopologicalManifold (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M] :
    TopologicalManifold n M where
  hausdorff := inferInstance

end AlgebraicTopologyI

section PoincareDuality

open CategoryTheory AlgebraicTopology LinearMap SingularCohomology

/-- Singular cohomology with coefficients in `F₂ = ZMod 2`, as a type. -/
abbrev SingularCohomology.CohomZMod2 (X : TopCat.{0}) (n : ℕ) : Type :=
  (singularCohomology (ZMod 2) X (ModuleCat.of (ZMod 2) (ZMod 2)) n : Type)

/-- Singular homology with coefficients in `F₂ = ZMod 2`, as a type. -/
abbrev HomolZMod2 (X : TopCat.{0}) (n : ℕ) : Type :=
  (singularHomologyModule (ZMod 2) X n : Type)

/-- The pairing `H^p(X; F₂) × H^q(X; F₂) → F₂` induced by cup product with a
fixed homology class `μ ∈ H_dim(X; F₂)`, given by
`(α, β) ↦ ⟨α ⌣ β, μ⟩`. Used to formulate Poincaré duality. -/
noncomputable def cupProductPairing
    (X : TopCat.{0}) (dim : ℕ) (μ : HomolZMod2 X dim)
    (p q : ℕ) (hpq : p + q = dim) :
    SingularCohomology.CohomZMod2 X p →ₗ[ZMod 2]
    SingularCohomology.CohomZMod2 X q →ₗ[ZMod 2] ZMod 2 :=
  let μ' : (singularHomologyModule (ZMod 2) X (p + q) : Type) := hpq ▸ μ
  TensorProduct.curry
    ((LinearMap.flip (kroneckerPairing (ZMod 2) X (p + q)) μ') ∘ₗ
     (cupProduct (ZMod 2) X p q).hom)


/-- Theorem 30.2 (`F₂`-Poincaré duality). On a closed (compact, Hausdorff)
topological `dim`-manifold there exists a *unique* fundamental class
`μ ∈ H_dim(M; F₂)` such that, for every `p + q = dim`, the cup-product
pairing `H^p(M; F₂) × H^q(M; F₂) → F₂` is a perfect pairing. -/
theorem poincareDuality_F2
    (dim : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin dim)) M] [T2Space M] [CompactSpace M] :
    ∃! (μ : HomolZMod2 (TopCat.of M) dim),
      ∀ (p q : ℕ) (hpq : p + q = dim),
        (cupProductPairing (TopCat.of M) dim μ p q hpq).IsPerfPair := by sorry


end PoincareDuality

noncomputable section

namespace SurfacesAndBilinearForms

open CategoryTheory AlgebraicTopology SingularCohomology

/-- A *compact surface*: a compact, connected, Hausdorff topological space
with a charted-space structure on `ℝ²` that makes it a `C⁰` manifold. This
is the geometric setting for the classification of surfaces. -/
structure CompactSurface where
  toTopCat : TopCat.{0}
  compact : CompactSpace toTopCat
  connected : ConnectedSpace toTopCat
  t2 : T2Space toTopCat
  charted : ChartedSpace (EuclideanSpace ℝ (Fin 2)) toTopCat
  isManifold : letI := charted;
    IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) 0 toTopCat

/-- Coerce a `CompactSurface` to its underlying `TopCat` object. -/
instance : CoeSort CompactSurface TopCat.{0} := ⟨CompactSurface.toTopCat⟩

attribute [instance] CompactSurface.compact CompactSurface.connected
  CompactSurface.t2 CompactSurface.charted

/-- Make the `C⁰`-manifold structure of a `CompactSurface` available
automatically through typeclass inference. -/
instance (S : CompactSurface) :
    IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) 0 S.toTopCat :=
  S.isManifold


/-- The underlying topological space of the connected sum `S₁ ♯ S₂` of two
compact surfaces: remove an open disk from each surface and glue along the
resulting boundary circles. -/
noncomputable def connectedSumTopCat (S₁ S₂ : CompactSurface) : TopCat.{0} := by sorry


/-- The connected sum of two compact surfaces is compact. -/
theorem connectedSum_compact (S₁ S₂ : CompactSurface) :
    CompactSpace (connectedSumTopCat S₁ S₂) := by sorry


/-- The connected sum of two compact surfaces is connected. -/
theorem connectedSum_connected (S₁ S₂ : CompactSurface) :
    ConnectedSpace (connectedSumTopCat S₁ S₂) := by sorry


/-- The connected sum of two compact surfaces is Hausdorff. -/
theorem connectedSum_t2 (S₁ S₂ : CompactSurface) :
    T2Space (connectedSumTopCat S₁ S₂) := by sorry


/-- A charted space structure on the connected sum modelled on `ℝ²`. -/
noncomputable def connectedSum_charted (S₁ S₂ : CompactSurface) :
    ChartedSpace (EuclideanSpace ℝ (Fin 2)) (connectedSumTopCat S₁ S₂) := by sorry

/-- The connected sum `S₁ ♯ S₂` of two compact surfaces, packaged as a
`CompactSurface`. -/
def connectedSum (S₁ S₂ : CompactSurface) : CompactSurface where
  toTopCat := connectedSumTopCat S₁ S₂
  compact := connectedSum_compact S₁ S₂
  connected := connectedSum_connected S₁ S₂
  t2 := connectedSum_t2 S₁ S₂
  charted := connectedSum_charted S₁ S₂
  isManifold := by
    letI := connectedSum_charted S₁ S₂
    infer_instance

scoped infixl:65 " ♯ " => connectedSum

/-- The fundamental class `[S] ∈ H_2(S; F₂)` of a compact surface, provided
by `F₂`-Poincaré duality. -/
noncomputable def CompactSurface.fundamentalClass (S : CompactSurface) :
    HomolZMod2 S.toTopCat 2 := by sorry


/-- The intersection form on `H¹(S; F₂)` of a compact surface `S`: the
symmetric bilinear form `(α, β) ↦ ⟨α ⌣ β, [S]⟩`. -/
def intersectionForm (S : CompactSurface) :
    LinearMap.BilinForm (ZMod 2) (CohomZMod2 S.toTopCat 1) :=
  cupProductPairing S.toTopCat 2 S.fundamentalClass 1 1 rfl

/-- The orthogonal direct sum `B₁ ⊥ B₂` of two `F₂`-bilinear forms on the
product space `V₁ × V₂`, defined by `((x₁, x₂), (y₁, y₂)) ↦ B₁(x₁, y₁) + B₂(x₂, y₂)`. -/
def orthogonalDirectSumForm
    {V₁ V₂ : Type} [AddCommGroup V₁] [Module (ZMod 2) V₁]
    [AddCommGroup V₂] [Module (ZMod 2) V₂]
    (B₁ : LinearMap.BilinForm (ZMod 2) V₁)
    (B₂ : LinearMap.BilinForm (ZMod 2) V₂) :
    LinearMap.BilinForm (ZMod 2) (V₁ × V₂) :=
  LinearMap.mk₂ (ZMod 2)
    (fun x y => B₁ x.1 y.1 + B₂ x.2 y.2)
    (fun x₁ x₂ y => by
      simp only [map_add, LinearMap.add_apply, Prod.fst_add, Prod.snd_add]; ring)
    (fun r x y => by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Prod.smul_fst,
        Prod.smul_snd]; ring)
    (fun x y₁ y₂ => by
      simp only [map_add, Prod.fst_add, Prod.snd_add]; ring)
    (fun r x y => by
      simp only [map_smul, smul_eq_mul, Prod.smul_fst, Prod.smul_snd]; ring)

/-- The *punctured surface* `S ∖ B`: remove a small open disk from `S`
using a chart centred at an arbitrary point. -/
def puncturedSurface (S : CompactSurface) : TopCat.{0} :=
  let x : S.toTopCat := Classical.arbitrary _
  let φ := chartAt (EuclideanSpace ℝ (Fin 2)) x
  let U : Set S.toTopCat := φ.source ∩ ⇑φ ⁻¹' Metric.ball (φ x) 1
  TopCat.of ↥Uᶜ

/-- The continuous inclusion `S ∖ B ↪ S` of the punctured surface into
the original surface. -/
def puncturedSurfaceInclusion (S : CompactSurface) :
    puncturedSurface S ⟶ S.toTopCat :=
  ⟨Subtype.val, continuous_subtype_val⟩


/-- The inclusion of the punctured surface into the surface induces an
isomorphism on `H¹(–; F₂)` (removing an open disk does not change `H¹`). -/
theorem puncturedSurfaceInclusion_H1_isIso (S : CompactSurface) :
    IsIso (singularCohomologyMap (ZMod 2) (puncturedSurfaceInclusion S) 1) := by sorry

/-- Package `puncturedSurfaceInclusion_H1_isIso` as a categorical isomorphism
`H¹(S; F₂) ≅ H¹(S ∖ B; F₂)`. -/
def puncturedSurfaceInclusion_H1_iso (S : CompactSurface) :
    singularCohomology (ZMod 2) S.toTopCat (ModuleCat.of (ZMod 2) (ZMod 2)) 1 ≅
      singularCohomology (ZMod 2) (puncturedSurface S) (ModuleCat.of (ZMod 2) (ZMod 2)) 1 :=
  letI := puncturedSurfaceInclusion_H1_isIso S
  asIso (singularCohomologyMap (ZMod 2) (puncturedSurfaceInclusion S) 1)

/-- The induced linear isomorphism `H¹(S ∖ B; F₂) ≃ₗ H¹(S; F₂)`. -/
def puncturedSurface_H1_iso (S : CompactSurface) :
    CohomZMod2 (puncturedSurface S) 1 ≃ₗ[ZMod 2] CohomZMod2 S.toTopCat 1 :=
  (puncturedSurfaceInclusion_H1_iso S).symm.toLinearEquiv


/-- Inclusion of the first punctured factor `S₁ ∖ B₁` into the connected
sum `S₁ ♯ S₂`. -/
noncomputable def puncturedSurfaceInclusionConnectedSum₁ (S₁ S₂ : CompactSurface) :
    puncturedSurface S₁ ⟶ (S₁ ♯ S₂).toTopCat := by sorry


/-- Inclusion of the second punctured factor `S₂ ∖ B₂` into the connected
sum `S₁ ♯ S₂`. -/
noncomputable def puncturedSurfaceInclusionConnectedSum₂ (S₁ S₂ : CompactSurface) :
    puncturedSurface S₂ ⟶ (S₁ ♯ S₂).toTopCat := by sorry

/-- Mayer–Vietoris restriction map on `H¹` for the connected sum: send a
cohomology class to its pair of restrictions to the two punctured factors. -/
def connectedSum_mv_restrictionMap (S₁ S₂ : CompactSurface) :
    CohomZMod2 (S₁ ♯ S₂).toTopCat 1 →ₗ[ZMod 2]
      CohomZMod2 (puncturedSurface S₁) 1 × CohomZMod2 (puncturedSurface S₂) 1 :=
  LinearMap.prod
    (singularCohomologyMap (ZMod 2)
      (puncturedSurfaceInclusionConnectedSum₁ S₁ S₂) 1).hom
    (singularCohomologyMap (ZMod 2)
      (puncturedSurfaceInclusionConnectedSum₂ S₁ S₂) 1).hom


/-- The Mayer–Vietoris connecting homomorphism in degree zero,
`H⁰(S¹; F₂) ≅ F₂ → H¹(S₁ ♯ S₂; F₂)`. -/
noncomputable def connectedSum_mv_connectingHomomorphism₀ (S₁ S₂ : CompactSurface) :
    ZMod 2 →ₗ[ZMod 2] CohomZMod2 (S₁ ♯ S₂).toTopCat 1 := by sorry


/-- Exactness of the Mayer–Vietoris sequence at the `H¹(S₁ ♯ S₂)` spot:
the image of the connecting homomorphism `δ⁰` equals the kernel of the
restriction map. -/
theorem connectedSum_mv_exact_at_H1 (S₁ S₂ : CompactSurface) :
    Function.Exact (connectedSum_mv_connectingHomomorphism₀ S₁ S₂)
      (connectedSum_mv_restrictionMap S₁ S₂) := by sorry

/-- The Mayer–Vietoris restriction map in degree zero, which on
`F₂ × F₂ → F₂` simply adds the two components. -/
def connectedSum_mv_restrictionMap₀ (_S₁ _S₂ : CompactSurface) :
    ZMod 2 × ZMod 2 →ₗ[ZMod 2] ZMod 2 :=
  { toFun := fun p => p.1 + p.2
    map_add' := fun x y => by
      simp only [Prod.fst_add, Prod.snd_add]
      ring
    map_smul' := fun r x => by
      simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_eq_mul]
      ring }


/-- Exactness at the `H⁰(S¹; F₂)` spot of the Mayer–Vietoris sequence:
the image of `H⁰(S₁∖B) ⊕ H⁰(S₂∖B) → H⁰(S¹)` equals the kernel of `δ⁰`. -/
theorem connectedSum_mv_exact_at_H0 (S₁ S₂ : CompactSurface) :
    Function.Exact (connectedSum_mv_restrictionMap₀ S₁ S₂)
      (connectedSum_mv_connectingHomomorphism₀ S₁ S₂) := by sorry

/-- The degree-zero restriction map `F₂ × F₂ → F₂` (addition) is
surjective. -/
theorem connectedSum_mv_restrictionMap₀_surjective (S₁ S₂ : CompactSurface) :
    Function.Surjective (connectedSum_mv_restrictionMap₀ S₁ S₂) := by
  intro x
  exact ⟨(x, 0), by simp [connectedSum_mv_restrictionMap₀]⟩

/-- Since the preceding restriction map is surjective, the connecting
homomorphism `δ⁰ : H⁰(S¹) → H¹(S₁ ♯ S₂)` is the zero map. -/
theorem connectedSum_mv_connectingHomomorphism₀_eq_zero (S₁ S₂ : CompactSurface) :
    connectedSum_mv_connectingHomomorphism₀ S₁ S₂ = 0 := by
  ext
  simp only [LinearMap.zero_apply]
  have hsurj := connectedSum_mv_restrictionMap₀_surjective S₁ S₂
  have hex := connectedSum_mv_exact_at_H0 S₁ S₂
  obtain ⟨m, hm⟩ := hsurj (1 : ZMod 2)
  have h := hex.apply_apply_eq_zero m
  rw [hm] at h
  exact h

/-- Because `δ⁰ = 0`, exactness at `H¹(S₁ ♯ S₂)` forces the restriction
map to be injective. -/
theorem connectedSum_mv_restrictionMap_injective (S₁ S₂ : CompactSurface) :
    Function.Injective (connectedSum_mv_restrictionMap S₁ S₂) := by
  have hex := connectedSum_mv_exact_at_H1 S₁ S₂
  have hδ := connectedSum_mv_connectingHomomorphism₀_eq_zero S₁ S₂
  have hexz : Function.Exact (⇑(0 : ZMod 2 →ₗ[ZMod 2] CohomZMod2 (S₁ ♯ S₂).toTopCat 1))
      ⇑(connectedSum_mv_restrictionMap S₁ S₂) := by
    rw [← hδ]; exact hex
  rwa [LinearMap.exact_zero_iff_injective (ZMod 2)] at hexz


/-- The Mayer–Vietoris map `H¹(S₁∖B) × H¹(S₂∖B) → H¹(S¹)` given by
restricting to the boundary circle `S¹`. -/
noncomputable def connectedSum_mv_gammaMap (S₁ S₂ : CompactSurface) :
    CohomZMod2 (puncturedSurface S₁) 1 × CohomZMod2 (puncturedSurface S₂) 1 →ₗ[ZMod 2]
      CohomZMod2 (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) 1 := by sorry


/-- Exactness at the `H¹(S₁∖B) × H¹(S₂∖B)` spot of the Mayer–Vietoris
sequence: an element of the product is in the image of the restriction map
iff it is annihilated by the boundary-restriction map. -/
theorem connectedSum_mv_exact_at_prod (S₁ S₂ : CompactSurface)
    (b : CohomZMod2 (puncturedSurface S₁) 1 × CohomZMod2 (puncturedSurface S₂) 1) :
    connectedSum_mv_gammaMap S₁ S₂ b = 0 ↔
      b ∈ LinearMap.range (connectedSum_mv_restrictionMap S₁ S₂) := by sorry


/-- The Mayer–Vietoris connecting homomorphism in degree one,
`H¹(S¹; F₂) → H²(S₁ ♯ S₂; F₂)`. -/
noncomputable def connectedSum_mv_connectingHomomorphism₁ (S₁ S₂ : CompactSurface) :
    CohomZMod2 (TopCat.of (Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1)) 1 →ₗ[ZMod 2]
      CohomZMod2 (S₁ ♯ S₂).toTopCat 2 := by sorry


/-- Exactness of the Mayer–Vietoris sequence at the `H¹(S¹; F₂)` spot:
the image of `γ` equals the kernel of `δ¹`. -/
theorem connectedSum_mv_exact_at_circle (S₁ S₂ : CompactSurface) :
    Function.Exact (connectedSum_mv_gammaMap S₁ S₂)
      (connectedSum_mv_connectingHomomorphism₁ S₁ S₂) := by sorry


/-- The degree-one connecting homomorphism `δ¹ : H¹(S¹) → H²(S₁ ♯ S₂)`
is injective (it is the dual to the inclusion of the fundamental class). -/
theorem connectedSum_mv_connectingHomomorphism₁_injective (S₁ S₂ : CompactSurface) :
    Function.Injective (connectedSum_mv_connectingHomomorphism₁ S₁ S₂) := by sorry

/-- Since `δ¹` is injective, exactness at `H¹(S¹)` forces the
boundary-restriction map `γ` to vanish identically. -/
theorem connectedSum_mv_gammaMap_eq_zero (S₁ S₂ : CompactSurface) :
    connectedSum_mv_gammaMap S₁ S₂ = 0 := by
  have hex := connectedSum_mv_exact_at_circle S₁ S₂
  have hinj := connectedSum_mv_connectingHomomorphism₁_injective S₁ S₂

  have hker : (connectedSum_mv_connectingHomomorphism₁ S₁ S₂).ker =
      (connectedSum_mv_gammaMap S₁ S₂).range := hex.linearMap_ker_eq
  have hkerbot : (connectedSum_mv_connectingHomomorphism₁ S₁ S₂).ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  have hrange : (connectedSum_mv_gammaMap S₁ S₂).range = ⊥ := by rw [← hker, hkerbot]
  exact LinearMap.range_eq_bot.mp hrange

/-- Since `γ = 0`, exactness at the product term implies the restriction
map `H¹(S₁ ♯ S₂) → H¹(S₁∖B) × H¹(S₂∖B)` is surjective. -/
theorem connectedSum_mv_restrictionMap_surjective (S₁ S₂ : CompactSurface) :
    Function.Surjective (connectedSum_mv_restrictionMap S₁ S₂) := by
  intro b
  have hγ := connectedSum_mv_gammaMap_eq_zero S₁ S₂
  have h : connectedSum_mv_gammaMap S₁ S₂ b = 0 := by simp [hγ]
  exact LinearMap.mem_range.mp ((connectedSum_mv_exact_at_prod S₁ S₂ b).mp h)

/-- Combine injectivity and surjectivity: the restriction map is
bijective. -/
theorem connectedSum_mv_restrictionMap_bijective (S₁ S₂ : CompactSurface) :
    Function.Bijective (connectedSum_mv_restrictionMap S₁ S₂) :=
  ⟨connectedSum_mv_restrictionMap_injective S₁ S₂,
   connectedSum_mv_restrictionMap_surjective S₁ S₂⟩

/-- Mayer–Vietoris isomorphism (punctured version):
`H¹(S₁ ♯ S₂; F₂) ≃ H¹(S₁∖B; F₂) × H¹(S₂∖B; F₂)`. -/
def mayerVietoris_connectedSum_punctured_iso (S₁ S₂ : CompactSurface) :
    CohomZMod2 (S₁ ♯ S₂).toTopCat 1 ≃ₗ[ZMod 2]
      CohomZMod2 (puncturedSurface S₁) 1 × CohomZMod2 (puncturedSurface S₂) 1 :=
  LinearEquiv.ofBijective
    (connectedSum_mv_restrictionMap S₁ S₂)
    (connectedSum_mv_restrictionMap_bijective S₁ S₂)

/-- Proposition 30.8: the Mayer–Vietoris isomorphism
`H¹(S₁ ♯ S₂; F₂) ≃ H¹(S₁; F₂) × H¹(S₂; F₂)`, obtained by combining the
punctured-surface isomorphism with the isomorphisms
`H¹(Sᵢ∖B; F₂) ≃ H¹(Sᵢ; F₂)`. -/
def mayerVietoris_connectedSum_H1_iso (S₁ S₂ : CompactSurface) :
    CohomZMod2 (S₁ ♯ S₂).toTopCat 1 ≃ₗ[ZMod 2]
      CohomZMod2 S₁.toTopCat 1 × CohomZMod2 S₂.toTopCat 1 :=
  (mayerVietoris_connectedSum_punctured_iso S₁ S₂) ≪≫ₗ
    (LinearEquiv.prodCongr (puncturedSurface_H1_iso S₁) (puncturedSurface_H1_iso S₂))


/-- Compatibility of the intersection form with the Mayer–Vietoris
decomposition: the intersection form on `S₁ ♯ S₂` decomposes as the sum of
the pulled-back intersection forms on `S₁` and `S₂`. -/
theorem mayerVietoris_connectedSum_H1_intersectionForm_compat
    (S₁ S₂ : CompactSurface)
    (x y : CohomZMod2 (S₁ ♯ S₂).toTopCat 1) :
    intersectionForm (S₁ ♯ S₂) x y =
      intersectionForm S₁
        (puncturedSurface_H1_iso S₁
          (mayerVietoris_connectedSum_punctured_iso S₁ S₂ x).1)
        (puncturedSurface_H1_iso S₁
          (mayerVietoris_connectedSum_punctured_iso S₁ S₂ y).1) +
      intersectionForm S₂
        (puncturedSurface_H1_iso S₂
          (mayerVietoris_connectedSum_punctured_iso S₁ S₂ x).2)
        (puncturedSurface_H1_iso S₂
          (mayerVietoris_connectedSum_punctured_iso S₁ S₂ y).2) := by sorry


/-- Under the Mayer–Vietoris isomorphism, the intersection form of
`S₁ ♯ S₂` is the orthogonal direct sum of the intersection forms of `S₁`
and `S₂`. -/
theorem mayerVietoris_connectedSum_H1_orthogonal (S₁ S₂ : CompactSurface)
    (x y : CohomZMod2 (S₁ ♯ S₂).toTopCat 1) :
    intersectionForm (S₁ ♯ S₂) x y =
      orthogonalDirectSumForm (intersectionForm S₁) (intersectionForm S₂)
        (mayerVietoris_connectedSum_H1_iso S₁ S₂ x)
        (mayerVietoris_connectedSum_H1_iso S₁ S₂ y) := by

  rw [mayerVietoris_connectedSum_H1_intersectionForm_compat]


  unfold orthogonalDirectSumForm mayerVietoris_connectedSum_H1_iso
  simp only [LinearMap.mk₂_apply, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply]

/-- Existential form of Proposition 30.8: there exists a linear isomorphism
`H¹(S₁ ♯ S₂; F₂) ≃ H¹(S₁; F₂) × H¹(S₂; F₂)` under which the intersection
form of `S₁ ♯ S₂` equals the orthogonal direct sum of those of `S₁`, `S₂`. -/
theorem cohomology_connectedSum_iso (S₁ S₂ : CompactSurface) :
    ∃ (φ : CohomZMod2 (S₁ ♯ S₂).toTopCat 1 ≃ₗ[ZMod 2]
        CohomZMod2 S₁.toTopCat 1 × CohomZMod2 S₂.toTopCat 1),
      ∀ (x y : CohomZMod2 (S₁ ♯ S₂).toTopCat 1),
        intersectionForm (S₁ ♯ S₂) x y =
          orthogonalDirectSumForm (intersectionForm S₁) (intersectionForm S₂) (φ x) (φ y) :=
  ⟨mayerVietoris_connectedSum_H1_iso S₁ S₂, mayerVietoris_connectedSum_H1_orthogonal S₁ S₂⟩

/-- Two compact surfaces are *homeomorphic* if there exists a homeomorphism
between their underlying topological spaces. -/
def CompactSurface.Homeomorphic (S₁ S₂ : CompactSurface) : Prop :=
  Nonempty (S₁.toTopCat ≃ₜ S₂.toTopCat)

/-- The set of *homeomorphism classes* of compact surfaces, as a quotient
of `CompactSurface` by the homeomorphism relation. -/
def SurfaceClass : Type 1 := Quot CompactSurface.Homeomorphic

/-- The canonical map sending a compact surface to its homeomorphism class. -/
def SurfaceClass.mk : CompactSurface → SurfaceClass := Quot.mk _

/-- The connected sum endows the set of homeomorphism classes of compact
surfaces with the structure of a commutative monoid. -/
noncomputable instance SurfaceClass.instAddCommMonoid : AddCommMonoid SurfaceClass := by sorry

attribute [instance] SurfaceClass.instAddCommMonoid

/-- A *nondegenerate symmetric bilinear form over `F₂`* packaged with its
underlying finite-dimensional `F₂`-vector space. -/
structure NondegenSymmBilinFormF2 where
  V : Type
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module (ZMod 2) V]
  [instFiniteDimensional : FiniteDimensional (ZMod 2) V]
  form : @LinearMap.BilinForm (ZMod 2) _ V instAddCommGroup.toAddCommMonoid instModule
  isSymm : form.IsSymm
  isNondeg : form.Nondegenerate

attribute [instance] NondegenSymmBilinFormF2.instAddCommGroup
  NondegenSymmBilinFormF2.instModule NondegenSymmBilinFormF2.instFiniteDimensional

/-- Two nondegenerate symmetric bilinear forms over `F₂` are *isometric* if
there is a linear isomorphism of the underlying vector spaces that takes
one form to the other. -/
def NondegenSymmBilinFormF2.Isometric (B₁ B₂ : NondegenSymmBilinFormF2) : Prop :=
  ∃ (f : B₁.V ≃ₗ[ZMod 2] B₂.V),
    ∀ (x y : B₁.V), B₂.form (f x) (f y) = B₁.form x y

/-- The set of *isometry classes* of nondegenerate symmetric bilinear forms
over `F₂`. -/
def BilinFormClass : Type 1 := Quot NondegenSymmBilinFormF2.Isometric

/-- The orthogonal direct sum endows the set of isometry classes of
nondegenerate symmetric `F₂`-bilinear forms with the structure of a
commutative monoid. -/
noncomputable instance BilinFormClass.instAddCommMonoid : AddCommMonoid BilinFormClass := by sorry

attribute [instance] BilinFormClass.instAddCommMonoid

/-- The canonical map sending a nondegenerate symmetric `F₂`-bilinear form
to its isometry class. -/
def BilinFormClass.mk : NondegenSymmBilinFormF2 → BilinFormClass := Quot.mk _


/-- The intersection form on `H¹(S; F₂)` of a compact surface is symmetric
(over characteristic 2 the cup product is graded-commutative without sign). -/
theorem intersectionForm_isSymm (S : CompactSurface) :
    (intersectionForm S).IsSymm := by sorry


/-- The intersection form on `H¹(S; F₂)` of a compact surface is
nondegenerate, as a consequence of Poincaré duality. -/
theorem intersectionForm_nondegenerate (S : CompactSurface) :
    (intersectionForm S).Nondegenerate := by sorry


/-- The first `F₂`-cohomology of a compact surface is finite-dimensional. -/
theorem cohomH1_finiteDimensional (S : CompactSurface) :
    FiniteDimensional (ZMod 2) (CohomZMod2 S.toTopCat 1) := by sorry

/-- Package the intersection form of a compact surface as a nondegenerate
symmetric `F₂`-bilinear form (on the finite-dimensional space
`H¹(S; F₂)`). -/
def CompactSurface.intersectionFormF2 (S : CompactSurface) : NondegenSymmBilinFormF2 where
  V := CohomZMod2 S.toTopCat 1
  form := intersectionForm S
  isSymm := intersectionForm_isSymm S
  isNondeg := intersectionForm_nondegenerate S
  instFiniteDimensional := cohomH1_finiteDimensional S

/-- The map sending a compact surface to the isometry class of its
intersection form. -/
def intersectionFormMap_surface : CompactSurface → BilinFormClass :=
  fun S => BilinFormClass.mk S.intersectionFormF2


/-- Homeomorphic compact surfaces have isometric intersection forms,
so the map descends to a function on surface classes. -/
theorem intersectionFormMap_respects_homeomorphism (S₁ S₂ : CompactSurface)
    (h : CompactSurface.Homeomorphic S₁ S₂) :
    intersectionFormMap_surface S₁ = intersectionFormMap_surface S₂ := by sorry

/-- The induced map on homeomorphism classes of surfaces: send a class
`[S]` to the isometry class of its intersection form on `H¹(S; F₂)`. -/
def intersectionFormClassMap : SurfaceClass → BilinFormClass :=
  Quot.lift intersectionFormMap_surface intersectionFormMap_respects_homeomorphism


/-- Theorem 30.9: the intersection form yields a monoid isomorphism between
the monoid of homeomorphism classes of compact surfaces (under connected
sum) and the monoid of isometry classes of nondegenerate symmetric
`F₂`-bilinear forms (under orthogonal direct sum). -/
noncomputable def intersectionForm_isomorphism : SurfaceClass ≃+ BilinFormClass := by sorry


end SurfacesAndBilinearForms

section

open LinearMap.BilinForm

namespace BilinearForm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- For a reflexive bilinear form `B`, the restriction `B|_W` is
nondegenerate iff `W` and its orthogonal complement intersect only at zero. -/
theorem restrict_nondegenerate_iff_disjoint_orthogonal
    (B : LinearMap.BilinForm K V) (hB_refl : B.IsRefl)
    (W : Submodule K V) :
    (B.restrict W).Nondegenerate ↔ Disjoint W (B.orthogonal W) := by
  rw [restrict_nondegenerate_iff_isCompl_orthogonal hB_refl,
      isCompl_orthogonal_iff_disjoint hB_refl]

/-- If `B` is nondegenerate and reflexive and `B|_W` is nondegenerate, then
the restriction of `B` to the orthogonal complement `W^⊥` is also
nondegenerate. -/
theorem restrict_orthogonal_nondegenerate
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (hB_refl : B.IsRefl)
    {W : Submodule K V} (hW : (B.restrict W).Nondegenerate) :
    (B.restrict (B.orthogonal W)).Nondegenerate := by
  rw [restrict_nondegenerate_iff_isCompl_orthogonal hB_refl,
      orthogonal_orthogonal hB hB_refl W]
  exact (isCompl_orthogonal_of_restrict_nondegenerate hB_refl hW).symm

/-- When `B|_W` is nondegenerate, `V` decomposes as the internal direct
sum `W ⊕ W^⊥`, giving a linear equivalence `W × W^⊥ ≃ₗ V`. -/
noncomputable def orthogonalProdEquiv
    (B : LinearMap.BilinForm K V) (hB_refl : B.IsRefl)
    {W : Submodule K V} (hW : (B.restrict W).Nondegenerate) :
    (↥W × ↥(B.orthogonal W)) ≃ₗ[K] V :=
  Submodule.prodEquivOfIsCompl W (B.orthogonal W)
    (isCompl_orthogonal_of_restrict_nondegenerate hB_refl hW)

/-- Under the direct-sum decomposition `V ≃ W × W^⊥`, the form `B` becomes
the orthogonal direct sum of `B|_W` and `B|_{W^⊥}`; the cross terms vanish
because they lie in the orthogonal complement. -/
theorem orthogonalProdEquiv_respects_form
    (B : LinearMap.BilinForm K V) (hB_refl : B.IsRefl)
    {W : Submodule K V} (hW : (B.restrict W).Nondegenerate)
    (x y : ↥W × ↥(B.orthogonal W)) :
    B (orthogonalProdEquiv B hB_refl hW x)
      (orthogonalProdEquiv B hB_refl hW y) =
    B (↑x.1) (↑y.1) + B (↑x.2) (↑y.2) := by
  simp only [orthogonalProdEquiv, Submodule.coe_prodEquivOfIsCompl',
    map_add, LinearMap.add_apply]
  have h1 : B (↑x.1) (↑y.2) = 0 := (y.2).2 x.1 (x.1).2
  have h2 : B (↑x.2) (↑y.1) = 0 := hB_refl _ _ ((x.2).2 y.1 (y.1).2)
  simp [h1, h2]

/-- Lemma 30.5 (packaged form): a triple characterisation of nondegeneracy
of the restriction `B|_W` of a nondegenerate reflexive bilinear form,
combining the disjointness criterion, the nondegeneracy of the restriction
to the orthogonal complement, and the orthogonal-direct-sum decomposition
of `V` together with the corresponding factorisation of `B`. -/
theorem restrict_nondegenerate_characterization
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (hB_refl : B.IsRefl)
    (W : Submodule K V) :
    ((B.restrict W).Nondegenerate ↔ Disjoint W (B.orthogonal W)) ∧
    ((B.restrict W).Nondegenerate →
      (B.restrict (B.orthogonal W)).Nondegenerate) ∧
    ((B.restrict W).Nondegenerate →
      ∃ (e : (↥W × ↥(B.orthogonal W)) ≃ₗ[K] V),
        ∀ (x y : ↥W × ↥(B.orthogonal W)),
          B (e x) (e y) = B (↑x.1) (↑y.1) + B (↑x.2) (↑y.2)) :=
  ⟨restrict_nondegenerate_iff_disjoint_orthogonal B hB_refl W,
   fun hW => restrict_orthogonal_nondegenerate B hB hB_refl hW,
   fun hW => ⟨orthogonalProdEquiv B hB_refl hW,
              orthogonalProdEquiv_respects_form B hB_refl hW⟩⟩

end BilinearForm

end
