/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.ClassGroup
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

set_option maxHeartbeats 800000

noncomputable section

namespace Lec17AbelJacobi

open AlgebraicGeometry CategoryTheory

/-- The scheme `Spec ℂ`, used as the base in the smooth-complex-curve setup of Lec 17. -/
def SpecC : Scheme := Scheme.Spec.obj (Opposite.op (CommRingCat.of ℂ))

/-- A smooth compact complex curve: an integral scheme over `Spec ℂ` that is proper
and smooth of relative dimension `1`. -/
structure SmoothCompactComplexCurve where
  toScheme : Scheme
  structureMorphism : toScheme ⟶ SpecC
  isIntegral : AlgebraicGeometry.IsIntegral toScheme
  isProper : IsProper structureMorphism
  isSmoothOfRelDim1 : SmoothOfRelativeDimension 1 structureMorphism

/-- Converts a complex period lattice into the Weierstrass cubic
`y² = 4x³ - g₂(L) x - g₃(L)`, with `aᵢ` coefficients adjusted to standard short form. -/
def periodPairToWeierstrassCurve (L : PeriodPair) : WeierstrassCurve ℂ where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -(L.g₂ / 4)
  a₆ := -(L.g₃ / 4)

/-- Two period pairs are homothetic if their lattices are scalar multiples of each
other by some nonzero complex `α`. -/
def LatticePairHomothetic (L₁ L₂ : PeriodPair) : Prop :=
  ∃ α : ℂ, α ≠ 0 ∧
    (∀ z : ℂ, z ∈ L₁.lattice ↔ ∃ w ∈ L₂.lattice, z = α * w)

/-- Period lattice data attached to a curve of genus `g`: a full-rank `ℤ`-submodule of
`ℂ^g`, representing the periods of holomorphic 1-forms. -/
structure PeriodLatticeData where
  genus : ℕ
  lattice : Submodule ℤ (Fin genus → ℂ)

/-- Two period lattice data are equivalent if there is a `ℂ`-linear isomorphism between
the ambient spaces carrying one lattice onto the other. -/
def PeriodLatticeData.Equivalent (D₁ D₂ : PeriodLatticeData) : Prop :=
  ∃ (φ : (Fin D₁.genus → ℂ) ≃ₗ[ℂ] (Fin D₂.genus → ℂ)),
    ∀ v : Fin D₁.genus → ℂ, v ∈ D₁.lattice ↔ φ v ∈ D₂.lattice

/-- Two smooth compact complex curves are isomorphic over `ℂ` if there is an
isomorphism of schemes compatible with their structure morphisms to `Spec ℂ`. -/
def SmoothCompactComplexCurve.IsIsomorphicOver (X₁ X₂ : SmoothCompactComplexCurve) : Prop :=
  ∃ (f : X₁.toScheme ⟶ X₂.toScheme), IsIso f ∧
    X₁.structureMorphism = f ≫ X₂.structureMorphism

/-- Assigns to a smooth compact complex curve its period lattice in `ℂ^{genus}`. -/
noncomputable def periodLatticeOf (X : SmoothCompactComplexCurve) : PeriodLatticeData := sorry

/-- Torelli's theorem: a smooth compact complex curve is determined up to isomorphism
by its period lattice. -/
theorem torelli_reconstruction
    (X₁ X₂ : SmoothCompactComplexCurve) :
    X₁.IsIsomorphicOver X₂ ↔
    PeriodLatticeData.Equivalent (periodLatticeOf X₁) (periodLatticeOf X₂) := by
  sorry

/-- A (proper smooth) abelian group scheme over `Spec ℂ`: a proper smooth scheme over
`ℂ` with a chosen identity section. -/
structure AbelianGroupScheme where
  toScheme : Scheme
  structureMorphism : toScheme ⟶ SpecC
  isProper : IsProper structureMorphism
  isSmooth : Smooth structureMorphism
  identitySection : SpecC ⟶ toScheme
  identitySection_comp : identitySection ≫ structureMorphism = 𝟙 SpecC

/-- Proposition 26 (Lec 17): existence of the Jacobian variety and the Abel–Jacobi map
`X → Jac(X)` over `ℂ`, compatible with structure morphisms to `Spec ℂ`. -/
theorem jacobian_variety_prop26
    (X : SmoothCompactComplexCurve) :
    ∃ (JacX : AbelianGroupScheme) (AJmap : X.toScheme ⟶ JacX.toScheme),

      AJmap ≫ JacX.structureMorphism = X.structureMorphism := by sorry

/-- An irreducible complete curve over `k`: an integral Dedekind domain regarded as the
coordinate ring of a 1-dimensional smooth curve. -/
structure IrreducibleCompleteCurve (k : Type*) [Field k] : Type 1 where
  coordinateRing : Type
  [instCommRing : CommRing coordinateRing]
  [instIsDomain : IsDomain coordinateRing]
  [instIsDedekind : IsDedekindDomain coordinateRing]

attribute [instance] IrreducibleCompleteCurve.instCommRing
  IrreducibleCompleteCurve.instIsDomain IrreducibleCompleteCurve.instIsDedekind

/-- A morphism `X → Y` of irreducible complete curves, contravariantly described by a
ring homomorphism on coordinate rings `Y.coordinateRing → X.coordinateRing`. -/
structure CurveMorphism {k : Type*} [Field k]
    (X Y : IrreducibleCompleteCurve k) : Type where
  ringHom : Y.coordinateRing →+* X.coordinateRing

/-- Composition of curve morphisms, defined contravariantly via composition of the
underlying ring maps. -/
def CurveMorphism.comp {k : Type*} [Field k]
    {X Y Z : IrreducibleCompleteCurve k}
    (g : CurveMorphism Y Z) (f : CurveMorphism X Y) :
    CurveMorphism X Z where
  ringHom := f.ringHom.comp g.ringHom

/-- A curve morphism is constant iff the underlying ring map is not injective (i.e.
collapses some function on the target curve). -/
def CurveMorphism.IsConstant {k : Type*} [Field k]
    {X Y : IrreducibleCompleteCurve k} (f : CurveMorphism X Y) : Prop :=
  ¬ Function.Injective f.ringHom

/-- A curve morphism is finite iff `X.coordinateRing` is module-finite over
`Y.coordinateRing` via `f.ringHom`. -/
def CurveMorphism.IsFinite {k : Type*} [Field k]
    {X Y : IrreducibleCompleteCurve k} (f : CurveMorphism X Y) : Prop :=
  letI : Algebra Y.coordinateRing X.coordinateRing := f.ringHom.toAlgebra
  Module.Finite Y.coordinateRing X.coordinateRing

/-- A curve morphism is an isomorphism iff its underlying ring map is bijective. -/
def CurveMorphism.IsIsomorphism {k : Type*} [Field k]
    {X Y : IrreducibleCompleteCurve k} (f : CurveMorphism X Y) : Prop :=
  Function.Bijective f.ringHom

/-- A curve morphism is birational iff its ring map is injective and every element of
`X.coordinateRing` is a fraction of elements pulled back from `Y.coordinateRing`. -/
def CurveMorphism.IsBirational {k : Type*} [Field k]
    {X Y : IrreducibleCompleteCurve k} (f : CurveMorphism X Y) : Prop :=
  Function.Injective f.ringHom ∧
  ∀ a : X.coordinateRing, ∃ (b : Y.coordinateRing) (s : Y.coordinateRing),
    s ≠ 0 ∧ f.ringHom s * a = f.ringHom b

/-- A curve is normal iff its coordinate ring is integrally closed in its field of
fractions. -/
def IrreducibleCompleteCurve.IsNormal {k : Type*} [Field k]
    (X : IrreducibleCompleteCurve k) : Prop :=
  IsIntegrallyClosed X.coordinateRing

/-- The Picard group `Pic⁰(X)` of a curve, modeled as the ideal class group of its
Dedekind coordinate ring. -/
def IrreducibleCompleteCurve.Pic0Group {k : Type*} [Field k]
    (X : IrreducibleCompleteCurve k) : Type :=
  ClassGroup X.coordinateRing

/-- `Pic⁰(X)` inherits a commutative group structure from the class group. -/
instance instCommGroupPic0Group {k : Type*} [Field k]
    (X : IrreducibleCompleteCurve k) : CommGroup X.Pic0Group := by
  unfold IrreducibleCompleteCurve.Pic0Group; infer_instance

/-- Normalization factorization: any non-constant morphism `f : X → Y` factors as a
birational map `X → NorY` followed by a finite normalization `NorY → Y`, with both `X`
and `NorY` normal. -/
theorem normalization_factorization {k : Type*} [Field k]
    {X Y : IrreducibleCompleteCurve k}
    (f : CurveMorphism X Y) (hf : ¬ f.IsConstant) :
    ∃ (NorY : IrreducibleCompleteCurve k)
      (g : CurveMorphism X NorY) (normMap : CurveMorphism NorY Y),
      g.IsBirational ∧ X.IsNormal ∧ NorY.IsNormal ∧ normMap.IsFinite ∧
      f = normMap.comp g := by
  sorry

/-- A birational morphism into a normal curve is automatically an isomorphism
(Zariski's main theorem for smooth complete curves). -/
theorem birational_to_normal_is_iso {k : Type*} [Field k]
    {X Y : IrreducibleCompleteCurve k}
    (f : CurveMorphism X Y) (hf : f.IsBirational) (hY : Y.IsNormal) :
    f.IsIsomorphism := by
  sorry

/-- Composition of an isomorphism `g : X → Y` and a finite map `h : Y → Z` is again
finite. -/
theorem finite_comp_of_iso_finite {k : Type*} [Field k]
    {X Y Z : IrreducibleCompleteCurve k}
    (g : CurveMorphism X Y) (h : CurveMorphism Y Z)
    (hg : g.IsIsomorphism) (hh : h.IsFinite) :
    (h.comp g).IsFinite := by
  sorry

/-- Abel–Jacobi surjectivity for an elliptic Weierstrass curve: the map from
affine points to the class group of the coordinate ring is surjective. -/
theorem toClass_surjective
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] :
    Function.Surjective
      (WeierstrassCurve.Affine.Point.toClass :
        W.Point → Additive (ClassGroup W.CoordinateRing)) := by sorry

/-- Corollary 21 (Lec 17): for an elliptic curve `W`, the Abel–Jacobi map
`W.Point → Pic⁰(W)` is a bijection (in fact a group isomorphism). -/
theorem genus_one_isomorphic_to_pic0
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] :
    Function.Bijective
      (WeierstrassCurve.Affine.Point.toClass :
        W.Point → Additive (ClassGroup W.CoordinateRing)) := by
  constructor
  ·
    exact WeierstrassCurve.Affine.Point.toClass_injective
  ·
    exact toClass_surjective W

/-- The affine points of an elliptic Weierstrass curve form an abelian group. -/
instance elliptic_curve_addCommGroup
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] :
    AddCommGroup W.Point :=
  inferInstance

/-- Normalization is finite (Lec 17): for `B` a finite-type `k`-domain with fraction
field `K` and `L/K` a finite extension, the integral closure of `B` in `L` is module-
finite over `B`. -/
theorem normalization_is_finite_lec17
    (k : Type*) [Field k]
    (B : Type*) [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    (K : Type*) [Field K] [Algebra B K] [IsFractionRing B K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra B L] [IsScalarTower B K L] :
    Module.Finite B (integralClosure B L) := by
  sorry

/-- Existence of the normalization with all relevant properties (Lec 17): the integral
closure of `B` in `L` is `B`-module finite, of finite type over `k`, integrally closed,
and the structure map `B → integralClosure B L` is injective. -/
theorem normalization_existence
    (k : Type*) [Field k]
    (B : Type*) [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    (K : Type*) [Field K] [Algebra B K] [IsFractionRing B K]
    [Algebra k K] [IsScalarTower k B K]
    (L : Type*) [Field L] [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [Algebra k L] [IsScalarTower k B L]
    [FiniteDimensional K L] :

    Module.Finite B (integralClosure B L) ∧

    Algebra.FiniteType k (integralClosure B L) ∧

    IsIntegrallyClosed (integralClosure B L) ∧

    Function.Injective (algebraMap B (integralClosure B L)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    exact normalization_is_finite_lec17 k B K L
  ·
    haveI : Module.Finite B (integralClosure B L) :=
      normalization_is_finite_lec17 k B K L
    exact Algebra.FiniteType.trans (‹Algebra.FiniteType k B›)
      (Module.Finite.finiteType (integralClosure B L))
  ·
    exact integralClosure.isIntegrallyClosedOfFiniteExtension K
  ·
    haveI : IsScalarTower B (integralClosure B L) L :=
      IsScalarTower.subalgebra' B L L (integralClosure B L)
    exact algebraMap_injective_of_field_isFractionRing B (↥(integralClosure B L)) K L

end Lec17AbelJacobi
