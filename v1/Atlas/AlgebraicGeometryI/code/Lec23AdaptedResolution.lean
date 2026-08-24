/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.Lec23DerivedFunctors

open CategoryTheory Category Limits

noncomputable section

universe v u

namespace Lec23AdaptedResolution

/-- Proposition 43 (canonical comparison map): For any resolution `K` of `M`, there is a
canonical map from `Hⁿ(F(K))` to the right derived functor `(RⁿF)(M)`. -/
theorem prop43_canonical_map
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (n : ℕ) {M : C} (K : Lec23.Resolution M) :
    Nonempty (
      (HomologicalComplex.homologyFunctor D _ n).obj
        ((F.mapHomologicalComplex _).obj K.cocomplex) ⟶
      (F.rightDerived n).obj M) :=
  Lec23.prop43_canonical_map_exists F n K

/-- Proposition 43 (adapted resolution computes derived functor): When every term of a
resolution `K` of `M` is adjusted to `F`, the comparison map is an isomorphism, so `RⁿF(M)`
can be computed from `Hⁿ(F(K))`. -/
theorem prop43_adapted_resolution_computes_derived
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (n : ℕ) {M : C} (K : Lec23.Resolution M)
    (hadj : ∀ i, Lec23.IsAdjustedToFunctor F (K.cocomplex.X i)) :
    Nonempty (
      (HomologicalComplex.homologyFunctor D _ n).obj
        ((F.mapHomologicalComplex _).obj K.cocomplex) ≅
      (F.rightDerived n).obj M) :=
  Lec23.prop43_iso_when_adjusted F n K hadj

/-- Every injective object is adjusted to any additive functor: `RⁿF` vanishes on
injectives for `n > 0`. -/
theorem injective_is_adjusted
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (M : C) [Injective M] :
    Lec23.IsAdjustedToFunctor F M :=
  Lec23.injective_isAdjustedToFunctor F M

/-- The standard identification of the right derived functor as the cohomology of `F`
applied to an injective resolution. -/
noncomputable def prop43_injective_resolution_iso
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (n : ℕ) {X : C} (I : InjectiveResolution X) :
    (F.rightDerived n).obj X ≅
      (HomologicalComplex.homologyFunctor D _ n).obj
        ((F.mapHomologicalComplex _).obj I.cocomplex) :=
  I.isoRightDerivedObj F n

/-- Independence of injective resolution: the cohomology of `F` applied to two different
injective resolutions of `X` is canonically isomorphic. -/
noncomputable def prop43_resolution_uniqueness
    {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type*} [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] (n : ℕ)
    {X : C} (I J : InjectiveResolution X) :
    (HomologicalComplex.homologyFunctor D _ n).obj
        ((F.mapHomologicalComplex _).obj I.cocomplex) ≅
      (HomologicalComplex.homologyFunctor D _ n).obj
        ((F.mapHomologicalComplex _).obj J.cocomplex) :=
  (I.isoRightDerivedObj F n).symm ≪≫ J.isoRightDerivedObj F n

end Lec23AdaptedResolution
