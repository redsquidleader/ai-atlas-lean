/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ModuleFunctor
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.Logic.UnivLE

set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category MonoidalCategory ModFun

/-- Underlying type of objects of the dual category `C*_M`: module endofunctors of `M`. -/
def DualCatObj'
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory' C M] :=
  ModuleFunctor' C M M

/-- The property that the module category `M` over `C` is exact: tensoring any object of
`M` with a projective object of `C` yields a projective object. -/
def IsExactModuleCategory'
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory' C M] : Prop :=
  ∀ (P : C) (N : M), Projective P → Projective (P ⊗ᵐ N)

/-- Hom-sets of module endofunctors of `M` are essentially `v₂`-small whenever `M` is
essentially `v₂`-small, giving a `Small` instance suitable for shrinking morphisms. -/
noncomputable instance DualCatObj'.natTransSmall
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory' C M]
    [UnivLE.{u₂, v₂}]
    (F G : DualCatObj' C M) : Small.{v₂} (F.toFunctor ⟶ G.toFunctor) :=
  small_of_injective (f := fun η => η.app) (fun _ _ h => NatTrans.ext h)

/-- Category structure on `DualCatObj' C M` whose morphisms are obtained by shrinking
the natural transformations between the underlying module functors. -/
@[reducible]
noncomputable def DualCatObj'.categoryInstance
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory' C M]
    [UnivLE.{u₂, v₂}] :
    Category.{v₂} (DualCatObj' C M) where
  Hom := fun F G => Shrink.{v₂} (F.toFunctor ⟶ G.toFunctor)
  id := fun F => (equivShrink _) (𝟙 F.toFunctor)
  comp := fun {X Y Z} f g =>
    (equivShrink _) ((equivShrink _).symm f ≫ (equivShrink _).symm g)
  id_comp := by
    intro F G f
    show (equivShrink _) ((equivShrink _).symm ((equivShrink _) (𝟙 F.toFunctor)) ≫
      (equivShrink _).symm f) = f
    simp only [Equiv.symm_apply_apply, Category.id_comp, Equiv.apply_symm_apply]
  comp_id := by
    intro F G f
    show (equivShrink _) ((equivShrink _).symm f ≫
      (equivShrink _).symm ((equivShrink _) (𝟙 G.toFunctor))) = f
    simp only [Equiv.symm_apply_apply, Category.comp_id, Equiv.apply_symm_apply]
  assoc := by
    intro W X Y Z f g h
    show (equivShrink _) ((equivShrink _).symm
      ((equivShrink _) ((equivShrink _).symm f ≫ (equivShrink _).symm g)) ≫
      (equivShrink _).symm h) =
      (equivShrink _) ((equivShrink _).symm f ≫ (equivShrink _).symm
      ((equivShrink _) ((equivShrink _).symm g ≫ (equivShrink _).symm h)))
    simp only [Equiv.symm_apply_apply, Category.assoc]

/-- Monoidal category structure on `DualCatObj' C M` obtained from composition of module
endofunctors of `M`. -/
@[reducible]
noncomputable def DualCatObj'.monoidalCategoryInstance
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory' C M]
    [UnivLE.{u₂, v₂}] :
    @MonoidalCategory (DualCatObj' C M) (DualCatObj'.categoryInstance C M) := by


  sorry

/-- Category structure on the type `ModuleFunctor' C M₁ M` of module functors from `M₁`
to `M`. -/
@[reducible]
noncomputable def ModuleFunctor'.categoryInstance
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M₁ : Type u₂) [Category.{v₂} M₁] [LeftModuleCategory' C M₁]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory' C M] :
    Category.{v₂} (ModuleFunctor' C M₁ M) := by


  sorry

/-- Left action of the dual category `DualCatObj' C M` on the category of module
functors `ModuleFunctor' C M₁ M`, given by post-composition. -/
@[reducible]
noncomputable def ModuleFunctor'.leftModuleInstance
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M₁ : Type u₂) [Category.{v₂} M₁] [LeftModuleCategory' C M₁]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory' C M]
    [UnivLE.{u₂, v₂}] :
    @LeftModuleCategory' (DualCatObj' C M)
      (DualCatObj'.categoryInstance C M)
      (DualCatObj'.monoidalCategoryInstance C M)
      (ModuleFunctor' C M₁ M)
      (ModuleFunctor'.categoryInstance C M₁ M) := by


  sorry

/-- If `M` is an exact module category over a rigid tensor category `C` with enough
projectives, then the category of module functors `M₁ → M` is an exact module category
over the dual category `C*_M`. -/
theorem funC_exact_over_dualCat
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [RigidCategory C] [EnoughProjectives C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory' C M]
    [UnivLE.{u₂, v₂}]
    (hM : IsExactModuleCategory' C M)
    (M₁ : Type u₂) [Category.{v₂} M₁] [LeftModuleCategory' C M₁] :
    letI catD := DualCatObj'.categoryInstance C M
    letI _monD := DualCatObj'.monoidalCategoryInstance C M
    letI catF := ModuleFunctor'.categoryInstance C M₁ M
    letI modF := ModuleFunctor'.leftModuleInstance C M₁ M
    ∀ (P : DualCatObj' C M) (F : ModuleFunctor' C M₁ M),
      @Projective (DualCatObj' C M) catD P →
        @Projective (ModuleFunctor' C M₁ M) catF (modF.actObj P F) := by


  sorry

/-- Lemma 2.14.10: tensoring with a projective object of the dual category preserves
projectivity of module functors, packaged from `funC_exact_over_dualCat`. -/
theorem lem_2_14_10
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [RigidCategory C] [EnoughProjectives C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory' C M]
    [UnivLE.{u₂, v₂}]
    (hM : IsExactModuleCategory' C M)
    (M₁ : Type u₂) [Category.{v₂} M₁] [LeftModuleCategory' C M₁] :
    letI catD := DualCatObj'.categoryInstance C M
    letI _monD := DualCatObj'.monoidalCategoryInstance C M
    letI catF := ModuleFunctor'.categoryInstance C M₁ M
    letI modF := ModuleFunctor'.leftModuleInstance C M₁ M
    ∀ (P : DualCatObj' C M) (F : ModuleFunctor' C M₁ M),
      @Projective (DualCatObj' C M) catD P →
        @Projective (ModuleFunctor' C M₁ M) catF (modF.actObj P F) :=
  funC_exact_over_dualCat hM M₁

/-- Canonical evaluation action of the dual category `C*_M` on `M`: a module endofunctor
`F : M → M` acts on `m ∈ M` by `F.obj m`. -/
@[reducible]
noncomputable def DualCatObj'.evalModuleInstance
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory' C M]
    [UnivLE.{u₂, v₂}] :
    @LeftModuleCategory' (DualCatObj' C M)
      (DualCatObj'.categoryInstance C M)
      (DualCatObj'.monoidalCategoryInstance C M)
      M _ := by


  sorry

/-- Existence of an internal `Hom` for a module category `M` over `C`: a right adjoint
`Hom(m, n) ∈ C` to the action `X ⊗ᵐ m`, natural in `X`. -/
class HasModuleInternalHom'
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory' C M] where
  moduleIHom' : M → M → C
  moduleIHomEquiv' : ∀ (X : C) (m n : M),
    (X ⊗ᵐ m ⟶ n) ≃ (X ⟶ moduleIHom' m n)
  moduleIHomEquiv'_natural : ∀ {X Y : C} (f : X ⟶ Y) (m n : M) (g : Y ⊗ᵐ m ⟶ n),
    moduleIHomEquiv' X m n (f ▷ᵐ m ≫ g) = f ≫ moduleIHomEquiv' Y m n g

export HasModuleInternalHom' (moduleIHom' moduleIHomEquiv' moduleIHomEquiv'_natural)

/-- An exact module category over a rigid tensor category with enough projectives admits
internal `Hom` objects valued in `C`. -/
noncomputable def HasModuleInternalHom'.ofExact
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    [RigidCategory C] [EnoughProjectives C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory' C M]
    [UnivLE.{u₂, v₂}]
    (_ : IsExactModuleCategory' C M) : HasModuleInternalHom' C M := by


  sorry

/-- Existence of an internal `Hom` for a module category `M` valued in the dual category
`C*_M`: a right adjoint to the evaluation action of `C*_M` on `M`. -/
class HasDualModuleInternalHom'
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory' C M]
    [UnivLE.{u₂, v₂}] where
  moduleIHomDual' : M → M → DualCatObj' C M
  moduleIHomDualEquiv' :
    letI catD := DualCatObj'.categoryInstance C M
    letI monD := DualCatObj'.monoidalCategoryInstance C M
    letI modD := DualCatObj'.evalModuleInstance C M
    ∀ (F : DualCatObj' C M) (m n : M),
      (@LeftModuleCategoryStruct'.actObj (DualCatObj' C M) catD monD M _
        modD.toLeftModuleCategoryStruct' F m ⟶ n) ≃
      (@Quiver.Hom (DualCatObj' C M) catD.toCategoryStruct.toQuiver F (moduleIHomDual' m n))

export HasDualModuleInternalHom' (moduleIHomDual' moduleIHomDualEquiv')

/-- An exact module category over a rigid tensor category with enough projectives admits
internal `Hom` objects valued in the dual category `C*_M`. -/
noncomputable def HasDualModuleInternalHom'.ofExact
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    [RigidCategory C] [EnoughProjectives C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory' C M]
    [UnivLE.{u₂, v₂}]
    (_ : IsExactModuleCategory' C M) : HasDualModuleInternalHom' C M := by


  sorry

/-- Existence of left duals in the dual category `C*_M`, given by the evaluation and
coevaluation morphisms `ᵛF ⊗ F ⟶ 𝟙` and `𝟙 ⟶ F ⊗ ᵛF`. -/
class HasDualCatLeftDual'
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory' C M]
    [UnivLE.{u₂, v₂}] where
  leftDualD : DualCatObj' C M → DualCatObj' C M
  evalD :
    letI catD := DualCatObj'.categoryInstance C M
    letI monD := DualCatObj'.monoidalCategoryInstance C M
    ∀ (F : DualCatObj' C M),
      @Quiver.Hom (DualCatObj' C M) catD.toCategoryStruct.toQuiver
        (@MonoidalCategoryStruct.tensorObj (DualCatObj' C M) catD
          monD.toMonoidalCategoryStruct (leftDualD F) F)
        (@MonoidalCategoryStruct.tensorUnit (DualCatObj' C M) catD
          monD.toMonoidalCategoryStruct)
  coevalD :
    letI catD := DualCatObj'.categoryInstance C M
    letI monD := DualCatObj'.monoidalCategoryInstance C M
    ∀ (F : DualCatObj' C M),
      @Quiver.Hom (DualCatObj' C M) catD.toCategoryStruct.toQuiver
        (@MonoidalCategoryStruct.tensorUnit (DualCatObj' C M) catD
          monD.toMonoidalCategoryStruct)
        (@MonoidalCategoryStruct.tensorObj (DualCatObj' C M) catD
          monD.toMonoidalCategoryStruct F (leftDualD F))

export HasDualCatLeftDual' (leftDualD evalD coevalD)

/-- An exact module category over a rigid tensor category with enough projectives gives
rise to left duals in the dual category `C*_M`. -/
noncomputable def HasDualCatLeftDual'.ofExact
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    [RigidCategory C] [EnoughProjectives C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory' C M]
    [UnivLE.{u₂, v₂}]
    (_ : IsExactModuleCategory' C M) : HasDualCatLeftDual' C M := by


  sorry

/-- Reduction step in the proof of Theorem 2.14.6: from a duality-style isomorphism of
module actions involving the dual internal `Hom`, deduce the dual-category version that
identifies tensoring with the left dual of `Hom_*` to tensoring with `Hom_C`. -/
theorem thm_2_14_6_reduction
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [RigidCategory C] [EnoughProjectives C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory' C M]
    [UnivLE.{u₂, v₂}]
    (hM : IsExactModuleCategory' C M) :
    letI catD := DualCatObj'.categoryInstance C M
    letI monD := DualCatObj'.monoidalCategoryInstance C M
    letI modD := DualCatObj'.evalModuleInstance C M
    letI ihomC := HasModuleInternalHom'.ofExact C M hM
    letI ihomD := HasDualModuleInternalHom'.ofExact C M hM
    letI dualD := HasDualCatLeftDual'.ofExact C M hM
    ∀ (X Y Z : M),

      Nonempty (
        @LeftModuleCategoryStruct'.actObj C _ _ M _ _ (ᘁ(moduleIHom' (C := C) Z X)) Y ≅
        @LeftModuleCategoryStruct'.actObj (DualCatObj' C M) catD monD M _
          modD.toLeftModuleCategoryStruct' (moduleIHomDual' X Y) Z) →

      Nonempty (
        @LeftModuleCategoryStruct'.actObj (DualCatObj' C M) catD monD M _
          modD.toLeftModuleCategoryStruct' (leftDualD (moduleIHomDual' Z X)) Y ≅
        @LeftModuleCategoryStruct'.actObj C _ _ M _ _ (moduleIHom' (C := C) X Y) Z) := by
  sorry

/-- Associativity of the internal `Hom` (Examples 2.10.8 / 2.14.5): there is a natural
isomorphism between the action of `ᘁ(Hom_C(Z, X))` on `Y` and the dual-category action of
`Hom_*(X, Y)` on `Z`. -/
theorem examples_2_10_8_2_14_5_associativity
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [RigidCategory C] [EnoughProjectives C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory' C M]
    [UnivLE.{u₂, v₂}]
    (hM : IsExactModuleCategory' C M) :
    letI catD := DualCatObj'.categoryInstance C M
    letI monD := DualCatObj'.monoidalCategoryInstance C M
    letI modD := DualCatObj'.evalModuleInstance C M
    letI ihomC := HasModuleInternalHom'.ofExact C M hM
    letI ihomD := HasDualModuleInternalHom'.ofExact C M hM
    ∀ (X Y Z : M),
      Nonempty (
        @LeftModuleCategoryStruct'.actObj C _ _ M _ _ (ᘁ(moduleIHom' (C := C) Z X)) Y ≅
        @LeftModuleCategoryStruct'.actObj (DualCatObj' C M) catD monD M _
          modD.toLeftModuleCategoryStruct' (moduleIHomDual' X Y) Z) := by
  sorry

/-- Proposition 2.14.14 (basic identity for module categories): there is a natural
isomorphism between the dual-category action of `ᵛ(Hom_*(Z, X))` on `Y` and the action of
`Hom_C(X, Y)` on `Z`. -/
theorem Proposition_2_14_14
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [RigidCategory C] [EnoughProjectives C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory' C M]
    [UnivLE.{u₂, v₂}]
    (hM : IsExactModuleCategory' C M) :
    letI catD := DualCatObj'.categoryInstance C M
    letI monD := DualCatObj'.monoidalCategoryInstance C M
    letI modD := DualCatObj'.evalModuleInstance C M
    letI ihomC := HasModuleInternalHom'.ofExact C M hM
    letI ihomD := HasDualModuleInternalHom'.ofExact C M hM
    letI dualD := HasDualCatLeftDual'.ofExact C M hM
    ∀ (X Y Z : M),
      Nonempty (
        @LeftModuleCategoryStruct'.actObj (DualCatObj' C M) catD monD M _
          modD.toLeftModuleCategoryStruct' (leftDualD (moduleIHomDual' Z X)) Y ≅
        @LeftModuleCategoryStruct'.actObj C _ _ M _ _ (moduleIHom' (C := C) X Y) Z) := by
  intro X Y Z
  exact thm_2_14_6_reduction hM X Y Z (examples_2_10_8_2_14_5_associativity hM X Y Z)

/-- Alias of `Proposition_2_14_14`: the basic identity relating internal `Hom`s in `C`
and in the dual category `C*_M`. -/
theorem basic_identity_hom
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [RigidCategory C] [EnoughProjectives C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory' C M]
    [UnivLE.{u₂, v₂}]
    (hM : IsExactModuleCategory' C M) :
    letI catD := DualCatObj'.categoryInstance C M
    letI monD := DualCatObj'.monoidalCategoryInstance C M
    letI modD := DualCatObj'.evalModuleInstance C M
    letI ihomC := HasModuleInternalHom'.ofExact C M hM
    letI ihomD := HasDualModuleInternalHom'.ofExact C M hM
    letI dualD := HasDualCatLeftDual'.ofExact C M hM
    ∀ (X Y Z : M),
      Nonempty (
        @LeftModuleCategoryStruct'.actObj (DualCatObj' C M) catD monD M _
          modD.toLeftModuleCategoryStruct' (leftDualD (moduleIHomDual' Z X)) Y ≅
        @LeftModuleCategoryStruct'.actObj C _ _ M _ _ (moduleIHom' (C := C) X Y) Z) :=
  Proposition_2_14_14 hM

end CategoryTheory
