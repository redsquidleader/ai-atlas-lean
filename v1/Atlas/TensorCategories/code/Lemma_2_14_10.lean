/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.DualCatDefs

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category MonoidalCategory ModFun

/-- Lemma 2.14.10 (EGNO). For a rigid monoidal category `C` with enough projectives acting
exactly on `M`, the category of module functors `Fun_C(M₁, M)` is an exact module category
over the dual `C_M^*`: the action of a projective object on any module functor produces a
projective module functor. -/
theorem Lemma_2_14_10
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

/-- Lowercase-named alias of `Lemma_2_14_10`: the dual category's projectives act on module
functors to produce projective module functors. -/
theorem lemma_2_14_10
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

end CategoryTheory
