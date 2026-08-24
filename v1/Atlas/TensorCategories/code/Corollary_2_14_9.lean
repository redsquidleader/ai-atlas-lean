/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.DualCatDefs
import Atlas.TensorCategories.code.IndecomposableModuleCat
import Mathlib.CategoryTheory.Simple

set_option maxHeartbeats 400000

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category MonoidalCategory ModFun Limits

/-- A left module category `M` over a monoidal category `C` is indecomposable if it is
nonzero and does not decompose as a product of two nonzero module categories. -/
class IsIndecomposableModuleCategory'
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory' C M] : Prop where
  nonzero' : ¬ IsZeroCategory M
  indecomposable' : ∀ (M₁ M₂ : Type u₂) [Category.{v₂} M₁] [Category.{v₂} M₂]
    [LeftModuleCategory' C M₁] [LeftModuleCategory' C M₂]
    [LeftModuleCategory' C (M₁ × M₂)]
    (_ : ModuleEquivalence' C M (M₁ × M₂)), IsZeroCategory M₁ ∨ IsZeroCategory M₂

/-- Auxiliary indecomposability statement used in the proof of Corollary 2.14.9: any
decomposition of the exact module category `M` over the dual category factors through a
zero summand. -/
theorem thm_2_14_6_lem_2_14_3_indecomposable'
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [RigidCategory C] [EnoughProjectives C]
    [HasZeroMorphisms C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory' C M]
    [UnivLE.{u₂, v₂}]
    (h_simple : Simple (𝟙_ C))
    (hM : IsExactModuleCategory' C M) :
    letI catD := DualCatObj'.categoryInstance C M
    letI monD := DualCatObj'.monoidalCategoryInstance C M
    letI modD := DualCatObj'.evalModuleInstance C M
    ∀ (M₁ M₂ : Type u₂) [Category.{v₂} M₁] [Category.{v₂} M₂]
      [@LeftModuleCategory' (DualCatObj' C M) catD monD M₁ _]
      [@LeftModuleCategory' (DualCatObj' C M) catD monD M₂ _]
      [@LeftModuleCategory' (DualCatObj' C M) catD monD (M₁ × M₂) _]
      (_ : @ModuleEquivalence' (DualCatObj' C M) catD monD M _ modD (M₁ × M₂) _ _),
      IsZeroCategory M₁ ∨ IsZeroCategory M₂ := by
  sorry

/-- An exact module category `M` over a tensor category `C` with simple unit object is not
the zero category. This is a nonzero condition used in Corollary 2.14.9. -/
theorem nonzeroModCat_of_exact'
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [RigidCategory C] [EnoughProjectives C]
    [HasZeroMorphisms C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory' C M]
    [UnivLE.{u₂, v₂}]
    (h_simple : Simple (𝟙_ C))
    (hM : IsExactModuleCategory' C M) :
    ¬ IsZeroCategory M := by
  sorry

/-- Corollary 2.14.9: If `C` is a finite tensor (not only multitensor) category, then any
exact module category `M` over `C` is indecomposable as a module category over the dual
category `C_M^*`. -/
theorem corollary_2_14_9
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    [RigidCategory C] [EnoughProjectives C]
    [HasZeroMorphisms C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory' C M]
    [UnivLE.{u₂, v₂}]
    (h_simple : Simple (𝟙_ C))
    (hM : IsExactModuleCategory' C M) :
    letI catD := DualCatObj'.categoryInstance C M
    letI monD := DualCatObj'.monoidalCategoryInstance C M
    letI modD := DualCatObj'.evalModuleInstance C M
    @IsIndecomposableModuleCategory' (DualCatObj' C M) catD monD M _ modD := by

  letI catD := DualCatObj'.categoryInstance C M
  letI monD := DualCatObj'.monoidalCategoryInstance C M
  letI modD := DualCatObj'.evalModuleInstance C M
  exact ⟨nonzeroModCat_of_exact' h_simple hM,
    thm_2_14_6_lem_2_14_3_indecomposable' h_simple hM⟩

end CategoryTheory
