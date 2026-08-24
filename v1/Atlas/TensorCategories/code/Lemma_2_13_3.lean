/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ModuleFunctorDefs

set_option maxHeartbeats 400000

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category MonoidalCategory LeftModCat

/-- Lemma 2.13.3 (EGNO). Any module functor between exact module categories admits both a
left and a right adjoint. Delegates to `moduleFunctorHasAdjoints`. -/
theorem Lemma_2_13_3
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M₁ : Type u₂} [Category.{v₂} M₁] [ExactModuleCategory C M₁]
    {M₂ : Type u₃} [Category.{v₃} M₂] [ExactModuleCategory C M₂]
    (F : ModuleFunctor C M₁ M₂) :
    F.toFunctor.IsLeftAdjoint ∧ F.toFunctor.IsRightAdjoint :=
  moduleFunctorHasAdjoints F

end CategoryTheory
