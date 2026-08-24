/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.DualCategory

open CategoryTheory

universe u v

/-- Proposition 2.14.14 ("Basic identity", Etingof–Gelaki–Nikshych–Ostrik):
For objects `X, Y, Z ∈ M`, there is a canonical isomorphism
`Hom_C(X, Y) ⊗ Z ≅ *Hom_{C*_M}(Z, X) ⊗ Y`. -/
theorem CategoryTheory.proposition_2_14_14_basic_identity
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {M : Type u} [Category.{v} M] [LeftModuleCategory C M]
    [RigidCategory C]
    (hExact : ExactModuleCategory C M)
    (inst_dual : LeftModuleCategory (DualCatObj C M) M)
    (X Y Z : M) :
    Nonempty (
      @LeftModuleCategoryStruct.actObj C _ _ M _ _ (moduleIHom X Y) Z ≅
      @LeftModuleCategoryStruct.actObj (DualCatObj C M) _ _ M _
        inst_dual.toLeftModuleCategoryStruct
        (leftDualDualCat inst_dual (moduleIHomDual inst_dual Z X)) Y) :=
  Proposition_2_14_14 hExact inst_dual X Y Z
