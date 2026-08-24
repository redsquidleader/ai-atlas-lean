/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.DeligneTensorProduct
import Atlas.TensorCategories.code.TensorCategoryDef

set_option maxHeartbeats 400000

noncomputable section

open TensorProduct CategoryTheory

namespace Deligne

open TensorCategories

/-- Proposition 1.46.3: if `C` and `D` are multitensor categories, then the Deligne
tensor product `C ⊠ D` carries a natural multitensor category structure (with
compatible monoidal, preadditive, linear and rigid structures). -/
theorem Proposition_1_46_3
    (k : Type*) [Field k]
    {C : Type*} [Category C] [Abelian C] [Linear k C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] [MultitensorCategory k C]
    {D : Type*} [Category D] [Abelian D] [Linear k D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear k D]
    [RigidCategory D] [MultitensorCategory k D]
    (T : HasDeligneTensorProduct k C D) :
    ∃ (mc : MonoidalCategory T.tensorCat)
      (mp : @MonoidalPreadditive T.tensorCat _ _ mc)
      (ml : @MonoidalLinear k _ T.tensorCat _ _ _ mc mp)
      (rc : @RigidCategory T.tensorCat _ mc),
      @MultitensorCategory k _ T.tensorCat _ _ _ _ mc mp ml rc ∧
      @LocallyFiniteCategory k _ T.tensorCat _ _ _ _ := by
  sorry

end Deligne

open Deligne TensorCategories CategoryTheory in
/-- Proposition 1.46.3 (root-namespace alias): if `C` and `D` are multitensor categories
then their Deligne tensor product `C ⊠ D` inherits a multitensor category structure. -/
theorem Proposition_1_46_3
    (k : Type*) [Field k]
    {C : Type*} [Category C] [Abelian C] [Linear k C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    [RigidCategory C] [MultitensorCategory k C]
    {D : Type*} [Category D] [Abelian D] [Linear k D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear k D]
    [RigidCategory D] [MultitensorCategory k D]
    (T : HasDeligneTensorProduct k C D) :
    ∃ (mc : MonoidalCategory T.tensorCat)
      (mp : @MonoidalPreadditive T.tensorCat _ _ mc)
      (ml : @MonoidalLinear k _ T.tensorCat _ _ _ mc mp)
      (rc : @RigidCategory T.tensorCat _ mc),
      @MultitensorCategory k _ T.tensorCat _ _ _ _ mc mp ml rc ∧
      @LocallyFiniteCategory k _ T.tensorCat _ _ _ _ :=
  Deligne.Proposition_1_46_3 k T

end
