/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ModuleFunctorDefs
import Atlas.TensorCategories.code.FiniteAbelianCategoryDef
import Atlas.TensorCategories.code.FiniteTensorCategory

set_option maxHeartbeats 800000

open CategoryTheory

universe w v₁ v₂ v₃ u₁ u₂ u₃

/-- The category of module functors between two left `C`-module categories carries a
canonical abelian structure. -/
noncomputable def moduleFunctorCategoryIsAbelian
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M₁ : Type u₂) [Category.{v₂} M₁] [LeftModuleCategory C M₁]
    (M₂ : Type u₃) [Category.{v₃} M₂] [LeftModuleCategory C M₂] :
    @Abelian (ModuleFunctor C M₁ M₂) (moduleFunctorCategory C M₁ M₂) := by sorry

/-- The category of module functors between two left `C`-module categories carries a
canonical `k`-linear structure compatible with the abelian structure. -/
noncomputable def moduleFunctorCategoryIsLinear
    (k : Type w) [Field k]
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M₁ : Type u₂) [Category.{v₂} M₁] [LeftModuleCategory C M₁]
    (M₂ : Type u₃) [Category.{v₃} M₂] [LeftModuleCategory C M₂] :
    @Linear k _ (ModuleFunctor C M₁ M₂) (moduleFunctorCategory C M₁ M₂)
      (moduleFunctorCategoryIsAbelian C M₁ M₂).toPreadditive := by sorry

/-- For a finite tensor category `C` and exact left `C`-module categories `M₁, M₂`, the
category of module functors between them is a finite abelian category. -/
theorem moduleFunctorCategory_isFinite
    (k : Type w) [Field k]
    (C : Type u₁) [Category.{v₁} C] [FiniteTensorCategory k C]
    (M₁ : Type u₂) [Category.{v₂} M₁] [ExactModuleCategory C M₁]
    (M₂ : Type u₃) [Category.{v₃} M₂] [ExactModuleCategory C M₂] :
    @IsFiniteAbelianCategory k _
      (ModuleFunctor C M₁ M₂)
      (moduleFunctorCategory C M₁ M₂)
      (moduleFunctorCategoryIsAbelian C M₁ M₂)
      (moduleFunctorCategoryIsLinear k C M₁ M₂) := by sorry

/-- Proposition 2.13.5 (EGNO): The category of module functors between two exact module
categories over a finite tensor category is itself a finite abelian category. -/
theorem proposition_2_13_5
    (k : Type w) [Field k]
    (C : Type u₁) [Category.{v₁} C] [FiniteTensorCategory k C]
    (M₁ : Type u₂) [Category.{v₂} M₁] [ExactModuleCategory C M₁]
    (M₂ : Type u₃) [Category.{v₃} M₂] [ExactModuleCategory C M₂] :
    @IsFiniteAbelianCategory k _
      (ModuleFunctor C M₁ M₂)
      (moduleFunctorCategory C M₁ M₂)
      (moduleFunctorCategoryIsAbelian C M₁ M₂)
      (moduleFunctorCategoryIsLinear k C M₁ M₂) :=
  moduleFunctorCategory_isFinite k C M₁ M₂
