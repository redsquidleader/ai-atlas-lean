/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ModuleFunctor
import Mathlib.CategoryTheory.Monoidal.Mod_

set_option maxHeartbeats 800000

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Category MonoidalCategory

/-- Two left module categories `ModA` and `ModB` over `C` are Morita equivalent if there
exists an equivalence of module categories between them. -/
def IsMoritaEquivalent
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (ModA : Type u₂) [Category.{v₂} ModA] [LeftModuleCategory' C ModA]
    (ModB : Type u₃) [Category.{v₃} ModB] [LeftModuleCategory' C ModB] : Prop :=
  Nonempty (ModuleEquivalence' C ModA ModB)

/-- EGNO Proposition 2.9.10: for any algebra `A` in `C`, the category `Mod_ C A` of
left `A`-modules in `C` is a left module category over `C`. -/
noncomputable def Proposition_2_9_10
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (A : C) [MonObj A] :
    LeftModuleCategory' C (Mod_ C A) := by sorry

/-- The left `C`-module category structure on `Mod_ C A` coming from Proposition 2.9.10,
registered as an instance. -/
noncomputable instance instLeftModuleCategory'_Mod_
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (A : C) [MonObj A] : LeftModuleCategory' C (Mod_ C A) :=
  Proposition_2_9_10 C A

/-- Two algebras `A` and `B` in `C` are Morita equivalent if their categories of left
modules in `C` are Morita equivalent as `C`-module categories. -/
def IsMoritaEquivalent_Algebras
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (A B : C) [MonObj A] [MonObj B] : Prop :=
  IsMoritaEquivalent C (Mod_ C A) (Mod_ C B)

/-- EGNO Definition 2.9.18: Morita equivalence of algebras in a monoidal category. -/
def Definition_2_9_18 := @IsMoritaEquivalent_Algebras

end CategoryTheory
