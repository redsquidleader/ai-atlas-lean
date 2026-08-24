/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ModuleCategory.Theorem2112
import Atlas.TensorCategories.code.InternalHom
import Mathlib.CategoryTheory.Monoidal.Mod_

open CategoryTheory MonoidalCategory LeftModCat

namespace CategoryTheory

universe u₁ v₁ u₂ v₂

/-- Predicate asserting that a left `C`-module category `M` is finite (placeholder class used
in the statement of Theorem 2.11.6). -/
class IsFiniteModuleCategory
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M] : Prop where
  finite : True

/-- Predicate asserting that a left `C`-module category `M` is exact (placeholder class used
in the statement of Theorem 2.11.6(ii)). -/
class IsExactModuleCat
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M] : Prop where
  exact : True

/-- Predicate asserting that the orbit of `gen` under the `C`-action generates the
Grothendieck group of `M`, used as the generation hypothesis in Theorem 2.11.6(ii). -/
noncomputable def GeneratesGrothendieck
    (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
    (gen : M) : Prop := by sorry

/-- Theorem 2.11.6(i) (EGNO): Every finite left `C`-module category `M_cat` is equivalent, as
a `C`-module category, to the category of modules `Mod_ C A` over some algebra object `A` in
`C`. -/
theorem thm_2_11_6_i
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M_cat : Type u₂} [Category.{v₂} M_cat] [LeftModuleCategory C M_cat]
    [IsFiniteModuleCategory C M_cat] :
    ∃ (A : C) (_ : MonObj A), haveI := ‹MonObj A›; Nonempty (M_cat ≌ Mod_ C A) := by sorry

/-- The algebra structure on the internal endomorphism object `moduleIHom gen gen` arising
from composition of internal homs. -/
noncomputable def monObj_moduleIHom
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M_cat : Type u₂} [Category.{v₂} M_cat] [LeftModuleCategory C M_cat]
    [HasModuleInternalHom C M_cat]
    (gen : M_cat) : MonObj (moduleIHom (C := C) gen gen) := by sorry

/-- Theorem 2.11.6(ii) (EGNO): If `gen ∈ M_cat` generates the Grothendieck group of an exact
left `C`-module category with internal hom, then `M_cat` is equivalent to the category of
modules over the internal endomorphism algebra `moduleIHom gen gen`. -/
theorem thm_2_11_6_ii
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M_cat : Type u₂} [Category.{v₂} M_cat] [LeftModuleCategory C M_cat]
    [HasModuleInternalHom C M_cat]
    [IsExactModuleCat C M_cat]
    (gen : M_cat) (h_gen : GeneratesGrothendieck C gen) :
    letI : MonObj (moduleIHom (C := C) gen gen) := monObj_moduleIHom gen
    Nonempty (M_cat ≌ Mod_ C (moduleIHom (C := C) gen gen)) := by sorry

end CategoryTheory
