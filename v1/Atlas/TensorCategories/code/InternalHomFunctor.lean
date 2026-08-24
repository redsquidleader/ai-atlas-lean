/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.InternalHom
import Atlas.TensorCategories.code.ConcreteModuleCategories

set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category MonoidalCategory LeftModCat

section Functoriality

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [RigidCategory C]
variable {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
variable [HasModuleInternalHom C M]

/-- Functoriality of the internal Hom in the right argument: the identity on `m₂` induces
the identity on `moduleIHom m₁ m₂`. -/
lemma moduleIHomMapRight_id (m₁ m₂ : M) :
    moduleIHomMapRight (C := C) m₁ (𝟙 m₂) = 𝟙 (moduleIHom m₁ m₂) := by
  simp only [moduleIHomMapRight, comp_id]
  exact (moduleIHomEquiv (moduleIHom m₁ m₂) m₁ m₂).apply_symm_apply (𝟙 _)

/-- Functoriality of the internal Hom in the right argument under composition:
`moduleIHomMapRight m₁ (f ≫ g) = moduleIHomMapRight m₁ f ≫ moduleIHomMapRight m₁ g`. -/
lemma moduleIHomMapRight_comp (m₁ : M) {m₂ m₂' m₂'' : M}
    (f : m₂ ⟶ m₂') (g : m₂' ⟶ m₂'') :
    moduleIHomMapRight (C := C) m₁ (f ≫ g) =
      moduleIHomMapRight m₁ f ≫ moduleIHomMapRight m₁ g := by
  sorry

/-- Contravariant functoriality of the internal Hom in the left argument: the identity on
`m₁` induces the identity on `moduleIHom m₁ m₂`. -/
lemma moduleIHomMapLeft_id (m₁ m₂ : M) :
    moduleIHomMapLeft (C := C) (𝟙 m₁) m₂ = 𝟙 (moduleIHom m₁ m₂) := by
  unfold moduleIHomMapLeft
  rw [LeftModuleCategory.actWhiskerLeft_id, id_comp]
  exact (moduleIHomEquiv (moduleIHom m₁ m₂) m₁ m₂).apply_symm_apply (𝟙 _)

/-- Contravariant functoriality of the internal Hom in the left argument under
composition: `moduleIHomMapLeft (f ≫ g) m₂ = moduleIHomMapLeft g m₂ ≫ moduleIHomMapLeft f m₂`. -/
lemma moduleIHomMapLeft_comp {m₁ m₁' m₁'' : M}
    (f : m₁ ⟶ m₁') (g : m₁' ⟶ m₁'') (m₂ : M) :
    moduleIHomMapLeft (C := C) (f ≫ g) m₂ =
      moduleIHomMapLeft g m₂ ≫ moduleIHomMapLeft f m₂ := by
  sorry

end Functoriality

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [RigidCategory C]
variable (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M]
variable [HasModuleInternalHom C M]

/-- Corollary 2.10.5 (part 1): for a fixed object `m₁` of the module category `M`, the
assignment `m₂ ↦ Hom(m₁, m₂)` is a module functor `M ⥤ C`. -/
noncomputable def corollary_2_10_5_part1 (m₁ : M) : ModuleFunctor C M C where
  toFunctor :=
    { obj := fun m₂ => moduleIHom (C := C) m₁ m₂
      map := fun f => moduleIHomMapRight m₁ f
      map_id := fun m₂ => moduleIHomMapRight_id m₁ m₂
      map_comp := fun f g => moduleIHomMapRight_comp m₁ f g }
  strIso X N := moduleIHom_tensor_left_iso X m₁ N
  strIso_natural := by
    intro X₁ X₂ N₁ N₂ f g
    sorry
  strIso_assoc := by
    intro X Y N


    sorry
  strIso_unit := by
    intro N


    sorry

/-- Corollary 2.10.5 (part 2): for a fixed object `m₂` of `M`, the assignment
`m₁ ↦ Hom(m₁, m₂)` is a module functor `Mᵒᵖ ⥤ C`. -/
def corollary_2_10_5_part2
    [LeftModuleCategory C Mᵒᵖ] (m₂ : M) : ModuleFunctor C Mᵒᵖ C := by sorry

end CategoryTheory
