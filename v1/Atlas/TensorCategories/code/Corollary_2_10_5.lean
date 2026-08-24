/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.InternalHom

set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category MonoidalCategory LeftModCat

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [RigidCategory C]
variable (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M]
variable [HasModuleInternalHom C M]

/-- Corollary 2.10.5 (1): For a fixed M₁ in a module category M over C, the assignment
M₂ ↦ Hom(M₁, M₂) defines a module functor M → C, where Hom denotes the internal Hom. -/
noncomputable def corollary_2_10_5_part1
    [LeftModuleCategory C C] (m₁ : M) : ModuleFunctor C M C where
  toFunctor :=
    { obj := fun m₂ => moduleIHom (C := C) m₁ m₂
      map := fun f => moduleIHomMapRight m₁ f
      map_id := fun m₂ => by
        simp only [moduleIHomMapRight, comp_id]
        exact (moduleIHomEquiv (C := C) (moduleIHom m₁ m₂) m₁ m₂).apply_symm_apply (𝟙 _)
      map_comp := fun {m₂ m₂' m₂''} f g => by
        simp only [moduleIHomMapRight]
        have h := moduleIHomEquiv_natural_right (C := C) _ m₁ g
            (moduleIHomEv (C := C) m₁ m₂ ≫ f)
        simp only [assoc] at h
        exact h }
  strIso X N := by
    exact
    { hom := sorry
      inv := sorry
      hom_inv_id := sorry
      inv_hom_id := sorry }
  strIso_natural := by
    intro X₁ X₂ N₁ N₂ f g
    sorry
  strIso_assoc := by
    intro X Y N
    sorry
  strIso_unit := by
    intro N
    sorry

/-- Corollary 2.10.5 (2): For a fixed M₂ in a module category M over C, the assignment
M₁ ↦ Hom(M₁, M₂) defines a module functor M → C^op, where Hom denotes the internal Hom. -/
def corollary_2_10_5_part2
    [LeftModuleCategory C Cᵒᵖ] (m₂ : M) : ModuleFunctor C M Cᵒᵖ := by sorry

end CategoryTheory
