/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ExactModuleCategory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category MonoidalCategory LeftModCat

/-- Corollary 2.7.2: If an exact module category M over C has finitely many isomorphism classes
of simple objects, then M is finite. -/
theorem corollary_2_7_2
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]
    {k : Type*} [Field k] [Abelian C] [Linear k C]
    [Abelian M] [Linear k M]
    [hC : IsFiniteAbelianCategory k C]
    (hFinSimples : ∃ (n : ℕ) (S : Fin n → M),
      (∀ i, Simple (S i)) ∧ (∀ (X : M), Simple X → ∃ i, Nonempty (X ≅ S i))) :
    IsFiniteAbelianCategory k M :=
  ExactModuleCategory.isFiniteAbelianCategory_of_exact (k := k) (C := C) hFinSimples

end CategoryTheory
