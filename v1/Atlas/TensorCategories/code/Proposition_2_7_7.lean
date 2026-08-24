/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ExactModuleCategory

set_option maxHeartbeats 800000

open CategoryTheory Category MonoidalCategory LeftModCat

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

namespace ExactModuleCategory

/-- Proposition 2.7.7 (Etingof–Gelaki–Nikshych–Ostrik): The module subcategories
`M_i` corresponding to the equivalence classes of simple objects under the
`IrrRelated` equivalence relation are exact, and `M` decomposes as the direct
sum of these module subcategories `M_i`. -/
theorem proposition_2_7_7
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M] [Abelian M]
    [EnoughProjectives M]
    (I : Type*) (repr : I → M)
    (repr_simple : ∀ i, Simple (repr i))
    (classification : ∀ (X : M), Simple X → ∃! i, IrrRelated C M (repr i) X) :

    ((∀ (N : M), ∃ i, AllSimpleSubquotientsInClass' C (repr i) N) ∧
     (∀ (i : I) (N : M) (L : C),
       AllSimpleSubquotientsInClass' C (repr i) N →
       AllSimpleSubquotientsInClass' C (repr i) (L ⊗ᵐ N))) ∧

    (∀ (i : I) (P : C) (_ : Projective P) (N : M),
       AllSimpleSubquotientsInClass' C (repr i) N →
       AllSimpleSubquotientsInClass' C (repr i) (P ⊗ᵐ N) ∧ Projective (P ⊗ᵐ N)) :=
  Proposition_2_7_7 I repr repr_simple classification

end ExactModuleCategory

end CategoryTheory
