/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.QuasiBialgebra

open CategoryTheory MonoidalCategory

open scoped TensorProduct

universe u


/-- Carrier type for the representation category `Rep(H)` of a quasi-bialgebra `H`. -/
def QuasiBialgebraRepCat (k : Type u) [Field k]
    (H : Type u) [Ring H] [Algebra k H]
    (qb : QuasiBialgebra k H) : Type u := by sorry

/-- Category structure on the representation category of a quasi-bialgebra. -/
def QuasiBialgebraRepCat.instCategory (k : Type u) [Field k]
    (H : Type u) [Ring H] [Algebra k H]
    (qb : QuasiBialgebra k H) : Category.{u} (QuasiBialgebraRepCat k H qb) := by sorry

/-- Monoidal category structure on the representation category of a quasi-bialgebra. -/
def QuasiBialgebraRepCat.instMonoidalCategory (k : Type u) [Field k]
    (H : Type u) [Ring H] [Algebra k H]
    (qb : QuasiBialgebra k H) :
    @MonoidalCategory (QuasiBialgebraRepCat k H qb)
      (QuasiBialgebraRepCat.instCategory k H qb) := by sorry

/-- Typeclass instance registering the category structure on `QuasiBialgebraRepCat`. -/
noncomputable instance (k : Type u) [Field k]
    (H : Type u) [Ring H] [Algebra k H]
    (qb : QuasiBialgebra k H) :
    Category.{u} (QuasiBialgebraRepCat k H qb) :=
  QuasiBialgebraRepCat.instCategory k H qb

/-- Typeclass instance registering the monoidal category structure on
`QuasiBialgebraRepCat`. -/
noncomputable instance (k : Type u) [Field k]
    (H : Type u) [Ring H] [Algebra k H]
    (qb : QuasiBialgebra k H) :
    MonoidalCategory (QuasiBialgebraRepCat k H qb) :=
  QuasiBialgebraRepCat.instMonoidalCategory k H qb


/-- Monoidal equivalence between two monoidal categories: an underlying equivalence
of categories whose forward functor is monoidal. -/
structure MonoidalEquiv
    (C : Type*) [Category C] [MonoidalCategory C]
    (D : Type*) [Category D] [MonoidalCategory D] where
  equiv : C ≌ D
  isMonoidal : Functor.Monoidal equiv.functor


/-- Twist-equivalent quasi-bialgebras have monoidally equivalent representation
categories: the categorical realization of Theorem 1.34.8 up to twist equivalence. -/
theorem thm_1_34_8_twist_equiv_monoidal_equiv
    (k : Type u) [Field k]
    (H : Type u) [Ring H] [Algebra k H]
    (qb₁ qb₂ : QuasiBialgebra k H)
    (htwist : QuasiBialgebraTwistEquiv qb₁ qb₂) :
    Nonempty (MonoidalEquiv
      (QuasiBialgebraRepCat k H qb₁)
      (QuasiBialgebraRepCat k H qb₂)) := by sorry
