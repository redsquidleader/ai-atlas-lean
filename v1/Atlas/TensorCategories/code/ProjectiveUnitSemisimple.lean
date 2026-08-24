/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Subobject.Lattice

set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Limits

universe v u

namespace TensorCategories

/-- An object `X` has finite length if its lattice of subobjects satisfies both ascending
and descending chain conditions. -/
def HasFiniteLength {C : Type u} [Category.{v} C] (X : C) : Prop :=
  WellFoundedLT (Subobject X) ∧ WellFoundedGT (Subobject X)

/-- A `k`-linear abelian category is locally finite (Definition 1.12.1) if all Hom spaces
are finite-dimensional over `k` and every object has finite length. -/
class LocallyFiniteCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C] : Prop where
  homFinite : ∀ (X Y : C), Module.Finite k (X ⟶ Y)
  hasFiniteLength : ∀ (X : C), HasFiniteLength X

/-- A multiring category over `k` (Definition 1.13.3) is a locally finite `k`-linear abelian
monoidal category whose tensor product is biexact (preserves monomorphisms and epimorphisms
in each variable). -/
class MultiringCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    : Prop extends LocallyFiniteCategory k C where
  whiskerRight_mono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f] (Z : C), Mono (f ▷ Z)
  whiskerLeft_mono : ∀ (Z : C) {X Y : C} (f : X ⟶ Y) [Mono f], Mono (Z ◁ f)
  whiskerRight_epi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f] (Z : C), Epi (f ▷ Z)
  whiskerLeft_epi : ∀ (Z : C) {X Y : C} (f : X ⟶ Y) [Epi f], Epi (Z ◁ f)

/-- A category is semisimple if every object is isomorphic to a finite biproduct of simple
objects. -/
class IsSemisimpleCategory (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroMorphisms C] : Prop where
  semisimple : ∀ (X : C), ∃ (n : ℕ) (Y : Fin n → C) (_ : ∀ i, Simple (Y i))
    (_ : HasBiproduct Y), Nonempty (X ≅ ⨁ Y)

section Prop_1_13_6

/-- Proposition 1.13.6: If `P` is projective in a multiring category and `X` has a right dual,
then `P ⊗ X` is projective. -/
theorem Proposition_1_13_6_projective_tensor_right_dual
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {P X : C} [hP : Projective P] [hX : HasRightDual X]
    (whiskerRight_epi : ∀ {A B : C} (f : A ⟶ B) [Epi f] (Z : C), Epi (f ▷ Z)) :
    Projective (P ⊗ X) where
  factors := by
    intro E Y f e he

    let f' : P ⟶ Y ⊗ Xᘁ := (tensorRightHomEquiv P X (Xᘁ) Y) f

    have he' : Epi (e ▷ Xᘁ) := whiskerRight_epi e (Xᘁ)

    obtain ⟨g', hg'⟩ := Projective.factors f' (e ▷ Xᘁ)

    use (tensorRightHomEquiv P X (Xᘁ) E).symm g'

    apply (tensorRightHomEquiv P X (Xᘁ) Y).injective
    rw [tensorRightHomEquiv_naturality]
    change (tensorRightHomEquiv P X (Xᘁ) E) ((tensorRightHomEquiv P X (Xᘁ) E).symm g') ≫
      e ▷ Xᘁ = f'
    rw [Equiv.apply_symm_apply]
    exact hg'

end Prop_1_13_6

section Cor_1_13_7

variable (k : Type*) [Field k]
variable (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear k C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]

/-- Helper: a multiring category in which every object is projective is semisimple. -/
theorem allProjective_implies_semisimple
    [MultiringCategory k C]
    (h : ∀ (X : C), Projective X) : IsSemisimpleCategory C := by sorry

/-- Helper: in a semisimple category, every object is projective. -/
theorem semisimple_implies_projective
    [IsSemisimpleCategory C] (X : C) : Projective X := by sorry

/-- Corollary 1.13.7: in a multiring category with right duals, the unit object `𝟙_ C` is
projective if and only if the category is semisimple. -/
theorem Corollary_1_13_7_projective_unit_iff_semisimple
    [hMR : MultiringCategory k C]
    [∀ (X : C), HasRightDual X] :
    Projective (𝟙_ C) ↔ IsSemisimpleCategory C := by
  constructor
  ·
    intro hProj


    apply allProjective_implies_semisimple k C
    intro X

    have h1 : Projective (𝟙_ C ⊗ X) :=
      Proposition_1_13_6_projective_tensor_right_dual hMR.whiskerRight_epi

    exact Projective.of_iso (λ_ X) h1
  ·
    intro hSS
    exact semisimple_implies_projective C (𝟙_ C)

end Cor_1_13_7

end TensorCategories
