/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_

set_option linter.unusedSimpArgs false

universe u v

open CategoryTheory MonoidalCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

open HasLeftDual HasRightDual ExactPairing MonObj

namespace Lemma2147

/-- The canonical algebra multiplication on `ᘁA ⊗ A` for an object `A` with a left dual,
defined by inserting the evaluation `ε_ (ᘁA) A` in the middle. -/
noncomputable def dualAlgMul (A : C) [HasLeftDual A] :
    ((ᘁA : C) ⊗ A) ⊗ ((ᘁA : C) ⊗ A) ⟶ (ᘁA : C) ⊗ A :=
  (α_ (ᘁA : C) A ((ᘁA : C) ⊗ A)).hom ≫
  (ᘁA : C) ◁ ((α_ A (ᘁA : C) A).inv ≫ (ε_ (ᘁA : C) A ▷ A) ≫ (λ_ A).hom)

/-- A left module object over an algebra `B` in `C`: an object `Y` equipped with an action
`B ⊗ Y ⟶ Y` satisfying the usual unit and associativity axioms. -/
structure LeftModObj (B : C) [MonObj B] (Y : C) where
  act : B ⊗ Y ⟶ Y
  act_one : (λ_ Y).inv ≫ (MonObj.one ▷ Y) ≫ act = 𝟙 Y
  act_assoc : (α_ B B Y).hom ≫ (B ◁ act) ≫ act = (MonObj.mul ▷ Y) ≫ act

/-- A right module object over an algebra `B` in `C`: an object `Y` equipped with an action
`Y ⊗ B ⟶ Y` satisfying the usual unit and associativity axioms. -/
structure RightModObj (B : C) [MonObj B] (Y : C) where
  act : Y ⊗ B ⟶ Y
  act_one : (ρ_ Y).inv ≫ (Y ◁ MonObj.one) ≫ act = 𝟙 Y
  act_assoc : (α_ Y B B).inv ≫ (act ▷ B) ≫ act = (Y ◁ MonObj.mul) ≫ act

/-- Auxiliary essential-surjectivity statement from the proof of Theorem 2.11.2 in EGNO:
every left `A`-module is isomorphic to one in the family `{F N}`. -/
theorem thm_2_11_2_essSurj_left
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (A : C) [MonObj A]
    (F : C → C)
    (F_modStr : ∀ (N : C), LeftModObj (C := C) A (F N))
    (L : C) (lm : LeftModObj (C := C) A L) :
    ∃ (N : C), Nonempty (L ≅ F N) := by sorry

/-- Right-module analogue of `thm_2_11_2_essSurj_left`: every right `A`-module is isomorphic
to one in the family `{G N}`. -/
theorem thm_2_11_2_essSurj_right
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (A : C) [MonObj A]
    (G : C → C)
    (G_modStr : ∀ (N : C), RightModObj (C := C) A (G N))
    (L : C) (rm : RightModObj (C := C) A L) :
    ∃ (N : C), Nonempty (L ≅ G N) := by sorry

/-- Associativity of the canonical left action of `ᘁA ⊗ A` on `ᘁA ⊗ N` from Example 2.10.8
in EGNO; left as a sorry stub. -/
theorem example_2_10_8_left_act_assoc
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (A : C) [MonObj A] [HasLeftDual A] [MonObj ((ᘁA : C) ⊗ A)]
    (h_mul : MonObj.mul (X := (ᘁA : C) ⊗ A) = dualAlgMul A)
    (N : C) :
    let B := (ᘁA : C) ⊗ A
    let act := (α_ (ᘁA : C) A ((ᘁA : C) ⊗ N)).hom ≫
      (ᘁA : C) ◁ ((α_ A (ᘁA : C) N).inv ≫ (ε_ (ᘁA : C) A ▷ N) ≫ (λ_ N).hom)
    (α_ B B ((ᘁA : C) ⊗ N)).hom ≫ (B ◁ act) ≫ act = (MonObj.mul ▷ ((ᘁA : C) ⊗ N)) ≫ act := by sorry

/-- Associativity of the canonical right action of `ᘁA ⊗ A` on `N ⊗ A` from Example 2.10.8
in EGNO; left as a sorry stub. -/
theorem example_2_10_8_right_act_assoc
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (A : C) [MonObj A] [HasLeftDual A] [MonObj ((ᘁA : C) ⊗ A)]
    (h_mul : MonObj.mul (X := (ᘁA : C) ⊗ A) = dualAlgMul A)
    (N : C) :
    let B := (ᘁA : C) ⊗ A
    let act := (α_ N A ((ᘁA : C) ⊗ A)).hom ≫
      N ◁ ((α_ A (ᘁA : C) A).inv ≫ (ε_ (ᘁA : C) A ▷ A) ≫ (λ_ A).hom)
    (α_ (N ⊗ A) B B).inv ≫ (act ▷ B) ≫ act = ((N ⊗ A) ◁ MonObj.mul) ≫ act := by sorry

/-- Canonical left `(ᘁA ⊗ A)`-module structure on `ᘁA ⊗ N` of Example 2.10.8. -/
noncomputable def example_2_10_8_leftMod
    (A : C) [MonObj A] [HasLeftDual A] [MonObj ((ᘁA : C) ⊗ A)]
    (h_one : MonObj.one (X := (ᘁA : C) ⊗ A) = η_ (ᘁA : C) A)
    (h_mul : MonObj.mul (X := (ᘁA : C) ⊗ A) = dualAlgMul A)
    (N : C) : LeftModObj (C := C) ((ᘁA : C) ⊗ A) ((ᘁA : C) ⊗ N) where
  act := (α_ (ᘁA : C) A ((ᘁA : C) ⊗ N)).hom ≫
    (ᘁA : C) ◁ ((α_ A (ᘁA : C) N).inv ≫ (ε_ (ᘁA : C) A ▷ N) ≫ (λ_ N).hom)
  act_one := by
    rw [h_one]
    simp only [MonoidalCategory.whiskerLeft_comp]
    slice_lhs 3 4 => rw [← MonoidalCategory.pentagon_inv_hom_hom_hom_inv]
    slice_lhs 2 3 => rw [MonoidalCategory.associator_inv_naturality_left]
    slice_lhs 5 6 => rw [← MonoidalCategory.associator_naturality_middle]
    slice_lhs 3 5 =>
      rw [← comp_whiskerRight, ← comp_whiskerRight]
      rw [ExactPairing.evaluation_coevaluation]
    monoidal
  act_assoc := example_2_10_8_left_act_assoc A h_mul N

/-- Canonical right `(ᘁA ⊗ A)`-module structure on `N ⊗ A` of Example 2.10.8. -/
noncomputable def example_2_10_8_rightMod
    (A : C) [MonObj A] [HasLeftDual A] [MonObj ((ᘁA : C) ⊗ A)]
    (h_one : MonObj.one (X := (ᘁA : C) ⊗ A) = η_ (ᘁA : C) A)
    (h_mul : MonObj.mul (X := (ᘁA : C) ⊗ A) = dualAlgMul A)
    (N : C) : RightModObj (C := C) ((ᘁA : C) ⊗ A) (N ⊗ A) where
  act := (α_ N A ((ᘁA : C) ⊗ A)).hom ≫
    N ◁ ((α_ A (ᘁA : C) A).inv ≫ (ε_ (ᘁA : C) A ▷ A) ≫ (λ_ A).hom)
  act_one := by
    rw [h_one]
    simp only [MonoidalCategory.whiskerLeft_comp]
    slice_lhs 2 3 => rw [MonoidalCategory.associator_naturality_right]
    slice_lhs 3 5 =>
      rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp]
      rw [ExactPairing.coevaluation_evaluation]
    monoidal
  act_assoc := example_2_10_8_right_act_assoc A h_mul N

/-- Every left `(ᘁA ⊗ A)`-module is isomorphic to `ᘁA ⊗ X` for some `X : C`. Combines the
canonical module structure of Example 2.10.8 with the essential surjectivity statement
`thm_2_11_2_essSurj_left`. -/
theorem leftBmod_of_leftDual_tensor
    (A : C) [MonObj A] [HasLeftDual A] [MonObj ((ᘁA : C) ⊗ A)]
    (h_one : MonObj.one (X := (ᘁA : C) ⊗ A) = η_ (ᘁA : C) A)
    (h_mul : MonObj.mul (X := (ᘁA : C) ⊗ A) = dualAlgMul A)
    (Y : C) (lm : LeftModObj (C := C) ((ᘁA : C) ⊗ A) Y) :
    ∃ (X : C), Nonempty (Y ≅ (ᘁA : C) ⊗ X) :=
  thm_2_11_2_essSurj_left
    ((ᘁA : C) ⊗ A)
    (fun N => (ᘁA : C) ⊗ N)
    (example_2_10_8_leftMod A h_one h_mul)
    Y lm

/-- Right-module analogue of `leftBmod_of_leftDual_tensor`: every right `(ᘁA ⊗ A)`-module
is isomorphic to `X ⊗ A` for some `X : C`. -/
theorem rightBmod_of_leftDual_tensor
    (A : C) [MonObj A] [HasLeftDual A] [MonObj ((ᘁA : C) ⊗ A)]
    (h_one : MonObj.one (X := (ᘁA : C) ⊗ A) = η_ (ᘁA : C) A)
    (h_mul : MonObj.mul (X := (ᘁA : C) ⊗ A) = dualAlgMul A)
    (Y : C) (rm : RightModObj (C := C) ((ᘁA : C) ⊗ A) Y) :
    ∃ (X : C), Nonempty (Y ≅ X ⊗ A) :=
  thm_2_11_2_essSurj_right
    ((ᘁA : C) ⊗ A)
    (fun N => N ⊗ A)
    (example_2_10_8_rightMod A h_one h_mul)
    Y rm

/-- Helper combining both sides of Lemma 2.14.7 inside the auxiliary namespace `Lemma2147`. -/
theorem lem_2_14_7
    (A : C) [MonObj A] [HasLeftDual A] [MonObj ((ᘁA : C) ⊗ A)]
    (h_one : MonObj.one (X := (ᘁA : C) ⊗ A) = η_ (ᘁA : C) A)
    (h_mul : MonObj.mul (X := (ᘁA : C) ⊗ A) = dualAlgMul A) :
    (∀ (Y : C) (_ : LeftModObj ((ᘁA : C) ⊗ A) Y),
      ∃ (X : C), Nonempty (Y ≅ (ᘁA : C) ⊗ X)) ∧
    (∀ (Y : C) (_ : RightModObj ((ᘁA : C) ⊗ A) Y),
      ∃ (X : C), Nonempty (Y ≅ X ⊗ A)) :=
  ⟨leftBmod_of_leftDual_tensor A h_one h_mul,
   rightBmod_of_leftDual_tensor A h_one h_mul⟩

end Lemma2147

/-- Lemma 2.14.7 (EGNO). For an object `A` with a left dual whose algebra `ᘁA ⊗ A` has the
standard multiplication, every left module is `ᘁA ⊗ X` for some `X` and every right module is
`X ⊗ A` for some `X`. -/
theorem Lemma_2_14_7
    (A : C) [MonObj A] [HasLeftDual A] [MonObj ((ᘁA : C) ⊗ A)]
    (h_one : MonObj.one (X := (ᘁA : C) ⊗ A) = η_ (ᘁA : C) A)
    (h_mul : MonObj.mul (X := (ᘁA : C) ⊗ A) = Lemma2147.dualAlgMul A) :
    (∀ (Y : C) (_ : Lemma2147.LeftModObj ((ᘁA : C) ⊗ A) Y),
      ∃ (X : C), Nonempty (Y ≅ (ᘁA : C) ⊗ X)) ∧
    (∀ (Y : C) (_ : Lemma2147.RightModObj ((ᘁA : C) ⊗ A) Y),
      ∃ (X : C), Nonempty (Y ≅ X ⊗ A)) :=
  Lemma2147.lem_2_14_7 A h_one h_mul

end CategoryTheory
