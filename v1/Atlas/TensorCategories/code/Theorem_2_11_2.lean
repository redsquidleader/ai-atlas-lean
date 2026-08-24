/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Equivalence

set_option maxHeartbeats 800000

set_option autoImplicit false

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category MonoidalCategory

/-- Internal algebra object in a monoidal category `C`: an object equipped with a
multiplication and unit morphism. -/
structure AlgObj₂ (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] where
  carrier : C
  mul : carrier ⊗ carrier ⟶ carrier
  unit : 𝟙_ C ⟶ carrier

/-- Right module object over an internal algebra `A` in a monoidal category: an
object `obj` of `C` together with a right action `obj ⊗ A.carrier ⟶ obj`. -/
structure RModObj₂ {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    (A : AlgObj₂ C) where
  obj : C
  act : obj ⊗ A.carrier ⟶ obj

/-- Type of right `A`-modules in `C`, used as the carrier of the category
`Mod_C(A)`. -/
def ModC₂ {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    (A : AlgObj₂ C) :=
  RModObj₂ A

/-- Morphism of right `A`-modules in `C`: a morphism `M.obj ⟶ N.obj` in `C` that
intertwines the right `A`-actions. -/
@[ext]
structure RModHom₂ {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {A : AlgObj₂ C} (M N : RModObj₂ A) where
  hom : M.obj ⟶ N.obj
  comm : (hom ▷ A.carrier) ≫ N.act = M.act ≫ hom := by aesop_cat

attribute [reassoc (attr := simp)] RModHom₂.comm

/-- Category structure on `ModC₂ A`, the category of right `A`-modules in `C`. -/
instance modC₂_category {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    (A : AlgObj₂ C) : Category.{v₁} (ModC₂ A) where
  Hom M N := RModHom₂ M N
  id M := { hom := 𝟙 M.obj, comm := by simp }
  comp f g := {
    hom := f.hom ≫ g.hom
    comm := by
      simp only [comp_whiskerRight, assoc]
      rw [g.comm, ← assoc, f.comm, assoc]
  }
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp [assoc]

/-- Data for the internal-Hom setup of Theorem 2.11.2: a chosen generator
`gen ∈ M`, the action functor `C ⥤ M`, the internal endomorphism algebra `A`,
and the corresponding functor `M ⥤ ModC₂ A` together with the natural identification
of the composition with the free-module functor. -/
structure InternalHomData₂ (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] where
  gen : M
  actOnGen : C ⥤ M
  endAlg : AlgObj₂ C
  F : M ⥤ ModC₂ endAlg
  freeModule : C ⥤ ModC₂ endAlg
  moduleCompat : actOnGen ⋙ F ≅ freeModule

/-- Right-exactness hypothesis on the internal-Hom functor `F = Hom(M, -)`. -/
structure InternalHomRightExact₂
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M]
    (hom : InternalHomData₂ C M) : Prop where
  preservesEpi : ∀ {N₁ N₂ : M} (f : N₁ ⟶ N₂), Epi f → Epi (hom.F.map f)

/-- Generation hypothesis: every object of `M` admits an epimorphism from some
`X ⊗ M` (i.e. `hom.actOnGen.obj X`). -/
structure InternalHomGeneration₂
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M]
    (hom : InternalHomData₂ C M) : Prop where
  generation : ∀ (N : M), ∃ (X : C) (f : hom.actOnGen.obj X ⟶ N), Epi f

/-- Step 1 in the proof of Theorem 2.11.2: the natural map sending a morphism
`hom.actOnGen.obj X ⟶ N₂` to its image under `F` is a bijection (Hom on free modules
identifies with Hom in `M`). -/
theorem step1_homIso_free₂
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M]
    (hom : InternalHomData₂ C M)
    (hExact : InternalHomRightExact₂ hom)
    (hGen : InternalHomGeneration₂ hom)
    (X : C) (N₂ : M) :
    Function.Bijective (fun (f : hom.actOnGen.obj X ⟶ N₂) => hom.F.map f) := by
  sorry

/-- Step 2(faithful) in the proof of Theorem 2.11.2: the internal-Hom functor `F` is
faithful. -/
theorem step2_faithful₂
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M]
    (hom : InternalHomData₂ C M)
    (hExact : InternalHomRightExact₂ hom)
    (hGen : InternalHomGeneration₂ hom) :
    hom.F.Faithful := by
  sorry

/-- Step 2(full) in the proof of Theorem 2.11.2: the internal-Hom functor `F` is
full. -/
theorem step2_full₂
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M]
    (hom : InternalHomData₂ C M)
    (hExact : InternalHomRightExact₂ hom)
    (hGen : InternalHomGeneration₂ hom) :
    hom.F.Full := by
  sorry

/-- Step 3 in the proof of Theorem 2.11.2: the internal-Hom functor `F` is essentially
surjective onto `ModC₂ A`. -/
theorem step3_essSurj₂
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M]
    (hom : InternalHomData₂ C M)
    (hExact : InternalHomRightExact₂ hom)
    (hGen : InternalHomGeneration₂ hom) :
    hom.F.EssSurj := by
  sorry

/-- Underlying equivalence of categories of Theorem 2.11.2: assembling fullness,
faithfulness, and essential surjectivity yields `M ≌ ModC₂ A`. -/
noncomputable def theorem_2_11_2_equiv
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M]
    (hom : InternalHomData₂ C M)
    (hExact : InternalHomRightExact₂ hom)
    (hGen : InternalHomGeneration₂ hom) :
    M ≌ ModC₂ hom.endAlg := by
  haveI : hom.F.Faithful := step2_faithful₂ hom hExact hGen
  haveI : hom.F.Full := step2_full₂ hom hExact hGen
  haveI : hom.F.EssSurj := step3_essSurj₂ hom hExact hGen
  haveI : hom.F.IsEquivalence := Functor.IsEquivalence.mk
  exact hom.F.asEquivalence

/-- Theorem 2.11.2 (Ostrik): Let `M` be a module category over `C` with object
`M ∈ M` such that `Hom(M, -)` is right exact and any object of `M` admits a
surjection from `X ⊗ M` for some `X ∈ C`. Setting `A = Hom(M, M)`, the functor
`F = Hom(M, -) : M → Mod_C(A)` is an equivalence of module categories. -/
theorem thm_2_11_2
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M]
    (hom : InternalHomData₂ C M)
    (hExact : InternalHomRightExact₂ hom)
    (hGen : InternalHomGeneration₂ hom) :
    Nonempty (M ≌ ModC₂ hom.endAlg) :=
  ⟨theorem_2_11_2_equiv hom hExact hGen⟩

end CategoryTheory
