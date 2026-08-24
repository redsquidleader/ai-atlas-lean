/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Linear
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Limits

universe v u

namespace TensorCategories

/-- An object has finite length if the subobject lattice is both noetherian and
artinian (well-founded under `<` and `>`). -/
def HasFiniteLength {C : Type u} [Category.{v} C] (X : C) : Prop :=
  WellFoundedLT (Subobject X) ∧ WellFoundedGT (Subobject X)

/-- A locally finite `k`-linear abelian category: every hom-space is finite-dimensional
over `k`, and every object has finite length. -/
class LocallyFiniteCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C] : Prop where
  homFinite : ∀ (X Y : C), Module.Finite k (X ⟶ Y)
  hasFiniteLength : ∀ (X : C), HasFiniteLength X

attribute [instance] LocallyFiniteCategory.homFinite

/-- Multiring category: a locally finite `k`-linear abelian monoidal category in which
left and right whiskerings preserve both monomorphisms and epimorphisms. -/
class MultiringCategory (k : Type*) [Field k] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    : Prop extends LocallyFiniteCategory k C where
  whiskerRight_mono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f] (Z : C), Mono (f ▷ Z)
  whiskerLeft_mono : ∀ (Z : C) {X Y : C} (f : X ⟶ Y) [Mono f], Mono (Z ◁ f)
  whiskerRight_epi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f] (Z : C), Epi (f ▷ Z)
  whiskerLeft_epi : ∀ (Z : C) {X Y : C} (f : X ⟶ Y) [Epi f], Epi (Z ◁ f)

/-- A category is semisimple if every object decomposes as a finite biproduct of
simple objects. -/
class IsSemisimpleCategory (C : Type u) [Category.{v} C] [Preadditive C]
    [HasZeroMorphisms C] : Prop where
  semisimple : ∀ (X : C), ∃ (n : ℕ) (Y : Fin n → C) (_ : ∀ i, Simple (Y i))
    (_ : HasBiproduct Y), Nonempty (X ≅ ⨁ Y)

/-- Proposition 1.13.6: In a monoidal category where right whiskering preserves
epimorphisms, the tensor product `P ⊗ X` of a projective object `P` with an object
admitting a right dual is projective. -/
theorem Proposition_1_13_6
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

/-- An epimorphism from a biproduct of simples onto a simple object admits a section. -/
theorem epi_section_of_biproduct_simples
    {C : Type u} [Category.{v} C] [Preadditive C] [Abelian C]
    (S : C) [Simple S]
    {n : ℕ} (W : Fin n → C) (hW : ∀ j, Simple (W j)) [HasBiproduct W]
    (e : (⨁ W) ⟶ S) [Epi e] :
    ∃ s : S ⟶ ⨁ W, s ≫ e = 𝟙 S := by

  have he_ne : e ≠ 0 := by
    intro he
    apply Simple.not_isZero S
    rw [IsZero.iff_id_eq_zero]
    subst he
    exact (cancel_epi (0 : (⨁ W) ⟶ S)).mp (by simp)

  have ⟨j, hj⟩ : ∃ j, biproduct.ι W j ≫ e ≠ 0 := by
    by_contra h
    push Not at h
    apply he_ne
    ext k
    simp [h k]

  haveI := hW j
  haveI : IsIso (biproduct.ι W j ≫ e) := isIso_of_hom_simple hj

  exact ⟨inv (biproduct.ι W j ≫ e) ≫ biproduct.ι W j,
    by rw [Category.assoc, IsIso.inv_hom_id]⟩

/-- In a semisimple abelian category, every simple object is projective. -/
theorem simple_projective_of_semisimple
    {C : Type u} [Category.{v} C] [Preadditive C] [Abelian C]
    [IsSemisimpleCategory C]
    (S : C) [Simple S] : Projective S := by
  constructor
  intro E Y f e he

  obtain ⟨n, W, hW, hbp, ⟨φ⟩⟩ := IsSemisimpleCategory.semisimple (C := C) (pullback f e)
  haveI := hbp

  haveI : Epi (pullback.fst f e) := Abelian.epi_pullback_of_epi_g f e

  haveI : Epi (φ.inv ≫ pullback.fst f e) := epi_comp _ _

  obtain ⟨s, hs⟩ := epi_section_of_biproduct_simples S W hW (φ.inv ≫ pullback.fst f e)

  refine ⟨s ≫ φ.inv ≫ pullback.snd f e, ?_⟩

  have cond : pullback.snd f e ≫ e = pullback.fst f e ≫ f := pullback.condition.symm
  rw [Category.assoc, Category.assoc, cond, ← Category.assoc (φ.inv), ← Category.assoc s, hs]
  simp

/-- The biproduct of projective objects is projective. -/
theorem biproduct_projective_of_components
    {C : Type u} [Category.{v} C] [Preadditive C]
    {n : ℕ} (Y : Fin n → C) [HasBiproduct Y]
    (hP : ∀ i, Projective (Y i)) : Projective (⨁ Y) := by
  constructor
  intro E X f e he

  have lift : ∀ i, ∃ g : Y i ⟶ E, g ≫ e = biproduct.ι Y i ≫ f := by
    intro i; exact (hP i).factors (biproduct.ι Y i ≫ f) e
  choose g hg using lift

  exact ⟨biproduct.desc g, by ext i; simp [hg i]⟩

/-- In a semisimple abelian (monoidal) category, every object is projective. -/
theorem semisimple_implies_projective'
    {C : Type u} [Category.{v} C] [Preadditive C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C]
    [IsSemisimpleCategory C] (X : C) : Projective X := by

  obtain ⟨n, Y, hY, hbp, ⟨φ⟩⟩ := IsSemisimpleCategory.semisimple (C := C) X
  haveI := hbp

  have hProj : ∀ i, Projective (Y i) := fun i => by
    haveI := hY i; exact simple_projective_of_semisimple (Y i)

  have hBP : Projective (⨁ Y) := biproduct_projective_of_components Y hProj

  constructor
  intro E Z f e he
  obtain ⟨g', hg'⟩ := hBP.factors (φ.inv ≫ f) e
  exact ⟨φ.hom ≫ g', by
    rw [Category.assoc, hg', ← Category.assoc, φ.hom_inv_id, Category.id_comp]⟩

/-- Converse direction: in a finite-length abelian category, if every object is
projective then the category is semisimple. -/
theorem allProjective_implies_semisimple'
    {C : Type u} [Category.{v} C] [Preadditive C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C]
    (hfl : ∀ (X : C), HasFiniteLength X)
    (h : ∀ (X : C), Projective X) : IsSemisimpleCategory C := by sorry

section Cor_1_13_7

variable (k : Type*) [Field k]
variable (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear k C] [Abelian C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]

/-- Corollary 1.13.7: In a multiring category where every object has a right dual,
the unit object is projective if and only if the category is semisimple. -/
theorem Corollary_1_13_7
    [hMR : MultiringCategory k C]
    [∀ (X : C), HasRightDual X] :
    Projective (𝟙_ C) ↔ IsSemisimpleCategory C := by
  constructor
  ·
    intro hProj


    apply allProjective_implies_semisimple' (hfl := hMR.toLocallyFiniteCategory.hasFiniteLength)
    intro X

    have h1 : Projective (𝟙_ C ⊗ X) :=
      Proposition_1_13_6 hMR.whiskerRight_epi

    exact Projective.of_iso (λ_ X) h1
  ·
    intro hSS
    exact semisimple_implies_projective' (𝟙_ C)

end Cor_1_13_7

end TensorCategories
