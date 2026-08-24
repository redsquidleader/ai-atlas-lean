/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Atlas.TensorCategories.code.FiniteTensorCategory
import Atlas.TensorCategories.code.UnitSemisimplicity
import Atlas.TensorCategories.code.HigherDerivation

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category Limits

universe v u w

noncomputable section

namespace TensorCategories

section Ext1Def

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The predicate `Ext¹(X, Y) = 0` expressed as: every short exact sequence
`0 → Y → V → X → 0` splits. -/
def Ext1Vanishes (X Y : C) : Prop :=
  ∀ (V : C) (f : Y ⟶ V) (g : V ⟶ X) (hfg : f ≫ g = 0),
    (ShortComplex.mk f g hfg).ShortExact → Nonempty (ShortComplex.mk f g hfg).Splitting

/-- If `Ext¹(X, Y) = 0`, then any short exact sequence `0 → Y → V → X → 0` admits a
section `s : X ⟶ V` of `g`. -/
theorem Ext1Vanishes.exists_section {X Y : C} (h : Ext1Vanishes X Y)
    {V : C} {f : Y ⟶ V} {g : V ⟶ X} {hfg : f ≫ g = 0}
    (hse : (ShortComplex.mk f g hfg).ShortExact) :
    ∃ s : X ⟶ V, s ≫ g = 𝟙 X := by
  obtain ⟨spl⟩ := h V f g hfg hse
  exact ⟨spl.s, spl.s_g⟩

/-- If `Ext¹(X, Y) = 0`, then any short exact sequence `0 → Y → V → X → 0` admits a
retraction `r : V ⟶ Y` of `f`. -/
theorem Ext1Vanishes.exists_retraction {X Y : C} (h : Ext1Vanishes X Y)
    {V : C} {f : Y ⟶ V} {g : V ⟶ X} {hfg : f ≫ g = 0}
    (hse : (ShortComplex.mk f g hfg).ShortExact) :
    ∃ r : V ⟶ Y, f ≫ r = 𝟙 Y := by
  obtain ⟨spl⟩ := h V f g hfg hse
  exact ⟨spl.r, spl.f_r⟩

/-- If `Ext¹(X, Y) = 0`, then any short exact sequence `0 → Y → V → X → 0` admits both
a retraction `r` of `f` and a section `s` of `g` satisfying the bi-product identity. -/
theorem Ext1Vanishes.full_splitting {X Y : C} (h : Ext1Vanishes X Y)
    {V : C} {f : Y ⟶ V} {g : V ⟶ X} {hfg : f ≫ g = 0}
    (hse : (ShortComplex.mk f g hfg).ShortExact) :
    ∃ (r : V ⟶ Y) (s : X ⟶ V), f ≫ r = 𝟙 Y ∧ s ≫ g = 𝟙 X ∧ r ≫ f + g ≫ s = 𝟙 V := by
  obtain ⟨spl⟩ := h V f g hfg hse
  exact ⟨spl.r, spl.s, spl.f_r, spl.s_g, spl.id⟩

/-- Version of the splitting consequence of `Ext1Vanishes` phrased for an arbitrary
short complex whose endpoints match `X` and `Y`. -/
theorem Ext1Vanishes.splitting {X Y : C} (h : Ext1Vanishes X Y)
    {S : ShortComplex C} (hse : S.ShortExact) (hX : S.X₃ = X) (hY : S.X₁ = Y) :
    Nonempty S.Splitting := by
  subst hX; subst hY
  exact h S.X₂ S.f S.g S.zero hse

end Ext1Def

/-- A `k`-linear abelian monoidal category that has enough projectives and finite-
dimensional Hom spaces; this is the underlying ring-category structure used in EGNO. -/
class FiniteRingCategory (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    extends MonoidalCategory C, Abelian C, Linear k C where
  enoughProj : EnoughProjectives C
  homFiniteDim : ∀ (X Y : C), FiniteDimensional k (X ⟶ Y)

section FiniteRingCategoryLemmas

variable (k : Type w) [Field k] (C : Type u) [Category.{v} C] [FiniteRingCategory k C]

include k in
/-- A `FiniteRingCategory` has enough projectives. -/
theorem FiniteRingCategory.enough_projectives : EnoughProjectives C :=
  FiniteRingCategory.enoughProj k

/-- Hom spaces in a `FiniteRingCategory` are finite-dimensional over the base field. -/
theorem FiniteRingCategory.hom_finite_dimensional (X Y : C) :
    FiniteDimensional k (X ⟶ Y) :=
  FiniteRingCategory.homFiniteDim X Y

end FiniteRingCategoryLemmas

/-- Every finite tensor category over `k` carries the underlying structure of a
`FiniteRingCategory` over `k`. -/
instance (priority := 100) FiniteRingCategory.ofFiniteTensorCategory
    (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    [CategoryTheory.FiniteTensorCategory k C] : FiniteRingCategory k C where
  enoughProj := CategoryTheory.FiniteTensorCategory.enoughProj k
  homFiniteDim := CategoryTheory.FiniteTensorCategory.homFiniteDim

section Ext1UnitVanishing

/-- Existence hypothesis: from a non-split extension of `𝟙_ C` by `𝟙_ C` one can build a
higher derivation system on some finite-dimensional `k`-algebra with nonzero first
coefficient `χ 1`. -/
class HasDerivationFromExtension (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    [FiniteRingCategory k C] [Simple (𝟙_ C)] : Prop where
  higher_derivation_from_nonsplit_ext :
    ∀ (V : C) (f : 𝟙_ C ⟶ V) (g : V ⟶ 𝟙_ C) (hfg : f ≫ g = 0),
      (ShortComplex.mk f g hfg).ShortExact →
      ¬ Nonempty (ShortComplex.mk f g hfg).Splitting →
      ∃ (A : Type w) (_ : Ring A) (_ : Algebra k A) (_ : FiniteDimensional k A)
        (ε : A →ₐ[k] k) (hds : HigherDerivationSystem k A ε),
        hds.χ 1 ≠ 0

/-- From a non-split extension of `𝟙_ C` by `𝟙_ C` one obtains a higher derivation
system on some finite-dimensional `k`-algebra whose first coefficient is nonzero. -/
theorem derivation_from_nonsplit_ext
    (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    [FiniteRingCategory k C] [Simple (𝟙_ C)]
    (V : C) (f : 𝟙_ C ⟶ V) (g : V ⟶ 𝟙_ C) (hfg : f ≫ g = 0)
    (hse : (ShortComplex.mk f g hfg).ShortExact)
    (hns : ¬ Nonempty (ShortComplex.mk f g hfg).Splitting) :
    ∃ (A : Type w) (_ : Ring A) (_ : Algebra k A) (_ : FiniteDimensional k A)
      (ε : A →ₐ[k] k) (hds : HigherDerivationSystem k A ε),
      hds.χ 1 ≠ 0 := by
  sorry

/-- The class `HasDerivationFromExtension` is automatically satisfied in any finite ring
category with a simple unit, via `derivation_from_nonsplit_ext`. -/
instance instHasDerivationFromExtension (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    [FiniteRingCategory k C] [Simple (𝟙_ C)] : HasDerivationFromExtension k C where
  higher_derivation_from_nonsplit_ext := fun V f g hfg hse hns =>
    derivation_from_nonsplit_ext k C V f g hfg hse hns

/-- In characteristic zero, `Ext¹(𝟙_ C, 𝟙_ C)` vanishes in any finite ring category with
simple unit, by contradiction with the higher derivation construction. -/
theorem ext1Vanishes_unit_unit_of_charZero
    (k : Type w) [Field k] [CharZero k]
    (C : Type u) [Category.{v} C] [FiniteRingCategory k C]
    [Simple (𝟙_ C)]
    [HasDerivationFromExtension k C]
    [HasHigherDerivationContradiction k] :
    Ext1Vanishes (𝟙_ C) (𝟙_ C) := by
  intro V f g hfg hse
  by_contra h_not_split

  obtain ⟨A, instR, instA, instFD, ε, hds, hne⟩ :=
    HasDerivationFromExtension.higher_derivation_from_nonsplit_ext (k := k) V f g hfg hse
      (fun ⟨s⟩ => h_not_split ⟨s⟩)

  exact hne (@HasHigherDerivationContradiction.higher_derivation_vanishes
    k _ _ _ A instR instA instFD ε hds)

end Ext1UnitVanishing

end TensorCategories
