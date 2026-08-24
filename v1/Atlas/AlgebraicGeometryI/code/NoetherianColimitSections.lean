/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import Mathlib.CategoryTheory.Filtered.Basic

universe u v w

open CategoryTheory Limits TopologicalSpace Opposite

/-- The functor sending a sheaf to its sections over a fixed open `U`. -/
noncomputable def TopCat.Sheaf.sectionsAt
    (C : Type u) [Category.{v} C] {X : TopCat.{w}} (U : Opens X) :
    TopCat.Sheaf C X ⥤ C :=
  TopCat.Sheaf.forget C X ⋙ (evaluation (Opens X)ᵒᵖ C).obj (op U)

/-- On a Noetherian space, the `sectionsAt U` functor preserves filtered
colimits (Lem 22, Lec 12). -/
theorem noetherianSpace_sectionsAt_preservesFilteredColimits
    (C : Type u) [Category.{v} C] {X : TopCat.{w}}
    [NoetherianSpace X]
    (U : Opens X) :
    PreservesFilteredColimits (TopCat.Sheaf.sectionsAt C U) := by
  sorry

/-- Over a Noetherian space, sections of a filtered colimit of sheaves at `U`
agree with the colimit of the sections at `U`. -/
noncomputable def noetherianSpace_colimit_sections_iso
    (C : Type u) [Category.{v} C] {X : TopCat.{w}}
    [NoetherianSpace X]
    (U : Opens X)
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ TopCat.Sheaf C X)
    [HasColimit F]
    [HasColimit (F ⋙ TopCat.Sheaf.sectionsAt C U)] :
    (TopCat.Sheaf.sectionsAt C U).obj (colimit F)
      ≅ colimit (F ⋙ TopCat.Sheaf.sectionsAt C U) := by
  haveI := noetherianSpace_sectionsAt_preservesFilteredColimits C U
  exact preservesColimitIso (TopCat.Sheaf.sectionsAt C U) F
