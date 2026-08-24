/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.NoetherianSpace
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Filtered.Basic

universe w v u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

/-- Lemma 22 (Lec 6/12): on a Noetherian topological space, the colimit of a filtered diagram of
sheaves, taken in the presheaf category, is itself a sheaf. -/
theorem presheaf_colimit_isSheaf_of_noetherian
    {X : Type w} [TopologicalSpace X] [NoetherianSpace X]
    {C : Type u} [Category.{v} C]
    {K : Type*} [SmallCategory K] [IsFiltered K]
    (F : K ⥤ Sheaf (Opens.grothendieckTopology X) C)
    (E : Cocone (F ⋙ sheafToPresheaf (Opens.grothendieckTopology X) C))
    (hE : IsColimit E) :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) E.pt := by
  sorry

/-- On a Noetherian space, the sheafification functor `Sheaf → Presheaf` creates filtered
colimits. -/
@[implicit_reducible]
noncomputable def sheafToPresheaf_createsFilteredColimits_of_noetherian
    {X : Type w} [TopologicalSpace X] [NoetherianSpace X]
    {C : Type u} [Category.{v} C]
    {K : Type*} [SmallCategory K] [IsFiltered K]
    (F : K ⥤ Sheaf (Opens.grothendieckTopology X) C) :
    CreatesColimit F (sheafToPresheaf (Opens.grothendieckTopology X) C) :=
  Sheaf.createsColimitOfIsSheaf F
    (fun c hc => presheaf_colimit_isSheaf_of_noetherian F c hc)
