/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.NoetherianSpace
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Filtered.Basic

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe w v u t

namespace TopCat.Sheaf

variable {C : Type u} [Category.{v} C]
variable {X : TopCat.{w}}
variable {J : Type t} [Category.{t} J] [IsFiltered J]

/-- The diagram of sections at a fixed open `U` of a `J`-shaped diagram of sheaves. -/
def sectionsAtU
    (F : J ⥤ TopCat.Sheaf C X) (U : (Opens (X : TopCat.{w}))ᵒᵖ) : J ⥤ C :=
  F ⋙ sheafToPresheaf (Opens.grothendieckTopology (X : TopCat.{w})) C ⋙
    (evaluation (Opens (X : TopCat.{w}))ᵒᵖ C).obj U

/-- On a Noetherian space, the presheaf colimit of a filtered diagram of sheaves
is already a sheaf (Lem 22, Lec 12). -/
theorem filteredColimitPresheafIsSheaf
    {C : Type u} [Category.{v} C]
    {X : TopCat.{w}}
    {J : Type t} [Category.{t} J] [IsFiltered J]
    [NoetherianSpace X]
    [HasColimitsOfShape J C]
    (F : J ⥤ TopCat.Sheaf C X)
    (c : Cocone (F ⋙ sheafToPresheaf (Opens.grothendieckTopology (X : TopCat.{w})) C))
    (hc : IsColimit c) :
    TopCat.Presheaf.IsSheaf c.pt := by sorry

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 80000 in
/-- Over a Noetherian space, sections of the sheaf colimit at any open `U` agree
with the colimit of sections at `U` (Lem 22, Lec 12). -/
def sectionsColimitIso
    [NoetherianSpace X]
    [HasColimitsOfShape J C]
    [HasColimitsOfShape J (TopCat.Sheaf C X)]
    (F : J ⥤ TopCat.Sheaf C X) (U : (Opens (X : TopCat.{w}))ᵒᵖ) :
    (colimit F).1.obj U ≅ colimit (sectionsAtU F U) := by


  have hcreates : CreatesColimit F
      (sheafToPresheaf (Opens.grothendieckTopology (X : TopCat.{w})) C) :=
    Sheaf.createsColimitOfIsSheaf F
      (fun c hc => filteredColimitPresheafIsSheaf F c hc)


  have hpreserves : PreservesColimit F
      (sheafToPresheaf (Opens.grothendieckTopology (X : TopCat.{w})) C) :=
    @preservesColimit_of_createsColimit_and_hasColimit _ _ _ _ _ _ _ _ hcreates inferInstance


  have : HasColimit F := inferInstance
  exact (@preservesColimitIso _ _ _ _
    (sheafToPresheaf (Opens.grothendieckTopology (X : TopCat.{w})) C) _ _ F
    hpreserves this).app U ≪≫
    colimitObjIsoColimitCompEvaluation
      (F ⋙ sheafToPresheaf (Opens.grothendieckTopology (X : TopCat.{w})) C) U

end TopCat.Sheaf
