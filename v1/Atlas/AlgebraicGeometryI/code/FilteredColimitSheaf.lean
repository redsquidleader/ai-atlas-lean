/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.NoetherianColimit

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w v u t

/-- Lem 22, Lec 12: a filtered colimit of sheaves on a Noetherian space is a
sheaf — the underlying presheaf colimit already satisfies the sheaf condition. -/
theorem lemma22_filtered_colimit_sheaf_noetherian
    {C : Type u} [Category.{v} C]
    {X : TopCat.{w}}
    {J : Type t} [Category.{t} J] [IsFiltered J]
    [NoetherianSpace X]
    [HasColimitsOfShape J C]
    (F : J ⥤ TopCat.Sheaf C X)
    (c : Cocone (F ⋙ sheafToPresheaf (Opens.grothendieckTopology (X : TopCat.{w})) C))
    (hc : IsColimit c) :
    TopCat.Presheaf.IsSheaf c.pt :=
  TopCat.Sheaf.filteredColimitPresheafIsSheaf F c hc
