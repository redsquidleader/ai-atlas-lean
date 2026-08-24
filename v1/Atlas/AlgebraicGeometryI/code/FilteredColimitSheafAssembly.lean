/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.NoetherianCoverFinite
import Atlas.AlgebraicGeometryI.code.FilteredColimitFiniteLimits
import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts
import Mathlib.Topology.NoetherianSpace
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

universe w v u t

namespace TopCat.Sheaf

variable {C : Type u} [Category.{v} C]
variable {X : TopCat.{w}}
variable {J : Type t} [Category.{t} J] [IsFiltered J]

/-- Lem 22, Lec 12: on a Noetherian space, a filtered colimit of sheaves is
already a sheaf; equivalently, the underlying presheaf colimit satisfies the
sheaf condition because finite covers and filtered colimits commute. -/
theorem filteredColimit_presheaf_isSheaf
    [NoetherianSpace X]
    [HasColimitsOfShape J C]
    (F : J ⥤ TopCat.Sheaf C X)
    (c : Cocone (F ⋙ sheafToPresheaf (Opens.grothendieckTopology (X : TopCat.{w})) C))
    (hc : IsColimit c) :
    TopCat.Presheaf.IsSheaf c.pt := by


  sorry

end TopCat.Sheaf
