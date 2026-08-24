/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Separation.Basic

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace SeparatedHausdorffClassical

/-- Complex points of a scheme `X`: morphisms `Spec ℂ → X`. -/
def complexPoints (X : Scheme) : Type _ :=
  (Spec (CommRingCat.of ℂ)) ⟶ X

/-- The classical (analytic / Hausdorff) topology on the complex points of
a reduced, locally-finite-type `ℂ`-scheme. -/
noncomputable def classicalTopology (X : Scheme) (f : X ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType f] [IsReduced X] :
    TopologicalSpace (complexPoints X) := by sorry

/-- A reduced, locally-finite-type `ℂ`-scheme is separated iff its complex
points form a Hausdorff space in the classical topology. -/
theorem separated_iff_hausdorff_classical
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType f] [IsReduced X] :
    X.IsSeparated ↔ @T2Space (complexPoints X) (classicalTopology X f) := by sorry

end SeparatedHausdorffClassical
