/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.Topology.Separation.Basic
import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace SeparatedHausdorff

/-- Complex points of a scheme `X`: morphisms `Spec ℂ → X`. -/
def complexPoints (X : Scheme) : Type _ :=
  (Spec (CommRingCat.of ℂ)) ⟶ X

/-- Classical (analytic) topology on the complex points of a reduced,
locally-finite-type `ℂ`-scheme. -/
noncomputable def classicalTopology (X : Scheme) (f : X ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType f] [AlgebraicGeometry.IsReduced X] :
    TopologicalSpace (complexPoints X) := by sorry

/-- Forward direction of the separated-iff-Hausdorff equivalence: if `X` is
separated, then the diagonal in `X(ℂ) × X(ℂ)` is closed for the classical
topology. -/
theorem separated_imp_diagonal_closed
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType f] [AlgebraicGeometry.IsReduced X] :
    X.IsSeparated →
    @IsClosed (complexPoints X × complexPoints X)
      (@instTopologicalSpaceProd (complexPoints X) (complexPoints X)
        (classicalTopology X f) (classicalTopology X f))
      (Set.diagonal (complexPoints X)) := by sorry

/-- Reverse direction: closedness of the diagonal in the classical topology
implies `X` is separated as a scheme. -/
theorem diagonal_closed_imp_separated
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType f] [AlgebraicGeometry.IsReduced X] :
    @IsClosed (complexPoints X × complexPoints X)
      (@instTopologicalSpaceProd (complexPoints X) (complexPoints X)
        (classicalTopology X f) (classicalTopology X f))
      (Set.diagonal (complexPoints X)) →
    X.IsSeparated := by sorry

/-- `X` is separated as a `ℂ`-scheme iff `X(ℂ)` is Hausdorff for the
classical topology. -/
theorem separated_iff_hausdorff_classical
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType f] [AlgebraicGeometry.IsReduced X] :
    X.IsSeparated ↔ @T2Space (complexPoints X) (classicalTopology X f) := by
  rw [@t2_iff_isClosed_diagonal (complexPoints X) (classicalTopology X f)]
  exact ⟨separated_imp_diagonal_closed f, diagonal_closed_imp_separated f⟩

/-- Goal 7.1: equivalence between scheme-theoretic separatedness and the
Hausdorff property of complex points (restated under the goal name). -/
theorem goal71_separated_iff_hausdorff
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType f] [AlgebraicGeometry.IsReduced X] :
    X.IsSeparated ↔ @T2Space (complexPoints X) (classicalTopology X f) :=
  separated_iff_hausdorff_classical f

end SeparatedHausdorff
