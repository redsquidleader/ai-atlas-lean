/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Topology.Basic
import Mathlib.AlgebraicGeometry.FunctionField

noncomputable section

open AlgebraicGeometry IsLocalRing

universe u

/-- The smooth locus of a scheme: points where the local ring is regular. -/
def Scheme.smoothLocus' (X : Scheme.{u}) [IsLocallyNoetherian X] : Set X :=
  {x : X | IsRegularLocalRing (X.presheaf.stalk x)}

/-- Membership in the smooth locus is equivalent to the stalk being a regular local ring. -/
theorem Scheme.mem_smoothLocus'_iff (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    x ∈ Scheme.smoothLocus' X ↔ IsRegularLocalRing (X.presheaf.stalk x) :=
  Iff.rfl

/-- The smooth locus of a reduced irreducible scheme is open. -/
theorem Scheme.smoothLocus'_isOpen (X : Scheme.{u}) [IsLocallyNoetherian X]
    [IsReduced X] [IrreducibleSpace X] [Nonempty X] :
    IsOpen (Scheme.smoothLocus' X) := by sorry

/-- Proposition 30: the smooth locus of a reduced irreducible scheme is open, dense,
and nonempty (containing the generic point). -/
theorem Scheme.proposition30_smooth_locus_dense_open
    (X : Scheme.{u}) [IsLocallyNoetherian X]
    [IsReduced X] [IrreducibleSpace X] [Nonempty X] :
    IsOpen (Scheme.smoothLocus' X) ∧
    Dense (Scheme.smoothLocus' X) ∧
    Set.Nonempty (Scheme.smoothLocus' X) := by
  have hI : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X

  have hOpen : IsOpen (Scheme.smoothLocus' X) := Scheme.smoothLocus'_isOpen X

  have hGeneric : genericPoint X ∈ Scheme.smoothLocus' X := by
    show IsRegularLocalRing (X.presheaf.stalk (genericPoint X))
    exact inferInstance

  have hNe : Set.Nonempty (Scheme.smoothLocus' X) := ⟨genericPoint X, hGeneric⟩

  have hDense : Dense (Scheme.smoothLocus' X) := hOpen.dense hNe
  exact ⟨hOpen, hDense, hNe⟩

end
