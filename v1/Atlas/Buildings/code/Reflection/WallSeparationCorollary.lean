/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Reflection.WallSeparation

open scoped InnerProductSpace
open Set

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace HyperplaneArrangement

variable {arr : HyperplaneArrangement E}

/-- *Corollary of the wall-separation theorem*: for distinct chambers $C, D$ in a locally
finite arrangement, there exists a wall $η$ of $C$ that strictly separates $C$ from $D$. This
is a cleaner repackaging of `wall_separates_distinct_chambers` with the inner membership
discarded. -/
theorem wall_of_C_separates_distinct_chambers (C D : arr.Chamber) (hne : C.set ≠ D.set)
    (hlf : arr.IsLocallyFinite) :
    ∃ η, ∃ hη : η ∈ arr.hyperplanes,
      η.IsWall C.set ∧ SeparatesChambers η hη C D := by
  obtain ⟨η, _, hη, hwall, hsep⟩ := wall_separates_distinct_chambers C D hne hlf
  exact ⟨η, hη, hwall, hsep⟩

end HyperplaneArrangement
