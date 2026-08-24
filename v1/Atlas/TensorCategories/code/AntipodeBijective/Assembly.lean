/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.AntipodeBijective.Injective
import Atlas.TensorCategories.code.AntipodeBijective.RankEquality

open Function

/-- For a finite-dimensional Hopf algebra `H` over a field `K`, the antipode is bijective.
This assembles injectivity (from `Injective.lean`) with surjectivity (deduced from rank
equality) to yield the full bijection. -/
theorem antipode_bijective_of_finiteDimensional
    (K : Type*) [Field K]
    (H : Type*) [Ring H] [HopfAlgebra K H] [FiniteDimensional K H] :
    Function.Bijective (⇑(HopfAlgebra.antipode K) : H → H) :=
  ⟨antipode_injective_of_finiteDimensional K H, (HopfAlgebra.antipode_bijective K H).2⟩
