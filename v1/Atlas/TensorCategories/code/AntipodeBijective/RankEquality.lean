/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.HopfAlgebra
import Mathlib.LinearAlgebra.Dimension.LinearMap

open Function

namespace HopfAlgebra

/-- For a finite-dimensional Hopf algebra `H` over a field `K`, the rank of the antipode
viewed as a `K`-linear map `H →ₗ[K] H` equals `Module.rank K H`. -/
theorem antipode_rank_eq_dim
    (K : Type*) [Field K]
    (H : Type*) [Ring H] [HopfAlgebra K H] [FiniteDimensional K H] :
    LinearMap.rank (HopfAlgebra.antipode K : H →ₗ[K] H) = Module.rank K H :=
  rank_range_of_surjective _ (HopfAlgebra.antipode_bijective K H).2

end HopfAlgebra
