/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.FrobeniusPerron

set_option maxHeartbeats 400000

open Real

namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {R : FusionRing ι}

/-- Corollary 1.45.16: Let A be a fusion ring and X a basis element. If FPdim(X) < 2, then
FPdim(X) = 2 cos(pi/n) for some integer n >= 3. -/
theorem corollary_1_45_16_fpdim_cosine (fpd : R.FPdimData) (i : ι)
    (hi : fpd.d i < 2) :
    ∃ n : ℕ, n ≥ 3 ∧ fpd.d i = 2 * Real.cos (Real.pi / (n : ℝ)) :=
  fpd.FPdim_lt_two_eq_cos i hi

end FusionRing
