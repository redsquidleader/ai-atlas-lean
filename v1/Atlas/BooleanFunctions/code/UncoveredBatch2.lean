/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.NoiseStability
import Atlas.BooleanFunctions.code.Influence
import Atlas.BooleanFunctions.code.Monotone
import Atlas.BooleanFunctions.code.InfluenceFourier

open Finset BigOperators

namespace BooleanFourier

theorem low_degree_concentration_hypercontractive :
    ∀ {n : ℕ} (f : (Fin n → Bool) → ℝ) (d : ℕ)
    (hdeg : degree f ≤ d),
    (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, (f x) ^ 4 ≤
      (9 : ℝ) ^ d * ((1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, (f x) ^ 2) ^ 2 := by sorry

end BooleanFourier
