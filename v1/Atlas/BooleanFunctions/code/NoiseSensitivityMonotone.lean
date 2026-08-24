/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Sensitivity
import Atlas.BooleanFunctions.code.Talagrand

open Finset BigOperators

namespace BooleanFourier


theorem expected_sqrt_sensitivity_lower_bound
    {n : ℕ} (f : (Fin n → Bool) → Bool) :
    (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, Real.sqrt (↑(sensitivity f x)) ≥
      (1 / 2) * variance (fun x => boolToReal (f x)) := by sorry

end BooleanFourier
