/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Influence
import Atlas.BooleanFunctions.code.Monotone
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Finset Real

namespace BooleanFourier

noncomputable def pBiasedProb {n : ℕ} (f : (Fin n → Bool) → Bool) (p : ℝ) : ℝ :=
  ∑ x : Fin n → Bool,
    (if f x = true then 1 else 0) *
    (∏ i : Fin n, if x i = true then p else (1 - p))

noncomputable def thresholdValue {n : ℕ} (f : (Fin n → Bool) → Bool) (ε : ℝ) : ℝ :=
  Classical.epsilon (fun p => 0 ≤ p ∧ p ≤ 1 ∧ pBiasedProb f p = ε)


theorem threshold_width_log_ratio
    {n : ℕ} (f : (Fin n → Bool) → Bool)
    (hmon : IsMonotone f)
    (hI : totalInfluence f > 0)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1/2) :
    thresholdValue f (1 - ε) - thresholdValue f ε ≤
      Real.log ((1 - ε) / ε) / (2 * totalInfluence f) := by sorry

end BooleanFourier
