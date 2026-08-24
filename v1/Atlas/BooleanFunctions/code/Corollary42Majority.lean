/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Majority

open Finset BigOperators Real Filter

namespace BooleanFourier

theorem noiseSensitivity_majority_limit_pos
    (δ : ℝ) (hδ_pos : 0 < δ) :
    0 < (1 / Real.pi) * Real.arccos (1 - 2 * δ) := by
  apply mul_pos
  · exact div_pos one_pos Real.pi_pos
  · rw [Real.arccos_pos]
    linarith

theorem majority_noiseSensitive
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1 / 2) :
    Filter.Tendsto
      (fun k => noiseSensitivityReal δ (majorityFn (2 * k + 1)))
      Filter.atTop
      (nhds ((1 / Real.pi) * Real.arccos (1 - 2 * δ)))
    ∧ 0 < (1 / Real.pi) * Real.arccos (1 - 2 * δ) :=
  ⟨noiseSensitivity_majority_tendsto δ hδ_pos hδ_le,
   noiseSensitivity_majority_limit_pos δ hδ_pos⟩

theorem majority_noiseSensitivity_eventually_pos
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1 / 2) :
    ∀ᶠ k in Filter.atTop,
      0 < noiseSensitivityReal δ (majorityFn (2 * k + 1)) := by
  have hlim := noiseSensitivity_majority_tendsto δ hδ_pos hδ_le
  have hpos := noiseSensitivity_majority_limit_pos δ hδ_pos
  exact hlim.eventually (eventually_gt_nhds hpos)

end BooleanFourier
