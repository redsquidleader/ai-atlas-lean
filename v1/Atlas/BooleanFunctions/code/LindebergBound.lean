/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.LindebergHybrid

noncomputable section

open MeasureTheory Measure Finset BigOperators

namespace BooleanFourier


theorem lindeberg_per_step_bound {n : ℕ} (f : (Fin n → Bool) → ℝ) (d : ℕ)
    (hdeg : degree f ≤ d) (Ψ : ℝ → ℝ) (hΨ : IsC3Bounded Ψ) (k : Fin n) :
    |hybridExpectation f Ψ k.val - hybridExpectation f Ψ (k.val + 1)| ≤
      (1 / 2) * (2 : ℝ) ^ ((3 : ℝ) * ↑d / 2) * hΨ.thirdDerivBound *
        (fourierInfluence f k) ^ ((3 : ℝ) / 2) := by sorry

end BooleanFourier

end
