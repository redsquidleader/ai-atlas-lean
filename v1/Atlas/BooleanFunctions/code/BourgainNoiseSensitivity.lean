/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.NoiseSensitivity
import Atlas.BooleanFunctions.code.Talagrand

open Finset BigOperators

namespace BooleanFourier


theorem bourgain_noise_sensitivity :
    ∃ c : ℝ, c > 0 ∧ ∀ (n : ℕ) (δ τ : ℝ) (f : (Fin n → Bool) → Bool),
      0 < δ → δ ≤ 1 / 2 →
      0 < τ → τ < 1 →
      (∀ i : Fin n, fourierInfluence (fun x => boolToReal (f x)) i ≤ τ) →
      noiseSensitivity δ f ≥
        c * variance (fun x => boolToReal (f x)) * min (δ * Real.log (1 / τ)) 1 := by sorry

end BooleanFourier
