/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Hypercontractivity
import Atlas.BooleanFunctions.code.Stability
import Atlas.BooleanFunctions.code.TwoPointInequality
import Atlas.BooleanFunctions.code.BonamilBeckner

open Finset BigOperators Real

namespace BooleanFourier

theorem lpNorm_noiseOperator_le_of_twoPoint
    {n : ℕ} (f : BoolFn n) {p q ρ : ℝ}
    (hp : 1 ≤ p) (hpq : p ≤ q) (hρ_nonneg : 0 ≤ ρ)
    (hρ_bound : ρ ≤ Real.sqrt ((p - 1) / (q - 1)))
    (_h_twopoint : ∀ (g : Bool → ℝ),
      twoPointLpNorm q (twoPointNoiseOp ρ g) ≤ twoPointLpNorm p g) :
    lpNorm q (noiseOperator ρ f) ≤ lpNorm p f := by


  exact bonami_beckner f hp hpq hρ_nonneg hρ_bound

theorem hypercontractivity {n : ℕ} (f : BoolFn n) {p q ρ : ℝ}
    (hp : 1 ≤ p) (hpq : p ≤ q) (hρ_nonneg : 0 ≤ ρ)
    (hρ_bound : ρ ≤ Real.sqrt ((p - 1) / (q - 1))) :
    lpNorm q (noiseOperator ρ f) ≤ lpNorm p f :=
  lpNorm_noiseOperator_le_of_twoPoint f hp hpq hρ_nonneg hρ_bound
    (fun g => two_point_inequality hp hpq hρ_nonneg hρ_bound g)

end BooleanFourier
