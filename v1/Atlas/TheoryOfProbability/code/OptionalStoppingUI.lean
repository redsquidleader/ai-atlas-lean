/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Atlas.TheoryOfProbability.code.OptionalStoppingAlt

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

/-- **General optional stopping theorem (uniform integrability preservation)** (Lecture 29):
let `M` be a uniformly integrable submartingale with respect to a filtration `ℱ` and let `τ` be a
stopping time. Then the stopped process `n ↦ M_{min(τ, n)}` is uniformly integrable. Thin
wrapper around `optional_stopping_alt_ui_preserved`. -/
theorem optional_stopping_uniformly_integrable
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0}
    {M : ℕ → Ω → ℝ} {τ : Ω → ℕ}
    (hmart : Submartingale M ℱ μ)
    (hui : UniformIntegrable M 1 μ)
    (hτ : IsStoppingTime ℱ (fun ω => (τ ω : ℕ∞))) :
    UniformIntegrable (fun n ω => M (min (τ ω) n) ω) 1 μ :=
  optional_stopping_alt_ui_preserved hmart hui hτ

end
