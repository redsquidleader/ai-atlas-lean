/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfProbability.code.StoppingTimeContinuous
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory MeasurableSpace
open scoped NNReal ENNReal

noncomputable section

namespace BrownianMotion

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The process obtained from `B` by shifting time by the stopping time `T` and
recentering at `B(T)`: `t ↦ B(T + t) - B(T)`. -/
def stoppedShiftedProcess (B : ℝ≥0 → Ω → ℝ) (T : Ω → ℝ≥0∞) : ℝ≥0 → Ω → ℝ :=
  fun t ω => B ((T ω).toNNReal + t) ω - B ((T ω).toNNReal) ω

end BrownianMotion

open BrownianMotion in
/-- **Strong Markov property for Brownian motion** (Lecture 39). Given a real-valued
Brownian motion `B` adapted to `ℱ` with `B 0 = 0`, independent Gaussian increments and
continuous paths, and an almost-surely finite stopping time `T`, the shifted/recentered
process `t ↦ B(T + t) - B(T)` is independent of `ℱ_T`, starts at `0`, has the same
Gaussian increment distribution as `B`, and has continuous paths almost surely. -/
theorem strong_markov_property_bm {Ω : Type*} {m : MeasurableSpace Ω}
    {B : ℝ≥0 → Ω → ℝ} {ℱ : Filtration ℝ≥0 m} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (hB_zero : ∀ᵐ ω ∂μ, B 0 ω = 0)
    (hB_indep : ∀ (s t : ℝ≥0), s ≤ t →
      Indep (ℱ s) (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) μ)
    (hB_cont : ∀ᵐ ω ∂μ, Continuous (fun t => B t ω))
    (T : Ω → ℝ≥0∞)
    (hT_stop : IsStoppingTimeContinuous ℱ T)
    (hT_fin : ∀ᵐ ω ∂μ, T ω < ⊤) :


    (∀ (t : ℝ≥0), Indep (hT_stop.measurableSpace)
        (MeasurableSpace.comap (stoppedShiftedProcess B T t) inferInstance) μ) ∧
    (∀ᵐ ω ∂μ, (stoppedShiftedProcess B T) 0 ω = 0) ∧
    (∀ (s t : ℝ≥0), s ≤ t →
      Measure.map (fun ω => stoppedShiftedProcess B T t ω -
        stoppedShiftedProcess B T s ω) μ =
      gaussianReal 0 (t - s)) ∧
    (∀ᵐ ω ∂μ, Continuous (fun t => stoppedShiftedProcess B T t ω)) := by sorry
