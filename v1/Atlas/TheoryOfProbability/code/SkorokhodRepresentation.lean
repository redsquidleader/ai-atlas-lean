/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

open scoped Topology

/-- **Skorokhod representation theorem.** If a sequence of probability measures `μₙ`
on `ℝ` converges weakly to a probability measure `μ`, then there exist random
variables `Yₙ` and `Z` on a common probability space `(Ω, P)` such that each `Yₙ`
has law `μₙ`, `Z` has law `μ`, and `Yₙ → Z` almost surely. This is the standard
device for converting weak convergence into a.s. convergence. -/
theorem skorokhod_representation
    {μs : ℕ → MeasureTheory.ProbabilityMeasure ℝ}
    {μ : MeasureTheory.ProbabilityMeasure ℝ}
    (hconv : Filter.Tendsto μs Filter.atTop (𝓝 μ)) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : MeasureTheory.Measure Ω)
      (_ : MeasureTheory.IsProbabilityMeasure P)
      (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ),
      (∀ n, Measurable (Y n)) ∧ Measurable Z ∧
      (∀ n, P.map (Y n) = (μs n : MeasureTheory.Measure ℝ)) ∧
      P.map Z = (μ : MeasureTheory.Measure ℝ) ∧
      ∀ᵐ ω ∂P, Filter.Tendsto (fun n ↦ Y n ω) Filter.atTop (𝓝 (Z ω)) := by sorry
