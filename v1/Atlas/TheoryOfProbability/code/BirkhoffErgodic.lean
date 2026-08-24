/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory Filter Function Set Finset Topology

noncomputable section

variable {α : Type*} {m₀ : MeasurableSpace α} {μ : Measure α}

/-- The sub-σ-algebra of *`T`-invariant measurable sets* on `(α, m₀)`: those
`s ∈ m₀` satisfying `T⁻¹(s) = s`. This is the invariant σ-algebra `𝓘`
appearing on the right-hand side of Birkhoff's ergodic theorem. -/
@[reducible]
def invariantMeasurableSpace (m₀ : MeasurableSpace α) (T : α → α) : MeasurableSpace α where
  MeasurableSet' s := @MeasurableSet α m₀ s ∧ T ⁻¹' s = s
  measurableSet_empty := ⟨MeasurableSet.empty, preimage_empty⟩
  measurableSet_compl s hs := ⟨hs.1.compl, by rw [preimage_compl, hs.2]⟩
  measurableSet_iUnion f hf := ⟨MeasurableSet.iUnion (fun i => (hf i).1),
    by rw [preimage_iUnion]; exact iUnion_congr (fun i => (hf i).2)⟩

/-- **Birkhoff's ergodic theorem (a.s. form).** Let `T` be a measure-preserving
transformation of the probability space `(α, m₀, μ)` and let `g ∈ L¹(μ)`. Then
the time averages
`(1/n) ∑_{m=0}^{n-1} g(T^m ω)`
converge `μ`-almost surely to the conditional expectation `E(g | 𝓘)`, where
`𝓘 = invariantMeasurableSpace m₀ T` is the σ-algebra of `T`-invariant
measurable sets (Durrett, Lecture 33). -/
theorem birkhoff_ergodic_theorem
    {α : Type*} {m₀ : MeasurableSpace α} {μ : Measure α}
    (T : α → α) (g : α → ℝ)
    (hT : MeasurePreserving T μ μ) [IsProbabilityMeasure μ]
    (hg : Integrable g μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => birkhoffAverage ℝ T g n ω) atTop
      (𝓝 (μ[g | invariantMeasurableSpace m₀ T] ω)) := by sorry

/-- **Birkhoff's ergodic theorem (`L¹` form).** Under the same hypotheses as
`birkhoff_ergodic_theorem`, the Birkhoff averages converge to
`E(g | 𝓘)` in `L¹(μ)`: the `L¹` distance
`∫ ‖A_n g - E(g | 𝓘)‖ dμ` tends to `0` as `n → ∞`. -/
theorem birkhoff_ergodic_theorem_L1
    {α : Type*} {m₀ : MeasurableSpace α} {μ : Measure α}
    (T : α → α) (g : α → ℝ)
    (hT : MeasurePreserving T μ μ) [IsProbabilityMeasure μ]
    (hg : Integrable g μ) :
    Tendsto (fun n => ∫ ω, ‖birkhoffAverage ℝ T g n ω - μ[g | invariantMeasurableSpace m₀ T] ω‖ ∂μ)
      atTop (𝓝 0) := by sorry

/-- **Birkhoff's ergodic theorem (combined).** Combines `birkhoff_ergodic_theorem`
and `birkhoff_ergodic_theorem_L1`: the Birkhoff averages of `g ∈ L¹(μ)` under
a measure-preserving `T` converge to `E(g | 𝓘)` both `μ`-almost surely and
in `L¹(μ)`. -/
theorem birkhoff_ergodic_theorem_full
    {α : Type*} {m₀ : MeasurableSpace α} {μ : Measure α}
    (T : α → α) (g : α → ℝ)
    (hT : MeasurePreserving T μ μ) [IsProbabilityMeasure μ]
    (hg : Integrable g μ) :
    (∀ᵐ ω ∂μ, Tendsto (fun n => birkhoffAverage ℝ T g n ω) atTop
      (𝓝 (μ[g | invariantMeasurableSpace m₀ T] ω))) ∧
    (Tendsto (fun n => ∫ ω, ‖birkhoffAverage ℝ T g n ω - μ[g | invariantMeasurableSpace m₀ T] ω‖ ∂μ)
      atTop (𝓝 0)) :=
  ⟨birkhoff_ergodic_theorem T g hT hg, birkhoff_ergodic_theorem_L1 T g hT hg⟩
