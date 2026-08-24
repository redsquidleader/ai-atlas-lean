/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Atlas.TheoryOfProbability.code.DomainAttraction

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology ENNReal NNReal

noncomputable section

set_option maxHeartbeats 3200000

namespace ProbabilityTheory

/-- For a regularly varying function `f` of index `-α` with `α > 0` that is eventually
non-increasing, there exists a sequence `a : ℕ → ℝ` of positive reals (a "generalized
inverse") such that `n · f (a n) → 1` as `n → ∞`. This is a standard tool in the
analysis of domains of attraction for stable laws. -/
theorem regularlyVarying_generalized_inverse (f : ℝ → ℝ) (α : ℝ)
    (hα : 0 < α)
    (hf : IsRegularlyVarying f (-α))
    (hdecr : ∀ᶠ x in atTop, ∀ y, x ≤ y → f y ≤ f x) :
    ∃ a : ℕ → ℝ, (∀ n, 0 < a n) ∧
      Tendsto (fun n => ↑n * f (a n)) atTop (𝓝 1) := by sorry

/-- Asymptotic for the truncated second moment of a distribution with regularly varying
tails of index `-α`, `0 < α < 2`. The ratio of `∫_{[-x, x]} y² dμ` to
`x² · P(|X| > x)` tends to `2 / (2 - α)` as `x → ∞`. This is a key estimate in the
proof of the convergence to stable laws. -/
theorem regularlyVarying_truncated_moment
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (α : ℝ) (hα₁ : 0 < α) (hα₂ : α < 2)
    (hRV : IsRegularlyVarying (combinedTail μ) (-α)) :
    Tendsto (fun x => (∫ y in Set.Icc (-x) x, y ^ 2 ∂μ) /
      (x ^ 2 * combinedTail μ x)) atTop (𝓝 (2 / (2 - α))) := by sorry

/-- Asymptotic for the integral `∫_{(0, c·x]} y dμ` of a distribution with regularly
varying tails of index `-α`, balanced with parameter `p`, normalized by
`x · P(|X| > x)`. The limit equals `p · α · c^{1-α} / (1 - α)`, used in establishing
domains of attraction to stable laws when `α ≠ 1`. -/
theorem regularlyVarying_tail_integral
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (α : ℝ) (hα₁ : 0 < α) (hα₂ : α < 2) (hα_ne_1 : α ≠ 1)
    (p : ℝ) (hTB : HasTailBalance μ p)
    (hRV : IsRegularlyVarying (combinedTail μ) (-α))
    (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x => (∫ y in Set.Ioc 0 (c * x), y ∂μ) /
      (x * combinedTail μ x)) atTop (𝓝 (p * α * c ^ (1 - α) / (1 - α))) := by sorry

end ProbabilityTheory
