/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory

/-- The set of **dyadic rationals** in ℝ, i.e., real numbers of the form `k / 2 ^ n` for some
integer `k` and natural number `n`. This is the dense countable set on which the Kolmogorov
continuity theorem first establishes Hölder continuity. -/
def dyadicRationals : Set ℝ :=
  { x : ℝ | ∃ (k : ℤ) (n : ℕ), x = k / (2 : ℝ) ^ n }

/-- **Kolmogorov continuity theorem.** Suppose `E |X_s - X_t|^β ≤ K |t - s|^{1+α}` where
`α, β > 0`. Then for every `γ < α/β` with `γ > 0`, there exists a modification `Y` of the
process `X` (i.e., `Y t = X t` almost surely for each `t`) such that with probability one
there is a constant `C(ω) > 0` with `|Y(q,ω) - Y(r,ω)| ≤ C |q - r|^γ` for all dyadic rationals
`q, r ∈ [0,1]`. In other words, `Y` has Hölder-continuous sample paths of exponent `γ` on the
dyadic rationals of the unit interval. -/
theorem kolmogorov_continuity_theorem
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℝ → Ω → ℝ}
    {α β K : ℝ} (hα : 0 < α) (hβ : 0 < β) (hK : 0 ≤ K)
    (hkolm : ∀ s t : ℝ, ∫ ω, |X s ω - X t ω| ^ β ∂μ ≤ K * |s - t| ^ (1 + α)) :
    ∀ γ : ℝ, γ < α / β → γ > 0 →
      ∃ (Y : ℝ → Ω → ℝ),
        (∀ t, ∀ᵐ ω ∂μ, Y t ω = X t ω) ∧
        (∀ᵐ ω ∂μ, ∃ C : ℝ, 0 < C ∧
          ∀ q r : ℝ, q ∈ dyadicRationals ∩ Set.Icc 0 1 →
            r ∈ dyadicRationals ∩ Set.Icc 0 1 →
            |Y q ω - Y r ω| ≤ C * |q - r| ^ γ) := by sorry
