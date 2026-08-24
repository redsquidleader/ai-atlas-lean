/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_11
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Normed.Group.Constructions

open MeasureTheory ProbabilityTheory

noncomputable section

/-- **Problem 1.1 (weighted sums of sub-exponentials).** For independent
sub-exponential variables `X₁,…,Xₙ` with parameter `λ`, there is a constant
`C > 0` such that for any coefficients `a` and any `t > 0`,
`P(|∑ aᵢXᵢ| > t) ≤ 2 exp(-C · min(t² / (λ² ∑ aᵢ²), t / (λ ‖a‖)))`. -/
theorem problem_1_1_weighted_subexponential
    {n : ℕ} {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω} (hP : IsProbabilityMeasure μ)
    {X : Fin n → Ω → ℝ} {lambda : ℝ}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_subexp : ∀ i, IsSubExponential (μ := μ) (X i) lambda)
    (hX_indep : iIndepFun (β := fun (_ : Fin n) => ℝ) X μ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Fin n → ℝ) (t : ℝ), 0 < t →
        (μ {ω | |∑ i, a i * X i ω| > t}).toReal ≤
          2 * Real.exp (-C * min (t ^ 2 / (lambda ^ 2 * ∑ i, a i ^ 2))
                                  (t / (lambda * ‖a‖))) := by sorry

end
