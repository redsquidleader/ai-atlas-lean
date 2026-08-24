/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2

open MeasureTheory Real

noncomputable section

/-- **Problem 1.3 (Integrability of a supremum of sub-Gaussians with
decaying variance).** If `Xᵢ` (for `i ≥ 2`) are sub-Gaussian with variance
proxy `C / √(log i)`, then `sup_i X_i` is integrable. -/
theorem problem_1_3_sup_decaying_variance :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (X : ℕ → Ω → ℝ),
        (∀ i : ℕ, 2 ≤ i →
          IsSubGaussian (X i) (C / Real.sqrt (Real.log (i : ℝ))) μ) →
        (∀ i : ℕ, 2 ≤ i → Measurable (X i)) →
        (∀ ω : Ω, BddAbove (Set.range (fun (i : {n : ℕ // 2 ≤ n}) => X i.val ω))) →
        Integrable (fun ω => ⨆ (i : {n : ℕ // 2 ≤ n}), X i.val ω) μ := by sorry

end
