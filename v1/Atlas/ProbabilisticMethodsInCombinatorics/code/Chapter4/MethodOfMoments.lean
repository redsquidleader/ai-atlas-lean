/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Moments.Basic

open MeasureTheory ProbabilityTheory Filter

open scoped Topology

namespace MethodOfMoments

/-- Method of moments (Theorem 4.5.4): if a sequence of random variables has moments of every
    positive order converging to those of the standard Gaussian, then it converges in
    distribution to the standard Gaussian. -/
theorem method_of_moments
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
  (X : (n : ℕ) → Ω n → ℝ) (μ : (n : ℕ) → Measure (Ω n))
  [∀ n, IsProbabilityMeasure (μ n)]
  (hmom : ∀ k : ℕ, k > 0 → Tendsto (fun n => moment (X n) k (μ n)) atTop
    (𝓝 (moment id k (gaussianReal 0 1)))) :
  TendstoInDistribution X atTop id μ (gaussianReal 0 1) := by sorry

end MethodOfMoments
