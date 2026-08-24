/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Chapter5.Problem55

noncomputable section

/-- Sobolev ellipsoid of smoothness `β` and radius `Q`:
`{θ : ∑_j (j + 1)^{2β} θ_j² ≤ Q}` in `ℝ^d`. -/
def sobolevEllipsoid (d : ℕ) (β Q : ℝ) : Set (Fin d → ℝ) :=
  {θ | ∑ j : Fin d, ((j : ℝ) + 1) ^ (2 * β) * (θ j) ^ 2 ≤ Q}

/-- Minimax risk over the Sobolev ellipsoid (placeholder definition for
Problem 5.5). -/
noncomputable def sobolevMinimaxRisk (d : ℕ) (β Q σ : ℝ) (n : ℕ) : ℝ := sorry

/-- The Sobolev minimax risk is nonnegative under the standard hypotheses. -/
theorem sobolevMinimaxRisk_nonneg (d : ℕ) (β Q σ : ℝ) (n : ℕ)
    (hβ : β ≥ 5 / 3) (hQ : 0 < Q) (hσ : 0 < σ) (hn : 0 < n) :
    0 ≤ sobolevMinimaxRisk d β Q σ n := by
  sorry

/-- Problem 5.5: the minimax rate over the Sobolev ellipsoid in a Gaussian
sequence model is `n^{-2β/(2β + 1)}` (matching upper and lower bounds). -/
theorem problem_5_5
    (β : ℝ) (hβ : β ≥ 5 / 3) (Q : ℝ) (hQ : 0 < Q)
    (σ : ℝ) (hσ : 0 < σ) (n : ℕ) (hn : 0 < n) (d : ℕ) (hd : 0 < d) :
    ∃ (C C' : ℝ), 0 < C ∧ 0 < C' ∧
      C' * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) ≤ sobolevMinimaxRisk d β Q σ n ∧
      sobolevMinimaxRisk d β Q σ n ≤ C * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) := by
  sorry

end

end Chapter5.Problem55
