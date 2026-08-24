/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter5.Cor_5_13

open MeasureTheory Cor_5_13

noncomputable section

namespace Problem_5_4

/-- Euclidean ball of squared radius `r` in `ℝ^d` (under `sqDist`). -/
def euclideanBall (d : ℕ) (r : ℝ) : Set (Fin d → ℝ) :=
  {θ | sqDist θ 0 ≤ r}

/-- Unit `ℓ∞`-ball `{θ ∈ ℝ^d : max_i |θ i| ≤ 1}`. -/
def linfBall (d : ℕ) : Set (Fin d → ℝ) :=
  {θ | ∀ i : Fin d, |θ i| ≤ 1}

/-- Non-negative orthant `{θ ∈ ℝ^d : θ_i ≥ 0 for all i}`. -/
def nonnegOrthant (d : ℕ) : Set (Fin d → ℝ) :=
  {θ | ∀ i : Fin d, 0 ≤ θ i}

/-- Scaled binary hypercube `{0, c}^d ⊂ ℝ^d`. -/
def scaledHypercube (d : ℕ) (c : ℝ) : Set (Fin d → ℝ) :=
  {θ | ∀ i : Fin d, θ i = 0 ∨ θ i = c}

/-- Problem 5.4(a): minimax rate `σ²d/n` over the Euclidean ball of squared
radius `σ²d/n` in a Gaussian sequence model, with the identity estimator
attaining the matching upper bound. -/
theorem problem_5_4a
    {d : ℕ} (hd : 0 < d)
    (σ : ℝ) (hσ : 0 < σ)
    (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP : IsGSM P σ n) :
    (∃ C' : ℝ, 0 < C' ∧
      minimaxRisk P (euclideanBall d (σ ^ 2 * ↑d / ↑n)) ≥ C' * σ ^ 2 * ↑d / ↑n) ∧
    (∃ C : ℝ, 0 < C ∧
      supRisk P (euclideanBall d (σ ^ 2 * ↑d / ↑n)) (identityEstimator d) ≤
        C * σ ^ 2 * ↑d / ↑n) := by
  sorry

/-- Problem 5.4(b): minimax rate `σ²d/n` over the unit `ℓ∞`-ball, again with
the identity estimator matching the lower bound (in the small-noise regime). -/
theorem problem_5_4b
    {d : ℕ} (hd : 0 < d)
    (σ : ℝ) (hσ : 0 < σ) (hσn : σ ^ 2 ≤ ↑n)
    (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP : IsGSM P σ n) :
    (∃ C' : ℝ, 0 < C' ∧
      minimaxRisk P (linfBall d) ≥ C' * σ ^ 2 * ↑d / ↑n) ∧
    (∃ C : ℝ, 0 < C ∧
      supRisk P (linfBall d) (identityEstimator d) ≤ C * σ ^ 2 * ↑d / ↑n) := by
  sorry

/-- Problem 5.4(c): minimax rate `σ²d/n` over the non-negative orthant of
`ℝ^d` in a Gaussian sequence model. -/
theorem problem_5_4c
    {d : ℕ} (hd : 0 < d)
    (σ : ℝ) (hσ : 0 < σ)
    (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP : IsGSM P σ n) :
    (∃ C' : ℝ, 0 < C' ∧
      minimaxRisk P (nonnegOrthant d) ≥ C' * σ ^ 2 * ↑d / ↑n) ∧
    (∃ C : ℝ, 0 < C ∧
      supRisk P (nonnegOrthant d) (identityEstimator d) ≤
        C * σ ^ 2 * ↑d / ↑n) := by
  sorry

/-- Problem 5.4(d): minimax rate `σ²d/n` over the scaled binary hypercube
`{0, σ / (16√n)}^d`, with the identity estimator matching the lower bound. -/
theorem problem_5_4d
    {d : ℕ} (hd : 0 < d)
    (σ : ℝ) (hσ : 0 < σ)
    (n : ℕ) (hn : 0 < n)
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ))
    (hP : IsGSM P σ n) :
    (∃ C' : ℝ, 0 < C' ∧
      minimaxRisk P (scaledHypercube d (σ / (16 * Real.sqrt ↑n))) ≥
        C' * σ ^ 2 * ↑d / ↑n) ∧
    (∃ C : ℝ, 0 < C ∧
      supRisk P (scaledHypercube d (σ / (16 * Real.sqrt ↑n))) (identityEstimator d) ≤
        C * σ ^ 2 * ↑d / ↑n) := by
  sorry

end Problem_5_4

end
