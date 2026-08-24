/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_17
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

open MeasureTheory Real Set Metric
open scoped ENNReal NNReal

noncomputable section

/-- A random vector `X : Ω → ℝ^p` is sub-Gaussian with variance proxy `σ²`
if every unit-norm linear projection `ω ↦ ⟨θ, X ω⟩` is sub-Gaussian with
proxy `σ²`. -/
def IsSubGaussianVec {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (X : Ω → EuclideanSpace ℝ (Fin p)) (σsq : ℝ)
    (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop :=
  ∀ θ : EuclideanSpace ℝ (Fin p), ‖θ‖ = 1 →
    IsSubGaussian (fun ω => @inner ℝ _ _ θ (X ω)) σsq μ

/-- **Problem 1.6 (Sub-Gaussian supremum over a compact subset of the sphere).**
If `K ⊆ S^{p-1}` has covering numbers bounded by `(C/ε)^d` and `X` is a
sub-Gaussian random vector with proxy `σ²`, then there exist positive
constants `c₁, c₂` such that, for every `δ ∈ (0,1)`, with probability at
least `1 - δ`,
`sup_{θ ∈ K} ⟨θ, X⟩ ≤ c₁ σ √(d log(2p/d)) + c₂ σ √(log(1/δ))`. -/
theorem problem_1_6_compact_sphere_max
    {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω} (_ : IsProbabilityMeasure μ)
    {p : ℕ} (hp : 0 < p)
    (K : Set (EuclideanSpace ℝ (Fin p)))
    (hK_compact : IsCompact K)
    (hK_sphere : K ⊆ Metric.sphere 0 1)
    (C : ℝ) (hC : 1 ≤ C)
    (d : ℝ) (hd_pos : 0 < d) (hd_le_p : d ≤ p)
    (hcov : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ (Nε : Finset (EuclideanSpace ℝ (Fin p))),
        IsEpsilonNet K (↑Nε) ε ∧ (Nε.card : ℝ) ≤ (C / ε) ^ d)
    (σ : ℝ) (hσ : 0 < σ)
    (X : Ω → EuclideanSpace ℝ (Fin p))
    (hX : IsSubGaussianVec X (σ ^ 2) μ) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ c₂ : ℝ, 0 < c₂ ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 →
        μ {ω | ∀ θ ∈ K, @inner ℝ _ _ θ (X ω) ≤
          c₁ * σ * Real.sqrt (d * Real.log (2 * ↑p / d)) +
          c₂ * σ * Real.sqrt (Real.log (1 / δ))} ≥
        ENNReal.ofReal (1 - δ) := by sorry

end
