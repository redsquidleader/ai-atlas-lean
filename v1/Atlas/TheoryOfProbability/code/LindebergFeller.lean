/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.CharFun

open MeasureTheory ProbabilityTheory Filter Complex Finset
open scoped Topology BoundedContinuousFunction NNReal

noncomputable section

namespace ProbabilityTheory

/-- The **Lindeberg condition** for a triangular array `X n k` of random variables on `(Ω, μ)`:
for every `ε > 0`, the truncated second moment
`∑ₖ ∫ (X n k)² · 𝟙{|X n k| > ε} dμ` tends to `0` as `n → ∞`. This is the key hypothesis of the
Lindeberg–Feller central limit theorem. -/
def LindebergConditionTriangular {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → ℕ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n => ∑ k ∈ Finset.range n,
      ∫ ω, (X n k ω) ^ 2 * Set.indicator {ω' | ε < |X n k ω'|} 1 ω ∂μ)
    atTop (𝓝 0)

set_option maxHeartbeats 3200000 in

set_option maxHeartbeats 1600000 in

/-- Helper bound: for any real `x`, `‖e^{ix} - 1 - ix‖ ≤ x²`. This is the standard
second-order Taylor estimate for the complex exponential along the imaginary axis. -/
theorem norm_exp_ofReal_mul_I_sub_one_sub_le (x : ℝ) :
    ‖exp (↑x * I) - 1 - ↑x * I‖ ≤ x ^ 2 := by sorry

/-- For a mean-zero random variable `X` with finite second moment, the deviation of its
characteristic function from `1` is controlled by the variance:
`‖φ_X(t) - 1‖ ≤ t² · 𝔼[X²]`. -/
theorem norm_charFun_sub_one_le_sq_mul_variance
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hmeas : Measurable X)
    (hmean : ∫ ω, X ω ∂μ = 0)
    (hint2 : Integrable (fun ω => (X ω) ^ 2) μ)
    (t : ℝ) :
    ‖charFun (μ.map X) t - 1‖ ≤ t ^ 2 * ∫ ω, (X ω) ^ 2 ∂μ := by sorry

/-- Under the Lindeberg hypothesis, the product of characteristic functions of the rows of a
mean-zero triangular array converges to the characteristic function of a `N(0, σ²)` Gaussian,
`exp(-σ² t²/2)`. This is the analytic core of the Lindeberg–Feller theorem. -/
theorem lindeberg_charFun_product_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → ℕ → Ω → ℝ)
    (hmeas : ∀ n k, Measurable (X n k))
    (hmean : ∀ n k, ∫ ω, X n k ω ∂μ = 0)
    (σ : ℝ) (hσ : 0 < σ)
    (hvar : Tendsto (fun n => ∑ k ∈ Finset.range n,
              ∫ ω, (X n k ω) ^ 2 ∂μ) atTop (𝓝 (σ ^ 2)))
    (hL : LindebergConditionTriangular X μ)
    (t : ℝ) :
    Tendsto (fun n => ∏ k ∈ Finset.range n, charFun (μ.map (X n k)) t)
      atTop (𝓝 (exp (-(↑(σ ^ 2) * ↑t ^ 2 / 2)))) := by sorry

/-- **Lindeberg–Feller central limit theorem** (triangular array form).

Suppose `X n k`, for `1 ≤ k ≤ n`, is a triangular array of independent, mean-zero random variables
on `(Ω, μ)`. If
* the row variances `∑ₖ 𝔼[X n k²]` converge to `σ² > 0`, and
* the Lindeberg condition `LindebergConditionTriangular X μ` holds,

then the row sums `Sₙ = ∑ₖ X n k` converge in distribution to `N(0, σ²)`: for every bounded
continuous `f : ℝ →ᵇ ℝ`, `𝔼[f(Sₙ)] → 𝔼[f(σ · χ)]` where `χ` is a standard normal. -/
theorem lindeberg_feller_clt_triangular
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → ℕ → Ω → ℝ)
    (hind : ∀ n, iIndepFun (m := fun _ => inferInstance) (X n) μ)
    (hmeas : ∀ n k, Measurable (X n k))
    (hmean : ∀ n k, ∫ ω, X n k ω ∂μ = 0)
    (σ : ℝ) (hσ : 0 < σ)
    (hvar : Tendsto (fun n => ∑ k ∈ Finset.range n,
              ∫ ω, (X n k ω) ^ 2 ∂μ) atTop (𝓝 (σ ^ 2)))
    (hL : LindebergConditionTriangular X μ) :
    ∀ f : ℝ →ᵇ ℝ,
      Tendsto (fun n => ∫ x, f x ∂(Measure.map (fun ω => ∑ k ∈ Finset.range n, X n k ω) μ))
        atTop (𝓝 (∫ x, f x ∂(gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩))) := by

  have hSn_meas : ∀ n, Measurable (fun ω => ∑ k ∈ Finset.range n, X n k ω) :=
    fun n => Finset.measurable_sum _ fun k _ => hmeas n k
  have hSn_prob : ∀ n,
      IsProbabilityMeasure (μ.map (fun ω => ∑ k ∈ Finset.range n, X n k ω)) :=
    fun n => ⟨by rw [Measure.map_apply (hSn_meas n) MeasurableSet.univ]; simp [measure_univ]⟩

  let μn : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨μ.map (fun ω => ∑ k ∈ Finset.range n, X n k ω), hSn_prob n⟩
  let μ₀ : ProbabilityMeasure ℝ :=
    ⟨gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩, inferInstance⟩

  suffices h : Tendsto μn atTop (𝓝 μ₀) by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at h
    exact h

  rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
  intro t

  have hcharFun_eq : ∀ n, charFun (↑(μn n)) t =
      ∏ k ∈ Finset.range n, charFun (μ.map (X n k)) t := by
    intro n
    show charFun (μ.map (fun ω => ∑ k ∈ Finset.range n, X n k ω)) t = _
    have h := ((hind n).restrict (Finset.range n)).charFun_map_fun_finset_sum_eq_prod
      (fun i _ => (hmeas n i).aemeasurable)
    exact (congr_fun h t).trans (by simp [Finset.prod_apply])

  have hcharFun_target : charFun (↑μ₀) t = exp (-(↑(σ ^ 2) * ↑t ^ 2 / 2)) := by
    show charFun (gaussianReal 0 ⟨σ ^ 2, sq_nonneg σ⟩) t = _
    rw [charFun_gaussianReal]
    simp only [ofReal_zero, mul_zero, zero_mul, NNReal.coe_mk, zero_sub]

  simp_rw [hcharFun_eq, hcharFun_target]
  exact lindeberg_charFun_product_tendsto X hmeas hmean σ hσ hvar hL t

end ProbabilityTheory
