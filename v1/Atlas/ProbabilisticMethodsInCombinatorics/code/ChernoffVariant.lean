/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option maxHeartbeats 400000

open MeasureTheory ProbabilityTheory Real Finset
open scoped NNReal ENNReal

namespace ChernoffBound

/-- `IsBernoulliRV X p μ` says that under measure `μ`, the random variable `X` is almost
surely $\{0,1\}$-valued, takes the value $1$ with probability $p$, and $p \in [0,1]$. -/
def IsBernoulliRV {Ω : Type*} {mΩ : MeasurableSpace Ω} (X : Ω → ℝ)
    (p : ℝ) (μ : Measure Ω) : Prop :=
  (∀ᵐ ω ∂μ, X ω = 0 ∨ X ω = 1) ∧
  μ {ω | X ω = 1} = ENNReal.ofReal p ∧
  0 ≤ p ∧ p ≤ 1

/-- Sharp Chernoff upper-tail bound (Theorem 5.0.5). For independent Bernoullis $X_i$ with
mean $\mu = \sum_i p_i > 0$ and $\varepsilon > 0$,
$\Pr\!\left(\sum_i X_i \ge (1+\varepsilon)\mu\right) \le \exp(-((1+\varepsilon)\log(1+\varepsilon) - \varepsilon)\mu)$. -/
theorem chernoff_upper_tail_sharp
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ_meas : Measure Ω}
  [IsProbabilityMeasure μ_meas]
  {ι : Type*} [Fintype ι]
  (X : ι → Ω → ℝ) (p : ι → ℝ)
  (hBernoulli : ∀ i, IsBernoulliRV (X i) (p i) μ_meas)
  (hIndep : iIndepFun X μ_meas)
  (hMeas : ∀ i, Measurable (X i))
  (μ_val : ℝ) (hμ : μ_val = ∑ i, p i)
  (hμ_pos : 0 < μ_val)
  (ε : ℝ) (hε : 0 < ε) :
  μ_meas {ω | (∑ i, X i ω) ≥ (1 + ε) * μ_val} ≤
    ENNReal.ofReal (exp (-((1 + ε) * log (1 + ε) - ε) * μ_val)) := by sorry

/-- Weak Chernoff upper-tail bound (Theorem 5.0.6 / Corollary 5.0.3). For independent
Bernoullis $X_i$ with mean $\mu > 0$ and $\varepsilon > 0$,
$\Pr\!\left(\sum_i X_i \ge (1+\varepsilon)\mu\right) \le \exp\!\left(-\dfrac{\varepsilon^2}{1+\varepsilon}\,\mu\right)$. -/
theorem chernoff_upper_tail_weak
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ_meas : Measure Ω}
  [IsProbabilityMeasure μ_meas]
  {ι : Type*} [Fintype ι]
  (X : ι → Ω → ℝ) (p : ι → ℝ)
  (hBernoulli : ∀ i, IsBernoulliRV (X i) (p i) μ_meas)
  (hIndep : iIndepFun X μ_meas)
  (hMeas : ∀ i, Measurable (X i))
  (μ_val : ℝ) (hμ : μ_val = ∑ i, p i)
  (hμ_pos : 0 < μ_val)
  (ε : ℝ) (hε : 0 < ε) :
  μ_meas {ω | (∑ i, X i ω) ≥ (1 + ε) * μ_val} ≤
    ENNReal.ofReal (exp (-(ε ^ 2 / (1 + ε)) * μ_val)) := by sorry

/-- Chernoff lower-tail bound (Theorem 5.0.7). For independent Bernoullis $X_i$ with mean
$\mu > 0$ and $\varepsilon > 0$,
$\Pr\!\left(\sum_i X_i \le (1-\varepsilon)\mu\right) \le \exp(-\varepsilon^2 \mu / 2)$. -/
theorem chernoff_lower_tail
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ_meas : Measure Ω}
  [IsProbabilityMeasure μ_meas]
  {ι : Type*} [Fintype ι]
  (X : ι → Ω → ℝ) (p : ι → ℝ)
  (hBernoulli : ∀ i, IsBernoulliRV (X i) (p i) μ_meas)
  (hIndep : iIndepFun X μ_meas)
  (hMeas : ∀ i, Measurable (X i))
  (μ_val : ℝ) (hμ : μ_val = ∑ i, p i)
  (hμ_pos : 0 < μ_val)
  (ε : ℝ) (hε : 0 < ε) :
  μ_meas {ω | (∑ i, X i ω) ≤ (1 - ε) * μ_val} ≤
    ENNReal.ofReal (exp (-(ε ^ 2 * μ_val / 2))) := by sorry

/-- Elementary inequality underlying the weakening from sharp to weak Chernoff:
$\dfrac{\varepsilon^2}{1+\varepsilon} \le (1+\varepsilon)\log(1+\varepsilon) - \varepsilon$
for all $\varepsilon > 0$. -/
theorem chernoff_upper_exponent_ineq
  (ε : ℝ) (hε : 0 < ε) :
  ε ^ 2 / (1 + ε) ≤ (1 + ε) * log (1 + ε) - ε := by sorry

end ChernoffBound
