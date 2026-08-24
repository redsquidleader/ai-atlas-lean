/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Gaussian.Multivariate
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory

noncomputable section

namespace GaussianIsoperimetric

/-- A set $H \subseteq E$ is a half-space if it has the form $\{x : \langle v, x \rangle \leq c\}$
for some nonzero $v$ and real $c$. -/
def IsHalfSpace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : Set E) : Prop :=
  ∃ (v : E) (_ : v ≠ 0) (c : ℝ), H = {x | @inner ℝ _ _ v x ≤ c}


/-- Gaussian isoperimetric inequality (Theorem 9.4.15): among all measurable sets $A$ of a
given standard Gaussian measure, half-spaces minimize the Gaussian measure of the
$t$-thickening. That is, if $\gamma(A) = \gamma(H)$ for a half-space $H$, then
$\gamma(A_t) \geq \gamma(H_t)$ for every $t \geq 0$. -/
theorem gaussian_isoperimetric_inequality
    {n : ℕ}
    {A H : Set (EuclideanSpace ℝ (Fin n))}
    (hA : MeasurableSet A)
    (hH : IsHalfSpace H)
    (hAH : stdGaussian (EuclideanSpace ℝ (Fin n)) A =
           stdGaussian (EuclideanSpace ℝ (Fin n)) H)
    {t : ℝ} (ht : 0 ≤ t) :
    stdGaussian (EuclideanSpace ℝ (Fin n)) (Metric.cthickening t A) ≥
    stdGaussian (EuclideanSpace ℝ (Fin n)) (Metric.cthickening t H) := by sorry


/-- Gaussian concentration for Lipschitz functions (Corollary 9.4.16): if $f$ is
$1$-Lipschitz on $\mathbb{R}^n$ and $Z$ is a standard Gaussian vector, there exists a median
$m$ such that $\mathbb{P}(|f(Z) - m| \geq t) \leq 2e^{-t^2/2}$ for all $t \geq 0$. -/
theorem gaussian_concentration_lipschitz
    {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : LipschitzWith 1 f) :
    ∃ m : ℝ, ∀ t : ℝ, 0 ≤ t →
      stdGaussian (EuclideanSpace ℝ (Fin n)) {z | t ≤ |f z - m|} ≤
        ENNReal.ofReal (2 * Real.exp (-(t ^ 2) / 2)) := by sorry

end GaussianIsoperimetric
