/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open ArithmeticFunction Finset Filter MeasureTheory ProbabilityTheory Real
open scoped Topology
attribute [local instance] Classical.propDecidable

namespace ErdosKac

/-- Normalized version of the number-of-distinct-prime-factors function:
$(\nu(x) - \log\log n) / \sqrt{\log\log n}$. This is the standardization that should
converge in distribution to a standard normal. -/
noncomputable def normalizedOmega (n : ℕ) (x : ℕ) : ℝ :=
  ((cardDistinctFactors x : ℝ) - Real.log (Real.log (n : ℝ))) /
    Real.sqrt (Real.log (Real.log (n : ℝ)))

/-- Empirical density at level $t$: the fraction of integers in $[1,n]$ whose normalized
omega is at least $t$. The Erdős–Kac theorem describes its limit as $n \to \infty$. -/
noncomputable def erdosKacDensity (n : ℕ) (t : ℝ) : ℝ :=
  ((Icc 1 n).filter (fun x => normalizedOmega n x ≥ t)).card / (n : ℝ)

/-- The standard Gaussian upper-tail probability $\Pr(Z \ge t)$ for $Z \sim \mathcal{N}(0,1)$. -/
noncomputable def gaussianTailProb (t : ℝ) : ℝ :=
  ((gaussianReal 0 1) (Set.Ici t)).toReal

/-- The $k$-th empirical moment of `normalizedOmega n ·` averaged uniformly over
$x \in [1,n]$. -/
noncomputable def empiricalMoment (n : ℕ) (k : ℕ) : ℝ :=
  (∑ x ∈ Icc 1 n, (normalizedOmega n x) ^ k) / (n : ℝ)

/-- The $k$-th moment of the standard normal distribution
$\mathbb{E}[Z^k]$ for $Z \sim \mathcal{N}(0,1)$. -/
noncomputable def standardNormalMoment (k : ℕ) : ℝ :=
  ∫ (x : ℝ), x ^ k ∂(gaussianReal 0 1)

end ErdosKac


/-- Mertens' theorem (second form, used here as an axiomatic input): the prime harmonic
sum $\sum_{p \le n} 1/p$ differs from $\log \log n$ by a bounded constant. -/
theorem mertens_theorem :
  ∃ C : ℝ, ∀ n : ℕ, |((Finset.Icc 1 n).filter Nat.Prime).sum
    (fun p => (1 : ℝ) / p) - Real.log (Real.log (n : ℝ))| ≤ C := by sorry

/-- Central limit theorem for sums of independent Bernoulli variables with variances
summing to infinity: the standardized partial sums converge in distribution to a standard
normal. -/
theorem clt_bernoulli_sums
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} [IsProbabilityMeasure P]
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    (Y : ℕ → Ω → ℝ) (p : ℕ → ℝ)
    (hY_indep : iIndepFun Y P)
    (hY_bern : ∀ i, ∀ᵐ ω ∂P, Y i ω = 0 ∨ Y i ω = 1)
    (hY_mean : ∀ i, P[Y i] = p i)
    (hp_range : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hvar_div : Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, p i * (1 - p i))
      Filter.atTop Filter.atTop)
    (Z : Ω' → ℝ) (hZ : HasLaw Z (gaussianReal 0 1) P') :
    TendstoInDistribution
      (fun (n : ℕ) (ω : Ω) =>
        (∑ i ∈ Finset.range n, Y i ω - ∑ i ∈ Finset.range n, p i) /
          Real.sqrt (∑ i ∈ Finset.range n, p i * (1 - p i)))
      Filter.atTop Z (fun _ => P) P' := by sorry

/-- Coupling step: for each $k$, the empirical $k$-th moment of `normalizedOmega n ·`
differs from a moment of an independent-Bernoulli model `b n` by an error vanishing as
$n \to \infty$, where `b n` tends to the standard normal $k$-th moment. -/
theorem clt_bernoulli_model_moments (k : ℕ) :
  ∃ b : ℕ → ℝ, Filter.Tendsto b Filter.atTop (nhds (ErdosKac.standardNormalMoment k)) ∧
    Filter.Tendsto (fun n => ErdosKac.empiricalMoment n k - b n) Filter.atTop (nhds 0) := by sorry


/-- Method of moments: if the empirical moments converge to the standard normal moments
in every order, then the empirical tail densities `erdosKacDensity n t` converge to
$\Pr(Z \ge t)$. -/
theorem method_of_moments_tail_convergence
    (h : ∀ k : ℕ, Filter.Tendsto (ErdosKac.empiricalMoment · k)
      Filter.atTop (nhds (ErdosKac.standardNormalMoment k))) :
    ∀ t : ℝ, Filter.Tendsto (ErdosKac.erdosKacDensity · t)
      Filter.atTop (nhds (ErdosKac.gaussianTailProb t)) := by sorry

namespace ErdosKac

open Filter

/-- For every $k$, the $k$-th empirical moment of `normalizedOmega n ·` converges to the
$k$-th moment of the standard normal, obtained by combining the Bernoulli-model coupling
with the CLT moment limit. -/
theorem moment_convergence_normalized_omega (k : ℕ) :
    Tendsto (empiricalMoment · k) atTop (nhds (standardNormalMoment k)) := by
  obtain ⟨b, hb_limit, hb_diff⟩ := clt_bernoulli_model_moments k
  have key : Tendsto (fun n => (empiricalMoment n k - b n) + b n) atTop
      (nhds (0 + standardNormalMoment k)) :=
    hb_diff.add hb_limit
  simp only [sub_add_cancel, zero_add] at key
  exact key

/-- Theorem 4.5.3 (Erdős–Kac 1940). For every $t \in \mathbb{R}$,
$$\frac{\#\{x \le n : (\nu(x) - \log\log n)/\sqrt{\log\log n} \ge t\}}{n} \to \Pr(Z \ge t)$$
as $n \to \infty$, where $Z \sim \mathcal{N}(0,1)$. -/
theorem erdos_kac (t : ℝ) :
    Tendsto (erdosKacDensity · t) atTop (nhds (gaussianTailProb t)) :=
  method_of_moments_tail_convergence moment_convergence_normalized_omega t

end ErdosKac
