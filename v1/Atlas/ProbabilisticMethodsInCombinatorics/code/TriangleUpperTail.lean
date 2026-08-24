/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option maxHeartbeats 400000

noncomputable section

open Filter Asymptotics Real

namespace TriangleUpperTail

/-- Probability that the Erdős–Rényi random graph $G(n, p)$ has at least
$(1 + \delta) \binom{n}{3} p^3$ triangles (the upper tail event). -/
noncomputable def erdosRenyiTriangleUpperTailProb (n : ℕ) (p : ℝ) (δ : ℝ) : ℝ := by sorry

/-- The triangle upper-tail probability is nonnegative. -/
theorem erdosRenyiTriangleUpperTailProb_nonneg (n : ℕ) (p : ℝ) (δ : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hδ : 0 < δ) :
    0 ≤ erdosRenyiTriangleUpperTailProb n p δ := by sorry

/-- The triangle upper-tail probability is at most $1$. -/
theorem erdosRenyiTriangleUpperTailProb_le_one (n : ℕ) (p : ℝ) (δ : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hδ : 0 < δ) :
    erdosRenyiTriangleUpperTailProb n p δ ≤ 1 := by sorry

/-- For $0 < p < 1$ and $\delta > 0$, the triangle upper-tail probability is strictly
positive (the event is achievable, e.g. by the complete graph). -/
theorem erdosRenyiTriangleUpperTailProb_pos (n : ℕ) (p : ℝ) (δ : ℝ)
    (hp : 0 < p) (hp1 : p < 1) (hδ : 0 < δ) :
    0 < erdosRenyiTriangleUpperTailProb n p δ := by sorry

/-- Rate function $-\log \mathbb{P}[\text{triangle upper tail}]$ associated with the
upper-tail event for $G(n, p)$. -/
def negLogProbTriangleUpperTail (n : ℕ) (p : ℝ) (δ : ℝ) : ℝ :=
  -Real.log (erdosRenyiTriangleUpperTailProb n p δ)

/-- Theorem 8.2.5 (Harel–Mousset–Samotij, upper regime). When $p \to 0$ with
$p \cdot n^{1/2} \to \infty$, the rate function is asymptotically equivalent to
$\min(\delta/3, \delta^{2/3}/2) \cdot n^2 p^2 \log(1/p)$. -/
theorem harel_mousset_samotij_upper_regime
    (p : ℕ → ℝ) (δ : ℝ)
    (hδ : 0 < δ)
    (hp_pos : ∀ᶠ n in atTop, 0 < p n)
    (hp_lt_one : ∀ᶠ n in atTop, p n < 1)
    (hp_lower : Tendsto (fun n => p n * (n : ℝ) ^ (1/2 : ℝ)) atTop atTop)
    (hp_upper : Tendsto p atTop (nhds 0)) :
    (fun n => negLogProbTriangleUpperTail n (p n) δ) ~[atTop]
      (fun n => min (δ / 3) (δ ^ (2/3 : ℝ) / 2) * (n : ℝ) ^ 2 * (p n) ^ 2 *
        Real.log (1 / p n)) := by sorry

/-- Theorem 8.2.5 (Harel–Mousset–Samotij, lower regime). When $p \cdot n / \log n \to
\infty$ but $p \cdot n^{1/2} \to 0$, the rate function is asymptotically equivalent to
$\frac{\delta^{2/3}}{2} \cdot n^2 p^2 \log(1/p)$. -/
theorem harel_mousset_samotij_lower_regime
    (p : ℕ → ℝ) (δ : ℝ)
    (hδ : 0 < δ)
    (hp_pos : ∀ᶠ n in atTop, 0 < p n)
    (hp_lower : Tendsto (fun n => p n * (n : ℝ) / Real.log n) atTop atTop)
    (hp_upper : Tendsto (fun n => p n * (n : ℝ) ^ (1/2 : ℝ)) atTop (nhds 0)) :
    (fun n => negLogProbTriangleUpperTail n (p n) δ) ~[atTop]
      (fun n => δ ^ (2/3 : ℝ) / 2 * (n : ℝ) ^ 2 * (p n) ^ 2 *
        Real.log (1 / p n)) := by sorry

end TriangleUpperTail
