/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.UniformSpace.Real
set_option maxHeartbeats 400000

open Filter Topology

namespace ColorabilityThreshold

/-- Probability that the random graph $G(n, d/n)$ on $n$ vertices is $k$-colorable. -/
noncomputable def probKColorable (k n : ℕ) (d : ℝ) : ℝ := by sorry

/-- The probability of $k$-colorability is nonnegative. -/
theorem probKColorable_nonneg (k n : ℕ) (d : ℝ) : 0 ≤ probKColorable k n d := by sorry

/-- The probability of $k$-colorability is at most $1$. -/
theorem probKColorable_le_one (k n : ℕ) (d : ℝ) : probKColorable k n d ≤ 1 := by sorry

/-- $k$-colorability sharp threshold (Achlioptas–Friedgut, Theorem 4.3.17):
    for every $k \ge 3$ there exists $d_k > 0$ such that for $d < d_k$ the graph
    $G(n, d/n)$ is $k$-colorable whp, while for $d > d_k$ it is not. -/
theorem sharp_threshold_k_colorability :
    ∀ k : ℕ, k ≥ 3 →
      ∃ d_k : ℝ, d_k > 0 ∧
        (∀ d : ℝ, d > 0 → d < d_k →
          Tendsto (fun n : ℕ => probKColorable k n d) atTop (𝓝 1)) ∧
        (∀ d : ℝ, d > d_k →
          Tendsto (fun n : ℕ => probKColorable k n d) atTop (𝓝 0)) := by sorry

end ColorabilityThreshold
