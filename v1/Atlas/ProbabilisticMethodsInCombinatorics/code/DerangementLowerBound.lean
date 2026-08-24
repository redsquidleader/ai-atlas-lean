/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
set_option maxHeartbeats 400000

namespace DerangementLowerBound

open Finset BigOperators Nat

/-- Integer form of the derangement lower bound: for $n \ge 1$,
$D_n \cdot n^n \ge (n-1)^n \cdot n!$, where $D_n = $ `numDerangements n`. -/
theorem derangement_nat_ineq (n : ℕ) (hn : 1 ≤ n) :
    numDerangements n * n ^ n ≥ (n - 1) ^ n * n.factorial := by sorry

/-- Corollary 6.5.6. The probability that a uniformly random permutation of
$\{1, \dots, n\}$ has no fixed points is at least $(1 - 1/n)^n$. -/
theorem derangement_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    (numDerangements n : ℝ) / (n.factorial : ℝ) ≥ (1 - 1 / (n : ℝ)) ^ n := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hfact_pos : (0 : ℝ) < (n.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos n)
  have hn_pow_pos : (0 : ℝ) < (n : ℝ) ^ n := pow_pos hn_pos n

  have h_eq : (1 - 1 / (n : ℝ)) ^ n = ((n : ℝ) - 1) ^ n / (n : ℝ) ^ n := by
    rw [show (1 : ℝ) - 1 / ↑n = (↑n - 1) / ↑n from by field_simp]
    rw [div_pow]
  rw [ge_iff_le, h_eq, div_le_div_iff₀ hn_pow_pos hfact_pos]


  have key := derangement_nat_ineq n hn

  have h_cast : ((n - 1) ^ n * n.factorial : ℕ) ≤ (numDerangements n * n ^ n : ℕ) := key
  have h_real := Nat.cast_le (α := ℝ).mpr h_cast
  push_cast at h_real

  have h_sub : (↑(n - 1) : ℝ) = (↑n : ℝ) - 1 := by
    rw [Nat.cast_sub hn]; simp
  rw [h_sub] at h_real
  linarith

end DerangementLowerBound
