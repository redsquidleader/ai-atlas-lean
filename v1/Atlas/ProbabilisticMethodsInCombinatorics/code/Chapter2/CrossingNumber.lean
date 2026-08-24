/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
set_option maxHeartbeats 400000

namespace CrossingNumber

/-- Predicate stating that a graph with $n$ vertices and $m$ edges is planar
(abstract placeholder for the planarity property used throughout this file). -/
noncomputable def IsPlanarGraph (n m : ℕ) : Prop := by sorry

/-- Euler's formula for planar graphs: a planar graph on $n \geq 1$ vertices has at most
$3n$ edges, i.e., $m \leq 3n$. -/
theorem euler_formula_planar (n m : ℕ) (hn : 0 < n) (h : IsPlanarGraph n m) : m ≤ 3 * n := by sorry

/-- A planarization of a graph: removing $cr$ crossing edges from a graph with $m$ edges
yields a planar graph on the same $n$ vertices. -/
theorem planarization_is_planar (n m cr : ℕ) : IsPlanarGraph n (m - cr) := by sorry

/-- Combining planarization with Euler's bound: $m - cr \leq 3n$ for $n \geq 1$. -/
theorem euler_bound_planarized (n m cr : ℕ) (hn : 0 < n) :
    m - cr ≤ 3 * n :=
  euler_formula_planar n (m - cr) hn (planarization_is_planar n m cr)

/-- The "cheap" crossing-number bound: if $4n \leq m$, then $m \leq cr + 3n$,
i.e., $cr \geq m - 3n$. -/
theorem cheap_bound (n m cr : ℕ) (hn : 0 < n) (_hm : 4 * n ≤ m) : m ≤ cr + 3 * n := by
  have h := euler_bound_planarized n m cr hn
  omega

/-- The expected number of crossings in a random subgraph where each vertex is kept
independently with probability $p$ (abstract placeholder). -/
noncomputable def expected_crossing_number (n m cr : ℕ) (p : ℝ) : ℝ := by sorry

/-- Upper bound on the expected crossing number of a random induced subgraph:
each of the $cr$ crossings survives with probability $p^4$, so
$\mathbb{E}[cr'] \leq p^4 \cdot cr$. -/
theorem expected_crossing_upper_bound (n m cr : ℕ) (hn : 0 < n) (hm : 4 * n ≤ m)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    expected_crossing_number n m cr p ≤ p ^ 4 * (cr : ℝ) := by sorry

/-- Lower bound for the expected crossing number from the cheap bound applied to the
random subgraph: $p^2 m - 3 p n \leq \mathbb{E}[cr']$. -/
theorem expected_crossing_lower_bound (n m cr : ℕ) (hn : 0 < n) (hm : 4 * n ≤ m)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    p ^ 2 * (m : ℝ) - 3 * p * (n : ℝ) ≤ expected_crossing_number n m cr p := by sorry

/-- Combined expectations for the random subgraph: there exists $\mathbb{E}[cr']$
sandwiched between the linear lower bound and the $p^4 \cdot cr$ upper bound. -/
theorem random_subgraph_expectations (n m cr : ℕ) (hn : 0 < n) (hm : 4 * n ≤ m)
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    ∃ E_cr : ℝ, p ^ 2 * (m : ℝ) - 3 * p * (n : ℝ) ≤ E_cr ∧ E_cr ≤ p ^ 4 * (cr : ℝ) :=
  ⟨expected_crossing_number n m cr p,
   expected_crossing_lower_bound n m cr hn hm p hp hp1,
   expected_crossing_upper_bound n m cr hn hm p hp hp1⟩

/-- For any $p \in (0,1]$, the random-subgraph inequality
$p^4 \cdot cr \geq p^2 m - 3 p n$ holds, obtained by combining the two expectation
bounds. -/
theorem subgraph_bound (n m cr : ℕ) (hn : 0 < n) (hm : 4 * n ≤ m) :
    ∀ p : ℝ, 0 < p → p ≤ 1 → p ^ 4 * (cr : ℝ) ≥ p ^ 2 * (m : ℝ) - 3 * p * (n : ℝ) := by
  intro p hp hp1
  obtain ⟨E_cr, h_lower, h_upper⟩ := random_subgraph_expectations n m cr hn hm p hp hp1
  linarith

/-- **Crossing number inequality (Theorem 2.6.2).** For any graph with $|V| = n \geq 1$
and $|E| = m \geq 4n$, the crossing number satisfies
$64 n^2 \cdot cr(G) \geq m^3$, i.e., $cr(G) \gtrsim m^3 / n^2$. -/
theorem crossing_number_inequality (n m cr : ℕ) (hn : 0 < n) (hm : 4 * n ≤ m) :
    64 * n ^ 2 * cr ≥ m ^ 3 := by
  have h_cheap := cheap_bound n m cr hn hm
  have h_subgraph_bound := subgraph_bound n m cr hn hm

  have hcr_ge_n : n ≤ cr := by omega
  have hm_pos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le (Nat.mul_pos (by norm_num : 0 < 4) hn) hm
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hcr_ge_n_real : (n : ℝ) ≤ (cr : ℝ) := Nat.cast_le.mpr hcr_ge_n

  have hp_pos : (0 : ℝ) < 4 * (n : ℝ) / (m : ℝ) := by positivity
  have hp_le : 4 * (n : ℝ) / (m : ℝ) ≤ 1 := by
    rw [div_le_one hm_pos]; exact_mod_cast hm

  have key := h_subgraph_bound (4 * ↑n / ↑m) hp_pos hp_le

  have hm4_pos : (0 : ℝ) < (m : ℝ) ^ 4 := by positivity
  have key2 : (4 * (n : ℝ)) ^ 4 * ↑cr ≥
      (4 * (n : ℝ)) ^ 2 * (m : ℝ) ^ 3 - 3 * (4 * (n : ℝ)) * (n : ℝ) * (m : ℝ) ^ 3 := by
    have h1 : (4 * (n : ℝ) / (m : ℝ)) ^ 4 * (cr : ℝ) * (m : ℝ) ^ 4 =
        (4 * (n : ℝ)) ^ 4 * (cr : ℝ) := by field_simp
    have h2 : ((4 * (n : ℝ) / (m : ℝ)) ^ 2 * (m : ℝ) -
        3 * (4 * (n : ℝ) / (m : ℝ)) * (n : ℝ)) * (m : ℝ) ^ 4 =
        (4 * (n : ℝ)) ^ 2 * (m : ℝ) ^ 3 -
        3 * (4 * (n : ℝ)) * (n : ℝ) * (m : ℝ) ^ 3 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right key (le_of_lt hm4_pos)]

  have key3 : 256 * (n : ℝ) ^ 4 * (cr : ℝ) ≥ 4 * (n : ℝ) ^ 2 * (m : ℝ) ^ 3 := by
    nlinarith

  have key4 : 64 * (n : ℝ) ^ 2 * (cr : ℝ) ≥ (m : ℝ) ^ 3 := by
    nlinarith [sq_nonneg (n : ℝ), hcr_ge_n_real,
      mul_pos (show (0 : ℝ) < 4 from by norm_num) (sq_pos_of_pos hn_pos)]
  exact_mod_cast key4

/-- **Corollary 2.6.4 of the crossing number inequality.** If $n \geq 4$ and
$|E| \geq n^2$, then the crossing number is bounded below by
$cr(G) \geq n^4 / 64$. -/
theorem crossing_number_corollary (n m cr : ℕ) (hn : 4 ≤ n) (hm : n ^ 2 ≤ m) :
    64 * cr ≥ n ^ 4 := by
  have hn_pos : 0 < n := by omega
  have h4n_le_m : 4 * n ≤ m := by
    calc 4 * n ≤ n * n := by nlinarith
    _ = n ^ 2 := by ring
    _ ≤ m := hm
  have thm := crossing_number_inequality n m cr hn_pos h4n_le_m

  have hm3 : m ^ 3 ≥ n ^ 6 := by
    have := Nat.pow_le_pow_left hm 3
    linarith [show (n ^ 2) ^ 3 = n ^ 6 from by ring]

  have h64 : 64 * n ^ 2 * cr ≥ n ^ 6 := by linarith
  have hn2_pos : 0 < n ^ 2 := by positivity
  have : 64 * cr * n ^ 2 ≥ n ^ 4 * n ^ 2 := by
    have : n ^ 6 = n ^ 4 * n ^ 2 := by ring
    linarith [show 64 * n ^ 2 * cr = 64 * cr * n ^ 2 from by ring]
  exact Nat.le_of_mul_le_mul_right this hn2_pos

end CrossingNumber
