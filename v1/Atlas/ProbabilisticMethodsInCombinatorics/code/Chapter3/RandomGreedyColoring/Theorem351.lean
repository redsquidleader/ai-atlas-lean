/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter3.RandomGreedyColoring.StructuralLemma
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fintype.BigOperators
open Finset Fintype TwoColorableHypergraph

namespace TwoColorableHypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Quantitative bound used in the analysis of Theorem 3.5.1: for $k \geq 2$,
$\tfrac{1}{8}(1 + 1/\log k) < 1$. -/
lemma one_eighth_bound (k : ℕ) (hk : 2 ≤ k) :
    (1 : ℝ) / 8 * (1 + 1 / Real.log ↑k) < 1 := by
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlogk : Real.log 2 ≤ Real.log (↑k : ℝ) := by
    apply Real.log_le_log (by norm_num : (0:ℝ) < 2)
    exact_mod_cast hk
  have hlogk_pos : (0 : ℝ) < Real.log ↑k := by linarith
  have hlogk_bound : (0.6931471803 : ℝ) < Real.log ↑k := by linarith
  have h1 : 1 / Real.log ↑k < 1 / 0.6931471803 := by
    apply div_lt_div_of_pos_left one_pos (by positivity) hlogk_bound
  have h2 : (1:ℝ) / 0.6931471803 < 1.4428 := by norm_num
  linarith

/-- Probabilistic existence statement: for $k$-uniform hypergraphs with at most
$c \sqrt{k/\log k} \, 2^k$ edges (with $0 < c \leq 1/8$), some injective ordering of the
vertices yields no conflicting pair. -/
theorem exists_no_conflicting_pair_of_few_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (c : ℝ) (hc : 0 < c) (hc_small : c ≤ 1 / 8)
    (H : Hypergraph V) (k : ℕ) (hk : 2 ≤ k)
    (huni : IsKUniform H k)
    (hfew : (H.card : ℝ) ≤ c * Real.sqrt (↑k / Real.log ↑k) * 2 ^ k) :
    ∃ (σ : V → ℕ), Function.Injective σ ∧ ¬HasConflictingPair H σ := by sorry

/-- **Theorem 3.5.1 (Radhakrishnan–Srinivasan 2000).** There is an absolute constant
$c > 0$ such that every $k$-uniform hypergraph with at most $c \sqrt{k/\log k} \, 2^k$
edges is 2-colorable. -/
theorem radhakrishnan_srinivasan_two_colorable :
    ∃ c : ℝ, c > 0 ∧ ∀ (V : Type*) [Fintype V] [DecidableEq V]
      (H : Hypergraph V) (k : ℕ),
      2 ≤ k → IsKUniform H k →
      (H.card : ℝ) ≤ c * Real.sqrt (↑k / Real.log ↑k) * 2 ^ k →
      IsTwoColorable H := by
  refine ⟨1 / 8, by norm_num, fun V _ _ H k hk huni hfew => ?_⟩
  obtain ⟨σ, hσ_inj, hσ_no_conflict⟩ :=
    exists_no_conflicting_pair_of_few_edges (1/8) (by norm_num : (0:ℝ) < 1/8)
      le_rfl H k hk huni hfew
  exact two_colorable_of_no_conflicting_pair H k hk huni σ hσ_inj hσ_no_conflict

end TwoColorableHypergraph
