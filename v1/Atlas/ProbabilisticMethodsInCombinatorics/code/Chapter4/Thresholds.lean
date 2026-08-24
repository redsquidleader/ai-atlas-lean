/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Order.Filter.AtTopBot.Ring
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter4.SubgraphThreshold
set_option maxHeartbeats 800000

open Filter Real SimpleGraph Classical

namespace Thresholds

/-- The number of ordered pairs $(u, v)$ in $S \times S$ with $u \neq v$ and $u \sim_H v$.
This is twice the number of edges in the induced subgraph $H[S]$. -/
noncomputable def directedEdgesInSubset {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V) : ℕ :=
  Finset.card <| (S ×ˢ S).filter fun p => p.1 ≠ p.2 ∧ H.Adj p.1 p.2

/-- The maximum edge-to-vertex ratio over nonempty subsets of $V(H)$, i.e.
$m(H) = \max_{S \ne \emptyset} |E(H[S])| / |S|$. -/
noncomputable def maxEdgeVertexRatio {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] [Nonempty V] : ℝ :=
  Finset.sup' (Finset.univ.filter (fun S : Finset V => S.Nonempty))
    (by
      simp only [Finset.filter_nonempty_iff]
      exact ⟨Finset.univ, Finset.mem_univ _,
        ⟨Classical.arbitrary V, Finset.mem_univ _⟩⟩)
    (fun S => (directedEdgesInSubset H S : ℝ) / (2 * S.card : ℝ))

/-- The probability that $G(n, p)$ contains $H$ as a (not necessarily induced) subgraph,
computed by summing Bernoulli edge weights over all graphs $G$ on $n$ vertices that admit
an injective graph homomorphism from $H$. -/
noncomputable def probContainsSubgraph {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (n : ℕ) (p : ℝ) : ℝ :=
  ∑ G : SimpleGraph (Fin n),
    (if ∃ f : V ↪ Fin n, ∀ v w, H.Adj v w → G.Adj (f v) (f w) then 1 else 0) *
    (p ^ Fintype.card G.edgeSet * (1 - p) ^ (n.choose 2 - Fintype.card G.edgeSet))

/-- The indicator of "there exists an injective homomorphism $H \hookrightarrow G$" is
bounded by the sum of indicators over all injections, since at least one injection works
whenever the existential holds. -/
theorem indicator_exists_le_sum {V : Type*} [Fintype V]
    (n : ℕ) (H : SimpleGraph V) [DecidableRel H.Adj] (G : SimpleGraph (Fin n)) :
    (if ∃ f : V ↪ Fin n, ∀ v w, H.Adj v w → G.Adj (f v) (f w) then (1 : ℝ) else 0) ≤
    ∑ f : V ↪ Fin n, (if ∀ v w, H.Adj v w → G.Adj (f v) (f w) then (1 : ℝ) else 0) := by
  by_cases h : ∃ f : V ↪ Fin n, ∀ v w, H.Adj v w → G.Adj (f v) (f w)
  · rw [if_pos h]
    obtain ⟨f, hf⟩ := h
    have hfterm : (if ∀ v w, H.Adj v w → G.Adj (f v) (f w) then (1 : ℝ) else 0) = 1 := if_pos hf
    calc (1 : ℝ) = if ∀ v w, H.Adj v w → G.Adj (f v) (f w) then 1 else 0 := hfterm.symm
      _ ≤ ∑ g : V ↪ Fin n, if ∀ v w, H.Adj v w → G.Adj (g v) (g w) then (1 : ℝ) else 0 := by
          apply Finset.single_le_sum _ (Finset.mem_univ f)
          intro i _
          split_ifs <;> linarith
  · rw [if_neg h]
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> linarith

/-- The Bernoulli probability that $G$ contains the image of $H$ under a fixed injection
$f : V(H) \hookrightarrow [n]$ is at most $p^{|E(H)|}$, since all $|E(H)|$ edges of $H$
must appear independently. -/
theorem restricted_bernoulli_sum_le {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] [Fintype H.edgeSet] (n : ℕ) (p : ℝ)
    (hp : 0 ≤ p) (hp1 : p ≤ 1) (f : V ↪ Fin n) :
    ∑ G : SimpleGraph (Fin n),
      (if ∀ v w, H.Adj v w → G.Adj (f v) (f w) then (1 : ℝ) else 0) *
      (p ^ Fintype.card G.edgeSet * (1 - p) ^ (n.choose 2 - Fintype.card G.edgeSet))
    ≤ p ^ Fintype.card H.edgeSet := by sorry

/-- A densest-subgraph first-moment bound: there exists $k > 0$ depending on $H$ such
that the probability of containing $H$ is bounded by $|p / n^{-1/m(H)}|^k$, the key
nonnegativity-plus-upper-bound estimate underlying the first moment direction. -/
theorem densest_subgraph_bound {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (H : SimpleGraph V) [DecidableRel H.Adj] [Fintype H.edgeSet]
    (hH : 0 < maxEdgeVertexRatio H) :
    ∃ (k : ℕ), 0 < k ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ (p : ℝ), |p| ≤ 1 →
    0 ≤ probContainsSubgraph H n p ∧
    probContainsSubgraph H n p ≤ |p / (n : ℝ) ^ (-(1 : ℝ) / maxEdgeVertexRatio H)| ^ k := by sorry

/-- **First moment side of Bollobás's threshold theorem.** If $p_n / n^{-1/m(H)} \to 0$,
then the probability that $G(n, p_n)$ contains $H$ as a subgraph tends to $0$. -/
theorem first_moment_zero_statement {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (H : SimpleGraph V) [DecidableRel H.Adj] [Fintype H.edgeSet]
    (hH : 0 < maxEdgeVertexRatio H)
    (p : ℕ → ℝ)
    (hp : Tendsto (fun n => p n / (n : ℝ) ^ (-(1 : ℝ) / maxEdgeVertexRatio H)) atTop (nhds 0)) :
    Tendsto (fun n => probContainsSubgraph H n (p n)) atTop (nhds 0) := by

  obtain ⟨k, hk_pos, hbound⟩ := densest_subgraph_bound H hH

  have hpow : Tendsto (fun n => |p n / (↑n : ℝ) ^ (-(1:ℝ) / maxEdgeVertexRatio H)| ^ k)
      atTop (nhds 0) := by
    have h := (hp.norm).pow k
    simp only [norm_eq_abs, zero_pow (Nat.pos_iff_ne_zero.mp hk_pos), abs_zero] at h
    exact h

  have hp_abs_bound : ∀ᶠ n in atTop, |p n| ≤ 1 := by
    filter_upwards [hp.eventually (Metric.ball_mem_nhds 0 one_pos),
        Filter.eventually_atTop.mpr ⟨1, fun _ h => h⟩] with n hn hnn
    simp only [Metric.mem_ball, dist_zero_right] at hn
    have hq_pos : (0:ℝ) < (↑n : ℝ) ^ (-(1:ℝ) / maxEdgeVertexRatio H) :=
      rpow_pos_of_pos (Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hnn)) _
    have hexp_neg : -(1:ℝ) / maxEdgeVertexRatio H < 0 :=
      div_neg_of_neg_of_pos (by linarith) hH
    have hq_le_one : (↑n : ℝ) ^ (-(1:ℝ) / maxEdgeVertexRatio H) ≤ 1 :=
      rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hnn : (1:ℝ) ≤ ↑n) (le_of_lt hexp_neg)

    have habs_ratio : |p n / (↑n : ℝ) ^ (-(1:ℝ) / maxEdgeVertexRatio H)| < 1 := hn
    calc |p n| = |p n / (↑n : ℝ) ^ (-(1:ℝ) / maxEdgeVertexRatio H)| *
            |(↑n : ℝ) ^ (-(1:ℝ) / maxEdgeVertexRatio H)| := by
          rw [← abs_mul, div_mul_cancel₀ (p n) hq_pos.ne']
      _ = |p n / (↑n : ℝ) ^ (-(1:ℝ) / maxEdgeVertexRatio H)| *
            (↑n : ℝ) ^ (-(1:ℝ) / maxEdgeVertexRatio H) := by
          rw [abs_of_pos hq_pos]
      _ ≤ 1 * 1 := by
          apply mul_le_mul (le_of_lt habs_ratio) hq_le_one (le_of_lt hq_pos) (by linarith)
      _ = 1 := one_mul 1
  apply squeeze_zero'
  ·
    filter_upwards [hp_abs_bound, Filter.eventually_atTop.mpr ⟨1, fun _ h => h⟩] with n hn hnn
    exact (hbound n hnn (p n) hn).1
  ·
    filter_upwards [hp_abs_bound, Filter.eventually_atTop.mpr ⟨1, fun _ h => h⟩] with n hn hnn
    exact (hbound n hnn (p n) hn).2
  ·
    exact hpow

/-- **Second moment side of Bollobás's threshold theorem.** If $p_n / n^{-1/m(H)} \to \infty$,
then the probability that $G(n, p_n)$ contains $H$ as a subgraph tends to $1$. -/
theorem second_moment_one_statement {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (H : SimpleGraph V) [DecidableRel H.Adj] [Fintype H.edgeSet]
    (hH : 0 < maxEdgeVertexRatio H)
    (p : ℕ → ℝ)
    (hp : Tendsto (fun n => p n / (n : ℝ) ^ (-(1 : ℝ) / maxEdgeVertexRatio H)) atTop atTop) :
    Tendsto (fun n => probContainsSubgraph H n (p n)) atTop (nhds 1) := by sorry

/-- **Bollobás's threshold theorem (Theorem 4.2.10, 1981).** For every graph $H$ with
positive maximum edge density $m(H)$, the function $n^{-1/m(H)}$ is a threshold for
the property that $G(n, p)$ contains $H$. -/
theorem bollobas_threshold {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (H : SimpleGraph V) [DecidableRel H.Adj] [Fintype H.edgeSet]
    (hH : 0 < maxEdgeVertexRatio H) :
    SubgraphThreshold.IsSubgraphThreshold
      (probContainsSubgraph H)
      (fun n => (n : ℝ) ^ (-(1 : ℝ) / maxEdgeVertexRatio H)) :=
  ⟨fun p hp => first_moment_zero_statement H hH p hp,
   fun p hp => second_moment_one_statement H hH p hp⟩

end Thresholds
