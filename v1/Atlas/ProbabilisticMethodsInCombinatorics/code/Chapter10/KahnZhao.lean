/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Analysis.SpecialFunctions.Pow.Real
set_option maxHeartbeats 400000

namespace SimpleGraph

/-- Decidability of adjacency in the complete bipartite graph on $V \sqcup W$. -/
instance completeBipartiteGraph.instDecidableRel (V W : Type*) [DecidableEq V] [DecidableEq W] :
    DecidableRel (completeBipartiteGraph V W).Adj := by
  intro x y
  simp only [completeBipartiteGraph]
  exact instDecidableOr

/-- $i(G)$: the number of independent sets in a finite simple graph $G$, counting the
empty set. -/
noncomputable def numIndSets {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  (Finset.univ.filter (fun s : Finset V =>
    ∀ u ∈ s, ∀ v ∈ s, u ≠ v → ¬G.Adj u v)).card

/-- The number of independent sets in $K_{d, d}$ equals $2^{d+1} - 1$: a nonempty
independent set is any nonempty subset of either side. -/
theorem numIndSets_completeBipartiteGraph (d : ℕ) (hd : 0 < d) :
    numIndSets (completeBipartiteGraph (Fin d) (Fin d)) = 2 ^ (d + 1) - 1 := by sorry

/-- The independent-set count of $G$ squared is at most that of its bipartite double
cover $G \times K_2$: $i(G)^2 \leq i(G \times K_2)$. -/
theorem numIndSets_sq_le_numIndSets_bipartiteDoubleCover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (numIndSets G : ℝ) ^ (2 : ℝ) ≤ (numIndSets G.bipartiteDoubleCover : ℝ) := by sorry

/-- Kahn-Zhao for bipartite graphs (Kahn 2001): for a $d$-regular bipartite graph $G$
on $n$ vertices, $i(G) \leq i(K_{d, d})^{n / (2d)}$. -/
theorem kahn_zhao_bipartite
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (hreg : G.IsRegularOfDegree d) (hbip : G.IsBipartite) :
    (numIndSets G : ℝ) ≤ (numIndSets (completeBipartiteGraph (Fin d) (Fin d)) : ℝ) ^
      ((Fintype.card V : ℝ) / (2 * (d : ℝ))) := by sorry

/-- Theorem 10.4.12 (Kahn-Zhao): for any $d$-regular graph $G$ on $n$ vertices,
$i(G) \leq i(K_{d, d})^{n / (2d)}$, deduced from the bipartite case via the bipartite
double-cover trick. -/
theorem kahn_zhao
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (d : ℕ) (hd : 0 < d) (hreg : G.IsRegularOfDegree d) :
    (numIndSets G : ℝ) ≤ (numIndSets (completeBipartiteGraph (Fin d) (Fin d)) : ℝ) ^
      ((Fintype.card V : ℝ) / (2 * (d : ℝ))) := by sorry

end SimpleGraph
