/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card

set_option maxHeartbeats 1600000

open Finset SimpleGraph

namespace BipartiteDoubleCover

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A finset $S$ of vertices of $G$ is independent if no two distinct vertices in $S$ are
adjacent. -/
def IsIndepFinset {W : Type*} [DecidableEq W] (G : SimpleGraph W) [DecidableRel G.Adj]
    (S : Finset W) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬G.Adj u v

/-- Decidability of the independence predicate on finsets when adjacency in $G$ is decidable. -/
instance instDecIsIndepFinset {W : Type*} [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] : DecidablePred (IsIndepFinset G) := by
  intro S; unfold IsIndepFinset; exact inferInstance

/-- The finset of all independent vertex sets of $G$. -/
def indepSets {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] : Finset (Finset W) :=
  Finset.univ.filter (IsIndepFinset G)

/-- The number of independent vertex sets of $G$, denoted $i(G)$. -/
def numIndepSets {W : Type*} [Fintype W] [DecidableEq W] (G : SimpleGraph W)
    [DecidableRel G.Adj] : ℕ :=
  (indepSets G).card

/-- Swapping-trick injection from pairs of independent sets of $G$ into independent sets of the
bipartite double cover $G \times K_2$, establishing the inequality $i(G)^2 \le i(G \times K_2)$. -/
theorem swapping_trick_injection
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∃ f : Finset V × Finset V → Finset (V ⊕ V),
      (∀ p ∈ indepSets G ×ˢ indepSets G,
        f p ∈ indepSets G.bipartiteDoubleCover) ∧
      (∀ p₁ ∈ indepSets G ×ˢ indepSets G,
        ∀ p₂ ∈ indepSets G ×ˢ indepSets G,
          f p₁ = f p₂ → p₁ = p₂) := by sorry

/-- Lemma 10.4.13 (Zhao): the square of the number of independent sets of $G$ is at most the
number of independent sets of its bipartite double cover, $i(G)^2 \le i(G \times K_2)$. -/
theorem indep_sets_sq_le_bipartite_double_cover
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    numIndepSets G ^ 2 ≤ numIndepSets G.bipartiteDoubleCover := by
  classical
  simp only [numIndepSets, sq, ← Finset.card_product]
  obtain ⟨f, hf_mem, hf_inj⟩ := swapping_trick_injection G
  exact Finset.card_le_card_of_injOn f hf_mem hf_inj

end BipartiteDoubleCover
