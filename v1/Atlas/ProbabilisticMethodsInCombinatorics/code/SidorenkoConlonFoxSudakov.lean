/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.Sidorenko

set_option maxHeartbeats 400000

noncomputable section

namespace Sidorenko

/-- A bipartite graph $F$ on $A \sqcup B$ has a "universal vertex" if some vertex in $A$
is adjacent to every vertex of $B$, or some vertex in $B$ is adjacent to every vertex of
$A$. This is the hypothesis of the Conlon-Fox-Sudakov theorem on Sidorenko's conjecture. -/
def HasUniversalVertex {A : Type*} {B : Type*}
    (F : SimpleGraph (A ⊕ B)) : Prop :=
  (∃ a : A, ∀ b : B, F.Adj (Sum.inl a) (Sum.inr b)) ∨
  (∃ b : B, ∀ a : A, F.Adj (Sum.inr b) (Sum.inl a))

/-- Entropy-style hom-count lower bound underlying the Conlon-Fox-Sudakov theorem: for a
bipartite graph $F$ with a universal vertex,
$$ \mathrm{hom}(F, G) \ge \left( \frac{\mathrm{hom}(K_2, G)}{|V(G)|^2} \right)^{|E(F)|}
    \cdot |V(G)|^{|V(F)|}. $$ -/
theorem entropy_bound_hom_count
    {A : Type*} {B : Type*} {W : Type*}
    [Fintype A] [Fintype B] [Fintype W]
    [DecidableEq A] [DecidableEq B] [DecidableEq W]
    (F : SimpleGraph (A ⊕ B)) [DecidableRel F.Adj]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hF : HasUniversalVertex F)
    (hW : 0 < Fintype.card W) :
    (Nat.card (F →g G) : ℝ) ≥
      ((Nat.card ((⊤ : SimpleGraph (Fin 2)) →g G) : ℝ) /
        (Nat.card W : ℝ) ^ Nat.card (Fin 2)) ^ F.edgeFinset.card *
      (Nat.card W : ℝ) ^ (Nat.card (A ⊕ B)) := by sorry

/-- A bipartite graph with a universal vertex has at least one edge, so its edge set is
non-empty. Used to avoid degenerate corner cases. -/
theorem hasUniversalVertex_edgeFinset_pos
    {A : Type*} {B : Type*}
    [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (F : SimpleGraph (A ⊕ B)) [DecidableRel F.Adj]
    (hF : HasUniversalVertex F) :
    0 < F.edgeFinset.card := by
  rcases hF with ⟨a, ha⟩ | ⟨b, hb⟩
  · obtain ⟨b⟩ := ‹Nonempty B›
    have hadj := ha b
    have hmem : s(Sum.inl a, Sum.inr b) ∈ F.edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact hadj
    exact Finset.card_pos.mpr ⟨_, hmem⟩
  · obtain ⟨a⟩ := ‹Nonempty A›
    have hadj := hb a
    have hmem : s(Sum.inr b, Sum.inl a) ∈ F.edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact hadj
    exact Finset.card_pos.mpr ⟨_, hmem⟩

/-- Theorem 10.3.7 (Conlon-Fox-Sudakov 2010). Sidorenko's conjecture holds for any
bipartite graph $F$ that has a universal vertex on one side:
$\mathrm{hom\text{-}density}(F, G) \ge \mathrm{hom\text{-}density}(K_2, G)^{|E(F)|}$. -/
theorem sidorenko_of_hasUniversalVertex
    {A : Type*} {B : Type*} {W : Type*}
    [Fintype A] [Fintype B] [Fintype W]
    [DecidableEq A] [DecidableEq B] [DecidableEq W]
    [Nonempty A] [Nonempty B]
    (F : SimpleGraph (A ⊕ B)) [DecidableRel F.Adj]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hF : HasUniversalVertex F) :
    homDensity F G ≥
      (homDensity (⊤ : SimpleGraph (Fin 2)) G) ^ F.edgeFinset.card := by
  unfold homDensity
  by_cases hW : Fintype.card W = 0
  ·
    have hW0 : (Nat.card W : ℝ) = 0 := by
      rw [Nat.card_eq_fintype_card]; exact_mod_cast hW

    have hV_ne : Nat.card (A ⊕ B) ≠ 0 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_sum]
      rcases hF with ⟨a, _⟩ | ⟨b, _⟩
      · have := Fintype.card_pos_iff.mpr ⟨a⟩; omega
      · have := Fintype.card_pos_iff.mpr ⟨b⟩; omega

    have he_ne : F.edgeFinset.card ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (hasUniversalVertex_edgeFinset_pos F hF)

    have h_fin2 : Nat.card (Fin 2) ≠ 0 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega

    rw [show (Nat.card W : ℝ) ^ Nat.card (A ⊕ B) = 0 from by rw [hW0]; exact zero_pow hV_ne]
    rw [show (Nat.card W : ℝ) ^ Nat.card (Fin 2) = 0 from by rw [hW0]; exact zero_pow h_fin2]

    rw [div_zero, div_zero, zero_pow he_ne]
  ·
    have hW_pos : 0 < Fintype.card W := Nat.pos_of_ne_zero hW

    have hW_cast_pos : (0 : ℝ) < (Nat.card W : ℝ) ^ Nat.card (A ⊕ B) := by
      apply pow_pos
      rw [Nat.card_eq_fintype_card]
      exact_mod_cast hW_pos

    rw [ge_iff_le, le_div_iff₀ hW_cast_pos]

    exact entropy_bound_hom_count F G hF hW_pos

end Sidorenko
