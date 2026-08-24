/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter11.Containers
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

set_option maxHeartbeats 400000

open SimpleGraph Finset Filter Real Asymptotics

namespace ErdosKleitmanRothschild

/-- The number of triangle-free (labelled) simple graphs on the vertex set $\{1, \dots, n\}$. -/
noncomputable def triangleFreeCount (n : ℕ) : ℕ :=
  Nat.card {G : SimpleGraph (Fin n) // G.CliqueFree 3}

/-- The number of subgraphs of a finite simple graph $G$ is at most $2^{|E(G)|}$, since
each subgraph corresponds to a subset of $E(G)$. -/
lemma subgraph_count_le (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Nat.card {H : SimpleGraph (Fin n) // H ≤ G} ≤ 2 ^ G.edgeFinset.card := by
  classical
  exact (Nat.card_le_card_of_injective
    (fun (x : {H : SimpleGraph (Fin n) // H ≤ G}) =>
      (⟨x.val.edgeFinset, Finset.mem_powerset.mpr
        (edgeFinset_subset_edgeFinset.mpr x.prop)⟩ : ↥(G.edgeFinset.powerset : Finset _)))
    (by intro ⟨_, _⟩ ⟨_, _⟩ h; exact Subtype.ext (edgeFinset_inj.mp (Subtype.mk.inj h)))).trans
    (by rw [Nat.card_eq_finsetCard, Finset.card_powerset])

/-- Upper bound on the number of triangle-free graphs derived from the container theorem:
for every $\varepsilon > 0$ there is $C > 0$ such that
$\#\{\text{triangle-free graphs on }[n]\} \leq n^{C n^{3/2}} \cdot 2^{(1/4 + \varepsilon) n^2}$. -/
theorem triangleFreeCount_upper_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      triangleFreeCount n ≤
        ⌈(n : ℝ) ^ (C * (n : ℝ) ^ ((3:ℝ)/2))⌉₊ * 2 ^ ⌈(1/4 + ε) * (n : ℝ) ^ 2⌉₊ := by

  obtain ⟨C, hC_pos, hContainers⟩ :=
    ContainersTriangleFree.containers_triangle_free ε hε
  refine ⟨C, hC_pos, fun n => ?_⟩
  classical
  obtain ⟨𝒞, h_size, h_edges, h_cover⟩ := hContainers n

  have h_nat_edges : ∀ G ∈ 𝒞, G.edgeFinset.card ≤ ⌈(1/4 + ε) * (n : ℝ) ^ 2⌉₊ := by
    intro G hG
    have key : (G.edgeFinset.card : ℝ) ≤ (1/4 + ε) * (n : ℝ) ^ 2 := by convert h_edges G hG
    exact_mod_cast key.trans (Nat.le_ceil _)

  have h_nat_size : 𝒞.card ≤ ⌈(n : ℝ) ^ (C * (↑n) ^ ((3:ℝ)/2))⌉₊ := by
    have key : (𝒞.card : ℝ) ≤ (n : ℝ) ^ (C * (↑n) ^ ((3:ℝ)/2)) := h_size
    exact_mod_cast key.trans (Nat.le_ceil _)

  let f : {H : SimpleGraph (Fin n) // H.CliqueFree 3} →
      (i : ↥𝒞) × {H : SimpleGraph (Fin n) // H ≤ i.val} :=
    fun ⟨H, hH⟩ => ⟨⟨(h_cover H hH).choose, ((h_cover H hH).choose_spec).1⟩,
                     ⟨H, ((h_cover H hH).choose_spec).2⟩⟩
  have hf : Function.Injective f := by
    intro ⟨H1, hH1⟩ ⟨H2, hH2⟩ heq
    simp only [f, Sigma.mk.inj_iff] at heq
    obtain ⟨heq1, heq2⟩ := heq
    rw [Subtype.heq_iff_coe_eq] at heq2
    · exact Subtype.ext heq2
    · intro a; constructor <;> intro ha
      · exact le_trans ha (by rw [Subtype.mk.injEq] at heq1; rw [heq1])
      · exact le_trans ha (by rw [Subtype.mk.injEq] at heq1; rw [← heq1])

  unfold triangleFreeCount
  calc Nat.card {H : SimpleGraph (Fin n) // H.CliqueFree 3}
      ≤ Nat.card ((i : ↥𝒞) × {H : SimpleGraph (Fin n) // H ≤ i.val}) :=
        Nat.card_le_card_of_injective f hf
    _ = ∑ i : ↥𝒞, Nat.card {H : SimpleGraph (Fin n) // H ≤ i.val} := Nat.card_sigma
    _ ≤ ∑ _ : ↥𝒞, 2 ^ ⌈(1/4 + ε) * (↑n) ^ 2⌉₊ := Finset.sum_le_sum (fun ⟨G, hG⟩ _ =>
        (subgraph_count_le n G).trans
          (Nat.pow_le_pow_right (by norm_num) (h_nat_edges G hG)))
    _ = Fintype.card ↥𝒞 * 2 ^ ⌈(1/4 + ε) * (↑n) ^ 2⌉₊ := by simp [Finset.sum_const]
    _ = 𝒞.card * 2 ^ ⌈(1/4 + ε) * (↑n) ^ 2⌉₊ := by rw [Fintype.card_coe]
    _ ≤ ⌈(↑n : ℝ) ^ (C * (↑n) ^ ((3:ℝ)/2))⌉₊ * 2 ^ ⌈(1/4 + ε) * (↑n) ^ 2⌉₊ := by
        gcongr

/-- The bipartite graph on $\{0, \dots, n-1\}$ with bipartition
$\{0, \dots, \lfloor n/2 \rfloor - 1\} \sqcup \{\lfloor n/2 \rfloor, \dots, n-1\}$ whose
edges are determined by the chosen subset $S$ of the bipartite edge set. Used as the lower
bound construction matching $2^{n^2/4}$ triangle-free graphs. -/
def bipartiteGraphOf (n : ℕ) (S : Finset (Fin (n / 2) × Fin (n - n / 2))) :
    SimpleGraph (Fin n) where
  Adj i j :=
    (∃ (a : Fin (n / 2)) (b : Fin (n - n / 2)),
      (a, b) ∈ S ∧ (i.val = a.val) ∧ (j.val = n / 2 + b.val)) ∨
    (∃ (a : Fin (n / 2)) (b : Fin (n - n / 2)),
      (a, b) ∈ S ∧ (j.val = a.val) ∧ (i.val = n / 2 + b.val))
  symm i j h := h.elim Or.inr Or.inl
  loopless := ⟨fun i h => by
    rcases h with ⟨a, b, _, ha, hb⟩ | ⟨a, b, _, ha, hb⟩ <;> omega⟩

end ErdosKleitmanRothschild
