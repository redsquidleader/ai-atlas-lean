/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.CombinatorialOptimization.code.Matching.Berge

open SimpleGraph

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def augPathLengths (G : SimpleGraph V) (M : G.Subgraph) : Set ℕ∞ :=
  { n : ℕ∞ | ∃ (u v : V) (p : G.Walk u v), p.IsAugmentingPath M ∧ (p.length : ℕ∞) = n }

noncomputable def shortestAugPathLength (G : SimpleGraph V) (M : G.Subgraph) : ℕ∞ :=
  sInf (augPathLengths G M)

structure VertexDisjointAugPaths (G : SimpleGraph V) (M : G.Subgraph) (k : ℕ) where
  ι : Type*
  src : ι → V
  tgt : ι → V
  path : (i : ι) → G.Walk (src i) (tgt i)
  isAug : ∀ i, (path i).IsAugmentingPath M
  hasLen : ∀ i, (path i).length = k
  disjoint : ∀ i j, i ≠ j →
    List.Disjoint ((path i).support) ((path j).support)

def VertexDisjointAugPaths.IsMaximal {G : SimpleGraph V} {M : G.Subgraph} {k : ℕ}
    (paths : VertexDisjointAugPaths G M k) : Prop :=
  ∀ (u v : V) (p : G.Walk u v),
    p.IsAugmentingPath M → p.length = k →
    ∃ i, ¬ List.Disjoint p.support ((paths.path i).support)

def IsAugmentationAlongPaths {G : SimpleGraph V} (M M' : G.Subgraph) {k : ℕ}
    (paths : VertexDisjointAugPaths G M k) : Prop :=
  M'.IsMatching ∧
  (∀ e ∈ M'.edgeSet, e ∉ M.edgeSet →
    ∃ i, e ∈ (paths.path i).edges.toFinset) ∧
  (∀ e ∈ M.edgeSet, e ∉ M'.edgeSet →
    ∃ i, e ∈ (paths.path i).edges.toFinset) ∧
  (∀ v : V, (∀ i, v ∉ (paths.path i).support) →
    (v ∈ M.verts ↔ v ∈ M'.verts))

theorem symm_diff_graph_decomposition
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (M M' : G.Subgraph) (hM : M.IsMatching)
    (k : ℕ) (hk : shortestAugPathLength G M = ↑k)
    (paths : VertexDisjointAugPaths G M k)
    (haug : IsAugmentationAlongPaths M M' paths)
    {u v : V} (Q : G.Walk u v) (hQ : Q.IsAugmentingPath M')
    (hle : Q.length ≤ k) :
    ∃ (n : ℕ) (_ : n ≥ 1)
      (srcs : Fin n → V) (tgts : Fin n → V)
      (Rs : (j : Fin n) → G.Walk (srcs j) (tgts j)),
      (∀ j, (Rs j).IsAugmentingPath M) ∧
      (∑ j : Fin n, (Rs j).length ≤ n * k) ∧
      (∀ j : Fin n, ∀ i, List.Disjoint (Rs j).support ((paths.path i).support)) := by sorry

theorem symm_diff_decomposition_length_bound
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (M M' : G.Subgraph) (hM : M.IsMatching)
    (k : ℕ) (hk : shortestAugPathLength G M = ↑k)
    (paths : VertexDisjointAugPaths G M k)
    (haug : IsAugmentationAlongPaths M M' paths)
    {u v : V} (Q : G.Walk u v) (hQ : Q.IsAugmentingPath M')
    (hle : Q.length ≤ k) :
    ∃ (a b : V) (R : G.Walk a b),
      R.IsAugmentingPath M ∧ R.length ≤ k ∧
      (∀ i, List.Disjoint R.support ((paths.path i).support)) := by


  have decomp : ∃ (n : ℕ) (_ : n ≥ 1)
      (srcs : Fin n → V) (tgts : Fin n → V)
      (Rs : (j : Fin n) → G.Walk (srcs j) (tgts j)),
      (∀ j, (Rs j).IsAugmentingPath M) ∧
      (∑ j : Fin n, (Rs j).length ≤ n * k) ∧
      (∀ j : Fin n, ∀ i, List.Disjoint (Rs j).support ((paths.path i).support)) := by
    exact symm_diff_graph_decomposition M M' hM k hk paths haug Q hQ hle

  obtain ⟨n, hn, srcs, tgts, Rs, hRs_aug, hRs_total, hRs_disj⟩ := decomp
  suffices ∃ j : Fin n, (Rs j).length ≤ k from by
    obtain ⟨j, hj⟩ := this
    exact ⟨srcs j, tgts j, Rs j, hRs_aug j, hj, hRs_disj j⟩
  by_contra hall
  push_neg at hall
  have hsum : n * k < ∑ j : Fin n, (Rs j).length := by
    calc n * k = ∑ _ : Fin n, k := by simp [Finset.sum_const]
      _ < ∑ j : Fin n, (Rs j).length := by
        apply Finset.sum_lt_sum
        · intro j _; exact Nat.le_of_lt (hall j)
        · exact ⟨⟨0, by omega⟩, Finset.mem_univ _, hall ⟨0, by omega⟩⟩
  omega

theorem aug_path_length_gt_of_maximal_phase
    {G : SimpleGraph V} (M M' : G.Subgraph) (hM : M.IsMatching)
    (k : ℕ) (hk : shortestAugPathLength G M = ↑k)
    (paths : VertexDisjointAugPaths G M k)
    (hmax : paths.IsMaximal)
    (haug : IsAugmentationAlongPaths M M' paths)
    {u v : V} (Q : G.Walk u v) (hQ : Q.IsAugmentingPath M') :
    k < Q.length := by
  by_contra hle
  push_neg at hle


  obtain ⟨a, b, R, hR_aug, hR_len, hR_disj⟩ :=
    symm_diff_decomposition_length_bound M M' hM k hk paths haug Q hQ hle

  have hR_eq : R.length = k := by
    apply le_antisymm hR_len

    have hmem : (↑(R.length) : ℕ∞) ∈ augPathLengths G M :=
      ⟨a, b, R, hR_aug, rfl⟩
    have hsInf := sInf_le hmem
    unfold shortestAugPathLength at hk
    rw [hk] at hsInf
    exact ENat.coe_le_coe.mp hsInf


  obtain ⟨i, hi⟩ := hmax a b R hR_aug hR_eq
  exact hi (hR_disj i)

theorem shortest_aug_path_length_strict_increase
    {G : SimpleGraph V} (M M' : G.Subgraph) (hM : M.IsMatching)
    (k : ℕ) (hk : shortestAugPathLength G M = ↑k)
    (paths : VertexDisjointAugPaths G M k)
    (hmax : paths.IsMaximal)
    (haug : IsAugmentationAlongPaths M M' paths) :
    shortestAugPathLength G M' > ↑k := by
  unfold shortestAugPathLength
  by_cases hne : (augPathLengths G M').Nonempty
  ·
    have succ_eq : Order.succ (↑k : ℕ∞) = ↑(k + 1 : ℕ) := by
      rw [Order.succ_eq_add_one]; push_cast; ring
    have hk1 : (↑(k + 1) : ℕ∞) ≤ sInf (augPathLengths G M') := by
      apply le_sInf
      intro b hb
      obtain ⟨u, v, Q, hQ, hlen⟩ := hb
      rw [← hlen, ← succ_eq]
      exact Order.succ_le_of_lt
        (ENat.coe_lt_coe.mpr
          (aug_path_length_gt_of_maximal_phase M M' hM k hk paths hmax haug Q hQ))
    calc (k : ℕ∞) < ↑(k + 1) := ENat.coe_lt_coe.mpr (Nat.lt_add_one k)
      _ ≤ sInf (augPathLengths G M') := hk1
  ·
    simp only [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, sInf_empty]
    exact le_top.lt_of_ne (ENat.coe_ne_top k)

end SimpleGraph
