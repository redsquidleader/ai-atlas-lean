/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.CombinatorialOptimization.code.Matching.ShortestAugPathPhase

open SimpleGraph

namespace SimpleGraph

universe u w

structure HopcroftKarpExecution {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) where
  numPhases : ℕ
  matching : Fin (numPhases + 1) → G.Subgraph
  isMatching : ∀ i, (matching i).IsMatching
  isFinalMaximum : ∀ M' : G.Subgraph, M'.IsMatching →
    M'.edgeSet.ncard ≤ (matching ⟨numPhases, Nat.lt_succ_of_le le_rfl⟩).edgeSet.ncard
  size_strictly_increases : ∀ i : Fin numPhases,
    (matching ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩).edgeSet.ncard <
    (matching ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩).edgeSet.ncard
  shortestLen : Fin numPhases → ℕ
  shortestLen_spec : ∀ i : Fin numPhases,
    shortestAugPathLength G (matching ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) =
      ↑(shortestLen i)
  paths : (i : Fin numPhases) →
    VertexDisjointAugPaths.{u, w} G (matching ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) (shortestLen i)
  paths_maximal : ∀ i : Fin numPhases, (paths i).IsMaximal
  isAugmentation : ∀ i : Fin numPhases,
    IsAugmentationAlongPaths
      (matching ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
      (matching ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (paths i)

theorem HopcroftKarpExecution.shortestLen_strict_mono
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (exec : HopcroftKarpExecution.{u, w} G)
    (i : Fin exec.numPhases) (hi : i.val + 1 < exec.numPhases) :
    exec.shortestLen i < exec.shortestLen ⟨i.val + 1, hi⟩ := by
  have h_inc := shortest_aug_path_length_strict_increase
    (exec.matching ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    (exec.matching ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    (exec.isMatching ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    (exec.shortestLen i)
    (exec.shortestLen_spec i)
    (exec.paths i)
    (exec.paths_maximal i)
    (exec.isAugmentation i)
  have h_spec := exec.shortestLen_spec ⟨i.val + 1, hi⟩
  have heq : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (exec.numPhases + 1)) =
             ⟨i.val + 1, Nat.lt_succ_of_lt hi⟩ := by
    ext; rfl
  rw [heq] at h_inc
  rw [h_spec] at h_inc
  exact ENat.coe_lt_coe.mp h_inc

lemma HopcroftKarpExecution.shortestLen_odd
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (exec : HopcroftKarpExecution.{u, w} G)
    (i : Fin exec.numPhases) :
    Odd (exec.shortestLen i) := by
  have hspec := exec.shortestLen_spec i


  have hne : (augPathLengths G (exec.matching ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    unfold shortestAugPathLength at hspec
    rw [hempty, sInf_empty] at hspec
    exact absurd hspec (by simp [ENat.top_ne_coe])
  have hmem := csInf_mem hne
  unfold shortestAugPathLength at hspec

  rw [hspec] at hmem

  obtain ⟨u, v, p, haug, hlen⟩ := hmem
  have hodd := augmenting_path_odd_length haug
  rw [p.length_edges] at hodd
  have hlen_eq : p.length = exec.shortestLen i := by
    have := ENat.coe_inj.mp hlen
    exact this
  rwa [hlen_eq] at hodd

theorem HopcroftKarpExecution.shortestLen_lower_bound
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (exec : HopcroftKarpExecution.{u, w} G)
    (i : Fin exec.numPhases) :
    2 * i.val + 1 ≤ exec.shortestLen i := by
  obtain ⟨k, hk⟩ := i
  induction k with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add]
    exact Odd.pos (exec.shortestLen_odd ⟨0, hk⟩)
  | succ j ih =>
    have hj_lt : j < exec.numPhases := Nat.lt_of_succ_lt hk
    have ih_applied := ih hj_lt


    have hmono := exec.shortestLen_strict_mono ⟨j, hj_lt⟩ hk
    have hodd_j := exec.shortestLen_odd ⟨j, hj_lt⟩
    have hodd_succ := exec.shortestLen_odd ⟨j + 1, hk⟩

    have hstep : exec.shortestLen ⟨j, hj_lt⟩ + 2 ≤ exec.shortestLen ⟨j + 1, hk⟩ := by
      have hm := hodd_j
      have hn := hodd_succ
      obtain ⟨a, ha⟩ := hm
      obtain ⟨b, hb⟩ := hn
      simp only [ha, hb] at hmono ⊢
      omega
    linarith

theorem deficit_bound_from_shortest_aug_path
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (M : G.Subgraph) (hM : M.IsMatching)
    (ℓ : ℕ) (hℓ : ∀ (u v : V) (p : G.Walk u v), p.IsAugmentingPath M → ℓ ≤ p.length)
    (M' : G.Subgraph) (hM' : M'.IsMatching) :
    M'.edgeSet.ncard ≤ M.edgeSet.ncard + Fintype.card V / (ℓ + 1) := by sorry

lemma HopcroftKarpExecution.matching_size_growth
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (exec : HopcroftKarpExecution.{u, w} G)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ exec.numPhases) :
    (exec.matching ⟨i, Nat.lt_succ_of_le (hij.trans hj)⟩).edgeSet.ncard + (j - i) ≤
    (exec.matching ⟨j, Nat.lt_succ_of_le hj⟩).edgeSet.ncard := by

  induction hij with
  | refl => simp
  | @step m him ih =>

    have hm_le : m ≤ exec.numPhases := Nat.le_of_succ_le hj
    have ih_applied := ih hm_le
    have hm_lt : m < exec.numPhases := Nat.lt_of_succ_le hj
    have hstep := exec.size_strictly_increases ⟨m, hm_lt⟩

    have heq1 : (exec.matching ⟨m, Nat.lt_succ_of_lt hm_lt⟩).edgeSet.ncard =
                (exec.matching ⟨m, Nat.lt_succ_of_le hm_le⟩).edgeSet.ncard := by congr 2
    have heq2 : (exec.matching ⟨m + 1, Nat.succ_lt_succ hm_lt⟩).edgeSet.ncard =
                (exec.matching ⟨m + 1, Nat.lt_succ_of_le hj⟩).edgeSet.ncard := by congr 2
    have heq3 : (exec.matching ⟨i, Nat.lt_succ_of_le (Nat.le_trans him hm_le)⟩).edgeSet.ncard =
                (exec.matching ⟨i, Nat.lt_succ_of_le (Nat.le_trans (Nat.le_succ_of_le him) hj)⟩).edgeSet.ncard := by
      congr 2
    rw [heq1, heq2] at hstep
    rw [heq3] at ih_applied


    have hi_le_m : i ≤ m := him
    have hsub : m + 1 - i = (m - i) + 1 := Nat.succ_sub hi_le_m
    linarith [hsub]

theorem hopcroft_karp_deficit_after_sqrt_phases
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (exec : HopcroftKarpExecution.{u, w} G)
    (hphases : Nat.sqrt (Fintype.card V) ≤ exec.numPhases) :
    ∀ M' : G.Subgraph, M'.IsMatching →
      M'.edgeSet.ncard ≤
        (exec.matching ⟨Nat.sqrt (Fintype.card V),
          Nat.lt_succ_of_le hphases⟩).edgeSet.ncard +
        Nat.sqrt (Fintype.card V) := by
  set s := Nat.sqrt (Fintype.card V)
  set n := Fintype.card V
  intro M' hM'

  rcases Nat.eq_or_lt_of_le hphases with hs_eq | hs_lt
  ·
    have hfin : (exec.matching ⟨s, Nat.lt_succ_of_le hphases⟩) =
                exec.matching ⟨exec.numPhases, Nat.lt_succ_of_le le_rfl⟩ := by
      congr 1; ext; exact hs_eq
    rw [hfin]
    have hmax := exec.isFinalMaximum M' hM'
    linarith
  ·

    have hs_phase : s < exec.numPhases := hs_lt
    have hlen_lb := exec.shortestLen_lower_bound ⟨s, hs_phase⟩


    have hspec := exec.shortestLen_spec ⟨s, hs_phase⟩

    have hall_paths : ∀ (u v : V) (p : G.Walk u v),
        p.IsAugmentingPath (exec.matching ⟨s, Nat.lt_succ_of_lt hs_phase⟩) →
        (2 * s + 1) ≤ p.length := by
      intro u v p hp

      have hmem : (↑(p.length) : ℕ∞) ∈ augPathLengths G
          (exec.matching ⟨s, Nat.lt_succ_of_lt hs_phase⟩) :=
        ⟨u, v, p, hp, rfl⟩
      have hsInf := sInf_le hmem
      unfold shortestAugPathLength at hspec
      rw [hspec] at hsInf
      have hle_shortest : exec.shortestLen ⟨s, hs_phase⟩ ≤ p.length :=
        ENat.coe_le_coe.mp hsInf
      linarith

    have hMs_matching := exec.isMatching ⟨s, Nat.lt_succ_of_lt hs_phase⟩

    have heq_match : (exec.matching ⟨s, Nat.lt_succ_of_lt hs_phase⟩) =
                     (exec.matching ⟨s, Nat.lt_succ_of_le hphases⟩) := by
      congr 1
    have hall_paths' : ∀ (u v : V) (p : G.Walk u v),
        p.IsAugmentingPath (exec.matching ⟨s, Nat.lt_succ_of_le hphases⟩) →
        (2 * s + 1) ≤ p.length := by
      rw [← heq_match]; exact hall_paths
    have hMs_matching' : (exec.matching ⟨s, Nat.lt_succ_of_le hphases⟩).IsMatching := by
      rw [← heq_match]; exact hMs_matching
    have hdeficit := deficit_bound_from_shortest_aug_path
      (exec.matching ⟨s, Nat.lt_succ_of_le hphases⟩)
      hMs_matching'
      (2 * s + 1)
      hall_paths'
      M' hM'


    suffices h : n / (2 * s + 1 + 1) ≤ s by linarith [hdeficit, h]
    have hn_bound : n < (s + 1) ^ 2 := Nat.lt_succ_sqrt' n
    have hn_bound' : n < (2 * s + 1 + 1) * (s + 1) := by
      have : (s + 1) ^ 2 ≤ (2 * s + 1 + 1) * (s + 1) := by
        have : (s + 1) ^ 2 = (s + 1) * (s + 1) := by ring
        rw [this]
        exact Nat.mul_le_mul_right _ (by omega)
      linarith
    have hdiv : n / (2 * s + 1 + 1) < s + 1 := Nat.div_lt_of_lt_mul hn_bound'
    omega

theorem hopcroft_karp_phase_bound
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (exec : HopcroftKarpExecution.{u, w} G) :
    exec.numPhases ≤ 2 * Nat.sqrt (Fintype.card V) + 1 := by
  set s := Nat.sqrt (Fintype.card V)
  by_cases h : exec.numPhases ≤ s
  · omega
  · push_neg at h
    have hphases : s ≤ exec.numPhases := Nat.le_of_lt h
    have hdeficit := hopcroft_karp_deficit_after_sqrt_phases exec hphases
      (exec.matching ⟨exec.numPhases, Nat.lt_succ_of_le le_rfl⟩)
      (exec.isMatching ⟨exec.numPhases, Nat.lt_succ_of_le le_rfl⟩)

    have hgrowth := exec.matching_size_growth s exec.numPhases hphases le_rfl


    have heq_s : (exec.matching ⟨s, Nat.lt_succ_of_le (Nat.le_trans hphases le_rfl)⟩).edgeSet.ncard =
                 (exec.matching ⟨s, Nat.lt_succ_of_le hphases⟩).edgeSet.ncard := by congr 2


    have h_sub_le : exec.numPhases - s ≤ s := by
      have h1 : (exec.matching ⟨s, Nat.lt_succ_of_le (Nat.le_trans hphases le_rfl)⟩).edgeSet.ncard +
                (exec.numPhases - s) ≤
                (exec.matching ⟨s, Nat.lt_succ_of_le hphases⟩).edgeSet.ncard + s := by
        calc (exec.matching ⟨s, Nat.lt_succ_of_le (Nat.le_trans hphases le_rfl)⟩).edgeSet.ncard +
              (exec.numPhases - s)
            ≤ (exec.matching ⟨exec.numPhases, Nat.lt_succ_of_le le_rfl⟩).edgeSet.ncard := hgrowth
          _ ≤ (exec.matching ⟨s, Nat.lt_succ_of_le hphases⟩).edgeSet.ncard + s := hdeficit
      linarith [heq_s]
    omega

end SimpleGraph
