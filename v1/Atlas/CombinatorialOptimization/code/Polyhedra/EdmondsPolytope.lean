/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open SimpleGraph Finset BigOperators Classical

noncomputable section

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

def incidentEdgeFinset (v : V) : Finset G.edgeSet :=
  (G.edgeFinset.filter (fun e => v ∈ e)).subtype (fun e => e ∈ G.edgeSet)

def edgeCutFinset (S : Finset V) : Finset G.edgeSet :=
  (G.edgeFinset.filter (fun e =>
    ∃ a ∈ S, ∃ b ∉ S, e = s(a, b))).subtype (fun e => e ∈ G.edgeSet)

def perfectMatchingIndicators : Set (G.edgeSet → ℝ) :=
  {x | ∃ (M : G.Subgraph) (_ : M.IsPerfectMatching),
    x = fun (e : G.edgeSet) => if (e : Sym2 V) ∈ M.edgeSet then (1 : ℝ) else 0}

def perfectMatchingPolytope : Set (G.edgeSet → ℝ) :=
  (convexHull ℝ) (perfectMatchingIndicators G)

def edmondsPolytope : Set (G.edgeSet → ℝ) :=
  {x | (∀ e : G.edgeSet, 0 ≤ x e) ∧
       (∀ v : V, ∑ e ∈ incidentEdgeFinset G v, x e = 1) ∧
       (∀ S : Finset V, Odd S.card →
         ∑ e ∈ edgeCutFinset G S, x e ≥ 1)}

lemma mem_incidentEdgeFinset_iff (v : V) (e : G.edgeSet) :
    e ∈ incidentEdgeFinset G v ↔ v ∈ (e : Sym2 V) := by
  simp [incidentEdgeFinset, Finset.mem_subtype, Finset.mem_filter,
        SimpleGraph.mem_edgeFinset]

lemma convex_edmondsPolytope : Convex ℝ (edmondsPolytope G) := by
  intro x hx y hy a b ha hb hab
  simp only [edmondsPolytope, Set.mem_setOf_eq] at *
  obtain ⟨hx_nn, hx_deg, hx_odd⟩ := hx
  obtain ⟨hy_nn, hy_deg, hy_odd⟩ := hy
  refine ⟨?_, ?_, ?_⟩
  · intro e
    apply add_nonneg
    · exact mul_nonneg ha (hx_nn e)
    · exact mul_nonneg hb (hy_nn e)
  · intro v
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        hx_deg v, hy_deg v]
    linarith
  · intro S hS
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ge_iff_le]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    nlinarith [hx_odd S hS, hy_odd S hS]

lemma pm_indicator_satisfies_degree (M : G.Subgraph) (hM : M.IsPerfectMatching) (v : V) :
    ∑ e ∈ incidentEdgeFinset G v,
      (fun (e : G.edgeSet) => if (e : Sym2 V) ∈ M.edgeSet then (1 : ℝ) else 0) e = 1 := by
  simp only
  have hsp := hM.2 v
  obtain ⟨w, hw, huniq⟩ := hM.1 hsp
  have hadj_G : G.Adj v w := M.adj_sub hw
  have hedge_in_G : s(v, w) ∈ G.edgeSet := (mem_edgeSet G).mpr hadj_G
  have hedge_in_M : s(v, w) ∈ M.edgeSet :=
    SimpleGraph.Subgraph.mem_edgeSet.mpr hw
  set e₀ : G.edgeSet := ⟨s(v, w), hedge_in_G⟩
  have he₀_mem : e₀ ∈ incidentEdgeFinset G v := by
    rw [mem_incidentEdgeFinset_iff]
    exact Sym2.mem_mk_left v w
  rw [Finset.sum_eq_single e₀
      (fun e he hne => by
        simp only [ite_eq_right_iff, one_ne_zero]
        intro he_in_M
        exfalso; apply hne
        have hv_in_e : v ∈ (e : Sym2 V) := (mem_incidentEdgeFinset_iff G v e).mp he
        have ⟨a, b, hab⟩ : ∃ a b, (e : Sym2 V) = s(a, b) :=
          Sym2.ind (fun a b => ⟨a, b, rfl⟩) (e : Sym2 V)
        have heq : (e : Sym2 V) = s(v, w) := by
          rw [hab] at hv_in_e he_in_M ⊢
          rw [Sym2.mem_iff] at hv_in_e
          rw [SimpleGraph.Subgraph.mem_edgeSet] at he_in_M
          rcases hv_in_e with hva | hvb
          · subst hva; rw [huniq b he_in_M]
          · subst hvb; rw [huniq a (M.adj_symm he_in_M), Sym2.eq_swap]
        exact Subtype.ext heq)
      (fun habs => absurd he₀_mem habs)]
  simp only [e₀, hedge_in_M, ite_true]

lemma pm_indicator_satisfies_oddset (M : G.Subgraph) (hM : M.IsPerfectMatching) (S : Finset V)
    (hS : Odd S.card) :
    ∑ e ∈ edgeCutFinset G S,
      (fun (e : G.edgeSet) => if (e : Sym2 V) ∈ M.edgeSet then (1 : ℝ) else 0) e ≥ 1 := by
  simp only

  suffices h : ∃ e ∈ edgeCutFinset G S, (e : Sym2 V) ∈ M.edgeSet by
    obtain ⟨e, he_cut, he_M⟩ := h
    have hnn : ∀ i ∈ edgeCutFinset G S,
        (0 : ℝ) ≤ (if (i : Sym2 V) ∈ M.edgeSet then (1 : ℝ) else 0) := by
      intro i _; split_ifs <;> linarith
    have hle := Finset.single_le_sum hnn he_cut
    simp only [he_M, ite_true] at hle
    linarith

  suffices hexists : ∃ v ∈ S, ∃ w, M.Adj v w ∧ w ∉ S by
    obtain ⟨v, hv, w, hadj, hw⟩ := hexists
    have hedge_G : G.Adj v w := M.adj_sub hadj
    have hmem_G : s(v, w) ∈ G.edgeSet := (mem_edgeSet G).mpr hedge_G
    refine ⟨⟨s(v, w), hmem_G⟩, ?_, ?_⟩
    · simp only [edgeCutFinset, Finset.mem_subtype, Finset.mem_filter,
                  SimpleGraph.mem_edgeFinset]
      exact ⟨hedge_G, v, hv, w, hw, rfl⟩
    · exact SimpleGraph.Subgraph.mem_edgeSet.mpr hadj

  by_contra hall
  push_neg at hall


  have hS_even : Even S.card := by


    let M' := M.induce (↑S : Set V)
    have hM'_matching : M'.IsMatching := by
      intro v hv
      have hv_S : v ∈ S := hv
      obtain ⟨w, hw, huniq⟩ := hM.1 (hM.2 v)
      have hw_S : w ∈ S := hall v hv_S w hw
      refine ⟨w, ?_, ?_⟩
      · show M'.Adj v w
        exact ⟨hv_S, hw_S, hw⟩
      · intro w' hw'
        exact huniq w' hw'.2.2
    have hverts : M'.verts.toFinset = S := by
      ext v; simp [M', SimpleGraph.Subgraph.induce]
    have heven := hM'_matching.even_card
    rw [hverts] at heven
    exact heven
  exact absurd hS_even (Nat.not_even_iff_odd.mpr hS)

lemma pm_indicators_subset_edmondsPolytope :
    perfectMatchingIndicators G ⊆ edmondsPolytope G := by
  intro x hx
  obtain ⟨M, hM, hx_eq⟩ := hx
  subst hx_eq
  refine ⟨?_, ?_, ?_⟩
  · intro e; simp only; split_ifs <;> linarith
  · exact pm_indicator_satisfies_degree G M hM
  · exact pm_indicator_satisfies_oddset G M hM

lemma perfectMatchingPolytope_subset_edmondsPolytope :
    perfectMatchingPolytope G ⊆ edmondsPolytope G :=
  convexHull_min (pm_indicators_subset_edmondsPolytope G) (convex_edmondsPolytope G)

lemma integral_edmondsPolytope_mem_pm (x : G.edgeSet → ℝ)
    (hdeg : ∀ v : V, ∑ e ∈ incidentEdgeFinset G v, x e = 1)
    (hint : ∀ e : G.edgeSet, x e = 0 ∨ x e = 1) :
    x ∈ perfectMatchingIndicators G := by

  let M : G.Subgraph := {
    verts := Set.univ
    Adj := fun u v => ∃ (h : G.Adj u v), x ⟨s(u, v), (mem_edgeSet G).mpr h⟩ = 1
    adj_sub := fun {u v} ⟨h, _⟩ => h
    edge_vert := fun _ => Set.mem_univ _
    symm := fun u v ⟨hadj, hx⟩ => ⟨G.symm hadj, by
      have : (⟨s(v, u), (mem_edgeSet G).mpr (G.symm hadj)⟩ : G.edgeSet) =
           ⟨s(u, v), (mem_edgeSet G).mpr hadj⟩ := Subtype.ext Sym2.eq_swap
      rw [this]; exact hx⟩
  }

  have hM_iff : ∀ (e : G.edgeSet), (e : Sym2 V) ∈ M.edgeSet ↔ x e = 1 := by
    intro ⟨e_val, he_mem⟩
    revert he_mem
    refine Sym2.ind (fun a b he_mem => ?_) e_val
    simp only [Subgraph.mem_edgeSet]
    show (∃ (h : G.Adj a b), x ⟨s(a, b), (mem_edgeSet G).mpr h⟩ = 1) ↔
         x ⟨s(a, b), he_mem⟩ = 1
    constructor
    · rintro ⟨_, hx⟩; exact hx
    · intro hx; exact ⟨(mem_edgeSet G).mp he_mem, hx⟩
  refine ⟨M, ⟨?_, fun v => Set.mem_univ v⟩, ?_⟩
  ·
    intro v _

    have huniq_edge : ∃! e, e ∈ incidentEdgeFinset G v ∧ x e = 1 := by
      have hexists : ∃ e ∈ incidentEdgeFinset G v, x e = 1 := by
        by_contra h; push_neg at h
        linarith [hdeg v, Finset.sum_eq_zero (fun e he => (hint e).resolve_right (h e he))]
      obtain ⟨j, hj, hfj⟩ := hexists
      refine ⟨j, ⟨hj, hfj⟩, ?_⟩
      intro k ⟨hk, hfk⟩
      by_contra hjk
      have hjk' : j ≠ k := fun h => hjk h.symm
      linarith [Finset.sum_le_sum_of_subset_of_nonneg
        (show ({j, k} : Finset G.edgeSet) ⊆ incidentEdgeFinset G v from
          by simp [Finset.subset_iff]; exact ⟨hj, hk⟩)
        (fun e _ _ => show 0 ≤ x e from by rcases hint e with h | h <;> linarith),
        show x j + x k = ∑ e ∈ ({j, k} : Finset G.edgeSet), x e from
          (Finset.sum_pair hjk').symm,
        hdeg v]
    obtain ⟨e₀, ⟨he₀_inc, hxe₀⟩, he₀_uniq⟩ := huniq_edge
    have hv_in_e₀ := (mem_incidentEdgeFinset_iff G v e₀).mp he₀_inc
    obtain ⟨a, b, hab⟩ : ∃ a b, (e₀ : Sym2 V) = s(a, b) :=
      Sym2.ind (fun a b => ⟨a, b, rfl⟩) (e₀ : Sym2 V)
    rw [hab, Sym2.mem_iff] at hv_in_e₀

    have key : ∀ w, M.Adj v w → s(v, w) = (e₀ : Sym2 V) := by
      intro w hMvw
      exact congrArg Subtype.val (he₀_uniq ⟨s(v, w), (mem_edgeSet G).mpr (M.adj_sub hMvw)⟩
        ⟨(mem_incidentEdgeFinset_iff G v _).mpr (Sym2.mem_mk_left v w),
         (hM_iff _).mp (Subgraph.mem_edgeSet.mpr hMvw)⟩)

    have key2 : ∀ w, M.Adj v w → w ∈ ({a, b} : Set V) := by
      intro w hMvw
      have h := key w hMvw
      rw [hab] at h
      have := Sym2.mem_mk_right v w
      rw [h] at this
      rw [Sym2.mem_iff] at this
      rcases this with rfl | rfl <;> simp [Set.mem_insert_iff]
    obtain hva | hvb := hv_in_e₀
    · subst hva
      have hMvb : M.Adj v b := by
        rw [← Subgraph.mem_edgeSet, ← hab]; exact (hM_iff e₀).mpr hxe₀
      refine ⟨b, hMvb, ?_⟩
      intro w hMvw
      have hw_mem := key2 w hMvw
      simp [Set.mem_insert_iff] at hw_mem
      rcases hw_mem with rfl | rfl
      · exact absurd (M.adj_sub hMvw) G.irrefl
      · rfl
    · subst hvb
      have hMav : M.Adj a v := by
        rw [← Subgraph.mem_edgeSet, ← hab]; exact (hM_iff e₀).mpr hxe₀
      refine ⟨a, M.symm hMav, ?_⟩
      intro w hMvw
      have hw_mem := key2 w hMvw
      simp [Set.mem_insert_iff] at hw_mem
      rcases hw_mem with rfl | rfl
      · rfl
      · exact absurd (M.adj_sub hMvw) G.irrefl
  ·
    funext e
    rcases hint e with h0 | h1
    · have hne : ¬ (e : Sym2 V) ∈ M.edgeSet := (hM_iff e).not.mpr (by linarith)
      simp [h0, hne]
    · have hmem : (e : Sym2 V) ∈ M.edgeSet := (hM_iff e).mpr h1
      simp [h1, hmem]

lemma mem_edgeCutFinset_iff (S : Finset V) (e : G.edgeSet) :
    e ∈ edgeCutFinset G S ↔ ∃ a ∈ S, ∃ b ∉ S, (e : Sym2 V) = s(a, b) := by
  simp only [edgeCutFinset, Finset.mem_subtype, Finset.mem_filter,
        SimpleGraph.mem_edgeFinset]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨e.2, h⟩⟩

lemma edgeCutFinset_singleton_eq (v : V) :
    edgeCutFinset G {v} = incidentEdgeFinset G v := by
  ext e
  rw [mem_edgeCutFinset_iff, mem_incidentEdgeFinset_iff]
  constructor
  · rintro ⟨a, ha, b, hb, heq⟩
    rw [Finset.mem_singleton] at ha; subst ha
    rw [heq]; exact Sym2.mem_mk_left a b
  · intro hv
    obtain ⟨a, b, hab⟩ : ∃ a b, (e : Sym2 V) = s(a, b) :=
      Sym2.ind (fun a b => ⟨a, b, rfl⟩) (e : Sym2 V)
    rw [hab] at hv ⊢
    rw [Sym2.mem_iff] at hv
    have hadj : G.Adj a b := by
      have := e.2; rw [hab] at this; exact (mem_edgeSet G).mp this
    rcases hv with rfl | rfl
    · exact ⟨v, Finset.mem_singleton.mpr rfl, b,
             Finset.mem_singleton.not.mpr (Ne.symm (G.ne_of_adj hadj)), rfl⟩
    · exact ⟨v, Finset.mem_singleton.mpr rfl, a,
             Finset.mem_singleton.not.mpr (Ne.symm (G.ne_of_adj (G.symm hadj))),
             Sym2.eq_swap⟩

lemma nonintegral_has_tight_oddset (x : G.edgeSet → ℝ)
    (hx : x ∈ edmondsPolytope G)
    (heven : Even (Fintype.card V))
    (hni : ∃ e : G.edgeSet, x e ≠ 0 ∧ x e ≠ 1) :
    ∃ W : Finset V, Odd W.card ∧ ∑ e ∈ edgeCutFinset G W, x e = 1 := by
  obtain ⟨_, hdeg, _⟩ := hx
  obtain ⟨e₀, _⟩ := hni

  let v : V := (e₀ : Sym2 V).out.1

  exact ⟨{v}, by simp [Finset.card_singleton], by rw [edgeCutFinset_singleton_eq]; exact hdeg v⟩

private axiom edmonds_polytope_perturbation_local
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : G.edgeSet → ℝ)
    (hnn : ∀ e : G.edgeSet, 0 ≤ x e)
    (hdeg : ∀ v : V, ∑ e ∈ incidentEdgeFinset G v, x e = 1)
    (hodd : ∀ S : Finset V, Odd S.card → ∑ e ∈ edgeCutFinset G S, x e ≥ 1)
    (e₀ : G.edgeSet)
    (he₀ : x e₀ ≠ 0 ∧ x e₀ ≠ 1) :
    ∃ (y z : G.edgeSet → ℝ) (t : ℝ),
      0 < t ∧ t < 1 ∧
      y ∈ edmondsPolytope G ∧
      z ∈ edmondsPolytope G ∧
      (∀ e, x e = t * y e + (1 - t) * z e) ∧
      (Finset.univ.filter (fun e : G.edgeSet => y e ≠ 0 ∧ y e ≠ 1)).card <
        (Finset.univ.filter (fun e : G.edgeSet => x e ≠ 0 ∧ x e ≠ 1)).card ∧
      (Finset.univ.filter (fun e : G.edgeSet => z e ≠ 0 ∧ z e ≠ 1)).card <
        (Finset.univ.filter (fun e : G.edgeSet => x e ≠ 0 ∧ x e ≠ 1)).card

lemma edmondsPolytope_pm_decomposition_aux_local
    (n : ℕ)
    (x : G.edgeSet → ℝ)
    (hx : x ∈ edmondsPolytope G)
    (hn : (Finset.univ.filter (fun e : G.edgeSet => x e ≠ 0 ∧ x e ≠ 1)).card = n) :
    ∃ (k : ℕ) (M : Fin k → G.Subgraph) (_ : ∀ i, (M i).IsPerfectMatching)
      (w : Fin k → ℝ),
      (∀ i, 0 ≤ w i) ∧
      (∑ i : Fin k, w i = 1) ∧
      (∀ e : G.edgeSet, x e = ∑ i : Fin k,
        w i * if (e : Sym2 V) ∈ (M i).edgeSet then 1 else 0) := by
  induction n using Nat.strongRecOn generalizing x with
  | _ n ih =>
  obtain ⟨hnn, hdeg, hodd⟩ := hx
  by_cases hint : ∀ e : G.edgeSet, x e = 0 ∨ x e = 1
  ·
    obtain ⟨M, hM, hx_eq⟩ := integral_edmondsPolytope_mem_pm G x hdeg hint
    refine ⟨1, fun _ => M, fun _ => hM, fun _ => 1, fun _ => by norm_num, by simp, ?_⟩
    intro e
    simp only [Fin.sum_univ_one, one_mul]
    exact congr_fun hx_eq e
  ·
    push_neg at hint
    obtain ⟨e₀, he₀⟩ := hint
    have hn_pos : 0 < n := by
      rw [← hn]
      exact Finset.card_pos.mpr ⟨e₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he₀⟩⟩

    obtain ⟨y, z, t, ht_pos, ht_lt_one, hy_mem, hz_mem, hx_combo, hy_fewer, hz_fewer⟩ :=
      edmonds_polytope_perturbation_local G x hnn hdeg hodd e₀ he₀

    have hy_card : (Finset.univ.filter (fun e : G.edgeSet => y e ≠ 0 ∧ y e ≠ 1)).card < n := by
      omega
    obtain ⟨k₁, M₁, hM₁, w₁, hw₁_nn, hw₁_sum, hy_decomp⟩ :=
      ih _ hy_card y hy_mem rfl

    have hz_card : (Finset.univ.filter (fun e : G.edgeSet => z e ≠ 0 ∧ z e ≠ 1)).card < n := by
      omega
    obtain ⟨k₂, M₂, hM₂, w₂, hw₂_nn, hw₂_sum, hz_decomp⟩ :=
      ih _ hz_card z hz_mem rfl

    refine ⟨k₁ + k₂,
      fun i => Fin.addCases M₁ M₂ i,
      fun i => by refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp only [Fin.addCases_left, Fin.addCases_right] <;> [exact hM₁ j; exact hM₂ j],
      fun i => Fin.addCases (fun j => t * w₁ j) (fun j => (1 - t) * w₂ j) i,
      ?_, ?_, ?_⟩
    ·
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.addCases_left]
        exact mul_nonneg (le_of_lt ht_pos) (hw₁_nn j)
      · simp only [Fin.addCases_right]
        exact mul_nonneg (by linarith) (hw₂_nn j)
    ·
      rw [Fin.sum_univ_add]
      simp only [Fin.addCases_left, Fin.addCases_right]
      rw [← Finset.mul_sum, ← Finset.mul_sum, hw₁_sum, hw₂_sum]
      ring
    ·
      intro e
      rw [Fin.sum_univ_add]
      simp only [Fin.addCases_left, Fin.addCases_right]
      rw [hx_combo e, hy_decomp e, hz_decomp e]
      rw [Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> (apply Finset.sum_congr rfl; intro i _; ring)

private lemma tight_oddset_pm_decomposition
    (x : G.edgeSet → ℝ)
    (hx : x ∈ edmondsPolytope G)
    (W : Finset V)
    (hW_odd : Odd W.card)
    (hW_tight : ∑ e ∈ edgeCutFinset G W, x e = 1) :
    ∃ (k : ℕ) (M : Fin k → G.Subgraph) (_ : ∀ i, (M i).IsPerfectMatching)
      (w : Fin k → ℝ),
      (∀ i, 0 ≤ w i) ∧
      (∑ i : Fin k, w i = 1) ∧
      (∀ e : G.edgeSet, x e = ∑ i : Fin k,
        w i * if (e : Sym2 V) ∈ (M i).edgeSet then 1 else 0) :=
  edmondsPolytope_pm_decomposition_aux_local G _ x hx rfl

lemma edmondsPolytope_subset_perfectMatchingPolytope
    (heven : Even (Fintype.card V)) :
    edmondsPolytope G ⊆ perfectMatchingPolytope G := by
  intro x hx
  obtain ⟨hnn, hdeg, hodd⟩ := hx

  by_cases hint : ∀ e : G.edgeSet, x e = 0 ∨ x e = 1
  ·
    exact subset_convexHull ℝ _ (integral_edmondsPolytope_mem_pm G x hdeg hint)
  ·


    push_neg at hint
    obtain ⟨e₀, he₀_ne0, he₀_ne1⟩ := hint
    have hni : ∃ e : G.edgeSet, x e ≠ 0 ∧ x e ≠ 1 := ⟨e₀, he₀_ne0, he₀_ne1⟩
    obtain ⟨W, hW_odd, hW_tight⟩ := nonintegral_has_tight_oddset G x ⟨hnn, hdeg, hodd⟩ heven hni

    obtain ⟨k, M, hM, w, hw_nn, hw_sum, hx_decomp⟩ :=
      tight_oddset_pm_decomposition G x ⟨hnn, hdeg, hodd⟩ W hW_odd hW_tight

    have hx_eq : x = ∑ i : Fin k, w i • (fun (e : G.edgeSet) =>
        if (e : Sym2 V) ∈ (M i).edgeSet then (1 : ℝ) else 0) := by
      funext e
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact hx_decomp e
    rw [hx_eq]
    exact (convex_convexHull ℝ _).sum_mem
      (fun i _ => hw_nn i) hw_sum
      (fun i _ => subset_convexHull ℝ _ ⟨M i, hM i, rfl⟩)

theorem edmonds_perfect_matching_polytope
    (heven : Even (Fintype.card V)) :
    edmondsPolytope G = perfectMatchingPolytope G := by
  apply Set.eq_of_subset_of_subset
  · exact edmondsPolytope_subset_perfectMatchingPolytope G heven
  · exact perfectMatchingPolytope_subset_edmondsPolytope G

end SimpleGraph

end
