/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.CombinatorialOptimization.code.Matching.Berge

open SimpleGraph

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

def blossomContractMap (B : Finset V) (base : V) : V → V :=
  fun v => if v ∈ B then base else v

omit [Fintype V] [DecidableRel G.Adj] in
@[simp]
lemma blossomContractMap_mem (B : Finset V) (base : V) (v : V) (hv : v ∈ B) :
    blossomContractMap B base v = base := by
  simp [blossomContractMap, hv]

omit [Fintype V] [DecidableRel G.Adj] in
@[simp]
lemma blossomContractMap_not_mem (B : Finset V) (base : V) (v : V) (hv : v ∉ B) :
    blossomContractMap B base v = v := by
  simp [blossomContractMap, hv]

def contractBlossom (G : SimpleGraph V) (B : Finset V) (base : V) : SimpleGraph V :=
  G.map (blossomContractMap B base)

structure IsBlossom (G : SimpleGraph V) (M : G.Subgraph) (B : Finset V) (base : V) : Prop where
  base_mem : base ∈ B
  card_odd : Odd B.card
  card_ge : B.card ≥ 3
  cycle_exists : ∃ (c : G.Walk base base), c.IsCycle ∧ c.support.toFinset = B
  matched_internal : ∀ v ∈ B, v ≠ base → ∃ w ∈ B, w ≠ v ∧ M.Adj v w
  stem : ∃ w, w ∉ B ∧ M.Adj base w

def inducedMatchingSubgraph (M : G.Subgraph) (B : Finset V) (base : V) :
    (contractBlossom G B base).Subgraph where
  verts := (blossomContractMap B base) '' M.verts
  Adj u v := (contractBlossom G B base).Adj u v ∧
    ∃ a b, blossomContractMap B base a = u ∧ blossomContractMap B base b = v ∧
      M.Adj a b ∧ ¬(a ∈ B ∧ b ∈ B)
  adj_sub := fun ⟨hadj, _⟩ => hadj
  edge_vert := by
    intro u v ⟨_, a, _, hau, _, hadj_M, _⟩
    rw [← hau]
    exact Set.mem_image_of_mem (blossomContractMap B base) (M.edge_vert hadj_M)
  symm := by
    intro u v ⟨hadj, a, b, hau, hbv, hadj_M, hnotB⟩
    exact ⟨hadj.symm, b, a, hbv, hau, hadj_M.symm, fun ⟨hb, ha⟩ => hnotB ⟨ha, hb⟩⟩

lemma inducedMatchingSubgraph_isMatching
    (M : G.Subgraph) (hM : M.IsMatching) (B : Finset V) (base : V)
    (hB : IsBlossom G M B base) :
    (inducedMatchingSubgraph M B base).IsMatching := by
  intro v hv
  simp only [inducedMatchingSubgraph] at hv ⊢
  obtain ⟨a, ha_mem, ha_eq⟩ := hv
  obtain ⟨w, hw_adj, hw_unique⟩ := hM ha_mem
  by_cases haB : a ∈ B
  ·
    subst ha_eq
    rw [blossomContractMap_mem B base a haB]
    obtain ⟨w_stem, hw_stem_notB, hw_stem_adj⟩ := hB.stem
    have hbase_mem : base ∈ M.verts := M.edge_vert hw_stem_adj
    obtain ⟨w_base, hw_base_adj, hw_base_unique⟩ := hM hbase_mem
    have hw_stem_eq : w_stem = w_base := hw_base_unique w_stem hw_stem_adj
    use blossomContractMap B base w_stem
    constructor
    · constructor
      · rw [blossomContractMap_not_mem B base w_stem hw_stem_notB]
        rw [contractBlossom, map_adj']
        refine ⟨?_, base, w_stem, M.adj_sub hw_stem_adj,
          blossomContractMap_mem B base base hB.base_mem,
          blossomContractMap_not_mem B base w_stem hw_stem_notB⟩
        intro h
        exact hw_stem_notB (h ▸ hB.base_mem)
      · exact ⟨base, w_stem, blossomContractMap_mem B base base hB.base_mem,
          rfl, hw_stem_adj, fun ⟨_, hw⟩ => hw_stem_notB hw⟩
    · intro y ⟨_, c, d, hcu, hdv, hcd_adj, hcd_notB⟩
      have hcB : c ∈ B := by
        by_contra hc
        simp [blossomContractMap_not_mem B base c hc] at hcu
        exact hc (hcu ▸ hB.base_mem)
      have hdnotB : d ∉ B := fun hd => hcd_notB ⟨hcB, hd⟩
      rw [blossomContractMap_not_mem B base d hdnotB] at hdv
      rw [← hdv, blossomContractMap_not_mem B base w_stem hw_stem_notB]
      by_cases hc_base : c = base
      · subst hc_base
        exact (hw_stem_eq ▸ hw_base_unique d hcd_adj)
      · obtain ⟨w', hw'B, _, hw'_adj⟩ := hB.matched_internal c hcB hc_base
        have hc_mem : c ∈ M.verts := M.edge_vert hcd_adj
        obtain ⟨unique_w, h_unique_adj, h_unique⟩ := hM hc_mem
        have hd_eq : d = unique_w := h_unique d hcd_adj
        have hw'_eq : w' = unique_w := h_unique w' hw'_adj
        exfalso
        exact hdnotB (hd_eq ▸ hw'_eq ▸ hw'B)
  ·
    subst ha_eq
    rw [blossomContractMap_not_mem B base a haB]
    use blossomContractMap B base w
    constructor
    · constructor
      · rw [contractBlossom, map_adj']
        constructor
        · intro h
          by_cases hwB : w ∈ B
          · rw [blossomContractMap_mem B base w hwB] at h
            exact haB (h ▸ hB.base_mem)
          · rw [blossomContractMap_not_mem B base w hwB] at h
            exact (M.adj_sub hw_adj).ne h
        · exact ⟨a, w, M.adj_sub hw_adj,
            blossomContractMap_not_mem B base a haB, rfl⟩
      · exact ⟨a, w, blossomContractMap_not_mem B base a haB, rfl, hw_adj,
          fun ⟨ha', _⟩ => haB ha'⟩
    · intro y ⟨_, c, d, hcu, hdv, hcd_adj, hcd_notB⟩
      have hcB_or : c = a := by
        by_cases hcB : c ∈ B
        · rw [blossomContractMap_mem B base c hcB] at hcu
          exact absurd (hcu ▸ hB.base_mem) haB
        · rwa [blossomContractMap_not_mem B base c hcB] at hcu
      subst hcB_or
      have : d = w := hw_unique d hcd_adj
      subst this
      exact hdv.symm

omit [Fintype V] [DecidableRel G.Adj] in
lemma blossom_verts_in_M_verts
    (M : G.Subgraph) (B : Finset V) (base : V)
    (hB : IsBlossom G M B base) :
    ∀ v ∈ B, v ∈ M.verts := by
  intro v hv
  by_cases h : v = base
  · subst h
    exact M.edge_vert hB.stem.choose_spec.2
  · obtain ⟨w, _, _, hw_adj⟩ := hB.matched_internal v hv h
    exact M.edge_vert hw_adj

omit [DecidableRel G.Adj] in
lemma odd_cycle_matching_avoiding_any_vertex
    {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V)
    (B : Finset V) (base : V) (hbase : base ∈ B)
    (hB_odd : Odd B.card) (hB_ge : 3 ≤ B.card)
    (c : G.Walk base base) (hc : c.IsCycle) (hsupp : c.support.toFinset = B)
    (v : V) (hv : v ∈ B) :
    ∃ (S : Set (Sym2 V)),
      S ⊆ G.edgeSet ∧
      (∀ e ∈ S, ∀ w ∈ e, w ∈ B ∧ w ≠ v) ∧
      S.ncard = (B.card - 1) / 2 ∧
      (∀ e₁ ∈ S, ∀ e₂ ∈ S, e₁ ≠ e₂ → Disjoint (e₁ : Set V) e₂) := by
  classical
  have hv_supp : v ∈ c.support := List.mem_toFinset.mp (hsupp ▸ hv)
  set c' := c.rotate v hv_supp with hc'_def
  have hc' : c'.IsCycle := hc.rotate hv_supp
  have hlen_eq : c'.length = c.length := by
    simp only [hc'_def, Walk.rotate, Walk.length_append]
    have := Walk.take_spec c hv_supp
    have h1 := congr_arg Walk.length this
    rw [Walk.length_append] at h1; omega
  have hsupp' : c'.support.toFinset = B := by
    ext w; simp only [List.mem_toFinset]
    constructor
    · intro hw
      have := (Walk.mem_support_rotate_iff c v hv_supp).mp hw
      rwa [← List.mem_toFinset, hsupp] at this
    · intro hw
      apply (Walk.mem_support_rotate_iff c v hv_supp).mpr
      rw [← List.mem_toFinset, hsupp]
      exact hw
  have hcard_len : B.card = c'.length := by
    rw [← hsupp']
    have h_nodup := hc'.support_nodup
    have h_u_in_tail : v ∈ c'.support.tail := by
      cases hc'_eq : c' with
      | nil => exact absurd hc'_eq (by intro h; exact hc'.ne_nil (h ▸ rfl))
      | cons hadj p =>
        simp only [Walk.support, List.tail_cons]
        exact Walk.end_mem_support p
    have h_eq : c'.support.toFinset = c'.support.tail.toFinset := by
      rw [Walk.support_eq_cons c', List.toFinset_cons]
      exact Finset.insert_eq_of_mem (List.mem_toFinset.mpr h_u_in_tail)
    rw [h_eq, List.toFinset_card_of_nodup h_nodup, List.length_tail, Walk.length_support]; omega
  have hlen_ge : 3 ≤ c'.length := hcard_len ▸ hB_ge
  obtain ⟨k, hk⟩ : ∃ k, c'.length = 2 * k + 1 := by
    obtain ⟨k, hk⟩ := (hcard_len ▸ hB_odd); exact ⟨k, by omega⟩
  have hk_pos : k ≥ 1 := by omega
  have getVert_mem_B : ∀ i, c'.getVert i ∈ B := fun i =>
    hsupp' ▸ List.mem_toFinset.mpr (Walk.getVert_mem_support c' i)
  have getVert_ne_v : ∀ i, 1 ≤ i → i < c'.length → c'.getVert i ≠ v := by
    intro i hi1 hi2 heq
    have hinj := hc'.getVert_injOn
    have hi_in : i ∈ {j : ℕ | 1 ≤ j ∧ j ≤ c'.length} := ⟨hi1, le_of_lt hi2⟩
    have hn_in : c'.length ∈ {j : ℕ | 1 ≤ j ∧ j ≤ c'.length} := ⟨by omega, le_refl _⟩
    have h_eq : c'.getVert i = c'.getVert c'.length := by rw [heq, Walk.getVert_length]
    exact absurd (hinj hi_in hn_in h_eq) (by omega)
  let mkEdge (i : Fin k) : Sym2 V :=
    s(c'.getVert (2 * i.val + 1), c'.getVert (2 * i.val + 2))
  have mkEdge_inj : Function.Injective mkEdge := by
    intro i j h_eq
    have hinj := hc'.getVert_injOn
    simp only [mkEdge, Sym2.eq_iff] at h_eq
    rcases h_eq with ⟨h1, _⟩ | ⟨h1, _⟩
    · have hi : (2 * i.val + 1) ∈ ({n | 1 ≤ n ∧ n ≤ c'.length} : Set ℕ) := by
        constructor <;> omega
      have hj : (2 * j.val + 1) ∈ ({n | 1 ≤ n ∧ n ≤ c'.length} : Set ℕ) := by
        constructor <;> omega
      exact Fin.ext (by have := hinj hi hj h1; omega)
    · have hi : (2 * i.val + 1) ∈ ({n | 1 ≤ n ∧ n ≤ c'.length} : Set ℕ) := by
        constructor <;> omega
      have hj : (2 * j.val + 2) ∈ ({n | 1 ≤ n ∧ n ≤ c'.length} : Set ℕ) := by
        constructor <;> omega
      exact absurd (hinj hi hj h1) (by omega)
  let S : Set (Sym2 V) := Set.range mkEdge
  refine ⟨S, ?_, ?_, ?_, ?_⟩
  ·
    intro e he; obtain ⟨i, rfl⟩ := he
    rw [SimpleGraph.mem_edgeSet]
    exact c'.adj_getVert_succ (by omega : 2 * i.val + 1 < c'.length)
  ·
    intro e he w hw
    obtain ⟨i, rfl⟩ := he
    change w ∈ (mkEdge i : Sym2 V) at hw
    simp only [mkEdge, Sym2.mem_iff] at hw
    rcases hw with rfl | rfl
    · exact ⟨getVert_mem_B _, getVert_ne_v _ (by omega) (by omega)⟩
    · exact ⟨getVert_mem_B _, getVert_ne_v _ (by omega) (by omega)⟩
  ·
    have h_ncard : S.ncard = k := by
      have h1 := Set.ncard_range_of_injective mkEdge_inj
      rw [Nat.card_fin] at h1
      exact h1
    rw [h_ncard, hcard_len, hk]; omega
  ·
    intro e₁ he₁ e₂ he₂ hne
    obtain ⟨i, rfl⟩ := he₁
    obtain ⟨j, rfl⟩ := he₂
    have hij : i ≠ j := fun h => hne (h ▸ rfl)
    rw [Set.disjoint_left]
    intro w hw₁ hw₂
    change w ∈ (mkEdge i : Sym2 V) at hw₁
    change w ∈ (mkEdge j : Sym2 V) at hw₂
    simp only [mkEdge, Sym2.mem_iff] at hw₁ hw₂
    have hinj := hc'.getVert_injOn
    have h_i1 : (2 * i.val + 1) ∈ ({n | 1 ≤ n ∧ n ≤ c'.length} : Set ℕ) := by
      constructor <;> omega
    have h_i2 : (2 * i.val + 2) ∈ ({n | 1 ≤ n ∧ n ≤ c'.length} : Set ℕ) := by
      constructor <;> omega
    have h_j1 : (2 * j.val + 1) ∈ ({n | 1 ≤ n ∧ n ≤ c'.length} : Set ℕ) := by
      constructor <;> omega
    have h_j2 : (2 * j.val + 2) ∈ ({n | 1 ≤ n ∧ n ≤ c'.length} : Set ℕ) := by
      constructor <;> omega
    rcases hw₁ with rfl | rfl <;> rcases hw₂ with h | h
    · exact absurd (hinj h_i1 h_j1 h) (by omega)
    · exact absurd (hinj h_i1 h_j2 h) (by omega)
    · exact absurd (hinj h_i2 h_j1 h) (by omega)
    · exact absurd (hinj h_i2 h_j2 h) (by omega)

lemma lift_matching_size
    (M : G.Subgraph) (hM : M.IsMatching) (B : Finset V) (base : V)
    (hB : IsBlossom G M B base)
    (N' : (contractBlossom G B base).Subgraph) (hN' : N'.IsMatching) :
    ∃ N : G.Subgraph, N.IsMatching ∧
      N'.edgeSet.ncard + (B.card - 1) / 2 ≤ N.edgeSet.ncard := by


  have h_construction : ∃ N : G.Subgraph, N.IsMatching ∧
      ∃ (S_ext S_int : Set (Sym2 V)),
        S_ext ⊆ N.edgeSet ∧ S_int ⊆ N.edgeSet ∧
        Disjoint S_ext S_int ∧
        S_ext.ncard = N'.edgeSet.ncard ∧
        S_int.ncard = (B.card - 1) / 2 := by
    classical
    obtain ⟨c, hc_cycle, hc_supp⟩ := hB.cycle_exists


    have h_avoid : ∃ (v_avoid : V), v_avoid ∈ B ∧
        ∃ (S_ext : Set (Sym2 V)),
          S_ext ⊆ G.edgeSet ∧
          S_ext.ncard = N'.edgeSet.ncard ∧
          (∀ e ∈ S_ext, ∀ w ∈ e, w ∉ B ∨ w = v_avoid) ∧
          (∀ e₁ ∈ S_ext, ∀ e₂ ∈ S_ext, e₁ ≠ e₂ → Disjoint (e₁ : Set V) e₂) := by
      sorry
    obtain ⟨v_avoid, hv_avoid_B, S_ext, hS_ext_G, hS_ext_card, hS_ext_verts, hS_ext_disj⟩ := h_avoid

    obtain ⟨S_int, hS_int_G, hS_int_verts, hS_int_card, hS_int_disj⟩ :=
      odd_cycle_matching_avoiding_any_vertex G B base hB.base_mem hB.card_odd hB.card_ge
        c hc_cycle hc_supp v_avoid hv_avoid_B

    let all_edges := S_ext ∪ S_int

    have hall_G : all_edges ⊆ G.edgeSet := Set.union_subset hS_ext_G hS_int_G

    let N : G.Subgraph := {
      verts := { v | ∃ e ∈ all_edges, v ∈ e }
      Adj := fun a b => s(a, b) ∈ all_edges ∧ G.Adj a b
      adj_sub := fun h => h.2
      edge_vert := fun {a b} h => ⟨s(a,b), h.1, Sym2.mem_mk_left a b⟩
      symm := fun {a b} ⟨h1, h2⟩ => ⟨Sym2.eq_swap ▸ h1, h2.symm⟩
    }


    have hN_edgeSet : N.edgeSet = all_edges := by
      ext e
      refine Sym2.ind (f := fun e => e ∈ N.edgeSet ↔ e ∈ all_edges) ?_ e
      intro a b
      rw [Subgraph.mem_edgeSet]
      simp only [N]
      exact ⟨fun h => h.1, fun he => ⟨he, (SimpleGraph.mem_edgeSet (G := G)).mp (hall_G he)⟩⟩


    have hN_matching : N.IsMatching := by
      sorry

    refine ⟨N, hN_matching, S_ext, S_int, ?_, ?_, ?_, hS_ext_card, hS_int_card⟩
    · rw [hN_edgeSet]; exact Set.subset_union_left
    · rw [hN_edgeSet]; exact Set.subset_union_right
    · rw [Set.disjoint_left]
      intro e he_ext he_int
      have ⟨hxB, hx_ne⟩ := hS_int_verts e he_int (Quot.out e).1 (Sym2.out_fst_mem e)
      rcases hS_ext_verts e he_ext (Quot.out e).1 (Sym2.out_fst_mem e) with h | h

      · exact h hxB
      · exact hx_ne h

  obtain ⟨N, hN_match, S_ext, S_int, hS_ext_sub, hS_int_sub, hS_disj, hS_ext_card, hS_int_card⟩ :=
    h_construction
  refine ⟨N, hN_match, ?_⟩
  have hN_fin : N.edgeSet.Finite := Set.Finite.subset Set.finite_univ (Set.subset_univ _)
  have h_union_sub : S_ext ∪ S_int ⊆ N.edgeSet := Set.union_subset hS_ext_sub hS_int_sub
  have h_union_card : (S_ext ∪ S_int).ncard = N'.edgeSet.ncard + (B.card - 1) / 2 := by
    rw [Set.ncard_union_eq hS_disj (hN_fin.subset hS_ext_sub) (hN_fin.subset hS_int_sub),
        hS_ext_card, hS_int_card]
  calc N'.edgeSet.ncard + (B.card - 1) / 2
      = (S_ext ∪ S_int).ncard := h_union_card.symm
    _ ≤ N.edgeSet.ncard := Set.ncard_le_ncard h_union_sub hN_fin

lemma induced_matching_edgeSet_ncard
    (M : G.Subgraph) (hM : M.IsMatching) (B : Finset V) (base : V)
    (hB : IsBlossom G M B base) :
    M.edgeSet.ncard = (inducedMatchingSubgraph M B base).edgeSet.ncard + (B.card - 1) / 2 := by


  have hM_fin : M.edgeSet.Finite := Set.Finite.subset Set.finite_univ (Set.subset_univ _)
  have hM'_fin : (inducedMatchingSubgraph M B base).edgeSet.Finite :=
    Set.Finite.subset Set.finite_univ (Set.subset_univ _)
  have hM' : (inducedMatchingSubgraph M B base).IsMatching :=
    inducedMatchingSubgraph_isMatching M hM B base hB
  have hM_eq := matching_verts_twice_edges hM hM_fin
  have hM'_eq := matching_verts_twice_edges hM' hM'_fin
  have hB_sub : (↑B : Set V) ⊆ M.verts :=
    fun v hv => blossom_verts_in_M_verts M B base hB v hv
  have hM_verts_fin : M.verts.Finite := Set.Finite.subset Set.finite_univ (Set.subset_univ _)

  have h_M_decomp : M.verts.ncard = (M.verts \ ↑B).ncard + B.card := by
    have := Set.ncard_diff_add_ncard_of_subset hB_sub hM_verts_fin
    rw [Set.ncard_coe_finset] at this; omega

  have h_verts_eq : (inducedMatchingSubgraph M B base).verts = (M.verts \ ↑B) ∪ {base} := by
    ext v
    simp only [inducedMatchingSubgraph, Set.mem_image, Set.mem_union, Set.mem_diff,
      Set.mem_singleton_iff, Finset.mem_coe]
    constructor
    · rintro ⟨a, ha_mem, ha_eq⟩
      by_cases haB : a ∈ B
      · have : blossomContractMap B base a = base := by simp [blossomContractMap, haB]
        rw [this] at ha_eq; right; exact ha_eq.symm
      · have : blossomContractMap B base a = a := by simp [blossomContractMap, haB]
        rw [this] at ha_eq; subst ha_eq; left; exact ⟨ha_mem, haB⟩
    · intro h
      rcases h with ⟨hv_mem, hv_notB⟩ | hv_eq
      · exact ⟨v, hv_mem, by simp [blossomContractMap, hv_notB]⟩
      · exact ⟨base, hB_sub hB.base_mem, by simp [blossomContractMap, hB.base_mem, hv_eq]⟩

  have h_M'_decomp : (inducedMatchingSubgraph M B base).verts.ncard =
      (M.verts \ ↑B).ncard + 1 := by
    rw [h_verts_eq]
    have hbase_not : base ∉ (M.verts \ (↑B : Set V)) := by
      simp [Set.mem_diff]; intro _; exact hB.base_mem
    have h_disj : Disjoint (M.verts \ ↑B) ({base} : Set V) :=
      Set.disjoint_singleton_right.mpr hbase_not
    rw [Set.ncard_union_eq h_disj (hM_verts_fin.subset Set.diff_subset)
        (Set.finite_singleton _), Set.ncard_singleton]

  obtain ⟨k, hk⟩ := hB.card_odd
  omega

lemma augmenting_path_lift
    (M : G.Subgraph) (hM : M.IsMatching) (B : Finset V) (base : V)
    (hB : IsBlossom G M B base)
    (haug' : HasAugmentingPath (contractBlossom G B base) (inducedMatchingSubgraph M B base)) :
    HasAugmentingPath G M := by
  obtain ⟨u, v, p', hp'⟩ := haug'
  obtain ⟨hpath', huv', hu_free', hv_free', halt'⟩ := hp'
  have hM' : (inducedMatchingSubgraph M B base).IsMatching :=
    inducedMatchingSubgraph_isMatching M hM B base hB
  have hbase_in_M'_verts : base ∈ (inducedMatchingSubgraph M B base).verts := by
    simp only [inducedMatchingSubgraph]
    exact ⟨base, M.edge_vert hB.stem.choose_spec.2, blossomContractMap_mem B base base hB.base_mem⟩
  have hu_ne_base : u ≠ base := fun h => hu_free' (h ▸ hbase_in_M'_verts)
  have hv_ne_base : v ≠ base := fun h => hv_free' (h ▸ hbase_in_M'_verts)
  have hM'_not_max : ¬(inducedMatchingSubgraph M B base).IsMaxMatching :=
    not_isMaxMatching_of_hasAugmentingPath _ hM' ⟨u, v, p', hpath', huv', hu_free', hv_free', halt'⟩
  apply hasAugmentingPath_of_not_isMaxMatching M hM (Set.toFinite _)
  intro hM_max
  apply hM'_not_max
  refine ⟨hM', fun N' hN'_match => ?_⟩
  obtain ⟨N, hN_match, hN_card⟩ := lift_matching_size M hM B base hB N' hN'_match
  have hN_le_M : N.edgeSet.ncard ≤ M.edgeSet.ncard := hM_max.2 N hN_match
  have hM_eq : M.edgeSet.ncard = (inducedMatchingSubgraph M B base).edgeSet.ncard + (B.card - 1) / 2 :=
    induced_matching_edgeSet_ncard M hM B base hB
  omega

lemma walk_edges_in_contractBlossom (B : Finset V) (base : V)
    {u v : V} (p : G.Walk u v) (hdisjoint : ∀ w ∈ p.support, w ∉ B) :
    ∀ e ∈ p.edges, e ∈ (contractBlossom G B base).edgeSet := by
  intro e he
  have hedge := p.edges_subset_edgeSet he
  revert he hedge
  apply Sym2.ind (f := fun e => e ∈ p.edges → e ∈ G.edgeSet →
    e ∈ (contractBlossom G B base).edgeSet)
  intro a b he hedge
  have hadj : G.Adj a b := by rwa [SimpleGraph.mem_edgeSet] at hedge
  have ha : a ∉ B := hdisjoint a (Walk.fst_mem_support_of_mem_edges p he)
  have hb : b ∉ B := hdisjoint b (Walk.snd_mem_support_of_mem_edges p he)
  rw [SimpleGraph.mem_edgeSet]
  show (contractBlossom G B base).Adj a b
  rw [contractBlossom, map_adj']
  exact ⟨hadj.ne, a, b, hadj, by simp [blossomContractMap, ha], by simp [blossomContractMap, hb]⟩

lemma inducedMatching_adj_iff_of_not_mem (M : G.Subgraph) (B : Finset V) (base : V)
    (hbase : base ∈ B) {a b : V} (ha : a ∉ B) (hb : b ∉ B) (hadj_G : G.Adj a b) :
    (inducedMatchingSubgraph M B base).Adj a b ↔ M.Adj a b := by
  constructor
  · intro ⟨_, c, d, hc, hd, hcd_adj, _⟩
    have hcB : c ∉ B := by
      intro hcB; simp [blossomContractMap, hcB] at hc; exact ha (hc ▸ hbase)
    simp [blossomContractMap, hcB] at hc
    have hdB : d ∉ B := by
      intro hdB; simp [blossomContractMap, hdB] at hd; exact hb (hd ▸ hbase)
    simp [blossomContractMap, hdB] at hd
    rw [← hc, ← hd]; exact hcd_adj
  · intro hab
    refine ⟨?_, a, b, ?_, ?_, hab, fun ⟨ha', _⟩ => ha ha'⟩
    · rw [contractBlossom, map_adj']
      exact ⟨hadj_G.ne, a, b, hadj_G,
        by simp [blossomContractMap, ha], by simp [blossomContractMap, hb]⟩
    · simp [blossomContractMap, ha]
    · simp [blossomContractMap, hb]

lemma inducedMatching_edgeSet_iff_of_support_disjoint (M : G.Subgraph) (B : Finset V) (base : V)
    (hbase : base ∈ B) {u v : V} (p : G.Walk u v) (hdisjoint : ∀ w ∈ p.support, w ∉ B)
    {e : Sym2 V} (he : e ∈ p.edges) :
    e ∈ (inducedMatchingSubgraph M B base).edgeSet ↔ e ∈ M.edgeSet := by
  revert he
  apply Sym2.ind (f := fun e => e ∈ p.edges →
    (e ∈ (inducedMatchingSubgraph M B base).edgeSet ↔ e ∈ M.edgeSet))
  intro a b he
  have ha : a ∉ B := hdisjoint a (Walk.fst_mem_support_of_mem_edges p he)
  have hb : b ∉ B := hdisjoint b (Walk.snd_mem_support_of_mem_edges p he)
  have hadj_G : G.Adj a b := by
    have := p.edges_subset_edgeSet he
    rwa [SimpleGraph.mem_edgeSet] at this
  rw [Subgraph.mem_edgeSet, Subgraph.mem_edgeSet]
  exact inducedMatching_adj_iff_of_not_mem M B base hbase ha hb hadj_G

lemma unmatched_not_in_induced_verts (M : G.Subgraph) (B : Finset V) (base : V)
    (hbase : base ∈ B) (hM : M.IsMatching) (hB : IsBlossom G M B base)
    {w : V} (hw : w ∉ M.verts) (hwB : w ∉ B) :
    w ∉ (inducedMatchingSubgraph M B base).verts := by
  simp only [inducedMatchingSubgraph]
  intro ⟨a, ha_mem, ha_eq⟩
  by_cases haB : a ∈ B
  · simp [blossomContractMap, haB] at ha_eq
    exact hwB (ha_eq ▸ hbase)
  · simp [blossomContractMap, haB] at ha_eq
    exact hw (ha_eq ▸ ha_mem)

lemma augmenting_path_project
    (M : G.Subgraph) (hM : M.IsMatching) (B : Finset V) (base : V)
    (hB : IsBlossom G M B base)
    (haug : HasAugmentingPath G M) :
    HasAugmentingPath (contractBlossom G B base) (inducedMatchingSubgraph M B base) := by
  obtain ⟨u, v, p, hp⟩ := haug
  obtain ⟨hpath, huv, hu_unmatched, hv_unmatched, halt⟩ := hp

  have hu_notB : u ∉ B := fun h => hu_unmatched (blossom_verts_in_M_verts M B base hB u h)
  have hv_notB : v ∉ B := fun h => hv_unmatched (blossom_verts_in_M_verts M B base hB v h)

  by_cases hdisjoint : ∀ w ∈ p.support, w ∉ B
  ·
    have hedges := walk_edges_in_contractBlossom B base p hdisjoint
    let p' := p.transfer (contractBlossom G B base) hedges
    refine ⟨u, v, p', hpath.transfer hedges, huv,
      unmatched_not_in_induced_verts M B base hB.base_mem hM hB hu_unmatched hu_notB,
      unmatched_not_in_induced_verts M B base hB.base_mem hM hB hv_unmatched hv_notB, ?_⟩

    intro i hi
    have h_eq : p'.edges = p.edges := Walk.edges_transfer p hedges
    have hi' : i < p.edges.length := by rw [← h_eq]; exact hi
    have h_item : p'.edges[i] = p.edges[i] := by simp only [h_eq]
    rw [h_item]
    have he : p.edges[i] ∈ p.edges := List.getElem_mem hi'
    have hiff : p.edges[i] ∈ (inducedMatchingSubgraph M B base).edgeSet ↔
                p.edges[i] ∈ M.edgeSet :=
      inducedMatching_edgeSet_iff_of_support_disjoint M B base hB.base_mem p hdisjoint he
    obtain ⟨heven, hodd⟩ := halt i hi'
    exact ⟨fun hev h => heven hev (hiff.mp h), fun hod => hiff.mpr (hodd hod)⟩
  ·
    push_neg at hdisjoint
    obtain ⟨w, hw_supp, hw_B⟩ := hdisjoint

    have hw_idx : ∃ n, p.getVert n ∈ B ∧ n ≤ p.length := by
      rw [Walk.mem_support_iff_exists_getVert] at hw_supp
      obtain ⟨n, hn_eq, hn_le⟩ := hw_supp
      exact ⟨n, hn_eq ▸ hw_B, hn_le⟩

    let k := Nat.find hw_idx
    have hk_prop : p.getVert k ∈ B ∧ k ≤ p.length := Nat.find_spec hw_idx
    have hk_first : ∀ j < k, p.getVert j ∉ B := by
      intro j hj habs
      have : j < k := hj
      have hj_le : j ≤ p.length := by omega
      exact Nat.find_min hw_idx hj ⟨habs, hj_le⟩

    have hk_pos : k ≥ 1 := by
      by_contra h
      push_neg at h
      interval_cases k
      rw [Walk.getVert_zero] at hk_prop
      exact hu_notB hk_prop.1

    have ha_notB : p.getVert (k - 1) ∉ B := hk_first (k - 1) (by omega)
    have hk_lt_len : k - 1 < p.length := by omega
    have hadj_ak : G.Adj (p.getVert (k - 1)) (p.getVert k) := by
      have h := Walk.adj_getVert_succ p hk_lt_len
      have : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos (by omega : k > 0)
      rwa [this] at h


    have hadj_G' : (contractBlossom G B base).Adj (p.getVert (k - 1)) base := by
      rw [contractBlossom, map_adj']
      refine ⟨?_, p.getVert (k - 1), p.getVert k, hadj_ak,
        blossomContractMap_not_mem B base _ ha_notB,
        blossomContractMap_mem B base _ hk_prop.1⟩
      intro h
      exact ha_notB (h ▸ hB.base_mem)
    sorry

theorem blossom_shrinking
    (M : G.Subgraph) (hM : M.IsMatching) (B : Finset V) (base : V)
    (hB : IsBlossom G M B base) :
    Subgraph.IsMaxMatching M ↔
      (inducedMatchingSubgraph M B base).IsMaxMatching := by
  have hM' : (inducedMatchingSubgraph M B base).IsMatching :=
    inducedMatchingSubgraph_isMatching M hM B base hB
  rw [berge_lemma M hM (Set.toFinite _), berge_lemma _ hM' (Set.toFinite _)]
  constructor
  · intro hno_aug haug'
    exact hno_aug (augmenting_path_lift M hM B base hB haug')
  · intro hno_aug' haug
    exact hno_aug' (augmenting_path_project M hM B base hB haug)

end SimpleGraph
