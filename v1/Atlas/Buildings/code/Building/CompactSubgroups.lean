/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Affine
import Atlas.Buildings.code.BNPair.ParabolicDefs

set_option maxHeartbeats 800000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace CompactSubgroups

variable {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}

/-- A bornology on a group $G$: a family of bounded sets closed under taking subsets, finite
unions, singletons, group products, and inversion. -/
structure GroupBornology (G : Type*) [Group G] where
  isBounded : Set G → Prop
  subset_bounded : ∀ {S T : Set G}, isBounded T → S ⊆ T → isBounded S
  singleton_bounded : ∀ (g : G), isBounded {g}
  union_bounded : ∀ {S T : Set G}, isBounded S → isBounded T → isBounded (S ∪ T)
  product_bounded : ∀ {S T : Set G}, isBounded S → isBounded T →
    isBounded (setMul S T)
  inv_bounded : ∀ {S : Set G}, isBounded S →
    isBounded ((fun x => x⁻¹) '' S)

/-- A subgroup $H$ is bounded in the bornology $\mathrm{born}$ if its underlying set is bounded. -/
def IsBoundedSubgroup (born : GroupBornology G) (H : Subgroup G) : Prop :=
  born.isBounded (H : Set G)

/-- A subgroup $K$ is *maximal bounded* if it is bounded and no strictly larger subgroup is bounded. -/
def IsMaximalBounded (born : GroupBornology G) (K : Subgroup G) : Prop :=
  IsBoundedSubgroup born K ∧ ∀ H : Subgroup G, K < H → ¬IsBoundedSubgroup born H

/-- $S$ is BN-pair bounded: covered by finitely many Bruhat cells of $\mathrm{bp}$. -/
def BNPairBoundedPredicate (bp : BNPair G M) (S : Set G) : Prop :=
  ∃ (ws : Finset M.Group), S ⊆ ⋃ w ∈ ws, bp.bruhatCell w

/-- Product of BN-pair bounded sets is BN-pair bounded (uses finiteness of Bruhat cell products). -/
theorem bnpair_product_bounded {G : Type*} [Group G] {B_idx : Type*}
    {M : CoxeterMatrix B_idx} (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (S T : Set G) (hS : BNPairBoundedPredicate bp S) (hT : BNPairBoundedPredicate bp T) :
    BNPairBoundedPredicate bp (setMul S T) := by
  classical
  obtain ⟨ws₁, hS⟩ := hS
  obtain ⟨ws₂, hT⟩ := hT


  let allCells : Finset M.Group :=
    ws₁.biUnion (fun w => ws₂.biUnion (fun w' => (bd.cell_mul_finite w w').choose))
  refine ⟨allCells, ?_⟩
  intro g hg

  obtain ⟨x, hxS, y, hyT, rfl⟩ := hg

  have hx_union := hS hxS
  rw [Set.mem_iUnion₂] at hx_union
  obtain ⟨w, hw_mem, hx_cell⟩ := hx_union

  have hy_union := hT hyT
  rw [Set.mem_iUnion₂] at hy_union
  obtain ⟨w', hw'_mem, hy_cell⟩ := hy_union

  have hxy_in_prod : x * y ∈ setMul (bp.bruhatCell w) (bp.bruhatCell w') :=
    ⟨x, hx_cell, y, hy_cell, rfl⟩

  have h_finite := (bd.cell_mul_finite w w').choose_spec
  have hxy_in_cells := h_finite hxy_in_prod

  rw [Set.mem_iUnion₂] at hxy_in_cells ⊢
  obtain ⟨u, hu_mem, hxy_u⟩ := hxy_in_cells
  exact ⟨u, Finset.mem_biUnion.mpr ⟨w, hw_mem, Finset.mem_biUnion.mpr ⟨w', hw'_mem, hu_mem⟩⟩, hxy_u⟩

/-- The inverse of a BN-pair bounded set is BN-pair bounded. -/
theorem bnpair_inv_bounded {G : Type*} [Group G] {B_idx : Type*}
    {M : CoxeterMatrix B_idx} (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (S : Set G) (hS : BNPairBoundedPredicate bp S) :
    BNPairBoundedPredicate bp ((fun x => x⁻¹) '' S) := by
  classical
  obtain ⟨ws, hS⟩ := hS

  refine ⟨ws.image (·⁻¹), ?_⟩
  intro g hg
  obtain ⟨x, hxS, rfl⟩ := hg
  have hx_union := hS hxS
  rw [Set.mem_iUnion₂] at hx_union ⊢
  obtain ⟨w, hw_mem, hx_cell⟩ := hx_union
  exact ⟨w⁻¹, Finset.mem_image.mpr ⟨w, hw_mem, rfl⟩, bd.cell_inv w x hx_cell⟩

/-- Every element of $G$ lies in some Bruhat cell of the BN-pair. -/
theorem bnpair_element_in_cell {G : Type*} [Group G] {B_idx : Type*}
    {M : CoxeterMatrix B_idx} (bp : BNPair G M) (bd : BNPair.BruhatProperties bp) (g : G) :
    ∃ w : M.Group, g ∈ bp.bruhatCell w :=
  bd.cell_cover g

/-- Union of two BN-pair bounded sets is BN-pair bounded. -/
theorem bnpair_union_bounded {G : Type*} [Group G] {B_idx : Type*}
    {M : CoxeterMatrix B_idx} (bp : BNPair G M)
    (S T : Set G) (hS : BNPairBoundedPredicate bp S) (hT : BNPairBoundedPredicate bp T) :
    BNPairBoundedPredicate bp (S ∪ T) := by
  classical
  obtain ⟨ws₁, hS⟩ := hS
  obtain ⟨ws₂, hT⟩ := hT
  exact ⟨ws₁ ∪ ws₂, Set.union_subset
    (hS.trans (Set.biUnion_subset_biUnion_left (Finset.coe_subset.mpr Finset.subset_union_left)))
    (hT.trans (Set.biUnion_subset_biUnion_left (Finset.coe_subset.mpr Finset.subset_union_right)))⟩

/-- A proper coatom-type parabolic subgroup $\mathrm{Univ} \setminus \{s\}$ corresponds to a finite
Weyl-image. -/
theorem proper_parabolic_finite
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (bp : BNPair G M)
    (s : B_idx) :
    ∃ (ws : Finset M.Group),
      ∀ w, w ∈ bp.parabolicSubgroupW (Set.univ \ {s}) → w ∈ ws := by sorry

/-- Each coatom standard parabolic subgroup $P_{\mathrm{Univ} \setminus \{s\}}$ is BN-pair bounded. -/
theorem coatom_parabolic_bounded
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (s : B_idx) :
    BNPairBoundedPredicate bp (bp.standardParabolic (Set.univ \ {s})) := by

  obtain ⟨ws, hws⟩ := proper_parabolic_finite bp s

  exact ⟨ws, fun g hg => by
    obtain ⟨w, hw, hg_cell⟩ := Set.mem_iUnion₂.mp hg
    exact Set.mem_biUnion (hws w hw) hg_cell⟩

/-- For infinite Weyl group, the whole group $G = P_{\mathrm{Univ}}$ is not BN-pair bounded. -/
theorem whole_group_not_bounded
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    [Infinite M.Group]
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp) :
    ¬ BNPairBoundedPredicate bp (bp.standardParabolic Set.univ) := by

  intro ⟨ws, h_cover⟩

  have h_parab_top : bp.parabolicSubgroupW Set.univ = ⊤ := by
    unfold BNPair.parabolicSubgroupW
    rw [Set.image_univ]
    exact M.toCoxeterSystem.subgroup_closure_range_simple


  have h_all_in_ws : ∀ w : M.Group, w ∈ ws := by
    intro w
    obtain ⟨g, hg⟩ := BNPair.exists_mem_bruhatCell bp w
    have hg_in_parab : g ∈ bp.standardParabolic Set.univ :=
      Set.mem_iUnion₂.mpr ⟨w, h_parab_top ▸ Subgroup.mem_top w, hg⟩
    have hg_in_union := h_cover hg_in_parab
    obtain ⟨w', hw'_mem, hg_cell'⟩ := Set.mem_iUnion₂.mp hg_in_union
    have : w = w' := bd.cell_disjoint w w' ⟨g, hg, hg_cell'⟩
    rwa [this]

  haveI : Fintype M.Group := ⟨ws, h_all_in_ws⟩
  exact not_finite M.Group

/-- Standard parabolic subgroups are monotone in the simple-root subset. -/
lemma standardParabolic_mono
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (bp : BNPair G M) (S₁ S₂ : Set B_idx) (h : S₁ ⊆ S₂) :
    bp.standardParabolic S₁ ⊆ bp.standardParabolic S₂ := by
  intro g hg
  obtain ⟨w, hw, hg_cell⟩ := Set.mem_iUnion₂.mp hg
  refine Set.mem_iUnion₂.mpr ⟨w, ?_, hg_cell⟩
  exact Subgroup.closure_mono (Set.image_mono h) hw

/-- Bruhat–Tits fixed point theorem (FPT) coatom step: if $K$ is a maximal bounded subgroup
containing $B$ with $K = P_{S'}$, then $S'$ is a coatom $\mathrm{Univ} \setminus \{s_0\}$. -/
theorem bruhatTitsFPT_maximal_is_coatom
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    [Infinite M.Group]
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (born : GroupBornology G)
    (hborn : born.isBounded = BNPairBoundedPredicate bp)
    (K : Subgroup G) (hK : IsMaximalBounded born K)
    (hB_le_K : bp.B ≤ K)
    (S' : Set B_idx) (hS' : (K : Set G) = bp.standardParabolic S') :
    ∃ s₀ : B_idx, S' = Set.univ \ {s₀} := by

  by_contra h_not_coatom

  by_cases h_univ : S' = Set.univ
  ·
    have hK_bounded := hK.1
    rw [IsBoundedSubgroup, hborn] at hK_bounded
    have : BNPairBoundedPredicate bp (bp.standardParabolic Set.univ) := by
      rwa [← h_univ, ← hS']
    exact whole_group_not_bounded bp bd this
  ·

    have ⟨s₁, hs₁⟩ : ∃ s₁ : B_idx, s₁ ∉ S' := by
      by_contra h_all
      push_neg at h_all
      exact h_univ (Set.eq_univ_of_forall h_all)

    have ⟨s₂, hs₂, hs₂_ne⟩ : ∃ s₂ : B_idx, s₂ ∉ S' ∧ s₂ ≠ s₁ := by
      by_contra h_all
      push_neg at h_all
      apply h_not_coatom
      refine ⟨s₁, ?_⟩
      ext x
      constructor
      · intro hx
        exact ⟨Set.mem_univ x, fun hxs => by
          rw [Set.mem_singleton_iff] at hxs; subst hxs; exact hs₁ hx⟩
      · intro ⟨_, hx_ne⟩
        by_contra hx_not
        have := h_all x hx_not
        exact hx_ne (Set.mem_singleton_iff.mpr this)


    have h_S'_sub : S' ⊆ Set.univ \ {s₂} := by
      intro x hx
      exact ⟨Set.mem_univ x, fun hxs => hs₂ (Set.mem_singleton_iff.mp hxs ▸ hx)⟩

    have h_S'_ne : S' ≠ Set.univ \ {s₂} := by
      intro heq
      exact hs₁ (heq ▸ ⟨Set.mem_univ s₁, fun h => hs₂_ne (Set.mem_singleton_iff.mp h).symm⟩)

    have h_parabolic_sub := standardParabolic_mono bp S' (Set.univ \ {s₂}) h_S'_sub

    have h_parabolic_ne : bp.standardParabolic S' ≠
        bp.standardParabolic (Set.univ \ {s₂}) := by
      intro heq
      exact h_S'_ne (BNPair.standardParabolicInjective bp bd S' _ heq)

    have h_sg := BNPair.parabolicsAreSubgroups bp bd (Set.univ \ {s₂})
    let H : Subgroup G := {
      carrier := bp.standardParabolic (Set.univ \ {s₂})
      mul_mem' := fun ha hb => h_sg.2.1 _ _ ha hb
      one_mem' := h_sg.1
      inv_mem' := fun ha => h_sg.2.2 _ ha
    }

    have hK_le_H : K ≤ H := by
      intro g hg
      show g ∈ bp.standardParabolic (Set.univ \ {s₂})
      exact h_parabolic_sub (hS' ▸ hg)
    have hK_ne_H : K ≠ H := by
      intro heq
      apply h_parabolic_ne
      have : (K : Set G) = (H : Set G) := by rw [heq]
      rw [hS'] at this
      exact this
    have hK_lt_H : K < H := lt_of_le_of_ne hK_le_H hK_ne_H

    have hH_bounded : IsBoundedSubgroup born H := by
      rw [IsBoundedSubgroup, hborn]
      exact coatom_parabolic_bounded bp bd s₂

    exact hK.2 H hK_lt_H hH_bounded

/-- Geometric input to Bruhat–Tits FPT: every maximal bounded subgroup $K$ admits a conjugate
containing $B$. -/
theorem bruhatTitsFPT_conjugate_contains_B_geometric
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (born : GroupBornology G)
    (hborn : born.isBounded = BNPairBoundedPredicate bp)
    (K : Subgroup G) (hK : IsMaximalBounded born K) :
    ∃ (g : G), bp.B ≤ K.map (MulAut.conj g).toMonoidHom := by sorry

/-- Carrier of a conjugated subgroup $gKg^{-1}$ lies inside the set product $\{g\} \cdot K \cdot \{g^{-1}\}$. -/
lemma subgroup_map_conj_carrier_subset_setMul
    {G : Type*} [Group G] (g : G) (K : Subgroup G) :
    (K.map (MulAut.conj g).toMonoidHom : Set G) ⊆
      setMul (setMul {g} (K : Set G)) {g⁻¹} := by
  intro x hx
  simp only [SetLike.mem_coe, Subgroup.mem_map] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  show g * k * g⁻¹ ∈ _
  exact ⟨g * k, ⟨g, Set.mem_singleton g, k, hk, rfl⟩, g⁻¹, Set.mem_singleton g⁻¹, rfl⟩

/-- Conjugation preserves boundedness of subgroups. -/
lemma isBoundedSubgroup_map_conj
    {G : Type*} [Group G]
    (born : GroupBornology G)
    (K : Subgroup G) (hK : IsBoundedSubgroup born K) (g : G) :
    IsBoundedSubgroup born (K.map (MulAut.conj g).toMonoidHom) := by
  apply born.subset_bounded
    (born.product_bounded (born.product_bounded (born.singleton_bounded g) hK)
      (born.singleton_bounded g⁻¹))
  exact subgroup_map_conj_carrier_subset_setMul g K

/-- Conjugation preserves maximal-boundedness of subgroups. -/
lemma isMaximalBounded_map_conj
    {G : Type*} [Group G]
    (born : GroupBornology G)
    (K : Subgroup G) (hK : IsMaximalBounded born K) (g : G) :
    IsMaximalBounded born (K.map (MulAut.conj g).toMonoidHom) := by
  constructor
  ·
    exact isBoundedSubgroup_map_conj born K hK.1 g
  ·
    intro H hH_lt hH_bounded

    set H' := H.map (MulAut.conj g⁻¹).toMonoidHom with hH'_def

    have hH'_bounded : IsBoundedSubgroup born H' :=
      isBoundedSubgroup_map_conj born H hH_bounded g⁻¹

    have hK_lt_H' : K < H' := by
      have hinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom :=
        (MulAut.conj g⁻¹).injective


      have h_recover : (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = K := by
        rw [Subgroup.map_map]
        convert Subgroup.map_id K using 2
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      rw [← h_recover]
      constructor
      · exact Subgroup.map_mono (le_of_lt hH_lt)
      · intro heq
        have h2 := (Subgroup.map_le_map_iff_of_injective hinj).mp heq.ge
        exact absurd (le_antisymm h2 (le_of_lt hH_lt)) (ne_of_lt hH_lt).symm

    exact hK.2 H' hK_lt_H' hH'_bounded

/-- Strengthened Bruhat–Tits FPT: a conjugate of a maximal bounded $K$ both contains $B$ and is itself maximal bounded. -/
theorem bruhatTitsFPT_conjugate_contains_B
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (born : GroupBornology G)
    (hborn : born.isBounded = BNPairBoundedPredicate bp)
    (K : Subgroup G) (hK : IsMaximalBounded born K) :
    ∃ (g : G),
      bp.B ≤ K.map (MulAut.conj g).toMonoidHom ∧
      IsMaximalBounded born (K.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨g, hB_le⟩ := bruhatTitsFPT_conjugate_contains_B_geometric bp bd born hborn K hK
  exact ⟨g, hB_le, isMaximalBounded_map_conj born K hK g⟩

/-- Carrier set of $gKg^{-1}$ equals the conjugate image $\{gkg^{-1} : k \in K\}$. -/
lemma subgroup_map_conj_coe {G : Type*} [Group G] (g : G) (K : Subgroup G) :
    (K.map (MulAut.conj g).toMonoidHom : Set G) =
    (fun x => g * x * g⁻¹) '' (K : Set G) := by
  ext x; simp [MulAut.conj_apply]

/-- Bruhat–Tits FPT: every maximal bounded subgroup $K$ is conjugate to a standard parabolic
$P_{\mathrm{Univ} \setminus \{s_0\}}$. -/
theorem bruhatTitsFPT_maximal_conjugate_to_standard
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    [Infinite M.Group]
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (born : GroupBornology G)
    (hborn : born.isBounded = BNPairBoundedPredicate bp)
    (K : Subgroup G) (hK : IsMaximalBounded born K) :
    ∃ (g : G) (s₀ : B_idx),
      (fun x => g * x * g⁻¹) '' (K : Set G) =
        bp.standardParabolic (Set.univ \ {s₀}) := by

  obtain ⟨g, hB_le, hK'_max⟩ := bruhatTitsFPT_conjugate_contains_B bp bd born hborn K hK

  set K' := K.map (MulAut.conj g).toMonoidHom with hK'_def

  obtain ⟨S', hS'⟩ := bd.subgroup_over_B_eq_parabolic K' hB_le

  obtain ⟨s₀, hs₀⟩ := bruhatTitsFPT_maximal_is_coatom bp bd born hborn K' hK'_max hB_le S' hS'

  exact ⟨g, s₀, by rw [← subgroup_map_conj_coe, hS', hs₀]⟩

/-- Every bounded subgroup is contained, after conjugation, in some *proper* parabolic subgroup. -/
theorem bruhatTitsFPT_bounded_conj_in_proper_parabolic
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (born : GroupBornology G)
    (hborn : born.isBounded = BNPairBoundedPredicate bp)
    (K : Subgroup G) (hK : IsBoundedSubgroup born K) :
    ∃ (g : G) (S' : Set B_idx), S' ≠ Set.univ ∧
      (fun x => g * x * g⁻¹) '' (K : Set G) ⊆
        bp.standardParabolic S' := by sorry

/-- Every bounded subgroup is contained, after conjugation, in some coatom standard parabolic
$P_{\mathrm{Univ} \setminus \{s_0\}}$. -/
theorem bruhatTitsFPT_bounded_conj_in_parabolic
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (born : GroupBornology G)
    (hborn : born.isBounded = BNPairBoundedPredicate bp)
    (K : Subgroup G) (hK : IsBoundedSubgroup born K) :
    ∃ (g : G) (s₀ : B_idx),
      (fun x => g * x * g⁻¹) '' (K : Set G) ⊆
        bp.standardParabolic (Set.univ \ {s₀}) := by

  obtain ⟨g, S', hS'_proper, hconj⟩ :=
    bruhatTitsFPT_bounded_conj_in_proper_parabolic bp bd born hborn K hK

  have ⟨s₀, hs₀⟩ : ∃ s₀ : B_idx, s₀ ∉ S' := by
    by_contra h_all
    push_neg at h_all
    exact hS'_proper (Set.eq_univ_of_forall h_all)

  have hS'_sub : S' ⊆ Set.univ \ {s₀} := by
    intro x hx
    simp only [Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff, true_and]
    intro heq
    exact hs₀ (heq ▸ hx)

  exact ⟨g, s₀, hconj.trans (standardParabolic_mono bp S' (Set.univ \ {s₀}) hS'_sub)⟩

/-- The standard parabolic correspondence reflects the order: $P_{S_1} \subseteq P_{S_2}$ implies $S_1 \subseteq S_2$. -/
theorem standardParabolic_order_reflects
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    (bp : BNPair G M)
    (S₁ S₂ : Set B_idx) :
    bp.standardParabolic S₁ ⊆ bp.standardParabolic S₂ → S₁ ⊆ S₂ := by sorry

/-- A conjugate of a vertex stabilizer (coatom parabolic subgroup) is maximal bounded. -/
theorem vertex_stabilizer_conj_is_maximal_bounded
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    [Infinite M.Group]
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (born : GroupBornology G)
    (hborn : born.isBounded = BNPairBoundedPredicate bp)
    (g : G) (s₀ : B_idx)
    (P_vs : Subgroup G)
    (hP_vs : (P_vs : Set G) = bp.standardParabolic (Set.univ \ {s₀})) :
    IsMaximalBounded born (P_vs.map (MulAut.conj g).toMonoidHom) := by

  have hP_maximal : IsMaximalBounded born P_vs := by
    refine ⟨?_, ?_⟩
    ·
      show born.isBounded (P_vs : Set G)
      rw [hborn, hP_vs]
      exact coatom_parabolic_bounded bp bd s₀
    ·
      intro H hP_lt_H
      show ¬ born.isBounded (H : Set G)
      rw [hborn]
      intro ⟨ws, hH_cover⟩

      have hB_le_P : bp.B ≤ P_vs := by
        intro b hb
        show b ∈ (P_vs : Set G)
        rw [hP_vs]
        exact Set.mem_biUnion
          (bp.parabolicSubgroupW (Set.univ \ {s₀})).one_mem
          ⟨⟨b, hb⟩, ⟨1, bp.N.one_mem⟩, ⟨1, bp.B.one_mem⟩, bp.π.map_one,
            by simp [mul_one]⟩

      have hB_le_H : bp.B ≤ H := le_trans hB_le_P (le_of_lt hP_lt_H)

      obtain ⟨S'', hH_eq⟩ := bd.subgroup_over_B_eq_parabolic H hB_le_H

      suffices h_eq : S'' = Set.univ by
        rw [h_eq] at hH_eq
        exact whole_group_not_bounded bp bd ⟨ws, hH_eq ▸ hH_cover⟩

      have h_sub : bp.standardParabolic (Set.univ \ {s₀}) ⊆
          bp.standardParabolic S'' := by
        intro x hx
        have hx_P : x ∈ (P_vs : Set G) := by
          show x ∈ (P_vs : Set G)
          rw [hP_vs]
          exact hx
        have : x ∈ (H : Set G) := (le_of_lt hP_lt_H) hx_P
        rwa [hH_eq] at this

      have h_S_ne : Set.univ \ {s₀} ≠ S'' := by
        intro heq
        have : (P_vs : Set G) = (H : Set G) := by
          rw [hP_vs, heq]; exact hH_eq.symm
        exact ne_of_lt hP_lt_H (SetLike.ext' this)


      have h_parabolic_reflects_order : ∀ S₁ S₂ : Set B_idx,
          bp.standardParabolic S₁ ⊆ bp.standardParabolic S₂ → S₁ ⊆ S₂ :=
        fun S₁ S₂ => standardParabolic_order_reflects bp S₁ S₂

      have h_S_sub : Set.univ \ {s₀} ⊆ S'' := h_parabolic_reflects_order _ _ h_sub

      ext x
      constructor
      · intro _; exact Set.mem_univ x
      · intro _
        by_cases hx : x = s₀
        · subst hx
          by_contra hc
          apply h_S_ne
          ext y
          constructor
          · intro hy; exact h_S_sub hy
          · intro hy
            exact ⟨Set.mem_univ y, fun hy' => hc (Set.mem_singleton_iff.mp hy' ▸ hy)⟩
        · exact h_S_sub ⟨Set.mem_univ x, fun h => hx (Set.mem_singleton_iff.mp h)⟩

  exact isMaximalBounded_map_conj born P_vs hP_maximal g

/-- Every bounded subgroup is contained in some maximal bounded subgroup. -/
theorem bruhatTitsFPT_bounded_has_maximal
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    [Infinite M.Group]
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (born : GroupBornology G)
    (hborn : born.isBounded = BNPairBoundedPredicate bp)
    (K : Subgroup G) (hK : IsBoundedSubgroup born K) :
    ∃ (K_max : Subgroup G), IsMaximalBounded born K_max ∧ K ≤ K_max := by

  obtain ⟨g, s₀, hconj⟩ := bruhatTitsFPT_bounded_conj_in_parabolic bp bd born hborn K hK

  have h_sg := BNPair.parabolicsAreSubgroups bp bd (Set.univ \ {s₀})
  let P_vs : Subgroup G := {
    carrier := bp.standardParabolic (Set.univ \ {s₀})
    mul_mem' := fun ha hb => h_sg.2.1 _ _ ha hb
    one_mem' := h_sg.1
    inv_mem' := fun ha => h_sg.2.2 _ ha
  }


  let K_max := P_vs.map (MulAut.conj g⁻¹).toMonoidHom
  have hK_max_mb : IsMaximalBounded born K_max :=
    vertex_stabilizer_conj_is_maximal_bounded bp bd born hborn g⁻¹ s₀ P_vs rfl

  refine ⟨K_max, hK_max_mb, ?_⟩


  intro k hk
  show k ∈ P_vs.map (MulAut.conj g⁻¹).toMonoidHom
  rw [Subgroup.mem_map]


  refine ⟨g * k * g⁻¹, ?_, ?_⟩
  ·
    exact hconj ⟨k, hk, rfl⟩
  ·
    simp [mul_assoc]

/-- Combined geometric statement of Bruhat–Tits FPT: existence of conjugating $g$, vertex $s_0$,
maximal bounded $K_{\max}$ containing $K$, with conjugated $K$ inside the coatom parabolic. -/
theorem bruhatTitsFPT_geometric_core
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    [Infinite M.Group]
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (born : GroupBornology G)
    (hborn : born.isBounded = BNPairBoundedPredicate bp)
    (K : Subgroup G) (hK : IsBoundedSubgroup born K) :
    ∃ (g : G) (s₀ : B_idx) (K_max : Subgroup G),
      (fun x => g * x * g⁻¹) '' (K : Set G) ⊆
        bp.standardParabolic (Set.univ \ {s₀}) ∧
      IsMaximalBounded born K_max ∧ K ≤ K_max := by

  obtain ⟨g, s₀, hconj⟩ := bruhatTitsFPT_bounded_conj_in_parabolic bp bd born hborn K hK

  obtain ⟨K_max, hK_max, hle⟩ := bruhatTitsFPT_bounded_has_maximal bp bd born hborn K hK

  exact ⟨g, s₀, K_max, hconj, hK_max, hle⟩

/-- Wrapper: every bounded subgroup sits in some maximal bounded subgroup. -/
theorem bruhatTitsFPT_bounded_in_maximal
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    [Infinite M.Group]
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (born : GroupBornology G)
    (hborn : born.isBounded = BNPairBoundedPredicate bp)
    (K : Subgroup G) (hK : IsBoundedSubgroup born K) :
    ∃ K_max : Subgroup G, IsMaximalBounded born K_max ∧ K ≤ K_max := by
  obtain ⟨_, _, K_max, _, hmax, hle⟩ := bruhatTitsFPT_geometric_core bp bd born hborn K hK
  exact ⟨K_max, hmax, hle⟩

/-- Every bounded subgroup is contained, up to conjugation, in a vertex stabilizer parabolic. -/
theorem bruhatTitsFPT_bounded_in_vertex_stabilizer
    {G : Type*} [Group G] {B_idx : Type*} {M : CoxeterMatrix B_idx}
    [Infinite M.Group]
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (born : GroupBornology G)
    (hborn : born.isBounded = BNPairBoundedPredicate bp)
    (K : Subgroup G) (hK : IsBoundedSubgroup born K) :
    ∃ (g : G) (s₀ : B_idx),
      (fun x => g * x * g⁻¹) '' (K : Set G) ⊆
        bp.standardParabolic (Set.univ \ {s₀}) := by

  obtain ⟨K_max, hK_max, hle⟩ :=
    bruhatTitsFPT_bounded_in_maximal bp bd born hborn K hK

  obtain ⟨g, s₀, heq⟩ :=
    bruhatTitsFPT_maximal_conjugate_to_standard bp bd born hborn K_max hK_max

  exact ⟨g, s₀, heq ▸ Set.image_mono (SetLike.coe_subset_coe.mpr hle)⟩

/-- Alias: every bounded subgroup is contained in some maximal bounded subgroup. -/
theorem bounded_subgroup_in_maximal_bounded
    [Infinite M.Group]
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (born : GroupBornology G)
    (hborn : born.isBounded = BNPairBoundedPredicate bp)
    (K : Subgroup G) (hK : IsBoundedSubgroup born K) :
    ∃ K_max : Subgroup G, IsMaximalBounded born K_max ∧ K ≤ K_max :=


  bruhatTitsFPT_bounded_in_maximal bp bd born hborn K hK

/-- A maximal bounded subgroup containing $B$ equals a vertex-stabilizer parabolic
$P_{\mathrm{Univ} \setminus \{s_0\}}$ for some $s_0$. -/
theorem maximal_bounded_eq_vertex_stabilizer
    [Infinite M.Group]
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (born : GroupBornology G)
    (hborn : born.isBounded = BNPairBoundedPredicate bp)
    (K : Subgroup G) (hK : IsMaximalBounded born K)
    (hB_le_K : bp.B ≤ K) :
    ∃ s₀ : B_idx, (K : Set G) = bp.standardParabolic (Set.univ \ {s₀}) := by

  obtain ⟨S', hS'⟩ := bd.subgroup_over_B_eq_parabolic K hB_le_K


  obtain ⟨s₀, hs₀⟩ := bruhatTitsFPT_maximal_is_coatom bp bd born hborn K hK hB_le_K S' hS'
  exact ⟨s₀, hs₀ ▸ hS'⟩

/-- Each coatom standard parabolic $P_{\mathrm{Univ} \setminus \{s_0\}}$ is a maximal bounded
subgroup containing $B$. -/
theorem standardParabolic_maximal_bounded
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (born : GroupBornology G)
    (hborn : born.isBounded = BNPairBoundedPredicate bp)
    (s₀ : B_idx)

    (h_fin_parabolic : ∃ ws : Finset M.Group,
      ∀ w, w ∈ bp.parabolicSubgroupW (Set.univ \ {s₀}) → w ∈ ws)

    (h_not_bounded_top : ¬ BNPairBoundedPredicate bp (bp.standardParabolic Set.univ))


    (h_parabolic_reflects_order : ∀ S₁ S₂ : Set B_idx,
      bp.standardParabolic S₁ ⊆ bp.standardParabolic S₂ → S₁ ⊆ S₂) :
    ∃ K : Subgroup G, (K : Set G) = bp.standardParabolic (Set.univ \ {s₀}) ∧
      IsMaximalBounded born K ∧ bp.B ≤ K := by

  have h_sg := BNPair.parabolicsAreSubgroups bp bd (Set.univ \ {s₀})
  let K : Subgroup G := {
    carrier := bp.standardParabolic (Set.univ \ {s₀})
    mul_mem' := fun ha hb => h_sg.2.1 _ _ ha hb
    one_mem' := h_sg.1
    inv_mem' := fun ha => h_sg.2.2 _ ha
  }
  refine ⟨K, rfl, ⟨?_, ?_⟩, ?_⟩
  ·
    rw [IsBoundedSubgroup, hborn]
    obtain ⟨ws, hws⟩ := h_fin_parabolic
    exact ⟨ws, fun g hg => by
      obtain ⟨w, hw, hg_cell⟩ := Set.mem_iUnion₂.mp hg
      exact Set.mem_biUnion (hws w hw) hg_cell⟩
  ·
    intro H hKH
    rw [IsBoundedSubgroup, hborn]
    intro ⟨ws, hH_cover⟩

    have hB_le_K : bp.B ≤ K := by
      intro b hb
      show b ∈ bp.standardParabolic (Set.univ \ {s₀})
      exact Set.mem_biUnion
        (bp.parabolicSubgroupW (Set.univ \ {s₀})).one_mem
        ⟨⟨b, hb⟩, ⟨1, bp.N.one_mem⟩, ⟨1, bp.B.one_mem⟩, bp.π.map_one,
          by simp [mul_one]⟩
    have hB_le_H : bp.B ≤ H := le_trans hB_le_K (le_of_lt hKH)

    obtain ⟨S'', hH_eq⟩ := bd.subgroup_over_B_eq_parabolic H hB_le_H

    suffices h_eq : S'' = Set.univ by
      rw [h_eq] at hH_eq
      exact h_not_bounded_top ⟨ws, hH_eq ▸ hH_cover⟩

    have h_sub : bp.standardParabolic (Set.univ \ {s₀}) ⊆ bp.standardParabolic S'' := by
      intro g hg
      have : g ∈ (H : Set G) := (le_of_lt hKH) hg
      rwa [hH_eq] at this

    have h_S_sub : Set.univ \ {s₀} ⊆ S'' := h_parabolic_reflects_order _ _ h_sub

    have h_S_ne : Set.univ \ {s₀} ≠ S'' := by
      intro heq
      have : (K : Set G) = (H : Set G) := by
        show bp.standardParabolic _ = _
        rw [heq, ← hH_eq]
      exact ne_of_lt hKH (SetLike.ext' this)

    ext x
    constructor
    · intro _; exact Set.mem_univ x
    · intro _
      by_cases hx : x = s₀
      ·
        subst hx
        by_contra hc
        apply h_S_ne
        ext y
        constructor
        · intro hy; exact h_S_sub hy
        · intro hy
          exact ⟨Set.mem_univ y, fun hy' => hc (Set.mem_singleton_iff.mp hy' ▸ hy)⟩
      · exact h_S_sub ⟨Set.mem_univ x, fun h => hx (Set.mem_singleton_iff.mp h)⟩
  ·
    intro b hb
    show b ∈ bp.standardParabolic (Set.univ \ {s₀})
    exact Set.mem_biUnion
      (bp.parabolicSubgroupW (Set.univ \ {s₀})).one_mem
      ⟨⟨b, hb⟩, ⟨1, bp.N.one_mem⟩, ⟨1, bp.B.one_mem⟩, bp.π.map_one,
        by simp [mul_one]⟩

/-- Alias: every bounded subgroup is conjugate-contained in a vertex-stabilizer parabolic. -/
theorem bounded_subgroup_in_vertex_stabilizer
    [Infinite M.Group]
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (born : GroupBornology G)
    (hborn : born.isBounded = BNPairBoundedPredicate bp)
    (K : Subgroup G) (hK : IsBoundedSubgroup born K) :
    ∃ (g : G) (s₀ : B_idx),
      (fun x => g * x * g⁻¹) '' (K : Set G) ⊆
        bp.standardParabolic (Set.univ \ {s₀}) :=


  bruhatTitsFPT_bounded_in_vertex_stabilizer bp bd born hborn K hK

/-- Alias: every maximal bounded subgroup is conjugate to a standard coatom parabolic. -/
theorem maximal_bounded_conjugate_to_standard
    [Infinite M.Group]
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (born : GroupBornology G)
    (hborn : born.isBounded = BNPairBoundedPredicate bp)
    (K : Subgroup G) (hK : IsMaximalBounded born K) :
    ∃ (g : G) (s₀ : B_idx),
      (fun x => g * x * g⁻¹) '' (K : Set G) =
        bp.standardParabolic (Set.univ \ {s₀}) :=


  bruhatTitsFPT_maximal_conjugate_to_standard bp bd born hborn K hK

/-- Main BN-pair boundedness theorem (Section 17.7): a five-part conjunction packaging the various
parts of the Bruhat–Tits fixed point theorem under the relevant finiteness hypotheses. -/
theorem BNPairBoundedness
    [Infinite M.Group]
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (born : GroupBornology G)
    (hborn : born.isBounded = BNPairBoundedPredicate bp)

    (h_fin_parabolic : ∀ s₀ : B_idx, ∃ ws : Finset M.Group,
      ∀ w, w ∈ bp.parabolicSubgroupW (Set.univ \ {s₀}) → w ∈ ws)

    (h_not_bounded_top : ¬ BNPairBoundedPredicate bp (bp.standardParabolic Set.univ))


    (h_parabolic_reflects_order : ∀ S₁ S₂ : Set B_idx,
      bp.standardParabolic S₁ ⊆ bp.standardParabolic S₂ → S₁ ⊆ S₂) :

    (∀ K : Subgroup G, IsBoundedSubgroup born K →
      ∃ K_max : Subgroup G, IsMaximalBounded born K_max ∧ K ≤ K_max) ∧

    (∀ K : Subgroup G, IsBoundedSubgroup born K →
      ∃ (g : G) (s₀ : B_idx),
        (fun x => g * x * g⁻¹) '' (K : Set G) ⊆
          bp.standardParabolic (Set.univ \ {s₀})) ∧

    (∀ K : Subgroup G, IsMaximalBounded born K → bp.B ≤ K →
      ∃ s₀ : B_idx, (K : Set G) = bp.standardParabolic (Set.univ \ {s₀})) ∧

    (∀ s₀ : B_idx,
      ∃ K : Subgroup G, (K : Set G) = bp.standardParabolic (Set.univ \ {s₀}) ∧
        IsMaximalBounded born K ∧ bp.B ≤ K) ∧

    (∀ K : Subgroup G, IsMaximalBounded born K →
      ∃ (g : G) (s₀ : B_idx),
        (fun x => g * x * g⁻¹) '' (K : Set G) =
          bp.standardParabolic (Set.univ \ {s₀})) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    intro K hK
    exact bounded_subgroup_in_maximal_bounded bp bd born hborn K hK
  ·
    intro K hK
    exact bounded_subgroup_in_vertex_stabilizer bp bd born hborn K hK
  ·
    intro K hK hB_le_K
    exact maximal_bounded_eq_vertex_stabilizer bp bd born hborn K hK hB_le_K
  ·
    intro s₀
    exact standardParabolic_maximal_bounded bp bd born hborn s₀
      (h_fin_parabolic s₀) h_not_bounded_top h_parabolic_reflects_order
  ·
    intro K hK
    exact maximal_bounded_conjugate_to_standard bp bd born hborn K hK

/-- $s_0$ is a *special vertex* (with respect to a linear-part homomorphism) if every element in
the image of the linear part has a preimage in the standard parabolic $W_{\mathrm{Univ} \setminus \{s_0\}}$. -/
structure IsSpecialVertex (M : CoxeterMatrix B_idx)
    (linearPart : M.Group →* M.Group) (s₀ : B_idx) : Prop where
  surjective : ∀ wbar : M.Group, wbar ∈ Set.range linearPart →
    ∃ w : M.Group,
      w ∈ (Subgroup.closure
        (M.toCoxeterSystem.simple '' (Set.univ \ {s₀})) : Set M.Group) ∧
      linearPart w = wbar

/-- A *good maximal bounded subgroup*: a maximal bounded subgroup $K$ containing $B$ that equals
a coatom standard parabolic $P_{\mathrm{Univ} \setminus \{\mathrm{vertex}\}}$ where the vertex is special. -/
structure GoodMaximalBounded (bp : BNPair G M) (born : GroupBornology G)
    (linearPart : M.Group →* M.Group) where
  K : Subgroup G
  maximal_bounded : IsMaximalBounded born K
  contains_B : bp.B ≤ K
  vertex : B_idx
  eq_parabolic : (K : Set G) = bp.standardParabolic (Set.univ \ {vertex})
  is_special : IsSpecialVertex M linearPart vertex

/-- For an indecomposable affine Coxeter matrix admitting a special vertex, there exists a good
maximal bounded subgroup. -/
theorem good_maximal_bounded_exists
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (born : GroupBornology G)
    (hborn : born.isBounded = BNPairBoundedPredicate bp)
    (linearPart : M.Group →* M.Group)
    (hM_indec : M.IsIndecomposable) (hM_aff : M.IsAffine)

    (h_special : ∃ s₀ : B_idx, IsSpecialVertex M linearPart s₀)


    (h_fin_parabolic : ∀ s₀ : B_idx, ∃ ws : Finset M.Group,
      ∀ w, w ∈ bp.parabolicSubgroupW (Set.univ \ {s₀}) → w ∈ ws)
    (h_not_bounded_top : ¬ BNPairBoundedPredicate bp (bp.standardParabolic Set.univ))
    (h_parabolic_reflects_order : ∀ S₁ S₂ : Set B_idx,
      bp.standardParabolic S₁ ⊆ bp.standardParabolic S₂ → S₁ ⊆ S₂) :
    ∃ (s₀ : B_idx) (K : Subgroup G),

      (K : Set G) = bp.standardParabolic (Set.univ \ {s₀}) ∧

      IsMaximalBounded born K ∧

      bp.B ≤ K ∧

      IsSpecialVertex M linearPart s₀ := by

  obtain ⟨s₀, hs₀⟩ := h_special

  obtain ⟨K, hK_eq, hK_max, hK_B⟩ :=
    standardParabolic_maximal_bounded bp bd born hborn s₀
      (h_fin_parabolic s₀) h_not_bounded_top h_parabolic_reflects_order

  exact ⟨s₀, K, hK_eq, hK_max, hK_B, hs₀⟩

/-- Specialization of `standardParabolic_maximal_bounded` for infinite Weyl groups, using
`proper_parabolic_finite` and `whole_group_not_bounded` as the finiteness inputs. -/
theorem standardParabolic_maximal_bounded'
    [Infinite M.Group]
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (born : GroupBornology G)
    (hborn : born.isBounded = BNPairBoundedPredicate bp)
    (s₀ : B_idx)
    (h_parabolic_reflects_order : ∀ S₁ S₂ : Set B_idx,
      bp.standardParabolic S₁ ⊆ bp.standardParabolic S₂ → S₁ ⊆ S₂) :
    ∃ K : Subgroup G, (K : Set G) = bp.standardParabolic (Set.univ \ {s₀}) ∧
      IsMaximalBounded born K ∧ bp.B ≤ K :=
  standardParabolic_maximal_bounded bp bd born hborn s₀
    (proper_parabolic_finite bp s₀)
    (whole_group_not_bounded bp bd)
    h_parabolic_reflects_order

/-- Specialization of `BNPairBoundedness` to infinite Weyl groups assuming only the order-reflection
hypothesis. -/
theorem BNPairBoundedness'
    [Infinite M.Group]
    (bp : BNPair G M) (bd : BNPair.BruhatProperties bp)
    (born : GroupBornology G)
    (hborn : born.isBounded = BNPairBoundedPredicate bp)
    (h_parabolic_reflects_order : ∀ S₁ S₂ : Set B_idx,
      bp.standardParabolic S₁ ⊆ bp.standardParabolic S₂ → S₁ ⊆ S₂) :

    (∀ K : Subgroup G, IsBoundedSubgroup born K →
      ∃ K_max : Subgroup G, IsMaximalBounded born K_max ∧ K ≤ K_max) ∧

    (∀ K : Subgroup G, IsBoundedSubgroup born K →
      ∃ (g : G) (s₀ : B_idx),
        (fun x => g * x * g⁻¹) '' (K : Set G) ⊆
          bp.standardParabolic (Set.univ \ {s₀})) ∧

    (∀ K : Subgroup G, IsMaximalBounded born K → bp.B ≤ K →
      ∃ s₀ : B_idx, (K : Set G) = bp.standardParabolic (Set.univ \ {s₀})) ∧

    (∀ s₀ : B_idx,
      ∃ K : Subgroup G, (K : Set G) = bp.standardParabolic (Set.univ \ {s₀}) ∧
        IsMaximalBounded born K ∧ bp.B ≤ K) ∧

    (∀ K : Subgroup G, IsMaximalBounded born K →
      ∃ (g : G) (s₀ : B_idx),
        (fun x => g * x * g⁻¹) '' (K : Set G) =
          bp.standardParabolic (Set.univ \ {s₀})) :=
  BNPairBoundedness bp bd born hborn
    (fun s₀ => proper_parabolic_finite bp s₀)
    (whole_group_not_bounded bp bd)
    h_parabolic_reflects_order

end CompactSubgroups
