/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Link
import Atlas.Buildings.code.Building.Basic

open scoped Classical

variable {V : Type} [DecidableEq V]

open SimplicialComplex in
/-- If $C$ is maximal in the link complex $\mathrm{lk}_\sigma(\mathcal{B})$,
then $\sigma \cup C$ is a chamber (maximal face) of the ambient building. -/
theorem linkComplex_maximal_union_maximal
    (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (C : Finset V)
    (hC : (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C) :
    b.toChamberComplex.toSimplicialComplex.IsMaximal (σ ∪ C) := by
  set K := b.toChamberComplex.toSimplicialComplex
  have hC_link := hC.1
  rw [mem_linkComplex_iff] at hC_link
  refine ⟨hC_link.2.2, fun w hw h_sub => ?_⟩
  have hσw : σ ⊆ w := Finset.subset_union_left.trans h_sub
  by_cases hne : (w \ σ).Nonempty
  · have hw_link := mem_linkComplex_of_sdiff K σ hσ w hw hσw hne
    have hC_sub : C ⊆ w \ σ := by
      intro v hv
      exact Finset.mem_sdiff.mpr ⟨h_sub (Finset.mem_union_right σ hv),
        Finset.disjoint_right.mp hC_link.2.1 hv⟩
    rw [hC.2 (w \ σ) hw_link hC_sub, Finset.union_sdiff_of_subset hσw]
  · rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hne
    exfalso
    obtain ⟨v, hv⟩ := hC_link.1
    exact Finset.disjoint_right.mp hC_link.2.1 hv (hne (h_sub (Finset.mem_union_right σ hv)))

/-- Coxeter star projection: a minimal gallery in an apartment between
chambers $\sigma \cup C$ and $\sigma \cup D$ projects to a gallery in the
link $\mathrm{lk}_\sigma$ from $C$ to $D$ of no greater length. -/
theorem coxeter_star_gallery_projection
    {V : Type} [DecidableEq V]
    (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (hσA : σ ∈ A.faces)
    (C D : Finset V)
    (hC_link : C ∈ (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).faces)
    (hD_link : D ∈ (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).faces)
    (hC_max : (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C)
    (hD_max : (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal D)
    (g : Gallery b.toChamberComplex.toSimplicialComplex)
    (hg_conn : g.Connects (σ ∪ C) (σ ∪ D))
    (hg_in_A : ∀ E ∈ g.chambers, E ∈ A.faces)
    (hg_min : g.length = galleryDist b.toChamberComplex.toSimplicialComplex (σ ∪ C) (σ ∪ D)) :
    ∃ g' : Gallery (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ),
      g'.Connects C D ∧ g'.length ≤ g.length := by sorry

/-- If $C, D$ are each disjoint from $\sigma$ and $C \neq D$, then
$\sigma \cup C \neq \sigma \cup D$. -/
lemma union_ne_of_disjoint_ne (σ C D : Finset V)
    (hC_disj : Disjoint σ C) (hD_disj : Disjoint σ D) (hne : C ≠ D) :
    σ ∪ C ≠ σ ∪ D := by
  intro h
  apply hne
  have hC' : C = (σ ∪ C) \ σ := (Finset.union_sdiff_cancel_left hC_disj).symm
  have hD' : D = (σ ∪ D) \ σ := (Finset.union_sdiff_cancel_left hD_disj).symm
  rw [hC', hD', h]

/-- Axiom-form of the link distance bound: the gallery distance in the link
$\mathrm{lk}_\sigma$ between maximal faces $C, D$ is bounded by the gallery
distance between the chambers $\sigma \cup C, \sigma \cup D$ in the ambient
building. -/
theorem link_gallery_dist_le_axiom
    {V : Type} [DecidableEq V]
    (b : Building V) (σ : Finset V)
    (hσ : σ ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (hσ_proper : ∃ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C ∧ σ ⊂ C)
    (link_cc : ChamberComplex V)
    (h_link_cc : link_cc.toSimplicialComplex =
      b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ)
    (C D : Finset V)
    (hC_max : (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal C)
    (hD_max : (b.toChamberComplex.toSimplicialComplex.linkComplex σ hσ).IsMaximal D) :
    galleryDist link_cc.toSimplicialComplex C D ≤
      galleryDist b.toChamberComplex.toSimplicialComplex (σ ∪ C) (σ ∪ D) := by
  set K := b.toChamberComplex.toSimplicialComplex
  set lk := K.linkComplex σ hσ

  rw [h_link_cc]

  by_cases hCD : C = D
  · subst hCD; simp [galleryDist_self]

  have hσC_max : K.IsMaximal (σ ∪ C) := linkComplex_maximal_union_maximal b σ hσ C hC_max
  have hσD_max : K.IsMaximal (σ ∪ D) := linkComplex_maximal_union_maximal b σ hσ D hD_max

  obtain ⟨A, hA_apt, hσC_in_A, hσD_in_A⟩ :=
    b.apartmentSystem.contains_pair (σ ∪ C) (σ ∪ D) hσC_max hσD_max

  have hσ_in_A : σ ∈ A.faces :=
    A.down_closed hσC_in_A Finset.subset_union_left (K.nonempty_of_mem σ hσ)

  have hC_disj : Disjoint σ C := SimplicialComplex.linkComplex_disjoint K σ hσ C hC_max.1
  have hD_disj : Disjoint σ D := SimplicialComplex.linkComplex_disjoint K σ hσ D hD_max.1
  have hσCσD_ne : σ ∪ C ≠ σ ∪ D := union_ne_of_disjoint_ne σ C D hC_disj hD_disj hCD

  obtain ⟨gK, hgK_conn⟩ :=
    b.toChamberComplex.gallery_connected (σ ∪ C) (σ ∪ D) hσC_max hσD_max

  have hgK_conn' : gK.Connects (σ ∪ C) (σ ∪ D) := ⟨hgK_conn.1, hgK_conn.2⟩
  have hne : {n | ∃ g : Gallery K, g.Connects (σ ∪ C) (σ ∪ D) ∧ g.length = n}.Nonempty :=
    ⟨gK.length, gK, hgK_conn', rfl⟩

  have hgd : galleryDist K (σ ∪ C) (σ ∪ D) =
      sInf {n | ∃ g : Gallery K, g.Connects (σ ∪ C) (σ ∪ D) ∧ g.length = n} := by
    unfold galleryDist; rw [if_neg hσCσD_ne]
  obtain ⟨g₀, hg₀_conn, hg₀_len⟩ := Nat.sInf_mem hne
  have hg₀_min : g₀.length = galleryDist K (σ ∪ C) (σ ∪ D) := by
    rw [hgd]; exact hg₀_len

  have hg₀_in_A : ∀ E ∈ g₀.chambers, E ∈ A.faces :=
    b.apartmentSystem.gallery_convex A hA_apt (σ ∪ C) (σ ∪ D)
      hσC_in_A hσC_max hσD_in_A hσD_max g₀ hg₀_conn hg₀_min

  obtain ⟨g', hg'_conn, hg'_len⟩ :=
    coxeter_star_gallery_projection b σ hσ A hA_apt hσ_in_A C D
      hC_max.1 hD_max.1 hC_max hD_max g₀ hg₀_conn hg₀_in_A hg₀_min

  calc galleryDist lk C D
      ≤ g'.length := by
        by_cases hCD' : C = D
        · exact absurd hCD' hCD
        · unfold galleryDist; rw [if_neg hCD']
          exact Nat.sInf_le ⟨g', hg'_conn, rfl⟩
    _ ≤ g₀.length := hg'_len
    _ = galleryDist K (σ ∪ C) (σ ∪ D) := hg₀_min
