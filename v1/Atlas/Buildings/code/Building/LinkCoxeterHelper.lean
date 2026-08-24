/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Link
import Atlas.Buildings.code.CoxeterGroup.ParabolicSubgroups
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {V : Type*} [DecidableEq V]

/-- Gallery-connectedness of the link of a face $\sigma$ in a Coxeter complex $A$: any two chambers
of $\mathrm{lk}_A(\sigma)$ are joined by a gallery, using the Coxeter labelling of $A$ via its
parabolic subgroup structure. -/
theorem coxeter_link_gallery_connected
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (σ : Finset V) (hσ : σ ∈ A.faces)
    (hσ_proper : ∃ C, A.IsMaximal C ∧ σ ⊂ C) :
    ∀ C D,
      (A.linkComplex σ hσ).IsMaximal C →
      (A.linkComplex σ hσ).IsMaximal D →
      ∃ g : Gallery (A.linkComplex σ hσ),
        g.chambers.head? = some C ∧ g.chambers.getLast? = some D := by sorry

/-- A chamber complex equipped with a Coxeter labelling (injective, surjective, and
adjacency-preserving) is thin: each codimension-one face is contained in exactly two chambers. -/
theorem coxeter_labeling_implies_thin
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C')) :
    cc.IsThin := by sorry

/-- Thinness is inherited by links: if $A$ has a thin chamber complex structure $cc$, then the
link $\mathrm{lk}_A(\sigma)$ is also thin under any chamber complex structure $cc'$. -/
theorem link_thin_of_ambient_thin
    (A : SimplicialComplex V)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (hcc_thin : cc.IsThin)
    (σ : Finset V) (hσ : σ ∈ A.faces)
    (hσ_proper : ∃ C, A.IsMaximal C ∧ σ ⊂ C)
    (cc' : ChamberComplex V)
    (hcc'_eq : cc'.toSimplicialComplex = A.linkComplex σ hσ) :
    cc'.IsThin := by sorry

/-- The link of a face in a Coxeter complex is thin, combining
`coxeter_labeling_implies_thin` and `link_thin_of_ambient_thin`. -/
theorem coxeter_link_thin
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (σ : Finset V) (hσ : σ ∈ A.faces)
    (hσ_proper : ∃ C, A.IsMaximal C ∧ σ ⊂ C)
    (cc' : ChamberComplex V)
    (hcc'_eq : cc'.toSimplicialComplex = A.linkComplex σ hσ) :
    cc'.IsThin :=
  link_thin_of_ambient_thin A cc hcc_eq
    (coxeter_labeling_implies_thin A B_idx M cc hcc_eq φ hinj hsurj hadj)
    σ hσ hσ_proper cc' hcc'_eq

/-- Local version of `linkComplex_maximal_of_union_maximal`: if $\sigma \cup \tau$ is a maximal
face of $K$ and $\tau$ lies in $\mathrm{lk}_K(\sigma)$, then $\tau$ is maximal in the link. -/
lemma linkComplex_maximal_of_union_maximal_local {K : SimplicialComplex V} {σ : Finset V}
    (hσ : σ ∈ K.faces) {τ : Finset V}
    (hτ_link : τ ∈ (K.linkComplex σ hσ).faces)
    (hστ_max : K.IsMaximal (σ ∪ τ)) :
    (K.linkComplex σ hσ).IsMaximal τ := by
  have hτ_data := (SimplicialComplex.mem_linkComplex_iff K σ hσ τ).mp hτ_link
  refine ⟨hτ_link, fun y hy hτy => ?_⟩
  have hy_data := (SimplicialComplex.mem_linkComplex_iff K σ hσ y).mp hy
  have h_eq := hστ_max.2 (σ ∪ y) hy_data.2.2 (Finset.union_subset_union_right hτy)
  ext v
  constructor
  · intro hv
    have := h_eq ▸ (Finset.mem_union_right σ hv)
    exact (Finset.mem_union.mp this).elim
      (fun h => absurd h (Finset.disjoint_right.mp hτ_data.2.1 hv)) id
  · intro hv
    have := h_eq.symm ▸ (Finset.mem_union_right σ hv)
    exact (Finset.mem_union.mp this).elim
      (fun h => absurd h (Finset.disjoint_right.mp hy_data.2.1 hv)) id

/-- Existence-of-maximal-faces axiom for the chamber complex structure on a link: every face of
$\mathrm{lk}_A(\sigma)$ extends to a maximal face. -/
lemma link_cc_exists_maximal
    (A : SimplicialComplex V)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (σ : Finset V) (hσ : σ ∈ A.faces)
    (hσ_proper : ∃ C, A.IsMaximal C ∧ σ ⊂ C) :
    ∀ s ∈ (A.linkComplex σ hσ).faces,
      ∃ C, (A.linkComplex σ hσ).IsMaximal C ∧ s ⊆ C := by
  intro s hs
  have hs_data := (SimplicialComplex.mem_linkComplex_iff A σ hσ s).mp hs
  have hσs_in_A : σ ∪ s ∈ A.faces := hs_data.2.2

  have hσs_in_cc : σ ∪ s ∈ cc.toSimplicialComplex.faces := hcc_eq ▸ hσs_in_A
  obtain ⟨C, hC_max_cc, hσs_sub⟩ := cc.exists_maximal (σ ∪ s) hσs_in_cc

  have hC_max : A.IsMaximal C := hcc_eq ▸ hC_max_cc

  have hσ_sub_C : σ ⊆ C := Finset.subset_union_left.trans hσs_sub

  have hne : (C \ σ).Nonempty := by
    obtain ⟨v, hv⟩ := hs_data.1
    exact ⟨v, Finset.mem_sdiff.mpr ⟨hσs_sub (Finset.mem_union_right σ hv),
      Finset.disjoint_right.mp hs_data.2.1 hv⟩⟩

  have hCσ_link := SimplicialComplex.mem_linkComplex_of_sdiff A σ hσ C hC_max.1 hσ_sub_C hne

  have hC_eq : σ ∪ (C \ σ) = C := Finset.union_sdiff_of_subset hσ_sub_C
  have hCσ_max_A : A.IsMaximal (σ ∪ (C \ σ)) := by rw [hC_eq]; exact hC_max
  have hCσ_max_lk : (A.linkComplex σ hσ).IsMaximal (C \ σ) :=
    linkComplex_maximal_of_union_maximal_local hσ hCσ_link hCσ_max_A

  have hs_sub : s ⊆ C \ σ := by
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨hσs_sub (Finset.mem_union_right σ hv),
      Finset.disjoint_right.mp hs_data.2.1 hv⟩
  exact ⟨C \ σ, hCσ_max_lk, hs_sub⟩

/-- The link of a face in a Coxeter complex carries a thin chamber complex structure, packaging
the existence of maximals, gallery-connectedness, and thinness. -/
theorem link_has_chamber_complex_structure
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (σ : Finset V) (hσ : σ ∈ A.faces)
    (hσ_proper : ∃ C, A.IsMaximal C ∧ σ ⊂ C) :
    ∃ (cc' : ChamberComplex V),
      cc'.toSimplicialComplex = A.linkComplex σ hσ ∧ cc'.IsThin := by

  let cc' : ChamberComplex V :=
    { toSimplicialComplex := A.linkComplex σ hσ
      exists_maximal := link_cc_exists_maximal A cc hcc_eq σ hσ hσ_proper
      gallery_connected :=
        coxeter_link_gallery_connected A B_idx M cc hcc_eq φ hinj hsurj hadj σ hσ hσ_proper }

  have hthin : cc'.IsThin :=
    coxeter_link_thin A B_idx M cc hcc_eq φ hinj hsurj hadj σ hσ hσ_proper cc' rfl
  exact ⟨cc', rfl, hthin⟩

/-- Restricted Coxeter labelling for the link: there exists a subset $T \subseteq B_{\mathrm{idx}}$
of generators and a Coxeter labelling of $\mathrm{lk}_A(\sigma)$ valued in the parabolic subgroup
$\langle T \rangle$. -/
theorem link_coxeter_labeling_from_restricted
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (σ : Finset V) (hσ : σ ∈ A.faces)
    (hσ_proper : ∃ C, A.IsMaximal C ∧ σ ⊂ C) :
    ∃ (T : Set B_idx) (φ' : Finset V → (M.restrictToSet T).Group),
      (∀ C, (A.linkComplex σ hσ).IsMaximal C →
            ∀ D, (A.linkComplex σ hσ).IsMaximal D → φ' C = φ' D → C = D) ∧
      (∀ w : (M.restrictToSet T).Group,
            ∃ C, (A.linkComplex σ hσ).IsMaximal C ∧ φ' C = w) ∧
      (∀ C C', (A.linkComplex σ hσ).Adjacent C C' →
        CoxeterComplex.ChamberAdjacent (M.restrictToSet T) (φ' C) (φ' C')) := by sorry

/-- Repackaging the restricted Coxeter labelling as a full Coxeter labelling on the parabolic
subgroup $M' := M|_T$, giving a Coxeter labelling of $\mathrm{lk}_A(\sigma)$. -/
theorem parabolic_coset_labeling_full
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (σ : Finset V) (hσ : σ ∈ A.faces)
    (hσ_proper : ∃ C, A.IsMaximal C ∧ σ ⊂ C) :
    ∃ (B_idx' : Type) (M' : CoxeterMatrix B_idx') (φ' : Finset V → M'.Group),
      (∀ C, (A.linkComplex σ hσ).IsMaximal C →
            ∀ D, (A.linkComplex σ hσ).IsMaximal D → φ' C = φ' D → C = D) ∧
      (∀ w : M'.Group, ∃ C, (A.linkComplex σ hσ).IsMaximal C ∧ φ' C = w) ∧
      (∀ C C', (A.linkComplex σ hσ).Adjacent C C' →
        CoxeterComplex.ChamberAdjacent M' (φ' C) (φ' C')) := by

  obtain ⟨T, φ', hinj', hsurj', hadj'⟩ :=
    link_coxeter_labeling_from_restricted A B_idx M cc hcc_eq φ hinj hsurj hadj σ hσ hσ_proper

  exact ⟨T, M.restrictToSet T, φ', hinj', hsurj', hadj'⟩

/-- The link $\mathrm{lk}_A(\sigma)$ of a face $\sigma$ in a Coxeter complex carries a Coxeter
labelling, expressed via `parabolic_coset_labeling_full`. -/
theorem link_has_coxeter_labeling
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (σ : Finset V) (hσ : σ ∈ A.faces)
    (hσ_proper : ∃ C, A.IsMaximal C ∧ σ ⊂ C) :
    ∃ (B_idx' : Type) (M' : CoxeterMatrix B_idx') (φ' : Finset V → M'.Group),
      (∀ C, (A.linkComplex σ hσ).IsMaximal C →
            ∀ D, (A.linkComplex σ hσ).IsMaximal D → φ' C = φ' D → C = D) ∧
      (∀ w : M'.Group, ∃ C, (A.linkComplex σ hσ).IsMaximal C ∧ φ' C = w) ∧
      (∀ C C', (A.linkComplex σ hσ).Adjacent C C' →
        CoxeterComplex.ChamberAdjacent M' (φ' C) (φ' C')) :=
  parabolic_coset_labeling_full A B_idx M cc hcc_eq φ hinj hsurj hadj σ hσ hσ_proper

/-- The link of a face in a Coxeter complex is again a (sub-)Coxeter complex: it carries a thin
chamber complex structure together with a Coxeter labelling, combining
`link_has_chamber_complex_structure` and `link_has_coxeter_labeling`. -/
theorem coxeter_link_is_sub_coxeter
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (σ : Finset V) (hσ : σ ∈ A.faces)
    (hσ_proper : ∃ C, A.IsMaximal C ∧ σ ⊂ C) :
    ∃ (B_idx' : Type) (M' : CoxeterMatrix B_idx') (cc' : ChamberComplex V),
      cc'.toSimplicialComplex = A.linkComplex σ hσ ∧
      ∃ (φ' : Finset V → M'.Group),
        (∀ C, (A.linkComplex σ hσ).IsMaximal C →
              ∀ D, (A.linkComplex σ hσ).IsMaximal D → φ' C = φ' D → C = D) ∧
        (∀ w : M'.Group, ∃ C, (A.linkComplex σ hσ).IsMaximal C ∧ φ' C = w) ∧
        (∀ C C', (A.linkComplex σ hσ).Adjacent C C' →
          CoxeterComplex.ChamberAdjacent M' (φ' C) (φ' C')) ∧
        cc'.IsThin := by


  obtain ⟨cc', hcc'_eq, hcc'_thin⟩ :=
    link_has_chamber_complex_structure A B_idx M cc hcc_eq φ hinj hsurj hadj σ hσ hσ_proper
  obtain ⟨B_idx', M', φ', hinj', hsurj', hadj'⟩ :=
    link_has_coxeter_labeling A B_idx M cc hcc_eq φ hinj hsurj hadj σ hσ hσ_proper
  exact ⟨B_idx', M', cc', hcc'_eq, φ', hinj', hsurj', hadj', hcc'_thin⟩
