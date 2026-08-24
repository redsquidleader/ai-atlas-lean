/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Basic
import Atlas.Buildings.code.Building.AptIsCoxeterProof
import Atlas.Buildings.code.ChamberComplex.CoxeterComplex

open scoped Classical

variable {V : Type} [DecidableEq V]

/-- In a thin chamber complex, each facet $F$ of a chamber $C$ lies in
exactly one other chamber $D \ne C$. -/
theorem thin_unique_other_chamber
    (cc : ChamberComplex V)
    (hthin : cc.IsThin)
    (F C : Finset V)
    (hFC : cc.toSimplicialComplex.IsFacet F C)
    (hC : cc.toSimplicialComplex.IsMaximal C) :
    ∃! D, D ≠ C ∧ cc.toSimplicialComplex.IsFacet F D ∧
      cc.toSimplicialComplex.IsMaximal D :=
  hthin F C hFC hC

/-- In a Coxeter complex, a strictly monotone labelling on faces has
$|\text{lab}(s)| = |s|$ for every face $s$. -/
theorem coxeter_lab_card_eq_face_card
    {V : Type} [DecidableEq V]
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj_φ : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (L : Type) [DecidableEq L]
    (lab : Finset V → Finset L)
    (hmono : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab s ⊂ lab t)
    (s : Finset V) (hs : s ∈ A.faces) :
    (lab s).card = s.card := by sorry

/-- Each label in $\text{lab}(s)$ already appears in the label of some vertex
$v \in s$. -/
theorem coxeter_lab_vertex_in_face_label
    {V : Type} [DecidableEq V]
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj_φ : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (L : Type) [DecidableEq L]
    (lab : Finset V → Finset L)
    (hmono : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab s ⊂ lab t)
    (s : Finset V) (hs : s ∈ A.faces) (ℓ : L) (hℓ : ℓ ∈ lab s) :
    ∃ v ∈ s, ℓ ∈ lab {v} := by sorry

/-- On a chamber $C$, the labelling $\text{lab}$ is surjective onto
$\text{lab}(C)$. -/
theorem coxeter_lab_surj_on_chamber
    {V : Type} [DecidableEq V]
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj_φ : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (L : Type) [DecidableEq L]
    (lab : Finset V → Finset L)
    (hmono : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab s ⊂ lab t)
    (C : Finset V) (hC : A.IsMaximal C) (ℓ : L) :
    ℓ ∈ lab C := by sorry

/-- A labelling of a Coxeter complex factors through a vertex-level map:
$\text{lab}(s) = \{\sigma(v) \mid v \in s\}$ for some $\sigma : V \to L$. -/
theorem coxeter_single_labelling_factors
    {V : Type} [DecidableEq V]
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj_φ : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (L : Type) [DecidableEq L]
    (lab : Finset V → Finset L)
    (hmono : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab s ⊂ lab t)
    (C : Finset V) (hC : A.IsMaximal C) :
    ∃ (τ : V → L),
      (∀ s : Finset V, s ∈ A.faces → lab s = s.image τ) ∧
      Set.InjOn τ ↑C ∧
      (∀ ℓ : L, ∃ v, v ∈ C ∧ τ v = ℓ) := by

  have hone : ∀ v : V, ({v} : Finset V) ∈ A.faces → (lab {v}).card = 1 := by
    intro v hv
    have := coxeter_lab_card_eq_face_card A B_idx M cc hcc_eq φ hinj hsurj hadj_φ
      L lab hmono {v} hv
    simpa using this

  have hCne : C.Nonempty := A.nonempty_of_mem C hC.1
  haveI : Nonempty L := by
    obtain ⟨v, hv⟩ := hCne
    have hv_face : ({v} : Finset V) ∈ A.faces :=
      A.down_closed hC.1 (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hone v hv_face)
    exact ⟨a⟩

  have hdef : ∀ v : V, ∃ ℓ : L, ({v} : Finset V) ∈ A.faces → lab {v} = {ℓ} := by
    intro v
    by_cases hv : ({v} : Finset V) ∈ A.faces
    · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hone v hv)
      exact ⟨a, fun _ => ha⟩
    · exact ⟨Classical.arbitrary L, fun h => absurd h hv⟩
  let τ : V → L := fun v => (hdef v).choose
  have hτ_spec : ∀ v, ({v} : Finset V) ∈ A.faces → lab {v} = {τ v} :=
    fun v hv => (hdef v).choose_spec hv

  have hfact : ∀ s : Finset V, s ∈ A.faces → lab s = s.image τ := by
    intro s hs
    apply Finset.Subset.antisymm
    · intro ℓ hℓ
      obtain ⟨v, hv, hℓv⟩ := coxeter_lab_vertex_in_face_label A B_idx M cc hcc_eq φ
        hinj hsurj hadj_φ L lab hmono s hs ℓ hℓ
      have hv_face : ({v} : Finset V) ∈ A.faces :=
        A.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
      rw [hτ_spec v hv_face] at hℓv
      simp only [Finset.mem_singleton] at hℓv
      exact Finset.mem_image.mpr ⟨v, hv, hℓv.symm⟩
    · intro ℓ hℓ
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hℓ
      have hv_face : ({v} : Finset V) ∈ A.faces :=
        A.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
      have hτv_in : τ v ∈ lab {v} := by rw [hτ_spec v hv_face]; simp
      by_cases heq : ({v} : Finset V) = s
      · rw [← heq]; exact hτv_in
      · exact (hmono {v} s hv_face hs (lt_of_le_of_ne
          (Finset.singleton_subset_iff.mpr hv) heq)).subset hτv_in

  have hinj_τ : Set.InjOn τ ↑C := by
    apply Finset.injOn_of_card_image_eq
    rw [← hfact C hC.1]
    exact coxeter_lab_card_eq_face_card A B_idx M cc hcc_eq φ hinj hsurj hadj_φ
      L lab hmono C hC.1

  have hsurj_τ : ∀ ℓ : L, ∃ v, v ∈ C ∧ τ v = ℓ := by
    intro ℓ
    have hℓ_in : ℓ ∈ lab C := coxeter_lab_surj_on_chamber A B_idx M cc hcc_eq φ
      hinj hsurj hadj_φ L lab hmono C hC ℓ
    rw [hfact C hC.1] at hℓ_in
    exact Finset.mem_image.mp hℓ_in
  exact ⟨τ, hfact, hinj_τ, hsurj_τ⟩

/-- The vertex-level labelling is pointwise compatible: the label of a
vertex matches the singleton label of that vertex. -/
theorem coxeter_vertex_type_pointwise_compat
    {V : Type} [DecidableEq V]
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj_φ : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (L₁ L₂ : Type) [DecidableEq L₁] [DecidableEq L₂]
    (lab₁ : Finset V → Finset L₁) (lab₂ : Finset V → Finset L₂)
    (hmono₁ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab₁ s ⊂ lab₁ t)
    (hmono₂ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab₂ s ⊂ lab₂ t)
    (f : L₁ → L₂) (hf : Function.Bijective f)
    (C : Finset V) (hC : A.IsMaximal C)
    (hagree : lab₂ C = (lab₁ C).image f)
    (τ₁ : V → L₁) (hτ₁ : ∀ s : Finset V, s ∈ A.faces → lab₁ s = s.image τ₁)
    (τ₂ : V → L₂) (hτ₂ : ∀ s : Finset V, s ∈ A.faces → lab₂ s = s.image τ₂)
    (v : V) (hv : v ∈ C) :
    τ₂ v = f (τ₁ v) := by sorry

/-- A labelling on a face is compatible with subface labels: removing a vertex
removes its label from the labelling. -/
theorem coxeter_subface_label_compat
    {V : Type} [DecidableEq V]
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj_φ : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (L₁ L₂ : Type) [DecidableEq L₁] [DecidableEq L₂]
    (lab₁ : Finset V → Finset L₁) (lab₂ : Finset V → Finset L₂)
    (hmono₁ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab₁ s ⊂ lab₁ t)
    (hmono₂ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab₂ s ⊂ lab₂ t)
    (f : L₁ → L₂) (hf : Function.Bijective f)
    (C : Finset V) (hC : A.IsMaximal C)
    (hagree : lab₂ C = (lab₁ C).image f)
    (s : Finset V) (hs : s ∈ A.faces) (hsC : s ⊆ C) :
    lab₂ s = (lab₁ s).image f := by

  obtain ⟨τ₁, hτ₁_factor, _, _⟩ :=
    coxeter_single_labelling_factors A B_idx M cc hcc_eq φ hinj hsurj hadj_φ
      L₁ lab₁ hmono₁ C hC
  obtain ⟨τ₂, hτ₂_factor, _, _⟩ :=
    coxeter_single_labelling_factors A B_idx M cc hcc_eq φ hinj hsurj hadj_φ
      L₂ lab₂ hmono₂ C hC

  have hpointwise : ∀ v : V, v ∈ C → τ₂ v = f (τ₁ v) := by
    intro v hv
    exact coxeter_vertex_type_pointwise_compat A B_idx M cc hcc_eq φ hinj hsurj hadj_φ
      L₁ L₂ lab₁ lab₂ hmono₁ hmono₂ f hf C hC hagree τ₁ hτ₁_factor τ₂ hτ₂_factor v hv

  rw [hτ₂_factor s hs, hτ₁_factor s hs, Finset.image_image]
  apply Finset.image_congr
  intro v hv
  exact hpointwise v (hsC hv)

/-- The vertex-type function $\sigma : V \to L$ associated to a Coxeter
labelling, extracted from the chamber-level labels. -/
theorem coxeter_vertex_type_function
    {V : Type} [DecidableEq V]
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj_φ : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (L₁ L₂ : Type) [DecidableEq L₁] [DecidableEq L₂]
    (lab₁ : Finset V → Finset L₁) (lab₂ : Finset V → Finset L₂)
    (hmono₁ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab₁ s ⊂ lab₁ t)
    (hmono₂ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab₂ s ⊂ lab₂ t)
    (f : L₁ → L₂) (hf : Function.Bijective f)
    (C : Finset V) (hC : A.IsMaximal C)
    (hagree : lab₂ C = (lab₁ C).image f) :
    ∃ (τ₁ : V → L₁) (τ₂ : V → L₂),
      (∀ s : Finset V, s ∈ A.faces → lab₁ s = s.image τ₁) ∧
      (∀ s : Finset V, s ∈ A.faces → lab₂ s = s.image τ₂) ∧
      (∀ v : V, v ∈ C → τ₂ v = f (τ₁ v)) ∧
      Set.InjOn τ₁ ↑C ∧
      (∀ ℓ : L₁, ∃ v, v ∈ C ∧ τ₁ v = ℓ) := by

  obtain ⟨τ₁, hτ₁_factor, hτ₁_inj, hτ₁_surj⟩ :=
    coxeter_single_labelling_factors A B_idx M cc hcc_eq φ hinj hsurj hadj_φ
      L₁ lab₁ hmono₁ C hC
  obtain ⟨τ₂, hτ₂_factor, _, _⟩ :=
    coxeter_single_labelling_factors A B_idx M cc hcc_eq φ hinj hsurj hadj_φ
      L₂ lab₂ hmono₂ C hC

  have hpointwise : ∀ v : V, v ∈ C → τ₂ v = f (τ₁ v) := by
    intro v hv

    have hv_face : ({v} : Finset V) ∈ A.faces :=
      A.down_closed hC.1 (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
    have hv_sub : ({v} : Finset V) ⊆ C := Finset.singleton_subset_iff.mpr hv

    have hcompat := coxeter_subface_label_compat A B_idx M cc hcc_eq φ hinj hsurj hadj_φ
      L₁ L₂ lab₁ lab₂ hmono₁ hmono₂ f hf C hC hagree {v} hv_face hv_sub

    have h1 : lab₁ {v} = {τ₁ v} := by
      rw [hτ₁_factor {v} hv_face, Finset.image_singleton]

    have h2 : lab₂ {v} = {τ₂ v} := by
      rw [hτ₂_factor {v} hv_face, Finset.image_singleton]

    rw [h1, Finset.image_singleton] at hcompat
    rw [h2] at hcompat
    exact Finset.singleton_injective hcompat

  exact ⟨τ₁, τ₂, hτ₁_factor, hτ₂_factor, hpointwise, hτ₁_inj, hτ₁_surj⟩

/-- The labelling is surjective on each chamber: every label appears on
some vertex of the chamber. -/
theorem coxeter_chamber_labels_surj
    {V : Type} [DecidableEq V]
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj_φ : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (L : Type) [DecidableEq L]
    (lab : Finset V → Finset L)
    (hmono : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab s ⊂ lab t)
    (C₀ : Finset V) (hC₀ : A.IsMaximal C₀) :
    (∀ ℓ : L, ℓ ∈ lab C₀) ∧ (lab C₀).card = C₀.card := by

  obtain ⟨τ, _, hτ, _, _, hinj_τ, hsurj_τ⟩ :=
    coxeter_vertex_type_function A B_idx M cc hcc_eq φ hinj hsurj hadj_φ
      L L lab lab hmono hmono id Function.bijective_id C₀ hC₀
      (by simp [Finset.image_id])

  have hfact : lab C₀ = C₀.image τ := hτ C₀ hC₀.1
  constructor
  ·
    intro ℓ
    obtain ⟨v, hv, rfl⟩ := hsurj_τ ℓ
    rw [hfact]
    exact Finset.mem_image_of_mem τ hv
  ·
    rw [hfact]
    exact Finset.card_image_of_injOn hinj_τ

/-- Any two chambers of a Coxeter complex have the same label set. -/
theorem coxeter_chambers_same_label_set
    {V : Type} [DecidableEq V]
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj_φ : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (L : Type) [DecidableEq L]
    (lab : Finset V → Finset L)
    (hmono : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab s ⊂ lab t)
    (C D : Finset V) (hC : A.IsMaximal C) (hD : A.IsMaximal D) :
    lab C = lab D := by

  obtain ⟨hC_surj, _⟩ := coxeter_chamber_labels_surj A B_idx M cc hcc_eq φ hinj hsurj
    hadj_φ L lab hmono C hC
  obtain ⟨hD_surj, _⟩ := coxeter_chamber_labels_surj A B_idx M cc hcc_eq φ hinj hsurj
    hadj_φ L lab hmono D hD

  ext x
  simp [hC_surj, hD_surj]

/-- Adjacent chambers differ in label by exactly one vertex. -/
theorem coxeter_adj_label_step
    {V : Type} [DecidableEq V]
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj_φ : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (L₁ L₂ : Type) [DecidableEq L₁] [DecidableEq L₂]
    (lab₁ : Finset V → Finset L₁) (lab₂ : Finset V → Finset L₂)
    (hmono₁ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab₁ s ⊂ lab₁ t)
    (hmono₂ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab₂ s ⊂ lab₂ t)
    (f : L₁ → L₂) (hf : Function.Bijective f)
    (C₁ C₂ : Finset V) (hadj : A.Adjacent C₁ C₂)
    (hagree : lab₂ C₁ = (lab₁ C₁).image f) :
    lab₂ C₂ = (lab₁ C₂).image f := by

  have hC₁ : A.IsMaximal C₁ := hadj.1
  have hC₂ : A.IsMaximal C₂ := hadj.2.1

  have hlab₁_eq : lab₁ C₁ = lab₁ C₂ :=
    coxeter_chambers_same_label_set A B_idx M cc hcc_eq φ hinj hsurj hadj_φ
      L₁ lab₁ hmono₁ C₁ C₂ hC₁ hC₂
  have hlab₂_eq : lab₂ C₁ = lab₂ C₂ :=
    coxeter_chambers_same_label_set A B_idx M cc hcc_eq φ hinj hsurj hadj_φ
      L₂ lab₂ hmono₂ C₁ C₂ hC₁ hC₂

  rw [← hlab₂_eq, hagree, hlab₁_eq]

/-- A subface labelling step: how the labels of $s \cup \{v\}$ relate to
those of $s$. -/
theorem coxeter_subface_label_step
    {V : Type} [DecidableEq V]
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj_φ : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (L₁ L₂ : Type) [DecidableEq L₁] [DecidableEq L₂]
    (lab₁ : Finset V → Finset L₁) (lab₂ : Finset V → Finset L₂)
    (hmono₁ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab₁ s ⊂ lab₁ t)
    (hmono₂ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab₂ s ⊂ lab₂ t)
    (f : L₁ → L₂) (hf : Function.Bijective f)
    (C : Finset V) (hC : A.IsMaximal C)
    (hagree : lab₂ C = (lab₁ C).image f)
    (s : Finset V) (hs : s ∈ A.faces) (hsC : s ⊆ C) :
    lab₂ s = (lab₁ s).image f := by
  obtain ⟨τ₁, τ₂, hτ₁, hτ₂, hpointwise, _, _⟩ :=
    coxeter_vertex_type_function A B_idx M cc hcc_eq φ hinj hsurj hadj_φ
      L₁ L₂ lab₁ lab₂ hmono₁ hmono₂ f hf C hC hagree
  rw [hτ₂ s hs, hτ₁ s hs, Finset.image_image]
  apply Finset.image_congr
  intro v hv
  exact hpointwise v (hsC hv)

/-- Existence of a label bijection between any two chambers compatible with
the vertex labelling. -/
theorem coxeter_label_bijection_exists
    {V : Type} [DecidableEq V]
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj_φ : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (L₁ L₂ : Type) [DecidableEq L₁] [DecidableEq L₂]
    (lab₁ : Finset V → Finset L₁) (lab₂ : Finset V → Finset L₂)
    (hmono₁ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab₁ s ⊂ lab₁ t)
    (hmono₂ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab₂ s ⊂ lab₂ t)
    (C₀ : Finset V) (hC₀ : A.IsMaximal C₀) :
    ∃ (f : L₁ → L₂), Function.Bijective f ∧ lab₂ C₀ = (lab₁ C₀).image f := by

  obtain ⟨h1_surj, h1_card⟩ := coxeter_chamber_labels_surj A B_idx M cc hcc_eq φ hinj hsurj
    hadj_φ L₁ lab₁ hmono₁ C₀ hC₀
  obtain ⟨h2_surj, h2_card⟩ := coxeter_chamber_labels_surj A B_idx M cc hcc_eq φ hinj hsurj
    hadj_φ L₂ lab₂ hmono₂ C₀ hC₀

  haveI : Fintype L₁ := ⟨lab₁ C₀, h1_surj⟩
  haveI : Fintype L₂ := ⟨lab₂ C₀, h2_surj⟩

  have hs_univ : lab₁ C₀ = Finset.univ := by ext x; simp [h1_surj]
  have ht_univ : lab₂ C₀ = Finset.univ := by ext x; simp [h2_surj]

  have hcard : Fintype.card L₁ = Fintype.card L₂ := by
    rw [← Finset.card_univ, ← hs_univ, ← Finset.card_univ, ← ht_univ]
    omega

  exact ⟨Fintype.equivOfCardEq hcard, (Fintype.equivOfCardEq hcard).bijective, by
    rw [hs_univ, ht_univ]; ext y; simp [Finset.mem_univ]⟩

/-- The Coxeter labelling is determined along a gallery: agreement at one
chamber forces agreement throughout the chain. -/
lemma coxeter_label_agree_along_chain
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj_φ : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (L₁ L₂ : Type) [DecidableEq L₁] [DecidableEq L₂]
    (lab₁ : Finset V → Finset L₁) (lab₂ : Finset V → Finset L₂)
    (hmono₁ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab₁ s ⊂ lab₁ t)
    (hmono₂ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab₂ s ⊂ lab₂ t)
    (f : L₁ → L₂) (hf : Function.Bijective f)
    (cs : List (Finset V))
    (hne : cs ≠ [])
    (hchain : List.IsChain A.Adjacent cs)
    (hall : ∀ C ∈ cs, A.IsMaximal C)
    (hagree_head : lab₂ (cs.head hne) = (lab₁ (cs.head hne)).image f) :
    ∀ D ∈ cs, lab₂ D = (lab₁ D).image f := by
  induction cs with
  | nil => exact absurd rfl hne
  | cons C rest ih =>
    simp only [List.head_cons] at hagree_head
    intro D hD
    simp only [List.mem_cons] at hD
    cases hD with
    | inl h => rw [h]; exact hagree_head
    | inr h =>
      cases rest with
      | nil => simp at h
      | cons C' rest' =>
        have hne' : C' :: rest' ≠ [] := List.cons_ne_nil _ _
        have hchain' : List.IsChain A.Adjacent (C' :: rest') :=
          List.IsChain.tail hchain
        have hall' : ∀ E ∈ C' :: rest', A.IsMaximal E :=
          fun E hE => hall E (List.mem_cons_of_mem _ hE)
        have hadj_CC' : A.Adjacent C C' := by
          exact List.IsChain.rel_head hchain
        have hagree_C' : lab₂ C' = (lab₁ C').image f :=
          coxeter_adj_label_step A B_idx M cc hcc_eq φ hinj hsurj hadj_φ
            L₁ L₂ lab₁ lab₂ hmono₁ hmono₂ f hf C C' hadj_CC' hagree_head
        exact ih hne' hchain' hall' hagree_C' D h

/-- The Coxeter complex satisfies the unique-labelling property: any two
labellings agreeing on a single chamber agree everywhere. -/
theorem coxeter_complex_unique_labelling_axiom
    (A : SimplicialComplex V)
    (B_idx : Type) (M : CoxeterMatrix B_idx)
    (cc : ChamberComplex V) (hcc_eq : cc.toSimplicialComplex = A)
    (φ : Finset V → M.Group)
    (hinj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hsurj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hadj : ∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C')) :
    ∀ (L₁ L₂ : Type) [DecidableEq L₁] [DecidableEq L₂],
    ∀ (lab₁ : Finset V → Finset L₁) (lab₂ : Finset V → Finset L₂),
    (∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab₁ s ⊂ lab₁ t) →
    (∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab₂ s ⊂ lab₂ t) →
    ∀ C₀, A.IsMaximal C₀ →
    (∃ (f : L₁ → L₂), Function.Bijective f ∧
      lab₂ C₀ = (lab₁ C₀).image f) ∧
    (∀ (f : L₁ → L₂), Function.Bijective f →
      lab₂ C₀ = (lab₁ C₀).image f →
      ∀ s, s ∈ A.faces → lab₂ s = (lab₁ s).image f) := by
  intro L₁ L₂ _ _ lab₁ lab₂ hmono₁ hmono₂ C₀ hC₀
  constructor
  ·
    exact coxeter_label_bijection_exists A B_idx M cc hcc_eq φ hinj hsurj hadj
      L₁ L₂ lab₁ lab₂ hmono₁ hmono₂ C₀ hC₀
  ·
    intro f hf hfC₀ s hs

    have hs_cc : s ∈ cc.toSimplicialComplex.faces := hcc_eq ▸ hs
    obtain ⟨C, hC_max, hsC⟩ := cc.exists_maximal s hs_cc
    have hC_max_A : A.IsMaximal C := hcc_eq ▸ hC_max

    have hC₀_max_cc : cc.toSimplicialComplex.IsMaximal C₀ := hcc_eq ▸ hC₀
    obtain ⟨g, hg_start, hg_end⟩ := cc.gallery_connected C₀ C hC₀_max_cc hC_max

    have hall : ∀ D ∈ g.chambers, A.IsMaximal D := by
      intro D hD
      rw [← hcc_eq]
      exact g.all_maximal D hD
    have hne : g.chambers ≠ [] := by
      intro h
      have := g.length_pos
      simp [h] at this
    have hagree_head : lab₂ (g.chambers.head hne) = (lab₁ (g.chambers.head hne)).image f := by
      have : g.chambers.head? = some C₀ := hg_start
      have h_eq : g.chambers.head hne = C₀ := by
        rw [List.head?_eq_some_head hne] at this
        exact Option.some_injective _ this
      rw [h_eq]
      exact hfC₀
    have hchain : List.IsChain A.Adjacent g.chambers := by
      rw [← hcc_eq]
      exact g.adjacent_consecutive
    have hagree_all := coxeter_label_agree_along_chain A B_idx M cc hcc_eq φ hinj hsurj hadj
      L₁ L₂ lab₁ lab₂ hmono₁ hmono₂ f hf g.chambers hne hchain hall hagree_head

    have hC_in : C ∈ g.chambers := by
      have : g.chambers.getLast? = some C := hg_end
      exact List.mem_of_getLast? this
    have hagree_C : lab₂ C = (lab₁ C).image f := hagree_all C hC_in

    exact coxeter_subface_label_step A B_idx M cc hcc_eq φ hinj hsurj hadj
      L₁ L₂ lab₁ lab₂ hmono₁ hmono₂ f hf C hC_max_A hagree_C s hs hsC
