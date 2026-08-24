/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Basic

open scoped Classical

variable {V : Type*} [DecidableEq V]

/-- A labelling of a simplicial complex $K$ by a set $L$: a strict-monotone assignment of a finite,
nonempty set of labels to each face, monotone with respect to face inclusion. -/
structure Labelling (K : SimplicialComplex V) (L : Type*) [DecidableEq L] where
  labelMap : Finset V → Finset L
  label_nonempty : ∀ s ∈ K.faces, (labelMap s).Nonempty
  label_strictMono : ∀ s t, s ∈ K.faces → t ∈ K.faces →
    s ⊂ t → labelMap s ⊂ labelMap t

/-- A simplicial complex $K$ is *labellable* if there exists a labelling by some label type. -/
def SimplicialComplex.IsLabellable (K : SimplicialComplex V) : Prop :=
  ∃ (L : Type*) (_ : DecidableEq L), Nonempty (Labelling K L)

/-- Application of a labelling to a face: returns the label set assigned to $s$. -/
def Labelling.labelOf {K : SimplicialComplex V} {L : Type*} [DecidableEq L]
    (lab : Labelling K L) (s : Finset V) : Finset L :=
  lab.labelMap s

/-- Two chambers $C_1, C_2$ are $\ell$-*adjacent* (with respect to a labelling) if they are
adjacent and the label of their common face $C_1 \cap C_2$ equals $\ell$. -/
def LabelAdjacent {L : Type*} [DecidableEq L]
    (K : ChamberComplex V) (lab : Labelling K.toSimplicialComplex L)
    (ℓ : Finset L) (C₁ C₂ : Finset V) : Prop :=
  K.toSimplicialComplex.Adjacent C₁ C₂ ∧
    lab.labelMap (C₁ ∩ C₂) = ℓ

/-- A chamber complex is *uniquely labellable* if any two labellings differ by a bijection of label
sets, i.e. all labellings are canonical up to renaming of labels. -/
def ChamberComplex.IsUniquelyLabellable (K : ChamberComplex V) : Prop :=
  ∀ (L₁ L₂ : Type) [DecidableEq L₁] [DecidableEq L₂]
    (lab₁ : Labelling K.toSimplicialComplex L₁)
    (lab₂ : Labelling K.toSimplicialComplex L₂),
    ∃ f : L₁ → L₂, Function.Bijective f ∧
      ∀ s ∈ K.toSimplicialComplex.faces,
        lab₂.labelMap s = (lab₁.labelMap s).image f

/-- The *link* of a face $\sigma$ in $K$: the set of nonempty faces $\tau$ disjoint from $\sigma$
such that $\sigma \cup \tau$ is still a face of $K$. -/
def SimplicialComplex.link (K : SimplicialComplex V) (σ : Finset V)
    (_hσ : σ ∈ K.faces) : Set (Finset V) :=
  { τ : Finset V | τ.Nonempty ∧ Disjoint σ τ ∧ (σ ∪ τ) ∈ K.faces }

/-- If `l.getLast? = some a`, then $a$ is a member of $l$. -/
lemma mem_of_getLast?_eq {α : Type*} {l : List α} {a : α}
    (h : l.getLast? = some a) : a ∈ l := by
  cases l with
  | nil => simp at h
  | cons x xs =>
    rw [List.getLast?_cons] at h
    have heq : a = Option.getD xs.getLast? x := (Option.some_injective _ h).symm
    rw [heq]
    cases xs with
    | nil => simp [List.getLast?]
    | cons y ys =>
      simp only [List.getLast?, Option.getD]
      exact List.mem_cons_of_mem x (List.getLast_mem _)

/-- Label agreement propagates along a chain of adjacent chambers: if two labellings $\mathrm{lab}_1$
and $\mathrm{lab}_2$ are related by a function $f$ on the head of a chain and the relation passes
through adjacency, then the relation holds along the whole chain. -/
lemma label_agree_along_chain
    {K : SimplicialComplex V}
    {L₁ L₂ : Type*} [DecidableEq L₁] [DecidableEq L₂]
    (lab₁ : Labelling K L₁) (lab₂ : Labelling K L₂)
    (f : L₁ → L₂)
    (hadj_prop : ∀ C₁ C₂ : Finset V, K.Adjacent C₁ C₂ →
      lab₂.labelMap C₁ = (lab₁.labelMap C₁).image f →
      lab₂.labelMap C₂ = (lab₁.labelMap C₂).image f)
    (cs : List (Finset V))
    (hne : cs ≠ [])
    (hchain : List.IsChain K.Adjacent cs)
    (hagree : lab₂.labelMap (cs.head hne) = (lab₁.labelMap (cs.head hne)).image f) :
    ∀ D ∈ cs, lab₂.labelMap D = (lab₁.labelMap D).image f := by
  induction cs with
  | nil => exact absurd rfl hne
  | cons a tl ih =>
    intro D hD
    rw [List.mem_cons] at hD
    rcases hD with rfl | hD
    · exact hagree
    · cases tl with
      | nil => simp at hD
      | cons b' rest =>
        rw [List.isChain_cons] at hchain
        obtain ⟨hrel, hchain_tl⟩ := hchain
        have hab : K.Adjacent a b' := hrel b' rfl
        have hagree_b : lab₂.labelMap b' = (lab₁.labelMap b').image f :=
          hadj_prop a b' hab hagree
        exact ih (List.cons_ne_nil b' rest) hchain_tl hagree_b D hD

/-- Label agreement at one chamber propagates to all chambers via the gallery-connectedness of a
chamber complex. -/
lemma label_agree_all_chambers
    {K : ChamberComplex V}
    {L₁ L₂ : Type*} [DecidableEq L₁] [DecidableEq L₂]
    (lab₁ : Labelling K.toSimplicialComplex L₁)
    (lab₂ : Labelling K.toSimplicialComplex L₂)
    (f : L₁ → L₂)
    (hadj_prop : ∀ C₁ C₂ : Finset V,
      K.toSimplicialComplex.Adjacent C₁ C₂ →
      lab₂.labelMap C₁ = (lab₁.labelMap C₁).image f →
      lab₂.labelMap C₂ = (lab₁.labelMap C₂).image f)
    (C₀ : Finset V)
    (hC₀ : K.toSimplicialComplex.IsMaximal C₀)
    (hagree₀ : lab₂.labelMap C₀ = (lab₁.labelMap C₀).image f) :
    ∀ D, K.toSimplicialComplex.IsMaximal D →
      lab₂.labelMap D = (lab₁.labelMap D).image f := by
  intro D hD
  obtain ⟨gal, hgal_head, hgal_last⟩ := K.gallery_connected C₀ D hC₀ hD
  have hne : gal.chambers ≠ [] := by
    intro h; simp [h] at hgal_head
  have hhead_eq : gal.chambers.head hne = C₀ := by
    rw [List.head?_eq_some_head hne] at hgal_head
    exact Option.some_injective _ hgal_head
  have hD_mem : D ∈ gal.chambers := mem_of_getLast?_eq hgal_last
  exact label_agree_along_chain lab₁ lab₂ f hadj_prop gal.chambers hne
    gal.adjacent_consecutive (hhead_eq ▸ hagree₀) D hD_mem

/-- Label agreement at one chamber propagates to *all faces* via gallery-connectedness on chambers
together with downward propagation from each chamber to its subfaces. -/
lemma label_agree_all_faces
    {K : ChamberComplex V}
    {L₁ L₂ : Type*} [DecidableEq L₁] [DecidableEq L₂]
    (lab₁ : Labelling K.toSimplicialComplex L₁)
    (lab₂ : Labelling K.toSimplicialComplex L₂)
    (f : L₁ → L₂)
    (hadj_prop : ∀ C₁ C₂ : Finset V,
      K.toSimplicialComplex.Adjacent C₁ C₂ →
      lab₂.labelMap C₁ = (lab₁.labelMap C₁).image f →
      lab₂.labelMap C₂ = (lab₁.labelMap C₂).image f)
    (hsub_prop : ∀ C : Finset V,
      K.toSimplicialComplex.IsMaximal C →
      lab₂.labelMap C = (lab₁.labelMap C).image f →
      ∀ s : Finset V, s ∈ K.toSimplicialComplex.faces → s ⊆ C →
      lab₂.labelMap s = (lab₁.labelMap s).image f)
    (C₀ : Finset V)
    (hC₀ : K.toSimplicialComplex.IsMaximal C₀)
    (hagree₀ : lab₂.labelMap C₀ = (lab₁.labelMap C₀).image f) :
    ∀ s ∈ K.toSimplicialComplex.faces,
      lab₂.labelMap s = (lab₁.labelMap s).image f := by
  intro s hs
  obtain ⟨C, hC_max, hsC⟩ := K.exists_maximal s hs
  have hagree_C : lab₂.labelMap C = (lab₁.labelMap C).image f :=
    label_agree_all_chambers lab₁ lab₂ f hadj_prop C₀ hC₀ hagree₀ C hC_max
  exact hsub_prop C hC_max hagree_C s hs hsC

/-- Every building has at least one chamber, extracted from a nonempty apartment. -/
lemma building_has_chamber {V : Type*} [DecidableEq V] (b : Building V) :
    ∃ C : Finset V, b.toChamberComplex.toSimplicialComplex.IsMaximal C := by
  obtain ⟨A, hA⟩ := b.apartmentSystem.nonempty_apartments
  obtain ⟨s, hs⟩ := b.apartmentSystem.apt_nonempty A hA
  have hs_bldg : s ∈ b.toChamberComplex.toSimplicialComplex.faces :=
    b.apartmentSystem.sub A hA hs
  obtain ⟨C, hC_max, _⟩ := b.toChamberComplex.exists_maximal s hs_bldg
  exact ⟨C, hC_max⟩

/-- For two labellings of a building, on any fixed chamber there exists a bijection $f$ between
the two label types translating one labelling into the other. -/
lemma building_label_translation {V : Type*} [DecidableEq V] (b : Building V)
    (L₁ : Type) (L₂ : Type) [DecidableEq L₁] [DecidableEq L₂]
    (lab₁ : Labelling b.toChamberComplex.toSimplicialComplex L₁)
    (lab₂ : Labelling b.toChamberComplex.toSimplicialComplex L₂)
    (C₀ : Finset V)
    (hC₀ : b.toChamberComplex.toSimplicialComplex.IsMaximal C₀) :
    ∃ f : L₁ → L₂, Function.Bijective f ∧
      lab₂.labelMap C₀ = (lab₁.labelMap C₀).image f := by

  obtain ⟨A, hA, hC₀A, _⟩ := b.apartmentSystem.contains_pair C₀ C₀ hC₀ hC₀

  have hC₀_apt_max : A.IsMaximal C₀ :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal A hA C₀ hC₀A hC₀


  have hmono₁ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t →
      lab₁.labelMap s ⊂ lab₁.labelMap t := by
    intro s t hs ht hst
    exact lab₁.label_strictMono s t (b.apartmentSystem.sub A hA hs)
      (b.apartmentSystem.sub A hA ht) hst
  have hmono₂ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t →
      lab₂.labelMap s ⊂ lab₂.labelMap t := by
    intro s t hs ht hst
    exact lab₂.label_strictMono s t (b.apartmentSystem.sub A hA hs)
      (b.apartmentSystem.sub A hA ht) hst

  obtain ⟨⟨f, hf_bij, hf_C₀⟩, _⟩ := b.apartmentSystem.apt_unique_labelling A hA
    L₁ L₂ lab₁.labelMap lab₂.labelMap hmono₁ hmono₂ C₀ hC₀_apt_max
  exact ⟨f, hf_bij, hf_C₀⟩

/-- Adjacency-step propagation of label agreement across a building: a bijection $f$ relating the
labels on a chamber $C_1$ extends to the labels on any adjacent chamber $C_2$. -/
lemma building_adj_label_propagation {V : Type*} [DecidableEq V] (b : Building V)
    (L₁ : Type) (L₂ : Type) [DecidableEq L₁] [DecidableEq L₂]
    (lab₁ : Labelling b.toChamberComplex.toSimplicialComplex L₁)
    (lab₂ : Labelling b.toChamberComplex.toSimplicialComplex L₂)
    (f : L₁ → L₂) (hf_bij : Function.Bijective f) (C₁ C₂ : Finset V)
    (hadj : b.toChamberComplex.toSimplicialComplex.Adjacent C₁ C₂)
    (hagree : lab₂.labelMap C₁ = (lab₁.labelMap C₁).image f) :
    lab₂.labelMap C₂ = (lab₁.labelMap C₂).image f := by

  obtain ⟨hC₁_max, hC₂_max, _, _⟩ := hadj

  obtain ⟨A, hA, hC₁A, hC₂A⟩ := b.apartmentSystem.contains_pair C₁ C₂ hC₁_max hC₂_max

  have hC₁_apt_max : A.IsMaximal C₁ :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal A hA C₁ hC₁A hC₁_max

  have hmono₁ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t →
      lab₁.labelMap s ⊂ lab₁.labelMap t := by
    intro s t hs ht hst
    exact lab₁.label_strictMono s t (b.apartmentSystem.sub A hA hs)
      (b.apartmentSystem.sub A hA ht) hst
  have hmono₂ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t →
      lab₂.labelMap s ⊂ lab₂.labelMap t := by
    intro s t hs ht hst
    exact lab₂.label_strictMono s t (b.apartmentSystem.sub A hA hs)
      (b.apartmentSystem.sub A hA ht) hst


  obtain ⟨_, hprop⟩ := b.apartmentSystem.apt_unique_labelling A hA
    L₁ L₂ lab₁.labelMap lab₂.labelMap hmono₁ hmono₂ C₁ hC₁_apt_max
  exact hprop f hf_bij hagree C₂ hC₂A

/-- Subface propagation of label agreement: if a bijection relates the labels on a chamber $C$,
then it also relates the labels on every subface $s \subseteq C$. -/
lemma building_subface_label_propagation {V : Type*} [DecidableEq V] (b : Building V)
    (L₁ : Type) (L₂ : Type) [DecidableEq L₁] [DecidableEq L₂]
    (lab₁ : Labelling b.toChamberComplex.toSimplicialComplex L₁)
    (lab₂ : Labelling b.toChamberComplex.toSimplicialComplex L₂)
    (f : L₁ → L₂) (hf_bij : Function.Bijective f) (C : Finset V)
    (hC : b.toChamberComplex.toSimplicialComplex.IsMaximal C)
    (hagree : lab₂.labelMap C = (lab₁.labelMap C).image f)
    (s : Finset V)
    (hs : s ∈ b.toChamberComplex.toSimplicialComplex.faces)
    (hsC : s ⊆ C) :
    lab₂.labelMap s = (lab₁.labelMap s).image f := by

  obtain ⟨A, hA, hCA, _⟩ := b.apartmentSystem.contains_pair C C hC hC

  have hC_apt_max : A.IsMaximal C :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal A hA C hCA hC

  have hs_ne : s.Nonempty :=
    b.toChamberComplex.toSimplicialComplex.nonempty_of_mem s hs
  have hsA : s ∈ A.faces := A.down_closed hCA hsC hs_ne

  have hmono₁ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t →
      lab₁.labelMap s ⊂ lab₁.labelMap t := by
    intro s t hs ht hst
    exact lab₁.label_strictMono s t (b.apartmentSystem.sub A hA hs)
      (b.apartmentSystem.sub A hA ht) hst
  have hmono₂ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t →
      lab₂.labelMap s ⊂ lab₂.labelMap t := by
    intro s t hs ht hst
    exact lab₂.label_strictMono s t (b.apartmentSystem.sub A hA hs)
      (b.apartmentSystem.sub A hA ht) hst

  obtain ⟨_, hprop⟩ := b.apartmentSystem.apt_unique_labelling A hA
    L₁ L₂ lab₁.labelMap lab₂.labelMap hmono₁ hmono₂ C hC_apt_max
  exact hprop f hf_bij hagree s hsA
