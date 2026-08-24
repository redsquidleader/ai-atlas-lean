/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.AptFoldingFromRetraction
import Atlas.Buildings.code.Building.UniqueRetraction

open scoped Classical
open AptFoldingFromRetraction

variable {V : Type} [DecidableEq V]

/-- The canonical retraction map $\rho : V \to V$ obtained from `exists_canonical_retraction`. -/
noncomputable def retraction_map
    (b : Building V)
    (A : SimplicialComplex V)
    (hA : A ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC_A : C ∈ A.faces) (hC_max : A.IsMaximal C) : V → V :=
  Classical.choose (exists_canonical_retraction b A hA C hC_max)

/-- The retraction map sends faces of the building to faces of the chosen apartment $A$. -/
theorem retraction_map_face
    (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC_A : C ∈ A.faces) (hC_max : A.IsMaximal C) :
    ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces,
      s.image (retraction_map b A hA C hC_A hC_max) ∈ A.faces :=
  (Classical.choose_spec (exists_canonical_retraction b A hA C hC_max)).1

/-- The retraction map fixes every vertex lying in the apartment $A$. -/
theorem retraction_map_fixes_apt
    (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC_A : C ∈ A.faces) (hC_max : A.IsMaximal C) :
    ∀ v, (∃ s ∈ A.faces, v ∈ s) → retraction_map b A hA C hC_A hC_max v = v :=
  (Classical.choose_spec (exists_canonical_retraction b A hA C hC_max)).2.1

/-- The retraction map is injective on the vertices of any apartment $B$ containing $C$. -/
theorem retraction_map_injective_on_apt
    (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC_A : C ∈ A.faces) (hC_max : A.IsMaximal C) :
    ∀ (B : SimplicialComplex V), B ∈ b.apartmentSystem.apartments →
      C ∈ B.faces →
      ∀ v₁ v₂, (∃ s ∈ B.faces, v₁ ∈ s) → (∃ s ∈ B.faces, v₂ ∈ s) →
        retraction_map b A hA C hC_A hC_max v₁ = retraction_map b A hA C hC_A hC_max v₂ →
        v₁ = v₂ :=
  (Classical.choose_spec (exists_canonical_retraction b A hA C hC_max)).2.2.2.2

/-- The retraction restricted to a second apartment $A'$ sends faces of $A'$ into faces of $A$. -/
theorem retraction_restricts_to_simplicial_map_A'_to_A
    {V : Type} [DecidableEq V]
    (b : Building V)
    (A A' : SimplicialComplex V)
    (hA : A ∈ b.apartmentSystem.apartments)
    (hA' : A' ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC_A : C ∈ A.faces) (hC_A' : C ∈ A'.faces)
    (hC_max : A.IsMaximal C) :
    ∀ s ∈ A'.faces, s.image (retraction_map b A hA C hC_A hC_max) ∈ A.faces := by
  intro s hs
  have hsub : IsSubcomplex A' b.toChamberComplex.toSimplicialComplex :=
    b.apartmentSystem.sub A' hA'
  exact retraction_map_face b A hA C hC_A hC_max s (hsub hs)

/-- Specialization of injectivity of the retraction to vertices of another apartment $A'$. -/
lemma retraction_injective_on_apt_vertices
    {V : Type} [DecidableEq V]
    (b : Building V)
    (A A' : SimplicialComplex V)
    (hA : A ∈ b.apartmentSystem.apartments)
    (hA' : A' ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC_A : C ∈ A.faces) (hC_A' : C ∈ A'.faces)
    (hC_max : A.IsMaximal C) :
    ∀ v₁ v₂, (∃ s ∈ A'.faces, v₁ ∈ s) → (∃ s ∈ A'.faces, v₂ ∈ s) →
      retraction_map b A hA C hC_A hC_max v₁ = retraction_map b A hA C hC_A hC_max v₂ →
      v₁ = v₂ :=
  retraction_map_injective_on_apt b A hA C hC_A hC_max A' hA' hC_A'

/-- Strict monotonicity of the retraction-induced image map on faces of $A'$. -/
lemma retraction_image_ssubset_of_ssubset
    {V : Type} [DecidableEq V]
    (b : Building V)
    (A A' : SimplicialComplex V)
    (hA : A ∈ b.apartmentSystem.apartments)
    (hA' : A' ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC_A : C ∈ A.faces) (hC_A' : C ∈ A'.faces)
    (hC_max : A.IsMaximal C)
    (s t : Finset V) (hs : s ∈ A'.faces) (ht : t ∈ A'.faces) (hst : s ⊂ t) :
    s.image (retraction_map b A hA C hC_A hC_max) ⊂
      t.image (retraction_map b A hA C hC_A hC_max) := by
  let ρ := retraction_map b A hA C hC_A hC_max
  have hinj : ∀ v₁ v₂, (∃ s ∈ A'.faces, v₁ ∈ s) → (∃ s ∈ A'.faces, v₂ ∈ s) →
      ρ v₁ = ρ v₂ → v₁ = v₂ :=
    retraction_injective_on_apt_vertices b A A' hA hA' C hC_A hC_A' hC_max
  constructor
  · exact Finset.image_subset_image hst.1
  · intro heq
    apply hst.2


    intro x hxt

    have hρx_t : ρ x ∈ t.image ρ := Finset.mem_image_of_mem ρ hxt

    have h_eq : t.image ρ ⊆ s.image ρ := heq

    have hρx_s : ρ x ∈ s.image ρ := h_eq hρx_t
    rw [Finset.mem_image] at hρx_s
    obtain ⟨y, hy_s, hρeq⟩ := hρx_s

    have hxy : x = y :=
      hinj x y ⟨t, ht, hxt⟩ ⟨s, hs, hy_s⟩ hρeq.symm
    rw [hxy]; exact hy_s

/-- The retraction $\rho$ centered at a chamber $C$ acts as the identity on every face of any
apartment $A'$ also containing $C$ — a consequence of label-uniqueness. -/
theorem retraction_identity_on_apt
    {V : Type} [DecidableEq V]
    (b : Building V)
    (A A' : SimplicialComplex V)
    (hA : A ∈ b.apartmentSystem.apartments)
    (hA' : A' ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC_A : C ∈ A.faces) (hC_A' : C ∈ A'.faces)
    (hC_max_bldg : b.toChamberComplex.toSimplicialComplex.IsMaximal C) :
    ∀ s ∈ A'.faces, s.image (retraction_map b A hA C hC_A
      (b.apartmentSystem.building_maximal_in_apt_is_apt_maximal A hA C hC_A hC_max_bldg)) = s := by
  let hC_max : A.IsMaximal C :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal A hA C hC_A hC_max_bldg
  let hC_max' : A'.IsMaximal C :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal A' hA' C hC_A' hC_max_bldg
  let ρ := retraction_map b A hA C hC_A hC_max


  have hmono1 : ∀ s t, s ∈ A'.faces → t ∈ A'.faces → s ⊂ t →
      (s : Finset V) ⊂ (t : Finset V) := by
    intro s t _ _ hst; exact hst
  have hmono2 : ∀ s t, s ∈ A'.faces → t ∈ A'.faces → s ⊂ t →
      s.image ρ ⊂ t.image ρ := by
    intro s t hs ht hst
    exact retraction_image_ssubset_of_ssubset b A A' hA hA' C hC_A hC_A' hC_max s t hs ht hst

  have uniq := b.apartmentSystem.apt_unique_labelling A' hA' V V
    (fun s => s) (fun s => s.image ρ) hmono1 hmono2 C hC_max'

  have hC_fix : C.image ρ = C := by
    ext v; simp only [Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have : ρ w = w := retraction_map_fixes_apt b A hA C hC_A hC_max w ⟨C, hC_A, hw⟩
      rw [this]; exact hw
    · intro hv; exact ⟨v, hv, retraction_map_fixes_apt b A hA C hC_A hC_max v ⟨C, hC_A, hv⟩⟩
  have h_agree : C.image ρ = C.image id := by simp [hC_fix]
  have h_bij_id : Function.Bijective (id : V → V) := Function.bijective_id
  have h_part2 := uniq.2 id h_bij_id h_agree

  intro s hs
  have := h_part2 s hs
  simp at this
  exact this

/-- Apartments containing a common chamber $C$ have one face-set contained in the other; in
particular this yields $A'.\mathrm{faces} \subseteq A.\mathrm{faces}$. -/
theorem apt_faces_subset
    {V : Type} [DecidableEq V]
    (b : Building V)
    (A A' : SimplicialComplex V)
    (hA : A ∈ b.apartmentSystem.apartments)
    (hA' : A' ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC_A : C ∈ A.faces) (hC_A' : C ∈ A'.faces)
    (hC_max_bldg : b.toChamberComplex.toSimplicialComplex.IsMaximal C) :
    A'.faces ⊆ A.faces := by
  intro s hs
  let hC_max : A.IsMaximal C :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal A hA C hC_A hC_max_bldg
  have h := retraction_identity_on_apt b A A' hA hA' C hC_A hC_A' hC_max_bldg s hs
  rw [← h]
  exact retraction_restricts_to_simplicial_map_A'_to_A b A A' hA hA' C hC_A hC_A' hC_max s hs

/-- Section 4.1 / 4.4: between two apartments $A, A'$ sharing a chamber $C$ there exists a
simplicial isomorphism $\varphi : V \to V$ that is bijective and fixes the intersection
$A \cap A'$ pointwise. -/
theorem apt_iso_exists_fixing_intersection
    {V : Type} [DecidableEq V]
    (b : Building V)
    (A A' : SimplicialComplex V)
    (hA : A ∈ b.apartmentSystem.apartments)
    (hA' : A' ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC_A : C ∈ A.faces) (hC_A' : C ∈ A'.faces)
    (hC_max : b.toChamberComplex.toSimplicialComplex.IsMaximal C) :
    ∃ (φ : V → V),
      (∀ s, s ∈ A.faces ↔ s.image φ ∈ A'.faces) ∧
      (∀ v, (∃ s ∈ A.faces, v ∈ s) → (∃ s ∈ A'.faces, v ∈ s) → φ v = v) ∧
      Function.Bijective φ := by

  have h_sub : A'.faces ⊆ A.faces := apt_faces_subset b A A' hA hA' C hC_A hC_A' hC_max
  have h_sub' : A.faces ⊆ A'.faces := apt_faces_subset b A' A hA' hA C hC_A' hC_A hC_max

  refine ⟨id, ?_, ?_, Function.bijective_id⟩
  · intro s; simp; exact ⟨fun hs => h_sub' hs, fun hs => h_sub hs⟩
  · intro v _ _; simp
