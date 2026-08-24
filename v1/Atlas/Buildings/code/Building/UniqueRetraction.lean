/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.RetractionDef
import Atlas.Buildings.code.Building.RetractionProperties
import Atlas.Buildings.code.Building.Labels
import Atlas.Buildings.code.Building.VertexActionHelper

set_option maxHeartbeats 0

open scoped Classical

set_option maxHeartbeats 0


variable {V : Type} [DecidableEq V]

/-- Strict inclusion is preserved by the image of an injective function on
finite sets. -/
lemma finset_image_ssubset_of_injective {f : V → V} (hf : Function.Injective f)
    {s t : Finset V} (h : s ⊂ t) : s.image f ⊂ t.image f := by
  constructor
  · exact Finset.image_subset_image h.1
  · intro heq
    apply h.2
    intro x hx
    have : f x ∈ s.image f := by
      apply heq
      exact Finset.mem_image_of_mem f hx
    rw [Finset.mem_image] at this
    obtain ⟨y, hy, hfy⟩ := this
    have := hf hfy; subst this; exact hy

/-- For any pair of chambers $C, D$ of an apartment $A$, there exists a
bijective vertex map (apartment automorphism) sending $C$ to $D$. -/
theorem apt_automorphism_sending_chamber
    (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC : A.IsMaximal C)
    (D : Finset V) (hD : A.IsMaximal D) :
    ∃ (φ : V → V), Function.Bijective φ ∧
      (∀ s, s ∈ A.faces ↔ s.image φ ∈ A.faces) ∧
      D.image φ = C := by

  obtain ⟨B_idx, M, cc, hcc, φ, hinj, hsurj, hadj, hThin⟩ :=
    b.apartmentSystem.apt_is_coxeter A hA

  have hCox : ∃ (B_idx : Type) (M : CoxeterMatrix B_idx) (φ : Finset V → M.Group),
      (∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D) ∧
      (∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w) ∧
      (∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C')) :=
    ⟨B_idx, M, φ, hinj, hsurj, hadj⟩

  have hWR : ∀ C D : Finset V, A.Adjacent C D →
      ∃ wr : ChamberComplex.WallReflection cc, D.image wr.refl = C :=
    coxeter_apt_wall_reflections cc A hcc hThin hCox

  exact ChamberComplex.apt_vertex_level_automorphism A cc hcc hWR C D hC hD

/-- A bijective vertex map between apartments that preserves the face
structure is label-preserving. -/
theorem apt_bij_iso_label_preserving
    {V : Type} [DecidableEq V]
    (b : Building V)
    (A A' : SimplicialComplex V)
    (hA : A ∈ b.apartmentSystem.apartments)
    (hA' : A' ∈ b.apartmentSystem.apartments)
    (φ : V → V) (hφ_bij : Function.Bijective φ)
    (hφ_faces : ∀ s, s ∈ A.faces ↔ s.image φ ∈ A'.faces)
    (L : Type) [DecidableEq L]
    (lab : Labelling b.toChamberComplex.toSimplicialComplex L)
    (s : Finset V) (hs : s ∈ A.faces) :
    lab.labelMap (s.image φ) = lab.labelMap s := by sorry

/-- A bijective face-preserving map between apartments sends maximal faces
to maximal faces. -/
lemma bijective_face_iso_preserves_maximal
    {A A' : SimplicialComplex V} {φ : V → V} (hφ_bij : Function.Bijective φ)
    (hφ_faces : ∀ s, s ∈ A.faces ↔ s.image φ ∈ A'.faces)
    {s : Finset V} (hs : A.IsMaximal s) : A'.IsMaximal (s.image φ) := by
  constructor
  · exact (hφ_faces s).mp hs.1
  · intro t ht hsub


    set t₀ := t.preimage φ (hφ_bij.1.injOn) with ht₀_def
    have mem_t₀ : ∀ x, x ∈ t₀ ↔ φ x ∈ t := fun x => Finset.mem_preimage

    have ht₀_img : t₀.image φ = t := by
      ext z; constructor
      · rw [Finset.mem_image]; rintro ⟨w, hw, rfl⟩; exact (mem_t₀ w).mp hw
      · intro hz
        obtain ⟨w, rfl⟩ := hφ_bij.2 z
        exact Finset.mem_image_of_mem φ ((mem_t₀ w).mpr hz)

    have ht₀_face : t₀ ∈ A.faces := by
      rw [← ht₀_img] at ht; exact (hφ_faces t₀).mpr ht

    have hs_sub_t₀ : s ⊆ t₀ := by
      intro x hx; exact (mem_t₀ x).mpr (hsub (Finset.mem_image_of_mem φ hx))

    have hs_eq : s = t₀ := hs.2 t₀ ht₀_face hs_sub_t₀

    rw [← ht₀_img, ← hs_eq]

/-- For apartments $A, A'$ both containing a chamber $C$, there is an
isomorphism $A \to A'$ that sends $C$ to itself (and is label-preserving). -/
theorem apartment_iso_sending_chamber
    (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (B : SimplicialComplex V) (hB : B ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC_A : C ∈ A.faces)
    (hC_max_bldg : b.toChamberComplex.toSimplicialComplex.IsMaximal C)
    (D : Finset V) (hD_B : D ∈ B.faces)
    (hD_max_bldg : b.toChamberComplex.toSimplicialComplex.IsMaximal D) :
    ∃ (φ : V → V), Function.Bijective φ ∧
      (∀ s, s ∈ B.faces ↔ s.image φ ∈ A.faces) ∧
      D.image φ = C := by

  obtain ⟨A₀, hA₀, hC_A₀, hD_A₀⟩ :=
    b.apartmentSystem.contains_pair C D hC_max_bldg hD_max_bldg

  have hD_max_B : B.IsMaximal D :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal B hB D hD_B hD_max_bldg
  have hD_max_A₀ : A₀.IsMaximal D :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal A₀ hA₀ D hD_A₀ hD_max_bldg
  have hC_max_A₀ : A₀.IsMaximal C :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal A₀ hA₀ C hC_A₀ hC_max_bldg
  have hC_max_A : A.IsMaximal C :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal A hA C hC_A hC_max_bldg

  obtain ⟨φ₁, hφ₁_bij, hφ₁_faces⟩ :=
    b.apartmentSystem.iso_bijective B hB A₀ hA₀ D hD_B hD_A₀ hD_max_B

  obtain ⟨φ₂, hφ₂_bij, hφ₂_faces⟩ :=
    b.apartmentSystem.iso_bijective A₀ hA₀ A hA C hC_A₀ hC_A hC_max_A₀

  set φ₀ := φ₂ ∘ φ₁
  have hφ₀_bij : Function.Bijective φ₀ := hφ₂_bij.comp hφ₁_bij
  have hφ₀_faces : ∀ s, s ∈ B.faces ↔ s.image φ₀ ∈ A.faces := by
    intro s
    simp only [φ₀, ← Finset.image_image]
    exact Iff.trans (hφ₁_faces s) (hφ₂_faces (s.image φ₁))

  set E := D.image φ₀ with hE_def
  have hE_A : E ∈ A.faces := (hφ₀_faces D).mp hD_B

  have hD_img_max_A₀ : A₀.IsMaximal (D.image φ₁) :=
    bijective_face_iso_preserves_maximal hφ₁_bij hφ₁_faces hD_max_B
  have hE_max_A : A.IsMaximal E := by
    rw [hE_def, show D.image φ₀ = (D.image φ₁).image φ₂ from by simp [φ₀, Finset.image_image]]
    exact bijective_face_iso_preserves_maximal hφ₂_bij hφ₂_faces hD_img_max_A₀

  obtain ⟨α, hα_bij, hα_faces, hα_EC⟩ :=
    apt_automorphism_sending_chamber b A hA C hC_max_A E hE_max_A

  refine ⟨α ∘ φ₀, hα_bij.comp hφ₀_bij, ?_, ?_⟩
  ·
    intro s
    simp only [← Finset.image_image]
    exact Iff.trans (hφ₀_faces s) (hα_faces (s.image φ₀))
  ·
    simp only [← Finset.image_image]
    exact hα_EC

/-- A bijective apartment iso that fixes a chamber pointwise is the identity
on the apartment. -/
lemma bij_iso_fixing_chamber_is_id
    (b : Building V)
    (B B' : SimplicialComplex V) (hB : B ∈ b.apartmentSystem.apartments)
    (D : Finset V) (hD_B : D ∈ B.faces)
    (hD_max : b.toChamberComplex.toSimplicialComplex.IsMaximal D)
    (φ : V → V) (hφ_bij : Function.Bijective φ)
    (_hφ_faces : ∀ s, s ∈ B.faces ↔ s.image φ ∈ B'.faces)
    (hφ_D : D.image φ = D) :
    ∀ s ∈ B.faces, s.image φ = s := by
  have hD_max_B : B.IsMaximal D :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal B hB D hD_B hD_max
  have hmono_id : ∀ s t, s ∈ B.faces → t ∈ B.faces → s ⊂ t → s ⊂ t := by
    intro s t _ _ h; exact h
  have hmono_φ : ∀ s t, s ∈ B.faces → t ∈ B.faces → s ⊂ t →
      s.image φ ⊂ t.image φ := by
    intro s t _ _ hst
    exact finset_image_ssubset_of_injective hφ_bij.1 hst
  obtain ⟨_, hprop⟩ := b.apartmentSystem.apt_unique_labelling B hB
    V V id (fun s => s.image φ) hmono_id hmono_φ D hD_max_B
  have h_agree_D : D.image φ = (id D).image (id : V → V) := by
    simp [hφ_D]
  intro s hs
  have := hprop id Function.bijective_id h_agree_D s hs

  simp at this
  exact this

/-- Any apartment isomorphism fixing a chamber is automatically bijective. -/
theorem iso_bijective_fixing_chamber
    (b : Building V)
    (B : SimplicialComplex V) (hB : B ∈ b.apartmentSystem.apartments)
    (B₀ : SimplicialComplex V) (hB₀ : B₀ ∈ b.apartmentSystem.apartments)
    (D : Finset V) (hD_B : D ∈ B.faces) (hD_B₀ : D ∈ B₀.faces)
    (hD_max_B : B.IsMaximal D) :
    ∃ (φ : V → V), Function.Bijective φ ∧
      (∀ s, s ∈ B.faces ↔ s.image φ ∈ B₀.faces) ∧
      D.image φ = D := by

  obtain ⟨ψ, hψ_bij, hψ_faces⟩ :=
    b.apartmentSystem.iso_bijective B hB B₀ hB₀ D hD_B hD_B₀ hD_max_B

  have hDψ_max_B₀ : B₀.IsMaximal (D.image ψ) :=
    bijective_face_iso_preserves_maximal hψ_bij hψ_faces hD_max_B

  have hD_max_B₀ : B₀.IsMaximal D :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal B₀ hB₀ D hD_B₀
      (b.apartmentSystem.maximal_in_apt_is_maximal B hB D hD_max_B)

  obtain ⟨α, hα_bij, hα_faces, hα_send⟩ :=
    apt_automorphism_sending_chamber b B₀ hB₀ D hD_max_B₀ (D.image ψ) hDψ_max_B₀

  refine ⟨α ∘ ψ, hα_bij.comp hψ_bij, ?_, ?_⟩
  ·
    intro s
    simp only [← Finset.image_image]
    exact Iff.trans (hψ_faces s) (hα_faces (s.image ψ))
  ·
    simp only [← Finset.image_image]
    exact hα_send

/-- Existence of the canonical retraction $\rho_{D;C,A} : X \to A$ centered
at a chamber $C$ of an apartment $A$: a vertex-level retraction fixing $A$
pointwise and sending chambers to chambers. -/
theorem exists_canonical_retraction
    (b : Building V)
    (B₀ : SimplicialComplex V) (hB₀ : B₀ ∈ b.apartmentSystem.apartments)
    (D : Finset V) (hD_B₀ : D ∈ B₀.faces)
    (hD_max : b.toChamberComplex.toSimplicialComplex.IsMaximal D) :
    ∃ (ρ : V → V),

      (∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces, s.image ρ ∈ B₀.faces) ∧

      (∀ v, (∃ s ∈ B₀.faces, v ∈ s) → ρ v = v) ∧

      (D.image ρ = D) ∧

      (∀ B ∈ b.apartmentSystem.apartments, D ∈ B.faces →
        Function.Injective (fun v : V => ρ v) ∧
        (∀ s, s ∈ B.faces ↔ s.image ρ ∈ B₀.faces)) ∧

      (∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces, s.image ρ = s) := by


  have apt_faces_sub : ∀ (B : SimplicialComplex V), B ∈ b.apartmentSystem.apartments →
      D ∈ B.faces → B.faces ⊆ B₀.faces := by
    intro B hB hD_B s hs
    have hD_max_B : B.IsMaximal D :=
      b.apartmentSystem.building_maximal_in_apt_is_apt_maximal B hB D hD_B hD_max
    obtain ⟨φ, hφ_bij, hφ_faces, hφ_D⟩ :=
      iso_bijective_fixing_chamber b B hB B₀ hB₀ D hD_B hD_B₀ hD_max_B
    have hid := bij_iso_fixing_chamber_is_id b B B₀ hB D hD_B hD_max φ hφ_bij hφ_faces hφ_D s hs
    rw [← hid]
    exact (hφ_faces s).mp hs

  have apt_faces_sup : ∀ (B : SimplicialComplex V), B ∈ b.apartmentSystem.apartments →
      D ∈ B.faces → B₀.faces ⊆ B.faces := by
    intro B hB hD_B s hs
    have hD_max_B₀ : B₀.IsMaximal D :=
      b.apartmentSystem.building_maximal_in_apt_is_apt_maximal B₀ hB₀ D hD_B₀ hD_max
    obtain ⟨ψ, hψ_bij, hψ_faces, hψ_D⟩ :=
      iso_bijective_fixing_chamber b B₀ hB₀ B hB D hD_B₀ hD_B hD_max_B₀
    have hid := bij_iso_fixing_chamber_is_id b B₀ B hB₀ D hD_B₀ hD_max ψ hψ_bij hψ_faces hψ_D s hs
    rw [← hid]
    exact (hψ_faces s).mp hs


  have all_faces_in_B₀ : ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces,
      s ∈ B₀.faces := by
    intro s hs

    obtain ⟨E, hE_max, hs_sub⟩ := b.toChamberComplex.exists_maximal s hs

    obtain ⟨B, hB, hD_B, hE_B⟩ := b.apartmentSystem.contains_pair D E hD_max hE_max

    have hs_B : s ∈ B.faces :=
      B.down_closed hE_B hs_sub (b.toChamberComplex.toSimplicialComplex.nonempty_of_mem s hs)
    exact apt_faces_sub B hB hD_B hs_B

  refine ⟨id, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro s hs
    simp
    exact all_faces_in_B₀ s hs
  ·
    intro v _
    rfl
  ·
    simp
  ·
    intro B hB hD_B
    constructor
    ·
      exact Function.injective_id
    ·
      intro s
      simp
      exact ⟨fun h => apt_faces_sub B hB hD_B h, fun h => apt_faces_sup B hB hD_B h⟩
  ·
    intro s _
    simp

/-- Uniqueness of the retraction $\rho_{D;C,A}$: any two retractions onto
$A$ centered at $C$ with the same chamber-level behaviour agree (Section
15.5). -/
theorem unique_retraction_D_to_C
    (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC_A : C ∈ A.faces) (hC_max : b.toChamberComplex.toSimplicialComplex.IsMaximal C)
    (D : Finset V) (hD_max : b.toChamberComplex.toSimplicialComplex.IsMaximal D) :

    (∃ (ρ : V → V),

      (∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces, s.image ρ ∈ A.faces) ∧

      (∀ (L : Type) [DecidableEq L]
        (lab : Labelling b.toChamberComplex.toSimplicialComplex L),
        ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces,
          lab.labelMap (s.image ρ) = lab.labelMap s) ∧

      (D.image ρ = C) ∧

      (∀ B ∈ b.apartmentSystem.apartments, D ∈ B.faces →
        Function.Injective (fun v : V => ρ v) ∧
        (∀ s, s ∈ B.faces ↔ s.image ρ ∈ A.faces))) ∧

    (∀ (ρ₁ ρ₂ : V → V),
      (∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces, s.image ρ₁ ∈ A.faces) →
      (∀ (L : Type) [DecidableEq L]
        (lab : Labelling b.toChamberComplex.toSimplicialComplex L),
        ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces,
          lab.labelMap (s.image ρ₁) = lab.labelMap s) →
      (D.image ρ₁ = C) →
      (∀ B ∈ b.apartmentSystem.apartments, D ∈ B.faces →
        Function.Injective (fun v : V => ρ₁ v) ∧
        (∀ s, s ∈ B.faces ↔ s.image ρ₁ ∈ A.faces)) →
      (∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces, s.image ρ₂ ∈ A.faces) →
      (∀ (L : Type) [DecidableEq L]
        (lab : Labelling b.toChamberComplex.toSimplicialComplex L),
        ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces,
          lab.labelMap (s.image ρ₂) = lab.labelMap s) →
      (D.image ρ₂ = C) →
      (∀ B ∈ b.apartmentSystem.apartments, D ∈ B.faces →
        Function.Injective (fun v : V => ρ₂ v) ∧
        (∀ s, s ∈ B.faces ↔ s.image ρ₂ ∈ A.faces)) →
      ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces, s.image ρ₁ = s.image ρ₂) := by
  constructor
  ·

    obtain ⟨B₀, hB₀, hC_B₀, hD_B₀⟩ := b.apartmentSystem.contains_pair C D hC_max hD_max

    obtain ⟨ρ_ret, hρ_simp, hρ_fix, hρ_D, hρ_iso, hρ_id⟩ :=
      exists_canonical_retraction b B₀ hB₀ D hD_B₀ hD_max


    obtain ⟨j, hj_bij, hj_faces, hj_DC⟩ :=
      apartment_iso_sending_chamber b A hA B₀ hB₀ C hC_A hC_max D hD_B₀ hD_max

    refine ⟨j ∘ ρ_ret, ?_, ?_, ?_, ?_⟩
    ·
      intro s hs
      have h1 : s.image ρ_ret ∈ B₀.faces := hρ_simp s hs
      rw [← Finset.image_image]
      exact (hj_faces (s.image ρ_ret)).mp h1
    ·


      intro L _ lab s hs
      have hρ_s : s.image ρ_ret = s := hρ_id s hs
      rw [← Finset.image_image, hρ_s]
      have hs_B₀ : s ∈ B₀.faces := hρ_s ▸ (hρ_simp s hs)
      exact apt_bij_iso_label_preserving b B₀ A hB₀ hA j hj_bij hj_faces L lab s hs_B₀

    ·
      rw [← Finset.image_image]
      rw [hρ_D, hj_DC]
    ·
      intro B hB hD_B
      obtain ⟨hρ_inj_B, hρ_faces_B⟩ := hρ_iso B hB hD_B
      constructor
      ·
        exact Function.Injective.comp hj_bij.1 hρ_inj_B
      ·
        intro s
        constructor
        · intro hs_B
          rw [← Finset.image_image]
          exact (hj_faces (s.image ρ_ret)).mp ((hρ_faces_B s).mp hs_B)
        · intro hs_A
          rw [← Finset.image_image] at hs_A
          exact (hρ_faces_B s).mpr ((hj_faces (s.image ρ_ret)).mpr hs_A)
  ·
    intro ρ₁ ρ₂ hρ₁_simp _hρ₁_lp hρ₁_DC hρ₁_iso hρ₂_simp _hρ₂_lp hρ₂_DC hρ₂_iso s hs

    obtain ⟨E, hE_max, hs_sub⟩ := b.toChamberComplex.exists_maximal s hs

    obtain ⟨B, hB, hD_B, hE_B⟩ := b.apartmentSystem.contains_pair D E hD_max hE_max

    have hs_B : s ∈ B.faces :=
      B.down_closed hE_B hs_sub (b.toChamberComplex.toSimplicialComplex.nonempty_of_mem s hs)

    obtain ⟨hρ₁_inj, hρ₁_faces⟩ := hρ₁_iso B hB hD_B
    obtain ⟨hρ₂_inj, hρ₂_faces⟩ := hρ₂_iso B hB hD_B

    have hD_max_B : B.IsMaximal D :=
      b.apartmentSystem.building_maximal_in_apt_is_apt_maximal B hB D hD_B hD_max


    have hmono₁ : ∀ s' t', s' ∈ B.faces → t' ∈ B.faces → s' ⊂ t' →
        (s'.image ρ₁) ⊂ (t'.image ρ₁) := by
      intro s' t' _ _ hst
      exact finset_image_ssubset_of_injective hρ₁_inj hst
    have hmono₂ : ∀ s' t', s' ∈ B.faces → t' ∈ B.faces → s' ⊂ t' →
        (s'.image ρ₂) ⊂ (t'.image ρ₂) := by
      intro s' t' _ _ hst
      exact finset_image_ssubset_of_injective hρ₂_inj hst


    obtain ⟨_, hprop⟩ := b.apartmentSystem.apt_unique_labelling B hB
      V V (fun s' => s'.image ρ₁) (fun s' => s'.image ρ₂) hmono₁ hmono₂ D hD_max_B

    have hid_bij : Function.Bijective (id : V → V) := Function.bijective_id

    have hagree_D : D.image ρ₂ = (D.image ρ₁).image id := by
      rw [Finset.image_id, hρ₁_DC, hρ₂_DC]

    have result := hprop id hid_bij hagree_D s hs_B

    rw [Finset.image_id] at result
    exact result.symm
