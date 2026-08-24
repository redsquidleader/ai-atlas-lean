/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Infinity.AffineFunc
import Atlas.Buildings.code.Building.Infinity.ChamberSectorConfig

set_option linter.unusedSectionVars false

open ChamberComplex

variable {V : Type} [DecidableEq V]

/-- A gallery is *minimal* between $C$ and $D$ if it connects them with length
equal to the gallery distance. -/
def Gallery.IsMinimal {K : SimplicialComplex V} (g : Gallery K) (C D : Finset V) : Prop :=
  g.Connects C D ∧ g.length = galleryDist K C D

namespace AffineBuilding

/-- Crossing a wall $\eta$ from a chamber $D_0$ in $\eta^+$ to a chamber $D'$ in
$\eta^-$ across a face $F$ increases the gallery distance to $C_{\text{meet}}$
by exactly one. -/
theorem coxeter_wall_crossing_gallery_dist
    {V : Type} [DecidableEq V]
    {b : Building V} (_si : SectorInfrastructure b)
    (A' : SimplicialComplex V)
    (_hA' : A' ∈ b.apartmentSystem.apartments)

    (eta : Wall b) (_heta_apt : eta.apartment = A')

    (C_meet : Finset V) (_hC_meet_face : C_meet ∈ A'.faces)
    (_hC_meet_max : A'.IsMaximal C_meet)
    (_hC_meet_pos : ∀ v ∈ C_meet, v ∈ eta.halfPos)

    (D₀ : Finset V) (_hD₀_face : D₀ ∈ A'.faces) (_hD₀_max : A'.IsMaximal D₀)
    (_hD₀_pos : ∃ v ∈ D₀, v ∈ eta.halfPos)

    (D' : Finset V) (_hD'_face : D' ∈ A'.faces) (_hD'_max : A'.IsMaximal D')
    (_hD'_neg : ∃ v ∈ D', v ∈ eta.halfNeg)

    (F : Finset V) (_hF_face : F ∈ A'.faces)
    (_hF_sub_D₀ : F ⊆ D₀) (_hF_sub_D' : F ⊆ D') :
    galleryDist A' C_meet D' = galleryDist A' C_meet D₀ + 1 := by sorry

/-- Replacement principle: any chamber $D$ adjacent to $D_0$ across the same face
$F$ inherits the same gallery distance relation to $C_{\text{meet}}$ as $D'$. -/
theorem reduced_type_gallery_replacement
    {V : Type} [DecidableEq V]
    {b : Building V} (_si : SectorInfrastructure b)
    (A' : SimplicialComplex V)
    (_hA' : A' ∈ b.apartmentSystem.apartments)

    (C_meet : Finset V) (_hC_meet_face : C_meet ∈ A'.faces)
    (_hC_meet_max : A'.IsMaximal C_meet)

    (D₀ : Finset V) (_hD₀_face : D₀ ∈ A'.faces) (_hD₀_max : A'.IsMaximal D₀)

    (D : Finset V) (_hD_face : D ∈ A'.faces) (_hD_max : A'.IsMaximal D)

    (F : Finset V) (_hF_face : F ∈ A'.faces)
    (_hF_sub_D₀ : F ⊆ D₀) (_hF_sub_D : F ⊆ D)

    (D' : Finset V) (_hD'_face : D' ∈ A'.faces) (_hD'_max : A'.IsMaximal D')
    (_hF_sub_D' : F ⊆ D')

    (_h_dist_D' : galleryDist A' C_meet D' = galleryDist A' C_meet D₀ + 1) :
    galleryDist A' C_meet D = galleryDist A' C_meet D₀ + 1 := by sorry

/-- Combination of `coxeter_wall_crossing_gallery_dist` and `reduced_type_gallery_replacement`:
both $D$ and $D'$ are at distance $\text{dist}(C_{\text{meet}}, D_0) + 1$. -/
theorem gallery_dist_wall_extension
    {V : Type} [DecidableEq V]
    {b : Building V} (_si : SectorInfrastructure b)
    (A' : SimplicialComplex V)
    (_hA' : A' ∈ b.apartmentSystem.apartments)

    (eta : Wall b) (_heta_apt : eta.apartment = A')

    (C_meet : Finset V) (_hC_meet_face : C_meet ∈ A'.faces)
    (_hC_meet_max : A'.IsMaximal C_meet)
    (_hC_meet_pos : ∀ v ∈ C_meet, v ∈ eta.halfPos)

    (D₀ : Finset V) (_hD₀_face : D₀ ∈ A'.faces) (_hD₀_max : A'.IsMaximal D₀)
    (_hD₀_pos : ∃ v ∈ D₀, v ∈ eta.halfPos)

    (D : Finset V) (_hD_face : D ∈ A'.faces) (_hD_max : A'.IsMaximal D)

    (F : Finset V) (_hF_face : F ∈ A'.faces)
    (_hF_sub_D₀ : F ⊆ D₀) (_hF_sub_D : F ⊆ D)

    (D' : Finset V) (_hD'_face : D' ∈ A'.faces) (_hD'_max : A'.IsMaximal D')
    (_hD'_neg : ∃ v ∈ D', v ∈ eta.halfNeg)

    (_hF_sub_D' : F ⊆ D') :

    galleryDist A' C_meet D = galleryDist A' C_meet D₀ + 1 ∧
    galleryDist A' C_meet D' = galleryDist A' C_meet D₀ + 1 := by

  have h_D' : galleryDist A' C_meet D' = galleryDist A' C_meet D₀ + 1 :=
    coxeter_wall_crossing_gallery_dist _si A' _hA' eta _heta_apt
      C_meet _hC_meet_face _hC_meet_max _hC_meet_pos
      D₀ _hD₀_face _hD₀_max _hD₀_pos
      D' _hD'_face _hD'_max _hD'_neg
      F _hF_face _hF_sub_D₀ _hF_sub_D'

  have h_D : galleryDist A' C_meet D = galleryDist A' C_meet D₀ + 1 :=
    reduced_type_gallery_replacement _si A' _hA'
      C_meet _hC_meet_face _hC_meet_max
      D₀ _hD₀_face _hD₀_max
      D _hD_face _hD_max
      F _hF_face _hF_sub_D₀ _hF_sub_D
      D' _hD'_face _hD'_max _hF_sub_D'
      h_D'
  exact ⟨h_D, h_D'⟩

/-- A simplicial map $A' → A$ between apartments that fixes the intersection pointwise
acts as the identity on every simplex of $A'$ — basically `AptIsoFixesIntersection`. -/
theorem intersection_fixing_map_is_identity
    {V : Type} [DecidableEq V]
    (b : Building V)
    (A A' : SimplicialComplex V)
    (hA : A ∈ b.apartmentSystem.apartments)
    (hA' : A' ∈ b.apartmentSystem.apartments)
    (ρ : SimplicialMap A' A)
    (hρ_fix : ∀ v, (∃ s ∈ A'.faces, v ∈ s) →
      (∃ t ∈ A.faces, v ∈ t) → ρ.toFun v = v)
    (s : Finset V) (hs : s ∈ A'.faces) :
    Finset.image ρ.toFun s = s := by sorry

/-- Gallery distance is invariant under apartments with the same face set. -/
theorem galleryDist_of_faces_eq
    {V : Type} [DecidableEq V]
    (A A' : SimplicialComplex V)
    (h_sub : A'.faces ⊆ A.faces)
    (h_sup : A.faces ⊆ A'.faces)
    (X Y : Finset V) :
    galleryDist A X Y = galleryDist A' X Y := by sorry

/-- The retraction of an apartment $A'$ onto a sector's apartment along $S$
preserves the gallery distance between two chambers $X, Y$ of $A'$. -/
theorem sector_retraction_preserves_gallery_dist
    {V : Type} [DecidableEq V]
    {b : Building V} (_si : SectorInfrastructure b)
    (S : Sector b)
    (A' : SimplicialComplex V)
    (_hA' : A' ∈ b.apartmentSystem.apartments)
    (ρ : SimplicialMap A' S.apartment)
    (_hρ_fix : ∀ v, (∃ s ∈ A'.faces, v ∈ s) →
      (∃ t ∈ S.apartment.faces, v ∈ t) → ρ.toFun v = v)
    (X Y : Finset V)
    (_hX_face : X ∈ A'.faces) (_hX_max : A'.IsMaximal X)
    (_hY_face : Y ∈ A'.faces) (_hY_max : A'.IsMaximal Y) :
    galleryDist S.apartment (Finset.image ρ.toFun X) (Finset.image ρ.toFun Y) =
    galleryDist A' X Y := by

  have hρX : Finset.image ρ.toFun X = X :=
    intersection_fixing_map_is_identity b S.apartment A' S.apartment_mem _hA' ρ _hρ_fix X _hX_face
  have hρY : Finset.image ρ.toFun Y = Y :=
    intersection_fixing_map_is_identity b S.apartment A' S.apartment_mem _hA' ρ _hρ_fix Y _hY_face
  rw [hρX, hρY]

  have hX_in_A : X ∈ S.apartment.faces := by
    rw [← hρX]; exact ρ.map_face X _hX_face

  have hX_bmax : b.toChamberComplex.toSimplicialComplex.IsMaximal X :=
    b.apartmentSystem.maximal_in_apt_is_maximal A' _hA' X _hX_max


  have h_sub : A'.faces ⊆ S.apartment.faces :=
    apt_faces_subset b S.apartment A' S.apartment_mem _hA' X hX_in_A _hX_face hX_bmax
  have h_sup : S.apartment.faces ⊆ A'.faces :=
    apt_faces_subset b A' S.apartment _hA' S.apartment_mem X _hX_face hX_in_A hX_bmax

  exact galleryDist_of_faces_eq S.apartment A' h_sub h_sup X Y

/-- The sector retraction is *non-stuttering*: chambers $D, D'$ on opposite sides of
the wall $\eta$ are mapped to distinct chambers from $D_0$. -/
theorem gallery_retraction_nonstuttering
    {V : Type} [DecidableEq V]
    {b : Building V} (_si : SectorInfrastructure b)
    (S : Sector b)

    (A' : SimplicialComplex V)
    (_hA' : A' ∈ b.apartmentSystem.apartments)

    (ρ : SimplicialMap A' S.apartment)
    (_hρ_fix : ∀ v, (∃ s ∈ A'.faces, v ∈ s) →
      (∃ t ∈ S.apartment.faces, v ∈ t) → ρ.toFun v = v)

    (eta : Wall b) (_heta_apt : eta.apartment = A')

    (C_meet : Finset V) (_hC_meet_face : C_meet ∈ A'.faces)
    (_hC_meet_max : A'.IsMaximal C_meet)
    (_hC_meet_pos : ∀ v ∈ C_meet, v ∈ eta.halfPos)

    (D₀ : Finset V) (_hD₀_face : D₀ ∈ A'.faces) (_hD₀_max : A'.IsMaximal D₀)
    (_hD₀_pos : ∃ v ∈ D₀, v ∈ eta.halfPos)

    (D : Finset V) (_hD_face : D ∈ A'.faces) (_hD_max : A'.IsMaximal D)

    (F : Finset V) (_hF_face : F ∈ A'.faces)
    (_hF_sub_D₀ : F ⊆ D₀) (_hF_sub_D : F ⊆ D)

    (D' : Finset V) (_hD'_face : D' ∈ A'.faces) (_hD'_max : A'.IsMaximal D')
    (_hD'_neg : ∃ v ∈ D', v ∈ eta.halfNeg)

    (_hF_sub_D' : F ⊆ D') :

    Finset.image ρ.toFun D ≠ Finset.image ρ.toFun D₀ ∧
    Finset.image ρ.toFun D' ≠ Finset.image ρ.toFun D₀ := by

  have h_wall := gallery_dist_wall_extension _si A' _hA' eta _heta_apt
    C_meet _hC_meet_face _hC_meet_max _hC_meet_pos
    D₀ _hD₀_face _hD₀_max _hD₀_pos
    D _hD_face _hD_max
    F _hF_face _hF_sub_D₀ _hF_sub_D
    D' _hD'_face _hD'_max _hD'_neg _hF_sub_D'
  obtain ⟨h_dist_D, h_dist_D'⟩ := h_wall

  have h_ρ_D := sector_retraction_preserves_gallery_dist _si S A' _hA' ρ _hρ_fix
    C_meet D _hC_meet_face _hC_meet_max _hD_face _hD_max
  have h_ρ_D₀ := sector_retraction_preserves_gallery_dist _si S A' _hA' ρ _hρ_fix
    C_meet D₀ _hC_meet_face _hC_meet_max _hD₀_face _hD₀_max
  have h_ρ_D' := sector_retraction_preserves_gallery_dist _si S A' _hA' ρ _hρ_fix
    C_meet D' _hC_meet_face _hC_meet_max _hD'_face _hD'_max

  constructor
  ·
    intro h_eq

    rw [h_eq] at h_ρ_D


    omega
  ·
    intro h_eq
    rw [h_eq] at h_ρ_D'
    omega

/-- Simplicial maps between apartments preserve maximal faces (chambers). -/
theorem simplicial_map_apt_preserves_maximal
    {V : Type} [DecidableEq V]
    {b : Building V}
    (A' : SimplicialComplex V)
    (_hA' : A' ∈ b.apartmentSystem.apartments)
    (A : SimplicialComplex V)
    (_hA : A ∈ b.apartmentSystem.apartments)
    (ρ : SimplicialMap A' A)
    (C : Finset V) (_hC : C ∈ A'.faces) (_hC_max : A'.IsMaximal C) :
    A.IsMaximal (Finset.image ρ.toFun C) := by


  let 𝒜 := b.apartmentSystem
  let bldgSC := b.toChamberComplex.toSimplicialComplex

  let φ : Finset V → Finset V := fun s => s.image ρ.toFun

  let S₁ : Set (Finset V) := {C}

  have hφ_into_A : ∀ C₁ ∈ S₁, φ C₁ ∈ A.faces := by
    intro C₁ hC₁
    have h := Set.eq_of_mem_singleton hC₁
    rw [h]
    exact ρ.map_face C _hC


  have hφ_dist : ∀ C₁ ∈ S₁, ∀ D ∈ S₁,
      galleryDist bldgSC (φ C₁) (φ D) = galleryDist bldgSC C₁ D := by
    intro C₁ hC₁ D hD
    rw [Set.eq_of_mem_singleton hC₁, Set.eq_of_mem_singleton hD]
    simp [galleryDist_self]

  exact (galleryDist_preserving_maps_to_maximal 𝒜 A _hA S₁ φ hφ_into_A hφ_dist C
    (Set.mem_singleton C)).1

/-- Under a simplicial map between apartments, chambers map to chambers and faces
to faces — a packaged convenience lemma. -/
theorem retraction_image_properties
    {V : Type} [DecidableEq V]
    {b : Building V}
    (A' : SimplicialComplex V)
    (_hA' : A' ∈ b.apartmentSystem.apartments)
    (A : SimplicialComplex V)
    (_hA : A ∈ b.apartmentSystem.apartments)
    (ρ : SimplicialMap A' A)

    (D₀ : Finset V) (_hD₀ : D₀ ∈ A'.faces) (_hD₀_max : A'.IsMaximal D₀)
    (D : Finset V) (_hD : D ∈ A'.faces) (_hD_max : A'.IsMaximal D)
    (D' : Finset V) (_hD' : D' ∈ A'.faces) (_hD'_max : A'.IsMaximal D')

    (F : Finset V) (_hF : F ∈ A'.faces)
    (_hF_sub_D₀ : F ⊆ D₀) (_hF_sub_D : F ⊆ D) (_hF_sub_D' : F ⊆ D') :

    A.IsMaximal (Finset.image ρ.toFun D₀) ∧
    A.IsMaximal (Finset.image ρ.toFun D) ∧
    A.IsMaximal (Finset.image ρ.toFun D') ∧
    Finset.image ρ.toFun F ∈ A.faces := by
  exact ⟨simplicial_map_apt_preserves_maximal A' _hA' A _hA ρ D₀ _hD₀ _hD₀_max,
         simplicial_map_apt_preserves_maximal A' _hA' A _hA ρ D _hD _hD_max,
         simplicial_map_apt_preserves_maximal A' _hA' A _hA ρ D' _hD' _hD'_max,
         ρ.map_face F _hF⟩

end AffineBuilding
