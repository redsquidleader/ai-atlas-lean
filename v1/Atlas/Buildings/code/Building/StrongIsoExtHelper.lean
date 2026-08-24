/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Basic
import Mathlib.GroupTheory.Coxeter.Length

set_option maxHeartbeats 400000

/-- Panel generator: in a Coxeter complex, every chamber $C$ has a chamber
$D$ adjacent across the $i$-th panel with $\varphi(D) = \varphi(C) \cdot s_i$. -/
theorem coxeter_panel_generator
    {V : Type*} [DecidableEq V]
    (A : SimplicialComplex V)
    {B_idx : Type} (M : CoxeterMatrix B_idx)
    (φ : Finset V → M.Group)
    (hφ_inj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hφ_surj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hφ_adj : ∀ C C', A.Adjacent C C' →
      CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (C : Finset V) (hC : A.IsMaximal C)
    (i : B_idx) :
    ∃ D, A.Adjacent C D ∧ φ D = φ C * M.toCoxeterSystem.simple i := by sorry

/-- Backward direction: if $\varphi(C), \varphi(D)$ are chamber-adjacent in the
Coxeter group and $C \neq D$, then $C, D$ are adjacent in the apartment. -/
theorem coxeter_complex_backward_adj
    {V : Type*} [DecidableEq V]
    (A : SimplicialComplex V)
    {B_idx : Type} (M : CoxeterMatrix B_idx)
    (φ : Finset V → M.Group)
    (hφ_inj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hφ_surj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hφ_adj : ∀ C C', A.Adjacent C C' →
      CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (C D : Finset V) (hC : A.IsMaximal C) (hD : A.IsMaximal D)
    (hne : C ≠ D)
    (h_cadj : CoxeterComplex.ChamberAdjacent M (φ C) (φ D)) :
    A.Adjacent C D := by

  obtain ⟨_, i, hφD⟩ := h_cadj


  obtain ⟨D', hD'_adj, hφD'⟩ := coxeter_panel_generator A M φ hφ_inj hφ_surj hφ_adj C hC i

  have hD'_max : A.IsMaximal D' := hD'_adj.2.1
  have hφ_eq : φ D = φ D' := by rw [hφD, hφD']
  have hDD' : D = D' := hφ_inj D hD D' hD'_max hφ_eq

  rw [hDD']
  exact hD'_adj

/-- Coxeter chamber-adjacency lifts to apartment adjacency (the $C \neq D$
side condition is automatic from the Coxeter adjacency). -/
theorem coxeter_adj_backward_in_apt
    {V : Type*} [DecidableEq V]
    (A : SimplicialComplex V)
    {B_idx : Type} (M : CoxeterMatrix B_idx)
    (φ : Finset V → M.Group)
    (hφ_inj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hφ_surj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hφ_adj : ∀ C C', A.Adjacent C C' →
      CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (C D : Finset V)
    (hC : A.IsMaximal C) (hD : A.IsMaximal D)
    (h_cadj : CoxeterComplex.ChamberAdjacent M (φ C) (φ D)) :
    A.Adjacent C D := by

  have hne : C ≠ D := fun h => h_cadj.1 (congrArg φ h)
  exact coxeter_complex_backward_adj A M φ hφ_inj hφ_surj hφ_adj C D hC hD hne h_cadj

/-- The chamber-level retraction $\bar\rho$ is induced by a vertex map
$\sigma : V \to V$ sending facets to facets. -/
theorem retraction_has_vertex_map
    {V : Type*} [DecidableEq V]
    {b : Building V}
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (ρbar : Finset V → Finset V)
    (hρbar_max : ∀ D, A.IsMaximal (ρbar D)) :
    ∃ σ : V → V,
      (∀ C, b.toChamberComplex.toSimplicialComplex.IsMaximal C →
        C.image σ = ρbar C) ∧
      (∀ F C, b.toChamberComplex.toSimplicialComplex.IsFacet F C →
        A.IsFacet (F.image σ) (ρbar C)) := by sorry

/-- For adjacent chambers $D_1, D_2$ with $\bar\rho(D_1) \neq \bar\rho(D_2)$,
the images share a common facet in the apartment $A$. -/
theorem retraction_facet_shared_or_collapsed
    {V : Type*} [DecidableEq V]
    {b : Building V}
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (ρbar : Finset V → Finset V)
    (hρbar_max : ∀ D, A.IsMaximal (ρbar D))
    (D₁ D₂ : Finset V)
    (h_adj : b.toChamberComplex.toSimplicialComplex.Adjacent D₁ D₂)
    (h_ne : ρbar D₁ ≠ ρbar D₂) :
    ∃ F, A.IsFacet F (ρbar D₁) ∧ A.IsFacet F (ρbar D₂) := by

  obtain ⟨σ, hσ_chamber, hσ_facet⟩ := retraction_has_vertex_map A hA ρbar hρbar_max

  obtain ⟨_, _, _, F₀, hF₀_D₁, hF₀_D₂⟩ := h_adj

  have hF_D₁ := hσ_facet F₀ D₁ hF₀_D₁

  have hF_D₂ := hσ_facet F₀ D₂ hF₀_D₂

  exact ⟨F₀.image σ, hF_D₁, hF_D₂⟩

/-- Under the retraction $\bar\rho$, adjacent chambers either collapse to the
same image or remain adjacent in the apartment. -/
theorem retraction_adj_or_eq_apt
    {V : Type*} [DecidableEq V]
    {b : Building V}
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (ρbar : Finset V → Finset V)
    (hρbar_max : ∀ D, A.IsMaximal (ρbar D))
    (D₁ D₂ : Finset V)
    (h_adj : b.toChamberComplex.toSimplicialComplex.Adjacent D₁ D₂) :
    ρbar D₁ = ρbar D₂ ∨ A.Adjacent (ρbar D₁) (ρbar D₂) := by
  by_cases h_eq : ρbar D₁ = ρbar D₂
  · exact Or.inl h_eq
  · right
    obtain ⟨F, hF₁, hF₂⟩ := retraction_facet_shared_or_collapsed A hA ρbar hρbar_max D₁ D₂ h_adj h_eq
    exact ⟨hρbar_max D₁, hρbar_max D₂, h_eq, F, hF₁, hF₂⟩

/-- At the level of the Coxeter labeling $\varphi$, the images of adjacent
chambers under $\bar\rho$ are either equal or chamber-adjacent. -/
theorem retraction_delta_adj_or_eq
    {V : Type*} [DecidableEq V]
    {b : Building V}
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (ρbar : Finset V → Finset V)
    (hρbar_max : ∀ D, A.IsMaximal (ρbar D))
    {B_idx : Type} {M : CoxeterMatrix B_idx}
    (φ : Finset V → M.Group)
    (hφ_inj : ∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D)
    (hφ_surj : ∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w)
    (hφ_adj : ∀ C C', A.Adjacent C C' →
      CoxeterComplex.ChamberAdjacent M (φ C) (φ C'))
    (D₁ D₂ : Finset V)
    (h_adj : b.toChamberComplex.toSimplicialComplex.Adjacent D₁ D₂) :
    φ (ρbar D₁) = φ (ρbar D₂) ∨
      CoxeterComplex.ChamberAdjacent M (φ (ρbar D₁)) (φ (ρbar D₂)) := by


  rcases retraction_adj_or_eq_apt A hA ρbar hρbar_max D₁ D₂ h_adj with h_eq | h_adj_apt
  ·
    left
    rw [h_eq]
  ·

    right
    exact hφ_adj (ρbar D₁) (ρbar D₂) h_adj_apt

/-- The retraction $\bar\rho$ preserves adjacency: images of adjacent chambers
are either equal or adjacent in $A$. -/
theorem retraction_adj_preserves
    {V : Type*} [DecidableEq V]
    {b : Building V}
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (ρbar : Finset V → Finset V)
    (hρbar_max : ∀ D, A.IsMaximal (ρbar D))
    (D₁ D₂ : Finset V)
    (h_adj : b.toChamberComplex.toSimplicialComplex.Adjacent D₁ D₂) :
    ρbar D₁ = ρbar D₂ ∨ A.Adjacent (ρbar D₁) (ρbar D₂) := by

  obtain ⟨B_idx, M, cc, hcc_eq, φ, hφ_inj, hφ_surj, hφ_adj, _hThin⟩ :=
    b.apartmentSystem.apt_is_coxeter A hA


  have h_cox := retraction_delta_adj_or_eq A hA ρbar hρbar_max φ hφ_inj hφ_surj
    hφ_adj D₁ D₂ h_adj
  rcases h_cox with h_eq | h_cadj
  ·
    left
    exact hφ_inj (ρbar D₁) (hρbar_max D₁) (ρbar D₂) (hρbar_max D₂) h_eq
  ·
    right
    exact coxeter_adj_backward_in_apt A M φ hφ_inj hφ_surj hφ_adj
      (ρbar D₁) (ρbar D₂) (hρbar_max D₁) (hρbar_max D₂) h_cadj

/-- Existence of a canonical retraction $\rho$ that lands in $A$ and
preserves the $\delta$-distance from $C$. -/
theorem canonical_retraction_delta_preserving
    {V : Type*} [DecidableEq V]
    {b : Building V}
    {W : Type*} [Group W]
    (delta : Finset V → Finset V → W)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC : A.IsMaximal C) :
    ∃ (ρ : Finset V → Finset V),
      (∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D →
        ρ D ∈ A.faces ∧ A.IsMaximal (ρ D)) ∧
      (∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D →
        delta C (ρ D) = delta C D) := by sorry

/-- Uniqueness of retractions: a $\delta$-preserving retraction $\rho$ must
agree on $Y$ with any other $\delta$-preserving partial map $f$. -/
theorem label_uniqueness_retraction_agreement
    {V : Type*} [DecidableEq V]
    {b : Building V}
    {W : Type*} [Group W]
    (delta : Finset V → Finset V → W)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC : A.IsMaximal C)
    (ρ : Finset V → Finset V)
    (hρ_max : ∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D →
      ρ D ∈ A.faces ∧ A.IsMaximal (ρ D))
    (hρ_delta : ∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D →
      delta C (ρ D) = delta C D)
    (Y : Set (Finset V)) (f : Finset V → Finset V)
    (hY : ∀ y ∈ Y, b.toChamberComplex.toSimplicialComplex.IsMaximal y)
    (hf_img : ∀ y ∈ Y, f y ∈ A.faces)
    (hf_delta : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, delta (f y₁) (f y₂) = delta y₁ y₂) :
    ∀ y ∈ Y, ρ y = f y := by sorry

/-- Combined statement: there exists a canonical retraction $\bar\rho$ that
agrees with any $\delta$-preserving partial map $f$ on its domain $Y$. -/
theorem retraction_label_agreement
    {V : Type*} [DecidableEq V]
    {b : Building V}
    {W : Type*} [Group W]
    (delta : Finset V → Finset V → W)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC : A.IsMaximal C)
    (Y : Set (Finset V)) (f : Finset V → Finset V)
    (hY : ∀ y ∈ Y, b.toChamberComplex.toSimplicialComplex.IsMaximal y)
    (hf_img : ∀ y ∈ Y, f y ∈ A.faces)
    (hf_delta : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, delta (f y₁) (f y₂) = delta y₁ y₂) :
    ∃ (ρbar : Finset V → Finset V),
      (∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D →
        ρbar D ∈ A.faces ∧ A.IsMaximal (ρbar D)) ∧
      (∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D →
        delta C (ρbar D) = delta C D) ∧
      (∀ y ∈ Y, ρbar y = f y) := by

  obtain ⟨ρ, hρ_max, hρ_delta⟩ :=
    canonical_retraction_delta_preserving delta A hA C hC

  have h_agree : ∀ y ∈ Y, ρ y = f y :=
    label_uniqueness_retraction_agreement delta A hA C hC ρ hρ_max hρ_delta
      Y f hY hf_img hf_delta

  exact ⟨ρ, hρ_max, hρ_delta, h_agree⟩

/-- Compatibility of a $\delta$-preserving map $f$ with the center chamber
$C$: $f$ preserves $\delta(C, -)$ on $Y$, and its image is maximal in $A$. -/
theorem delta_preserving_map_center_compat
    {V : Type*} [DecidableEq V]
    {b : Building V}
    {W : Type*} [Group W]
    (delta : Finset V → Finset V → W)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC : A.IsMaximal C)
    (Y : Set (Finset V)) (f : Finset V → Finset V)
    (hY : ∀ y ∈ Y, b.toChamberComplex.toSimplicialComplex.IsMaximal y)
    (hf_img : ∀ y ∈ Y, f y ∈ A.faces)
    (hf_delta : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, delta (f y₁) (f y₂) = delta y₁ y₂) :
    (∀ y ∈ Y, delta C (f y) = delta C y) ∧ (∀ y ∈ Y, A.IsMaximal (f y)) := by


  obtain ⟨ρbar, hρ_max, hρ_delta, h_agree⟩ :=
    retraction_label_agreement delta A hA C hC Y f hY hf_img hf_delta
  constructor
  ·

    intro y hy
    rw [← h_agree y hy]
    exact hρ_delta y (hY y hy)
  ·

    intro y hy
    rw [← h_agree y hy]
    exact (hρ_max y (hY y hy)).2

/-- Injectivity of $\delta$ in an apartment: assuming a Coxeter compatibility,
$\delta(C, D_1) = \delta(C, D_2)$ forces $D_1 = D_2$. -/
theorem delta_injective_in_apt_generic
    {V : Type*} [DecidableEq V]
    {b : Building V}
    {W : Type*} [Group W]
    (delta : Finset V → Finset V → W)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (C D₁ D₂ : Finset V)
    (hC : A.IsMaximal C)
    (hD₁_mem : D₁ ∈ A.faces) (hD₁ : A.IsMaximal D₁)
    (hD₂_mem : D₂ ∈ A.faces) (hD₂ : A.IsMaximal D₂)
    (h_delta_compat : ∃ (B_idx : Type) (M : CoxeterMatrix B_idx)
      (φ : Finset V → M.Group),
      (∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D) ∧
      ∃ (iso : W ≃* M.Group),
        ∀ C D, C ∈ A.faces → A.IsMaximal C → D ∈ A.faces → A.IsMaximal D →
          iso (delta C D) = (φ C)⁻¹ * (φ D))
    (h_eq : delta C D₁ = delta C D₂) :
    D₁ = D₂ := by

  obtain ⟨B_idx, M, φ, hφ_inj, iso, h_compat⟩ := h_delta_compat

  have h1 : iso (delta C D₁) = iso (delta C D₂) := by rw [h_eq]

  rw [h_compat C D₁ hC.1 hC hD₁_mem hD₁,
      h_compat C D₂ hC.1 hC hD₂_mem hD₂] at h1


  have h2 : φ D₁ = φ D₂ := mul_left_cancel h1

  exact hφ_inj D₁ hD₁ D₂ hD₂ h2

/-- Any $\delta$-preserving retraction $\bar\rho$ which fixes the apartment
agrees on $Y$ with any other $\delta$-preserving partial map $f$. -/
theorem retraction_agrees_with_delta_preserving
    {V : Type*} [DecidableEq V]
    {b : Building V}
    {W : Type*} [Group W]
    (delta : Finset V → Finset V → W)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC : A.IsMaximal C)
    (ρbar : Finset V → Finset V)
    (hρ_max : ∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D →
      ρbar D ∈ A.faces ∧ A.IsMaximal (ρbar D))
    (hρ_fix : ∀ D, D ∈ A.faces → A.IsMaximal D → ρbar D = D)
    (hρ_delta : ∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D →
      delta C (ρbar D) = delta C D)
    (Y : Set (Finset V)) (f : Finset V → Finset V)
    (hY : ∀ y ∈ Y, b.toChamberComplex.toSimplicialComplex.IsMaximal y)
    (hf_img : ∀ y ∈ Y, f y ∈ A.faces)
    (hf_delta : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, delta (f y₁) (f y₂) = delta y₁ y₂)
    (h_delta_compat : ∃ (B_idx : Type) (M : CoxeterMatrix B_idx)
      (φ : Finset V → M.Group),
      (∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D) ∧
      ∃ (iso : W ≃* M.Group),
        ∀ C D, C ∈ A.faces → A.IsMaximal C → D ∈ A.faces → A.IsMaximal D →
          iso (delta C D) = (φ C)⁻¹ * (φ D)) :
    ∀ y ∈ Y, ρbar y = f y := by


  obtain ⟨hf_center, hf_max⟩ :=
    delta_preserving_map_center_compat delta A hA C hC Y f hY hf_img hf_delta

  intro y hy

  have hρy := hρ_max y (hY y hy)
  have hfy_mem := hf_img y hy
  have hfy_max := hf_max y hy

  have hρ_eq := hρ_delta y (hY y hy)

  have hf_eq := hf_center y hy

  have h_delta_eq : delta C (ρbar y) = delta C (f y) := by
    rw [hρ_eq, hf_eq]

  exact delta_injective_in_apt_generic delta A hA C (ρbar y) (f y) hC
    hρy.1 hρy.2 hfy_mem hfy_max h_delta_compat h_delta_eq
