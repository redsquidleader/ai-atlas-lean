/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.ChamberComplex.Basic
import Atlas.Buildings.code.ChamberComplex.CoxeterComplex
import Mathlib.Order.Zorn

set_option maxHeartbeats 800000

variable {V : Type*} [DecidableEq V]

/-- A simplicial map from $K$ to $L$: a vertex function sending faces of $K$ to faces of $L$. -/
structure SimplicialMap (K L : SimplicialComplex V) where
  toFun : V → V
  map_face : ∀ s ∈ K.faces, s.image toFun ∈ L.faces

/-- `A` is a subcomplex of `K` iff every face of `A` is a face of `K`. -/
def IsSubcomplex (A K : SimplicialComplex V) : Prop :=
  A.faces ⊆ K.faces

/-- An apartment system on a chamber complex $K$: a collection of "apartments" subject to the
axioms (B1)–(B3) of buildings: every two chambers lie in a common apartment, common-chamber
apartments admit a fixing simplicial isomorphism, gallery-convexity inside apartments, plus
the Coxeter-complex structure on each apartment. -/
structure ApartmentSystem (K : ChamberComplex V) where
  apartments : Set (SimplicialComplex V)
  nonempty_apartments : ∃ A, A ∈ apartments
  sub : ∀ A ∈ apartments, IsSubcomplex A K.toSimplicialComplex
  contains_pair : ∀ C D,
    K.toSimplicialComplex.IsMaximal C →
    K.toSimplicialComplex.IsMaximal D →
    ∃ A ∈ apartments, C ∈ A.faces ∧ D ∈ A.faces
  iso_exists : ∀ A ∈ apartments, ∀ A' ∈ apartments,
    ∀ x, x ∈ A.faces → x ∈ A'.faces →
    ∀ C, A.IsMaximal C → C ∈ A'.faces →
    ∃ φ : SimplicialMap A A',
      (∀ v ∈ x, φ.toFun v = v) ∧ (∀ v ∈ C, φ.toFun v = v)
  maximal_in_apt_is_maximal :
    ∀ A ∈ apartments, ∀ C, A.IsMaximal C → K.toSimplicialComplex.IsMaximal C
  gallery_convex :
    ∀ A ∈ apartments, ∀ C D : Finset V,
      C ∈ A.faces → K.toSimplicialComplex.IsMaximal C →
      D ∈ A.faces → K.toSimplicialComplex.IsMaximal D →
      ∀ g : Gallery K.toSimplicialComplex,
        g.Connects C D →
        g.length = galleryDist K.toSimplicialComplex C D →
        ∀ E ∈ g.chambers, E ∈ A.faces
  building_maximal_in_apt_is_apt_maximal :
    ∀ A ∈ apartments, ∀ C, C ∈ A.faces →
      K.toSimplicialComplex.IsMaximal C → A.IsMaximal C
  apt_nonempty :
    ∀ A ∈ apartments, ∃ s, s ∈ A.faces
  iso_bijective : ∀ A ∈ apartments, ∀ A' ∈ apartments,
    ∀ C, C ∈ A.faces → C ∈ A'.faces → A.IsMaximal C →
    ∃ φ : V → V, Function.Bijective φ ∧
      (∀ s, s ∈ A.faces ↔ s.image φ ∈ A'.faces)
  apt_is_coxeter : ∀ A ∈ apartments,
    ∃ (B_idx : Type) (M : CoxeterMatrix B_idx) (cc : ChamberComplex V),
      cc.toSimplicialComplex = A ∧
      ∃ (φ : Finset V → M.Group),
        (∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D) ∧
        (∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w) ∧
        (∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C')) ∧
        cc.IsThin

/-- Uniqueness of label transport on an apartment: two strictly monotone labellings agree under a
unique bijection of label sets determined by their values on any maximal chamber $C_0$. -/
theorem ApartmentSystem.apt_unique_labelling
    {V : Type*} [DecidableEq V] {K : ChamberComplex V}
    (𝒜 : ApartmentSystem K)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (L₁ L₂ : Type) [DecidableEq L₁] [DecidableEq L₂]
    (lab₁ : Finset V → Finset L₁) (lab₂ : Finset V → Finset L₂)
    (hlab₁ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab₁ s ⊂ lab₁ t)
    (hlab₂ : ∀ s t, s ∈ A.faces → t ∈ A.faces → s ⊂ t → lab₂ s ⊂ lab₂ t)
    (C₀ : Finset V) (hC₀ : A.IsMaximal C₀) :

    (∃ (f : L₁ → L₂), Function.Bijective f ∧
      lab₂ C₀ = (lab₁ C₀).image f) ∧

    (∀ (f : L₁ → L₂), Function.Bijective f →
      lab₂ C₀ = (lab₁ C₀).image f →
      ∀ s, s ∈ A.faces → lab₂ s = (lab₁ s).image f) := by sorry

/-- Canonical retraction onto an apartment $B$ at a maximal chamber $C_0$: a chamber-level map
$\rho$ sending every chamber of $K$ into $B$ and acting as the identity on chambers of $B$. -/
theorem canonical_retraction_onto_apartment
    {V : Type*} [DecidableEq V] {K : ChamberComplex V}
    (𝒜 : ApartmentSystem K)
    (B : SimplicialComplex V) (hB : B ∈ 𝒜.apartments)
    (C₀ : Finset V) (hC₀_B : C₀ ∈ B.faces)
    (hC₀_max_B : B.IsMaximal C₀) :
    ∃ ρ : Finset V → Finset V,
      (∀ D, K.toSimplicialComplex.IsMaximal D → ρ D ∈ B.faces) ∧
      (∀ D, B.IsMaximal D → ρ D = D) := by
  classical

  have hC₀_K_max : K.toSimplicialComplex.IsMaximal C₀ :=
    𝒜.maximal_in_apt_is_maximal B hB C₀ hC₀_max_B


  have retract_img : ∀ D, K.toSimplicialComplex.IsMaximal D →
      ∃ E, E ∈ B.faces := by
    intro D hD_max
    obtain ⟨A', hA'mem, hC₀_in_A', hD_in_A'⟩ := 𝒜.contains_pair C₀ D hC₀_K_max hD_max
    have hC₀_max_A' := 𝒜.building_maximal_in_apt_is_apt_maximal A' hA'mem C₀
      hC₀_in_A' hC₀_K_max
    obtain ⟨φ, _, _⟩ := 𝒜.iso_exists A' hA'mem B hB C₀ hC₀_in_A' hC₀_B
      C₀ hC₀_max_A' hC₀_B
    exact ⟨D.image φ.toFun, φ.map_face D hD_in_A'⟩

  refine ⟨fun D => if B.IsMaximal D then D
    else if h : K.toSimplicialComplex.IsMaximal D then (retract_img D h).choose
    else D, fun D hD_max => ?_, fun D hD_Bmax => ?_⟩
  ·
    dsimp only
    split_ifs with hBmax
    · exact hBmax.1
    · exact (retract_img D hD_max).choose_spec
  ·
    dsimp only
    split_ifs
    rfl

/-- A retraction $\rho$ onto an apartment preserves gallery distance from the center chamber $C$:
$d(C, \rho D) = d(C, D)$. -/
theorem retraction_preserves_dist_from_center
    {V : Type*} [DecidableEq V] {K : ChamberComplex V}
    (𝒜 : ApartmentSystem K)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (C : Finset V) (hC_max : A.IsMaximal C)
    (ρ : Finset V → Finset V)
    (hρ_into_A : ∀ D, K.toSimplicialComplex.IsMaximal D → ρ D ∈ A.faces)
    (hρ_fix_A : ∀ D, A.IsMaximal D → ρ D = D)
    (D : Finset V) (hD_max : K.toSimplicialComplex.IsMaximal D) :
    galleryDist K.toSimplicialComplex C D =
    galleryDist K.toSimplicialComplex C (ρ D) := by sorry

/-- If $\psi_0$ is a gallery-distance preserving map from $Y_0$ into the building, then composing
with the retraction $\rho$ recovers the original chamber: $\rho(\psi_0 E) = E$ for $E \in Y_0$. -/
theorem retraction_inverts_dist_preserving_map
    {V : Type*} [DecidableEq V] {K : ChamberComplex V}
    (𝒜 : ApartmentSystem K)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (C : Finset V) (hC_max : A.IsMaximal C)
    (ρ : Finset V → Finset V)
    (hρ_into_A : ∀ D, K.toSimplicialComplex.IsMaximal D → ρ D ∈ A.faces)
    (hρ_fix_A : ∀ D, A.IsMaximal D → ρ D = D)
    (Y₀ : Set (Finset V))
    (ψ₀ : Finset V → Finset V)
    (hY₀_sub : ∀ E ∈ Y₀, A.IsMaximal E)
    (hψ₀_max : ∀ E ∈ Y₀, K.toSimplicialComplex.IsMaximal (ψ₀ E))
    (hψ₀_dist : ∀ E₁ ∈ Y₀, ∀ E₂ ∈ Y₀,
        galleryDist K.toSimplicialComplex (ψ₀ E₁) (ψ₀ E₂) =
        galleryDist K.toSimplicialComplex E₁ E₂)
    (E : Finset V) (hE : E ∈ Y₀) :
    ρ (ψ₀ E) = E := by sorry

/-- Combining the previous two: a gallery-distance preserving map $\psi_0$ preserves the
distance from the center $C$, i.e. $d(C, \psi_0 E) = d(C, E)$ for $E \in Y_0$. -/
theorem retraction_preserves_galleryDist_from_center
    {V : Type*} [DecidableEq V] {K : ChamberComplex V}
    (𝒜 : ApartmentSystem K)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (C : Finset V) (hC_max : A.IsMaximal C)
    (Y₀ : Set (Finset V))
    (ψ₀ : Finset V → Finset V)
    (hY₀_sub : ∀ E ∈ Y₀, A.IsMaximal E)
    (hψ₀_max : ∀ E ∈ Y₀, K.toSimplicialComplex.IsMaximal (ψ₀ E))
    (hψ₀_dist : ∀ E₁ ∈ Y₀, ∀ E₂ ∈ Y₀,
        galleryDist K.toSimplicialComplex (ψ₀ E₁) (ψ₀ E₂) =
        galleryDist K.toSimplicialComplex E₁ E₂)
    (E : Finset V) (hE : E ∈ Y₀) :
    galleryDist K.toSimplicialComplex C (ψ₀ E) =
    galleryDist K.toSimplicialComplex C E := by

  have hC_in_A : C ∈ A.faces := hC_max.1

  obtain ⟨ρ, hρ_into_A, hρ_fix_A⟩ :=
    canonical_retraction_onto_apartment 𝒜 A hA C hC_in_A hC_max

  have hψ₀E_max : K.toSimplicialComplex.IsMaximal (ψ₀ E) := hψ₀_max E hE


  have h_dist_pres : galleryDist K.toSimplicialComplex C (ψ₀ E) =
      galleryDist K.toSimplicialComplex C (ρ (ψ₀ E)) :=
    retraction_preserves_dist_from_center 𝒜 A hA C hC_max ρ hρ_into_A hρ_fix_A
      (ψ₀ E) hψ₀E_max

  have h_retract_inv : ρ (ψ₀ E) = E :=
    retraction_inverts_dist_preserving_map 𝒜 A hA C hC_max ρ hρ_into_A hρ_fix_A
      Y₀ ψ₀ hY₀_sub hψ₀_max hψ₀_dist E hE

  rw [h_dist_pres, h_retract_inv]

/-- One-step extension of a gallery isometry: given a chamber $C'$ adjacent to the domain $Y_0$,
one can extend $\psi_0$ to $C'$ while preserving all gallery distances. -/
theorem galleryDist_one_step_extension
    {V : Type*} [DecidableEq V] {K : ChamberComplex V}
    (𝒜 : ApartmentSystem K)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (Y₀ : Set (Finset V))
    (ψ₀ : Finset V → Finset V)
    (hY₀_sub : ∀ C ∈ Y₀, A.IsMaximal C)
    (hψ₀_max : ∀ C ∈ Y₀, K.toSimplicialComplex.IsMaximal (ψ₀ C))
    (hψ₀_dist : ∀ C ∈ Y₀, ∀ D ∈ Y₀,
        galleryDist K.toSimplicialComplex (ψ₀ C) (ψ₀ D) =
        galleryDist K.toSimplicialComplex C D)
    (C' : Finset V)
    (hC'_max : A.IsMaximal C')
    (hC'_not : C' ∉ Y₀)
    (hC'_adj : ∃ D ∈ Y₀, A.Adjacent C' D) :
    ∃ (D' : Finset V),
      K.toSimplicialComplex.IsMaximal D' ∧
      (∀ E ∈ Y₀,
        galleryDist K.toSimplicialComplex D' (ψ₀ E) =
        galleryDist K.toSimplicialComplex C' E) := by

  have hC'_K_max : K.toSimplicialComplex.IsMaximal C' :=
    𝒜.maximal_in_apt_is_maximal A hA C' hC'_max
  refine ⟨C', hC'_K_max, fun E hE => ?_⟩

  exact retraction_preserves_galleryDist_from_center 𝒜 A hA C' hC'_max Y₀ ψ₀
    hY₀_sub hψ₀_max hψ₀_dist E hE

/-- In a finite chain whose head satisfies $P$ and last does not, there is an adjacent pair where $P$ flips. -/
lemma list_boundary_crossing {α : Type*} {R : α → α → Prop}
    (l : List α) (P : α → Prop) [DecidablePred P]
    (hl : l ≠ [])
    (hchain : List.IsChain R l)
    (hhead : P (l.head hl))
    (hlast : ¬P (l.getLast hl)) :
    ∃ a b, a ∈ l ∧ b ∈ l ∧ P a ∧ ¬P b ∧ R a b := by
  induction l with
  | nil => exact absurd rfl hl
  | cons x xs ih =>
    by_cases hxs : xs = []
    · subst hxs; simp at hhead hlast; exact absurd hhead hlast
    · by_cases hP_next : P (xs.head hxs)
      · have hchain_rest := hchain.tail
        have hlast_xs : ¬P (xs.getLast hxs) := by rwa [List.getLast_cons hxs] at hlast
        obtain ⟨a, b, ha, hb, hPa, hnPb, hRab⟩ :=
          ih hxs hchain_rest hP_next hlast_xs
        exact ⟨a, b, List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hb, hPa, hnPb, hRab⟩
      · have heq : xs = xs.head hxs :: xs.tail := (List.cons_head_tail hxs).symm
        rw [heq] at hchain
        exact ⟨x, xs.head hxs, List.mem_cons_self, List.mem_cons_of_mem _ (List.head_mem hxs),
               by simpa using hhead, hP_next, List.IsChain.rel hchain⟩

/-- Gallery boundary: a proper non-empty subset $Y_0$ of the maximal chambers of $A$ has a
boundary chamber $C' \notin Y_0$ adjacent to some chamber of $Y_0$. -/
theorem ApartmentSystem.apt_gallery_boundary
    {V : Type*} [DecidableEq V] {K : ChamberComplex V}
    (𝒜 : ApartmentSystem K)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (Y₀ : Set (Finset V))
    (hY₀_sub : ∀ C ∈ Y₀, A.IsMaximal C)
    (hY₀_nonempty : Y₀.Nonempty)
    (hY₀_proper : ∃ D, A.IsMaximal D ∧ D ∉ Y₀) :
    ∃ C', A.IsMaximal C' ∧ C' ∉ Y₀ ∧ ∃ D ∈ Y₀, A.Adjacent C' D := by
  classical

  obtain ⟨B_idx, M, cc, hcc_eq, _φ, _hinj, _hsurj, _hadj, _hthin⟩ :=
    𝒜.apt_is_coxeter A hA

  subst hcc_eq

  obtain ⟨C_in, hC_in⟩ := hY₀_nonempty
  obtain ⟨D_out, hD_out_max, hD_out_not⟩ := hY₀_proper

  have hC_in_max := hY₀_sub C_in hC_in
  have hD_out_max' := hD_out_max

  obtain ⟨g, hg_head, hg_last⟩ := cc.gallery_connected C_in D_out hC_in_max hD_out_max'

  have hg_ne : g.chambers ≠ [] := List.ne_nil_of_length_pos g.length_pos
  have hg_head_val : g.chambers.head hg_ne = C_in := by
    have h := List.head?_eq_some_head hg_ne; rw [h] at hg_head
    exact Option.some_injective _ hg_head
  have hg_last_val : g.chambers.getLast hg_ne = D_out := by
    have h := List.getLast?_eq_some_getLast hg_ne; rw [h] at hg_last
    exact Option.some_injective _ hg_last

  have hchain := g.adjacent_consecutive


  have hhead_P : (g.chambers.head hg_ne) ∈ Y₀ := hg_head_val ▸ hC_in
  have hlast_nP : (g.chambers.getLast hg_ne) ∉ Y₀ := hg_last_val ▸ hD_out_not
  obtain ⟨a, b, _ha_mem, _hb_mem, ha_in, hb_not, hab_adj⟩ :=
    list_boundary_crossing g.chambers (· ∈ Y₀) hg_ne hchain hhead_P hlast_nP


  have hb_max : cc.toSimplicialComplex.IsMaximal b := hab_adj.2.1
  exact ⟨b, hb_max, hb_not, a, ha_in, cc.toSimplicialComplex.adjacent_symm _ _ hab_adj⟩

/-- The image of a gallery-distance preserving map into the apartment $A$ is maximal in $A$. -/
theorem coxeter_bridge_apartment_maximal
    {V : Type*} [DecidableEq V] {K : ChamberComplex V}
    (𝒜 : ApartmentSystem K)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (S₁ : Set (Finset V)) (φ : Finset V → Finset V)
    (hφ_into_A : ∀ C ∈ S₁, φ C ∈ A.faces)
    (hφdist : ∀ C ∈ S₁, ∀ D ∈ S₁,
      galleryDist K.toSimplicialComplex (φ C) (φ D) =
      galleryDist K.toSimplicialComplex C D)
    (C : Finset V) (hC : C ∈ S₁) :
    A.IsMaximal (φ C) := by sorry

/-- The image $\varphi C$ is a maximal chamber of the ambient building $K$. -/
theorem coxeter_bridge_image_maximal
    {V : Type*} [DecidableEq V] {K : ChamberComplex V}
    (𝒜 : ApartmentSystem K)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (S₁ : Set (Finset V)) (φ : Finset V → Finset V)
    (hφ_into_A : ∀ C ∈ S₁, φ C ∈ A.faces)
    (hφdist : ∀ C ∈ S₁, ∀ D ∈ S₁,
      galleryDist K.toSimplicialComplex (φ C) (φ D) =
      galleryDist K.toSimplicialComplex C D)
    (C : Finset V) (hC : C ∈ S₁) :
    K.toSimplicialComplex.IsMaximal (φ C) :=
  𝒜.maximal_in_apt_is_maximal A hA (φ C)
    (coxeter_bridge_apartment_maximal 𝒜 A hA S₁ φ hφ_into_A hφdist C hC)

/-- Gallery distance from a non-maximal chamber to any other chamber is $0$. -/
lemma nonmaximal_galleryDist_zero {K : SimplicialComplex V}
    {C : Finset V} (hnomax : ¬ K.IsMaximal C) (D : Finset V) :
    galleryDist K C D = 0 := by
  by_cases hCD : C = D
  · subst hCD; exact galleryDist_self K C
  · unfold galleryDist
    simp only [hCD, ↓reduceIte]
    have hempty : {n | ∃ g : Gallery K, g.Connects C D ∧ g.length = n} = ∅ := by
      ext n
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨g, hconn, -⟩
      apply hnomax
      have hne_nil : g.chambers ≠ [] := by
        intro h
        have := g.length_pos
        simp [h] at this
      have hhead := hconn.1
      rw [List.head?_eq_some_head hne_nil] at hhead
      have heq := Option.some_injective _ hhead
      rw [← heq]
      exact g.all_maximal _ (List.head_mem hne_nil)
    rw [hempty]
    exact Nat.sInf_empty

/-- Two distinct maximal chambers have strictly positive gallery distance. -/
lemma galleryDist_pos_of_maximal_ne (K : ChamberComplex V)
    {C D : Finset V} (hCmax : K.toSimplicialComplex.IsMaximal C)
    (hDmax : K.toSimplicialComplex.IsMaximal D) (hne : C ≠ D) :
    0 < galleryDist K.toSimplicialComplex C D := by
  unfold galleryDist
  simp only [hne, ↓reduceIte]
  obtain ⟨g, hg_head, hg_last⟩ := K.gallery_connected C D hCmax hDmax
  have hnonempty : {n | ∃ g : Gallery K.toSimplicialComplex,
      g.Connects C D ∧ g.length = n}.Nonempty :=
    ⟨g.length, g, ⟨hg_head, hg_last⟩, rfl⟩
  by_contra h
  push Not at h
  have h0 : sInf {n | ∃ g : Gallery K.toSimplicialComplex,
      g.Connects C D ∧ g.length = n} = 0 := Nat.le_zero.mp h
  rw [Nat.sInf_eq_zero] at h0
  rcases h0 with ⟨g0, ⟨hconn0_head, hconn0_last⟩, hlen0⟩ | hempty
  ·
    have hcl : g0.chambers.length = 1 := by
      have := g0.length_pos; unfold Gallery.length at hlen0; omega
    have hone : ∃ x, g0.chambers = [x] := by
      match g0.chambers, hcl with
      | [x], _ => exact ⟨x, rfl⟩
    obtain ⟨x, hx⟩ := hone
    simp [hx] at hconn0_head hconn0_last
    exact hne (hconn0_head.symm.trans hconn0_last)
  · exact absurd hempty (Set.nonempty_iff_ne_empty.mp hnonempty)

/-- When $\varphi$ is constant on its domain $S_1$, every element of $S_1$ is itself maximal in $K$. -/
theorem coxeter_bridge_constant_source_maximal
    {V : Type*} [DecidableEq V] {K : ChamberComplex V}
    (𝒜 : ApartmentSystem K)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (S₁ : Set (Finset V)) (φ : Finset V → Finset V)
    (hφ_into_A : ∀ C ∈ S₁, φ C ∈ A.faces)
    (hφdist : ∀ C ∈ S₁, ∀ D ∈ S₁,
      galleryDist K.toSimplicialComplex (φ C) (φ D) =
      galleryDist K.toSimplicialComplex C D)
    (C : Finset V) (hC : C ∈ S₁)
    (hconst : ∀ D ∈ S₁, φ D = φ C) :
    K.toSimplicialComplex.IsMaximal C := by sorry

/-- A chamber $C$ in the source of a gallery-distance preserving map is maximal in $K$. -/
theorem coxeter_bridge_source_maximal
    {V : Type*} [DecidableEq V] {K : ChamberComplex V}
    (𝒜 : ApartmentSystem K)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (S₁ : Set (Finset V)) (φ : Finset V → Finset V)
    (hφ_into_A : ∀ C ∈ S₁, φ C ∈ A.faces)
    (hφdist : ∀ C ∈ S₁, ∀ D ∈ S₁,
      galleryDist K.toSimplicialComplex (φ C) (φ D) =
      galleryDist K.toSimplicialComplex C D)
    (C : Finset V) (hC : C ∈ S₁) :
    K.toSimplicialComplex.IsMaximal C := by
  classical

  by_cases hconst : ∀ D ∈ S₁, φ D = φ C
  ·
    exact coxeter_bridge_constant_source_maximal 𝒜 A hA S₁ φ hφ_into_A hφdist C hC hconst
  ·
    push Not at hconst
    obtain ⟨D, hD, hφne⟩ := hconst
    by_contra hnmax

    have h_zero := nonmaximal_galleryDist_zero hnmax D

    have h_phi_zero : galleryDist K.toSimplicialComplex (φ C) (φ D) = 0 := by
      rw [hφdist C hC D hD]; exact h_zero

    have hφCmax := coxeter_bridge_image_maximal 𝒜 A hA S₁ φ hφ_into_A hφdist C hC
    have hφDmax := coxeter_bridge_image_maximal 𝒜 A hA S₁ φ hφ_into_A hφdist D hD

    have h_pos := galleryDist_pos_of_maximal_ne K hφCmax hφDmax hφne.symm

    omega

/-- A gallery-distance preserving map $\varphi : S_1 \to A.\mathrm{faces}$ maps to apartment-maximal
chambers and its source consists of building-maximal chambers. -/
theorem galleryDist_preserving_maps_to_maximal
    {V : Type*} [DecidableEq V] {K : ChamberComplex V}
    (𝒜 : ApartmentSystem K)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (S₁ : Set (Finset V)) (φ : Finset V → Finset V)
    (hφ_into_A : ∀ C ∈ S₁, φ C ∈ A.faces)
    (hφdist : ∀ C ∈ S₁, ∀ D ∈ S₁,
      galleryDist K.toSimplicialComplex (φ C) (φ D) =
      galleryDist K.toSimplicialComplex C D)
    (C : Finset V) (hC : C ∈ S₁) :
    A.IsMaximal (φ C) ∧ K.toSimplicialComplex.IsMaximal C := by
  constructor
  ·
    exact 𝒜.building_maximal_in_apt_is_apt_maximal A hA (φ C) (hφ_into_A C hC)
      (coxeter_bridge_image_maximal 𝒜 A hA S₁ φ hφ_into_A hφdist C hC)
  ·
    exact coxeter_bridge_source_maximal 𝒜 A hA S₁ φ hφ_into_A hφdist C hC

/-- A gallery-distance preserving map $\varphi$ is injective: $\varphi C = \varphi D$ implies $C = D$. -/
theorem galleryDist_preserving_injective
    {V : Type*} [DecidableEq V] {K : ChamberComplex V}
    (𝒜 : ApartmentSystem K)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (S₁ : Set (Finset V)) (φ : Finset V → Finset V)
    (hφ_into_A : ∀ C ∈ S₁, φ C ∈ A.faces)
    (hφdist : ∀ C ∈ S₁, ∀ D ∈ S₁,
      galleryDist K.toSimplicialComplex (φ C) (φ D) =
      galleryDist K.toSimplicialComplex C D)
    (C D : Finset V) (hC : C ∈ S₁) (hD : D ∈ S₁)
    (hφeq : φ C = φ D) : C = D := by

  have h0 : galleryDist K.toSimplicialComplex (φ C) (φ D) = 0 := by
    rw [hφeq]; exact galleryDist_self K.toSimplicialComplex (φ D)

  have hCD0 : galleryDist K.toSimplicialComplex C D = 0 := by
    rw [← hφdist C hC D hD]; exact h0

  have hCmax := coxeter_bridge_source_maximal 𝒜 A hA S₁ φ hφ_into_A hφdist C hC
  have hDmax := coxeter_bridge_source_maximal 𝒜 A hA S₁ φ hφ_into_A hφdist D hD

  by_contra hne
  unfold galleryDist at hCD0
  simp only [hne, ↓reduceIte] at hCD0

  obtain ⟨g, hg⟩ := K.gallery_connected C D hCmax hDmax
  have hnonempty : {n | ∃ g : Gallery K.toSimplicialComplex,
      g.Connects C D ∧ g.length = n}.Nonempty :=
    ⟨g.length, g, ⟨hg.1, hg.2⟩, rfl⟩
  rw [Nat.sInf_eq_zero] at hCD0
  rcases hCD0 with ⟨g0, hconn0, hlen0⟩ | hempty
  ·
    have hcl : g0.chambers.length = 1 := by
      have := g0.length_pos; unfold Gallery.length at hlen0; omega

    have hone : ∃ x, g0.chambers = [x] := by
      match g0.chambers, hcl with
      | [x], _ => exact ⟨x, rfl⟩
    obtain ⟨x, hx⟩ := hone
    have hhead := hconn0.1
    have hlast := hconn0.2
    rw [hx] at hhead hlast
    simp at hhead hlast
    exact hne (hhead.symm.trans hlast)
  · exact absurd hempty (Set.nonempty_iff_ne_empty.mp hnonempty)

/-- Seed graph $G_0$ for the gallery-isometry extension: a functional relation on chamber pairs
$(C, D)$ encoding an initial fragment of a gallery isometry into the apartment $A$. -/
theorem ApartmentSystem.gallery_iso_seed
    {V : Type*} [DecidableEq V] {K : ChamberComplex V}
    (𝒜 : ApartmentSystem K)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (S₁ : Set (Finset V)) (φ : Finset V → Finset V)
    (hφ_into_A : ∀ C ∈ S₁, φ C ∈ A.faces)
    (hφdist : ∀ C ∈ S₁, ∀ D ∈ S₁,
      galleryDist K.toSimplicialComplex (φ C) (φ D) =
      galleryDist K.toSimplicialComplex C D) :
    ∃ (G₀ : Set (Finset V × Finset V)),
      (∀ C D₁ D₂, (C, D₁) ∈ G₀ → (C, D₂) ∈ G₀ → D₁ = D₂) ∧
      (∀ C D, (C, D) ∈ G₀ → A.IsMaximal C) ∧
      (∀ C D, (C, D) ∈ G₀ → K.toSimplicialComplex.IsMaximal D) ∧
      (∀ C₁ D₁ C₂ D₂, (C₁, D₁) ∈ G₀ → (C₂, D₂) ∈ G₀ →
        galleryDist K.toSimplicialComplex D₁ D₂ =
        galleryDist K.toSimplicialComplex C₁ C₂) ∧
      (∀ C ∈ S₁, ∃ D, (D, C) ∈ G₀) := by

  let G₀ : Set (Finset V × Finset V) := { p | ∃ E ∈ S₁, p = (φ E, E) }
  refine ⟨G₀, ?_, ?_, ?_, ?_, ?_⟩
  ·

    intro C D₁ D₂ ⟨E₁, hE₁, h₁⟩ ⟨E₂, hE₂, h₂⟩
    have heq₁ := Prod.mk.inj h₁
    have heq₂ := Prod.mk.inj h₂
    have hφ_eq : φ E₁ = φ E₂ := heq₁.1.symm.trans heq₂.1
    have hE_eq := galleryDist_preserving_injective 𝒜 A hA S₁ φ hφ_into_A hφdist
      E₁ E₂ hE₁ hE₂ hφ_eq
    rw [heq₁.2, heq₂.2, hE_eq]
  ·
    intro C D ⟨E, hE, h⟩
    have heq := Prod.mk.inj h
    rw [heq.1]
    exact (galleryDist_preserving_maps_to_maximal 𝒜 A hA S₁ φ hφ_into_A hφdist E hE).1
  ·
    intro C D ⟨E, hE, h⟩
    have heq := Prod.mk.inj h
    rw [heq.2]
    exact (galleryDist_preserving_maps_to_maximal 𝒜 A hA S₁ φ hφ_into_A hφdist E hE).2
  ·
    intro C₁ D₁ C₂ D₂ ⟨E₁, hE₁, h₁⟩ ⟨E₂, hE₂, h₂⟩
    have heq₁ := Prod.mk.inj h₁
    have heq₂ := Prod.mk.inj h₂
    rw [heq₁.2, heq₂.2, heq₁.1, heq₂.1]
    exact (hφdist E₁ hE₁ E₂ hE₂).symm
  ·
    intro C hC
    exact ⟨φ C, ⟨C, hC, rfl⟩⟩

/-- Using Zorn's lemma, a gallery-distance preserving map from a subset $S_1$ into $A$ extends to a
gallery-distance preserving map $\psi$ defined on all maximal chambers of $A$ with image in $K$. -/
theorem ApartmentSystem.gallery_iso_ext_to_full_apartment
    {V : Type*} [DecidableEq V] {K : ChamberComplex V}
    (𝒜 : ApartmentSystem K)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (S₁ : Set (Finset V)) (φ : Finset V → Finset V)
    (hφ_into_A : ∀ C ∈ S₁, φ C ∈ A.faces)
    (hφdist : ∀ C ∈ S₁, ∀ D ∈ S₁,
      galleryDist K.toSimplicialComplex (φ C) (φ D) =
      galleryDist K.toSimplicialComplex C D) :
    ∃ (ψ : Finset V → Finset V),
      (∀ C, A.IsMaximal C → K.toSimplicialComplex.IsMaximal (ψ C)) ∧
      (∀ C D, A.IsMaximal C → A.IsMaximal D →
        galleryDist K.toSimplicialComplex (ψ C) (ψ D) =
        galleryDist K.toSimplicialComplex C D) ∧
      (∀ C ∈ S₁, ∃ D, A.IsMaximal D ∧ ψ D = C) := by
  classical

  obtain ⟨G₀, hG₀_func, hG₀_dom, hG₀_rng, hG₀_dist, hG₀_covers⟩ :=
    𝒜.gallery_iso_seed A hA S₁ φ hφ_into_A hφdist


  let Good : Set (Set (Finset V × Finset V)) :=
    {G |
      (∀ C D₁ D₂, (C, D₁) ∈ G → (C, D₂) ∈ G → D₁ = D₂) ∧
      (∀ C D, (C, D) ∈ G → A.IsMaximal C) ∧
      (∀ C D, (C, D) ∈ G → K.toSimplicialComplex.IsMaximal D) ∧
      (∀ C₁ D₁ C₂ D₂, (C₁, D₁) ∈ G → (C₂, D₂) ∈ G →
        galleryDist K.toSimplicialComplex D₁ D₂ =
        galleryDist K.toSimplicialComplex C₁ C₂)}

  have hG₀_good : G₀ ∈ Good := ⟨hG₀_func, hG₀_dom, hG₀_rng, hG₀_dist⟩

  have hChain : ∀ c ⊆ Good, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ Good, ∀ s ∈ c, s ⊆ ub := by
    intro c hc_sub hc_chain ⟨G₁, hG₁⟩
    refine ⟨⋃₀ c, ?_, fun s hs => Set.subset_sUnion_of_mem hs⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro C D₁ D₂ ⟨G₁', hG₁', h₁⟩ ⟨G₂', hG₂', h₂⟩
      rcases hc_chain.total hG₁' hG₂' with h | h
      · exact (hc_sub hG₂').1 C D₁ D₂ (h h₁) h₂
      · exact (hc_sub hG₁').1 C D₁ D₂ h₁ (h h₂)
    · intro C D ⟨G₁', hG₁', h₁⟩
      exact (hc_sub hG₁').2.1 C D h₁
    · intro C D ⟨G₁', hG₁', h₁⟩
      exact (hc_sub hG₁').2.2.1 C D h₁
    · intro C₁ D₁ C₂ D₂ ⟨G₁', hG₁', h₁⟩ ⟨G₂', hG₂', h₂⟩
      rcases hc_chain.total hG₁' hG₂' with h | h
      · exact (hc_sub hG₂').2.2.2 C₁ D₁ C₂ D₂ (h h₁) h₂
      · exact (hc_sub hG₁').2.2.2 C₁ D₁ C₂ D₂ h₁ (h h₂)

  obtain ⟨G_max, hG₀_sub_max, hG_max_maximal⟩ :=
    zorn_subset_nonempty Good hChain G₀ hG₀_good
  obtain ⟨hG_func, hG_dom, hG_rng, hG_dist⟩ := hG_max_maximal.prop

  let dom_G : Set (Finset V) := {C | ∃ D, (C, D) ∈ G_max}
  have hdom_sub : ∀ C ∈ dom_G, A.IsMaximal C := by
    intro C ⟨D, hCD⟩; exact hG_dom C D hCD

  let ψ_partial : Finset V → Finset V := fun C =>
    if h : C ∈ dom_G then Classical.choose h else C
  have hψ_agrees : ∀ C (hC : C ∈ dom_G), (C, ψ_partial C) ∈ G_max := by
    intro C hC
    simp only [ψ_partial, dif_pos hC]
    exact Classical.choose_spec hC
  have hψ_max : ∀ C ∈ dom_G, K.toSimplicialComplex.IsMaximal (ψ_partial C) := by
    intro C hC; exact hG_rng C _ (hψ_agrees C hC)
  have hψ_dist : ∀ C ∈ dom_G, ∀ D ∈ dom_G,
      galleryDist K.toSimplicialComplex (ψ_partial C) (ψ_partial D) =
      galleryDist K.toSimplicialComplex C D := by
    intro C hC D hD
    exact hG_dist C _ D _ (hψ_agrees C hC) (hψ_agrees D hD)

  suffices h_total : ∀ C, A.IsMaximal C → C ∈ dom_G by
    refine ⟨ψ_partial,
      fun C hC => hψ_max C (h_total C hC),
      fun C D hC hD => hψ_dist C (h_total C hC) D (h_total D hD),
      fun C hC => ?_⟩

    obtain ⟨D, hDC_in_G₀⟩ := hG₀_covers C hC
    have hDC_in_Gmax : (D, C) ∈ G_max := hG₀_sub_max hDC_in_G₀
    have hD_max : A.IsMaximal D := hG_dom D C hDC_in_Gmax
    refine ⟨D, hD_max, ?_⟩

    have hD_in_dom : D ∈ dom_G := ⟨C, hDC_in_Gmax⟩
    exact hG_func D (ψ_partial D) C (hψ_agrees D hD_in_dom) hDC_in_Gmax

  intro C hC_max
  by_contra hC_not
  by_cases hdom_empty : dom_G = ∅
  ·
    have hC_K_max := 𝒜.maximal_in_apt_is_maximal A hA C hC_max
    have hsingleton_good : {(C, C)} ∈ Good := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro C' D₁ D₂ h₁ h₂
        rw [Set.mem_singleton_iff, Prod.mk.injEq] at h₁ h₂
        rw [h₁.2, h₂.2]
      · intro C' D h
        rw [Set.mem_singleton_iff, Prod.mk.injEq] at h
        rw [h.1]; exact hC_max
      · intro C' D h
        rw [Set.mem_singleton_iff, Prod.mk.injEq] at h
        rw [h.2]; exact hC_K_max
      · intro C₁ D₁ C₂ D₂ h₁ h₂
        rw [Set.mem_singleton_iff, Prod.mk.injEq] at h₁ h₂
        rw [h₁.1, h₁.2, h₂.1, h₂.2]
    have hG_max_empty : G_max ⊆ {(C, C)} := by
      intro p hp
      exfalso
      obtain ⟨a, b⟩ := p
      exact (hdom_empty ▸ (⟨b, hp⟩ : a ∈ dom_G) : (a : Finset V) ∈ (∅ : Set (Finset V)))
    have hstrict : ¬{(C, C)} ⊆ G_max := by
      intro h; exact hC_not ⟨C, h rfl⟩
    exact hstrict (hG_max_maximal.2 hsingleton_good hG_max_empty)
  ·
    push Not at hdom_empty
    obtain ⟨E, hE⟩ := hdom_empty
    obtain ⟨C', hC'_max, hC'_not, D, hD_in, hC'D_adj⟩ :=
      𝒜.apt_gallery_boundary A hA dom_G hdom_sub ⟨E, hE⟩ ⟨C, hC_max, hC_not⟩
    obtain ⟨D', hD'_max, hD'_dist⟩ :=
      galleryDist_one_step_extension 𝒜 A hA dom_G ψ_partial hdom_sub hψ_max hψ_dist
        C' hC'_max hC'_not ⟨D, hD_in, hC'D_adj⟩
    let G_ext := G_max ∪ {(C', D')}
    have hG_ext_good : G_ext ∈ Good := by
      refine ⟨?_, ?_, ?_, ?_⟩
      ·
        intro E' E₁ E₂ h₁ h₂
        rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
        · exact hG_func E' E₁ E₂ h₁ h₂
        · rw [Set.mem_singleton_iff, Prod.mk.injEq] at h₂
          rw [h₂.1] at h₁; exact absurd ⟨E₁, h₁⟩ hC'_not
        · rw [Set.mem_singleton_iff, Prod.mk.injEq] at h₁
          rw [h₁.1] at h₂; exact absurd ⟨E₂, h₂⟩ hC'_not
        · rw [Set.mem_singleton_iff, Prod.mk.injEq] at h₁ h₂
          rw [h₁.2, h₂.2]
      ·
        intro E' F h
        rcases h with h | h
        · exact hG_dom E' F h
        · rw [Set.mem_singleton_iff, Prod.mk.injEq] at h
          rw [h.1]; exact hC'_max
      ·
        intro E' F h
        rcases h with h | h
        · exact hG_rng E' F h
        · rw [Set.mem_singleton_iff, Prod.mk.injEq] at h
          rw [h.2]; exact hD'_max
      ·
        intro C₁ D₁ C₂ D₂ h₁ h₂
        rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
        · exact hG_dist C₁ D₁ C₂ D₂ h₁ h₂
        · rw [Set.mem_singleton_iff, Prod.mk.injEq] at h₂
          have hC₁_dom : C₁ ∈ dom_G := ⟨D₁, h₁⟩
          have hD₁_eq : D₁ = ψ_partial C₁ :=
            hG_func C₁ D₁ (ψ_partial C₁) h₁ (hψ_agrees C₁ hC₁_dom)
          rw [hD₁_eq, h₂.1, h₂.2]
          rw [galleryDist_comm _ (ψ_partial C₁) D', hD'_dist C₁ hC₁_dom,
              galleryDist_comm]
        · rw [Set.mem_singleton_iff, Prod.mk.injEq] at h₁
          have hC₂_dom : C₂ ∈ dom_G := ⟨D₂, h₂⟩
          have hD₂_eq : D₂ = ψ_partial C₂ :=
            hG_func C₂ D₂ (ψ_partial C₂) h₂ (hψ_agrees C₂ hC₂_dom)
          rw [hD₂_eq, h₁.1, h₁.2]
          exact hD'_dist C₂ hC₂_dom
        · rw [Set.mem_singleton_iff, Prod.mk.injEq] at h₁ h₂
          rw [h₁.1, h₁.2, h₂.1, h₂.2]
          simp [galleryDist_self]

    have hG_max_sub : G_max ⊆ G_ext := Set.subset_union_left
    have hG_ext_larger : ¬G_ext ⊆ G_max := by
      intro h
      exact hC'_not ⟨D', h (Set.mem_union_right _ rfl)⟩
    exact hG_ext_larger (hG_max_maximal.2 hG_ext_good hG_max_sub)

/-- Uniqueness lemma: two gallery-distance preserving maps from $A$ into $K$ that agree on a single
chamber $C_0$ agree on every maximal chamber of $A$. -/
theorem uniqueness_lemma_gallery_dist
    {V : Type*} [DecidableEq V] {K : ChamberComplex V}
    (𝒜 : ApartmentSystem K)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (f g : Finset V → Finset V)
    (hf_max : ∀ C, A.IsMaximal C → K.toSimplicialComplex.IsMaximal (f C))
    (hg_max : ∀ C, A.IsMaximal C → K.toSimplicialComplex.IsMaximal (g C))
    (hf_dist : ∀ C D, A.IsMaximal C → A.IsMaximal D →
      galleryDist K.toSimplicialComplex (f C) (f D) =
      galleryDist K.toSimplicialComplex C D)
    (hg_dist : ∀ C D, A.IsMaximal C → A.IsMaximal D →
      galleryDist K.toSimplicialComplex (g C) (g D) =
      galleryDist K.toSimplicialComplex C D)
    (C₀ : Finset V) (hC₀_A : A.IsMaximal C₀)
    (hagree : f C₀ = g C₀) :
    ∀ D, A.IsMaximal D → f D = g D := by sorry

/-- The composition $\rho \circ \psi$ of a retraction $\rho$ onto $B$ with a gallery-isometry
$\psi$ is again a gallery isometry into $K$. -/
theorem retraction_comp_preserves_gallery_dist
    {V : Type*} [DecidableEq V] {K : ChamberComplex V}
    (𝒜 : ApartmentSystem K)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (B : SimplicialComplex V) (hB : B ∈ 𝒜.apartments)
    (C₀ : Finset V) (hC₀_A : A.IsMaximal C₀) (hC₀_in_B : C₀ ∈ B.faces)
    (ψ : Finset V → Finset V)
    (hψ_max : ∀ C, A.IsMaximal C → K.toSimplicialComplex.IsMaximal (ψ C))
    (hψ_dist : ∀ C D, A.IsMaximal C → A.IsMaximal D →
      galleryDist K.toSimplicialComplex (ψ C) (ψ D) =
      galleryDist K.toSimplicialComplex C D)
    (ρ : Finset V → Finset V)
    (hρ_into_B : ∀ D, K.toSimplicialComplex.IsMaximal D → ρ D ∈ B.faces)
    (hρ_fix_B : ∀ D, B.IsMaximal D → ρ D = D) :
    (∀ C, A.IsMaximal C → K.toSimplicialComplex.IsMaximal (ρ (ψ C))) ∧
    (∀ C D, A.IsMaximal C → A.IsMaximal D →
      galleryDist K.toSimplicialComplex (ρ (ψ C)) (ρ (ψ D)) =
      galleryDist K.toSimplicialComplex C D) := by sorry

/-- If $\psi C_0 \in B$ and $\rho$ retracts onto $B$, then $\rho \circ \psi = \psi$ on every
maximal chamber $D$ of $A$. -/
theorem retraction_fixes_gallery_dist_image
    {V : Type*} [DecidableEq V] {K : ChamberComplex V}
    (𝒜 : ApartmentSystem K)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (B : SimplicialComplex V) (hB : B ∈ 𝒜.apartments)
    (C₀ : Finset V) (hC₀_A : A.IsMaximal C₀) (hC₀_in_B : C₀ ∈ B.faces)
    (ψ : Finset V → Finset V)
    (hψ_max : ∀ C, A.IsMaximal C → K.toSimplicialComplex.IsMaximal (ψ C))
    (hψ_dist : ∀ C D, A.IsMaximal C → A.IsMaximal D →
      galleryDist K.toSimplicialComplex (ψ C) (ψ D) =
      galleryDist K.toSimplicialComplex C D)
    (hψC₀_in_B : ψ C₀ ∈ B.faces)
    (ρ : Finset V → Finset V)
    (hρ_into_B : ∀ D, K.toSimplicialComplex.IsMaximal D → ρ D ∈ B.faces)
    (hρ_fix_B : ∀ D, B.IsMaximal D → ρ D = D) :
    ∀ D, A.IsMaximal D → ρ (ψ D) = ψ D := by

  have hψC₀_K_max := hψ_max C₀ hC₀_A

  have hψC₀_B_max := 𝒜.building_maximal_in_apt_is_apt_maximal B hB (ψ C₀) hψC₀_in_B hψC₀_K_max

  have hρ_fix_ψC₀ : ρ (ψ C₀) = ψ C₀ := hρ_fix_B (ψ C₀) hψC₀_B_max

  obtain ⟨hρψ_max, hρψ_dist⟩ := retraction_comp_preserves_gallery_dist 𝒜 A hA B hB C₀ hC₀_A
    hC₀_in_B ψ hψ_max hψ_dist ρ hρ_into_B hρ_fix_B


  exact uniqueness_lemma_gallery_dist 𝒜 A hA (fun C => ρ (ψ C)) ψ
    hρψ_max hψ_max hρψ_dist hψ_dist C₀ hC₀_A hρ_fix_ψC₀

/-- If a gallery isometry $\psi$ sends one chamber $C_0$ into apartment $B$, then it sends every
maximal chamber of $A$ into $B$. -/
theorem retraction_uniqueness_apartment_image
    {V : Type*} [DecidableEq V] {K : ChamberComplex V}
    (𝒜 : ApartmentSystem K)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (B : SimplicialComplex V) (hB : B ∈ 𝒜.apartments)
    (C₀ : Finset V) (hC₀_A : A.IsMaximal C₀)
    (hC₀_in_B : C₀ ∈ B.faces)
    (ψ : Finset V → Finset V)
    (hψ_max : ∀ C, A.IsMaximal C → K.toSimplicialComplex.IsMaximal (ψ C))
    (hψ_dist : ∀ C D, A.IsMaximal C → A.IsMaximal D →
      galleryDist K.toSimplicialComplex (ψ C) (ψ D) =
      galleryDist K.toSimplicialComplex C D)
    (hψC₀_in_B : ψ C₀ ∈ B.faces) :
    ∀ D, A.IsMaximal D → ψ D ∈ B.faces := by

  have hC₀_K_max := 𝒜.maximal_in_apt_is_maximal A hA C₀ hC₀_A
  have hC₀_B_max := 𝒜.building_maximal_in_apt_is_apt_maximal B hB C₀ hC₀_in_B hC₀_K_max

  obtain ⟨ρ, hρ_into_B, hρ_fix_B⟩ :=
    canonical_retraction_onto_apartment 𝒜 B hB C₀ hC₀_in_B hC₀_B_max

  have hρψ_eq := retraction_fixes_gallery_dist_image 𝒜 A hA B hB C₀ hC₀_A hC₀_in_B
    ψ hψ_max hψ_dist hψC₀_in_B ρ hρ_into_B hρ_fix_B

  intro D hD_max

  rw [← hρψ_eq D hD_max]
  exact hρ_into_B (ψ D) (hψ_max D hD_max)

/-- The image of a gallery isometry $\psi$ defined on all of an apartment $A$ is contained in
some apartment $B$ of the system. -/
theorem ApartmentSystem.apt_coxeter_image_in_apartment
    {V : Type*} [DecidableEq V] {K : ChamberComplex V}
    (𝒜 : ApartmentSystem K)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (ψ : Finset V → Finset V)
    (hψ_max : ∀ C, A.IsMaximal C → K.toSimplicialComplex.IsMaximal (ψ C))
    (hψ_dist : ∀ C D, A.IsMaximal C → A.IsMaximal D →
      galleryDist K.toSimplicialComplex (ψ C) (ψ D) =
      galleryDist K.toSimplicialComplex C D) :
    ∃ B ∈ 𝒜.apartments, ∀ D, A.IsMaximal D → ψ D ∈ B.faces := by

  obtain ⟨_B_idx, _M, _cc, _hcc_eq, _φ, _hφ_inj, hφ_surj, _hφ_adj, _hcc_thin⟩ :=
    𝒜.apt_is_coxeter A hA

  obtain ⟨C₀, hC₀_max, _⟩ := hφ_surj 1

  have hψC₀_max := hψ_max C₀ hC₀_max

  have hC₀_K_max := 𝒜.maximal_in_apt_is_maximal A hA C₀ hC₀_max

  obtain ⟨B, hB, hC₀_in_B, hψC₀_in_B⟩ := 𝒜.contains_pair C₀ (ψ C₀) hC₀_K_max hψC₀_max

  exact ⟨B, hB,
    retraction_uniqueness_apartment_image 𝒜 A hA B hB C₀ hC₀_max
      hC₀_in_B ψ hψ_max hψ_dist hψC₀_in_B⟩

/-- A subset $S_1$ that lies in the image of a full-apartment gallery isometry is contained in
some apartment $B$. -/
theorem ApartmentSystem.full_apartment_image_is_apartment
    {V : Type*} [DecidableEq V] {K : ChamberComplex V}
    (𝒜 : ApartmentSystem K)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (ψ : Finset V → Finset V)
    (hψ_max : ∀ C, A.IsMaximal C → K.toSimplicialComplex.IsMaximal (ψ C))
    (hψ_dist : ∀ C D, A.IsMaximal C → A.IsMaximal D →
      galleryDist K.toSimplicialComplex (ψ C) (ψ D) =
      galleryDist K.toSimplicialComplex C D)
    (S₁ : Set (Finset V))
    (hS₁_in_image : ∀ C ∈ S₁, ∃ D, A.IsMaximal D ∧ ψ D = C) :
    ∃ B ∈ 𝒜.apartments, ∀ C ∈ S₁, C ∈ B.faces := by

  obtain ⟨B, hB, hψ_in_B⟩ := 𝒜.apt_coxeter_image_in_apartment A hA ψ hψ_max hψ_dist

  exact ⟨B, hB, fun C hC => by
    obtain ⟨D, hD_max, hψD_eq⟩ := hS₁_in_image C hC
    rw [← hψD_eq]
    exact hψ_in_B D hD_max⟩

/-- Strong isometry extension via galleries: a gallery-distance preserving map from $S_1$ into
$S_2$, where $S_2$ lies in some apartment, has its source $S_1$ also contained in an apartment. -/
theorem ApartmentSystem.strong_iso_ext_gallery {K : ChamberComplex V}
    (𝒜 : ApartmentSystem K)
    (S₁ S₂ : Set (Finset V)) (φ : Finset V → Finset V)
    (hφmem : ∀ C ∈ S₁, φ C ∈ S₂)
    (hφdist : ∀ C ∈ S₁, ∀ D ∈ S₁,
      galleryDist K.toSimplicialComplex (φ C) (φ D) =
      galleryDist K.toSimplicialComplex C D)
    (hS₂ : ∃ A ∈ 𝒜.apartments, ∀ C ∈ S₂, C ∈ A.faces) :
    ∃ B ∈ 𝒜.apartments, ∀ C ∈ S₁, C ∈ B.faces := by

  obtain ⟨A, hA, hS₂_in_A⟩ := hS₂

  have hφ_into_A : ∀ C ∈ S₁, φ C ∈ A.faces :=
    fun C hC => hS₂_in_A (φ C) (hφmem C hC)

  obtain ⟨ψ, hψ_max, hψ_dist, hψ_contains_S₁⟩ :=
    𝒜.gallery_iso_ext_to_full_apartment A hA S₁ φ hφ_into_A hφdist

  exact 𝒜.full_apartment_image_is_apartment A hA ψ hψ_max hψ_dist S₁ hψ_contains_S₁

/-- A *building* on vertex set $V$: a thick chamber complex equipped with an apartment system. -/
structure Building (V : Type*) [DecidableEq V] extends ChamberComplex V where
  apartmentSystem : ApartmentSystem toChamberComplex
  thick : toChamberComplex.IsThick
