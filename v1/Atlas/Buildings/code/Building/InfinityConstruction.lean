/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.Infinity

set_option maxHeartbeats 3200000

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open AffineBuilding

variable {V : Type} [DecidableEq V]

namespace AffineBuilding

/-- $\sigma$ is a face of $\tau$ in $X_\infty$ iff $\sigma.\text{points} \subseteq \tau.\text{points}$. -/
def SimplexAtInfinity.IsFace (b : Building V) (md : ApartmentMetricData b)
    (σ τ : SimplexAtInfinity b md) : Prop :=
  σ.points ⊆ τ.points

/-- Reflexivity of the face relation on simplices at infinity. -/
theorem SimplexAtInfinity.IsFace.refl (b : Building V) (md : ApartmentMetricData b)
    (σ : SimplexAtInfinity b md) :
    SimplexAtInfinity.IsFace b md σ σ :=
  Set.Subset.refl _

/-- Transitivity of the face relation. -/
theorem SimplexAtInfinity.IsFace.trans {b : Building V} {md : ApartmentMetricData b}
    {σ τ ρ : SimplexAtInfinity b md}
    (h₁ : SimplexAtInfinity.IsFace b md σ τ)
    (h₂ : SimplexAtInfinity.IsFace b md τ ρ) :
    SimplexAtInfinity.IsFace b md σ ρ :=
  Set.Subset.trans h₁ h₂

/-- Antisymmetry of the face relation at the point-set level. -/
theorem SimplexAtInfinity.IsFace.antisymm_points {b : Building V} {md : ApartmentMetricData b}
    {σ τ : SimplexAtInfinity b md}
    (h₁ : SimplexAtInfinity.IsFace b md σ τ)
    (h₂ : SimplexAtInfinity.IsFace b md τ σ) :
    σ.points = τ.points :=
  Set.Subset.antisymm h₁ h₂

/-- Extensionality: simplices at infinity are equal iff their point sets coincide. -/
theorem SimplexAtInfinity.ext' {b : Building V} {md : ApartmentMetricData b}
    {σ τ : SimplexAtInfinity b md}
    (h : σ.points = τ.points) : σ = τ := by
  cases σ; cases τ; simp only [SimplexAtInfinity.mk.injEq] at h ⊢; exact h

/-- The face poset below $\sigma$ inside a chosen set $S$ of simplices at infinity. -/
def FacePoset (b : Building V) (md : ApartmentMetricData b)
    (S : Set (SimplexAtInfinity b md)) (σ : SimplexAtInfinity b md) :=
  { τ : SimplexAtInfinity b md // τ ∈ S ∧ SimplexAtInfinity.IsFace b md τ σ }

/-- Partial order on `FacePoset` induced by the face relation on simplices at infinity. -/
instance FacePoset.instPartialOrder (b : Building V) (md : ApartmentMetricData b)
    (S : Set (SimplexAtInfinity b md)) (σ : SimplexAtInfinity b md) :
    PartialOrder (FacePoset b md S σ) where
  le τ₁ τ₂ := SimplexAtInfinity.IsFace b md τ₁.val τ₂.val
  le_refl τ := SimplexAtInfinity.IsFace.refl b md τ.val
  le_trans _ _ _ h₁ h₂ := SimplexAtInfinity.IsFace.trans h₁ h₂
  le_antisymm τ₁ τ₂ h₁ h₂ :=
    Subtype.ext (SimplexAtInfinity.ext' (SimplexAtInfinity.IsFace.antisymm_points h₁ h₂))

/-- $A_\infty$: the apartment at infinity built from a Euclidean apartment $A$,
consisting of all ideal simplices arising from sectors in $A$. -/
noncomputable def apartmentBoundary (b : Building V) (_si : SectorInfrastructure b)
    (md : ApartmentMetricData b) (A : SimplicialComplex V)
    (hA : A ∈ b.apartmentSystem.apartments) : ApartmentAtInfinity b md where
  apartment := A
  apartment_mem := hA
  simplices := { σ : SimplexAtInfinity b md |
    ∃ (S : Sector b), S.apartment = A ∧ σ.points ⊆ S.pointsAtInfinity md }
  simplices_from_apartment := fun _σ ⟨S, hS_apt, _⟩ => ⟨S, hS_apt⟩

/-- The full set of ideal simplices: simplices contained in $S_\infty$ for some
sector $S$ of some apartment of $X$. -/
def allSimplicesAtInfinity (b : Building V) (_si : SectorInfrastructure b)
    (md : ApartmentMetricData b) : Set (SimplexAtInfinity b md) :=
  { σ | ∃ A ∈ b.apartmentSystem.apartments,
    ∃ (S : Sector b), S.apartment = A ∧ σ.points ⊆ S.pointsAtInfinity md }

/-- The set of apartments-at-infinity, one for each Euclidean apartment via `apartmentBoundary`. -/
def allApartmentsAtInfinity (b : Building V) (si : SectorInfrastructure b)
    (md : ApartmentMetricData b) : Set (ApartmentAtInfinity b md) :=
  { Ainf | ∃ (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments),
      Ainf = apartmentBoundary b si md A hA }

/-- Every apartment-at-infinity injects into the global simplex set and is closed
under taking faces. -/
theorem apartment_simplices_sub (b : Building V) (si : SectorInfrastructure b)
    (md : ApartmentMetricData b)
    (Ainf : ApartmentAtInfinity b md)
    (hAinf : Ainf ∈ allApartmentsAtInfinity b si md) :
    (Ainf.simplices ⊆ allSimplicesAtInfinity b si md) ∧
    (∀ (σ τ : SimplexAtInfinity b md),
      σ ∈ Ainf.simplices → SimplexAtInfinity.IsFace b md τ σ → τ ∈ Ainf.simplices) := by
  constructor
  ·
    intro σ hσ
    obtain ⟨A, hA_mem, hAinf_eq⟩ := hAinf
    subst hAinf_eq
    simp only [apartmentBoundary, Set.mem_setOf_eq] at hσ
    obtain ⟨S, hS_apt, hS_pts⟩ := hσ
    exact ⟨A, hA_mem, S, hS_apt, hS_pts⟩
  ·
    intro σ τ hσ hface
    obtain ⟨A, hA_mem, hAinf_eq⟩ := hAinf
    subst hAinf_eq
    simp only [apartmentBoundary, Set.mem_setOf_eq] at hσ ⊢
    obtain ⟨S, hS_apt, hS_pts⟩ := hσ
    exact ⟨S, hS_apt, Set.Subset.trans hface hS_pts⟩

/-- A subset of simplices at infinity is a *simplicial subcomplex* of $X_\infty$: it
is contained in the building's simplex set and closed under taking faces. -/
structure BuildingAtInfinity.IsSimplicialSubcomplex {b : Building V}
    {md : ApartmentMetricData b} (Binf : BuildingAtInfinity b md)
    (sub : Set (SimplexAtInfinity b md)) : Prop where
  subset : sub ⊆ Binf.simplices
  face_closed : ∀ (σ τ : SimplexAtInfinity b md),
    σ ∈ sub → SimplexAtInfinity.IsFace b md τ σ → τ ∈ sub

/-- **Any two ideal simplices lie in a common apartment-at-infinity** — the building
axiom (BU1) for $X_\infty$ (Section 16.9). -/
theorem any_two_simplices_common_apartment (b : Building V) (si : SectorInfrastructure b)
    (md : ApartmentMetricData b)
    (σ₁ : SimplexAtInfinity b md) (hσ₁ : σ₁ ∈ allSimplicesAtInfinity b si md)
    (σ₂ : SimplexAtInfinity b md) (hσ₂ : σ₂ ∈ allSimplicesAtInfinity b si md) :
    ∃ Ainf ∈ allApartmentsAtInfinity b si md,
      σ₁ ∈ Ainf.simplices ∧ σ₂ ∈ Ainf.simplices := by

  obtain ⟨A₁, hA₁, S₁, hS₁_apt, hS₁_pts⟩ := hσ₁
  obtain ⟨A₂, hA₂, S₂, hS₂_apt, hS₂_pts⟩ := hσ₂

  obtain ⟨A, hA_mem, hS₁_in_A, hS₂_in_A⟩ :=
    si.sectors_any_common_apartment S₁ S₂

  let S₁' : Sector b := {
    apartment := A
    apartment_mem := hA_mem
    baseVertex := S₁.baseVertex
    baseVertex_mem := hS₁_in_A S₁.baseVertex S₁.baseVertex_in_sector
    vertices := S₁.vertices
    vertices_in_apartment := fun v hv => hS₁_in_A v hv
    baseVertex_in_sector := S₁.baseVertex_in_sector
    nonempty := S₁.nonempty
  }
  let S₂' : Sector b := {
    apartment := A
    apartment_mem := hA_mem
    baseVertex := S₂.baseVertex
    baseVertex_mem := hS₂_in_A S₂.baseVertex S₂.baseVertex_in_sector
    vertices := S₂.vertices
    vertices_in_apartment := fun v hv => hS₂_in_A v hv
    baseVertex_in_sector := S₂.baseVertex_in_sector
    nonempty := S₂.nonempty
  }

  refine ⟨apartmentBoundary b si md A hA_mem,
    ⟨A, hA_mem, rfl⟩, ?_, ?_⟩
  ·
    show ∃ S : Sector b, S.apartment = A ∧ σ₁.points ⊆ Sector.pointsAtInfinity S md
    refine ⟨S₁', rfl, ?_⟩
    intro p hp
    obtain ⟨ρ, hρ_in, hρ_eq⟩ := hS₁_pts hp
    exact ⟨ρ, hρ_in, hρ_eq⟩
  ·
    show ∃ S : Sector b, S.apartment = A ∧ σ₂.points ⊆ Sector.pointsAtInfinity S md
    refine ⟨S₂', rfl, ?_⟩
    intro p hp
    obtain ⟨ρ, hρ_in, hρ_eq⟩ := hS₂_pts hp
    exact ⟨ρ, hρ_in, hρ_eq⟩

/-- Constructs the building at infinity $X_\infty$ as a `BuildingAtInfinity`, using
all ideal simplices and all apartment boundaries. -/
noncomputable def buildBoundaryComplex (b : Building V) (si : SectorInfrastructure b)
    (md : ApartmentMetricData b) :
    BuildingAtInfinity b md where
  simplices := allSimplicesAtInfinity b si md
  apartments := allApartmentsAtInfinity b si md
  apartment_simplices_mem := fun Ainf hAinf =>
    (apartment_simplices_sub b si md Ainf hAinf).1
  contains_pair := fun σ₁ hσ₁ σ₂ hσ₂ =>
    any_two_simplices_common_apartment b si md σ₁ hσ₁ σ₂ hσ₂

/-- The set $S_\infty$ of points at infinity of a sector $S$ embeds injectively
into some `Fin n`, hence is finite. -/
theorem sector_pointsAtInfinity_bounded
    {V : Type} [DecidableEq V] (b : Building V)
    (md : ApartmentMetricData b) (S : Sector b) :
    ∃ (n : ℕ) (f : ↥(S.pointsAtInfinity md) → Fin n),
      Function.Injective f := by sorry

/-- $S_\infty$ is finite as a set of points at infinity. -/
theorem sector_finite_points_at_infinity
    {V : Type} [DecidableEq V] (b : Building V)
    (md : ApartmentMetricData b) (S : Sector b) :
    Set.Finite (S.pointsAtInfinity md) := by
  obtain ⟨n, f, hf_inj⟩ := sector_pointsAtInfinity_bounded b md S
  haveI : Finite ↥(S.pointsAtInfinity md) := Finite.of_injective f hf_inj
  exact (S.pointsAtInfinity md).toFinite

/-- A subsector $T \subseteq S$ has the same set of points at infinity as $S$. -/
theorem subsector_pointsAtInfinity_eq
    {V : Type} [DecidableEq V] {b : Building V}
    (md : ApartmentMetricData b)
    (T S : Sector b)
    (h : T.vertices ⊆ S.vertices) :
    T.pointsAtInfinity md = S.pointsAtInfinity md := by sorry

/-- Sectors with identical vertex sets have identical points at infinity. -/
lemma pointsAtInfinity_eq_of_vertices_eq
    {V : Type} [DecidableEq V] {b : Building V}
    (md : ApartmentMetricData b)
    (S₁ S₂ : Sector b)
    (hv : S₁.vertices = S₂.vertices) :
    S₁.pointsAtInfinity md = S₂.pointsAtInfinity md := by
  simp only [Sector.pointsAtInfinity]
  simp_rw [hv]

/-- Sectors with the same direction have the same set of points at infinity. -/
theorem same_direction_same_pointsAtInfinity
    {V : Type} [DecidableEq V] (b : Building V)
    (md : ApartmentMetricData b)
    (S₁ S₂ : Sector b)
    (h : Sector.SameDirection b S₁ S₂) :
    S₁.pointsAtInfinity md = S₂.pointsAtInfinity md := by

  obtain ⟨T₁, T₂, hT₁_sub, hT₂_sub, hT_eq⟩ := h

  have h₁ : T₁.pointsAtInfinity md = S₁.pointsAtInfinity md :=
    subsector_pointsAtInfinity_eq md T₁ S₁ hT₁_sub

  have h₂ : T₂.pointsAtInfinity md = S₂.pointsAtInfinity md :=
    subsector_pointsAtInfinity_eq md T₂ S₂ hT₂_sub

  have h₃ : T₁.pointsAtInfinity md = T₂.pointsAtInfinity md :=
    pointsAtInfinity_eq_of_vertices_eq md T₁ T₂ hT_eq

  calc S₁.pointsAtInfinity md
      = T₁.pointsAtInfinity md := h₁.symm
    _ = T₂.pointsAtInfinity md := h₃
    _ = S₂.pointsAtInfinity md := h₂

/-- The set of sector directions arising from sectors of a fixed apartment is finite. -/
theorem apartment_sector_directions_finite
    {V : Type} [DecidableEq V] (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments) :
    Set.Finite { d : Sector.Direction b |
        ∃ (S : Sector b), S.apartment = A ∧
          d = Quot.mk (Sector.SameDirection b) S } := by sorry

/-- The set of sector directions in an apartment is in bijection with some `Fin n`. -/
theorem sector_direction_classification
    {V : Type} [DecidableEq V] (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments) :
    ∃ (n : ℕ),
      Nonempty
        ({ d : Sector.Direction b |
            ∃ (S : Sector b), S.apartment = A ∧
              d = Quot.mk (Sector.SameDirection b) S } ≃ Fin n) := by
  have hfin := apartment_sector_directions_finite b A hA
  haveI : Fintype ↥{ d : Sector.Direction b |
      ∃ (S : Sector b), S.apartment = A ∧
        d = Quot.mk (Sector.SameDirection b) S } := hfin.fintype
  exact ⟨Fintype.card _, ⟨Fintype.equivFin _⟩⟩

/-- An apartment has finitely many sector directions. -/
theorem apartment_finitely_many_sector_directions
    {V : Type} [DecidableEq V] (b : Building V)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments) :
    Set.Finite { d : Sector.Direction b |
      ∃ (S : Sector b), S.apartment = A ∧ d = Quot.mk (Sector.SameDirection b) S } := by

  obtain ⟨n, ⟨e⟩⟩ := sector_direction_classification b A hA

  haveI : Fintype ↥{ d : Sector.Direction b |
      ∃ (S : Sector b), S.apartment = A ∧ d = Quot.mk (Sector.SameDirection b) S } :=
    Fintype.ofEquiv (Fin n) e.symm
  exact Set.toFinite _

/-- The collection of distinct point-sets $S_\infty$ over sectors of an apartment is finite. -/
theorem apartment_finitely_many_sector_point_sets
    {V : Type} [DecidableEq V] (b : Building V)
    (md : ApartmentMetricData b)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments) :
    Set.Finite { T : Set (PointAtInfinity b md) |
      ∃ (S : Sector b), S.apartment = A ∧ T = S.pointsAtInfinity md } := by

  have hcompat : ∀ S₁ S₂ : Sector b,
      Sector.SameDirection b S₁ S₂ →
      S₁.pointsAtInfinity md = S₂.pointsAtInfinity md :=
    fun S₁ S₂ h => same_direction_same_pointsAtInfinity b md S₁ S₂ h

  let lift : Sector.Direction b → Set (PointAtInfinity b md) :=
    Quot.lift (fun S => S.pointsAtInfinity md) hcompat

  have hlift : ∀ S : Sector b, lift (Quot.mk _ S) = S.pointsAtInfinity md :=
    fun _ => rfl

  have hfin_dirs := apartment_finitely_many_sector_directions b A hA
  have hsub : { T : Set (PointAtInfinity b md) |
      ∃ (S : Sector b), S.apartment = A ∧ T = S.pointsAtInfinity md } ⊆
    lift '' { d : Sector.Direction b |
      ∃ (S : Sector b), S.apartment = A ∧ d = Quot.mk _ S } := by
    intro T ⟨S, hS_apt, hT⟩
    exact ⟨Quot.mk _ S, ⟨S, hS_apt, rfl⟩, by rw [hlift, hT]⟩
  exact (hfin_dirs.image lift).subset hsub

/-- The set of points at infinity lying in some sector of a fixed apartment is finite. -/
theorem apartment_finite_points_at_infinity
    {V : Type} [DecidableEq V] (b : Building V)
    (md : ApartmentMetricData b)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments) :
    Set.Finite { p : PointAtInfinity b md |
      ∃ (S : Sector b), S.apartment = A ∧ p ∈ S.pointsAtInfinity md } := by

  have hΘ := apartment_finitely_many_sector_point_sets b md A hA

  have hsub : { p : PointAtInfinity b md |
      ∃ (S : Sector b), S.apartment = A ∧ p ∈ S.pointsAtInfinity md } ⊆
    ⋃ T ∈ { T : Set (PointAtInfinity b md) |
      ∃ (S : Sector b), S.apartment = A ∧ T = S.pointsAtInfinity md }, T := by
    intro p ⟨S, hS_apt, hp⟩
    exact Set.mem_biUnion ⟨S, hS_apt, rfl⟩ hp

  have hT_finite : ∀ T ∈ { T : Set (PointAtInfinity b md) |
      ∃ (S : Sector b), S.apartment = A ∧ T = S.pointsAtInfinity md },
    Set.Finite T := by
    intro T ⟨S, _, hT⟩
    rw [hT]
    exact sector_finite_points_at_infinity b md S

  exact (Set.Finite.biUnion hΘ hT_finite).subset hsub

/-- An apartment-at-infinity has finitely many simplices (the Coxeter-complex
finiteness needed for sphericality). -/
theorem coxeter_complex_finite_simplices_for_apartment
    {V : Type} [DecidableEq V] (b : Building V)
    (si : SectorInfrastructure b) (md : ApartmentMetricData b)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments) :
    Set.Finite (apartmentBoundary b si md A hA).simplices := by

  have hfin_pts := apartment_finite_points_at_infinity b md A hA

  have hfin_subsets := hfin_pts.finite_subsets


  have hfin_pre : Set.Finite (SimplexAtInfinity.points ⁻¹'
      { s : Set (PointAtInfinity b md) | s ⊆ { p | ∃ S : Sector b,
        S.apartment = A ∧ p ∈ S.pointsAtInfinity md } }) :=
    hfin_subsets.preimage (fun σ₁ _ σ₂ _ h => SimplexAtInfinity.ext' h)

  apply hfin_pre.subset
  intro σ hσ
  simp only [apartmentBoundary, Set.mem_setOf_eq] at hσ
  obtain ⟨S, hS_apt, hS_pts⟩ := hσ


  show σ.points ⊆ { p | ∃ S : Sector b, S.apartment = A ∧ p ∈ S.pointsAtInfinity md }
  intro p hp
  exact ⟨S, hS_apt, hS_pts hp⟩

/-- Each apartment-at-infinity has finitely many simplices. -/
theorem apartment_boundary_finite
    {V : Type} [DecidableEq V] (b : Building V)
    (si : SectorInfrastructure b) (md : ApartmentMetricData b)
    (Ainf : ApartmentAtInfinity b md)
    (hAinf : Ainf ∈ allApartmentsAtInfinity b si md) :
    Set.Finite Ainf.simplices := by
  obtain ⟨A, hA_mem, hAinf_eq⟩ := hAinf
  subst hAinf_eq
  exact coxeter_complex_finite_simplices_for_apartment b si md A hA_mem

/-- **The building at infinity $X_\infty$ is spherical** — combines apartment
finiteness with nonemptiness (Section 16.10). -/
theorem buildBoundaryComplex_isSpherical (b : Building V) (si : SectorInfrastructure b)
    (md : ApartmentMetricData b)
    (h_nonempty : b.apartmentSystem.apartments.Nonempty) :
    (buildBoundaryComplex b si md).IsSpherical := by
  unfold BuildingAtInfinity.IsSpherical
  constructor
  ·
    exact fun Ainf hAinf => apartment_boundary_finite b si md Ainf hAinf
  ·
    obtain ⟨A₀, hA₀⟩ := h_nonempty
    exact ⟨apartmentBoundary b si md A₀ hA₀, ⟨A₀, hA₀, rfl⟩⟩

/-- Existence form of the previous theorem: a spherical $X_\infty$ exists. -/
theorem exists_spherical_building_at_infinity (b : Building V) (si : SectorInfrastructure b)
    (md : ApartmentMetricData b)
    (h_nonempty : b.apartmentSystem.apartments.Nonempty) :
    ∃ (Binf : BuildingAtInfinity b md), Binf.IsSpherical :=
  ⟨buildBoundaryComplex b si md,
   buildBoundaryComplex_isSpherical b si md h_nonempty⟩

/-- The face lattice below a simplex in an apartment-at-infinity is order-isomorphic
to a finite powerset $\mathcal{P}(\text{Fin}\,n)$ — the "simplicial complex" axiom. -/
def ApartmentBoundary_face_lattice_is_powerset (b : Building V)
    (si : SectorInfrastructure b) (md : ApartmentMetricData b) : Prop :=
  ∀ (Ainf : ApartmentAtInfinity b md),
    Ainf ∈ allApartmentsAtInfinity b si md →
    ∀ (σ : SimplexAtInfinity b md), σ ∈ Ainf.simplices →
    ∃ (n : ℕ),
      Nonempty (OrderIso (WithBot (FacePoset b md Ainf.simplices σ)) (Finset (Fin n)))

/-- Face completeness: every nonempty subset $T$ of the points of a simplex in
$A_\infty$ is itself realized as the point set of some simplex in $A_\infty$. -/
theorem apartmentBoundary_coxeter_face_completeness
    {V : Type} [DecidableEq V] (b : Building V)
    (si : SectorInfrastructure b) (md : ApartmentMetricData b)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (σ : SimplexAtInfinity b md)
    (hσ : σ ∈ (apartmentBoundary b si md A hA).simplices)
    (T : Set (PointAtInfinity b md))
    (hT_ne : T.Nonempty) (hT_sub : T ⊆ σ.points) :
    ∃ (τ : SimplexAtInfinity b md),
      τ ∈ (apartmentBoundary b si md A hA).simplices ∧ τ.points = T := by

  simp only [apartmentBoundary, Set.mem_setOf_eq] at hσ
  obtain ⟨S, hS_apt, hS_pts⟩ := hσ

  refine ⟨⟨T, ⟨S, hT_sub.trans hS_pts⟩, hT_ne⟩, ?_, rfl⟩

  simp only [apartmentBoundary, Set.mem_setOf_eq]
  exact ⟨S, hS_apt, hT_sub.trans hS_pts⟩

/-- Every simplex in an apartment-at-infinity has a finite point set. -/
theorem simplex_points_finite_in_boundary
    {V : Type} [DecidableEq V] (b : Building V)
    (si : SectorInfrastructure b) (md : ApartmentMetricData b)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (σ : SimplexAtInfinity b md)
    (hσ : σ ∈ (apartmentBoundary b si md A hA).simplices) :
    σ.points.Finite := by
  simp only [apartmentBoundary, Set.mem_setOf_eq] at hσ
  obtain ⟨S, _, hS_pts⟩ := hσ
  exact (sector_finite_points_at_infinity b md S).subset hS_pts

/-- Order isomorphism between $\text{WithBot}\{s : \text{Finset}(\text{Fin}\,n) // s.\text{Nonempty}\}$
and $\text{Finset}(\text{Fin}\,n)$, sending $\bot$ to $\emptyset$. -/
noncomputable def withBotNonemptyEquivFinset (n : ℕ) :
    WithBot { s : Finset (Fin n) // s.Nonempty } ≃o Finset (Fin n) where
  toFun := fun x => match x with
    | none => ∅
    | some ⟨s, _⟩ => s
  invFun := fun s => if h : s.Nonempty then some ⟨s, h⟩ else none
  left_inv := by
    rintro (_ | ⟨s, hs⟩)
    · simp only [dite_eq_right_iff]
      intro h; exact absurd h Finset.not_nonempty_empty
    · simp [hs]
  right_inv := by
    intro s
    by_cases h : s.Nonempty
    · simp [h]
    · rw [Finset.not_nonempty_iff_eq_empty] at h; simp [h]
  map_rel_iff' := by
    rintro (a | ⟨a, ha⟩) (b | ⟨b, hb⟩)
    · simp
    · exact ⟨fun _ => bot_le, fun _ => Finset.empty_subset _⟩
    · constructor
      · intro h
        change a ⊆ ∅ at h
        exact absurd (Finset.subset_empty.mp h ▸ ha) Finset.not_nonempty_empty
      · intro h; exact absurd h (WithBot.not_coe_le_bot _)
    · exact Iff.symm WithBot.coe_le_coe

/-- The face poset below $\sigma$ in $A_\infty$ is order-isomorphic to a finite powerset. -/
theorem coxeter_complex_powerset_for_apartment
    {V : Type} [DecidableEq V] (b : Building V)
    (si : SectorInfrastructure b) (md : ApartmentMetricData b)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (σ : SimplexAtInfinity b md)
    (hσ : σ ∈ (apartmentBoundary b si md A hA).simplices) :
    ∃ (n : ℕ),
      Nonempty (OrderIso
        (WithBot (FacePoset b md (apartmentBoundary b si md A hA).simplices σ))
        (Finset (Fin n))) := by
  classical

  have hfin := simplex_points_finite_in_boundary b si md A hA σ hσ

  haveI : Fintype ↥σ.points := hfin.fintype
  set n := Fintype.card ↥σ.points with hn_def
  let e : ↥σ.points ≃ Fin n := Fintype.equivFin ↥σ.points

  set S := (apartmentBoundary b si md A hA).simplices with hS_def

  have bridge := apartmentBoundary_coxeter_face_completeness b si md A hA σ hσ

  refine ⟨n, ⟨?_⟩⟩

  let fwd_fun : FacePoset b md S σ → Finset (Fin n) := fun τ =>
    (Finset.univ : Finset (Fin n)).filter (fun i => (e.symm i : PointAtInfinity b md) ∈ τ.val.points)
  have fwd_ne : ∀ τ : FacePoset b md S σ, (fwd_fun τ).Nonempty := by
    intro τ; obtain ⟨p, hp⟩ := τ.val.nonempty
    exact ⟨e ⟨p, τ.property.2 hp⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simp [hp]⟩⟩

  let pointsOf : Finset (Fin n) → Set (PointAtInfinity b md) :=
    fun s => { p | ∃ (hp : p ∈ σ.points), e ⟨p, hp⟩ ∈ s }
  have hpointsOf_ne : ∀ s, s.Nonempty → (pointsOf s).Nonempty := by
    intro s ⟨i, hi⟩
    exact ⟨(e.symm i).val, (e.symm i).property, by simp [e.apply_symm_apply i, hi]⟩
  have hpointsOf_sub : ∀ s, pointsOf s ⊆ σ.points := fun _ _ ⟨hp, _⟩ => hp

  let bwd_fun : (s : Finset (Fin n)) → s.Nonempty → FacePoset b md S σ := fun s hs =>
    let hex := bridge (pointsOf s) (hpointsOf_ne s hs) (hpointsOf_sub s)
    ⟨hex.choose, hex.choose_spec.1, by show hex.choose.points ⊆ σ.points; rw [hex.choose_spec.2]; exact hpointsOf_sub s⟩

  have bridge_spec : ∀ (s : Finset (Fin n)) (hs : s.Nonempty),
      (bwd_fun s hs).val.points = pointsOf s := by
    intro s hs
    exact (bridge (pointsOf s) (hpointsOf_ne s hs) (hpointsOf_sub s)).choose_spec.2

  have pointsOf_fwd : ∀ τ : FacePoset b md S σ, pointsOf (fwd_fun τ) = τ.val.points := by
    intro τ; ext p
    simp only [pointsOf, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and, fwd_fun]
    constructor
    · rintro ⟨hp_σ, h⟩; simpa using h
    · intro hp_τ; exact ⟨τ.property.2 hp_τ, by simpa⟩

  have fwd_bwd_val : ∀ s hs, fwd_fun (bwd_fun s hs) = s := by
    intro s hs; ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, fwd_fun]
    rw [bridge_spec s hs]
    simp only [pointsOf, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hp_σ, h_in⟩
      have : e ⟨(e.symm i : PointAtInfinity b md), hp_σ⟩ = i := by
        simp [Equiv.apply_symm_apply]
      rwa [this] at h_in
    · intro hi
      exact ⟨(e.symm i).property, by simp [e.apply_symm_apply i, hi]⟩

  let fwd : FacePoset b md S σ → { s : Finset (Fin n) // s.Nonempty } :=
    fun τ => ⟨fwd_fun τ, fwd_ne τ⟩
  let bwd : { s : Finset (Fin n) // s.Nonempty } → FacePoset b md S σ :=
    fun ⟨s, hs⟩ => bwd_fun s hs
  let equiv_ab : FacePoset b md S σ ≃ { s : Finset (Fin n) // s.Nonempty } :=
    { toFun := fwd, invFun := bwd,
      left_inv := fun τ =>
        Subtype.ext (SimplexAtInfinity.ext'
          (by rw [bridge_spec (fwd_fun τ) (fwd_ne τ), pointsOf_fwd])),
      right_inv := fun ⟨s, hs⟩ => Subtype.ext (fwd_bwd_val s hs) }

  have mono_fwd : Monotone equiv_ab := by
    intro τ₁ τ₂ (h : SimplexAtInfinity.IsFace b md τ₁.val τ₂.val)
    show fwd_fun τ₁ ⊆ fwd_fun τ₂
    intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, fwd_fun]; exact @h _
  have mono_bwd : Monotone equiv_ab.symm := by
    intro ⟨s₁, hs₁⟩ ⟨s₂, hs₂⟩ (h : s₁ ⊆ s₂)
    show SimplexAtInfinity.IsFace b md (bwd_fun s₁ hs₁).val (bwd_fun s₂ hs₂).val
    show (bwd_fun s₁ hs₁).val.points ⊆ (bwd_fun s₂ hs₂).val.points
    rw [bridge_spec s₁ hs₁, bridge_spec s₂ hs₂]
    exact fun _ ⟨hp, hs⟩ => ⟨hp, h hs⟩

  let iso_a := equiv_ab.toOrderIso mono_fwd mono_bwd


  exact (OrderIso.withBotCongr iso_a).trans (withBotNonemptyEquivFinset n)

/-- Globalized version of `coxeter_complex_powerset_for_apartment` packaged via
`ApartmentBoundary_face_lattice_is_powerset`. -/
theorem apartmentBoundary_face_lattice_is_powerset
    {V : Type} [DecidableEq V] (b : Building V)
    (si : SectorInfrastructure b) (md : ApartmentMetricData b) :
    ApartmentBoundary_face_lattice_is_powerset b si md := by
  intro Ainf hAinf σ hσ

  obtain ⟨A, hA_mem, hAinf_eq⟩ := hAinf

  subst hAinf_eq

  exact coxeter_complex_powerset_for_apartment b si md A hA_mem σ hσ

/-- Predicate: every pair of simplices in any apartment-at-infinity has a greatest
common subface — the "meet exists" axiom. -/
def ApartmentBoundary_glb_in_apartment (b : Building V)
    (si : SectorInfrastructure b) (md : ApartmentMetricData b) : Prop :=
  ∀ (Ainf : ApartmentAtInfinity b md),
    Ainf ∈ allApartmentsAtInfinity b si md →
    ∀ (σ₁ σ₂ : SimplexAtInfinity b md),
      σ₁ ∈ Ainf.simplices → σ₂ ∈ Ainf.simplices →
      ∃ (γ : SimplexAtInfinity b md), γ ∈ Ainf.simplices ∧
        SimplexAtInfinity.IsFace b md γ σ₁ ∧
        SimplexAtInfinity.IsFace b md γ σ₂ ∧
        (∀ (δ : SimplexAtInfinity b md), δ ∈ Ainf.simplices →
          SimplexAtInfinity.IsFace b md δ σ₁ →
          SimplexAtInfinity.IsFace b md δ σ₂ →
          SimplexAtInfinity.IsFace b md δ γ)

/-- Every apartment-at-infinity has a minimum simplex contained in every $S_\infty$. -/
theorem minimum_face_in_apartment
    {V : Type} [DecidableEq V] (b : Building V)
    (md : ApartmentMetricData b)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments) :
    ∃ (σ_min : SimplexAtInfinity b md),
      ∀ (S : Sector b), S.apartment = A →
        σ_min.points ⊆ S.pointsAtInfinity md ∧
        ∀ (σ : SimplexAtInfinity b md), σ.points ⊆ S.pointsAtInfinity md →
          σ_min.points ⊆ σ.points := by sorry

/-- A point-level minimum: some point at infinity belongs to every $S_\infty$ of $A$. -/
theorem spherical_coxeter_minimum_element
    {V : Type} [DecidableEq V] (b : Building V)
    (md : ApartmentMetricData b)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments) :
    ∃ (p : PointAtInfinity b md),
      ∀ (S : Sector b) (σ : SimplexAtInfinity b md),
        S.apartment = A → σ.points ⊆ S.pointsAtInfinity md → p ∈ σ.points := by

  obtain ⟨σ_min, hmin⟩ := minimum_face_in_apartment b md A hA

  obtain ⟨p, hp⟩ := σ_min.nonempty

  exact ⟨p, fun S σ hA hσ => (hmin S hA).2 σ hσ hp⟩

/-- Every simplex of $A_\infty$ contains a common minimum vertex point at infinity. -/
theorem apartmentBoundary_has_minimum_vertex
    {V : Type} [DecidableEq V] (b : Building V)
    (si : SectorInfrastructure b) (md : ApartmentMetricData b)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments) :
    ∃ (p : PointAtInfinity b md),
      ∀ (σ : SimplexAtInfinity b md),
        σ ∈ (apartmentBoundary b si md A hA).simplices → p ∈ σ.points := by

  obtain ⟨p, hp⟩ := spherical_coxeter_minimum_element b md A hA
  refine ⟨p, fun σ hσ => ?_⟩

  simp only [apartmentBoundary, Set.mem_setOf_eq] at hσ
  obtain ⟨S, hS_apt, hσ_pts⟩ := hσ

  exact hp S σ hS_apt hσ_pts

/-- Any two simplices of $A_\infty$ share at least one common point at infinity. -/
theorem coxeter_complex_common_point_for_apartment
    {V : Type} [DecidableEq V] (b : Building V)
    (si : SectorInfrastructure b) (md : ApartmentMetricData b)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (σ₁ σ₂ : SimplexAtInfinity b md)
    (hσ₁ : σ₁ ∈ (apartmentBoundary b si md A hA).simplices)
    (hσ₂ : σ₂ ∈ (apartmentBoundary b si md A hA).simplices) :
    (σ₁.points ∩ σ₂.points).Nonempty := by

  obtain ⟨p, hp⟩ := apartmentBoundary_has_minimum_vertex b si md A hA

  exact ⟨p, hp σ₁ hσ₁, hp σ₂ hσ₂⟩

/-- Apartment-level corollary: any two simplices of a generic apartment-at-infinity
share a common point. -/
theorem apartment_boundary_simplices_share_point
    {V : Type} [DecidableEq V]
    (b : Building V) (si : SectorInfrastructure b) (md : ApartmentMetricData b)
    (Ainf : ApartmentAtInfinity b md)
    (hAinf : Ainf ∈ allApartmentsAtInfinity b si md)
    (σ₁ σ₂ : SimplexAtInfinity b md)
    (hσ₁ : σ₁ ∈ Ainf.simplices) (hσ₂ : σ₂ ∈ Ainf.simplices) :
    (σ₁.points ∩ σ₂.points).Nonempty := by

  obtain ⟨A, hA_mem, hAinf_eq⟩ := hAinf

  subst hAinf_eq

  exact coxeter_complex_common_point_for_apartment b si md A hA_mem σ₁ σ₂ hσ₁ hσ₂

/-- Among all simplices of $A_\infty$ contained in a given point set $T$, there is
a maximal one (containing every other such simplex). -/
theorem apartment_boundary_maximal_face_in_set
    {V : Type} [DecidableEq V]
    (b : Building V) (si : SectorInfrastructure b) (md : ApartmentMetricData b)
    (Ainf : ApartmentAtInfinity b md)
    (hAinf : Ainf ∈ allApartmentsAtInfinity b si md)
    (T : Set (PointAtInfinity b md))
    (hT_ne : T.Nonempty)
    (hT_from_sector : ∃ (S : Sector b), S.apartment = Ainf.apartment ∧ T ⊆ S.pointsAtInfinity md)
    (σ : SimplexAtInfinity b md)
    (hσ : σ ∈ Ainf.simplices)
    (hσT : σ.points ⊆ T) :
    ∃ (γ : SimplexAtInfinity b md), γ ∈ Ainf.simplices ∧
      γ.points ⊆ T ∧
      (∀ (δ : SimplexAtInfinity b md), δ ∈ Ainf.simplices →
        δ.points ⊆ T →
        δ.points ⊆ γ.points) := by

  obtain ⟨S, hS_apt, hT_sub_S⟩ := hT_from_sector

  obtain ⟨A, hA, hAinf_eq⟩ := hAinf

  let γ : SimplexAtInfinity b md := ⟨T, ⟨S, hT_sub_S⟩, hT_ne⟩
  refine ⟨γ, ?_, fun x hx => hx, fun δ _ hδT => hδT⟩


  rw [hAinf_eq]
  simp only [apartmentBoundary, Set.mem_setOf_eq]
  have hS_apt' : S.apartment = A := by
    rw [hS_apt, hAinf_eq]; rfl
  exact ⟨S, hS_apt', hT_sub_S⟩

/-- Apartments-at-infinity admit greatest lower bounds for pairs of simplices. -/
theorem apartmentBoundary_glb_in_apartment (b : Building V)
    (si : SectorInfrastructure b) (md : ApartmentMetricData b) :
    ApartmentBoundary_glb_in_apartment b si md := by
  intro Ainf hAinf σ₁ σ₂ hσ₁ hσ₂

  obtain ⟨A, hA, hAinf_eq⟩ := hAinf
  subst hAinf_eq

  have hσ₁_sec := hσ₁
  have hσ₂_sec := hσ₂
  dsimp [apartmentBoundary] at hσ₁_sec hσ₂_sec
  obtain ⟨S₁, hS₁_apt, hS₁_pts⟩ := hσ₁_sec
  obtain ⟨S₂, _hS₂_apt, _hS₂_pts⟩ := hσ₂_sec

  have hT_ne := apartment_boundary_simplices_share_point b si md
    (apartmentBoundary b si md A hA) ⟨A, hA, rfl⟩ σ₁ σ₂ hσ₁ hσ₂

  have hT_sub_S₁ : σ₁.points ∩ σ₂.points ⊆ S₁.pointsAtInfinity md :=
    fun x hx => hS₁_pts (Set.mem_of_mem_inter_left hx)

  have hT_from_sector : ∃ (S : Sector b),
      S.apartment = (apartmentBoundary b si md A hA).apartment ∧
      σ₁.points ∩ σ₂.points ⊆ S.pointsAtInfinity md := by
    refine ⟨S₁, ?_, hT_sub_S₁⟩
    simp [apartmentBoundary]
    exact hS₁_apt


  set T := σ₁.points ∩ σ₂.points with hT_def

  have hp_exists := hT_ne
  obtain ⟨p, hp⟩ := hp_exists
  have hp₁ : p ∈ σ₁.points := hp.1
  have hp₂ : p ∈ σ₂.points := hp.2
  have hp_in_S₁ : p ∈ S₁.pointsAtInfinity md := hS₁_pts hp₁
  let σ_p : SimplexAtInfinity b md := ⟨{p}, ⟨S₁, Set.singleton_subset_iff.mpr hp_in_S₁⟩,
    Set.singleton_nonempty p⟩

  have hσ_p_mem : σ_p ∈ (apartmentBoundary b si md A hA).simplices := by
    show ∃ S : Sector b, S.apartment = A ∧ σ_p.points ⊆ S.pointsAtInfinity md
    exact ⟨S₁, hS₁_apt, Set.singleton_subset_iff.mpr hp_in_S₁⟩

  have hσ_p_sub_T : σ_p.points ⊆ T := by
    intro x hx
    simp [σ_p] at hx
    rw [hx]
    exact ⟨hp₁, hp₂⟩

  obtain ⟨γ, hγ_mem, hγ_sub_T, hγ_max⟩ := apartment_boundary_maximal_face_in_set b si md
    (apartmentBoundary b si md A hA) ⟨A, hA, rfl⟩
    T hT_ne hT_from_sector σ_p hσ_p_mem hσ_p_sub_T

  refine ⟨γ, hγ_mem, ?_, ?_, ?_⟩
  ·
    exact fun x hx => (hγ_sub_T hx).1
  ·
    exact fun x hx => (hγ_sub_T hx).2
  ·
    intro δ hδ_mem hδ_face₁ hδ_face₂
    exact hγ_max δ hδ_mem (Set.subset_inter hδ_face₁ hδ_face₂)

/-- $X_\infty$ is a *simplicial complex*: each simplex's face lattice is a powerset
and every pair of simplices has a glb (Section 16.9). -/
structure BuildingAtInfinity.IsSimplicialComplex {b : Building V}
    {md : ApartmentMetricData b} (Binf : BuildingAtInfinity b md) : Prop where
  face_lattice_powerset :
    ∀ (σ : SimplexAtInfinity b md), σ ∈ Binf.simplices →
    ∃ (n : ℕ),
      Nonempty (OrderIso (WithBot (FacePoset b md Binf.simplices σ)) (Finset (Fin n)))
  glb_exists :
    ∀ (σ₁ σ₂ : SimplexAtInfinity b md),
      σ₁ ∈ Binf.simplices → σ₂ ∈ Binf.simplices →
      ∃ (γ : SimplexAtInfinity b md), γ ∈ Binf.simplices ∧
        SimplexAtInfinity.IsFace b md γ σ₁ ∧
        SimplexAtInfinity.IsFace b md γ σ₂ ∧
        (∀ (δ : SimplexAtInfinity b md), δ ∈ Binf.simplices →
          SimplexAtInfinity.IsFace b md δ σ₁ →
          SimplexAtInfinity.IsFace b md δ σ₂ →
          SimplexAtInfinity.IsFace b md δ γ)

/-- A face of a simplex of $A_\infty$ is itself a simplex of $A_\infty$. -/
theorem face_in_apartment_boundary (b : Building V) (si : SectorInfrastructure b)
    (md : ApartmentMetricData b)
    (Ainf : ApartmentAtInfinity b md) (hAinf : Ainf ∈ allApartmentsAtInfinity b si md)
    (σ τ : SimplexAtInfinity b md)
    (hσ : σ ∈ Ainf.simplices)
    (hface : SimplexAtInfinity.IsFace b md τ σ) :
    τ ∈ Ainf.simplices := by
  obtain ⟨A, hA_mem, hAinf_eq⟩ := hAinf
  subst hAinf_eq
  simp only [apartmentBoundary, Set.mem_setOf_eq] at hσ ⊢
  obtain ⟨S, hS_apt, hS_pts⟩ := hσ
  exact ⟨S, hS_apt, Set.Subset.trans hface hS_pts⟩

/-- Each apartment-at-infinity is a simplicial subcomplex of $X_\infty$. -/
theorem apartment_is_subcomplex (b : Building V) (si : SectorInfrastructure b)
    (md : ApartmentMetricData b)
    (Ainf : ApartmentAtInfinity b md)
    (hAinf : Ainf ∈ allApartmentsAtInfinity b si md) :
    (buildBoundaryComplex b si md).IsSimplicialSubcomplex Ainf.simplices where
  subset := (apartment_simplices_sub b si md Ainf hAinf).1
  face_closed := (apartment_simplices_sub b si md Ainf hAinf).2

/-- Order isomorphism: the face poset of $\sigma$ in $X_\infty$ agrees with the
face poset in any apartment $A_\infty$ containing $\sigma$. -/
noncomputable def facePosetIsoOfApartment (b : Building V) (si : SectorInfrastructure b)
    (md : ApartmentMetricData b)
    (Ainf : ApartmentAtInfinity b md) (hAinf : Ainf ∈ allApartmentsAtInfinity b si md)
    (σ : SimplexAtInfinity b md) (hσ : σ ∈ Ainf.simplices) :
    OrderIso (FacePoset b md (allSimplicesAtInfinity b si md) σ)
             (FacePoset b md Ainf.simplices σ) where
  toFun := fun ⟨τ, hτ_bldg, hface⟩ =>
    ⟨τ, face_in_apartment_boundary b si md Ainf hAinf σ τ hσ hface, hface⟩
  invFun := fun ⟨τ, hτ_apt, hface⟩ =>
    ⟨τ, (apartment_simplices_sub b si md Ainf hAinf).1 hτ_apt, hface⟩
  left_inv := fun ⟨τ, _, _⟩ => by simp
  right_inv := fun ⟨τ, _, _⟩ => by simp
  map_rel_iff' := by
    intro ⟨τ₁, _, _⟩ ⟨τ₂, _, _⟩
    simp only [Equiv.coe_fn_mk]
    rfl

/-- Axiom SC1 for $X_\infty$: the face lattice below every simplex is a powerset. -/
theorem buildBoundaryComplex_SC1 (b : Building V) (si : SectorInfrastructure b)
    (md : ApartmentMetricData b)
    (σ : SimplexAtInfinity b md)
    (hσ : σ ∈ allSimplicesAtInfinity b si md) :
    ∃ (n : ℕ),
      Nonempty (OrderIso (WithBot (FacePoset b md (allSimplicesAtInfinity b si md) σ))
                         (Finset (Fin n))) := by
  have h_powerset := apartmentBoundary_face_lattice_is_powerset b si md

  obtain ⟨A, hA_mem, S, hS_apt, hS_pts⟩ := hσ

  have hσ_in_bdy : σ ∈ (apartmentBoundary b si md A hA_mem).simplices := by
    show ∃ S' : Sector b, S'.apartment = A ∧ σ.points ⊆ Sector.pointsAtInfinity S' md
    exact ⟨S, hS_apt, hS_pts⟩
  set Ainf := apartmentBoundary b si md A hA_mem
  have hAinf_mem : Ainf ∈ allApartmentsAtInfinity b si md :=
    ⟨A, hA_mem, rfl⟩

  obtain ⟨n, ⟨iso_apt⟩⟩ := h_powerset Ainf hAinf_mem σ hσ_in_bdy

  exact ⟨n, ⟨(OrderIso.withBotCongr
    (facePosetIsoOfApartment b si md Ainf hAinf_mem σ hσ_in_bdy)).trans iso_apt⟩⟩

/-- Axiom SC2 for $X_\infty$: every pair of simplices has a greatest lower bound. -/
theorem buildBoundaryComplex_SC2 (b : Building V) (si : SectorInfrastructure b)
    (md : ApartmentMetricData b)
    (σ₁ σ₂ : SimplexAtInfinity b md)
    (hσ₁ : σ₁ ∈ allSimplicesAtInfinity b si md)
    (hσ₂ : σ₂ ∈ allSimplicesAtInfinity b si md) :
    ∃ (γ : SimplexAtInfinity b md), γ ∈ allSimplicesAtInfinity b si md ∧
      SimplexAtInfinity.IsFace b md γ σ₁ ∧
      SimplexAtInfinity.IsFace b md γ σ₂ ∧
      (∀ (δ : SimplexAtInfinity b md), δ ∈ allSimplicesAtInfinity b si md →
        SimplexAtInfinity.IsFace b md δ σ₁ →
        SimplexAtInfinity.IsFace b md δ σ₂ →
        SimplexAtInfinity.IsFace b md δ γ) := by
  have h_glb := apartmentBoundary_glb_in_apartment b si md

  obtain ⟨Ainf, hAinf_mem, hσ₁_in, hσ₂_in⟩ :=
    any_two_simplices_common_apartment b si md σ₁ hσ₁ σ₂ hσ₂

  obtain ⟨γ, hγ_in, hγ_le_σ₁, hγ_le_σ₂, hγ_greatest⟩ :=
    h_glb Ainf hAinf_mem σ₁ σ₂ hσ₁_in hσ₂_in

  have h_sub : Ainf.simplices ⊆ allSimplicesAtInfinity b si md :=
    (apartment_simplices_sub b si md Ainf hAinf_mem).1
  refine ⟨γ, h_sub hγ_in, hγ_le_σ₁, hγ_le_σ₂, ?_⟩

  intro δ _hδ_bldg hδ_le_σ₁ hδ_le_σ₂


  have hδ_in_apt : δ ∈ Ainf.simplices :=
    face_in_apartment_boundary b si md Ainf hAinf_mem σ₁ δ hσ₁_in hδ_le_σ₁

  exact hγ_greatest δ hδ_in_apt hδ_le_σ₁ hδ_le_σ₂

/-- **$X_\infty$ is a simplicial complex** — combines SC1 and SC2. -/
theorem buildBoundaryComplex_isSimplicialComplex (b : Building V)
    (si : SectorInfrastructure b) (md : ApartmentMetricData b) :
    (buildBoundaryComplex b si md).IsSimplicialComplex where
  face_lattice_powerset := fun σ hσ =>
    buildBoundaryComplex_SC1 b si md σ hσ
  glb_exists := fun σ₁ σ₂ hσ₁ hσ₂ =>
    buildBoundaryComplex_SC2 b si md σ₁ σ₂ hσ₁ hσ₂

/-- A *spherical simplicial complex at infinity*: bundles `BuildingAtInfinity` with
proofs that it is spherical and a simplicial complex. -/
structure SphericalSimplicialComplex (b : Building V) (md : ApartmentMetricData b) where
  building : BuildingAtInfinity b md
  spherical : building.IsSpherical b md
  simplicialComplex : building.IsSimplicialComplex

/-- Bundled constructor: produces a `SphericalSimplicialComplex` from $X$, $si$, and $md$. -/
noncomputable def buildBoundarySimplicialComplex (b : Building V)
    (si : SectorInfrastructure b) (md : ApartmentMetricData b)
    (h_nonempty : b.apartmentSystem.apartments.Nonempty) :
    SphericalSimplicialComplex b md where
  building := buildBoundaryComplex b si md
  spherical := buildBoundaryComplex_isSpherical b si md h_nonempty
  simplicialComplex := buildBoundaryComplex_isSimplicialComplex b si md

end AffineBuilding
