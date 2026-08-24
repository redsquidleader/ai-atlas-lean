/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.AffineCoxeter.AffineWeylBook
import Atlas.Buildings.code.AffineCoxeter.TitsCone
import Atlas.Buildings.code.ChamberComplex.Uniqueness
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Mathlib.Data.Set.Card

set_option maxHeartbeats 800000

open scoped InnerProductSpace
open Set

noncomputable section

namespace AffineCoxeter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A map $f : E \to E'$ is a similitude with respect to distances $d_1, d_2$ if there
exists a uniform scale factor $\mu$ with $d_2(f(x), f(y)) = \mu \cdot d_1(x, y)$. -/
def IsSimilitude {E' : Type*} [NormedAddCommGroup E'] (f : E → E')
    (d₁ : E → E → ℝ) (d₂ : E' → E' → ℝ) : Prop :=
  ∃ (μ : ℝ), ∀ x y : E, d₂ (f x) (f y) = μ * d₁ x y

/-- The Euclidean distance on an inner-product space: $d(x, y) = \|x - y\|$. -/
def euclideanDist (x y : E) : ℝ := ‖x - y‖

/-- A distance function is $W$-invariant if every element of the affine reflection
group acts as an isometry. -/
def IsWInvariant (W : AffineReflectionGroup E) (d : E → E → ℝ) : Prop :=
  ∀ w ∈ W.group, ∀ x y : E, d (w x) (w y) = d x y

/-- The Euclidean distance is invariant under any affine reflection group, since each
element is an affine isometry. -/
theorem euclideanDist_isWInvariant (W : AffineReflectionGroup E) :
    IsWInvariant W euclideanDist := by
  intro w hw x y
  simp only [euclideanDist]
  have : dist (w x) (w y) = dist x y := AffineIsometryEquiv.dist_map w x y
  simp only [dist_eq_norm] at this
  exact this

/-- An isomorphism of simplicial complexes: a pair of mutually inverse morphisms
between $K$ and $L$. -/
structure SimplicialComplexIso {V W : Type*} [DecidableEq V] [DecidableEq W]
    (K : SimplicialComplex V) (L : SimplicialComplex W) where
  toMorphism : SimplicialComplex.Morphism K L
  invMorphism : SimplicialComplex.Morphism L K
  left_inv : ∀ v, invMorphism.toFun (toMorphism.toFun v) = v
  right_inv : ∀ w, toMorphism.toFun (invMorphism.toFun w) = w

/-- The structure of an abstract affine Coxeter complex in $E$: an abstract simplicial
complex on vertices $V$ with a labelling, an affine vertex map onto a spanning subset,
a chosen chamber diameter, a Coxeter matrix and normal basis with Gram matrix encoding
the local Coxeter data, and the bijection between chamber adjacencies and Coxeter exponents. -/
structure AffineCoxeterComplex (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] where
  V : Type*
  [decEq : DecidableEq V]
  W : AffineReflectionGroup E
  complex : SimplicialComplex V
  vertexMap : V → E
  affineSpan_vertexMap_eq_top : affineSpan ℝ (Set.range vertexMap) = ⊤
  chamberDiameter : ℝ
  chamberDiameter_pos : chamberDiameter > 0
  n : ℕ
  normalBasis : Module.Basis (Fin n) ℝ E
  coxeterMatrix : Fin n → Fin n → ℕ
  coxeterGram : Fin n → Fin n → ℝ
  coxeterGram_of_coxeterMatrix : ∀ i j : Fin n,
    coxeterGram i j = -Real.cos (Real.pi / (coxeterMatrix i j : ℝ))
  normalBasis_inner : ∀ i j : Fin n, @inner ℝ E _ (normalBasis i) (normalBasis j) = coxeterGram i j
  chamber_card : ∀ C, complex.IsMaximal C → C.card = n + 1
  exists_chamber : ∃ C, complex.IsMaximal C
  vertexType : V → Fin (n + 1)
  vertexType_chamber_bijective :
    ∀ (C : Finset V), complex.IsMaximal C →
      ∀ (t : Fin (n + 1)), ∃! v, v ∈ C ∧ vertexType v = t
  coxeterMatrix_eq_chamberCount :
    ∀ (C : Finset V), complex.IsMaximal C →
    ∀ i j : Fin n,
      Set.ncard {D | complex.IsMaximal D ∧
        C.filter (fun v => vertexType v ≠ i.castSucc ∧ vertexType v ≠ j.castSucc) ⊆ D} =
      2 * coxeterMatrix i j
  chamberCount_finite :
    ∀ (C : Finset V), complex.IsMaximal C →
    ∀ i j : Fin n,
      Set.Finite {D | complex.IsMaximal D ∧
        C.filter (fun v => vertexType v ≠ i.castSucc ∧ vertexType v ≠ j.castSucc) ⊆ D}
  vertex_in_chamber : ∀ v : V, ∃ C : Finset V, complex.IsMaximal C ∧ v ∈ C

attribute [instance] AffineCoxeterComplex.decEq

/-- The canonical normalised distance on an affine Coxeter complex: the Euclidean
distance scaled so that every closed chamber has diameter $1$. -/
def normalizedDist (A : AffineCoxeterComplex E) (x y : E) : ℝ :=
  euclideanDist x y / A.chamberDiameter

/-- The vertex type $V$ of an affine Coxeter complex is nonempty, since otherwise the
affine span condition forces $\mathbb{R}^0 = \top$, a contradiction. -/
theorem AffineCoxeterComplex.nonempty_V (A : AffineCoxeterComplex E) :
    Nonempty A.V := by
  by_contra hemp
  rw [not_nonempty_iff] at hemp
  have hrng : (Set.range A.vertexMap) = ∅ := by
    ext x; constructor
    · rintro ⟨v, _⟩; exact (hemp.false v).elim
    · intro h; exact h.elim
  have hspan := A.affineSpan_vertexMap_eq_top
  rw [hrng, AffineSubspace.span_empty] at hspan
  exact bot_ne_top hspan

/-- A linear map that sends one basis to another with matching Gram matrices
preserves the inner product on all of $E$. -/
theorem inner_preservation_from_gram_matching
    {n : ℕ}
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (b : Module.Basis (Fin n) ℝ E) (b' : Module.Basis (Fin n) ℝ E')
    (hgram : ∀ i j : Fin n, @inner ℝ E' _ (b' i) (b' j) = @inner ℝ E _ (b i) (b j))
    (Ψ : E →ₗ[ℝ] E')
    (hΨ : ∀ i : Fin n, Ψ (b i) = b' i) :
    ∀ x y : E, @inner ℝ E' _ (Ψ x) (Ψ y) = @inner ℝ E _ x y := by
  intro x y
  conv_lhs => rw [show x = ∑ i : Fin n, b.equivFun x i • b i from (b.sum_equivFun x).symm]
  conv_lhs => rw [show y = ∑ i : Fin n, b.equivFun y i • b i from (b.sum_equivFun y).symm]
  simp only [map_sum, map_smul, hΨ]
  simp_rw [sum_inner (𝕜 := ℝ), inner_sum (𝕜 := ℝ), inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  conv_rhs => rw [show x = ∑ i : Fin n, b.equivFun x i • b i from (b.sum_equivFun x).symm]
  conv_rhs => rw [show y = ∑ i : Fin n, b.equivFun y i • b i from (b.sum_equivFun y).symm]
  simp_rw [sum_inner (𝕜 := ℝ), inner_sum (𝕜 := ℝ), inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  congr 1; ext i; congr 1; ext j; rw [hgram]

/-- A linear map that preserves the inner product also preserves the norm. -/
theorem norm_of_inner_preserving_map
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (Ψ : E →ₗ[ℝ] E')
    (h : ∀ x y : E, @inner ℝ E' _ (Ψ x) (Ψ y) = @inner ℝ E _ x y) :
    ∀ v : E, ‖Ψ v‖ = ‖v‖ := by
  intro v
  have h1 : ‖Ψ v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq (F := E') (Ψ v)]
    rw [← real_inner_self_eq_norm_sq (F := E) v]
    exact h v v
  nlinarith [norm_nonneg (Ψ v), norm_nonneg v, sq_nonneg (‖Ψ v‖ - ‖v‖)]

/-- The forward morphism of a simplicial complex isomorphism is injective. -/
theorem SimplicialComplexIso.injective {V' W' : Type*} [DecidableEq V'] [DecidableEq W']
    {K : SimplicialComplex V'} {L : SimplicialComplex W'}
    (φ : SimplicialComplexIso K L) : Function.Injective φ.toMorphism.toFun :=
  Function.HasLeftInverse.injective ⟨φ.invMorphism.toFun, φ.left_inv⟩

/-- The inverse of a simplicial complex isomorphism, obtained by swapping forward and
backward morphisms. -/
def SimplicialComplexIso.symm {V' W' : Type*} [DecidableEq V'] [DecidableEq W']
    {K : SimplicialComplex V'} {L : SimplicialComplex W'}
    (φ : SimplicialComplexIso K L) : SimplicialComplexIso L K where
  toMorphism := φ.invMorphism
  invMorphism := φ.toMorphism
  left_inv := φ.right_inv
  right_inv := φ.left_inv

/-- Simplicial isomorphisms preserve maximal faces (chambers). -/
theorem SimplicialComplexIso.maps_maximal {V' W' : Type*} [DecidableEq V'] [DecidableEq W']
    {K : SimplicialComplex V'} {L : SimplicialComplex W'}
    (φ : SimplicialComplexIso K L) (C : Finset V') (hC : K.IsMaximal C) :
    L.IsMaximal (C.image φ.toMorphism.toFun) := by
  refine ⟨φ.toMorphism.map_face C hC.1, ?_⟩
  intro D hD hCD
  have hD_inv := φ.invMorphism.map_face D hD
  have hC_sub : C ⊆ D.image φ.invMorphism.toFun := by
    intro v hv
    have := hCD (Finset.mem_image_of_mem _ hv)
    exact Finset.mem_image.mpr ⟨φ.toMorphism.toFun v, this, φ.left_inv v⟩
  have := hC.2 _ hD_inv hC_sub
  rw [this]; ext w; simp only [Finset.mem_image]
  exact ⟨fun ⟨v, ⟨u, hu, huv⟩, hvw⟩ => by rw [← huv, φ.right_inv] at hvw; rwa [← hvw],
         fun hw => ⟨φ.invMorphism.toFun w, ⟨w, hw, rfl⟩, φ.right_inv w⟩⟩

/-- An isomorphism of affine Coxeter complexes implies their ranks (dimensions) are equal. -/
theorem coxeter_iso_dim_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (A : AffineCoxeterComplex E) (A' : AffineCoxeterComplex E')
    (φ : SimplicialComplexIso A.complex A'.complex) :
    A.n = A'.n := by
  obtain ⟨C, hC⟩ := A.exists_chamber
  have h1 := A.chamber_card C hC
  have h2 := A'.chamber_card _ (φ.maps_maximal C hC)
  have h3 := Finset.card_image_of_injective C φ.injective
  omega

/-- Gallery connectivity of an affine Coxeter complex: any two chambers are connected
by a sequence of adjacent chambers (gallery) of common-face dimension $n$. -/
theorem AffineCoxeterComplex.gallery_connected
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : AffineCoxeterComplex E)
    (C D : Finset A.V)
    (hC : A.complex.IsMaximal C) (hD : A.complex.IsMaximal D) :
    ∃ (k : ℕ) (gallery : Fin (k + 1) → Finset A.V),
      gallery ⟨0, Nat.zero_lt_succ k⟩ = C ∧
      gallery ⟨k, Nat.lt_succ_of_le le_rfl⟩ = D ∧
      (∀ i : Fin k, A.complex.IsMaximal (gallery i.castSucc)) ∧
      (A.complex.IsMaximal (gallery ⟨k, Nat.lt_succ_of_le le_rfl⟩)) ∧
      (∀ i : Fin k,
        (gallery i.castSucc ∩ gallery i.succ).card = A.n) := by sorry

/-- Existence of a chamber where two compatible labellings agree: a useful "seed" for
spreading agreement of labellings across chambers via gallery connectivity. -/
theorem AffineCoxeterComplex.labeling_agrees_on_some_chamber
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : AffineCoxeterComplex E)
    (τ : A.V → Fin (A.n + 1))
    (hτ : ∀ (C : Finset A.V), A.complex.IsMaximal C →
      ∀ (t : Fin (A.n + 1)), ∃! v, v ∈ C ∧ τ v = t) :
    ∃ (C₀ : Finset A.V), A.complex.IsMaximal C₀ ∧ ∀ v ∈ C₀, τ v = A.vertexType v := by sorry

/-- Uniqueness of the vertex type labelling: any labelling satisfying the chamber-bijection
property must agree with $A.\text{vertexType}$ on every vertex. -/
theorem vertex_type_unique
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : AffineCoxeterComplex E)
    (τ : A.V → Fin (A.n + 1))
    (hτ : ∀ (C : Finset A.V), A.complex.IsMaximal C →
      ∀ (t : Fin (A.n + 1)), ∃! v, v ∈ C ∧ τ v = t) :
    ∀ v, τ v = A.vertexType v := by
  classical

  obtain ⟨C₀, hC₀, hagree₀⟩ := A.labeling_agrees_on_some_chamber τ hτ


  have adjacency_step : ∀ (C C' : Finset A.V),
      A.complex.IsMaximal C → A.complex.IsMaximal C' →
      (C ∩ C').card = A.n →
      (∀ v ∈ C, τ v = A.vertexType v) →
      ∀ v ∈ C', τ v = A.vertexType v := by
    intro C C' hC hC' hshared hC_agree w hw

    by_cases hw_shared : w ∈ C
    · exact hC_agree w hw_shared
    ·


      set t := A.vertexType w with ht_def

      obtain ⟨u, ⟨hu_mem, hu_τ⟩, hu_uniq⟩ := hτ C' hC' t

      by_cases huw : u = w
      · rw [← huw]; exact hu_τ
      ·

        exfalso
        have hu_in_C : u ∈ C := by
          by_contra hu_not_C

          have hcard_C' := A.chamber_card C' hC'
          have hu_in_diff : u ∈ C' \ (C ∩ C') := by
            rw [Finset.mem_sdiff]
            exact ⟨hu_mem, fun h => hu_not_C (Finset.mem_inter.mp h).1⟩
          have hw_in_diff : w ∈ C' \ (C ∩ C') := by
            rw [Finset.mem_sdiff]
            exact ⟨hw, fun h => hw_shared (Finset.mem_inter.mp h).1⟩
          have hdiff_card : (C' \ (C ∩ C')).card = C'.card - ((C ∩ C') ∩ C').card :=
            Finset.card_sdiff
          have hsimp : (C ∩ C') ∩ C' = C ∩ C' :=
            Finset.inter_eq_left.mpr Finset.inter_subset_right
          rw [hsimp, hcard_C', hshared] at hdiff_card
          have : (C' \ (C ∩ C')).card = 1 := by omega
          rw [Finset.card_eq_one] at this
          obtain ⟨x, hx⟩ := this
          have : u = x := Finset.mem_singleton.mp (hx ▸ hu_in_diff)
          have : w = x := Finset.mem_singleton.mp (hx ▸ hw_in_diff)
          exact huw (by rw [‹u = x›, ‹w = x›])

        have hu_eq : τ u = A.vertexType u := hC_agree u hu_in_C


        have hvt_eq : A.vertexType u = A.vertexType w := by
          rw [← hu_eq, hu_τ]

        have hvt_uniq := (A.vertexType_chamber_bijective C' hC' t).choose_spec.2
        have : u = (A.vertexType_chamber_bijective C' hC' t).choose :=
          hvt_uniq u ⟨hu_mem, hvt_eq⟩
        have : w = (A.vertexType_chamber_bijective C' hC' t).choose :=
          hvt_uniq w ⟨hw, rfl⟩
        exact huw (by rw [‹u = _›, ‹w = _›])


  intro v
  obtain ⟨D, hD, hv⟩ := A.vertex_in_chamber v

  obtain ⟨k, gallery, hg0, hgk, hg_max, hgk_max, hg_adj⟩ :=
    A.gallery_connected C₀ D hC₀ hD

  suffices h_all : ∀ (i : Fin (k + 1)),
      A.complex.IsMaximal (gallery i) →
      ∀ w ∈ gallery i, τ w = A.vertexType w by
    have hD_is_gk : D = gallery ⟨k, Nat.lt_succ_of_le le_rfl⟩ := hgk.symm
    rw [hD_is_gk] at hv
    exact h_all ⟨k, Nat.lt_succ_of_le le_rfl⟩ hgk_max v hv
  intro i
  induction i using Fin.induction with
  | zero =>
    intro hmax w hw
    have hg0' : gallery (0 : Fin (k + 1)) = C₀ := hg0
    rw [hg0'] at hw
    exact hagree₀ w hw
  | succ j ih =>
    intro hmax_succ w hw
    have hmax_j : A.complex.IsMaximal (gallery j.castSucc) := hg_max j
    exact adjacency_step (gallery j.castSucc) (gallery j.succ)
      hmax_j hmax_succ (hg_adj j) (ih hmax_j) w hw

/-- An isomorphism of affine Coxeter complexes preserves the vertex type labelling
(up to the canonical reindexing $\text{Fin.cast}$). -/
theorem iso_preserves_vertex_type
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (A : AffineCoxeterComplex E) (A' : AffineCoxeterComplex E')
    (φ : SimplicialComplexIso A.complex A'.complex)
    (hn : A.n = A'.n) :
    ∀ v, A'.vertexType (φ.toMorphism.toFun v) = Fin.cast (by omega) (A.vertexType v) := by


  let τ : A.V → Fin (A.n + 1) := fun v =>
    Fin.cast (by omega : A'.n + 1 = A.n + 1) (A'.vertexType (φ.toMorphism.toFun v))

  have hτ_bij : ∀ (C : Finset A.V), A.complex.IsMaximal C →
      ∀ (t : Fin (A.n + 1)), ∃! v, v ∈ C ∧ τ v = t := by
    intro C hC t

    have hC' := φ.maps_maximal C hC

    let t' : Fin (A'.n + 1) := Fin.cast (by omega : A.n + 1 = A'.n + 1) t

    obtain ⟨w, ⟨hwC', hwt'⟩, hw_unique⟩ := A'.vertexType_chamber_bijective _ hC' t'

    rw [Finset.mem_image] at hwC'
    obtain ⟨v, hvC, hvw⟩ := hwC'

    refine ⟨v, ⟨hvC, ?_⟩, ?_⟩
    ·
      show Fin.cast (by omega : A'.n + 1 = A.n + 1) (A'.vertexType (φ.toMorphism.toFun v)) = t
      rw [hvw, hwt']
      ext; simp [Fin.cast, t']
    ·
      rintro v' ⟨hv'C, hv't⟩

      have hv'_type : A'.vertexType (φ.toMorphism.toFun v') = t' := by
        show A'.vertexType (φ.toMorphism.toFun v') = Fin.cast (by omega) t
        have : Fin.cast (by omega : A'.n + 1 = A.n + 1) (A'.vertexType (φ.toMorphism.toFun v')) = t := hv't
        ext
        have := congr_arg Fin.val this
        simp [Fin.cast] at this ⊢
        exact this
      have := hw_unique (φ.toMorphism.toFun v') ⟨Finset.mem_image_of_mem _ hv'C, hv'_type⟩
      rw [← hvw] at this
      exact φ.injective this

  have huniq := vertex_type_unique A τ hτ_bij

  intro v
  have hv := huniq v


  show A'.vertexType (φ.toMorphism.toFun v) = Fin.cast (by omega) (A.vertexType v)
  have : τ v = A.vertexType v := hv
  change Fin.cast (by omega : A'.n + 1 = A.n + 1) (A'.vertexType (φ.toMorphism.toFun v)) = A.vertexType v at this
  ext
  have := congr_arg Fin.val this
  simp [Fin.cast] at this ⊢
  exact this

/-- An isomorphism preserves the number of chambers containing a given face. -/
theorem iso_chamber_count_preserved
    {V' W' : Type*} [DecidableEq V'] [DecidableEq W']
    {K : SimplicialComplex V'} {L : SimplicialComplex W'}
    (φ : SimplicialComplexIso K L) (F : Finset V') :
    Set.ncard {D | L.IsMaximal D ∧ F.image φ.toMorphism.toFun ⊆ D} =
    Set.ncard {C | K.IsMaximal C ∧ F ⊆ C} := by


  suffices h : (fun C => C.image φ.toMorphism.toFun) '' {C | K.IsMaximal C ∧ F ⊆ C} =
      {D | L.IsMaximal D ∧ F.image φ.toMorphism.toFun ⊆ D} by
    rw [← h]
    exact Set.ncard_image_of_injective _ (fun _ _ h => Finset.image_injective φ.injective h)
  ext D
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, ⟨hCmax, hFC⟩, rfl⟩
    exact ⟨φ.maps_maximal C hCmax, Finset.image_subset_image hFC⟩
  · rintro ⟨hDmax, hFD⟩

    refine ⟨D.image φ.invMorphism.toFun, ⟨φ.symm.maps_maximal D hDmax, ?_⟩, ?_⟩
    ·
      intro v hv
      have hφv : φ.toMorphism.toFun v ∈ D := hFD (Finset.mem_image_of_mem _ hv)
      exact Finset.mem_image.mpr ⟨φ.toMorphism.toFun v, hφv, φ.left_inv v⟩
    ·
      rw [Finset.image_image]
      have : φ.toMorphism.toFun ∘ φ.invMorphism.toFun = id := funext φ.right_inv
      rw [this, Finset.image_id]

/-- An isomorphism of affine Coxeter complexes preserves the Coxeter matrix:
$m_{ij}$ is the same combinatorial datum on either side. -/
theorem coxeter_matrix_iso_preserved
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (A : AffineCoxeterComplex E) (A' : AffineCoxeterComplex E')
    (φ : SimplicialComplexIso A.complex A'.complex)
    (hn : A.n = A'.n) :
    ∀ i j : Fin A.n,
      A.coxeterMatrix i j = A'.coxeterMatrix (Fin.cast hn i) (Fin.cast hn j) := by
  intro i j

  obtain ⟨C, hC⟩ := A.exists_chamber

  let C' := C.image φ.toMorphism.toFun
  have hC' : A'.complex.IsMaximal C' := φ.maps_maximal C hC

  have hA := A.coxeterMatrix_eq_chamberCount C hC i j
  have hA' := A'.coxeterMatrix_eq_chamberCount C' hC' (Fin.cast hn i) (Fin.cast hn j)


  have hvt := iso_preserves_vertex_type A A' φ hn

  have hcast_i : Fin.cast (by omega : A.n + 1 = A'.n + 1) i.castSucc = (Fin.cast hn i).castSucc := by
    ext; simp [Fin.castSucc, Fin.cast]
  have hcast_j : Fin.cast (by omega : A.n + 1 = A'.n + 1) j.castSucc = (Fin.cast hn j).castSucc := by
    ext; simp [Fin.castSucc, Fin.cast]

  have hfilter_eq : C'.filter (fun w => A'.vertexType w ≠ (Fin.cast hn i).castSucc ∧
      A'.vertexType w ≠ (Fin.cast hn j).castSucc) =
    (C.filter (fun v => A.vertexType v ≠ i.castSucc ∧
      A.vertexType v ≠ j.castSucc)).image φ.toMorphism.toFun := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_image, C']
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, hw_type⟩
      refine ⟨v, ⟨hv, ?_⟩, rfl⟩
      rw [hvt v, ← hcast_i, ← hcast_j] at hw_type
      exact ⟨fun h => hw_type.1 (by rw [h]), fun h => hw_type.2 (by rw [h])⟩
    · rintro ⟨v, ⟨hv, hv_type⟩, rfl⟩
      refine ⟨⟨v, hv, rfl⟩, ?_⟩
      rw [hvt v, ← hcast_i, ← hcast_j]
      exact ⟨fun h => hv_type.1 (by exact Fin.cast_injective _ h),
             fun h => hv_type.2 (by exact Fin.cast_injective _ h)⟩

  rw [hfilter_eq] at hA'
  have hcount := iso_chamber_count_preserved φ
    (C.filter (fun v => A.vertexType v ≠ i.castSucc ∧ A.vertexType v ≠ j.castSucc))


  omega

/-- Since an isomorphism preserves the Coxeter matrix and the Gram matrix
$G_{ij} = -\cos(\pi/m_{ij})$ is determined by $m_{ij}$, isomorphic affine Coxeter
complexes have equal Gram matrices (up to the dimension reindexing). -/
theorem coxeter_iso_gram_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (A : AffineCoxeterComplex E) (A' : AffineCoxeterComplex E')
    (φ : SimplicialComplexIso A.complex A'.complex)
    (hn : A.n = A'.n) :
    ∀ i j : Fin A.n, A.coxeterGram i j = A'.coxeterGram (Fin.cast hn i) (Fin.cast hn j) := by
  intro i j

  rw [A.coxeterGram_of_coxeterMatrix i j]
  rw [A'.coxeterGram_of_coxeterMatrix (Fin.cast hn i) (Fin.cast hn j)]

  have hm := coxeter_matrix_iso_preserved A A' φ hn i j
  rw [hm]

/-- Existence half: a linear map $\Psi$ sending the normal basis of $A$ to the
normal basis of $A'$ induces some simplicial isomorphism $\Psi^*$ that, after
rescaling by the diameter ratio, agrees with $\Psi$ on vertex differences. -/
theorem psi_induces_vertex_compatible_iso
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (A : AffineCoxeterComplex E) (A' : AffineCoxeterComplex E')
    (hn : A.n = A'.n)
    (Ψ : E →ₗ[ℝ] E')
    (hΨ : ∀ i : Fin A.n, Ψ (A.normalBasis i) = A'.normalBasis (Fin.cast hn i)) :
    ∃ Ψ_star : SimplicialComplexIso A.complex A'.complex,
      ∀ u w : A.V,
        (A'.chamberDiameter / A.chamberDiameter) • Ψ (A.vertexMap u - A.vertexMap w) =
        A'.vertexMap (Ψ_star.toMorphism.toFun u) - A'.vertexMap (Ψ_star.toMorphism.toFun w) := by sorry

/-- Uniqueness half: any simplicial isomorphism $\Psi^*$ inducing the diameter-scaled
$\Psi$ on vertex differences must coincide with the given $\varphi$ on vertices. -/
theorem uniqueness_lemma_psi_star_eq_phi
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (A : AffineCoxeterComplex E) (A' : AffineCoxeterComplex E')
    (φ : SimplicialComplexIso A.complex A'.complex)
    (hn : A.n = A'.n)
    (Ψ : E →ₗ[ℝ] E')
    (hΨ : ∀ i : Fin A.n, Ψ (A.normalBasis i) = A'.normalBasis (Fin.cast hn i))
    (Ψ_star : SimplicialComplexIso A.complex A'.complex)
    (hcompat : ∀ u w : A.V,
      (A'.chamberDiameter / A.chamberDiameter) • Ψ (A.vertexMap u - A.vertexMap w) =
      A'.vertexMap (Ψ_star.toMorphism.toFun u) - A'.vertexMap (Ψ_star.toMorphism.toFun w)) :
    ∀ v : A.V, Ψ_star.toMorphism.toFun v = φ.toMorphism.toFun v := by sorry

/-- Combining existence and uniqueness: for any basis-matching $\Psi$, the diameter
ratio $A'.\mathrm{chamberDiameter} / A.\mathrm{chamberDiameter}$ times $\Psi$ acts
on vertex differences of $A$ as $\varphi$ acts on the corresponding vertices of $A'$. -/
theorem psi_scaled_compatible_on_vertex_differences
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (A : AffineCoxeterComplex E) (A' : AffineCoxeterComplex E')
    (φ : SimplicialComplexIso A.complex A'.complex)
    (hn : A.n = A'.n)
    (Ψ : E →ₗ[ℝ] E')
    (hΨ : ∀ i : Fin A.n, Ψ (A.normalBasis i) = A'.normalBasis (Fin.cast hn i)) :
    ∀ u w : A.V,
      (A'.chamberDiameter / A.chamberDiameter) • Ψ (A.vertexMap u - A.vertexMap w) =
      A'.vertexMap (φ.toMorphism.toFun u) - A'.vertexMap (φ.toMorphism.toFun w) := by

  obtain ⟨Ψ_star, hΨ_star⟩ := psi_induces_vertex_compatible_iso A A' hn Ψ hΨ

  have heq := uniqueness_lemma_psi_star_eq_phi A A' φ hn Ψ hΨ Ψ_star hΨ_star

  intro u w
  have h := hΨ_star u w
  rw [heq u, heq w] at h
  exact h

/-- Translating from vertex differences to vertices: there is a translation vector
$t \in E'$ such that the diameter-scaled $\Psi$ on vertices equals
$\varphi$ on vertices plus $t$. -/
theorem psi_scaled_agrees_with_phi_on_vertices
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (A : AffineCoxeterComplex E) (A' : AffineCoxeterComplex E')
    (φ : SimplicialComplexIso A.complex A'.complex)
    (hn : A.n = A'.n)
    (Ψ : E →ₗ[ℝ] E')
    (hΨ : ∀ i : Fin A.n, Ψ (A.normalBasis i) = A'.normalBasis (Fin.cast hn i)) :
    ∃ t : E', ∀ v : A.V,
      (A'.chamberDiameter / A.chamberDiameter) • Ψ (A.vertexMap v) =
      A'.vertexMap (φ.toMorphism.toFun v) + t := by

  have hdiff := psi_scaled_compatible_on_vertex_differences A A' φ hn Ψ hΨ

  have hne : Nonempty A.V := A.nonempty_V
  set v₀ := Classical.choice hne

  refine ⟨(A'.chamberDiameter / A.chamberDiameter) • Ψ (A.vertexMap v₀) -
    A'.vertexMap (φ.toMorphism.toFun v₀), ?_⟩

  intro v

  have h := hdiff v v₀


  rw [map_sub, smul_sub] at h


  have h1 := sub_eq_iff_eq_add.mp h
  rw [h1, sub_add_comm, add_comm]

/-- Inverse form of the vertex-difference compatibility: the unscaled $\Psi$ on
vertex differences equals $(A.\mathrm{chamberDiameter}/A'.\mathrm{chamberDiameter})$
times the image under $\varphi$. -/
theorem coxeter_iso_vertex_compat
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (A : AffineCoxeterComplex E) (A' : AffineCoxeterComplex E')
    (φ : SimplicialComplexIso A.complex A'.complex)
    (hn : A.n = A'.n)
    (Ψ : E →ₗ[ℝ] E')
    (hΨ : ∀ i : Fin A.n, Ψ (A.normalBasis i) = A'.normalBasis (Fin.cast hn i)) :
    ∀ u w : A.V,
      Ψ (A.vertexMap u - A.vertexMap w) =
      (A.chamberDiameter / A'.chamberDiameter) •
      (A'.vertexMap (φ.toMorphism.toFun u) - A'.vertexMap (φ.toMorphism.toFun w)) := by

  obtain ⟨t, ht⟩ := psi_scaled_agrees_with_phi_on_vertices A A' φ hn Ψ hΨ

  let c := A'.chamberDiameter / A.chamberDiameter
  have hc_pos : c > 0 := div_pos A'.chamberDiameter_pos A.chamberDiameter_pos
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos

  intro u w

  have hu := ht u

  have hw := ht w


  have hdiff : c • Ψ (A.vertexMap u) - c • Ψ (A.vertexMap w) =
    A'.vertexMap (φ.toMorphism.toFun u) - A'.vertexMap (φ.toMorphism.toFun w) := by
    rw [hu, hw, add_sub_add_right_eq_sub]

  rw [← smul_sub] at hdiff

  rw [map_sub]


  have hinv : (A.chamberDiameter / A'.chamberDiameter) =
    c⁻¹ := by
    simp only [c, inv_div]
  rw [hinv, eq_inv_smul_iff₀ hc_ne]
  exact hdiff

/-- Existence of a basis-and-vertex-compatible linear map: given an iso $\varphi$
of affine Coxeter complexes, there is a linear map $\Psi : E \to E'$ that maps the
normal basis of $A$ to the normal basis of $A'$, preserves the Gram matrix, and
satisfies the diameter-scaled vertex compatibility. -/
theorem coxeter_iso_basis_compatible
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (A : AffineCoxeterComplex E) (A' : AffineCoxeterComplex E')
    (φ : SimplicialComplexIso A.complex A'.complex) :
    ∃ (hn : A.n = A'.n)
      (Ψ : E →ₗ[ℝ] E'),
      (∀ i : Fin A.n, Ψ (A.normalBasis i) = A'.normalBasis (Fin.cast hn i))
      ∧ (∀ i j : Fin A.n,
          @inner ℝ E' _ (A'.normalBasis (Fin.cast hn i)) (A'.normalBasis (Fin.cast hn j)) =
          @inner ℝ E _ (A.normalBasis i) (A.normalBasis j))
      ∧ (∀ u w : A.V,
          Ψ (A.vertexMap u - A.vertexMap w) =
          (A.chamberDiameter / A'.chamberDiameter) •
          (A'.vertexMap (φ.toMorphism.toFun u) - A'.vertexMap (φ.toMorphism.toFun w))) := by

  have hn : A.n = A'.n := coxeter_iso_dim_eq A A' φ

  have hgram_cox : ∀ i j : Fin A.n,
      A.coxeterGram i j = A'.coxeterGram (Fin.cast hn i) (Fin.cast hn j) :=
    coxeter_iso_gram_eq A A' φ hn


  let b := A.normalBasis
  let b' := A'.normalBasis

  let b'r : Module.Basis (Fin A.n) ℝ E' := b'.reindex (finCongr hn).symm

  let Ψe : E ≃ₗ[ℝ] E' := b.equiv b'r (Equiv.refl _)
  let Ψ : E →ₗ[ℝ] E' := Ψe.toLinearMap

  have hΨ_basis : ∀ i : Fin A.n, Ψ (b i) = b' (Fin.cast hn i) := by
    intro i
    show Ψe (b i) = b' (Fin.cast hn i)
    simp only [Ψe, Module.Basis.equiv_apply, b'r, Module.Basis.reindex_apply,
               Equiv.refl_apply, finCongr, Equiv.symm_symm]
    rfl

  have hΨ_gram : ∀ i j : Fin A.n,
      @inner ℝ E' _ (b' (Fin.cast hn i)) (b' (Fin.cast hn j)) =
      @inner ℝ E _ (b i) (b j) := by
    intro i j
    rw [A'.normalBasis_inner, A.normalBasis_inner]
    exact (hgram_cox i j).symm

  have hΨ_vert := coxeter_iso_vertex_compat A A' φ hn Ψ hΨ_basis
  exact ⟨hn, Ψ, hΨ_basis, hΨ_gram, hΨ_vert⟩

/-- From an iso $\varphi$ one produces a scaled linear map $\Phi : E \to E'$ that
multiplies every norm by the diameter ratio $A'.\mathrm{chamberDiameter}/A.\mathrm{chamberDiameter}$
and sends vertex differences in $A$ to the corresponding vertex differences in $A'$. -/
theorem coxeter_iso_scaled_linear_map
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (A : AffineCoxeterComplex E) (A' : AffineCoxeterComplex E')
    (φ : SimplicialComplexIso A.complex A'.complex) :
    ∃ (Φ : E →ₗ[ℝ] E'),
      (∀ v : E, ‖Φ v‖ = (A'.chamberDiameter / A.chamberDiameter) * ‖v‖)
      ∧ (∀ u w : A.V,
          Φ (A.vertexMap u - A.vertexMap w) =
          A'.vertexMap (φ.toMorphism.toFun u) - A'.vertexMap (φ.toMorphism.toFun w)) := by

  obtain ⟨hn, Ψ, hΨ_basis, hΨ_gram, hΨ_vert⟩ := coxeter_iso_basis_compatible A A' φ

  have hΨ_inner : ∀ x y : E, @inner ℝ E' _ (Ψ x) (Ψ y) = @inner ℝ E _ x y := by
    exact inner_preservation_from_gram_matching A.normalBasis
      (A'.normalBasis.reindex (finCongr hn).symm)
      (by intro i j; simp [Module.Basis.reindex_apply, finCongr]; exact hΨ_gram i j)
      Ψ
      (by intro i; rw [Module.Basis.reindex_apply]; simp [finCongr]; exact hΨ_basis i)

  have hΨ_norm : ∀ v : E, ‖Ψ v‖ = ‖v‖ :=
    norm_of_inner_preserving_map Ψ hΨ_inner

  let c := A'.chamberDiameter / A.chamberDiameter
  have hc : c ≥ 0 := le_of_lt (div_pos A'.chamberDiameter_pos A.chamberDiameter_pos)
  let Φ : E →ₗ[ℝ] E' := c • Ψ
  refine ⟨Φ, ?_, ?_⟩
  ·
    intro v
    show ‖(c • Ψ) v‖ = c * ‖v‖
    simp [LinearMap.smul_apply, norm_smul, abs_of_nonneg hc, hΨ_norm]
  ·
    intro u w
    show (c • Ψ) (A.vertexMap u - A.vertexMap w) =
      A'.vertexMap (φ.toMorphism.toFun u) - A'.vertexMap (φ.toMorphism.toFun w)
    simp only [LinearMap.smul_apply, hΨ_vert u w, smul_smul]
    have : c * (A.chamberDiameter / A'.chamberDiameter) = 1 := by
      simp only [c]
      rw [div_mul_div_comm, mul_comm A'.chamberDiameter A.chamberDiameter, div_self]
      exact mul_ne_zero (ne_of_gt A.chamberDiameter_pos) (ne_of_gt A'.chamberDiameter_pos)
    rw [this, one_smul]

/-- Promoting the scaled linear map to an affine map: there exists an affine map
$g : E \to E'$ that is a similitude with factor the diameter ratio, and that
restricts to $\varphi$ on the vertices. -/
theorem coxeter_iso_induces_vertex_compatible_similitude
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (A : AffineCoxeterComplex E) (A' : AffineCoxeterComplex E')
    (φ : SimplicialComplexIso A.complex A'.complex) :
    ∃ (g : E →ᵃ[ℝ] E'),
      (∀ x y : E, euclideanDist (E := E') (g x) (g y) =
        (A'.chamberDiameter / A.chamberDiameter) * euclideanDist x y)
      ∧ (∀ v, g (A.vertexMap v) = A'.vertexMap (φ.toMorphism.toFun v)) := by

  obtain ⟨Φ, hΦ_norm, hΦ_compat⟩ := coxeter_iso_scaled_linear_map A A' φ

  have hne : Nonempty A.V := A.nonempty_V
  let v₀ := Classical.choice hne

  let b := A.vertexMap v₀
  let b' := A'.vertexMap (φ.toMorphism.toFun v₀)
  let g : E →ᵃ[ℝ] E' := AffineMap.mk' (fun x => Φ (x - b) + b') Φ b
    (by intro x; simp [vadd_eq_add, vsub_eq_sub])
  refine ⟨g, ?_, ?_⟩
  ·

    intro x y
    show euclideanDist (Φ (x - b) + b') (Φ (y - b) + b') =
      (A'.chamberDiameter / A.chamberDiameter) * euclideanDist x y
    simp only [euclideanDist, add_sub_add_right_eq_sub, ← map_sub, sub_sub_sub_cancel_right]
    exact hΦ_norm (x - y)
  ·


    intro v
    show Φ (A.vertexMap v - b) + b' = A'.vertexMap (φ.toMorphism.toFun v)
    rw [hΦ_compat v v₀]
    abel

/-- Stronger packaged form: from $\varphi$ we extract an affine similitude $g$ with
explicit similitude factor $\mu > 0$ satisfying $A'.\mathrm{chamberDiameter}
= \mu \cdot A.\mathrm{chamberDiameter}$ and $g \circ A.\mathrm{vertexMap}
= A'.\mathrm{vertexMap} \circ \varphi$. -/
theorem coxeter_iso_induces_scaled_isometry
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (A : AffineCoxeterComplex E) (A' : AffineCoxeterComplex E')
    (φ : SimplicialComplexIso A.complex A'.complex) :
    ∃ (g : E →ᵃ[ℝ] E') (μ : ℝ), μ > 0
      ∧ (∀ x y : E, euclideanDist (E := E') (g x) (g y) = μ * euclideanDist x y)
      ∧ A'.chamberDiameter = μ * A.chamberDiameter
      ∧ (∀ v, g (A.vertexMap v) = A'.vertexMap (φ.toMorphism.toFun v)) := by

  obtain ⟨g, hg_simil, hg_compat⟩ := coxeter_iso_induces_vertex_compatible_similitude A A' φ
  refine ⟨g, A'.chamberDiameter / A.chamberDiameter,
    div_pos A'.chamberDiameter_pos A.chamberDiameter_pos, hg_simil, ?_, hg_compat⟩
  rw [div_mul_cancel₀]
  exact ne_of_gt A.chamberDiameter_pos

/-- Uniqueness of the affine extension: two affine maps that agree with $\varphi$ on
the vertex set $\mathrm{range}(A.\mathrm{vertexMap})$ agree everywhere, because the
vertex set affinely spans $E$. -/
theorem vertex_compatible_map_unique
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (A : AffineCoxeterComplex E) (A' : AffineCoxeterComplex E')
    (φ : SimplicialComplexIso A.complex A'.complex)
    (f g : E →ᵃ[ℝ] E')
    (hf : ∀ v, f (A.vertexMap v) = A'.vertexMap (φ.toMorphism.toFun v))
    (hg : ∀ v, g (A.vertexMap v) = A'.vertexMap (φ.toMorphism.toFun v)) :
    f = g := by


  ext x
  have h_eqon : Set.EqOn f g (Set.range A.vertexMap) := by
    intro y hy
    obtain ⟨v, rfl⟩ := hy
    rw [hf v, hg v]
  have h_span := AffineMap.eqOn_affineSpan h_eqon
  have hx : x ∈ (affineSpan ℝ (Set.range A.vertexMap) : Set E) := by
    rw [A.affineSpan_vertexMap_eq_top]; trivial
  exact h_span hx

/-- Main quantitative form: any affine map $f$ extending $\varphi$ on the vertex set
is a similitude with factor $\mu$, where $A'.\mathrm{chamberDiameter}
= \mu \cdot A.\mathrm{chamberDiameter}$. -/
theorem simplicial_iso_is_similitude_with_diameter
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (A : AffineCoxeterComplex E) (A' : AffineCoxeterComplex E')
    (φ : SimplicialComplexIso A.complex A'.complex)
    (f : E →ᵃ[ℝ] E')
    (_hf_compat : ∀ v, f (A.vertexMap v) = A'.vertexMap (φ.toMorphism.toFun v)) :
    ∃ (μ : ℝ), μ > 0
      ∧ (∀ x y : E, euclideanDist (E := E') (f x) (f y) = μ * euclideanDist x y)
      ∧ A'.chamberDiameter = μ * A.chamberDiameter := by


  obtain ⟨g, μ, hμ_pos, hg_simil, hg_diam, hg_compat⟩ :=
    coxeter_iso_induces_scaled_isometry A A' φ

  have hfg : f = g := vertex_compatible_map_unique A A' φ f g _hf_compat hg_compat

  exact ⟨μ, hμ_pos, fun x y => by rw [hfg]; exact hg_simil x y, hg_diam⟩

/-- Qualitative form: any affine extension $f$ of $\varphi$ is a similitude with
respect to the Euclidean distances. -/
theorem simplicial_iso_is_similitude
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (A : AffineCoxeterComplex E) (A' : AffineCoxeterComplex E')
    (φ : SimplicialComplexIso A.complex A'.complex)
    (f : E →ᵃ[ℝ] E')
    (hf_compat : ∀ v, f (A.vertexMap v) = A'.vertexMap (φ.toMorphism.toFun v)) :
    IsSimilitude f euclideanDist (euclideanDist (E := E')) := by
  obtain ⟨μ, _, hf_simil, _⟩ := simplicial_iso_is_similitude_with_diameter A A' φ f hf_compat
  exact ⟨μ, hf_simil⟩

/-- The canonical distance: Euclidean distance divided by the chamber diameter, so
that each chamber has diameter exactly $1$. -/
def canonicalDist (chamberDiam : ℝ) (_hD : chamberDiam > 0) (x y : E) : ℝ :=
  euclideanDist x y / chamberDiam

/-- The Weyl-group-invariance of the Euclidean distance descends to its rescaling
$d/\mathrm{chamberDiameter}$. -/
theorem normalizedDist_isWInvariant (A : AffineCoxeterComplex E) :
    IsWInvariant A.W (normalizedDist A) := by
  intro w hw x y
  simp only [normalizedDist]
  rw [euclideanDist_isWInvariant A.W w hw x y]

/-- The canonical (chamber-diameter-normalized) metric is an isometry invariant of
the simplicial structure: any affine map $f$ extending an iso $\varphi$ preserves the
normalized Euclidean distance. This is the main result of Section 13.7. -/
theorem canonical_metric_isometry
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E']
    (A : AffineCoxeterComplex E) (A' : AffineCoxeterComplex E')
    (φ : SimplicialComplexIso A.complex A'.complex)
    (f : E →ᵃ[ℝ] E')
    (hf_compat : ∀ v, f (A.vertexMap v) = A'.vertexMap (φ.toMorphism.toFun v)) :
    ∀ x y : E, normalizedDist A' (f x) (f y) = normalizedDist A x y := by


  obtain ⟨μ, hμ_pos, hf_simil, hD_rel⟩ :=
    simplicial_iso_is_similitude_with_diameter A A' φ f hf_compat
  intro x y

  simp only [normalizedDist]

  rw [hf_simil]

  rw [hD_rel]

  have hμ_ne : (μ : ℝ) ≠ 0 := ne_of_gt hμ_pos
  have hD_ne : (A.chamberDiameter : ℝ) ≠ 0 := ne_of_gt A.chamberDiameter_pos
  field_simp

end AffineCoxeter

end
