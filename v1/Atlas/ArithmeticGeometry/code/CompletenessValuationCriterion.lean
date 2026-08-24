/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.CompleteVarieties
import Atlas.ArithmeticGeometry.code.ValuationRings
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Topology.NoetherianSpace

universe u

namespace AlgebraicGeometry.CompletenessValuationCriterion

structure AlgVariety (k : Type u) [Field k] where
  carrier : Type u
  [topInst : TopologicalSpace carrier]
  functionField : Type u
  [ffField : Field functionField]
  baseEmbed : k →+* functionField
  baseEmbed_inj : Function.Injective baseEmbed
  localRingAt : carrier → Subring functionField
  base_le_localRing : ∀ P x, baseEmbed x ∈ localRingAt P
  noethProduct : ∀ (Y : Type u) [TopologicalSpace Y] [TopologicalSpace.NoetherianSpace Y],
    TopologicalSpace.NoetherianSpace (carrier × Y)

attribute [instance] AlgVariety.topInst AlgVariety.ffField

structure SubvarietyOf {k : Type u} [Field k] (X : AlgVariety k) where
  toVariety : AlgVariety k
  inclusion : toVariety.carrier → X.carrier

structure ValRingOver {k : Type u} [Field k] (V : AlgVariety k) where
  valSub : ValuationSubring V.functionField
  contains_base : ∀ x : k, V.baseEmbed x ∈ valSub

def localRing_le {k : Type u} [Field k] {V : AlgVariety k}
    (P : V.carrier) (R : ValRingOver V) : Prop :=
  ∀ x : V.functionField, x ∈ V.localRingAt P → x ∈ R.valSub

def SatisfiesValuationCriterion {k : Type u} [Field k] (X : AlgVariety k) : Prop :=
  ∀ (Z : SubvarietyOf X) (R : ValRingOver Z.toVariety),
    ∃ P : Z.toVariety.carrier, localRing_le P R

theorem lemma_16_29 {k : Type u} [Field k] [IsAlgClosed k] {K : Type u} [Field K]
    (A : Subring K) (φ : A →+* k) :
    ∃ (B : ValuationSubring K) (_ : (A : Set K) ⊆ (B : Set K)) (Φ : B →+* k),
      (∀ (a : K) (ha : a ∈ A) (hb : a ∈ (B : Set K)), Φ ⟨a, hb⟩ = φ ⟨a, ha⟩) ∧
      (RingHom.ker Φ = IsLocalRing.maximalIdeal B) ∧
      (Function.Surjective Φ) := by sorry

lemma noetherian_finite_union_irreducible {k : Type u} [Field k]
    (X : AlgVariety k) (Y : Type u) [TopologicalSpace Y] [TopologicalSpace.NoetherianSpace Y]
    (V : Set (X.carrier × Y)) (hV : IsClosed V) :
    ∃ (n : ℕ) (components : Fin n → Set (X.carrier × Y)),
      (∀ i, IsClosed (components i)) ∧
      (∀ i, IsIrreducible (components i)) ∧
      V = ⋃ i, components i := by
  haveI := X.noethProduct Y
  obtain ⟨S, hSfin, hSclosed, hSirr, hSunion⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hV
  lift S to Finset (Set (X.carrier × Y)) using hSfin
  let e := S.equivFin
  refine ⟨S.card, fun i => (e.symm i).val, fun i => ?_, fun i => ?_, ?_⟩
  · exact hSclosed _ (Finset.coe_mem (e.symm i))
  · exact hSirr _ (Finset.coe_mem (e.symm i))
  · rw [hSunion]
    ext x
    simp only [Set.mem_sUnion, Set.mem_iUnion, Finset.mem_coe]
    constructor
    · rintro ⟨t, ht, hx⟩
      exact ⟨e ⟨t, ht⟩, by simpa [e.symm_apply_apply] using hx⟩
    · rintro ⟨i, hx⟩
      exact ⟨(e.symm i).val, Finset.coe_mem (e.symm i), hx⟩

lemma isClosed_image_finite_union {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) (n : ℕ) (components : Fin n → Set X)
    (hclosed : ∀ i, IsClosed (f '' (components i))) :
    IsClosed (f '' (⋃ i, components i)) := by
  rw [Set.image_iUnion]
  exact isClosed_iUnion_of_finite fun i => hclosed i

structure DominantProjectionData {k : Type u} [Field k]
    (X : AlgVariety k) (Y : Type u) [TopologicalSpace Y]
    (V : Set (X.carrier × Y)) where
  Z : SubvarietyOf X
  Vvar : AlgVariety k
  embed : Vvar.carrier → X.carrier × Y
  embed_mem : ∀ p, embed p ∈ V
  toZ : Vvar.carrier → Z.toVariety.carrier
  psiStar : Z.toVariety.functionField →+* Vvar.functionField
  psiStar_inj : Function.Injective psiStar
  psiStar_base_compat : ∀ x : k,
    psiStar (Z.toVariety.baseEmbed x) = Vvar.baseEmbed x

theorem exists_dominant_projection_data {k : Type u} [Field k]
    (X : AlgVariety k) (Y : Type u) [TopologicalSpace Y]
    (V : Set (X.carrier × Y)) (_hV : IsClosed V) (_hVirr : IsIrreducible V)
    (_hVne : V.Nonempty) :
    Nonempty (DominantProjectionData X Y V) := by sorry

lemma valuation_ring_pullback
    {F₁ F₂ : Type*} [Field F₁] [Field F₂]
    (ψ : F₁ →+* F₂) (_hψ : Function.Injective ψ)
    (S : ValuationSubring F₂) :
    ∃ R : ValuationSubring F₁, ∀ x : F₁, x ∈ R ↔ ψ x ∈ S := by
  exact ⟨S.comap ψ, fun x => ValuationSubring.mem_comap⟩

structure CoordRingEvalData {k : Type u} [Field k]
    {X : AlgVariety k} {Y : Type u} [TopologicalSpace Y]
    {V : Set (X.carrier × Y)}
    (dpd : DominantProjectionData X Y V) (Q : Y) where
  coordRingY : Subring dpd.Vvar.functionField
  evalAtQ : coordRingY →+* k
  base_le_coordRingY : ∀ x : k, dpd.Vvar.baseEmbed x ∈ coordRingY
  evalAtQ_fixes_base : ∀ (x : k) (hx : dpd.Vvar.baseEmbed x ∈ coordRingY),
    evalAtQ ⟨dpd.Vvar.baseEmbed x, hx⟩ = x
  psiStar_base_compat : ∀ x : k,
    dpd.psiStar (dpd.Z.toVariety.baseEmbed x) = dpd.Vvar.baseEmbed x

theorem exists_coord_ring_eval_data {k : Type u} [Field k] [IsAlgClosed k]
    {X : AlgVariety k} {Y : Type u} [TopologicalSpace Y]
    {V : Set (X.carrier × Y)}
    (dpd : DominantProjectionData X Y V) (Q : Y) :
    Nonempty (CoordRingEvalData dpd Q) := by sorry

theorem nullstellensatz_point_from_coordring {k : Type u} [Field k] [IsAlgClosed k]
    {X : AlgVariety k} {Y : Type u} [TopologicalSpace Y]
    {V : Set (X.carrier × Y)}
    (dpd : DominantProjectionData X Y V)
    (Q : Y)
    (coordRingY : Subring dpd.Vvar.functionField)
    (evalAtQ : coordRingY →+* k)
    (coordRingV : Subring dpd.Vvar.functionField)
    (hYV : (coordRingY : Set dpd.Vvar.functionField) ⊆ (coordRingV : Set dpd.Vvar.functionField))
    (S : ValuationSubring dpd.Vvar.functionField)
    (hVS : (coordRingV : Set dpd.Vvar.functionField) ⊆ (S : Set dpd.Vvar.functionField))
    (Φ : S →+* k)
    (hΦ_ext : ∀ (a : dpd.Vvar.functionField)
      (ha : a ∈ coordRingY) (hb : a ∈ (S : Set dpd.Vvar.functionField)),
      Φ ⟨a, hb⟩ = evalAtQ ⟨a, ha⟩) :
    ∃ p : dpd.Vvar.carrier, Prod.snd (dpd.embed p) = Q := by sorry

theorem coordring_contained_in_valring {k : Type u} [Field k] [IsAlgClosed k]
    {X : AlgVariety k} {Y : Type u} [TopologicalSpace Y]
    {V : Set (X.carrier × Y)}
    (dpd : DominantProjectionData X Y V)
    (coordRingY : Subring dpd.Vvar.functionField)
    (S : ValuationSubring dpd.Vvar.functionField)
    (hAS : (coordRingY : Set dpd.Vvar.functionField) ⊆ (S : Set dpd.Vvar.functionField))
    (_P₀ : dpd.Z.toVariety.carrier)
    (_hP₀ : ∀ x : dpd.Z.toVariety.functionField,
      x ∈ dpd.Z.toVariety.localRingAt _P₀ → dpd.psiStar x ∈ S) :
    ∃ (coordRingV : Subring dpd.Vvar.functionField),
      (coordRingY : Set dpd.Vvar.functionField) ⊆ (coordRingV : Set dpd.Vvar.functionField) ∧
      (coordRingV : Set dpd.Vvar.functionField) ⊆ (S : Set dpd.Vvar.functionField) :=
  ⟨coordRingY, Set.Subset.refl _, hAS⟩

theorem hilbert_nullstellensatz_variety_point {k : Type u} [Field k] [IsAlgClosed k]
    {X : AlgVariety k} {Y : Type u} [TopologicalSpace Y]
    {V : Set (X.carrier × Y)}
    (dpd : DominantProjectionData X Y V)
    (Q : Y)
    (coordRingY : Subring dpd.Vvar.functionField)
    (evalAtQ : coordRingY →+* k)
    (S : ValuationSubring dpd.Vvar.functionField)
    (hAS : (coordRingY : Set dpd.Vvar.functionField) ⊆ (S : Set dpd.Vvar.functionField))
    (Φ : S →+* k)
    (hΦ_ext : ∀ (a : dpd.Vvar.functionField)
      (ha : a ∈ coordRingY) (hb : a ∈ (S : Set dpd.Vvar.functionField)),
      Φ ⟨a, hb⟩ = evalAtQ ⟨a, ha⟩)
    (P₀ : dpd.Z.toVariety.carrier)
    (hP₀ : ∀ x : dpd.Z.toVariety.functionField,
      x ∈ dpd.Z.toVariety.localRingAt P₀ → dpd.psiStar x ∈ S) :
    ∃ p : dpd.Vvar.carrier, Prod.snd (dpd.embed p) = Q := by


  obtain ⟨coordRingV, hYV, hVS⟩ :=
    coordring_contained_in_valring dpd coordRingY S hAS P₀ hP₀


  exact nullstellensatz_point_from_coordring dpd Q coordRingY evalAtQ
    coordRingV hYV S hVS Φ hΦ_ext

theorem nullstellensatz_point_recovery {k : Type u} [Field k] [IsAlgClosed k]
    {X : AlgVariety k} {Y : Type u} [TopologicalSpace Y]
    {V : Set (X.carrier × Y)}
    (dpd : DominantProjectionData X Y V)
    (Q : Y)
    (coordRingY : Subring dpd.Vvar.functionField)
    (evalAtQ : coordRingY →+* k)
    (S : ValuationSubring dpd.Vvar.functionField)
    (hAS : (coordRingY : Set dpd.Vvar.functionField) ⊆ (S : Set dpd.Vvar.functionField))
    (Φ : S →+* k)
    (hΦ_ext : ∀ (a : dpd.Vvar.functionField)
      (ha : a ∈ coordRingY) (hb : a ∈ (S : Set dpd.Vvar.functionField)),
      Φ ⟨a, hb⟩ = evalAtQ ⟨a, ha⟩)
    (P₀ : dpd.Z.toVariety.carrier)
    (hP₀ : ∀ x : dpd.Z.toVariety.functionField,
      x ∈ dpd.Z.toVariety.localRingAt P₀ → dpd.psiStar x ∈ S) :
    ∃ P : X.carrier, (P, Q) ∈ V := by

  obtain ⟨p, hp⟩ := hilbert_nullstellensatz_variety_point dpd Q coordRingY evalAtQ S hAS Φ hΦ_ext P₀ hP₀

  refine ⟨Prod.fst (dpd.embed p), ?_⟩
  rw [← hp, Prod.eta]
  exact dpd.embed_mem p

lemma point_in_V_from_valuation_data {k : Type u} [Field k] [IsAlgClosed k]
    (X : AlgVariety k) (Y : Type u) [TopologicalSpace Y]
    (V : Set (X.carrier × Y))
    (hX : SatisfiesValuationCriterion X)
    (dpd : DominantProjectionData X Y V)
    (Q : Y) :
    ∃ P : X.carrier, (P, Q) ∈ V := by


  obtain ⟨crd⟩ := exists_coord_ring_eval_data dpd Q


  obtain ⟨S, hAS, Φ, hΦ_ext, _, _⟩ :=
    lemma_16_29 crd.coordRingY crd.evalAtQ


  obtain ⟨R, hR_mem⟩ := valuation_ring_pullback dpd.psiStar dpd.psiStar_inj S


  have hR_contains_base : ∀ x : k, dpd.Z.toVariety.baseEmbed x ∈ R := by
    intro x
    rw [hR_mem]
    rw [dpd.psiStar_base_compat]
    exact hAS (crd.base_le_coordRingY x)
  let R' : ValRingOver dpd.Z.toVariety := ⟨R, hR_contains_base⟩

  obtain ⟨P₀, hP₀⟩ := hX dpd.Z R'


  have hP₀_in_S : ∀ x : dpd.Z.toVariety.functionField,
      x ∈ dpd.Z.toVariety.localRingAt P₀ → dpd.psiStar x ∈ S := by
    intro x hx
    have := hP₀ x hx
    rwa [hR_mem] at this


  exact nullstellensatz_point_recovery dpd Q crd.coordRingY crd.evalAtQ S hAS Φ hΦ_ext P₀ hP₀_in_S

lemma irreducible_component_has_point {k : Type u} [Field k] [IsAlgClosed k]
    (X : AlgVariety k) (hX : SatisfiesValuationCriterion X)
    (Y : Type u) [TopologicalSpace Y]
    (V : Set (X.carrier × Y)) (hV : IsClosed V) (hVirr : IsIrreducible V)
    (Q : Y) (_hQ : Q ∈ closure (Prod.snd '' V)) :
    Q ∈ Prod.snd '' V := by
  rcases hVirr.nonempty with ⟨p, hp⟩
  rcases point_in_V_from_valuation_data X Y V hX
    (exists_dominant_projection_data X Y V hV hVirr ⟨p, hp⟩).some Q with ⟨P, hPQ⟩
  exact ⟨(P, Q), hPQ, rfl⟩

lemma isClosed_snd_image_of_closure_subset {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y]
    (V : Set (X × Y)) (h : closure (Prod.snd '' V) ⊆ Prod.snd '' V) :
    IsClosed (Prod.snd '' V) :=
  closure_eq_iff_isClosed.mp (Set.Subset.antisymm h subset_closure)

lemma snd_image_closed_of_valuation_criterion {k : Type u} [Field k] [IsAlgClosed k]
    (X : AlgVariety k) (hX : SatisfiesValuationCriterion X)
    (Y : Type u) [TopologicalSpace Y] [TopologicalSpace.NoetherianSpace Y]
    (V : Set (X.carrier × Y)) (hV : IsClosed V) :
    IsClosed (Prod.snd '' V) := by
  obtain ⟨n, components, hcl, hirr, hV_eq⟩ :=
    noetherian_finite_union_irreducible X Y V hV
  rw [hV_eq]
  exact isClosed_image_finite_union Prod.snd n components fun i =>
    isClosed_snd_image_of_closure_subset (components i) fun Q hQ =>
      irreducible_component_has_point X hX Y (components i) (hcl i) (hirr i) Q hQ

theorem completeness_valuation_criterion {k : Type u} [Field k] [IsAlgClosed k]
    (X : AlgVariety k) (hX : SatisfiesValuationCriterion X) :
    IsCompleteVariety X.carrier :=
  have hnoeth : TopologicalSpace.NoetherianSpace X.carrier :=
    (TopologicalSpace.noetherianSpace_iff_of_homeomorph
      (Homeomorph.prodPUnit X.carrier)).mp (X.noethProduct PUnit)
  { isVariety := hnoeth
    isClosedMap_snd := by
      intro Y _ _
      intro V hV
      exact snd_image_closed_of_valuation_criterion X hX Y V hV }

end AlgebraicGeometry.CompletenessValuationCriterion
