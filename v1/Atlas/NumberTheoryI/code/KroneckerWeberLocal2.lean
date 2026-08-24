/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.Group.TypeTags.Basic
import Atlas.NumberTheoryI.code.GroupCounts

noncomputable section

namespace KroneckerWeberLocal2

class IsCyclicExtension (F : Type*) (E : Type*) [Field F] [Field E]
    [Algebra F E] : Prop where
  isGalois : IsGalois F E
  isCyclic : IsCyclic (E ≃ₐ[F] E)

def LiesInCyclotomicExtension (F : Type*) (K : Type*) [Field F] [Field K]
    [Algebra F K] : Prop :=
  ∃ (m : ℕ+), Nonempty (K →ₐ[F] CyclotomicField (m : ℕ) F)

lemma index_map_mulEquiv {G G' : Type*} [Group G] [Group G']
    (φ : G ≃* G') (H : Subgroup G) :
    (H.map φ.toMonoidHom).index = H.index := by
  apply Subgroup.index_map_eq
  · exact φ.surjective
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    have : x = 1 := φ.injective (hx.trans (map_one φ).symm)
    rw [this]; exact H.one_mem

lemma index_subgroups_card_eq_of_mulEquiv {G G' : Type*} [Group G] [Group G']
    (φ : G ≃* G') (n : ℕ) :
    Nat.card {H : Subgroup G // H.index = n} =
      Nat.card {H : Subgroup G' // H.index = n} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv φ.mapSubgroup.toEquiv ?_
  intro H
  constructor
  · intro h
    change (φ.mapSubgroup H).index = n
    rw [show (φ.mapSubgroup H) = H.map φ.toMonoidHom from rfl]
    rw [index_map_mulEquiv]; exact h
  · intro h
    have : (φ.mapSubgroup H).index = n := h
    rw [show (φ.mapSubgroup H) = H.map φ.toMonoidHom from rfl] at this
    rw [index_map_mulEquiv] at this; exact this

def galoisCorrespondenceIndex (F : Type*) [Field F] (K : Type*) [Field K]
    [Algebra F K] [FiniteDimensional F K] [IsGalois F K] (n : ℕ) :
    {H : Subgroup (K ≃ₐ[F] K) // H.index = n} ≃
    {L : IntermediateField F K // Module.finrank F L = n} where
  toFun := fun ⟨H, hH⟩ => ⟨IntermediateField.fixedField H, by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
        @IntermediateField.fixingSubgroup_fixedField F _ K _ _ H _]
    exact hH⟩
  invFun := fun ⟨L, hL⟩ => ⟨L.fixingSubgroup, by
    rwa [← IntermediateField.finrank_eq_fixingSubgroup_index]⟩
  left_inv := fun ⟨H, _⟩ => by
    simp only [Subtype.mk.injEq]
    exact @IntermediateField.fixingSubgroup_fixedField F _ K _ _ H _
  right_inv := fun ⟨L, _⟩ => by
    simp only [Subtype.mk.injEq]
    exact IsGalois.fixedField_fixingSubgroup L


theorem ps4_at_most_7_quadratic_extensions :
    ∀ (K : Type) [Field K] [Algebra ℚ_[2] K] [FiniteDimensional ℚ_[2] K],
    Nat.card {L : IntermediateField ℚ_[2] K // Module.finrank ℚ_[2] L = 2} ≤ 7 := by sorry

theorem ps4_galois_index2_bound
    (K : Type) [Field K] [Algebra ℚ_[2] K]
    [FiniteDimensional ℚ_[2] K] [IsGalois ℚ_[2] K] :
    Nat.card {H : Subgroup (K ≃ₐ[ℚ_[2]] K) // H.index = 2} ≤ 7 := by
  rw [Nat.card_congr (galoisCorrespondenceIndex ℚ_[2] K 2)]
  exact ps4_at_most_7_quadratic_extensions K

theorem Z2Z4_index2_count :
    Nat.card {H : Subgroup (Multiplicative (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)) //
      H.index = 2} = 15 :=
  GroupCounts.Z2Z4_index2_count


theorem ps5_at_most_12_cyclic_quartic_extensions :
    ∀ (K : Type) [Field K] [Algebra ℚ_[2] K] [FiniteDimensional ℚ_[2] K],
    Nat.card {L : IntermediateField ℚ_[2] K //
      Module.finrank ℚ_[2] L = 4 ∧
      IsGalois ℚ_[2] L ∧
      IsCyclic (L ≃ₐ[ℚ_[2]] L)} ≤ 12 := by sorry

theorem ps5_galois_cyclic_quartic_bound :
    ∀ (K : Type) (_ : Field K) (_ : Algebra ℚ_[2] K)
      (_ : FiniteDimensional ℚ_[2] K) (_ : IsGalois ℚ_[2] K),
    Nat.card {H : Subgroup (K ≃ₐ[ℚ_[2]] K) //
      H.index = 4 ∧ ∃ (_ : H.Normal), IsCyclic ((K ≃ₐ[ℚ_[2]] K) ⧸ H)} ≤ 12 := by
  intro K _ _ _ _
  haveI : Finite (IntermediateField ℚ_[2] K) :=
    Field.finite_intermediateField_of_exists_primitive_element ℚ_[2] K
      (Field.exists_primitive_element ℚ_[2] K)
  apply le_trans _ (ps5_at_most_12_cyclic_quartic_extensions K)
  apply Nat.card_le_card_of_injective
    (fun x => ⟨IntermediateField.fixedField x.1, by
      obtain ⟨H, hindex, hexists⟩ := x
      haveI : H.Normal := hexists.choose
      refine ⟨?_, ?_, ?_⟩
      · rw [IntermediateField.finrank_eq_fixingSubgroup_index,
            @IntermediateField.fixingSubgroup_fixedField ℚ_[2] _ K _ _ H _]
        exact hindex
      · exact IsGalois.of_fixedField_normal_subgroup H
      · exact (MulEquiv.isCyclic (IsGalois.normalAutEquivQuotient H)).mp hexists.choose_spec⟩)
  intro ⟨H1, _⟩ ⟨H2, _⟩ heq
  simp only [Subtype.mk.injEq] at heq ⊢
  have : (IntermediateField.fixedField H1).fixingSubgroup =
         (IntermediateField.fixedField H2).fixingSubgroup := by rw [heq]
  rwa [IntermediateField.fixingSubgroup_fixedField,
       IntermediateField.fixingSubgroup_fixedField] at this

theorem Z4Z3_cyclic_quartic_count :
    Nat.card {H : Subgroup (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4)) //
      H.index = 4 ∧ IsCyclic (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4) ⧸ H)} = 28 :=
  GroupCounts.Z4Z3_cyclic_quartic_count

theorem Z4Z3_cyclic_quartic_count_with_normal :
    Nat.card {H : Subgroup (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4)) //
      H.index = 4 ∧ ∃ (_ : H.Normal),
        IsCyclic (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4) ⧸ H)} = 28 := by
  rw [show (fun H : Subgroup (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4)) =>
      H.index = 4 ∧ ∃ (_ : H.Normal),
        IsCyclic (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4) ⧸ H)) =
    (fun H => H.index = 4 ∧
        IsCyclic (Multiplicative (ZMod 4 × ZMod 4 × ZMod 4) ⧸ H)) from by
    ext H; constructor
    · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, Subgroup.normal_of_comm H, h2⟩]
  exact GroupCounts.Z4Z3_cyclic_quartic_count

theorem cyclic_normal_index_subgroups_card_eq_of_mulEquiv
    {G G' : Type} [Group G] [Group G'] (φ : G ≃* G') (n : ℕ) :
    Nat.card {H : Subgroup G // H.index = n ∧ ∃ (_ : H.Normal), IsCyclic (G ⧸ H)} =
    Nat.card {H : Subgroup G' // H.index = n ∧ ∃ (_ : H.Normal), IsCyclic (G' ⧸ H)} := by
  apply Nat.card_congr
  refine Equiv.subtypeEquiv φ.mapSubgroup.toEquiv ?_
  intro H
  constructor
  · rintro ⟨h_idx, h_norm, h_cyc⟩
    have h_norm' : (φ.mapSubgroup H).Normal := by
      change (H.map φ.toMonoidHom).Normal
      exact Subgroup.Normal.map h_norm φ.toMonoidHom φ.surjective
    refine ⟨?_, h_norm', ?_⟩
    · change (H.map (φ : G →* G')).index = n
      rw [Subgroup.index_map_equiv H φ]; exact h_idx
    · haveI : (H.map φ.toMonoidHom).Normal :=
        Subgroup.Normal.map h_norm φ.toMonoidHom φ.surjective
      haveI := h_norm
      exact (QuotientGroup.congr H (H.map φ.toMonoidHom) φ rfl).isCyclic.mp h_cyc
  · rintro ⟨h_idx, h_norm, h_cyc⟩
    have h_norm' : (φ.mapSubgroup H).Normal := h_norm
    haveI : (φ.mapSubgroup.toEquiv H).Normal := h_norm
    haveI : (H.map (φ : G →* G')).Normal := ‹_›
    have h_normH : H.Normal := by
      have heq : H = (H.map (φ : G →* G')).comap (φ : G →* G') := by
        ext x; constructor
        · intro hx; exact ⟨x, hx, rfl⟩
        · rintro ⟨y, hy, he⟩; exact φ.injective he ▸ hy
      rw [heq]; exact Subgroup.Normal.comap ‹(H.map (φ : G →* G')).Normal› _
    refine ⟨?_, h_normH, ?_⟩
    · change (H.map (φ : G →* G')).index = n at h_idx
      rw [Subgroup.index_map_equiv H φ] at h_idx; exact h_idx
    · haveI := h_normH
      haveI : (H.map φ.toMonoidHom).Normal := ‹(H.map (φ : G →* G')).Normal›
      exact (QuotientGroup.congr H (H.map φ.toMonoidHom) φ rfl).isCyclic.mpr h_cyc

theorem lemma_20_11_no_Z2Z4 :
    ¬ ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ_[2] K)
      (_ : FiniteDimensional ℚ_[2] K) (_ : IsGalois ℚ_[2] K),
      Nonempty ((K ≃ₐ[ℚ_[2]] K) ≃*
        Multiplicative (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)) := by
  intro ⟨K, hK_field, hK_alg, hK_fd, hK_gal, ⟨φ⟩⟩
  have h_bound := ps4_galois_index2_bound K
  rw [index_subgroups_card_eq_of_mulEquiv φ 2, Z2Z4_index2_count] at h_bound
  omega

theorem lemma_20_11_no_Z4Z3 :
    ¬ ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ_[2] K)
      (_ : FiniteDimensional ℚ_[2] K) (_ : IsGalois ℚ_[2] K),
      Nonempty ((K ≃ₐ[ℚ_[2]] K) ≃*
        Multiplicative (ZMod 4 × ZMod 4 × ZMod 4)) := by
  intro ⟨K, hK_field, hK_alg, hK_fd, hK_gal, ⟨φ⟩⟩
  have h_bound := ps5_galois_cyclic_quartic_bound K hK_field hK_alg hK_fd hK_gal
  rw [cyclic_normal_index_subgroups_card_eq_of_mulEquiv φ,
      Z4Z3_cyclic_quartic_count_with_normal] at h_bound
  omega

theorem lemma_20_11 :
    (¬ ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ_[2] K)
      (_ : FiniteDimensional ℚ_[2] K) (_ : IsGalois ℚ_[2] K),
      Nonempty ((K ≃ₐ[ℚ_[2]] K) ≃*
        Multiplicative (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2))) ∧
    (¬ ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ_[2] K)
      (_ : FiniteDimensional ℚ_[2] K) (_ : IsGalois ℚ_[2] K),
      Nonempty ((K ≃ₐ[ℚ_[2]] K) ≃*
        Multiplicative (ZMod 4 × ZMod 4 × ZMod 4))) :=
  ⟨lemma_20_11_no_Z2Z4, lemma_20_11_no_Z4Z3⟩

theorem galois_quotient_extension.{u₁, u₂, u₃}
    (F : Type u₁) (L : Type u₂) [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] [IsGalois F L]
    (Q : Type u₃) [Group Q] [Fintype Q]
    (φ : (L ≃ₐ[F] L) →* Q) (hφ : Function.Surjective φ) :
    ∃ (E : Type u₂) (_ : Field E) (_ : Algebra F E)
      (_ : FiniteDimensional F E) (_ : IsGalois F E),
      Nonempty ((E ≃ₐ[F] E) ≃* Q) := by
  let H := φ.ker
  let E := IntermediateField.fixedField H
  haveI : Subgroup.Normal H := φ.normal_ker
  haveI : IsGalois F E := IsGalois.of_fixedField_normal_subgroup H
  have iso1 : (L ≃ₐ[F] L) ⧸ H ≃* (↥E ≃ₐ[F] ↥E) := IsGalois.normalAutEquivQuotient H
  have iso2 : (L ≃ₐ[F] L) ⧸ H ≃* Q := QuotientGroup.quotientKerEquivOfSurjective φ hφ
  exact ⟨↥E, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨iso1.symm.trans iso2⟩⟩


theorem cor_10_17_18_galois_group_structure
    (K : Type*) [Field K] [Algebra ℚ_[2] K]
    [IsCyclicExtension ℚ_[2] K] [FiniteDimensional ℚ_[2] K]
    (r : ℕ) (hdeg : Module.finrank ℚ_[2] K = 2 ^ r)
    (hnotcyc : ¬ LiesInCyclotomicExtension ℚ_[2] K) :
    (∃ (L : Type) (_ : Field L) (_ : Algebra ℚ_[2] L)
      (_ : FiniteDimensional ℚ_[2] L) (_ : IsGalois ℚ_[2] L)
      (s : ℕ) (_ : 1 ≤ s) (_ : s ≤ r),
      Nonempty ((L ≃ₐ[ℚ_[2]] L) ≃*
        Multiplicative (ZMod 2 × ZMod (2 ^ r) × ZMod (2 ^ r) × ZMod (2 ^ s)))) ∨
    (∃ (L : Type) (_ : Field L) (_ : Algebra ℚ_[2] L)
      (_ : FiniteDimensional ℚ_[2] L) (_ : IsGalois ℚ_[2] L)
      (s : ℕ) (_ : 2 ≤ s) (_ : s ≤ r),
      Nonempty ((L ≃ₐ[ℚ_[2]] L) ≃*
        Multiplicative (ZMod (2 ^ r) × ZMod (2 ^ r) × ZMod (2 ^ s)))) := by sorry

lemma surjective_toMultiplicative {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (f : A →+ B) (hf : Function.Surjective f) :
    Function.Surjective (AddMonoidHom.toMultiplicative f) := by
  intro b
  obtain ⟨a, ha⟩ := hf (Multiplicative.toAdd b)
  exact ⟨Multiplicative.ofAdd a, by simp [AddMonoidHom.toMultiplicative, ha]⟩

lemma addMonoidHom_prodMap_surjective {M N M' N' : Type*}
    [AddZeroClass M] [AddZeroClass N] [AddZeroClass M'] [AddZeroClass N']
    (f : M →+ M') (g : N →+ N')
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    Function.Surjective (AddMonoidHom.prodMap f g) := by
  intro ⟨m', n'⟩
  obtain ⟨m, hm⟩ := hf m'
  obtain ⟨n, hn⟩ := hg n'
  exact ⟨(m, n), Prod.ext (by simp [hm]) (by simp [hn])⟩

theorem cor_10_17_18_compositum_galois_surjection
    (K : Type*) [Field K] [Algebra ℚ_[2] K]
    [IsCyclicExtension ℚ_[2] K] [FiniteDimensional ℚ_[2] K]
    (r : ℕ) (hdeg : Module.finrank ℚ_[2] K = 2 ^ r)
    (hnotcyc : ¬ LiesInCyclotomicExtension ℚ_[2] K) :
    (∃ (L : Type) (_ : Field L) (_ : Algebra ℚ_[2] L)
      (_ : FiniteDimensional ℚ_[2] L) (_ : IsGalois ℚ_[2] L)
      (φ : (L ≃ₐ[ℚ_[2]] L) →*
        Multiplicative (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2)),
      Function.Surjective φ) ∨
    (∃ (L : Type) (_ : Field L) (_ : Algebra ℚ_[2] L)
      (_ : FiniteDimensional ℚ_[2] L) (_ : IsGalois ℚ_[2] L)
      (φ : (L ≃ₐ[ℚ_[2]] L) →*
        Multiplicative (ZMod 4 × ZMod 4 × ZMod 4)),
      Function.Surjective φ) := by
  obtain h | h := cor_10_17_18_galois_group_structure K r hdeg hnotcyc
  ·

    left
    obtain ⟨L, hFL, hAL, hFDL, hGL, s, hs1, hsr, ⟨iso⟩⟩ := h
    have hr2 : 2 ∣ 2 ^ r := Dvd.dvd.pow (dvd_refl 2) (by omega)
    have hs2 : 2 ∣ 2 ^ s := Dvd.dvd.pow (dvd_refl 2) (by omega)
    let castR := (ZMod.castHom hr2 (ZMod 2)).toAddMonoidHom
    let castS := (ZMod.castHom hs2 (ZMod 2)).toAddMonoidHom
    let addMap := AddMonoidHom.prodMap (AddMonoidHom.id (ZMod 2))
      (AddMonoidHom.prodMap castR (AddMonoidHom.prodMap castR castS))
    let multMap := AddMonoidHom.toMultiplicative addMap
    have hmult_surj : Function.Surjective multMap := by
      apply surjective_toMultiplicative
      apply addMonoidHom_prodMap_surjective _ _ Function.surjective_id
      apply addMonoidHom_prodMap_surjective _ _ (ZMod.ringHom_surjective _)
      exact addMonoidHom_prodMap_surjective _ _
        (ZMod.ringHom_surjective _) (ZMod.ringHom_surjective _)
    exact ⟨L, hFL, hAL, hFDL, hGL, multMap.comp iso.toMonoidHom,
           hmult_surj.comp iso.surjective⟩
  ·

    right
    obtain ⟨L, hFL, hAL, hFDL, hGL, s, hs2, hsr, ⟨iso⟩⟩ := h
    have hr4 : 4 ∣ 2 ^ r := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl]; exact Nat.pow_dvd_pow 2 (le_trans hs2 hsr)
    have hs4 : 4 ∣ 2 ^ s := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl]; exact Nat.pow_dvd_pow 2 hs2
    let castR := (ZMod.castHom hr4 (ZMod 4)).toAddMonoidHom
    let castS := (ZMod.castHom hs4 (ZMod 4)).toAddMonoidHom
    let addMap := AddMonoidHom.prodMap castR (AddMonoidHom.prodMap castR castS)
    let multMap := AddMonoidHom.toMultiplicative addMap
    have hmult_surj : Function.Surjective multMap := by
      apply surjective_toMultiplicative
      apply addMonoidHom_prodMap_surjective _ _ (ZMod.ringHom_surjective _)
      exact addMonoidHom_prodMap_surjective _ _
        (ZMod.ringHom_surjective _) (ZMod.ringHom_surjective _)
    exact ⟨L, hFL, hAL, hFDL, hGL, multMap.comp iso.toMonoidHom,
           hmult_surj.comp iso.surjective⟩

theorem theorem_20_10_contradiction_step
    (K : Type*) [Field K] [Algebra ℚ_[2] K]
    [IsCyclicExtension ℚ_[2] K] [FiniteDimensional ℚ_[2] K]
    (r : ℕ) (hdeg : Module.finrank ℚ_[2] K = 2 ^ r)
    (hnotcyc : ¬ LiesInCyclotomicExtension ℚ_[2] K) :
    (∃ (E : Type) (_ : Field E) (_ : Algebra ℚ_[2] E)
      (_ : FiniteDimensional ℚ_[2] E) (_ : IsGalois ℚ_[2] E),
      Nonempty ((E ≃ₐ[ℚ_[2]] E) ≃*
        Multiplicative (ZMod 2 × ZMod 2 × ZMod 2 × ZMod 2))) ∨
    (∃ (E : Type) (_ : Field E) (_ : Algebra ℚ_[2] E)
      (_ : FiniteDimensional ℚ_[2] E) (_ : IsGalois ℚ_[2] E),
      Nonempty ((E ≃ₐ[ℚ_[2]] E) ≃*
        Multiplicative (ZMod 4 × ZMod 4 × ZMod 4))) := by
  obtain h | h := cor_10_17_18_compositum_galois_surjection K r hdeg hnotcyc
  · left
    obtain ⟨L, hFL, hAL, hFDL, hGL, φ, hφ⟩ := h
    exact galois_quotient_extension ℚ_[2] L _ φ hφ
  · right
    obtain ⟨L, hFL, hAL, hFDL, hGL, φ, hφ⟩ := h
    exact galois_quotient_extension ℚ_[2] L _ φ hφ

theorem theorem_20_10
    (K : Type*) [Field K] [Algebra ℚ_[2] K]
    [IsCyclicExtension ℚ_[2] K] [FiniteDimensional ℚ_[2] K]
    (r : ℕ) (hdeg : Module.finrank ℚ_[2] K = 2 ^ r) :
    LiesInCyclotomicExtension ℚ_[2] K := by
  by_contra hnotcyc
  rcases theorem_20_10_contradiction_step K r hdeg hnotcyc with h | h
  · exact lemma_20_11_no_Z2Z4 h
  · exact lemma_20_11_no_Z4Z3 h

end KroneckerWeberLocal2

end
