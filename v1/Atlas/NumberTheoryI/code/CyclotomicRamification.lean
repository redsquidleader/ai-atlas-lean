/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Atlas.NumberTheoryI.code.Cor1015
import Atlas.NumberTheoryI.code.LocalExtensions
import Atlas.NumberTheoryI.code.TracePairing

noncomputable section

theorem dvr_extension_isLocalHom
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Module.Finite A B] :
    IsLocalHom (algebraMap A B) := by

  have hint : (algebraMap A B).IsIntegral := fun b => isIntegral_of_noetherian inferInstance b

  have hmax : ((IsLocalRing.maximalIdeal B).comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' (algebraMap A B) hint
      (IsLocalRing.maximalIdeal B)

  have hcomap : (IsLocalRing.maximalIdeal B).comap (algebraMap A B) = IsLocalRing.maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal hmax

  constructor
  intro a ha
  by_contra hna

  have ha_mem : a ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal]; exact mem_nonunits_iff.mpr hna
  rw [← hcomap] at ha_mem
  have hba : algebraMap A B a ∈ IsLocalRing.maximalIdeal B := Ideal.mem_comap.mp ha_mem
  exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hba)) ha

theorem dvr_extension_module_finite
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L] :
    Module.Finite A B :=
  IsIntegralClosure.finite A K L B

theorem dvr_extension_finite_and_local
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L] :
    Module.Finite A B ∧ IsLocalHom (algebraMap A B) := by
  haveI := dvr_extension_module_finite A K L B
  exact ⟨inferInstance, dvr_extension_isLocalHom A B⟩

theorem cyclotomic_monogenicity_hensel
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {m : ℕ} (_hm : 0 < m)
    {L : Type*} [Field L] [Algebra K L]
    [IsCyclotomicExtension {m} K L] [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Module.Finite A B] [IsLocalHom (algebraMap A B)]
    (ζ : B) (_hζ : IsPrimitiveRoot ζ m) :
    Algebra.adjoin A ({ζ} : Set B) = ⊤ := by


  haveI : Algebra.IsSeparable K L := IsCyclotomicExtension.isSeparable {m} K L
  haveI : NeZero m := ⟨Nat.pos_iff_ne_zero.mp _hm⟩

  apply subalgebra_eq_top_of_mod_maximal


  sorry

theorem cyclotomic_residue_field_generated
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {m : ℕ} (_hm : 0 < m)
    {L : Type*} [Field L] [Algebra K L]
    [IsCyclotomicExtension {m} K L] [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Module.Finite A B] [IsLocalHom (algebraMap A B)]
    (ζ : B) (_hζ : IsPrimitiveRoot ζ m) :
    Algebra.adjoin A
      ({(Ideal.Quotient.mkₐ A (IsLocalRing.maximalIdeal B) : B →ₐ[A] B ⧸ IsLocalRing.maximalIdeal B) ζ} :
        Set (B ⧸ IsLocalRing.maximalIdeal B)) = ⊤ := by

  have hadj : Algebra.adjoin A ({ζ} : Set B) = ⊤ :=
    cyclotomic_monogenicity_hensel (A := A) (K := K) (L := L) _hm ζ _hζ

  set φ : B →ₐ[A] B ⧸ IsLocalRing.maximalIdeal B := Ideal.Quotient.mkₐ A _
  have h1 : Subalgebra.map φ (Algebra.adjoin A ({ζ} : Set B)) =
      Algebra.adjoin A ({φ ζ} : Set (B ⧸ IsLocalRing.maximalIdeal B)) :=
    AlgHom.map_adjoin_singleton φ ζ
  rw [hadj, Algebra.map_top] at h1
  rw [← h1]
  exact (AlgHom.range_eq_top φ).mpr (Ideal.Quotient.mkₐ_surjective A _)

theorem cyclotomic_lifting_mod_maxideal_B
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {m : ℕ} (_hm : 0 < m)
    {L : Type*} [Field L] [Algebra K L]
    [IsCyclotomicExtension {m} K L] [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Module.Finite A B]
    (ζ : B) (_hζ : IsPrimitiveRoot ζ m)
    (b : B) :
    ∃ s : B, s ∈ (Algebra.adjoin A ({ζ} : Set B)).toSubmodule ∧
      b - s ∈ IsLocalRing.maximalIdeal B := by

  haveI : IsLocalHom (algebraMap A B) := dvr_extension_isLocalHom A B

  set φ : B →ₐ[A] B ⧸ IsLocalRing.maximalIdeal B :=
    Ideal.Quotient.mkₐ A (IsLocalRing.maximalIdeal B)

  have htop := cyclotomic_residue_field_generated (A := A) (K := K) (L := L) _hm ζ _hζ
  have himage : Subalgebra.map φ (Algebra.adjoin A ({ζ} : Set B)) = ⊤ := by
    rw [AlgHom.map_adjoin_singleton, htop]

  have hb_im : φ b ∈ Subalgebra.map φ (Algebra.adjoin A ({ζ} : Set B)) := by
    rw [himage]; trivial
  obtain ⟨s, hs, hφs⟩ := hb_im
  exact ⟨s, hs, by rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]; exact hφs.symm⟩

theorem cyclotomic_uniformizer_in_adjoin
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {m : ℕ} (_hm : 0 < m)
    {L : Type*} [Field L] [Algebra K L]
    [IsCyclotomicExtension {m} K L] [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Module.Finite A B]
    (ζ : B) (_hζ : IsPrimitiveRoot ζ m) :
    ∃ π : B, π ∈ Algebra.adjoin A ({ζ} : Set B) ∧ Irreducible π := by

  haveI : IsLocalHom (algebraMap A B) := dvr_extension_isLocalHom A B

  have hadj : Algebra.adjoin A ({ζ} : Set B) = ⊤ :=
    cyclotomic_monogenicity_hensel (A := A) (K := K) (L := L) _hm ζ _hζ

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B

  exact ⟨π, hadj ▸ Algebra.mem_top, hπ⟩

theorem cyclotomic_root_spans_mod_maximal
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (m : ℕ) (_hm : 0 < m)
    (L : Type*) [Field L] [Algebra K L]
    [IsCyclotomicExtension {m} K L] [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Module.Finite A B]
    (ζ : B) (_hζ : IsPrimitiveRoot ζ m) :
    (⊤ : Submodule A B) ≤
      (Algebra.adjoin A ({ζ} : Set B)).toSubmodule ⊔
        (IsLocalRing.maximalIdeal A) • ⊤ := by
  set S := Algebra.adjoin A ({ζ} : Set B)
  set n := Module.finrank K L
  set e := (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B)

  obtain ⟨π, hπ_mem, hπ_irr⟩ := cyclotomic_uniformizer_in_adjoin
    (A := A) (K := K) (m := m) (L := L) (B := B) _hm ζ _hζ

  have hlift : ∀ b : B, ∃ s : B, s ∈ S.toSubmodule ∧
      b - s ∈ IsLocalRing.maximalIdeal B :=
    fun b => cyclotomic_lifting_mod_maxideal_B
      (A := A) (K := K) (m := m) (L := L) (B := B) _hm ζ _hζ b

  have hπ_span : IsLocalRing.maximalIdeal B = Ideal.span {π} := hπ_irr.maximalIdeal_eq

  have span_pow_eq : ∀ k : ℕ, (IsLocalRing.maximalIdeal B) ^ k = Ideal.span {π ^ k} := by
    intro k; rw [hπ_span, Ideal.span_singleton_pow]

  have hind_step : ∀ k : ℕ,
      (((IsLocalRing.maximalIdeal B) ^ k).restrictScalars A : Submodule A B) ≤
      S.toSubmodule ⊔ ((IsLocalRing.maximalIdeal B) ^ (k + 1)).restrictScalars A := by
    intro k x hx
    simp only [Submodule.restrictScalars_mem] at hx
    rw [span_pow_eq k, Ideal.mem_span_singleton'] at hx
    obtain ⟨c, hc⟩ := hx
    obtain ⟨s, hs_mem, hs_diff⟩ := hlift c
    have hxdecomp : x = s * π ^ k + (c - s) * π ^ k := by
      rw [← add_mul, add_sub_cancel, hc]
    rw [hxdecomp]
    apply Submodule.add_mem_sup
    ·
      exact S.mem_toSubmodule.mpr
        (Subalgebra.mul_mem S (S.mem_toSubmodule.mp hs_mem)
          (Subalgebra.pow_mem S hπ_mem k))
    ·
      show (c - s) * π ^ k ∈
        ((IsLocalRing.maximalIdeal B) ^ (k + 1)).restrictScalars A
      simp only [Submodule.restrictScalars_mem]
      have hd : c - s ∈ IsLocalRing.maximalIdeal B := hs_diff
      have hpk : π ^ k ∈ (IsLocalRing.maximalIdeal B) ^ k := by
        rw [span_pow_eq k]; exact Ideal.mem_span_singleton_self _
      rw [pow_succ]
      exact mul_comm (c - s) (π ^ k) ▸ Ideal.mul_mem_mul hpk hd

  have hiter : ∀ b : B,
      b ∈ S.toSubmodule ⊔ ((IsLocalRing.maximalIdeal B) ^ n).restrictScalars A := by
    intro b
    suffices h : ∀ k : ℕ, b ∈ S.toSubmodule ⊔
        ((IsLocalRing.maximalIdeal B) ^ k).restrictScalars A from h n
    intro k
    induction k with
    | zero =>
      have : b ∈ ((IsLocalRing.maximalIdeal B) ^ 0).restrictScalars A := by simp
      exact Submodule.mem_sup_right this
    | succ k ih =>
      have hle : S.toSubmodule ⊔ ((IsLocalRing.maximalIdeal B) ^ k).restrictScalars A ≤
          S.toSubmodule ⊔ ((IsLocalRing.maximalIdeal B) ^ (k + 1)).restrictScalars A :=
        (sup_le_sup_left (hind_step k) S.toSubmodule).trans
          (by rw [← sup_assoc, sup_idem])
      exact hle ih


  have hmap_eq : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      (IsLocalRing.maximalIdeal B) ^ e := by
    set I := Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)
    have hinj_AL : Function.Injective (algebraMap A L) := by
      rw [IsScalarTower.algebraMap_eq A K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
    have hinj : Function.Injective (algebraMap A B) := by
      rw [IsScalarTower.algebraMap_eq A B L] at hinj_AL
      exact Function.Injective.of_comp hinj_AL
    have hIne : I ≠ ⊥ := by
      intro h
      have : IsLocalRing.maximalIdeal A = ⊥ := by
        rw [Ideal.map_eq_bot_iff_le_ker] at h
        have hker : RingHom.ker (algebraMap A B) = ⊥ :=
          (RingHom.injective_iff_ker_eq_bot _).mp hinj
        rw [hker] at h
        exact le_bot_iff.mp h
      exact IsDiscreteValuationRing.not_a_field A this
    obtain ⟨m, hm⟩ := exists_maximalIdeal_pow_eq_of_principal B
      (IsPrincipalIdealRing.principal _) I hIne
    have hgt : ¬(I ≤ (IsLocalRing.maximalIdeal B) ^ (m + 1)) := by
      intro hle
      have hle' : (IsLocalRing.maximalIdeal B) ^ m ≤ (IsLocalRing.maximalIdeal B) ^ (m + 1) :=
        hm ▸ hle
      have : (IsLocalRing.maximalIdeal B : Ideal B) ^ m = ⊥ := by
        have key : ((IsLocalRing.maximalIdeal B) ^ m : Ideal B) ≤
            IsLocalRing.maximalIdeal B • ((IsLocalRing.maximalIdeal B) ^ m : Ideal B) := by
          calc ((IsLocalRing.maximalIdeal B) ^ m : Ideal B)
              ≤ (IsLocalRing.maximalIdeal B) ^ (m + 1) := hle'
            _ = (IsLocalRing.maximalIdeal B) ^ m * IsLocalRing.maximalIdeal B := pow_succ _ m
            _ = IsLocalRing.maximalIdeal B * (IsLocalRing.maximalIdeal B) ^ m := mul_comm _ _
            _ = IsLocalRing.maximalIdeal B • (IsLocalRing.maximalIdeal B) ^ m :=
                (Ideal.smul_eq_mul _ _).symm
        exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
          (IsLocalRing.maximalIdeal B) ((IsLocalRing.maximalIdeal B) ^ m : Ideal B)
          (IsNoetherian.noetherian _) key
          (by rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top])
      exact hIne (hm.trans this)
    have hme : m = e := by
      have h1 : I ≤ (IsLocalRing.maximalIdeal B) ^ m := hm ▸ le_refl _
      exact (Ideal.ramificationIdx_spec h1 hgt).symm
    rw [← hme, hm]


  have he_le_n : e ≤ n := by
    haveI : IsDedekindDomain A := inferInstance
    haveI : IsDedekindDomain B := inferInstance
    haveI : (IsLocalRing.maximalIdeal A).IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
    set f := Ideal.inertiaDeg (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)
    have hefn : e * f = n :=
      Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing B K L
        (IsDiscreteValuationRing.not_a_field A)
    have hn_pos : 0 < n := Module.finrank_pos (R := K) (M := L)
    have hf_pos : 0 < f := Nat.pos_of_mul_pos_left (hefn ▸ hn_pos)
    calc e = e * 1 := (Nat.mul_one e).symm
      _ ≤ e * f := Nat.mul_le_mul_left e hf_pos
      _ = n := hefn
  have hpow_le_smul : ((IsLocalRing.maximalIdeal B) ^ n).restrictScalars A ≤
      (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A B) := by
    rw [Ideal.smul_top_eq_map, hmap_eq]
    exact Submodule.restrictScalars_mono A (Ideal.pow_le_pow_right he_le_n)

  intro b _
  have hb := hiter b
  exact (sup_le_sup_left hpow_le_smul S.toSubmodule) hb

theorem dvr_cyclotomic_monogenic_adjoin_eq_top
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (m : ℕ) (hm : 0 < m)
    (L : Type*) [Field L] [Algebra K L]
    [IsCyclotomicExtension {m} K L] [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L]
    (ζ : B) (hζ : IsPrimitiveRoot ζ m) :
    Algebra.adjoin A ({ζ} : Set B) = ⊤ := by
  haveI : Algebra.IsSeparable K L := IsCyclotomicExtension.isSeparable {m} K L
  haveI : Module.Finite A B := dvr_extension_module_finite A K L B
  exact subalgebra_eq_top_of_mod_maximal _ (cyclotomic_root_spans_mod_maximal A K m hm L B ζ hζ)

theorem dvr_cyclotomic_monogenic_root
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (m : ℕ) (hm : 0 < m)
    (L : Type*) [Field L] [Algebra K L]
    [IsCyclotomicExtension {m} K L] [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L] :
    ∃ ζ : B, IsPrimitiveRoot ζ m ∧ Algebra.adjoin A ({ζ} : Set B) = ⊤ := by

  obtain ⟨ζ_L, hζ_L⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K L
    (Set.mem_singleton m) (Nat.pos_iff_ne_zero.mp hm)

  have hζ_int : IsIntegral B ζ_L := (hζ_L.isIntegral hm).tower_top

  haveI : IsIntegrallyClosed B := GCDMonoid.toIsIntegrallyClosed
  rw [IsIntegrallyClosed.isIntegral_iff] at hζ_int
  obtain ⟨ζ_B, hζ_eq⟩ := hζ_int

  have hζ_prim : IsPrimitiveRoot ζ_B m := by
    rw [← hζ_eq] at hζ_L
    exact (IsPrimitiveRoot.map_iff_of_injective (IsFractionRing.injective B L)).mp hζ_L

  exact ⟨ζ_B, hζ_prim, dvr_cyclotomic_monogenic_adjoin_eq_top A K m hm L B ζ_B hζ_prim⟩

theorem dvr_cyclotomic_unramified_finrank
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    [Fintype (IsLocalRing.ResidueField A)]
    [CharP (IsLocalRing.ResidueField A) p]
    (m : ℕ) (hm : 0 < m) (hcop : ¬(p ∣ m))
    (L : Type*) [Field L] [Algebra K L]
    [IsCyclotomicExtension {m} K L] [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsLocalHom (algebraMap A B)]
    [IsIntegralClosure B A L] :
    Module.finrank A B =
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) := by

  obtain ⟨ζ, hζ_prim, hζ_gen⟩ := dvr_cyclotomic_monogenic_root A K m hm L B

  have hint : IsIntegral A ζ := (hζ_prim.isIntegral hm).tower_top

  haveI : Module.Finite A B := by
    haveI : Algebra.FiniteType A B := ⟨⟨{ζ}, by simp [hζ_gen]⟩⟩
    haveI : Algebra.IsIntegral A B := by
      rw [Algebra.isIntegral_def]
      intro x
      exact IsIntegral.of_mem_of_fg _ hint.fg_adjoin_singleton x (hζ_gen ▸ Algebra.mem_top)
    exact Algebra.IsIntegral.finite

  haveI : NoZeroSMulDivisors A B := by
    have hinj_AL : Function.Injective (algebraMap A L) := by
      rw [IsScalarTower.algebraMap_eq A K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
    have hinj : Function.Injective (algebraMap A B) := by
      rw [IsScalarTower.algebraMap_eq A B L] at hinj_AL
      exact Function.Injective.of_comp hinj_AL
    constructor
    intro a c hac
    rw [Algebra.smul_def] at hac
    rcases mul_eq_zero.mp hac with ha | hc
    · left; exact hinj (by rw [ha, map_zero])
    · right; exact hc

  have hm_ne : (m : IsLocalRing.ResidueField A) ≠ 0 := by
    intro h
    exact hcop ((CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A) p m).mp h)


  set k := IsLocalRing.ResidueField A
  set l := IsLocalRing.ResidueField B
  set ζbar := IsLocalRing.residue B ζ
  set gbar := (minpoly A ζ).map (IsLocalRing.residue A)

  have hmon : (minpoly A ζ).Monic := minpoly.monic hint

  haveI : IsIntegrallyClosed A := GCDMonoid.toIsIntegrallyClosed
  have hdvd : minpoly A ζ ∣ Polynomial.X ^ m - Polynomial.C 1 :=
    minpoly.isIntegrallyClosed_dvd hint (by simp [hζ_prim.pow_eq_one])
  have hdvd_bar : gbar ∣ Polynomial.X ^ m - Polynomial.C 1 := by
    have h1 := Polynomial.map_dvd (IsLocalRing.residue A) hdvd
    simp [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one, Polynomial.map_X] at h1
    exact h1
  have hsep_xm : (Polynomial.X ^ m - Polynomial.C (1 : k)).Separable :=
    Polynomial.separable_X_pow_sub_C 1 hm_ne one_ne_zero
  have hsep_gbar : gbar.Separable := hsep_xm.of_dvd hdvd_bar


  have hmon_gbar : gbar.Monic := hmon.map _
  have hdeg_pos : 0 < gbar.natDegree := by
    rw [hmon.natDegree_map]; exact minpoly.natDegree_pos hint
  have hnu_gbar : ¬IsUnit gbar := by
    intro hu; exact absurd (Polynomial.natDegree_eq_zero_of_isUnit hu) (by omega)
  have hirr_minpoly : Irreducible (minpoly A ζ) := minpoly.irreducible hint
  have hirred : Irreducible gbar := by
    constructor
    · exact hnu_gbar
    · intro p q hpq
      have hcop : IsCoprime p q := (hpq ▸ hsep_gbar).isCoprime
      exact irreducible_no_coprime_factor_mod hirr_minpoly p q hpq hcop

  have hres_top : Algebra.adjoin k ({ζbar} : Set l) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective (R := B) x
    have hb : b ∈ Algebra.adjoin A ({ζ} : Set B) := hζ_gen ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hb ⊢
    obtain ⟨p, rfl⟩ := hb
    refine ⟨p.map (IsLocalRing.residue A), ?_⟩
    simp only [Polynomial.aeval_def, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Polynomial.eval₂_map, Polynomial.hom_eval₂]
    congr 1

  have heval_gbar : Polynomial.aeval ζbar gbar = 0 := by
    show Polynomial.aeval ζbar ((minpoly A ζ).map (IsLocalRing.residue A)) = 0
    simp only [Polynomial.aeval_def, Polynomial.eval₂_map]
    have hcomp : (algebraMap k l).comp (IsLocalRing.residue A) =
      (IsLocalRing.residue B).comp (algebraMap A B) := by ext; rfl
    rw [hcomp, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]
  have hintk : IsIntegral k ζbar := ⟨gbar, hmon_gbar, heval_gbar⟩
  have heq_minpoly : gbar = minpoly k ζbar :=
    minpoly.eq_of_irreducible_of_monic hirred heval_gbar hmon_gbar

  let pbA := PowerBasis.ofAdjoinEqTop' hint hζ_gen
  let pbk := PowerBasis.ofAdjoinEqTop' hintk hres_top
  calc Module.finrank A B
    _ = pbA.dim := pbA.finrank
    _ = (minpoly A ζ).natDegree := rfl
    _ = gbar.natDegree := (hmon.natDegree_map _).symm
    _ = (minpoly k ζbar).natDegree := by rw [heq_minpoly]
    _ = pbk.dim := rfl
    _ = Module.finrank k l := pbk.finrank.symm

theorem pth_root_unity_eq_one_of_no_prim_root
    (L : Type*) [Field L] (p : ℕ) [hp : Fact (Nat.Prime p)]
    (hno : ∀ ω : L, ¬IsPrimitiveRoot ω p)
    (η : L) (hη : η ^ p = 1) : η = 1 := by
  have h1 : orderOf η ∣ p := orderOf_dvd_of_pow_eq_one hη
  rcases hp.out.eq_one_or_self_of_dvd (orderOf η) h1 with h | h
  · rwa [orderOf_eq_one_iff] at h
  · exact absurd (h ▸ IsPrimitiveRoot.orderOf η) (hno η)

lemma prod_mem_ideal_pow {R : Type*} [CommRing R] (I : Ideal R)
    (s : Finset ℕ) (f : ℕ → R) (hf : ∀ i ∈ s, f i ∈ I) :
    ∏ i ∈ s, f i ∈ I ^ s.card := by
  induction s using Finset.induction_on with
  | empty => simp [Ideal.one_eq_top]
  | insert a s hna ih =>
    rw [Finset.prod_insert hna, Finset.card_insert_of_notMem hna, pow_succ']
    exact Ideal.mul_mem_mul (hf _ (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem no_prim_root_in_unramified_ext_of_base
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Fintype (IsLocalRing.ResidueField A)]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    [CharP (IsLocalRing.ResidueField A) p]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (habsunram : Ideal.span {(↑p : A)} = IsLocalRing.maximalIdeal A)
    (he : (IsLocalRing.maximalIdeal A).ramificationIdx
      (IsLocalRing.maximalIdeal B) = 1)
    (hnoroot : ∀ ω : K, ¬IsPrimitiveRoot ω p)
    (ω : L) : ¬IsPrimitiveRoot ω p := by
  intro hprim

  have hmap_le : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) ≤
      IsLocalRing.maximalIdeal B := by
    have h := Ideal.le_pow_of_le_ramificationIdx
      (show 1 ≤ (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B)
       from he.symm ▸ le_refl 1)
    simpa [pow_one] using h

  have hp_mem_B : (↑p : B) ∈ IsLocalRing.maximalIdeal B := by
    have hp_mem_A : (↑p : A) ∈ IsLocalRing.maximalIdeal A :=
      habsunram ▸ Ideal.subset_span (Set.mem_singleton _)
    have := hmap_le (Ideal.mem_map_of_mem _ hp_mem_A)
    rwa [map_natCast] at this

  have hp_not_sq : (↑p : B) ∉ (IsLocalRing.maximalIdeal B) ^ 2 := by
    intro h
    have hnotmap : ¬(Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) ≤
        (IsLocalRing.maximalIdeal B) ^ 2) := by
      rw [← Ideal.ramificationIdx_ne_one_iff hmap_le]; omega
    apply hnotmap
    rw [← habsunram, Ideal.map_span, Ideal.span_le]
    rintro x ⟨a, rfl, rfl⟩
    rwa [map_natCast]

  haveI hcharB : CharP (IsLocalRing.ResidueField B) p := by
    rw [CharP.charP_iff_prime_eq_zero hp.out]
    rw [show (↑p : IsLocalRing.ResidueField B) = (IsLocalRing.residue B) (↑p : B) from
      (map_natCast (IsLocalRing.residue B) p).symm]
    exact (IsLocalRing.residue_eq_zero_iff (↑p : B)).mpr hp_mem_B

  have hp_ne_zero_A : (↑p : A) ≠ 0 := by
    intro h
    have : IsLocalRing.maximalIdeal A = ⊥ := by rw [← habsunram, h]; simp
    exact IsDiscreteValuationRing.not_isField A
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr this)

  have hp_ne_zero_K : (↑p : K) ≠ 0 := by
    intro h
    apply hp_ne_zero_A
    have : algebraMap A K (↑p : A) = 0 := by rwa [map_natCast]
    exact (IsFractionRing.injective A K) (this.trans (map_zero _).symm)

  by_cases hp2 : p = 2
  · apply hnoroot (-1 : K)
    subst hp2
    have hne : (-1 : K) ≠ 1 := by
      intro h
      apply hp_ne_zero_K
      have h1 : (1 : K) + 1 = 0 := by
        have := neg_add_cancel (1 : K); rwa [h] at this
      have : (2 : K) = 0 := by
        have : (2 : K) = 1 + 1 := by norm_num
        rw [this]; exact h1
      exact_mod_cast this
    constructor
    · norm_num
    · intro l hl
      rw [neg_one_pow_eq_one_iff_even hne] at hl
      exact hl.two_dvd
  ·
    have hp_ge_3 : 3 ≤ p := by have := hp.out.two_le; omega

    obtain ⟨b, hb_eq, hb_prim⟩ : ∃ b : B, algebraMap B L b = ω ∧ IsPrimitiveRoot b p := by
      have hint : IsIntegral B ω := (hprim.isIntegral hp.out.pos).tower_top
      obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
      exact ⟨b, hb, (hb ▸ hprim).of_map_of_injective (IsFractionRing.injective B L)⟩

    have hres_one : IsLocalRing.residue B b = 1 := by
      have hbp : b ^ p = 1 := hb_prim.pow_eq_one
      have hres_pow : (IsLocalRing.residue B b) ^ p = 1 := by
        rw [← map_pow, hbp, map_one]
      have h1 : ((IsLocalRing.residue B b) - 1) ^ p = 0 := by
        rw [sub_pow_char _ 1, one_pow, hres_pow, sub_self]
      have h2 : (IsLocalRing.residue B b) - 1 = 0 := by
        rwa [pow_eq_zero_iff (Nat.Prime.ne_zero hp.out)] at h1
      exact sub_eq_zero.mp h2

    have hmem_max : ∀ k ∈ Finset.range (p - 1),
        1 - b ^ (k + 1) ∈ IsLocalRing.maximalIdeal B := by
      intro k _
      rw [← IsLocalRing.residue_eq_zero_iff]
      simp only [map_sub, map_one, map_pow, hres_one, one_pow, sub_self]

    have hprod : ∏ k ∈ Finset.range (p - 1), (1 - b ^ (k + 1)) = (↑p : B) := by
      have hp1 : 1 ≤ p := hp.out.one_le
      have hb' : IsPrimitiveRoot b ((p - 1) + 1) :=
        (show p = (p - 1) + 1 by omega) ▸ hb_prim
      rw [IsPrimitiveRoot.prod_one_sub_pow_eq_order hb']
      push_cast [Nat.cast_sub hp1]
      ring

    have hp_in_pow : (↑p : B) ∈ (IsLocalRing.maximalIdeal B) ^ (p - 1) := by
      rw [← hprod]
      convert prod_mem_ideal_pow (IsLocalRing.maximalIdeal B) (Finset.range (p - 1))
        (fun i => 1 - b ^ (i + 1)) hmem_max using 1
      simp [Finset.card_range]

    exact hp_not_sq (Ideal.pow_le_pow_right (by omega : 2 ≤ p - 1) hp_in_pow)

theorem no_prim_pth_root_in_unramified_ext
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Fintype (IsLocalRing.ResidueField A)]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    [CharP (IsLocalRing.ResidueField A) p]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (habsunram : Ideal.span {(↑p : A)} = IsLocalRing.maximalIdeal A)
    (he : (IsLocalRing.maximalIdeal A).ramificationIdx
      (IsLocalRing.maximalIdeal B) = 1)
    (hnoroot : ∀ ω : K, ¬IsPrimitiveRoot ω p)
    (η : L) (hη : η ^ p = 1) : η = 1 := by
  have hnoL : ∀ ω : L, ¬IsPrimitiveRoot ω p :=
    no_prim_root_in_unramified_ext_of_base A K p L B habsunram he hnoroot
  exact pth_root_unity_eq_one_of_no_prim_root L p hnoL η hη

theorem unramified_pth_root_in_base
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Fintype (IsLocalRing.ResidueField A)]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    [CharP (IsLocalRing.ResidueField A) p]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (habsunram : Ideal.span {(↑p : A)} = IsLocalRing.maximalIdeal A)
    (he : (IsLocalRing.maximalIdeal A).ramificationIdx
      (IsLocalRing.maximalIdeal B) = 1)
    (η : L) (hη : η ^ p = 1) :
    ∃ ζ : K, algebraMap K L ζ = η := by

  by_cases hprim : ∃ ω : K, IsPrimitiveRoot ω p
  ·

    obtain ⟨ω, hω⟩ := hprim
    have hωL : IsPrimitiveRoot (algebraMap K L ω) p :=
      hω.map_of_injective (algebraMap K L).injective
    haveI : NeZero p := ⟨Nat.Prime.ne_zero hp.out⟩
    obtain ⟨i, _, hi⟩ := hωL.eq_pow_of_pow_eq_one hη
    exact ⟨ω ^ i, by rw [map_pow, hi]⟩
  ·

    rw [not_exists] at hprim
    have h1 := no_prim_pth_root_in_unramified_ext A K p L B habsunram he hprim η hη
    exact ⟨1, by rw [map_one, h1]⟩

theorem dvr_pth_root_ramified
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    [Fintype (IsLocalRing.ResidueField A)]
    [CharP (IsLocalRing.ResidueField A) p]
    (hno_prim : ∀ ζ : K, ζ ^ p = 1 → ζ = 1)
    (m : ℕ) (hm : 0 < m) (hdvd : p ∣ m)
    (L : Type*) [Field L] [Algebra K L]
    [IsCyclotomicExtension {m} K L]
    [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (habsunram : Ideal.span {(↑p : A)} = IsLocalRing.maximalIdeal A) :
    (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) ≠ 1 := by

  intro he

  have hm_ne : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm
  have hpp : Nat.Prime p := hp.out
  obtain ⟨ζ_m, hζ_m⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K L
    (Set.mem_singleton m) hm_ne
  obtain ⟨j, hj⟩ := hdvd
  have hj_pos : 0 < j := Nat.pos_of_ne_zero (by intro h; simp [h] at hj; omega)

  have η_prim : IsPrimitiveRoot (ζ_m ^ j) p := by
    rw [hj] at hζ_m
    have hj_ne : j ≠ 0 := Nat.pos_iff_ne_zero.mp hj_pos
    have hj_dvd : j ∣ p * j := dvd_mul_left j p
    have h := hζ_m.pow_of_dvd hj_ne hj_dvd
    rwa [Nat.mul_div_cancel _ hj_pos] at h
  set η := ζ_m ^ j with hη_def

  obtain ⟨ζ, hζ⟩ := unramified_pth_root_in_base A K p L B habsunram he η η_prim.pow_eq_one

  have hζ_pow : ζ ^ p = 1 := by
    have h1 : algebraMap K L (ζ ^ p) = η ^ p := by rw [map_pow, hζ]
    rw [η_prim.pow_eq_one] at h1
    exact (algebraMap K L).injective (h1.trans (map_one _).symm)
  have hζ_eq : ζ = 1 := hno_prim ζ hζ_pow

  have hη_eq : η = 1 := by rw [← hζ, hζ_eq, map_one]
  exact η_prim.ne_one hpp.one_lt hη_eq

theorem cyclotomic_unramified_of_coprime
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    [Fintype (IsLocalRing.ResidueField A)]
    [CharP (IsLocalRing.ResidueField A) p]
    (m : ℕ) (hm : 0 < m) (hcop : ¬(p ∣ m))
    (L : Type*) [Field L] [Algebra K L]
    [IsCyclotomicExtension {m} K L]
    [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable K L] [IsIntegralClosure B A L] :
    (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) = 1 := by

  obtain ⟨h_fin, h_loc⟩ := dvr_extension_finite_and_local A K L B
  haveI : Module.Finite A B := h_fin
  haveI : IsLocalHom (algebraMap A B) := h_loc

  haveI : IsDedekindDomain A := inferInstance
  haveI : IsDedekindDomain B := inferInstance
  haveI : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A) :=
    IsLocalRing.ResidueField.instLiesOverMaximalIdeal
  haveI : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  haveI : Algebra.IsAlgebraic A B := Algebra.IsAlgebraic.of_finite A B

  set 𝔭 := IsLocalRing.maximalIdeal A
  set 𝔮 := IsLocalRing.maximalIdeal B
  set e := 𝔭.ramificationIdx 𝔮
  set f := Ideal.inertiaDeg 𝔭 𝔮
  set f_res := Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)

  have efn : e * f = Module.finrank K L :=
    Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing B K L
      (IsDiscreteValuationRing.not_a_field A)

  have f_eq : f = f_res := @Ideal.inertiaDeg_algebraMap A _ B _ _ 𝔭 𝔮 _

  have fKL_AB : Module.finrank K L = Module.finrank A B :=
    Algebra.IsAlgebraic.finrank_of_isFractionRing A K B L

  have fAB_res : Module.finrank A B = f_res :=
    dvr_cyclotomic_unramified_finrank A K p m hm hcop L B

  have h_emul : e * f_res = f_res := by
    calc e * f_res = e * f := by rw [f_eq]
    _ = Module.finrank K L := efn
    _ = Module.finrank A B := fKL_AB
    _ = f_res := fAB_res

  have hf_pos : 0 < f_res := by
    have hKL : 0 < Module.finrank K L := Module.finrank_pos
    rw [fKL_AB, fAB_res] at hKL
    exact hKL

  exact mul_right_cancel₀ (Nat.pos_iff_ne_zero.mp hf_pos) (by rw [h_emul, one_mul])

theorem cyclotomic_ramified_of_dvd
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    [Fintype (IsLocalRing.ResidueField A)]
    [CharP (IsLocalRing.ResidueField A) p]
    (hno_prim : ∀ ζ : K, ζ ^ p = 1 → ζ = 1)
    (m : ℕ) (hm : 0 < m) (hdvd : p ∣ m)
    (L : Type*) [Field L] [Algebra K L]
    [IsCyclotomicExtension {m} K L]
    [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (habsunram : Ideal.span {(↑p : A)} = IsLocalRing.maximalIdeal A) :
    (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) ≠ 1 :=
  dvr_pth_root_ramified A K p hno_prim m hm hdvd L B habsunram

theorem cyclotomic_ramified_iff_char_dvd

    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]

    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

    (p : ℕ) [hp : Fact (Nat.Prime p)]

    [Fintype (IsLocalRing.ResidueField A)]
    [CharP (IsLocalRing.ResidueField A) p]

    (hno_prim : ∀ ζ : K, ζ ^ p = 1 → ζ = 1)

    (m : ℕ) (hm : 0 < m)

    (L : Type*) [Field L] [Algebra K L]
    [IsCyclotomicExtension {m} K L]
    [FiniteDimensional K L]

    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (habsunram : Ideal.span {(↑p : A)} = IsLocalRing.maximalIdeal A)

    [Algebra.IsSeparable K L] [IsIntegralClosure B A L] :

    ((IsLocalRing.maximalIdeal A).ramificationIdx
      (IsLocalRing.maximalIdeal B) ≠ 1) ↔ (p ∣ m) := by
  constructor
  ·


    intro hram
    by_contra hndvd
    exact hram (cyclotomic_unramified_of_coprime A K p m hm hndvd L B)
  ·

    intro hdvd
    exact cyclotomic_ramified_of_dvd A K p hno_prim m hm hdvd L B habsunram

theorem cor_10_16
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (n : ℕ) (hn_pos : 0 < n)
    (L : Type*) [Field L] [Algebra K L]
    [IsCyclotomicExtension {n} K L] [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    [IsIntegralClosure B A L]
    [IsLocalHom (algebraMap A B)] [Module.Finite A B] [NoZeroSMulDivisors A B]
    (ζ : B) (hprim : IsPrimitiveRoot ζ n)
    (hcoprime : Nat.Coprime n (ringChar (IsLocalRing.ResidueField A))) :
    IsUnramifiedDVRExtension A B := by
  have hgen : Algebra.adjoin A ({ζ} : Set B) = ⊤ :=
    dvr_cyclotomic_monogenic_adjoin_eq_top A K n hn_pos L B ζ hprim
  exact cor_10_16_of_adjoin A B hprim hcoprime hgen

end
