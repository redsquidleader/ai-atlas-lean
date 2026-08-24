/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.EisensteinRamified
import Atlas.NumberTheoryI.code.Thm1023
import Atlas.NumberTheoryI.code.Cor1015
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct

open Ideal IsLocalRing

section RamificationDefinitions

variable
  (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L] [IsFractionRing B L]
  [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]

noncomputable abbrev AKLB_residueChar :=
  ringChar (IsLocalRing.ResidueField A)

def AKLB_IsTamelyRamified : Prop :=
  ¬ (AKLB_residueChar A ∣ AKLB_ramIdx A B)

def AKLB_IsTotallyTamelyRamified : Prop :=
  AKLB_ramIdx A B = Module.finrank K L ∧ ¬ (AKLB_residueChar A ∣ AKLB_ramIdx A B) ∧
  1 < Module.finrank K L

end RamificationDefinitions

section RamificationTransitivity

variable {p e_EK e_EL e_LK : ℕ}

theorem tamelyRamified_of_tower_left
    (hmul : e_EK = e_EL * e_LK) (h : ¬ (p ∣ e_EK)) : ¬ (p ∣ e_LK) :=
  fun hd => h (hmul ▸ dvd_mul_of_dvd_right hd e_EL)

theorem tamelyRamified_of_tower_right
    (hmul : e_EK = e_EL * e_LK) (h : ¬ (p ∣ e_EK)) : ¬ (p ∣ e_EL) :=
  fun hd => h (hmul ▸ dvd_mul_of_dvd_left hd e_LK)

theorem tamelyRamified_tower
    (hp : Nat.Prime p ∨ p = 0)
    (hmul : e_EK = e_EL * e_LK)
    (hEL : ¬ (p ∣ e_EL)) (hLK : ¬ (p ∣ e_LK)) : ¬ (p ∣ e_EK) := by
  rw [hmul]
  rcases hp with hp | rfl
  · exact hp.not_dvd_mul hEL hLK
  · simp only [zero_dvd_iff, mul_eq_zero, not_or] at *
    exact ⟨hEL, hLK⟩

theorem tamelyRamified_tower_iff
    (hp : Nat.Prime p ∨ p = 0)
    (hmul : e_EK = e_EL * e_LK) :
    ¬ (p ∣ e_EK) ↔ ¬ (p ∣ e_EL) ∧ ¬ (p ∣ e_LK) :=
  ⟨fun h => ⟨tamelyRamified_of_tower_right hmul h, tamelyRamified_of_tower_left hmul h⟩,
   fun ⟨hEL, hLK⟩ => tamelyRamified_tower hp hmul hEL hLK⟩

lemma residueChar_prime_or_zero (F : Type*) [Field F] :
    Nat.Prime (ringChar F) ∨ ringChar F = 0 := by
  haveI := ringChar.charP F
  exact CharP.char_is_prime_or_zero F (ringChar F)

variable {f_EK f_EL f_LK : ℕ}

theorem totallyRamified_tower
    (hmul_f : f_EK = f_EL * f_LK)
    (hEL : f_EL = 1) (hLK : f_LK = 1) : f_EK = 1 := by
  rw [hmul_f, hEL, hLK, mul_one]

end RamificationTransitivity

section TotallyTamelyRamifiedCharacterization

variable
  (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L] [IsFractionRing B L]
  [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]

structure IsNthRootOfUniformizer (n : ℕ) (π : B) (πA : A) : Prop where
  uniformizer_A : Irreducible πA
  pow_eq : π ^ n = algebraMap A B πA
  adjoin_eq_top : Algebra.adjoin A ({π} : Set B) = ⊤

theorem nth_root_of_uniformizer_generates
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (n : ℕ) (hn : 1 < n) (π : B) (πA : A)
    (hπA : Irreducible πA) (hpow : π ^ n = algebraMap A B πA)
    (hn_eq : n = Module.finrank K L) :
    Irreducible π ∧ Algebra.adjoin A ({π} : Set B) = ⊤ := by


  obtain ⟨πB, hπB⟩ := IsDiscreteValuationRing.exists_irreducible (R := B)

  have hπ_ne_zero : π ≠ 0 := by
    intro h; rw [h, zero_pow (by omega : n ≠ 0)] at hpow
    exact hπA.ne_zero (FaithfulSMul.algebraMap_injective A B (hpow.symm.trans (map_zero _).symm))
  have hπ_not_unit : ¬IsUnit π := by
    intro h; have := h.pow n; rw [hpow] at this
    exact hπA.1 ((isUnit_map_iff (algebraMap A B) _).mp this)

  have hπ_span_ne_bot : Ideal.span {π} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  obtain ⟨k, hk_eq⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hπ_span_ne_bot hπB

  have h_maxB : IsLocalRing.maximalIdeal B = Ideal.span {πB} := hπB.maximalIdeal_eq

  have hk_max : Ideal.span {π} = (IsLocalRing.maximalIdeal B) ^ k := by
    rw [hk_eq, ← Ideal.span_singleton_pow, h_maxB]

  have hk_pos : 0 < k := by
    by_contra h; push Not at h; interval_cases k
    rw [pow_zero, Ideal.one_eq_top] at hk_max
    exact hπ_not_unit (Ideal.span_singleton_eq_top.mp hk_max)


  have hπA_span : IsLocalRing.maximalIdeal A = Ideal.span {πA} := hπA.maximalIdeal_eq

  have h_map : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      Ideal.span {algebraMap A B πA} := by
    rw [hπA_span, Ideal.map_span, Set.image_singleton]

  have h_span_pow : Ideal.span {algebraMap A B πA} = (Ideal.span {π}) ^ n := by
    rw [Ideal.span_singleton_pow, ← hpow]

  have h_map_eq : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
      (IsLocalRing.maximalIdeal B) ^ (n * k) := by
    rw [h_map, h_span_pow, hk_max, ← pow_mul, mul_comm]

  have h_degree := AKLB_degree_eq_ramIdx_mul_resDeg A K B L

  have hπA_B_ne_zero : algebraMap A B πA ≠ 0 := by
    intro h
    exact hπA.ne_zero (FaithfulSMul.algebraMap_injective A B (h.trans (map_zero _).symm))

  have hnk_ne : n * k ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have h_map_ne_bot : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) ≠ ⊥ := by
    rw [h_map_eq]; exact (pow_ne_zero_iff hnk_ne).mpr
      (IsDiscreteValuationRing.not_a_field B)
  have hPbot : IsLocalRing.maximalIdeal B ≠ ⊥ := IsDiscreteValuationRing.not_a_field B
  have hPprime : (IsLocalRing.maximalIdeal B).IsPrime := Ideal.IsMaximal.isPrime
    (IsLocalRing.maximalIdeal.isMaximal (R := B))
  have he_eq_nk : (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) =
      n * k := by
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count h_map_ne_bot
        hPprime hPbot, h_map_eq, UniqueFactorizationMonoid.normalizedFactors_pow,
        Multiset.count_nsmul,
        UniqueFactorizationMonoid.normalizedFactors_irreducible
          (Ideal.prime_of_isPrime hPbot hPprime).irreducible]
    simp [normalize_eq]


  have he_pos : 0 < (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) := by
    rw [he_eq_nk]; exact Nat.mul_pos (by omega) hk_pos
  have h_fk_eq_1 : AKLB_resDeg A B * k = 1 := by
    have h_n_eq_ef : n = (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B)
        * AKLB_resDeg A B := by rw [hn_eq]; exact h_degree
    nlinarith [he_eq_nk]
  have hk_eq_1 : k = 1 := Nat.eq_one_of_mul_eq_one_left h_fk_eq_1
  have hf_eq_1 : AKLB_resDeg A B = 1 := Nat.eq_one_of_mul_eq_one_right h_fk_eq_1

  have h_span_eq : Ideal.span {π} = IsLocalRing.maximalIdeal B := by
    rw [hk_max, hk_eq_1, pow_one]
  have hπ_irr : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr h_span_eq.symm

  have htotram : (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) =
      Module.finrank K L := by
    rw [he_eq_nk, hk_eq_1, mul_one, hn_eq]
  constructor
  · exact hπ_irr
  · exact totally_ramified_adjoin_uniformizer A K B L π hπ_irr htotram

theorem uniformizer_pow_associated_algebraMap
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (πA₀ : A) (hπA₀ : Irreducible πA₀)
    (πB : B) (hπB : Irreducible πB) :
    ∃ u : Bˣ, πB ^ (Module.finrank K L) = ↑u * algebraMap A B πA₀ := by

  have hne : algebraMap A B πA₀ ≠ 0 := by
    simp only [ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective A B)]
    exact hπA₀.ne_zero

  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hπB

  have hram : (maximalIdeal A).ramificationIdx (maximalIdeal B) = m := by

    have hmap : Ideal.map (algebraMap A B) (maximalIdeal A) = (maximalIdeal B) ^ m := by
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer πA₀).mp hπA₀,
          Ideal.map_span, Set.image_singleton, hv]
      rw [show (↑v : B) * πB ^ m = πB ^ m * ↑v from mul_comm _ _,
          ← Ideal.span_singleton_mul_span_singleton]
      simp [Ideal.span_singleton_eq_top.mpr (Units.isUnit v),
            ← Ideal.span_singleton_pow,
            ← (IsDiscreteValuationRing.irreducible_iff_uniformizer πB).mp hπB]
    have hmap_ne : Ideal.map (algebraMap A B) (maximalIdeal A) ≠ ⊥ := by
      rw [hmap, (IsDiscreteValuationRing.irreducible_iff_uniformizer πB).mp hπB,
          Ideal.span_singleton_pow, ne_eq, Ideal.span_singleton_eq_bot]
      exact pow_ne_zero _ hπB.ne_zero
    rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity hmap_ne
          (Ideal.IsMaximal.isPrime' (maximalIdeal B)),
        hmap]
    apply multiplicity_pow_self
    · rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer πB).mp hπB,
          ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact hπB.ne_zero
    · rw [Ideal.isUnit_iff]
      exact (IsLocalRing.maximalIdeal.isMaximal (R := B)).ne_top

  have hm : m = Module.finrank K L := by
    rw [← htotram]; exact hram.symm

  refine ⟨v⁻¹, ?_⟩
  rw [hm] at hv
  rw [hv, ← mul_assoc]
  simp

theorem hensel_unit_nth_root_of_one_mod
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [IsAdicComplete (IsLocalRing.maximalIdeal B) B]
    (n : ℕ) (hn : 1 < n)
    (hp : ¬ (ringChar (IsLocalRing.ResidueField B) ∣ n))
    (u : Bˣ) (hu_mod : (u : B) - 1 ∈ IsLocalRing.maximalIdeal B) :
    ∃ r : Bˣ, (↑r : B) ^ n = ↑u := by
  open Polynomial IsLocalRing in
  haveI : HenselianRing B (maximalIdeal B) := inferInstance
  set f := X ^ n - C (u : B)
  have hf_monic : f.Monic := monic_X_pow_sub_C _ (by omega)

  have hf_eval : f.eval 1 ∈ maximalIdeal B := by
    simp only [f, eval_sub, eval_pow, eval_X, eval_C, one_pow]
    rw [show (1 : B) - ↑u = -(↑u - 1) from by ring]
    exact (maximalIdeal B).neg_mem hu_mod

  have hf_deriv : IsUnit (Ideal.Quotient.mk (maximalIdeal B) (f.derivative.eval 1)) := by
    simp only [f, derivative_sub, derivative_C, sub_zero, derivative_pow, derivative_X, mul_one,
      eval_mul, eval_pow, eval_X, one_pow, mul_one, map_natCast, eval_natCast]
    change IsUnit ((n : ResidueField B))
    rw [isUnit_iff_ne_zero]; exact fun h => hp (ringChar.dvd h)

  obtain ⟨a, ha_root, ha_close⟩ := HenselianRing.is_henselian f hf_monic 1 hf_eval hf_deriv

  have ha_pow : a ^ n = (u : B) := by
    have h : f.eval a = 0 := ha_root
    simp only [f, eval_sub, eval_pow, eval_X, eval_C] at h
    exact sub_eq_zero.mp h

  have ha_unit : IsUnit a := by
    by_contra ha_nmem
    have ha_mem : a ∈ maximalIdeal B := ha_nmem
    have h1_mem : (1 : B) ∈ maximalIdeal B := by
      have : (1 : B) = a - (a - 1) := by ring
      rw [this]; exact Ideal.sub_mem _ ha_mem ha_close
    have := (maximalIdeal.isMaximal B).ne_top
    rw [Ideal.ne_top_iff_one] at this; exact this h1_mem
  obtain ⟨r, rfl⟩ := ha_unit
  exact ⟨r, ha_pow⟩

theorem uniformizer_adjust_mod_maximal
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (πA₀ : A) (hπA₀ : Irreducible πA₀)
    (πB : B) (hπB : Irreducible πB)
    (u : Bˣ) (hu : πB ^ (Module.finrank K L) = ↑u * algebraMap A B πA₀) :
    ∃ (πA₁ : A) (u₁ : Bˣ),
      Irreducible πA₁ ∧
      πB ^ (Module.finrank K L) = ↑u₁ * algebraMap A B πA₁ ∧
      ((u₁ : B) - 1) ∈ IsLocalRing.maximalIdeal B := by

  have hfund := AKLB_degree_eq_ramIdx_mul_resDeg A K B L

  have hn_pos : 0 < Module.finrank K L := Module.finrank_pos
  have hf1 : AKLB_resDeg A B = 1 := by
    rw [htotram] at hfund; nlinarith

  have hsurj : Function.Surjective
      (algebraMap (ResidueField A) (ResidueField B)) := by
    haveI : FiniteDimensional (ResidueField A) (ResidueField B) :=
      FiniteDimensional.of_finrank_pos (by change 0 < AKLB_resDeg A B; omega)
    have hrange : (Algebra.linearMap (ResidueField A) (ResidueField B)).range = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [LinearMap.finrank_range_of_inj
            (algebraMap (ResidueField A) (ResidueField B)).injective,
          Module.finrank_self]; exact hf1.symm

    rwa [LinearMap.range_eq_top] at hrange

  obtain ⟨abar, habar⟩ := hsurj ((residue B) (u : B))
  obtain ⟨a, ha⟩ := residue_surjective (R := A) abar

  have hres_eq : (residue B) ((algebraMap A B) a) = (residue B) (u : B) := by
    have h1 := RingHom.congr_fun (ResidueField.map_comp_residue (algebraMap A B)) a
    simp only [RingHom.comp_apply] at h1
    rw [← h1, ha]; exact habar

  have ha_unit : IsUnit a := by
    by_contra h_nonunit
    have ha_mem : a ∈ maximalIdeal A := by rwa [mem_maximalIdeal]
    have hab_mem : (algebraMap A B) a ∈ maximalIdeal B :=
      map_nonunit (algebraMap A B) a ha_mem
    rw [← residue_eq_zero_iff] at hab_mem
    rw [hres_eq] at hab_mem
    exact (RingHom.isUnit_map _ u.isUnit).ne_zero hab_mem
  obtain ⟨aA, haA⟩ := ha_unit

  set bA := Units.map (algebraMap A B).toMonoidHom aA with hbA_def
  refine ⟨(aA : A) * πA₀, u * bA⁻¹, ?_, ?_, ?_⟩
  ·
    exact (associated_unit_mul_right πA₀ aA aA.isUnit).irreducible hπA₀
  ·
    rw [Units.val_mul, map_mul]
    have hbA_inv_val : (↑bA⁻¹ : B) = algebraMap A B (↑aA⁻¹ : A) := by simp [bA]
    have h_cancel : (algebraMap A B) (↑aA⁻¹ : A) * (algebraMap A B) (↑aA : A) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [show ↑u * ↑bA⁻¹ * ((algebraMap A B) ↑aA * (algebraMap A B) πA₀) =
      ↑u * (↑bA⁻¹ * (algebraMap A B) ↑aA) * (algebraMap A B) πA₀ from by ring]
    rw [hbA_inv_val, h_cancel, mul_one]
    exact hu
  ·
    rw [← residue_eq_zero_iff, map_sub, map_one, sub_eq_zero]
    show (residue B) (↑(u * bA⁻¹)) = 1
    rw [Units.val_mul, map_mul]

    have hbA_val : (↑bA : B) = algebraMap A B (↑aA : A) := by simp [bA]
    rw [← haA] at hres_eq
    rw [← hbA_val] at hres_eq

    rw [← hres_eq, ← map_mul, Units.mul_inv, map_one]

lemma isPrecomplete_of_pow
    {R : Type*} [CommRing R] {I : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]
    (e : ℕ) (he : 1 ≤ e) [hpc : IsPrecomplete (I ^ e) M] :
    IsPrecomplete I M := by
  constructor
  intro f hf
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
      f (m * e) ≡ f (n * e) [SMOD (I ^ e) ^ m • (⊤ : Submodule R M)] := by
    intro m n hmn
    rw [show (I ^ e) ^ m = I ^ (m * e) from by rw [← pow_mul, mul_comm]]
    exact hf (Nat.mul_le_mul_right e hmn)
  obtain ⟨L, hL⟩ := hpc.prec' (fun n => f (n * e)) hcauchy
  exact ⟨L, fun n => by
    have h1 : f n ≡ f (n * e) [SMOD I ^ n • (⊤ : Submodule R M)] :=
      hf (Nat.le_mul_of_pos_right n (by omega))
    have h2 : f (n * e) ≡ L [SMOD (I ^ e) ^ n • (⊤ : Submodule R M)] := hL n
    rw [show (I ^ e) ^ n = I ^ (n * e) from by rw [← pow_mul, mul_comm]] at h2
    exact h1.trans (SModEq.mono (Submodule.smul_mono_left
      (Ideal.pow_le_pow_right (Nat.le_mul_of_pos_right n (by omega)))) h2)⟩

set_option maxHeartbeats 400000 in
theorem finite_extension_adic_complete
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B] :
    IsAdicComplete (IsLocalRing.maximalIdeal B) B := by
  rw [isAdicComplete_iff]
  refine ⟨inferInstance, ?_⟩

  have hpc_A : IsPrecomplete (IsLocalRing.maximalIdeal A) B := by
    rw [← AdicCompletion.of_surjective_iff]
    set I := IsLocalRing.maximalIdeal A
    have hsurj_tp := AdicCompletion.ofTensorProduct_surjective_of_finite I B
    have hsurj_A : Function.Surjective (AdicCompletion.of I A) :=
      (AdicCompletion.of_bijective_iff.mpr inferInstance).2
    suffices h : ∀ t, AdicCompletion.ofTensorProduct I B t ∈
        LinearMap.range (AdicCompletion.of I B) by
      intro y
      obtain ⟨t, ht⟩ := hsurj_tp y
      exact ⟨(h t).choose, by rw [(h t).choose_spec, ht]⟩
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul r b =>
      obtain ⟨a, ha⟩ := hsurj_A r
      exact ⟨a • b, by
        rw [AdicCompletion.ofTensorProduct_tmul, ← ha, map_smul]; rfl⟩
    | add x y hx hy =>
      obtain ⟨bx, hbx⟩ := hx
      obtain ⟨by_, hby⟩ := hy
      exact ⟨bx + by_, by simp [map_add, hbx, hby]⟩

  have hpc_map : IsPrecomplete (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) B :=
    IsPrecomplete.map_algebraMap_iff.mpr hpc_A

  set J := Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) with hJ_def
  have hle : J ≤ IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
  have hJne : J ≠ ⊥ := by
    intro h
    rw [hJ_def, Ideal.map_eq_bot_iff_le_ker] at h
    have hker : RingHom.ker (algebraMap A B) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective A B)
    rw [hker] at h
    exact IsDiscreteValuationRing.not_a_field A (le_bot_iff.mp h)
  obtain ⟨e, he⟩ := exists_maximalIdeal_pow_eq_of_principal B
    (IsPrincipalIdealRing.principal _) J hJne
  have he1 : 1 ≤ e := by
    by_contra h
    push Not at h
    interval_cases e
    simp only [pow_zero, Ideal.one_eq_top] at he
    exact (IsLocalRing.maximalIdeal.isMaximal (R := B)).ne_top
      (eq_top_iff.mpr (he ▸ hle))

  rw [he] at hpc_map
  exact isPrecomplete_of_pow e he1 (hpc := hpc_map)

theorem residue_char_eq_of_local_hom
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] :
    ringChar (IsLocalRing.ResidueField B) = ringChar (IsLocalRing.ResidueField A) := by


  letI : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
    (IsLocalRing.ResidueField.map (algebraMap A B)).toAlgebra
  exact (Algebra.ringChar_eq (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)).symm

theorem totally_tamely_ramified_has_nth_root
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (htame : ¬ (AKLB_residueChar A ∣ AKLB_ramIdx A B))
    (hn1 : 1 < Module.finrank K L) :
    ∃ (πA : A) (π : B),
      Irreducible πA ∧ π ^ (Module.finrank K L) = algebraMap A B πA ∧
      Algebra.adjoin A ({π} : Set B) = ⊤ := by
  set n := Module.finrank K L with hn_def


  have key : ∃ (πA₀ : A) (πB : B) (u : Bˣ) (r : Bˣ),
      Irreducible πA₀ ∧ 1 < n ∧ πB ^ n = ↑u * algebraMap A B πA₀ ∧ (↑r : B) ^ n = ↑u := by

    obtain ⟨πA₀, hπA₀⟩ := IsDiscreteValuationRing.exists_irreducible A
    obtain ⟨πB, hπB⟩ := IsDiscreteValuationRing.exists_irreducible B


    obtain ⟨u₀, hu₀⟩ := uniformizer_pow_associated_algebraMap A K B L htotram πA₀ hπA₀ πB hπB

    obtain ⟨πA₁, u₁, hπA₁, hu₁, hu₁_mod⟩ :=
      uniformizer_adjust_mod_maximal A K B L htotram πA₀ hπA₀ πB hπB u₀ hu₀


    haveI : IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
      finite_extension_adic_complete A B

    have hchar : ringChar (IsLocalRing.ResidueField B) = ringChar (IsLocalRing.ResidueField A) :=
      residue_char_eq_of_local_hom A B

    have htame_B : ¬ (ringChar (IsLocalRing.ResidueField B) ∣ n) := by
      rw [hchar]; rwa [htotram] at htame
    obtain ⟨r, hr⟩ := hensel_unit_nth_root_of_one_mod B n hn1 htame_B u₁ hu₁_mod
    exact ⟨πA₁, πB, u₁, r, hπA₁, hn1, hu₁, hr⟩

  obtain ⟨πA₀, πB, u, r, hπA₀, hn1, hu, hr⟩ := key


  refine ⟨πA₀, πB * ↑(r⁻¹ : Bˣ), hπA₀, ?_, ?_⟩
  ·
    have hrinv_pow : (r⁻¹ : Bˣ) ^ n = u⁻¹ := by
      rw [inv_pow]; congr 1; ext; exact hr
    rw [mul_pow, hu, ← Units.val_pow_eq_pow_val, hrinv_pow]
    rw [mul_assoc, mul_comm (algebraMap A B πA₀) (↑(u⁻¹ : Bˣ)), ← mul_assoc]
    simp [Units.mul_inv]
  ·
    have hpow : (πB * ↑(r⁻¹ : Bˣ)) ^ n = algebraMap A B πA₀ := by
      have hrinv_pow : (r⁻¹ : Bˣ) ^ n = u⁻¹ := by
        rw [inv_pow]; congr 1; ext; exact hr
      rw [mul_pow, hu, ← Units.val_pow_eq_pow_val, hrinv_pow]
      rw [mul_assoc, mul_comm (algebraMap A B πA₀) (↑(u⁻¹ : Bˣ)), ← mul_assoc]
      simp [Units.mul_inv]
    have := nth_root_of_uniformizer_generates A K B L n hn1
      (πB * ↑(r⁻¹ : Bˣ)) πA₀ hπA₀ hpow rfl
    exact this.2

theorem totallyTamelyRamified_of_nthRootOfUniformizer
    (hn : 1 < Module.finrank K L)
    (π : B) (πA : A) (hroot : IsNthRootOfUniformizer A B (Module.finrank K L) π πA)
    (htame : ¬ (AKLB_residueChar A ∣ Module.finrank K L)) :
    AKLB_IsTotallyTamelyRamified A K B L := by

  have ⟨hπ_irr, hadj⟩ :=
    nth_root_of_uniformizer_generates A K B L (Module.finrank K L) hn π πA
      hroot.uniformizer_A hroot.pow_eq rfl


  have hsurj : Function.Surjective (IsLocalRing.ResidueField.map (algebraMap A B)) :=
    residueField_map_surj_of_adjoin_uniformizer π hπ_irr hadj
  have hf1 : AKLB_resDeg A B = 1 :=
    finrank_eq_one_of_algebraMap_surjective hsurj
  have hfund := AKLB_degree_eq_ramIdx_mul_resDeg A K B L
  rw [hf1, mul_one] at hfund


  exact ⟨hfund.symm, hfund.symm ▸ htame, hn⟩

theorem nthRootOfUniformizer_of_totallyTamelyRamified
    (httr : AKLB_IsTotallyTamelyRamified A K B L) :
    ∃ (πA : A) (π : B), IsNthRootOfUniformizer A B (Module.finrank K L) π πA := by
  obtain ⟨htotram, htame, hlt⟩ := httr
  obtain ⟨πA, π, hπA, hpow, hadj⟩ :=
    totally_tamely_ramified_has_nth_root A K B L htotram htame hlt
  exact ⟨πA, π, hπA, hpow, hadj⟩

theorem totallyTamelyRamified_iff_nthRootOfUniformizer
    (hn : 1 < Module.finrank K L)
    (htame_deg : ¬ (AKLB_residueChar A ∣ Module.finrank K L)) :
    AKLB_IsTotallyTamelyRamified A K B L ↔
    ∃ (πA : A) (π : B), IsNthRootOfUniformizer A B (Module.finrank K L) π πA := by
  constructor
  · exact nthRootOfUniformizer_of_totallyTamelyRamified A K B L
  · rintro ⟨πA, π, hroot⟩
    exact totallyTamelyRamified_of_nthRootOfUniformizer A K B L hn π πA hroot htame_deg

end TotallyTamelyRamifiedCharacterization

section PadicDecompositionArithmetic

theorem padic_decomp_exists (e : ℕ) (he : e ≠ 0) (p : ℕ) (hp : Nat.Prime p ∨ p = 0) :
    ∃ m a, e = m * p ^ a ∧ ¬(p ∣ m) := by
  rcases hp with hp | rfl
  · obtain ⟨a, m, hm, heq⟩ := Nat.exists_eq_pow_mul_and_not_dvd he p hp.one_lt.ne'
    exact ⟨m, a, by rw [heq, mul_comm], hm⟩
  · exact ⟨e, 0, by simp, by simp [he]⟩

theorem padic_decomp_unique (p : ℕ) (hp : Nat.Prime p ∨ p = 0) (m₁ m₂ a₁ a₂ : ℕ)
    (hm₁ : ¬(p ∣ m₁)) (hm₂ : ¬(p ∣ m₂))
    (hne : m₁ * p ^ a₁ ≠ 0)
    (heq : m₁ * p ^ a₁ = m₂ * p ^ a₂) : m₁ = m₂ ∧ a₁ = a₂ := by
  rcases hp with hp | rfl
  ·
    suffices ha : a₁ = a₂ by
      subst ha
      exact ⟨Nat.eq_of_mul_eq_mul_right
        (Nat.pos_of_ne_zero (pow_ne_zero _ hp.ne_zero)) heq, rfl⟩
    by_contra hab

    have key : ∀ {m₁ m₂ a₁ a₂ : ℕ}, ¬(p ∣ m₁) →
        m₁ * p ^ a₁ = m₂ * p ^ a₂ → a₁ < a₂ → False := by
      intro m₁ m₂ a₁ a₂ hm heq h
      have heq' : m₁ * p ^ a₁ = m₂ * p ^ (a₂ - a₁) * p ^ a₁ := by
        rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (le_of_lt h)]; exact heq
      have hm₁eq : m₁ = m₂ * p ^ (a₂ - a₁) :=
        Nat.eq_of_mul_eq_mul_right
          (Nat.pos_of_ne_zero (pow_ne_zero _ hp.ne_zero)) heq'
      exact hm (hm₁eq ▸ dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) m₂)
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · exact key hm₁ heq h
    · exact key hm₂ heq.symm h
  ·
    simp only [zero_dvd_iff] at hm₁ hm₂
    rcases Nat.eq_zero_or_pos a₁ with rfl | ha₁ <;>
      rcases Nat.eq_zero_or_pos a₂ with rfl | ha₂
    · simp at heq; exact ⟨heq, rfl⟩
    · simp [zero_pow (by omega : a₂ ≠ 0)] at heq; omega
    · simp [zero_pow (by omega : a₁ ≠ 0)] at heq; omega
    · simp [zero_pow (by omega : a₁ ≠ 0)] at hne

theorem padic_decomp_unique_tower (p : ℕ) (hp : Nat.Prime p ∨ p = 0)
    {e m₁ m₂ a₁ a₂ : ℕ} (he : e ≠ 0)
    (heq₁ : e = m₁ * p ^ a₁) (hm₁ : ¬(p ∣ m₁))
    (heq₂ : e = m₂ * p ^ a₂) (hm₂ : ¬(p ∣ m₂)) :
    m₁ = m₂ ∧ a₁ = a₂ :=
  padic_decomp_unique p hp m₁ m₂ a₁ a₂ hm₁ hm₂ (heq₁ ▸ he) (by rw [← heq₂, ← heq₁])

end PadicDecompositionArithmetic

section TameWildDecompositionTotallyRamified

lemma IntermediateField.adjoin_singleton_eq_of_smul
    {K L : Type*} [Field K] [Field L] [Algebra K L] (α β : L)
    (h1 : ∃ k : K, algebraMap K L k * β = α)
    (h2 : ∃ k : K, algebraMap K L k * α = β) :
    IntermediateField.adjoin K ({α} : Set L) = IntermediateField.adjoin K ({β} : Set L) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx
    obtain ⟨k, hk⟩ := h1; rw [← hk]
    exact mul_mem (IntermediateField.algebraMap_mem _ k)
      (IntermediateField.subset_adjoin K {β} rfl)
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx
    obtain ⟨k, hk⟩ := h2; rw [← hk]
    exact mul_mem (IntermediateField.algebraMap_mem _ k)
      (IntermediateField.subset_adjoin K {α} rfl)

lemma ratio_pow_eq_one {L : Type*} [Field L] (α β c : L) (m : ℕ)
    (hα : α ^ m = c) (hβ : β ^ m = c) (hc : c ≠ 0) :
    (α * β⁻¹) ^ m = 1 := by
  rw [mul_pow, hα, inv_pow, hβ, mul_inv_cancel₀ hc]

theorem rootOfUnity_intCl_unramified
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (E : Type*) [Field E] [Algebra K E] [FiniteDimensional K E]
    [Algebra.IsSeparable K E]
    [Algebra A E] [IsScalarTower A K E]
    (m : ℕ) (hm_ne : (m : IsLocalRing.ResidueField A) ≠ 0)
    (ζ : E) (hζ : ζ ^ m = 1)
    (hgen : IntermediateField.adjoin K ({ζ} : Set E) = ⊤) :
    let _instDVR := thm_9_22_integralClosure_isDVR A K E
    ∃ (_ : IsLocalHom (algebraMap A ↥(integralClosure A E))),
      Ideal.map (algebraMap A ↥(integralClosure A E))
        (IsLocalRing.maximalIdeal A) =
        IsLocalRing.maximalIdeal ↥(integralClosure A E) ∧
      Algebra.IsSeparable (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField ↥(integralClosure A E)) := by
  sorry

set_option maxHeartbeats 800000 in
theorem rootOfUnity_adjoin_le_maxUnram
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L]
    (m : ℕ) (hm : ¬ (AKLB_residueChar A ∣ m))
    (ζ : L) (hζ : ζ ^ m = 1) :
    IntermediateField.adjoin K ({ζ} : Set L) ≤
      maximalUnramifiedSubextension A K L := by


  set E := IntermediateField.adjoin K ({ζ} : Set L) with hE_def

  haveI hfin : FiniteDimensional K E := IntermediateField.finiteDimensional_left E

  have hm_ne_zero : (m : IsLocalRing.ResidueField A) ≠ 0 := by
    intro h; apply hm
    exact (CharP.cast_eq_zero_iff (IsLocalRing.ResidueField A)
      (ringChar (IsLocalRing.ResidueField A)) m).mp h

  have hm_ne_zero_K : (m : K) ≠ 0 := by
    intro h
    apply hm_ne_zero
    have hA : (m : A) = 0 := by
      have hinj := IsFractionRing.injective A K
      have : (algebraMap A K) (m : A) = (m : K) := by simp [map_natCast]
      rw [h] at this; exact hinj (this.trans (map_zero _).symm)
    have : (algebraMap A (IsLocalRing.ResidueField A)) (m : A) = (m : IsLocalRing.ResidueField A) :=
      by simp [map_natCast]
    rw [← this, hA, map_zero]
  haveI hsep_E : Algebra.IsSeparable K E := by
    rw [hE_def, IntermediateField.isSeparable_adjoin_iff_isSeparable]
    intro x hx; rw [Set.mem_singleton_iff] at hx; subst hx
    show (minpoly K x).Separable
    have hdvd : minpoly K x ∣ Polynomial.X ^ m - Polynomial.C 1 :=
      minpoly.dvd K x (by simp [sub_eq_zero, hζ])
    exact (Polynomial.separable_X_pow_sub_C 1 hm_ne_zero_K one_ne_zero).of_dvd hdvd


  set B := integralClosure A E with hB_def
  haveI hDVR_B : IsDiscreteValuationRing B := thm_9_22_integralClosure_isDVR A K E


  have hζ_mem : ζ ∈ E := by
    rw [hE_def]
    exact IntermediateField.subset_adjoin K {ζ} (Set.mem_singleton ζ)
  let ζ_E : E := ⟨ζ, hζ_mem⟩
  have hζ_E_pow : ζ_E ^ m = 1 := by
    ext; simp [ζ_E, SubmonoidClass.mk_pow, hζ]
  have hgen : IntermediateField.adjoin K ({ζ_E} : Set E) = ⊤ := by


    apply IntermediateField.map_injective E.val
    rw [IntermediateField.adjoin_map K {ζ_E} E.val]
    have h1 : E.val '' ({ζ_E} : Set E) = {ζ} := by ext y; simp [ζ_E]
    rw [h1]
    have h2 : IntermediateField.map E.val ⊤ = E := by
      ext x; simp [IntermediateField.mem_map]
    rw [h2, ← hE_def]


  obtain ⟨hLH, hmap, hsep⟩ := rootOfUnity_intCl_unramified A K E m hm_ne_zero ζ_E hζ_E_pow hgen
  haveI := hLH
  haveI := hsep

  haveI : IsNoetherian A ↥(integralClosure A ↥E) :=
    IsIntegralClosure.isNoetherian A K ↥E (integralClosure A ↥E)
  haveI : Module.Finite A ↥(integralClosure A ↥E) := inferInstance
  haveI : Algebra.EssFiniteType A ↥(integralClosure A ↥E) :=
    Algebra.EssFiniteType.of_finiteType A ↥(integralClosure A ↥E)

  haveI : Algebra.FormallyUnramified A B :=
    Algebra.FormallyUnramified.of_map_maximalIdeal hmap


  show E ≤ maximalUnramifiedSubextension A K L
  simp only [maximalUnramifiedSubextension]
  exact le_iSup₂ (f := fun (F : IntermediateField K L) (_ : IsFiniteUnramifiedSubext A K L F) => F)
    E ⟨hfin, ‹Algebra.FormallyUnramified A B›⟩

theorem rootOfUnity_trivialAdjoin_of_totallyRamified
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (m : ℕ) (hm : ¬ (AKLB_residueChar A ∣ m))
    (ζ : L) (hζ : ζ ^ m = 1) :
    Module.finrank K (IntermediateField.adjoin K ({ζ} : Set L)) = 1 := by

  have hef := AKLB_degree_eq_ramIdx_mul_resDeg A K B L
  rw [htotram] at hef

  have hpos : 0 < Module.finrank K L := Module.finrank_pos
  have hf1 : AKLB_resDeg A B = 1 :=
    (Nat.mul_eq_left hpos.ne').mp hef.symm

  have hF_deg := thm_10_23_part_i A K B L
  rw [hf1] at hF_deg


  have hζ_in_F : IntermediateField.adjoin K ({ζ} : Set L) ≤
      maximalUnramifiedSubextension A K L :=
    rootOfUnity_adjoin_le_maxUnram A K L m hm ζ hζ

  haveI : FiniteDimensional K (maximalUnramifiedSubextension A K L) :=
    IntermediateField.finiteDimensional_left _
  have h_le := IntermediateField.finrank_le_of_le_right hζ_in_F
  rw [hF_deg] at h_le
  have h_pos : 0 < Module.finrank K (IntermediateField.adjoin K ({ζ} : Set L)) :=
    Module.finrank_pos
  omega

theorem roots_of_unity_in_base_of_totally_ramified
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (m : ℕ) (hm : ¬ (AKLB_residueChar A ∣ m))
    (ζ : L) (hζ : ζ ^ m = 1) :
    ∃ ζ₀ : K, algebraMap K L ζ₀ = ζ := by
  have h1 := rootOfUnity_trivialAdjoin_of_totallyRamified A K B L htotram m hm ζ hζ
  rw [IntermediateField.finrank_adjoin_eq_one_iff] at h1
  have h2 : ζ ∈ (⊥ : IntermediateField K L) := h1 (Set.mem_singleton ζ)
  rw [IntermediateField.mem_bot] at h2
  exact h2

theorem hensel_dvr_mth_root_of_uniformizer
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (m : ℕ) (hm : ¬ (AKLB_residueChar A ∣ m))
    (hm_dvd : m ∣ Module.finrank K L) :
    ∃ (ϖ : A) (π : L), Irreducible ϖ ∧ π ^ m = algebraMap K L (algebraMap A K ϖ) ∧ π ≠ 0 := by

  have hm_ne : m ≠ 0 := by
    intro h; subst h; exact hm (dvd_zero _)

  by_cases hm1 : m = 1
  · subst hm1
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
    refine ⟨ϖ, algebraMap K L (algebraMap A K ϖ), hϖ, pow_one _, ?_⟩
    simp only [ne_eq, map_eq_zero, map_eq_zero_iff _ (IsFractionRing.injective A K)]
    exact hϖ.ne_zero

  · have hm_ge2 : 1 < m := by omega

    obtain ⟨πA₀, hπA₀⟩ := IsDiscreteValuationRing.exists_irreducible A
    obtain ⟨πB, hπB_irr⟩ := IsDiscreteValuationRing.exists_irreducible B

    haveI hB_complete : IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
      finite_extension_adic_complete A B

    obtain ⟨u₀, hu₀⟩ := uniformizer_pow_associated_algebraMap A K B L htotram πA₀ hπA₀ πB hπB_irr

    obtain ⟨ϖ, u₁, hϖ, hu₁, hu₁_mod⟩ :=
      uniformizer_adjust_mod_maximal A K B L htotram πA₀ hπA₀ πB hπB_irr u₀ hu₀

    have hm_B : ¬ (ringChar (IsLocalRing.ResidueField B) ∣ m) := by
      rwa [residue_char_eq_of_local_hom A B]

    obtain ⟨r, hr⟩ := hensel_unit_nth_root_of_one_mod B m hm_ge2 hm_B u₁ hu₁_mod


    set n := Module.finrank K L with hn_def
    obtain ⟨k, hk⟩ := hm_dvd

    set πB_L := algebraMap B L πB
    set r_L := algebraMap B L (↑r : B)
    have hr_L_ne : r_L ≠ 0 := by
      simp only [r_L, ne_eq, map_eq_zero_iff _ (IsFractionRing.injective B L)]
      exact Units.ne_zero r
    refine ⟨ϖ, πB_L ^ k / r_L, hϖ, ?_, ?_⟩
    ·
      rw [div_pow, ← pow_mul, mul_comm k m, ← hk]


      have h1 : πB_L ^ n = algebraMap B L (↑u₁ : B) * algebraMap B L (algebraMap A B ϖ) := by
        rw [← map_pow, hu₁, map_mul]


      have h2 : r_L ^ m = algebraMap B L (↑u₁ : B) := by
        rw [← map_pow, hr]


      have h3 : algebraMap B L (algebraMap A B ϖ) = algebraMap K L (algebraMap A K ϖ) := by
        rw [← IsScalarTower.algebraMap_apply A B L,
            ← IsScalarTower.algebraMap_apply A K L]

      rw [h2, h1, h3]
      have hu_L_ne : algebraMap B L (↑u₁ : B) ≠ 0 := by
        simp only [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective B L)]
        exact Units.ne_zero u₁
      field_simp
    ·
      apply div_ne_zero
      · apply pow_ne_zero
        show πB_L ≠ 0
        simp only [πB_L, ne_eq, map_eq_zero_iff _ (IsFractionRing.injective B L)]
        exact hπB_irr.ne_zero
      · exact hr_L_ne

theorem hensel_uniformizer_construction
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (m a : ℕ) (hma : Module.finrank K L = m * (AKLB_residueChar A) ^ a)
    (hm : ¬ (AKLB_residueChar A ∣ m)) :
    ∃ (πA_img : K) (π : L),
      π ^ m = algebraMap K L πA_img ∧
      algebraMap K L πA_img ≠ 0 ∧
      π ≠ 0 ∧
      Module.finrank K (IntermediateField.adjoin K ({π} : Set L)) = m ∧
      Module.finrank (IntermediateField.adjoin K ({π} : Set L)) L =
        (AKLB_residueChar A) ^ a ∧
      (∃ πA : A, Irreducible πA ∧ algebraMap A K πA = πA_img) := by


  have core : ∃ (πA_img : K) (π : L),
      π ^ m = algebraMap K L πA_img ∧
      algebraMap K L πA_img ≠ 0 ∧
      π ≠ 0 ∧
      Module.finrank K (IntermediateField.adjoin K ({π} : Set L)) = m ∧
      (∃ πA : A, Irreducible πA ∧ algebraMap A K πA = πA_img) := by


    obtain ⟨ϖ, π, hϖ_irr, hπ_pow, hπ_ne⟩ :=
      hensel_dvr_mth_root_of_uniformizer A K B L htotram m hm
        ⟨(AKLB_residueChar A) ^ a, hma⟩

    have hπA_img_ne : algebraMap K L (algebraMap A K ϖ) ≠ 0 := by
      simp only [ne_eq, map_eq_zero]
      rw [← map_zero (algebraMap A K)]
      exact (IsFractionRing.injective A K).ne hϖ_irr.ne_zero


    have step_iii : Module.finrank K (IntermediateField.adjoin K ({π} : Set L)) = m := by

      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · simp only [zero_mul] at hma
          linarith [Module.finrank_pos (R := K) (M := L)]
        · exact h
      have hm_ne : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm_pos

      open Polynomial in
      have heis : (X ^ m - C ϖ : Polynomial A).IsEisensteinAt
          (IsLocalRing.maximalIdeal A) := by
        apply (monic_X_pow_sub_C ϖ hm_ne).isEisensteinAt_of_mem_of_notMem
        · exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
        · intro n hn
          rw [natDegree_X_pow_sub_C] at hn
          simp only [coeff_sub, coeff_X_pow, coeff_C,
            if_neg (Nat.ne_of_lt hn), zero_sub, neg_mem_iff]
          split_ifs with h0
          · subst h0; rw [IsLocalRing.mem_maximalIdeal]; exact hϖ_irr.1
          · exact (IsLocalRing.maximalIdeal A).zero_mem
        · simp only [coeff_sub, coeff_X_pow, coeff_C, eq_comm, hm_ne, if_false,
            if_true, zero_sub]
          rw [Ideal.neg_mem_iff, hϖ_irr.maximalIdeal_eq, Ideal.span_singleton_pow,
            Ideal.mem_span_singleton]
          intro ⟨a, ha⟩; rw [sq, mul_assoc] at ha
          exact hϖ_irr.1 (IsUnit.of_mul_eq_one a
            (mul_left_cancel₀ hϖ_irr.ne_zero (by rw [mul_one]; exact ha)).symm)

      open Polynomial in
      have hirr_A : Irreducible (X ^ m - C ϖ : Polynomial A) :=
        heis.irreducible inferInstance (monic_X_pow_sub_C ϖ hm_ne).isPrimitive
          (by rw [natDegree_X_pow_sub_C]; exact hm_pos)

      open Polynomial in
      have hirr_K : Irreducible (X ^ m - C (algebraMap A K ϖ) : Polynomial K) := by
        have := (monic_X_pow_sub_C ϖ hm_ne).irreducible_iff_irreducible_map_fraction_map
          (K := K) |>.mp hirr_A
        simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C] at this
        exact this

      open Polynomial in
      have hroot : aeval π (X ^ m - C (algebraMap A K ϖ) : Polynomial K) = 0 := by
        simp [map_sub, map_pow, aeval_X, aeval_C, hπ_pow]

      open Polynomial in
      have hminpoly : (X ^ m - C (algebraMap A K ϖ) : Polynomial K) = minpoly K π :=
        minpoly.eq_of_irreducible_of_monic hirr_K hroot
          (monic_X_pow_sub_C (algebraMap A K ϖ) hm_ne)

      open Polynomial in
      have hdeg : (minpoly K π).natDegree = m := by
        rw [← hminpoly, natDegree_X_pow_sub_C]

      rw [IntermediateField.adjoin.finrank (IsIntegral.of_finite K π), hdeg]
    exact ⟨algebraMap A K ϖ, π, hπ_pow, hπA_img_ne, hπ_ne, step_iii, ⟨ϖ, hϖ_irr, rfl⟩⟩


  obtain ⟨πA_img, π, hπm, hπA_ne, hπ_ne, hrank_Kπ, hπA_irr_info⟩ := core
  refine ⟨πA_img, π, hπm, hπA_ne, hπ_ne, hrank_Kπ, ?_, hπA_irr_info⟩


  set F := IntermediateField.adjoin K ({π} : Set L)
  have htower : Module.finrank K L = Module.finrank K F * Module.finrank F L := by
    rw [← Module.finrank_mul_finrank K (↥F) L]
  rw [hma, hrank_Kπ] at htower


  have hm_pos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · simp only [zero_mul] at hma
      linarith [Module.finrank_pos (R := K) (M := L)]
    · exact h
  exact mul_left_cancel₀ (Nat.pos_iff_ne_zero.mp hm_pos) htower.symm

theorem hensel_dvr_mth_root_in_subext
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (m : ℕ) (hm_pos : 0 < m) (hm : ¬ (AKLB_residueChar A ∣ m))
    (T : IntermediateField K L)
    (hT_deg : Module.finrank K T = m) :
    ∃ (ϖ : A) (α₀ : T), Irreducible ϖ ∧
      (α₀ : L) ^ m = algebraMap K L (algebraMap A K ϖ) ∧
      (α₀ : L) ≠ 0 := by sorry

theorem sub_ext_uniformizer_adjust
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (πA : A) (hπA_irr : Irreducible πA)
    (m : ℕ) (hm_pos : 0 < m) (hm : ¬ (AKLB_residueChar A ∣ m))
    (T : IntermediateField K L)
    (hT_deg : Module.finrank K T = m)
    (ϖ : A) (hϖ_irr : Irreducible ϖ)
    (α₀ : T) (hα₀ : (α₀ : L) ^ m = algebraMap K L (algebraMap A K ϖ)) :
    ∃ (πA₁ : A) (α₁ : T) (u : Aˣ),
      Irreducible πA₁ ∧
      (α₁ : L) ^ m = algebraMap K L (algebraMap A K πA₁) ∧
      πA = (u : A) * πA₁ ∧
      ((u : A) - 1 ∈ IsLocalRing.maximalIdeal A) := by sorry

set_option maxHeartbeats 800000 in
theorem hensel_mth_root_in_subext
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (πA : A) (hπA_irr : Irreducible πA)
    (m : ℕ) (hm_pos : 0 < m) (hm : ¬ (AKLB_residueChar A ∣ m))
    (T : IntermediateField K L)
    (hT_deg : Module.finrank K T = m) :
    ∃ α₀ : T, (α₀ : L) ^ m = algebraMap K L (algebraMap A K πA) := by

  by_cases hm1 : m = 1
  · subst hm1
    exact ⟨⟨algebraMap K L (algebraMap A K πA), T.algebraMap_mem _⟩, pow_one _⟩

  have hm_ge2 : 1 < m := by omega

  obtain ⟨ϖ, α₀, hϖ_irr, hα₀_pow, _⟩ :=
    hensel_dvr_mth_root_in_subext A K B L htotram m hm_pos hm T hT_deg

  obtain ⟨πA₁, α₁, u, hπA₁_irr, hα₁_pow, hπA_eq, hu_mod⟩ :=
    sub_ext_uniformizer_adjust A K B L htotram πA hπA_irr m hm_pos hm T hT_deg
      ϖ hϖ_irr α₀ hα₀_pow

  obtain ⟨v, hv_pow⟩ := hensel_unit_nth_root_of_one_mod A m hm_ge2
    (by rwa [AKLB_residueChar] at hm) u hu_mod

  set v_K := algebraMap A K (v : A) with hv_K_def
  set v_L := algebraMap K L v_K with hv_L_def
  have hv_in_T : v_L ∈ (T : Set L) := T.algebraMap_mem v_K
  refine ⟨⟨v_L * (α₁ : L), T.mul_mem hv_in_T α₁.prop⟩, ?_⟩

  show (v_L * (α₁ : L)) ^ m = algebraMap K L (algebraMap A K πA)
  rw [mul_pow, hα₁_pow]
  rw [hv_L_def, hv_K_def, ← map_pow, ← map_pow, hv_pow]
  rw [← map_mul, ← map_mul, hπA_eq]

theorem subExtNewtonApproxInIntermediate
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (πA : A) (hπA_irr : Irreducible πA)
    (m : ℕ) (hm : ¬ (AKLB_residueChar A ∣ m))
    (T : IntermediateField K L)
    (hT_deg : Module.finrank K T = m) :
    ∃ (ϖ : A) (α₀ : T) (u : Aˣ),
      Irreducible ϖ ∧
      (α₀ : L) ^ m = algebraMap K L (algebraMap A K ϖ) ∧
      πA = (u : A) * ϖ ∧
      ((u : A) - 1 ∈ IsLocalRing.maximalIdeal A) := by
  have hm_pos : 0 < m := by
    have : 0 < Module.finrank K (T : Type _) := Module.finrank_pos (R := K) (M := T)
    omega
  obtain ⟨α₀, hα₀⟩ := hensel_mth_root_in_subext A K B L htotram πA hπA_irr m hm_pos hm T hT_deg
  exact ⟨πA, α₀, 1, hπA_irr, hα₀, by simp, by
    show (1 : A) - 1 ∈ IsLocalRing.maximalIdeal A
    simp [(IsLocalRing.maximalIdeal A).zero_mem]⟩

theorem rootInIntermediate_of_totallyRamified
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (πA_img : K) (_hπA : algebraMap K L πA_img ≠ 0)
    (hπA_img : ∃ πA : A, Irreducible πA ∧ algebraMap A K πA = πA_img)
    (m : ℕ) (hm : ¬ (AKLB_residueChar A ∣ m))
    (T : IntermediateField K L)
    (hT_deg : Module.finrank K T = m) :
    ∃ α : T, (α : L) ^ m = algebraMap K L πA_img := by

  obtain ⟨πA, hπA_irr, hπA_eq⟩ := hπA_img

  have hm_pos : 0 < m := by
    have : 0 < Module.finrank K (T : Type _) := Module.finrank_pos (R := K) (M := T)
    omega

  by_cases hm1 : m = 1
  · subst hm1
    exact ⟨⟨algebraMap K L πA_img, T.algebraMap_mem πA_img⟩, pow_one _⟩

  have hm_ge2 : 1 < m := by omega

  obtain ⟨ϖ, α₀, u, hϖ_irr, hα₀_pow, hπA_eq_uϖ, hu_mod⟩ :=
    subExtNewtonApproxInIntermediate A K B L htotram πA hπA_irr m hm T hT_deg

  obtain ⟨v, hv_pow⟩ := hensel_unit_nth_root_of_one_mod A m hm_ge2
    (by rwa [AKLB_residueChar] at hm) u hu_mod

  set v_K := algebraMap A K (v : A) with hv_K_def
  set v_L := algebraMap K L v_K with hv_L_def
  have hv_in_T : v_L ∈ (T : Set L) := T.algebraMap_mem v_K
  refine ⟨⟨v_L * (α₀ : L), T.mul_mem hv_in_T α₀.prop⟩, ?_⟩

  show (v_L * (α₀ : L)) ^ m = algebraMap K L πA_img
  rw [mul_pow, hα₀_pow]

  rw [hv_L_def, hv_K_def, ← map_pow, ← map_pow, hv_pow]

  rw [← map_mul, ← map_mul, ← hπA_eq, hπA_eq_uϖ]

theorem uniformizerPreimage
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (πA_img : K) (hπA : algebraMap K L πA_img ≠ 0)
    (hπA_img : ∃ πA : A, Irreducible πA ∧ algebraMap A K πA = πA_img) :
    ∃ πA : A, algebraMap A K πA = πA_img ∧
      πA ∈ IsLocalRing.maximalIdeal A ∧
      πA ∉ (IsLocalRing.maximalIdeal A) ^ 2 := by
  obtain ⟨πA, hπA_irr, hπA_eq⟩ := hπA_img
  refine ⟨πA, hπA_eq, ?_, ?_⟩
  ·
    have h := hπA_irr.maximalIdeal_eq (R := A)
    rw [h]
    exact Ideal.subset_span (Set.mem_singleton πA)
  ·
    have h := hπA_irr.maximalIdeal_eq (R := A)
    rw [h, Ideal.span_singleton_pow]
    intro hmem
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hne : πA ≠ 0 := hπA_irr.ne_zero
    have h1 : πA * (πA * c) = πA := by
      calc πA * (πA * c) = πA ^ 2 * c := by ring
      _ = πA := hc.symm
    have h2 : πA * c = 1 :=
      mul_left_cancel₀ hne (h1.trans (mul_one πA).symm)
    exact hπA_irr.not_isUnit ⟨⟨πA, c, h2, by rw [mul_comm]; exact h2⟩, rfl⟩

theorem irreducible_xm_sub_uniformizer
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (πA_img : K) (hπA : algebraMap K L πA_img ≠ 0)
    (hπA_img : ∃ πA : A, Irreducible πA ∧ algebraMap A K πA = πA_img)
    (m : ℕ) (hm : ¬ (AKLB_residueChar A ∣ m))
    (hm_pos : 0 < m) :
    Irreducible (Polynomial.X ^ m - Polynomial.C πA_img : Polynomial K) := by

  obtain ⟨πA, hπA_eq, hπA_mem, hπA_sq⟩ :=
    uniformizerPreimage A K B L htotram πA_img hπA hπA_img

  set f : Polynomial A := Polynomial.X ^ m - Polynomial.C πA with hf_def

  have hf_monic : f.Monic := Polynomial.monic_X_pow_sub_C πA (by omega)

  have hf_deg : f.natDegree = m := Polynomial.natDegree_X_pow_sub_C

  have hf_eis : f.IsEisensteinAt (IsLocalRing.maximalIdeal A) := by
    constructor
    ·
      rw [Polynomial.Monic.leadingCoeff hf_monic]
      exact fun h => (IsLocalRing.maximalIdeal.isMaximal (R := A)).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h isUnit_one)
    ·
      intro n hn
      rw [hf_deg] at hn
      simp only [f, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
      have hne : n ≠ m := by omega
      simp only [if_neg hne]
      by_cases h0 : n = 0
      · simp [h0, hπA_mem]
      · simp [h0]
    ·
      simp only [f, Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
      have hne : (0 : ℕ) ≠ m := by omega
      simp only [if_neg hne, zero_sub]
      intro h
      exact hπA_sq (neg_mem_iff.mp h)

  have hirr_A : Irreducible f :=
    hf_eis.irreducible (IsLocalRing.maximalIdeal.isMaximal (R := A)).isPrime
      hf_monic.isPrimitive (by rw [hf_deg]; omega)

  have hirr_K : Irreducible (f.map (algebraMap A K)) :=
    hf_monic.irreducible_iff_irreducible_map_fraction_map.mp hirr_A

  have hmap : f.map (algebraMap A K) = Polynomial.X ^ m - Polynomial.C πA_img := by
    simp [f, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, hπA_eq]
  rwa [hmap] at hirr_K

theorem intermediateField_generatedByRoot
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (πA_img : K) (hπA : algebraMap K L πA_img ≠ 0)
    (hπA_img : ∃ πA : A, Irreducible πA ∧ algebraMap A K πA = πA_img)
    (m : ℕ) (hm : ¬ (AKLB_residueChar A ∣ m))
    (T : IntermediateField K L)
    (hT_deg : Module.finrank K T = m) :
    ∃ (α : L),
      α ^ m = algebraMap K L πA_img ∧
      T = IntermediateField.adjoin K ({α} : Set L) := by

  have hm_pos : 0 < m := by
    have : 0 < Module.finrank K (T : Type _) := Module.finrank_pos (R := K) (M := T)
    omega


  obtain ⟨⟨α, hα_mem⟩, hα_pow⟩ :=
    rootInIntermediate_of_totallyRamified A K B L htotram πA_img hπA hπA_img m hm T hT_deg

  have hirr := irreducible_xm_sub_uniformizer
    A K B L htotram πA_img hπA hπA_img m hm hm_pos

  have hα_int : IsIntegral K (α : L) := IsIntegral.of_finite K (α : L)

  have hα_root : Polynomial.aeval (α : L) (Polynomial.X ^ m - Polynomial.C πA_img) = 0 := by
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hα_pow, sub_self]


  have hminpoly_eq : minpoly K (α : L) = Polynomial.X ^ m - Polynomial.C πA_img := by
    have hmonic : (Polynomial.X ^ m - Polynomial.C πA_img : Polynomial K).Monic :=
      Polynomial.monic_X_pow_sub_C _ (by omega)
    exact (minpoly.eq_of_irreducible_of_monic hirr hα_root hmonic).symm

  have hfinrank_adjoin : Module.finrank K (IntermediateField.adjoin K ({(α : L)} : Set L)) = m := by
    rw [IntermediateField.adjoin.finrank hα_int, hminpoly_eq,
        Polynomial.natDegree_X_pow_sub_C]

  have h_le : IntermediateField.adjoin K ({(α : L)} : Set L) ≤ T := by
    exact IntermediateField.adjoin_le_iff.mpr (by simp [hα_mem])

  have h_eq : IntermediateField.adjoin K ({(α : L)} : Set L) = T := by
    haveI : FiniteDimensional K T := by
      exact Module.finite_of_finrank_pos (by omega : 0 < Module.finrank K ↥T)
    exact IntermediateField.eq_of_le_of_finrank_eq h_le (by rw [hfinrank_adjoin, hT_deg])
  exact ⟨α, hα_pow, h_eq.symm⟩

theorem tameWildDecomposition_existence
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (m a : ℕ) (hma : Module.finrank K L = m * (AKLB_residueChar A) ^ a)
    (hm : ¬ (AKLB_residueChar A ∣ m)) :
    ∃ (T : IntermediateField K L),
      Module.finrank K T = m ∧
      Module.finrank T L = (AKLB_residueChar A) ^ a := by
  obtain ⟨πA_img, π, _, _, _, hT_deg, hT_wild, _⟩ :=
    hensel_uniformizer_construction A K B L htotram m a hma hm

  exact ⟨IntermediateField.adjoin K ({π} : Set L), hT_deg, hT_wild⟩

theorem tameWildDecomposition_uniqueness
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (m a : ℕ) (hma : Module.finrank K L = m * (AKLB_residueChar A) ^ a)
    (hm : ¬ (AKLB_residueChar A ∣ m))
    (T₁ T₂ : IntermediateField K L)
    (hT₁_deg : Module.finrank K T₁ = m)
    (_hT₁_wild : Module.finrank T₁ L = (AKLB_residueChar A) ^ a)
    (hT₂_deg : Module.finrank K T₂ = m)
    (_hT₂_wild : Module.finrank T₂ L = (AKLB_residueChar A) ^ a) :

    T₁ = T₂ := by

  obtain ⟨πA_img, π₀, hπ₀_pow, hπA_ne, hπ₀_ne, _, _, hπA_irr_info⟩ :=
    hensel_uniformizer_construction A K B L htotram m a hma hm

  obtain ⟨α, hα_pow, hT₁_eq⟩ :=
    intermediateField_generatedByRoot A K B L htotram πA_img hπA_ne hπA_irr_info m hm T₁ hT₁_deg
  obtain ⟨β, hβ_pow, hT₂_eq⟩ :=
    intermediateField_generatedByRoot A K B L htotram πA_img hπA_ne hπA_irr_info m hm T₂ hT₂_deg


  have hζ_root : (α * β⁻¹) ^ m = 1 :=
    ratio_pow_eq_one α β (algebraMap K L πA_img) m hα_pow hβ_pow hπA_ne

  obtain ⟨ζ₀, hζ₀⟩ := roots_of_unity_in_base_of_totally_ramified
    A K B L htotram m hm (α * β⁻¹) hζ_root

  have hm_ne : m ≠ 0 := by
    intro h; subst h
    have : Module.finrank K (T₁ : Type _) ≥ 1 := Module.finrank_pos (R := K) (M := T₁)
    omega
  have hα_ne : α ≠ 0 := by
    intro h; apply hπA_ne; rw [← hα_pow, h, zero_pow hm_ne]
  have hβ_ne : β ≠ 0 := by
    intro h; apply hπA_ne; rw [← hβ_pow, h, zero_pow hm_ne]
  have hα_eq_ζβ : algebraMap K L ζ₀ * β = α := by
    rw [hζ₀, mul_assoc, inv_mul_cancel₀ hβ_ne, mul_one]
  have hβ_eq_ζα : algebraMap K L ζ₀⁻¹ * α = β := by
    rw [map_inv₀, hζ₀, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel₀ hα_ne, mul_one]


  have hadj_eq : IntermediateField.adjoin K ({α} : Set L) =
      IntermediateField.adjoin K ({β} : Set L) :=
    IntermediateField.adjoin_singleton_eq_of_smul α β ⟨ζ₀, hα_eq_ζβ⟩ ⟨ζ₀⁻¹, hβ_eq_ζα⟩

  rw [hT₁_eq, hT₂_eq, hadj_eq]

theorem tameWildDecomposition
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (htotram : AKLB_ramIdx A B = Module.finrank K L)
    (hn : 0 < Module.finrank K L) :
    ∃! (T : IntermediateField K L),
      ∃ (m a : ℕ), Module.finrank K L = m * (AKLB_residueChar A) ^ a ∧
        ¬ (AKLB_residueChar A ∣ m) ∧
        Module.finrank K T = m ∧
        Module.finrank T L = AKLB_residueChar A ^ a := by
  set p := AKLB_residueChar A with hp_def
  set e := Module.finrank K L with he_def
  have he_ne : e ≠ 0 := by omega
  have hp_or := residueChar_prime_or_zero (IsLocalRing.ResidueField A)

  obtain ⟨m, a, hdecomp, hm⟩ := padic_decomp_exists e he_ne p hp_or

  obtain ⟨T, hT_deg, hT_wild⟩ :=
    tameWildDecomposition_existence A K B L htotram m a hdecomp hm

  refine ⟨T, ⟨m, a, hdecomp, hm, hT_deg, hT_wild⟩, ?_⟩
  intro T' ⟨m', a', hdecomp', hm', hT'_deg, hT'_wild⟩

  have ⟨hm_eq, ha_eq⟩ := padic_decomp_unique_tower p hp_or he_ne hdecomp hm hdecomp' hm'
  subst hm_eq; subst ha_eq

  exact (tameWildDecomposition_uniqueness A K B L htotram m a hdecomp hm
    T T' hT_deg hT_wild hT'_deg hT'_wild).symm

end TameWildDecompositionTotallyRamified

section TameWildDecompositionGeneral

noncomputable def intClE_to_L_algHom
    (A : Type*) [CommRing A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (E : IntermediateField K L) :
    ↥(integralClosure A ↥E) →ₐ[A] L :=
  (E.val.restrictScalars A).comp (integralClosure A ↥E).val

noncomputable def intClE_to_B_algHom
    (A : Type*) [CommRing A] [IsDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    {L : Type*} [Field L] [Algebra K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    (E : IntermediateField K L) :
    ↥(integralClosure A ↥E) →ₐ[A] B := by
  letI : Algebra ↥(integralClosure A ↥E) L :=
    (intClE_to_L_algHom A E).toAlgebra
  haveI : IsScalarTower A ↥(integralClosure A ↥E) L :=
    IsScalarTower.of_algHom (intClE_to_L_algHom A E)
  haveI : Algebra.IsIntegral A ↥(integralClosure A ↥E) :=
    integralClosure.AlgebraIsIntegral
  exact IsIntegralClosure.lift A B L

noncomputable def ramIdx_sub
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (E : IntermediateField K L) : ℕ := by
  haveI : IsDiscreteValuationRing ↥(integralClosure A ↥E) :=
    AKLB_intClE_isDVR A K L E
  exact (IsLocalRing.maximalIdeal A).ramificationIdx
    (IsLocalRing.maximalIdeal ↥(integralClosure A ↥E))

noncomputable def ramIdx_over
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (E : IntermediateField K L) : ℕ := by
  haveI : IsDiscreteValuationRing ↥(integralClosure A ↥E) :=
    AKLB_intClE_isDVR A K L E
  letI : Algebra ↥(integralClosure A ↥E) B :=
    (intClE_to_B_algHom A B E).toAlgebra
  exact (IsLocalRing.maximalIdeal ↥(integralClosure A ↥E)).ramificationIdx
    (IsLocalRing.maximalIdeal B)

theorem ramIdx_mul
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (E : IntermediateField K L) :
    AKLB_ramIdx A B = ramIdx_over A B E * ramIdx_sub A B E := by

  set C := integralClosure A ↥E
  haveI hDVR : IsDiscreteValuationRing ↥C := AKLB_intClE_isDVR A K L E

  letI : Algebra ↥C B := (intClE_to_B_algHom A B E).toAlgebra
  haveI : IsScalarTower A ↥C B := IsScalarTower.of_algHom (intClE_to_B_algHom A B E)

  set p := IsLocalRing.maximalIdeal A
  set P := IsLocalRing.maximalIdeal ↥C
  set Q := IsLocalRing.maximalIdeal B

  show p.ramificationIdx Q = P.ramificationIdx Q * p.ramificationIdx P


  have hinj_CB : Function.Injective (algebraMap ↥C B) := by


    change Function.Injective (intClE_to_B_algHom A B E)
    intro x y hxy

    have hinj_L : Function.Injective (intClE_to_L_algHom A E) := by
      intro a b hab
      unfold intClE_to_L_algHom at hab
      simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars'] at hab
      exact Subtype.val_injective (Subtype.val_injective hab)
    apply hinj_L


    have hBL : Function.Injective (algebraMap B L) := IsFractionRing.injective B L


    have key : ∀ z : ↥C, (intClE_to_L_algHom A E) z =
        algebraMap B L (intClE_to_B_algHom A B E z) := by
      intro z
      unfold intClE_to_B_algHom
      letI : Algebra ↥C L := (intClE_to_L_algHom A E).toAlgebra
      haveI : IsScalarTower A ↥C L := IsScalarTower.of_algHom (intClE_to_L_algHom A E)
      haveI : Algebra.IsIntegral A ↥C := integralClosure.AlgebraIsIntegral
      rw [IsIntegralClosure.algebraMap_lift A B L z]
      rfl
    rw [key x, key y, hxy]

  haveI : FaithfulSMul ↥C B :=
    (faithfulSMul_iff_algebraMap_injective ↥C B).mpr hinj_CB
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  haveI : Algebra.IsIntegral ↥C B := Algebra.IsIntegral.tower_top A
  haveI : IsLocalHom (algebraMap ↥C B) := Algebra.IsIntegral.isLocalHom ↥C B

  have hg : Ideal.map (algebraMap ↥C B) P ≤ Q :=
    IsLocalRing.map_maximalIdeal_le (algebraMap ↥C B)

  have hg0 : Ideal.map (algebraMap ↥C B) P ≠ ⊥ := by
    haveI : Module.IsTorsionFree ↥C B :=
      (Module.isTorsionFree_iff_faithfulSMul).mpr inferInstance
    exact Ideal.map_ne_bot_of_ne_bot (IsDiscreteValuationRing.not_a_field ↥C)

  have hfg : Ideal.map (algebraMap A B) p ≠ ⊥ := by
    intro h; apply IsDiscreteValuationRing.not_a_field A; rw [eq_bot_iff]
    intro x hx; rw [Submodule.mem_bot]; by_contra hx0
    have hmem := Ideal.mem_map_of_mem (algebraMap A B) hx; rw [h] at hmem
    exact hx0 (FaithfulSMul.algebraMap_injective A B
      (by rw [Ideal.mem_bot.mp hmem, map_zero]))
  rw [Ideal.ramificationIdx_algebra_tower hg0 hfg hg, mul_comm]

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 80000 in

theorem ramIdx_over_eq_finrank_of_above_maxUnram
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (E : IntermediateField K L)
    (hE : maximalUnramifiedSubextension A K L ≤ E) :
    ramIdx_over A B E = Module.finrank E L := by

  set F₀ := maximalUnramifiedSubextension A K L
  set C_E := integralClosure A ↥E
  haveI hDVR_CE : IsDiscreteValuationRing ↥C_E := AKLB_intClE_isDVR A K L E

  letI algCEB : Algebra ↥C_E B := (intClE_to_B_algHom A B E).toAlgebra
  haveI : IsScalarTower A ↥C_E B := IsScalarTower.of_algHom (intClE_to_B_algHom A B E)

  have hinj_CB : Function.Injective (algebraMap ↥C_E B) := by
    change Function.Injective (intClE_to_B_algHom A B E)
    intro x y hxy
    have hinj_L : Function.Injective (intClE_to_L_algHom A E) := by
      intro a b hab
      unfold intClE_to_L_algHom at hab
      simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars'] at hab
      exact Subtype.val_injective (Subtype.val_injective hab)
    apply hinj_L
    have key : ∀ z : ↥C_E, (intClE_to_L_algHom A E) z =
        algebraMap B L (intClE_to_B_algHom A B E z) := by
      intro z
      unfold intClE_to_B_algHom
      letI : Algebra ↥C_E L := (intClE_to_L_algHom A E).toAlgebra
      haveI : IsScalarTower A ↥C_E L := IsScalarTower.of_algHom (intClE_to_L_algHom A E)
      haveI : Algebra.IsIntegral A ↥C_E := integralClosure.AlgebraIsIntegral
      rw [IsIntegralClosure.algebraMap_lift A B L z]
      rfl
    rw [key x, key y, hxy]
  haveI : FaithfulSMul ↥C_E B :=
    (faithfulSMul_iff_algebraMap_injective ↥C_E B).mpr hinj_CB
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  haveI : Algebra.IsIntegral ↥C_E B := Algebra.IsIntegral.tower_top A
  haveI : IsLocalHom (algebraMap ↥C_E B) := Algebra.IsIntegral.isLocalHom ↥C_E B
  haveI : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal ↥C_E) :=
    IsLocalRing.ResidueField.instLiesOverMaximalIdeal
  haveI : FiniteDimensional K ↥E := IntermediateField.finiteDimensional_left E
  haveI : FiniteDimensional (↥E) L := IntermediateField.finiteDimensional_right E
  haveI : Algebra.IsSeparable K ↥E := IntermediateField.isSeparable_tower_bot K E
  haveI : IsFractionRing ↥C_E ↥E :=
    integralClosure.isFractionRing_of_finite_extension K ↥E
  haveI : IsNoetherian A ↥C_E :=
    IsIntegralClosure.isNoetherian A K ↥E (integralClosure A ↥E)
  haveI : Module.Finite A ↥C_E := inferInstance
  letI algCEL : Algebra ↥C_E L := (intClE_to_L_algHom A E).toAlgebra
  haveI : IsScalarTower A ↥C_E L := IsScalarTower.of_algHom (intClE_to_L_algHom A E)
  haveI : IsScalarTower ↥C_E ↥E L := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    show algebraMap ↥E L (algebraMap ↥C_E ↥E x) = (intClE_to_L_algHom A E) x
    unfold intClE_to_L_algHom
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', Subalgebra.coe_val]
    rfl
  haveI : IsScalarTower ↥C_E B L := by
    apply IsScalarTower.of_algebraMap_eq
    intro x


    change (intClE_to_L_algHom A E) x = algebraMap B L (intClE_to_B_algHom A B E x)
    unfold intClE_to_B_algHom
    letI : Algebra ↥C_E L := (intClE_to_L_algHom A E).toAlgebra
    haveI : IsScalarTower A ↥C_E L := IsScalarTower.of_algHom (intClE_to_L_algHom A E)
    haveI : Algebra.IsIntegral A ↥C_E := integralClosure.AlgebraIsIntegral
    rw [IsIntegralClosure.algebraMap_lift A B L x]; rfl

  haveI : IsDedekindDomain ↥C_E := by
    haveI : Ring.DimensionLEOne ↥C_E :=
      Ring.DimensionLEOne.isIntegralClosure A ↥E (integralClosure A ↥E)
    haveI : IsIntegrallyClosed ↥C_E :=
      integralClosure.isIntegrallyClosedOfFiniteExtension K
    exact {}
  haveI : Module.Finite ↥C_E B := Module.Finite.of_restrictScalars_finite A ↥C_E B
  have hCE_ne_bot : IsLocalRing.maximalIdeal ↥C_E ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field ↥C_E

  have hfund := @Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
    (↥C_E) C_E.toCommRing B _ algCEB _ (↥E) L _ _ ‹IsDedekindDomain ↥C_E› _
    ‹IsFractionRing ↥C_E ↥E› _ _ _ algCEL ‹IsScalarTower ↥C_E B L›
    ‹IsScalarTower ↥C_E ↥E L› ‹Module.Finite ↥C_E B› _ _ _ hCE_ne_bot

  rw [Ideal.inertiaDeg_algebraMap] at hfund


  set C_F₀ := integralClosure A ↥F₀
  haveI hDVR_CF₀ : IsDiscreteValuationRing ↥C_F₀ := AKLB_intClE_isDVR A K L F₀

  obtain ⟨E₀, hE₀_unram, hE₀_deg, hE₀_max, _⟩ := thm_10_13_maxUnram_eq_resDeg A K B L

  have hF₀_eq_E₀ : F₀ = E₀ := by
    apply le_antisymm
    · exact iSup₂_le fun E hE => hE₀_max E hE
    · exact le_iSup₂ (f := fun E (_ : IsFiniteUnramifiedSubext A K L E) => E) E₀ hE₀_unram
  subst hF₀_eq_E₀

  letI algCF₀B : Algebra ↥C_F₀ B := (intClE_to_B_algHom A B F₀).toAlgebra
  haveI inst_st_A_CF₀_B : IsScalarTower A ↥C_F₀ B :=
    IsScalarTower.of_algHom (intClE_to_B_algHom A B F₀)

  have hinj_CF₀B : Function.Injective (algebraMap ↥C_F₀ B) := by
    change Function.Injective (intClE_to_B_algHom A B F₀)
    intro x y hxy
    have hinj_L : Function.Injective (intClE_to_L_algHom A F₀) := by
      intro a b hab
      unfold intClE_to_L_algHom at hab
      simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars'] at hab
      exact Subtype.val_injective (Subtype.val_injective hab)
    apply hinj_L
    have key : ∀ z : ↥C_F₀, (intClE_to_L_algHom A F₀) z =
        algebraMap B L (intClE_to_B_algHom A B F₀ z) := by
      intro z; unfold intClE_to_B_algHom
      letI : Algebra ↥C_F₀ L := (intClE_to_L_algHom A F₀).toAlgebra
      haveI : IsScalarTower A ↥C_F₀ L := IsScalarTower.of_algHom (intClE_to_L_algHom A F₀)
      haveI : Algebra.IsIntegral A ↥C_F₀ := integralClosure.AlgebraIsIntegral
      rw [IsIntegralClosure.algebraMap_lift A B L z]; rfl
    rw [key x, key y, hxy]

  haveI : FaithfulSMul ↥C_F₀ B :=
    (faithfulSMul_iff_algebraMap_injective ↥C_F₀ B).mpr hinj_CF₀B
  haveI : Algebra.IsIntegral ↥C_F₀ B := Algebra.IsIntegral.tower_top A
  haveI inst_lh_CF₀B : IsLocalHom (algebraMap ↥C_F₀ B) :=
    Algebra.IsIntegral.isLocalHom ↥C_F₀ B
  haveI : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal ↥C_F₀) :=
    IsLocalRing.ResidueField.instLiesOverMaximalIdeal

  have hf_CF₀B : Module.finrank
      (IsLocalRing.ResidueField ↥C_F₀) (IsLocalRing.ResidueField B) = 1 :=
    AKLB_resDeg_over_eq_one A K B L F₀ hE₀_unram hE₀_deg


  letI inclF₀E : ↥F₀ →ₐ[A] ↥E :=
    (IntermediateField.inclusion hE).restrictScalars A
  letI algCF₀E : Algebra ↥C_F₀ ↥E :=
    (inclF₀E.comp (integralClosure A ↥F₀).val).toAlgebra
  haveI : IsScalarTower A ↥C_F₀ ↥E :=
    IsScalarTower.of_algHom (inclF₀E.comp (integralClosure A ↥F₀).val)
  haveI : Algebra.IsIntegral A ↥C_F₀ := integralClosure.AlgebraIsIntegral

  let φ_CF₀_CE : ↥C_F₀ →ₐ[A] ↥C_E := IsIntegralClosure.lift A (↥C_E) (↥E)
  letI algCF₀CE : Algebra ↥C_F₀ ↥C_E := φ_CF₀_CE.toAlgebra

  haveI : IsScalarTower ↥C_F₀ ↥C_E B := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    apply IsFractionRing.injective B L

    conv_lhs => rw [show algebraMap ↥C_F₀ B x = intClE_to_B_algHom A B F₀ x from rfl]


    conv_rhs => rw [show algebraMap ↥C_F₀ ↥C_E x = φ_CF₀_CE x from rfl,
                     show algebraMap ↥C_E B (φ_CF₀_CE x) =
                       intClE_to_B_algHom A B E (φ_CF₀_CE x) from rfl]

    unfold intClE_to_B_algHom
    letI algCF₀L' : Algebra ↥C_F₀ L := (intClE_to_L_algHom A F₀).toAlgebra
    haveI : IsScalarTower A ↥C_F₀ L := IsScalarTower.of_algHom (intClE_to_L_algHom A F₀)
    rw [IsIntegralClosure.algebraMap_lift A B L x]
    haveI : Algebra.IsIntegral A ↥C_E := integralClosure.AlgebraIsIntegral
    rw [IsIntegralClosure.algebraMap_lift A B L (φ_CF₀_CE x)]


    show (intClE_to_L_algHom A F₀) x = (intClE_to_L_algHom A E) (φ_CF₀_CE x)
    unfold intClE_to_L_algHom
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', Subalgebra.coe_val]
    have hlift := IsIntegralClosure.algebraMap_lift A (↥C_E) (↥E) x
    change (F₀.val : ↥F₀ → L) ↑x = (E.val : ↥E → L) ↑(φ_CF₀_CE x)

    rw [show (↑(φ_CF₀_CE x) : ↥E) = algebraMap ↥C_E ↥E (φ_CF₀_CE x) from rfl]
    rw [hlift]
    rfl


  haveI : IsLocalHom (algebraMap ↥C_F₀ ↥C_E) := by
    have hcomp : IsLocalHom ((algebraMap ↥C_E B).comp (algebraMap ↥C_F₀ ↥C_E)) := by
      rwa [← IsScalarTower.algebraMap_eq ↥C_F₀ ↥C_E B]
    exact isLocalHom_of_comp _ (algebraMap ↥C_E B)

  haveI : (IsLocalRing.maximalIdeal ↥C_E).LiesOver (IsLocalRing.maximalIdeal ↥C_F₀) :=
    IsLocalRing.ResidueField.instLiesOverMaximalIdeal

  have htower := Ideal.inertiaDeg_algebra_tower
    (IsLocalRing.maximalIdeal ↥C_F₀) (IsLocalRing.maximalIdeal ↥C_E)
    (IsLocalRing.maximalIdeal B)

  rw [Ideal.inertiaDeg_algebraMap, Ideal.inertiaDeg_algebraMap, Ideal.inertiaDeg_algebraMap] at htower


  letI : Algebra (↥C_F₀ ⧸ IsLocalRing.maximalIdeal ↥C_F₀) (B ⧸ IsLocalRing.maximalIdeal B) :=
    Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq
      (IsLocalRing.maximalIdeal_comap (algebraMap ↥C_F₀ B)).symm)
  letI : Module (↥C_F₀ ⧸ IsLocalRing.maximalIdeal ↥C_F₀) (B ⧸ IsLocalRing.maximalIdeal B) :=
    Algebra.toModule
  have hf_CF₀B' : Module.finrank
      (↥C_F₀ ⧸ IsLocalRing.maximalIdeal ↥C_F₀) (B ⧸ IsLocalRing.maximalIdeal B) = 1 :=
    hf_CF₀B

  rw [hf_CF₀B'] at htower


  letI : Algebra (↥C_E ⧸ IsLocalRing.maximalIdeal ↥C_E) (B ⧸ IsLocalRing.maximalIdeal B) :=
    Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq
      (IsLocalRing.maximalIdeal_comap (algebraMap ↥C_E B)).symm)
  letI : Module (↥C_E ⧸ IsLocalRing.maximalIdeal ↥C_E) (B ⧸ IsLocalRing.maximalIdeal B) :=
    Algebra.toModule


  have hf_CEB : Module.finrank
      (↥C_E ⧸ IsLocalRing.maximalIdeal ↥C_E) (B ⧸ IsLocalRing.maximalIdeal B) = 1 := by
    exact Nat.eq_one_of_mul_eq_one_right (Nat.mul_comm _ _ ▸ htower.symm)


  rw [hf_CEB, mul_one] at hfund

  exact hfund

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem tameWildDecomposition_inSubTower
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (m a : ℕ) (hma : AKLB_ramIdx A B = m * (AKLB_residueChar A) ^ a)
    (hm : ¬ (AKLB_residueChar A ∣ m)) :
    ∃ (T : IntermediateField (↥(maximalUnramifiedSubextension A K L)) L),
      Module.finrank T L = (AKLB_residueChar A) ^ a := by

  set F₀ := maximalUnramifiedSubextension A K L with hF₀_def
  set C := integralClosure A ↥F₀ with hC_def

  haveI hDVR_C : IsDiscreteValuationRing ↥C := AKLB_intClE_isDVR A K L F₀
  letI algCB : Algebra ↥C B := (intClE_to_B_algHom A B F₀).toAlgebra
  haveI : IsScalarTower A ↥C B := IsScalarTower.of_algHom (intClE_to_B_algHom A B F₀)
  have hinj_CB : Function.Injective (algebraMap ↥C B) := by
    change Function.Injective (intClE_to_B_algHom A B F₀)
    intro x y hxy
    have hinj_L : Function.Injective (intClE_to_L_algHom A F₀) := by
      intro a b hab
      unfold intClE_to_L_algHom at hab
      simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars'] at hab
      exact Subtype.val_injective (Subtype.val_injective hab)
    apply hinj_L
    have key : ∀ z : ↥C, (intClE_to_L_algHom A F₀) z =
        algebraMap B L (intClE_to_B_algHom A B F₀ z) := by
      intro z
      unfold intClE_to_B_algHom
      letI : Algebra ↥C L := (intClE_to_L_algHom A F₀).toAlgebra
      haveI : IsScalarTower A ↥C L := IsScalarTower.of_algHom (intClE_to_L_algHom A F₀)
      haveI : Algebra.IsIntegral A ↥C := integralClosure.AlgebraIsIntegral
      rw [IsIntegralClosure.algebraMap_lift A B L z]
      rfl
    rw [key x, key y, hxy]
  haveI : FaithfulSMul ↥C B :=
    (faithfulSMul_iff_algebraMap_injective ↥C B).mpr hinj_CB
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  haveI : Algebra.IsIntegral ↥C B := Algebra.IsIntegral.tower_top A
  haveI : IsLocalHom (algebraMap ↥C B) := Algebra.IsIntegral.isLocalHom ↥C B
  haveI : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal ↥C) :=
    IsLocalRing.ResidueField.instLiesOverMaximalIdeal
  haveI : FiniteDimensional K ↥F₀ := IntermediateField.finiteDimensional_left F₀
  haveI : FiniteDimensional (↥F₀) L := IntermediateField.finiteDimensional_right F₀
  haveI : Algebra.IsSeparable K ↥F₀ := IntermediateField.isSeparable_tower_bot K F₀
  haveI : IsFractionRing ↥C ↥F₀ :=
    integralClosure.isFractionRing_of_finite_extension K ↥F₀
  haveI : IsNoetherian A ↥C :=
    IsIntegralClosure.isNoetherian A K ↥F₀ (integralClosure A ↥F₀)
  haveI : Module.Finite A ↥C := inferInstance
  letI algCL : Algebra ↥C L := (intClE_to_L_algHom A F₀).toAlgebra
  haveI : IsScalarTower A ↥C L := IsScalarTower.of_algHom (intClE_to_L_algHom A F₀)
  haveI : IsScalarTower ↥C ↥F₀ L := by
    apply IsScalarTower.of_algebraMap_eq; intro x
    show algebraMap ↥F₀ L (algebraMap ↥C ↥F₀ x) = (intClE_to_L_algHom A F₀) x
    unfold intClE_to_L_algHom
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', Subalgebra.coe_val]; rfl
  haveI : IsScalarTower ↥C B L := by
    apply IsScalarTower.of_algebraMap_eq; intro x
    change (intClE_to_L_algHom A F₀) x = algebraMap B L (intClE_to_B_algHom A B F₀ x)
    unfold intClE_to_B_algHom
    letI : Algebra ↥C L := (intClE_to_L_algHom A F₀).toAlgebra
    haveI : IsScalarTower A ↥C L := IsScalarTower.of_algHom (intClE_to_L_algHom A F₀)
    haveI : Algebra.IsIntegral A ↥C := integralClosure.AlgebraIsIntegral
    rw [IsIntegralClosure.algebraMap_lift A B L x]; rfl
  haveI : IsDedekindDomain ↥C := by
    haveI : Ring.DimensionLEOne ↥C :=
      Ring.DimensionLEOne.isIntegralClosure A ↥F₀ (integralClosure A ↥F₀)
    haveI : IsIntegrallyClosed ↥C :=
      integralClosure.isIntegrallyClosedOfFiniteExtension K
    exact {}
  haveI : Module.Finite ↥C B := Module.Finite.of_restrictScalars_finite A ↥C B
  haveI : NoZeroSMulDivisors ↥C B := by
    constructor; intro a b hab
    rw [Algebra.smul_def] at hab
    rcases mul_eq_zero.mp hab with h | h
    · left; exact hinj_CB (by rwa [map_zero])
    · right; exact h


  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥C) ↥C :=
    integral_closure_isAdicComplete A K ↥F₀


  obtain ⟨E₀, hE₀_unram, hE₀_deg, hE₀_max, _⟩ :=
    thm_10_13_maxUnram_eq_resDeg A K B L

  have hF₀_eq_E₀ : F₀ = E₀ := by
    apply le_antisymm
    · exact iSup₂_le fun E hE => hE₀_max E hE
    · exact le_iSup₂ (f := fun E (_ : IsFiniteUnramifiedSubext A K L E) => E) E₀ hE₀_unram
  subst hF₀_eq_E₀
  have hf_one : Module.finrank
      (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B) = 1 :=
    AKLB_resDeg_over_eq_one A K B L F₀ hE₀_unram hE₀_deg
  haveI : Algebra.IsSeparable (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B) := by
    haveI : FiniteDimensional (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B) :=
      FiniteDimensional.of_finrank_eq_succ (by omega : Module.finrank (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B) = Nat.succ 0)
    rw [← Field.finSepDegree_eq_finrank_iff]
    have h1 := Field.finSepDegree_le_finrank (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B)
    have h2 : 0 < Field.finSepDegree (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B) :=
      Nat.pos_of_neZero _
    omega

  have hramIdx_eq : AKLB_ramIdx A B = Module.finrank (↥F₀) L :=
    (thm_10_23_part_ii_degree A K B L).symm


  have htotram : AKLB_ramIdx (↥C) B = Module.finrank (↥F₀) L := by
    have hro := ramIdx_over_eq_finrank_of_above_maxUnram A K B L F₀ (le_refl _)


    show ramIdx_over A B F₀ = Module.finrank (↥F₀) L
    exact hro

  have hma_sub : Module.finrank (↥F₀) L = m * (AKLB_residueChar A) ^ a := by
    linarith [hramIdx_eq, hma]


  have hchar : AKLB_residueChar (↥C) = AKLB_residueChar A := by
    unfold AKLB_residueChar

    haveI : IsLocalHom (algebraMap A ↥C) := by
      have : IsLocalHom ((algebraMap (↥C) B).comp (algebraMap A ↥C)) := by
        rw [← IsScalarTower.algebraMap_eq]; exact ‹IsLocalHom (algebraMap A B)›
      exact isLocalHom_of_comp _ (algebraMap ↥C B)
    haveI : CharP (IsLocalRing.ResidueField ↥C) (ringChar (IsLocalRing.ResidueField A)) :=
      charP_of_injective_algebraMap
        (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥C)).injective _
    exact ringChar.eq (IsLocalRing.ResidueField ↥C) (ringChar (IsLocalRing.ResidueField A))


  have hma_sub' : Module.finrank (↥F₀) L = m * (AKLB_residueChar (↥C)) ^ a := by
    rw [hchar]; exact hma_sub
  have hm' : ¬ (AKLB_residueChar (↥C) ∣ m) := by rw [hchar]; exact hm


  haveI : Algebra.IsSeparable (↥F₀) L :=
    Algebra.isSeparable_tower_top_of_isSeparable K (↥F₀) L


  have result := @tameWildDecomposition_existence (↥C) _ _ hDVR_C (↥F₀) _ _ ‹IsFractionRing ↥C ↥F₀› ‹IsAdicComplete (IsLocalRing.maximalIdeal ↥C) ↥C› B _ _ _ algCB ‹IsLocalHom (algebraMap (↥C) B)› ‹Module.Finite (↥C) B› ‹NoZeroSMulDivisors (↥C) B› L _ _ ‹FiniteDimensional (↥F₀) L› ‹Algebra.IsSeparable (↥F₀) L› _ ‹IsFractionRing B L› algCL ‹IsScalarTower (↥C) B L› ‹IsScalarTower (↥C) (↥F₀) L› ‹Algebra.IsSeparable (IsLocalRing.ResidueField (↥C)) (IsLocalRing.ResidueField B)› htotram m a hma_sub' hm'

  obtain ⟨T, _, hT_wild⟩ := result
  rw [hchar] at hT_wild
  exact ⟨T, hT_wild⟩

theorem tameWildDecomposition_subTowerExistence
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (m a : ℕ) (hma : AKLB_ramIdx A B = m * (AKLB_residueChar A) ^ a)
    (hm : ¬ (AKLB_residueChar A ∣ m)) :
    ∃ (E : IntermediateField K L),
      maximalUnramifiedSubextension A K L ≤ E ∧
      Module.finrank E L = (AKLB_residueChar A) ^ a := by
  obtain ⟨T, hT_deg⟩ := tameWildDecomposition_inSubTower A K B L m a hma hm
  let F₀ := maximalUnramifiedSubextension A K L
  let E := T.restrictScalars K
  use E
  constructor
  · intro x hx
    rw [IntermediateField.mem_restrictScalars]
    exact T.algebraMap_mem ⟨x, hx⟩
  · show Module.finrank (↥(T.restrictScalars K)) L = _
    rw [show Module.finrank (↥(T.restrictScalars K)) L = Module.finrank (↥T) L from by congr 1]
    exact hT_deg

theorem exists_intermediate_with_ramIdx_over_eq_pa
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (m a : ℕ) (hma : AKLB_ramIdx A B = m * (AKLB_residueChar A) ^ a)
    (hm : ¬ (AKLB_residueChar A ∣ m)) :
    ∃ (E : IntermediateField K L),
      maximalUnramifiedSubextension A K L ≤ E ∧
      ramIdx_over A B E = (AKLB_residueChar A) ^ a ∧
      Module.finrank E L = (AKLB_residueChar A) ^ a := by
  obtain ⟨E, hE_le, hE_deg⟩ := tameWildDecomposition_subTowerExistence A K B L m a hma hm
  have hE_ram : ramIdx_over A B E = Module.finrank E L :=
    ramIdx_over_eq_finrank_of_above_maxUnram A K B L E hE_le
  exact ⟨E, hE_le, by rw [hE_ram, hE_deg], hE_deg⟩

theorem tameWildDecomposition_towerTranslation
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (m a : ℕ) (hma : AKLB_ramIdx A B = m * (AKLB_residueChar A) ^ a)
    (hm : ¬ (AKLB_residueChar A ∣ m)) :
    ∃ (E : IntermediateField K L),
      maximalUnramifiedSubextension A K L ≤ E ∧
      ramIdx_sub A B E = m ∧
      ramIdx_over A B E = Module.finrank E L ∧
      Module.finrank E L = (AKLB_residueChar A) ^ a := by

  obtain ⟨E, hE_F, hE_ramover, hE_deg⟩ :=
    exists_intermediate_with_ramIdx_over_eq_pa A K B L m a hma hm

  have hE_totram : ramIdx_over A B E = Module.finrank E L := by
    rw [hE_ramover, hE_deg]

  have hmul := ramIdx_mul A K B L E

  have hE_sub : ramIdx_sub A B E = m := by
    rw [hma, hE_ramover] at hmul

    have hpa_pos : 0 < (AKLB_residueChar A) ^ a := by
      by_contra h
      push_neg at h
      interval_cases (AKLB_residueChar A) ^ a

      simp at hma

      have hef := AKLB_degree_eq_ramIdx_mul_resDeg A K B L
      rw [hma, zero_mul] at hef

      have := Module.finrank_pos (R := K) (M := L)
      omega
    have h : m * (AKLB_residueChar A) ^ a = ramIdx_sub A B E * (AKLB_residueChar A) ^ a := by
      rw [hmul, mul_comm]
    exact (Nat.eq_of_mul_eq_mul_right hpa_pos h).symm

  exact ⟨E, hE_F, hE_sub, hE_totram, hE_deg⟩

theorem tameWildDecompositionGeneral_existence
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)] :
    ∃ (E : IntermediateField K L),
      ¬ (AKLB_residueChar A ∣ ramIdx_sub A B E) ∧
      ramIdx_over A B E = Module.finrank E L ∧
      (∃ k : ℕ, ramIdx_over A B E = (AKLB_residueChar A) ^ k) ∧
      maximalUnramifiedSubextension A K L ≤ E := by

  have hef := AKLB_degree_eq_ramIdx_mul_resDeg A K B L
  have he_ne : AKLB_ramIdx A B ≠ 0 := by
    intro h; simp only [h, zero_mul] at hef
    exact absurd hef (by have := Module.finrank_pos (R := K) (M := L); omega)


  have hp_or := residueChar_prime_or_zero (IsLocalRing.ResidueField A)
  obtain ⟨m, a, hdecomp, hm⟩ := padic_decomp_exists (AKLB_ramIdx A B) he_ne
    (AKLB_residueChar A) hp_or

  obtain ⟨E, hE_F, hE_sub, hE_totram, hE_deg⟩ :=
    tameWildDecomposition_towerTranslation A K B L m a hdecomp hm

  exact ⟨E, hE_sub ▸ hm, hE_totram, ⟨a, hE_totram.trans hE_deg⟩, hE_F⟩


theorem intClE_residue_surj_of_totallyRamified
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (E' : IntermediateField K L)
    (hE'_totram : ramIdx_over A B E' = Module.finrank E' L)
    [Algebra ↥(integralClosure A ↥E') B]
    [IsScalarTower A ↥(integralClosure A ↥E') B]
    (α : IsLocalRing.ResidueField B) :
    ∃ γ : ↥(integralClosure A ↥E'),
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)) (algebraMap ↥(integralClosure A ↥E') B γ) = α := by sorry


set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem hensel_lift_in_totallyRamified_complement
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (E' : IntermediateField K L)
    (hE'_totram : ramIdx_over A B E' = Module.finrank E' L)
    (α : IsLocalRing.ResidueField B)
    (hα : IntermediateField.adjoin (IsLocalRing.ResidueField A) {α} = ⊤)
    (β : B)
    (hβ : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)) β = α) :
    algebraMap B L β ∈ (E' : Set L) := by

  set β_L : L := algebraMap B L β
  set E₀_β : IntermediateField K L := IntermediateField.adjoin K {β_L}
  have hE₀_β_unram : IsFiniteUnramifiedSubext A K L E₀_β :=
    ⟨IntermediateField.finiteDimensional_left E₀_β,
     integralClosure_formallyUnramified_of_hensel_lift A K B L α hα β hβ⟩
  have hE₀_β_deg : Module.finrank K E₀_β =
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
    adjoin_degree_eq_resDeg_of_hensel_lift A K B L α hα β hβ

  obtain ⟨E₀, hE₀_unram, hE₀_deg, hE₀_max, _⟩ := thm_10_13_maxUnram_eq_resDeg A K B L

  have hE₀_β_eq_E₀ : E₀_β = E₀ :=
    IntermediateField.eq_of_le_of_finrank_eq (hE₀_max E₀_β hE₀_β_unram)
      (by rw [hE₀_β_deg, hE₀_deg])

  suffices h : E₀ ≤ E' by
    exact h (hE₀_β_eq_E₀ ▸ IntermediateField.subset_adjoin K {β_L} (Set.mem_singleton β_L))


  set C_E' := integralClosure A ↥E'
  haveI : IsDiscreteValuationRing ↥C_E' := AKLB_intClE_isDVR A K L E'
  letI : Algebra ↥C_E' B := (intClE_to_B_algHom A B E').toAlgebra
  haveI : IsScalarTower A ↥C_E' B := IsScalarTower.of_algHom (intClE_to_B_algHom A B E')


  obtain ⟨γ, hγ⟩ := intClE_residue_surj_of_totallyRamified E' hE'_totram α

  set β' : B := algebraMap ↥C_E' B γ
  have hβ' : (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)) β' = α := hγ

  have hβ'_in_E' : algebraMap B L β' ∈ (E' : Set L) := by


    have key : ∀ z : ↥C_E', algebraMap B L (algebraMap ↥C_E' B z) =
        (E'.val.restrictScalars A).comp C_E'.val z := by
      intro z
      change algebraMap B L ((intClE_to_B_algHom A B E') z) = _
      unfold intClE_to_B_algHom
      letI : Algebra ↥C_E' L := (intClE_to_L_algHom A E').toAlgebra
      haveI : IsScalarTower A ↥C_E' L := IsScalarTower.of_algHom (intClE_to_L_algHom A E')
      haveI : Algebra.IsIntegral A ↥C_E' := integralClosure.AlgebraIsIntegral
      rw [IsIntegralClosure.algebraMap_lift A B L z]
      rfl
    rw [key γ]
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars']
    exact (γ.val : ↥E').property


  set E₀_β' : IntermediateField K L := IntermediateField.adjoin K {algebraMap B L β'}
  have hE₀_β'_unram : IsFiniteUnramifiedSubext A K L E₀_β' :=
    ⟨IntermediateField.finiteDimensional_left E₀_β',
     integralClosure_formallyUnramified_of_hensel_lift A K B L α hα β' hβ'⟩
  have hE₀_β'_deg : Module.finrank K E₀_β' =
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
    adjoin_degree_eq_resDeg_of_hensel_lift A K B L α hα β' hβ'
  have hE₀_β'_le_E' : E₀_β' ≤ E' :=
    IntermediateField.adjoin_le_iff.mpr (fun y hy => by
      rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hβ'_in_E')

  exact le_trans (thm_10_13_unram_le E₀ E₀_β' hE₀_unram hE₀_β'_unram hE₀_β'_deg) hE₀_β'_le_E'

theorem maxUnram_le_of_totally_ramified
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (E₀ : IntermediateField K L)
    (hE₀_unram : IsFiniteUnramifiedSubext A K L E₀)
    (hE₀_deg : Module.finrank K E₀ =
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))
    (E' : IntermediateField K L)
    (hE'_totram : ramIdx_over A B E' = Module.finrank E' L) :
    E₀ ≤ E' := by

  obtain ⟨E₀', hE₀'_unram, hE₀'_deg, hE₀'_max, _⟩ := thm_10_13_maxUnram_eq_resDeg A K B L
  have hE₀_le_E₀' : E₀ ≤ E₀' := hE₀'_max E₀ hE₀_unram
  have hE₀_eq_E₀' : E₀ = E₀' :=
    IntermediateField.eq_of_le_of_finrank_eq hE₀_le_E₀' (by rw [hE₀_deg, hE₀'_deg])
  rw [hE₀_eq_E₀']

  obtain ⟨α, hα⟩ := Field.exists_primitive_element
    (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)
  obtain ⟨β, hβ⟩ := Ideal.Quotient.mk_surjective α
  set β_L : L := algebraMap B L β
  set E₀'' : IntermediateField K L := IntermediateField.adjoin K {β_L}
  have hE₀''_unram : IsFiniteUnramifiedSubext A K L E₀'' :=
    ⟨IntermediateField.finiteDimensional_left E₀'',
     integralClosure_formallyUnramified_of_hensel_lift A K B L α hα β hβ⟩
  have hE₀''_deg : Module.finrank K E₀'' =
      Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
    adjoin_degree_eq_resDeg_of_hensel_lift A K B L α hα β hβ
  have hE₀''_eq : E₀'' = E₀' :=
    IntermediateField.eq_of_le_of_finrank_eq
      (hE₀'_max E₀'' hE₀''_unram) (by rw [hE₀''_deg, hE₀'_deg])
  rw [← hE₀''_eq]


  apply IntermediateField.adjoin_le_iff.mpr
  intro y hy
  rw [Set.mem_singleton_iff] at hy; rw [hy]
  exact hensel_lift_in_totallyRamified_complement E' hE'_totram α hα β hβ

theorem unramified_le_of_totallyRamified
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (E : IntermediateField K L)
    (hE : IsFiniteUnramifiedSubext A K L E)
    (E' : IntermediateField K L)
    (hE'_totram : ramIdx_over A B E' = Module.finrank E' L) :
    E ≤ E' := by

  obtain ⟨E₀, hE₀_unram, hE₀_deg, hE₀_max, _⟩ := thm_10_13_maxUnram_eq_resDeg A K B L

  have hE_le_E₀ : E ≤ E₀ := hE₀_max E hE

  have hE₀_le_E' : E₀ ≤ E' :=
    maxUnram_le_of_totally_ramified A K B L E₀ hE₀_unram hE₀_deg E' hE'_totram

  exact le_trans hE_le_E₀ hE₀_le_E'

theorem totally_wildly_ramified_contains_unramified
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (E' : IntermediateField K L)
    (hE'_totram : ramIdx_over A B E' = Module.finrank E' L)
    (_hE'_wild : ∃ k : ℕ, ramIdx_over A B E' = (AKLB_residueChar A) ^ k) :
    maximalUnramifiedSubextension A K L ≤ E' := by


  simp only [maximalUnramifiedSubextension]
  apply iSup_le; intro E; apply iSup_le; intro hE
  exact unramified_le_of_totallyRamified A K B L E hE E' hE'_totram

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem tameWildDecomposition_uniquenessContainment
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (E₁ E₂ : IntermediateField K L)
    (hE₁_F : maximalUnramifiedSubextension A K L ≤ E₁)
    (hE₂_F : maximalUnramifiedSubextension A K L ≤ E₂)
    (hE₁_totram : ramIdx_over A B E₁ = Module.finrank E₁ L)
    (hE₂_totram : ramIdx_over A B E₂ = Module.finrank E₂ L)
    (hE₁_tame : ¬ (AKLB_residueChar A ∣ ramIdx_sub A B E₁))
    (hfin_over : Module.finrank E₁ L = Module.finrank E₂ L) :
    E₁ ≤ E₂ := by


  set F₀ := maximalUnramifiedSubextension A K L with hF₀_def
  set C := integralClosure A ↥F₀ with hC_def

  suffices heq : E₁ = E₂ from heq ▸ le_refl _


  rw [show E₁ = IntermediateField.restrictScalars K (IntermediateField.extendScalars hE₁_F)
    from (IntermediateField.extendScalars_restrictScalars hE₁_F).symm,
    show E₂ = IntermediateField.restrictScalars K (IntermediateField.extendScalars hE₂_F)
    from (IntermediateField.extendScalars_restrictScalars hE₂_F).symm]
  rw [IntermediateField.restrictScalars_inj]
  set T₁ := IntermediateField.extendScalars hE₁_F
  set T₂ := IntermediateField.extendScalars hE₂_F


  haveI hDVR_C : IsDiscreteValuationRing ↥C := AKLB_intClE_isDVR A K L F₀
  letI algCB : Algebra ↥C B := (intClE_to_B_algHom A B F₀).toAlgebra
  haveI : IsScalarTower A ↥C B := IsScalarTower.of_algHom (intClE_to_B_algHom A B F₀)
  have hinj_CB : Function.Injective (algebraMap ↥C B) := by
    change Function.Injective (intClE_to_B_algHom A B F₀)
    intro x y hxy
    have hinj_L : Function.Injective (intClE_to_L_algHom A F₀) := by
      intro a b hab
      unfold intClE_to_L_algHom at hab
      simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars'] at hab
      exact Subtype.val_injective (Subtype.val_injective hab)
    apply hinj_L
    have key : ∀ z : ↥C, (intClE_to_L_algHom A F₀) z =
        algebraMap B L (intClE_to_B_algHom A B F₀ z) := by
      intro z
      unfold intClE_to_B_algHom
      letI : Algebra ↥C L := (intClE_to_L_algHom A F₀).toAlgebra
      haveI : IsScalarTower A ↥C L := IsScalarTower.of_algHom (intClE_to_L_algHom A F₀)
      haveI : Algebra.IsIntegral A ↥C := integralClosure.AlgebraIsIntegral
      rw [IsIntegralClosure.algebraMap_lift A B L z]
      rfl
    rw [key x, key y, hxy]
  haveI : FaithfulSMul ↥C B :=
    (faithfulSMul_iff_algebraMap_injective ↥C B).mpr hinj_CB
  haveI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  haveI : Algebra.IsIntegral ↥C B := Algebra.IsIntegral.tower_top A
  haveI : IsLocalHom (algebraMap ↥C B) := Algebra.IsIntegral.isLocalHom ↥C B
  haveI : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal ↥C) :=
    IsLocalRing.ResidueField.instLiesOverMaximalIdeal
  haveI : FiniteDimensional K ↥F₀ := IntermediateField.finiteDimensional_left F₀
  haveI : FiniteDimensional (↥F₀) L := IntermediateField.finiteDimensional_right F₀
  haveI : Algebra.IsSeparable K ↥F₀ := IntermediateField.isSeparable_tower_bot K F₀
  haveI : IsFractionRing ↥C ↥F₀ :=
    integralClosure.isFractionRing_of_finite_extension K ↥F₀
  haveI : IsNoetherian A ↥C :=
    IsIntegralClosure.isNoetherian A K ↥F₀ (integralClosure A ↥F₀)
  haveI : Module.Finite A ↥C := inferInstance
  letI algCL : Algebra ↥C L := (intClE_to_L_algHom A F₀).toAlgebra
  haveI : IsScalarTower A ↥C L := IsScalarTower.of_algHom (intClE_to_L_algHom A F₀)
  haveI : IsScalarTower ↥C ↥F₀ L := by
    apply IsScalarTower.of_algebraMap_eq; intro x
    show algebraMap ↥F₀ L (algebraMap ↥C ↥F₀ x) = (intClE_to_L_algHom A F₀) x
    unfold intClE_to_L_algHom
    simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', Subalgebra.coe_val]; rfl
  haveI : IsScalarTower ↥C B L := by
    apply IsScalarTower.of_algebraMap_eq; intro x
    change (intClE_to_L_algHom A F₀) x = algebraMap B L (intClE_to_B_algHom A B F₀ x)
    unfold intClE_to_B_algHom
    letI : Algebra ↥C L := (intClE_to_L_algHom A F₀).toAlgebra
    haveI : IsScalarTower A ↥C L := IsScalarTower.of_algHom (intClE_to_L_algHom A F₀)
    haveI : Algebra.IsIntegral A ↥C := integralClosure.AlgebraIsIntegral
    rw [IsIntegralClosure.algebraMap_lift A B L x]; rfl
  haveI : IsDedekindDomain ↥C := by
    haveI : Ring.DimensionLEOne ↥C :=
      Ring.DimensionLEOne.isIntegralClosure A ↥F₀ (integralClosure A ↥F₀)
    haveI : IsIntegrallyClosed ↥C :=
      integralClosure.isIntegrallyClosedOfFiniteExtension K
    exact {}
  haveI : Module.Finite ↥C B := Module.Finite.of_restrictScalars_finite A ↥C B
  haveI : NoZeroSMulDivisors ↥C B := by
    constructor; intro a b hab
    rw [Algebra.smul_def] at hab
    rcases mul_eq_zero.mp hab with h | h
    · left; exact hinj_CB (by rwa [map_zero])
    · right; exact h
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥C) ↥C :=
    integral_closure_isAdicComplete A K ↥F₀

  obtain ⟨E₀, hE₀_unram, hE₀_deg, hE₀_max, _⟩ :=
    thm_10_13_maxUnram_eq_resDeg A K B L
  have hF₀_eq_E₀ : F₀ = E₀ := by
    apply le_antisymm
    · exact iSup₂_le fun E hE => hE₀_max E hE
    · exact le_iSup₂ (f := fun E (_ : IsFiniteUnramifiedSubext A K L E) => E) E₀ hE₀_unram
  subst hF₀_eq_E₀
  have hf_one : Module.finrank
      (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B) = 1 :=
    AKLB_resDeg_over_eq_one A K B L F₀ hE₀_unram hE₀_deg
  haveI : Algebra.IsSeparable (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B) := by
    haveI : FiniteDimensional (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B) :=
      FiniteDimensional.of_finrank_eq_succ (by omega : Module.finrank (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B) = Nat.succ 0)
    rw [← Field.finSepDegree_eq_finrank_iff]
    have h1 := Field.finSepDegree_le_finrank (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B)
    have h2 : 0 < Field.finSepDegree (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B) :=
      Nat.pos_of_neZero _
    omega
  haveI : Algebra.IsSeparable (↥F₀) L :=
    Algebra.isSeparable_tower_top_of_isSeparable K (↥F₀) L

  have htotram : AKLB_ramIdx (↥C) B = Module.finrank (↥F₀) L := by
    have hro := ramIdx_over_eq_finrank_of_above_maxUnram A K B L F₀ (le_refl _)
    show ramIdx_over A B F₀ = Module.finrank (↥F₀) L
    exact hro

  have hchar : AKLB_residueChar (↥C) = AKLB_residueChar A := by
    unfold AKLB_residueChar
    haveI : IsLocalHom (algebraMap A ↥C) := by
      have : IsLocalHom ((algebraMap (↥C) B).comp (algebraMap A ↥C)) := by
        rw [← IsScalarTower.algebraMap_eq]; exact ‹IsLocalHom (algebraMap A B)›
      exact isLocalHom_of_comp _ (algebraMap ↥C B)
    haveI : CharP (IsLocalRing.ResidueField ↥C) (ringChar (IsLocalRing.ResidueField A)) :=
      charP_of_injective_algebraMap
        (algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField ↥C)).injective _
    exact ringChar.eq (IsLocalRing.ResidueField ↥C) (ringChar (IsLocalRing.ResidueField A))


  obtain ⟨πC, hπC_irr⟩ := IsDiscreteValuationRing.exists_irreducible (↥C)
  set πC_img : ↥F₀ := algebraMap (↥C) (↥F₀) πC with hπC_img_def
  have hπC_ne : algebraMap (↥F₀) L πC_img ≠ 0 := by
    simp only [πC_img]
    intro h
    have hinj_F₀ : Function.Injective (algebraMap (↥F₀) L) :=
      (algebraMap (↥F₀) L).injective
    have hinj_CF : Function.Injective (algebraMap (↥C) (↥F₀)) :=
      IsFractionRing.injective (↥C) (↥F₀)
    have h1 := hinj_F₀ (h.trans (map_zero _).symm)
    have h2 := hinj_CF (h1.trans (map_zero _).symm)
    exact hπC_irr.ne_zero h2
  have hπC_irr_info : ∃ πA : ↥C, Irreducible πA ∧ algebraMap (↥C) (↥F₀) πA = πC_img := by
    exact ⟨πC, hπC_irr, rfl⟩

  haveI : FiniteDimensional ↥F₀ ↥T₁ := IntermediateField.finiteDimensional_left T₁
  haveI : FiniteDimensional ↥F₀ ↥T₂ := IntermediateField.finiteDimensional_left T₂
  haveI : FiniteDimensional ↥T₁ L := IntermediateField.finiteDimensional_right T₁
  haveI : FiniteDimensional ↥T₂ L := IntermediateField.finiteDimensional_right T₂

  have hT₁L : Module.finrank ↥T₁ L = Module.finrank ↥E₁ L := by
    show Module.finrank ↥(IntermediateField.extendScalars hE₁_F) L = _; congr 1
  have hT₂L : Module.finrank ↥T₂ L = Module.finrank ↥E₂ L := by
    show Module.finrank ↥(IntermediateField.extendScalars hE₂_F) L = _; congr 1

  have hT_deg_eq : Module.finrank ↥F₀ ↥T₁ = Module.finrank ↥F₀ ↥T₂ := by
    have h1 := Module.finrank_mul_finrank ↥F₀ ↥T₁ L
    have h2 := Module.finrank_mul_finrank ↥F₀ ↥T₂ L
    rw [hT₁L, hfin_over] at h1
    rw [hT₂L] at h2
    have hpos : 0 < Module.finrank ↥E₂ L := by
      rw [← hfin_over]; exact Module.finrank_pos (R := ↥E₁) (M := L)
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  set m := Module.finrank ↥F₀ ↥T₁

  have hm_tame : ¬ (AKLB_residueChar ↥C ∣ m) := by
    rw [hchar]


    have hramIdx_eq : AKLB_ramIdx A B = Module.finrank (↥F₀) L :=
      (thm_10_23_part_ii_degree A K B L).symm
    have hmul := ramIdx_mul A K B L E₁
    have htow := Module.finrank_mul_finrank ↥F₀ ↥T₁ L
    rw [hT₁L] at htow


    rw [hE₁_totram] at hmul

    rw [hramIdx_eq] at hmul

    have hE₁L_pos : 0 < Module.finrank (↥E₁) L := Module.finrank_pos (R := ↥E₁) (M := L)
    rw [mul_comm] at hmul

    have hm_eq : m = ramIdx_sub A B E₁ :=
      Nat.eq_of_mul_eq_mul_right hE₁L_pos (htow.trans hmul)
    rw [hm_eq]
    exact hE₁_tame
  have hT₂_deg : Module.finrank ↥F₀ ↥T₂ = m := hT_deg_eq.symm

  have hgen₁ := @intermediateField_generatedByRoot ↥C _ _ hDVR_C ↥F₀ _ _ ‹IsFractionRing ↥C ↥F₀› ‹IsAdicComplete (IsLocalRing.maximalIdeal ↥C) ↥C› B _ _ _ algCB ‹IsLocalHom (algebraMap ↥C B)› ‹Module.Finite ↥C B› ‹NoZeroSMulDivisors ↥C B› L _ _ ‹FiniteDimensional ↥F₀ L› ‹Algebra.IsSeparable ↥F₀ L› _ ‹IsFractionRing B L› algCL ‹IsScalarTower ↥C B L› ‹IsScalarTower ↥C ↥F₀ L› ‹Algebra.IsSeparable (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B)› htotram πC_img hπC_ne hπC_irr_info m hm_tame T₁ rfl
  have hgen₂ := @intermediateField_generatedByRoot ↥C _ _ hDVR_C ↥F₀ _ _ ‹IsFractionRing ↥C ↥F₀› ‹IsAdicComplete (IsLocalRing.maximalIdeal ↥C) ↥C› B _ _ _ algCB ‹IsLocalHom (algebraMap ↥C B)› ‹Module.Finite ↥C B› ‹NoZeroSMulDivisors ↥C B› L _ _ ‹FiniteDimensional ↥F₀ L› ‹Algebra.IsSeparable ↥F₀ L› _ ‹IsFractionRing B L› algCL ‹IsScalarTower ↥C B L› ‹IsScalarTower ↥C ↥F₀ L› ‹Algebra.IsSeparable (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B)› htotram πC_img hπC_ne hπC_irr_info m hm_tame T₂ hT₂_deg
  obtain ⟨α, hα_pow, hT₁_eq⟩ := hgen₁
  obtain ⟨β, hβ_pow, hT₂_eq⟩ := hgen₂

  have hπ_ne := hπC_ne
  have hζ_root : (α * β⁻¹) ^ m = 1 :=
    ratio_pow_eq_one α β (algebraMap ↥F₀ L πC_img) m hα_pow hβ_pow hπ_ne
  obtain ⟨ζ₀, hζ₀⟩ := @roots_of_unity_in_base_of_totally_ramified ↥C _ _ hDVR_C ↥F₀ _ _ ‹IsFractionRing ↥C ↥F₀› ‹IsAdicComplete (IsLocalRing.maximalIdeal ↥C) ↥C› B _ _ _ algCB ‹IsLocalHom (algebraMap ↥C B)› ‹Module.Finite ↥C B› ‹NoZeroSMulDivisors ↥C B› L _ _ ‹FiniteDimensional ↥F₀ L› ‹Algebra.IsSeparable ↥F₀ L› _ ‹IsFractionRing B L› algCL ‹IsScalarTower ↥C B L› ‹IsScalarTower ↥C ↥F₀ L› ‹Algebra.IsSeparable (IsLocalRing.ResidueField ↥C) (IsLocalRing.ResidueField B)› htotram m hm_tame (α * β⁻¹) hζ_root

  have hm_ne : m ≠ 0 := by
    intro h; have : Module.finrank ↥F₀ (T₁ : Type _) ≥ 1 := Module.finrank_pos (R := ↥F₀) (M := T₁); omega
  have hα_ne : α ≠ 0 := by intro h; apply hπ_ne; rw [← hα_pow, h, zero_pow hm_ne]
  have hβ_ne : β ≠ 0 := by intro h; apply hπ_ne; rw [← hβ_pow, h, zero_pow hm_ne]
  have hα_eq_ζβ : algebraMap ↥F₀ L ζ₀ * β = α := by
    rw [hζ₀, mul_assoc, inv_mul_cancel₀ hβ_ne, mul_one]
  have hβ_eq_ζα : algebraMap ↥F₀ L ζ₀⁻¹ * α = β := by
    rw [map_inv₀, hζ₀, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel₀ hα_ne, mul_one]

  have hadj_eq : IntermediateField.adjoin ↥F₀ ({α} : Set L) =
      IntermediateField.adjoin ↥F₀ ({β} : Set L) :=
    IntermediateField.adjoin_singleton_eq_of_smul α β ⟨ζ₀, hα_eq_ζβ⟩ ⟨ζ₀⁻¹, hβ_eq_ζα⟩
  rw [hT₁_eq, hT₂_eq, hadj_eq]

theorem tameWildDecomposition_uniquenessTowerTranslation
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (E₁ E₂ : IntermediateField K L)
    (hE₁_F : maximalUnramifiedSubextension A K L ≤ E₁)
    (hE₂_F : maximalUnramifiedSubextension A K L ≤ E₂)
    (hE₁_totram : ramIdx_over A B E₁ = Module.finrank E₁ L)
    (hE₂_totram : ramIdx_over A B E₂ = Module.finrank E₂ L)
    (hE₁_tame : ¬ (AKLB_residueChar A ∣ ramIdx_sub A B E₁))
    (hdeg : Module.finrank K E₁ = Module.finrank K E₂) :
    E₁ = E₂ := by

  have htow₁ := Module.finrank_mul_finrank K E₁ L
  have htow₂ := Module.finrank_mul_finrank K E₂ L

  have hKL_pos : 0 < Module.finrank K L := Module.finrank_pos (R := K) (M := L)

  have hKE₁_pos : 0 < Module.finrank K ↥E₁ :=
    Nat.pos_of_mul_pos_right (htow₁ ▸ hKL_pos)
  have hfin_over : Module.finrank (↥E₁) L = Module.finrank (↥E₂) L := by
    rw [hdeg] at htow₁


    have hKE₂_pos : 0 < Module.finrank K ↥E₂ := hdeg ▸ hKE₁_pos
    exact Nat.eq_of_mul_eq_mul_left hKE₂_pos (htow₁.trans htow₂.symm)

  have h_le : E₁ ≤ E₂ := tameWildDecomposition_uniquenessContainment
    A K B L E₁ E₂ hE₁_F hE₂_F hE₁_totram hE₂_totram hE₁_tame hfin_over

  exact IntermediateField.eq_of_le_of_finrank_eq h_le hdeg

theorem tameWildDecompositionGeneral_uniqueness
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (E₁ E₂ : IntermediateField K L)
    (hE₁_tame : ¬ (AKLB_residueChar A ∣ ramIdx_sub A B E₁))
    (hE₁_totram : ramIdx_over A B E₁ = Module.finrank E₁ L)
    (hE₁_wild : ∃ k : ℕ, ramIdx_over A B E₁ = (AKLB_residueChar A) ^ k)
    (hE₁_F : maximalUnramifiedSubextension A K L ≤ E₁)
    (hE₂_tame : ¬ (AKLB_residueChar A ∣ ramIdx_sub A B E₂))
    (hE₂_totram : ramIdx_over A B E₂ = Module.finrank E₂ L)
    (hE₂_wild : ∃ k : ℕ, ramIdx_over A B E₂ = (AKLB_residueChar A) ^ k)
    (hE₂_F : maximalUnramifiedSubextension A K L ≤ E₂) :
    E₁ = E₂ := by

  set p := AKLB_residueChar A with hp_def
  obtain ⟨k₁, hk₁⟩ := hE₁_wild
  obtain ⟨k₂, hk₂⟩ := hE₂_wild

  have hmul₁ := ramIdx_mul A K B L E₁
  have hmul₂ := ramIdx_mul A K B L E₂

  rw [hk₁] at hmul₁
  rw [hk₂] at hmul₂


  rw [mul_comm] at hmul₁
  rw [mul_comm] at hmul₂


  have hef := AKLB_degree_eq_ramIdx_mul_resDeg A K B L
  have he_ne : AKLB_ramIdx A B ≠ 0 := by
    intro h; simp only [h, zero_mul] at hef
    exact absurd hef (by have := Module.finrank_pos (R := K) (M := L); omega)

  have hp_or := residueChar_prime_or_zero (IsLocalRing.ResidueField A)

  have ⟨hsub_eq, hk_eq⟩ := padic_decomp_unique_tower p hp_or he_ne
    hmul₁ hE₁_tame hmul₂ hE₂_tame

  have hfinrank_over : Module.finrank E₁ L = Module.finrank E₂ L := by
    rw [← hE₁_totram, ← hE₂_totram, hk₁, hk₂, hk_eq]

  have hfinrank_sub : Module.finrank K E₁ = Module.finrank K E₂ := by
    have htow₁ := Module.finrank_mul_finrank K E₁ L
    have htow₂ := Module.finrank_mul_finrank K E₂ L
    rw [hfinrank_over] at htow₁
    have hLEi_ne : Module.finrank (↑E₂) L ≠ 0 := by
      rw [← hE₂_totram, hk₂]
      intro h
      rw [h, mul_zero] at hmul₂
      exact he_ne hmul₂
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hLEi_ne) (htow₁.trans htow₂.symm)

  exact tameWildDecomposition_uniquenessTowerTranslation A K B L E₁ E₂
    hE₁_F hE₂_F hE₁_totram hE₂_totram hE₁_tame hfinrank_sub

theorem tameWildDecompositionGeneral
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
    [NoZeroSMulDivisors A B]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)] :
    ∃! (E : IntermediateField K L),

      ¬ (AKLB_residueChar A ∣ ramIdx_sub A B E) ∧

      ramIdx_over A B E = Module.finrank E L ∧

      (∃ k : ℕ, ramIdx_over A B E = (AKLB_residueChar A) ^ k) := by

  obtain ⟨E, hE_tame, hE_totram, hE_wild, hE_F⟩ := tameWildDecompositionGeneral_existence A K B L

  refine ⟨E, ⟨hE_tame, hE_totram, hE_wild⟩, ?_⟩

  intro E' ⟨hE'_tame, hE'_totram, hE'_wild⟩

  have hE'_F : maximalUnramifiedSubextension A K L ≤ E' :=
    totally_wildly_ramified_contains_unramified A K B L E' hE'_totram hE'_wild

  exact (tameWildDecompositionGeneral_uniqueness A K B L E E'
    hE_tame hE_totram hE_wild hE_F hE'_tame hE'_totram hE'_wild hE'_F).symm

end TameWildDecompositionGeneral
