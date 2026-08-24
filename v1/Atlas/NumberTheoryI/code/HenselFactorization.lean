/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.HenselLemmas
import Atlas.NumberTheoryI.code.ScalingStep
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Transitivity

open Polynomial IsLocalRing


section HenselIII

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]

theorem hensel_lemma_III
    (f : A[X])
    (g_bar h_bar : (A ⧸ maximalIdeal A)[X])
    (hfact : Polynomial.map (Ideal.Quotient.mk (maximalIdeal A)) f = g_bar * h_bar)
    (hcoprime : IsCoprime g_bar h_bar) :
    ∃ (g h : A[X]),
      f = g * h ∧
      Polynomial.map (Ideal.Quotient.mk (maximalIdeal A)) g = g_bar ∧
      Polynomial.map (Ideal.Quotient.mk (maximalIdeal A)) h = h_bar ∧
      g.natDegree = g_bar.natDegree := by sorry

theorem irreducible_no_coprime_factor_mod
    {f : A[X]}
    (hirr : Irreducible f)
    (g_bar h_bar : (A ⧸ maximalIdeal A)[X])
    (hfact : Polynomial.map (Ideal.Quotient.mk (maximalIdeal A)) f = g_bar * h_bar)
    (hcoprime : IsCoprime g_bar h_bar) :
    IsUnit g_bar ∨ IsUnit h_bar := by
  obtain ⟨g, h, hgh, hg_map, hh_map, _⟩ := hensel_lemma_III f g_bar h_bar hfact hcoprime
  rcases hirr.isUnit_or_isUnit hgh with hgu | hhu
  · exact Or.inl (hg_map ▸ (Polynomial.mapRingHom
      (Ideal.Quotient.mk (maximalIdeal A))).isUnit_map hgu)
  · exact Or.inr (hh_map ▸ (Polynomial.mapRingHom
      (Ideal.Quotient.mk (maximalIdeal A))).isUnit_map hhu)

end HenselIII


section HenselKurschak

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

theorem hensel_kurschak_scaling_step
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    (f : K[X])
    (hirr : Irreducible f)
    (hlead : ∃ a : A, algebraMap A K a = f.leadingCoeff)
    (hconst : ∃ a : A, algebraMap A K a = f.coeff 0)
    (hnotinA : ¬∃ g : A[X], f = Polynomial.map (algebraMap A K) g) :
    ∃ (g : A[X]),
      Irreducible g ∧
      g.coeff 0 ∈ maximalIdeal A ∧
      g.coeff g.natDegree ∈ maximalIdeal A ∧
      (∃ i, ¬(g.coeff i ∈ maximalIdeal A)) :=
  hensel_kurschak_scaling_step' f hirr hlead hconst hnotinA

theorem hensel_kurschak
    (f : K[X])
    (hirr : Irreducible f)
    (hlead : ∃ a : A, algebraMap A K a = f.leadingCoeff)
    (hconst : ∃ a : A, algebraMap A K a = f.coeff 0) :
    ∃ g : A[X], f = Polynomial.map (algebraMap A K) g := by
  by_contra hnotinA
  obtain ⟨g, hirr_g, hg0, hgn, ⟨j, hj⟩⟩ :=
    hensel_kurschak_scaling_step f hirr hlead hconst hnotinA
  set 𝔭 := maximalIdeal A
  set π := Ideal.Quotient.mk 𝔭
  haveI h𝔭_max : 𝔭.IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  letI : Field (A ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  set g_bar := Polynomial.map π g

  have hg_bar_ne : g_bar ≠ 0 := by
    intro h; apply hj
    have hzero : g_bar.coeff j = 0 := by rw [h]; simp
    rw [Polynomial.coeff_map] at hzero
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hzero

  have hroot0 : g_bar.IsRoot 0 := by
    rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hg0

  have hd_pos : 0 < g_bar.rootMultiplicity 0 :=
    (Polynomial.rootMultiplicity_pos hg_bar_ne).mpr hroot0
  obtain ⟨q, hfact_bar, hq_ndvd⟩ :=
    g_bar.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hg_bar_ne 0
  set d := g_bar.rootMultiplicity 0
  simp only [sub_zero, map_zero] at hfact_bar hq_ndvd

  have hcoprime : IsCoprime (X ^ d) q :=
    (Irreducible.coprime_pow_of_not_dvd d Polynomial.irreducible_X hq_ndvd).symm

  obtain ⟨u, v, hguv, hu_map, hv_map, hu_deg⟩ :=
    hensel_lemma_III g (X ^ d) q hfact_bar hcoprime

  have hu_deg_eq : u.natDegree = d := by
    rw [hu_deg, Polynomial.natDegree_X_pow]
  have hu_not_unit : ¬IsUnit u := by
    intro hu; rw [Polynomial.isUnit_iff] at hu
    obtain ⟨_, _, hrp⟩ := hu
    have : u.natDegree = 0 := by rw [← hrp]; exact Polynomial.natDegree_C _
    omega


  have hv_not_unit : ¬IsUnit v := by
    intro hv; rw [Polynomial.isUnit_iff] at hv
    obtain ⟨c, hc_unit, hvc⟩ := hv
    have hc_ne : c ≠ 0 := IsUnit.ne_zero hc_unit
    have hg_deg : g.natDegree = d := by
      have : g.natDegree = u.natDegree + (C c).natDegree := by
        rw [hguv, ← hvc]
        exact Polynomial.natDegree_mul
          (fun hu_z => hirr_g.ne_zero (by rw [hguv, ← hvc, hu_z, zero_mul]))
          (fun hv_z => by simp [Polynomial.C_eq_zero] at hv_z ⊢; exact absurd hv_z hc_ne)
      simp [Polynomial.natDegree_C] at this; linarith
    have hgd_in_p : g.coeff d ∈ 𝔭 := hg_deg ▸ hgn
    have hu_d_map : π (u.coeff d) = 1 := by
      have : (Polynomial.map π u).coeff d = 1 := by
        rw [hu_map]; simp [Polynomial.coeff_X_pow]
      rwa [Polynomial.coeff_map] at this
    have hgd_eq : g.coeff d = u.coeff d * c := by
      rw [hguv, ← hvc, Polynomial.coeff_mul_C]
    have hpc : π (g.coeff d) = π c := by
      rw [hgd_eq, map_mul, hu_d_map, one_mul]
    have hpc0 : π (g.coeff d) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hgd_in_p
    have hc_in_p : c ∈ 𝔭 := Ideal.Quotient.eq_zero_iff_mem.mp (hpc ▸ hpc0)
    exact h𝔭_max.ne_top (Ideal.eq_top_of_isUnit_mem 𝔭 hc_in_p hc_unit)

  exact (hirr_g.isUnit_or_isUnit hguv).elim hu_not_unit hv_not_unit

end HenselKurschak


section NormIntegrality

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
variable {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra A L] [IsScalarTower A K L]

omit [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
  [Algebra A K] [IsFractionRing A K] [Algebra A L]
  [IsScalarTower A K L] in
theorem norm_eq_minpoly_const_power
    (α : L) :
    ∃ e : ℕ, 0 < e ∧ Algebra.norm K α =
      (-1) ^ (Module.finrank K L) * (minpoly K α).eval 0 ^ e := by
  open IntermediateField in
  haveI : Algebra.IsIntegral K L := Algebra.IsIntegral.of_finite K L
  have hα : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  refine ⟨Module.finrank K⟮α⟯ L, Module.finrank_pos (R := ↥K⟮α⟯) (M := L), ?_⟩
  rw [Algebra.norm_eq_norm_adjoin K α]
  set pb := IntermediateField.adjoin.powerBasis hα
  rw [← IntermediateField.adjoin.powerBasis_gen hα]
  rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb]
  rw [IntermediateField.adjoin.powerBasis_gen hα,
      IntermediateField.minpoly_gen K α]
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  rw [mul_pow, ← pow_mul]
  have h1 : pb.dim = (minpoly K α).natDegree := IntermediateField.adjoin.powerBasis_dim hα
  have h2 : Module.finrank K ↥K⟮α⟯ = (minpoly K α).natDegree :=
    IntermediateField.adjoin.finrank hα
  rw [h1, ← h2, Module.finrank_mul_finrank K ↥K⟮α⟯ L]

theorem norm_integral_of_integral
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L]
    (α : L) (hα : IsIntegral A α) :
    ∃ a : A, algebraMap A K a = Algebra.norm K α := by
  haveI : IsIntegrallyClosed A := UniqueFactorizationMonoid.instIsIntegrallyClosed
  exact IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_norm K hα)

theorem integral_of_norm_integral
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L]
    (α : L)
    (hα_norm : ∃ a : A, algebraMap A K a = Algebra.norm K α) :
    IsIntegral A α := by
  haveI : IsIntegrallyClosed A := UniqueFactorizationMonoid.instIsIntegrallyClosed
  haveI : Algebra.IsIntegral K L := Algebra.IsIntegral.of_finite K L
  have hα_K : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  set f := minpoly K α
  have hf_irr : Irreducible f := minpoly.irreducible hα_K
  have hf_monic : f.Monic := minpoly.monic hα_K

  have hlead : ∃ a : A, algebraMap A K a = f.leadingCoeff :=
    ⟨1, by rw [hf_monic.leadingCoeff, map_one]⟩

  obtain ⟨e, he_pos, he⟩ := @norm_eq_minpoly_const_power K _ L _ _ _ α
  obtain ⟨a, ha⟩ := hα_norm
  set n := Module.finrank K L
  set c := f.eval 0

  have hce_in_A : ∃ b : A, algebraMap A K b = c ^ e := by
    refine ⟨(-1) ^ n * a, ?_⟩
    rw [map_mul, ha, he]
    push_cast
    ring_nf
    rw [show n * 2 = n + n from by ring]
    rw [Even.neg_one_pow (α := K) ⟨n, rfl⟩, mul_one]

  obtain ⟨b, hb⟩ := hce_in_A
  have hconst : ∃ a₀ : A, algebraMap A K a₀ = f.coeff 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
    exact IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow he_pos
      (hb ▸ isIntegral_algebraMap)

  obtain ⟨g, hg⟩ := hensel_kurschak f hf_irr hlead hconst

  have hg_monic : g.Monic :=
    Polynomial.monic_of_injective (IsFractionRing.injective A K) (hg ▸ hf_monic)

  exact ⟨g, hg_monic, by
    change Polynomial.aeval α g = 0
    rw [← Polynomial.aeval_map_algebraMap (R := A) (A := K) (B := L) α g, hg.symm]
    exact minpoly.aeval K α⟩

theorem integral_iff_norm_integral
    (α : L) :
    IsIntegral A α ↔ ∃ a : A, algebraMap A K a = Algebra.norm K α :=
  ⟨norm_integral_of_integral α, integral_of_norm_integral α⟩

end NormIntegrality


section IntegralClosureDVR

theorem isLocalRing_of_unique_maximal (R : Type*) [CommRing R] [IsDomain R]
    (𝔮 : Ideal R) (h𝔮 : 𝔮.IsMaximal)
    (huniq : ∀ (I : Ideal R), I.IsMaximal → I = 𝔮) : IsLocalRing R :=
  IsLocalRing.of_is_unit_or_is_unit_of_add_one (fun {a b} hab => by
    by_cases ha : a ∈ 𝔮
    · right
      have hb : b ∉ 𝔮 := fun hb =>
        h𝔮.ne_top ((Ideal.eq_top_iff_one 𝔮).mpr (hab ▸ 𝔮.add_mem ha hb))
      rw [← Ideal.span_singleton_eq_top]
      by_contra h
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
      exact hb (huniq M hM ▸ hle (Ideal.subset_span rfl))
    · left
      rw [← Ideal.span_singleton_eq_top]
      by_contra h
      obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
      exact ha (huniq M hM ▸ hle (Ideal.subset_span rfl)))

theorem isDVR_of_local_dedekind (R : Type*) [CommRing R] [IsDomain R]
    [IsDedekindDomain R] [IsLocalRing R] (hnotfield : ¬IsField R) :
    IsDiscreteValuationRing R :=
  (IsDiscreteValuationRing.TFAE R hnotfield |>.out 2 0).mp ‹_›

theorem maximal_lies_over_in_AKLB
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra A L] [IsScalarTower A K L]
    (B : Type*) [CommRing B] [IsDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    (𝔮 : Ideal B) (h𝔮 : 𝔮.IsMaximal) :
    Ideal.comap (algebraMap A B) 𝔮 = maximalIdeal A := by
  have hprime : (Ideal.comap (algebraMap A B) 𝔮).IsPrime :=
    Ideal.IsPrime.comap (algebraMap A B)
  have hne : Ideal.comap (algebraMap A B) 𝔮 ≠ ⊥ := by
    haveI : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A K L B
    have h𝔮_ne_bot : 𝔮 ≠ ⊥ := by
      intro h𝔮_eq_bot
      have hBfield : IsField B := by
        rw [← not_not (a := IsField B)]
        intro hnotfield
        exact (Ring.ne_bot_of_isMaximal_of_not_isField h𝔮 hnotfield) h𝔮_eq_bot
      haveI : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
      have hinj : Function.Injective (algebraMap A B) := by
        have h1 : Function.Injective (algebraMap A L) := by
          rw [IsScalarTower.algebraMap_eq A K L]
          exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
        intro a b hab
        exact h1 (by simp [IsScalarTower.algebraMap_eq A B L, hab])
      exact IsDiscreteValuationRing.not_isField A
        (isField_of_isIntegral_of_isField hinj hBfield)
    obtain ⟨x, hx_mem, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔮_ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hx_ne hx_mem
      (IsIntegralClosure.isIntegral A L x)
  exact IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne hprime)

theorem two_maximal_ideals_give_coprime_factorization
    {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra A L] [IsScalarTower A K L]
    {B : Type*} [CommRing B] [IsDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    (𝔮₁ 𝔮₂ : Ideal B)
    (h₁ : 𝔮₁.IsMaximal) (h₂ : 𝔮₂.IsMaximal) (_hne : 𝔮₁ ≠ 𝔮₂)
    (b : B) (hb₁ : b ∈ 𝔮₁) (hb₂ : b ∉ 𝔮₂)
    (hbint : IsIntegral A b)
    (_hirr : Irreducible (minpoly A b)) :
    ∃ (g_bar h_bar : (A ⧸ maximalIdeal A)[X]),
      Polynomial.map (Ideal.Quotient.mk (maximalIdeal A)) (minpoly A b)
        = g_bar * h_bar ∧
      IsCoprime g_bar h_bar ∧
      ¬IsUnit g_bar ∧ ¬IsUnit h_bar := by
  set 𝔭 := maximalIdeal A with h𝔭_def
  set f := minpoly A b with hf_def
  set π := Ideal.Quotient.mk 𝔭 with hπ_def
  set f_bar := Polynomial.map π f with hf_bar_def

  haveI h𝔭_max : 𝔭.IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  letI : Field (A ⧸ 𝔭) := Ideal.Quotient.field 𝔭

  have hcoeff0_in_p : f.coeff 0 ∈ 𝔭 := by

    have hmem : f.coeff 0 ∈ Ideal.comap (algebraMap A B) 𝔮₁ := by
      rw [Ideal.mem_comap]
      have heval_zero : (Ideal.Quotient.mk 𝔮₁) (algebraMap A B (f.coeff 0)) = 0 := by
        have h1 : (Ideal.Quotient.mk 𝔮₁) (Polynomial.aeval b f) = 0 := by
          rw [minpoly.aeval, map_zero]
        rw [Polynomial.aeval_def, Polynomial.hom_eval₂,
            Ideal.Quotient.eq_zero_iff_mem.mpr hb₁, Polynomial.eval₂_at_zero] at h1
        exact h1
      rwa [Ideal.Quotient.eq_zero_iff_mem] at heval_zero

    rwa [maximal_lies_over_in_AKLB A K L B 𝔮₁ h₁] at hmem

  have hf_bar_ne_zero : f_bar ≠ 0 :=
    (Polynomial.Monic.map π (minpoly.monic hbint)).ne_zero

  have hroot0 : f_bar.IsRoot 0 := by
    rw [Polynomial.IsRoot, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hcoeff0_in_p
  have hd_pos : 0 < f_bar.rootMultiplicity 0 :=
    (Polynomial.rootMultiplicity_pos hf_bar_ne_zero).mpr hroot0

  obtain ⟨q, hfact, hq_ndvd⟩ :=
    f_bar.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hf_bar_ne_zero 0
  set d := f_bar.rootMultiplicity 0 with hd_def

  have hXC : (X : (A ⧸ 𝔭)[X]) - C 0 = X := by simp
  rw [hXC] at hfact hq_ndvd

  have hXd_not_unit : ¬IsUnit (X ^ d : (A ⧸ 𝔭)[X]) := by
    intro hu
    rw [Polynomial.isUnit_iff] at hu
    obtain ⟨r, _, hrp⟩ := hu
    have : (X ^ d : (A ⧸ 𝔭)[X]).natDegree = 0 := by rw [← hrp, Polynomial.natDegree_C]
    rw [Polynomial.natDegree_X_pow] at this
    omega

  have hq_not_unit : ¬IsUnit q := by
    intro hqu

    rw [Polynomial.isUnit_iff] at hqu
    obtain ⟨r, hr_unit, hrq⟩ := hqu


    have hcomap₂ : Ideal.comap (algebraMap A B) 𝔮₂ = 𝔭 :=
      maximal_lies_over_in_AKLB A K L B 𝔮₂ h₂
    have hlift_cond : ∀ a ∈ 𝔭, ((Ideal.Quotient.mk 𝔮₂).comp (algebraMap A B)) a = 0 := by
      intro a ha
      simp only [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      rwa [← Ideal.mem_comap, hcomap₂]
    set g := Ideal.Quotient.lift 𝔭 ((Ideal.Quotient.mk 𝔮₂).comp (algebraMap A B)) hlift_cond

    have hg_comp : g.comp π = (Ideal.Quotient.mk 𝔮₂).comp (algebraMap A B) :=
      Ideal.Quotient.lift_comp_mk 𝔭 _ hlift_cond

    set b_bar₂ := Ideal.Quotient.mk 𝔮₂ b with hb_bar₂_def
    have heval_fbar : Polynomial.eval₂ g b_bar₂ f_bar = 0 := by
      rw [hf_bar_def, Polynomial.eval₂_map, hg_comp]


      rw [← Polynomial.hom_eval₂ f (algebraMap A B) (Ideal.Quotient.mk 𝔮₂) b]


      have : Polynomial.eval₂ (algebraMap A B) b f = 0 := by
        rw [← Polynomial.aeval_def]; exact minpoly.aeval A b
      rw [this, map_zero]

    have heval_expand : g r * b_bar₂ ^ d = 0 := by
      rw [hfact, ← hrq, mul_comm] at heval_fbar
      rwa [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at heval_fbar

    have hgr_unit : IsUnit (g r) := g.isUnit_map hr_unit

    haveI : Nontrivial (B ⧸ 𝔮₂) := Ideal.Quotient.nontrivial_iff.mpr h₂.ne_top
    have hgr_ne_zero : g r ≠ 0 := hgr_unit.ne_zero

    have hbd_zero : b_bar₂ ^ d = 0 := by
      rcases mul_eq_zero.mp heval_expand with h | h
      · exact absurd h hgr_ne_zero
      · exact h

    haveI : IsDomain (B ⧸ 𝔮₂) := by
      exact Ideal.Quotient.isDomain 𝔮₂
    have hb_bar_zero : b_bar₂ = 0 :=
      (pow_eq_zero_iff (by omega : d ≠ 0)).mp hbd_zero

    exact hb₂ (Ideal.Quotient.eq_zero_iff_mem.mp hb_bar_zero)

  have hcoprime : IsCoprime q (X ^ d) :=
    Irreducible.coprime_pow_of_not_dvd d Polynomial.irreducible_X hq_ndvd

  exact ⟨q, X ^ d, by rw [hfact, mul_comm], hcoprime, hq_not_unit, hXd_not_unit⟩

theorem unique_maximal_ideal_of_complete_DVR
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra A L] [IsScalarTower A K L]
    (B : Type*) [CommRing B] [IsDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L]
    (𝔮₁ 𝔮₂ : Ideal B) (h₁ : 𝔮₁.IsMaximal) (h₂ : 𝔮₂.IsMaximal) :
    𝔮₁ = 𝔮₂ := by
  by_contra hne
  haveI : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A K L B

  have hne' : ¬(𝔮₁ ≤ 𝔮₂) := by
    intro h
    exact hne (h₁.eq_of_le h₂.ne_top h)
  obtain ⟨b, hb₁, hb₂⟩ := Set.not_subset.mp hne'
  have hbint : IsIntegral A b := IsIntegralClosure.isIntegral A L b
  have hirr : Irreducible (minpoly A b) := minpoly.irreducible hbint

  obtain ⟨g_bar, h_bar, hfact, hcoprime, hg_nu, hh_nu⟩ :=
    two_maximal_ideals_give_coprime_factorization (K := K) (L := L) 𝔮₁ 𝔮₂ h₁ h₂ hne b hb₁ hb₂ hbint hirr

  rcases irreducible_no_coprime_factor_mod hirr g_bar h_bar hfact hcoprime with hu | hu
  · exact hg_nu hu
  · exact hh_nu hu

theorem integral_closure_complete_DVR_is_DVR
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra A L] [IsScalarTower A K L]
    (B : Type*) [CommRing B] [IsDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] :
    IsDiscreteValuationRing B := by
  haveI : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A K L B
  have hB_not_field : ¬IsField B := by
    intro hfield
    haveI : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L
    have hinj : Function.Injective (algebraMap A B) := by
      have h1 : Function.Injective (algebraMap A L) := by
        rw [IsScalarTower.algebraMap_eq A K L]
        exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
      intro a b hab
      exact h1 (by simp [IsScalarTower.algebraMap_eq A B L, hab])
    exact IsDiscreteValuationRing.not_isField A
      (isField_of_isIntegral_of_isField hinj hfield)
  obtain ⟨𝔮, h𝔮⟩ := Ideal.exists_maximal B
  have huniq : ∀ (I : Ideal B), I.IsMaximal → I = 𝔮 := fun I hI =>
    unique_maximal_ideal_of_complete_DVR A K L B I 𝔮 hI h𝔮
  haveI : IsLocalRing B := isLocalRing_of_unique_maximal B 𝔮 h𝔮 huniq
  exact isDVR_of_local_dedekind B hB_not_field

end IntegralClosureDVR
