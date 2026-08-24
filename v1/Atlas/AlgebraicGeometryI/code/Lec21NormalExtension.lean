/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Atlas.AlgebraicGeometryI.code.NormalExtension

open AlgebraicHartogs in
/-- An ideal of height at least `2` cannot be contained in a height-one prime. -/
theorem not_le_heightOnePrime_of_height_ge_two {A : Type*} [CommRing A]
    (I : Ideal A) (hI : 2 ≤ I.height) (p : HeightOnePrime A) : ¬(I ≤ p.asIdeal) := by
  intro hle
  have h1 : I.height ≤ p.asIdeal.height := Ideal.height_mono hle
  rw [p.height_eq] at h1
  exact absurd (le_trans hI h1) (by norm_num)

namespace Proposition39

section NormalDomain

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

/-- Key technical step: if `x ∈ K` is locally regular at every height-one prime and
`c · x` already lies in `A`, then `c · x²` also lies in `A`. Used inductively to bound
denominators when proving integrality. -/
theorem denominator_ideal_self_improvement
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    (x : K)
    (hx : ∀ (p : AlgebraicHartogs.HeightOnePrime A), x ∈ Localization.subalgebra.ofField K
      p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors)
    (c : A) (hc : algebraMap A K c * x ∈ Set.range (algebraMap A K)) :
    algebraMap A K c * x * x ∈ Set.range (algebraMap A K) := by
  sorry

/-- The `A`-linear map `A → K` sending `a ↦ a / b`, used to realise `A[x] ⊆ K` as a
submodule of a finitely generated `A`-module when `b` clears all denominators of `A[x]`. -/
noncomputable def divByMap (b : A) : A →ₗ[A] K where
  toFun a := algebraMap A K a * (algebraMap A K b)⁻¹
  map_add' a₁ a₂ := by simp [add_mul]
  map_smul' r a := by
    simp only [RingHom.id_apply, smul_eq_mul, map_mul, Algebra.smul_def]; ring

/-- If `x ∈ K` lies in the localization of `A` at every height-one prime, then `x` is
integral over `A`. This is a key input to Hartogs/normal-domain results. -/
theorem isIntegral_of_mem_heightOnePrime_localizations
    (x : K)
    (hx : ∀ (p : AlgebraicHartogs.HeightOnePrime A), x ∈ Localization.subalgebra.ofField K
      p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors) :
    IsIntegral A x := by

  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A x
  have hbx : algebraMap A K b * x ∈ Set.range (algebraMap A K) :=
    ⟨a, by rw [← hab, div_eq_mul_inv, ← mul_assoc, mul_comm (algebraMap A K b), mul_assoc,
              mul_inv_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb),
              mul_one]⟩

  have hpow : ∀ n : ℕ, algebraMap A K b * x ^ n ∈ Set.range (algebraMap A K) := by
    suffices h : ∀ n, algebraMap A K b * x ^ n ∈ Set.range (algebraMap A K) ∧
                       algebraMap A K b * x ^ (n + 1) ∈ Set.range (algebraMap A K) from
      fun n => (h n).1
    intro n; induction n with
    | zero => exact ⟨⟨b, by simp⟩, by simpa [pow_one] using hbx⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      obtain ⟨cn, hcn⟩ := ih.1
      have hcnx : algebraMap A K cn * x ∈ Set.range (algebraMap A K) := by
        have : algebraMap A K cn * x = algebraMap A K b * x ^ (n + 1) := by rw [hcn]; ring
        rw [this]; exact ih.2
      rw [show algebraMap A K b * x ^ (n + 2) = algebraMap A K cn * x * x from by rw [hcn]; ring]
      exact denominator_ideal_self_improvement x hx cn hcnx

  have haeval : ∀ p : Polynomial A,
      algebraMap A K b * Polynomial.aeval x p ∈ Set.range (algebraMap A K) := by
    intro p; induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      rw [map_add, mul_add]
      obtain ⟨ap, hap⟩ := hp; obtain ⟨aq, haq⟩ := hq
      exact ⟨ap + aq, by rw [map_add, hap, haq]⟩
    | monomial n c =>
      simp only [Polynomial.aeval_monomial]
      obtain ⟨d, hd⟩ := hpow n
      exact ⟨c * d, by rw [map_mul, show algebraMap A K b * (algebraMap A K c * x ^ n) =
          algebraMap A K c * (algebraMap A K b * x ^ n) from by ring, hd]⟩

  have hbK_ne : algebraMap A K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hle : Subalgebra.toSubmodule (Algebra.adjoin A ({x} : Set K)) ≤
      (divByMap (A := A) (K := K) b).range := by
    intro y hy
    rw [Subalgebra.mem_toSubmodule] at hy
    have hy' : y ∈ (Polynomial.aeval (R := A) x).range := by
      rwa [Algebra.adjoin_singleton_eq_range_aeval] at hy
    obtain ⟨p, hp⟩ := hy'
    obtain ⟨c, hc⟩ := haeval p
    exact ⟨c, by simp only [divByMap, LinearMap.coe_mk, AddHom.coe_mk]
                ; rw [hc, mul_comm (algebraMap A K b) _, mul_assoc, mul_inv_cancel₀ hbK_ne,
                    mul_one]
                ; exact hp⟩

  have hnoeth_range : IsNoetherian A ↥((divByMap (A := A) (K := K) b).range) :=
    isNoetherian_of_surjective (divByMap (A := A) (K := K) b).rangeRestrict
      (LinearMap.range_rangeRestrict _)

  exact isIntegral_of_submodule_noetherian (Algebra.adjoin A {x}) (isNoetherian_of_le hle) x
    (Algebra.subset_adjoin (Set.mem_singleton x))

/-- For an integrally closed Noetherian domain, the intersection of all height-one
localizations inside its fraction field equals `A` itself. -/
theorem iInf_heightOnePrime_localization_eq_bot :
    (⨅ (p : AlgebraicHartogs.HeightOnePrime A), Localization.subalgebra.ofField K
      p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ := by
  apply le_antisymm
  · intro x hx
    rw [Algebra.mem_bot]
    have hmem : ∀ (p : AlgebraicHartogs.HeightOnePrime A), x ∈ Localization.subalgebra.ofField K
        p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors :=
      fun p => Algebra.mem_iInf.mp hx p
    exact IsIntegrallyClosed.isIntegral_iff.mp
      (isIntegral_of_mem_heightOnePrime_localizations x hmem)
  · exact bot_le

/-- An element of the fraction field that lies in every height-one localization of a
normal Noetherian domain already lies in the ring itself. -/
theorem mem_of_mem_heightOnePrime_localizations (x : K)
    (hx : ∀ (p : AlgebraicHartogs.HeightOnePrime A), x ∈ Localization.subalgebra.ofField K
      p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors) :
    x ∈ Set.range (algebraMap A K) := by
  rw [← Algebra.mem_bot, ← iInf_heightOnePrime_localization_eq_bot]
  exact Algebra.mem_iInf.mpr hx

/-- Proposition 39 (codimension-2 extension): For a normal Noetherian domain, any element
of the fraction field that is regular outside a closed subset of codimension `≥ 2`
extends globally to a regular function on `Spec A`. -/
theorem proposition39_codim2_extension (I : Ideal A) (hI : 2 ≤ I.height) (x : K)
    (hx : ∀ (p : PrimeSpectrum A), ¬(I ≤ p.asIdeal) → x ∈ Localization.subalgebra.ofField K
      p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors) :
    x ∈ Set.range (algebraMap A K) := by
  apply mem_of_mem_heightOnePrime_localizations
  intro p
  have hnotI : ¬(I ≤ p.asIdeal) := not_le_heightOnePrime_of_height_ge_two I hI p
  exact hx ⟨p.asIdeal, p.isPrime⟩ hnotI

/-- Proposition 39 (set-theoretic form): For a normal Noetherian domain `A` and an ideal of
height at least `2`, `A` equals the intersection of all localizations at primes not
containing that ideal. -/
theorem proposition39_range (I : Ideal A) (hI : 2 ≤ I.height) :
    Set.range (algebraMap A K) =
    ⋂ (p : PrimeSpectrum A) (_ : ¬(I ≤ p.asIdeal)),
      (Localization.subalgebra.ofField K
        p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors : Set K) := by
  ext x
  constructor
  · intro ⟨a, ha⟩
    simp only [Set.mem_iInter]
    intro p _
    rw [← ha]
    exact (Localization.subalgebra.ofField K p.asIdeal.primeCompl
      p.asIdeal.primeCompl_le_nonZeroDivisors).algebraMap_mem a
  · intro hx
    apply proposition39_codim2_extension I hI
    intro p hp
    exact Set.mem_iInter.mp (Set.mem_iInter.mp hx p) hp

end NormalDomain

end Proposition39
