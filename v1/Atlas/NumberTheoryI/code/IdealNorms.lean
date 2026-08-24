/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.KummerDedekind
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind

open nonZeroDivisors DirectSum


section LocalModuleIndex

variable {R : Type*} [CommRing R] [IsDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {M : Type*} [AddCommGroup M] [Module R M]

noncomputable def localModuleIndex (φ : M →ₗ[R] M) : FractionalIdeal R⁰ K :=
  FractionalIdeal.spanSingleton R⁰ (algebraMap R K (LinearMap.det φ))

theorem localModuleIndex_comp_equiv (φ : M →ₗ[R] M) (u v : M ≃ₗ[R] M) :
    localModuleIndex (K := K) ((u : M →ₗ[R] M) ∘ₗ φ ∘ₗ (v : M →ₗ[R] M)) =
    localModuleIndex (K := K) φ := by
  simp only [localModuleIndex, LinearMap.det_comp, map_mul]
  rw [FractionalIdeal.spanSingleton_eq_spanSingleton]
  refine ⟨(LinearEquiv.det u)⁻¹ * (LinearEquiv.det v)⁻¹, ?_⟩
  simp only [Units.smul_def, Units.val_mul, Algebra.smul_def, ← LinearEquiv.coe_det, ← map_mul]
  congr 1
  have hu := Units.inv_mul (LinearEquiv.det u)
  have hv := Units.inv_mul (LinearEquiv.det v)
  calc ↑(LinearEquiv.det u)⁻¹ * ↑(LinearEquiv.det v)⁻¹ *
      (↑(LinearEquiv.det u) * (LinearMap.det φ * ↑(LinearEquiv.det v)))
      = (↑(LinearEquiv.det u)⁻¹ * ↑(LinearEquiv.det u)) *
        (↑(LinearEquiv.det v)⁻¹ * ↑(LinearEquiv.det v)) * LinearMap.det φ := by ring
    _ = 1 * 1 * LinearMap.det φ := by rw [hu, hv]
    _ = LinearMap.det φ := by ring

omit [IsDomain R] in
theorem localModuleIndex_comp (φ ψ : M →ₗ[R] M) :
    localModuleIndex (K := K) (φ ∘ₗ ψ) =
    localModuleIndex (K := K) φ * localModuleIndex (K := K) ψ := by
  simp only [localModuleIndex, LinearMap.det_comp, map_mul,
    FractionalIdeal.spanSingleton_mul_spanSingleton]

omit [IsDomain R] in
@[simp]
theorem localModuleIndex_id :
    localModuleIndex (K := K) (LinearMap.id : M →ₗ[R] M) = 1 := by
  simp [localModuleIndex, LinearMap.det_id, map_one, FractionalIdeal.spanSingleton_one]

end LocalModuleIndex

section GlobalModuleIndex

lemma prod_ne_zero_of_ne_bot
    {A : Type*} [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {n : ℕ} (J : Fin n → Ideal A) (hJ : ∀ i, J i ≠ ⊥) :
    (↑(∏ i : Fin n, J i) : FractionalIdeal A⁰ K) ≠ 0 := by
  rw [FractionalIdeal.coeIdeal_ne_zero]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_castSucc, Ne, Ideal.mul_eq_bot]
    push Not
    exact ⟨ih (J ∘ Fin.castSucc) (fun i => hJ (Fin.castSucc i)), hJ (Fin.last n)⟩

theorem locally_free_becomes_free_after_inverting
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (M N : Submodule A V) [Module.Finite A ↥M] [Module.Finite A ↥N] :
    ∃ (I : FractionalIdeal A⁰ K), I ≠ 0 ∧
      (∀ (v : IsDedekindDomain.HeightOneSpectrum A) (φ : V →ₗ[A] V)
        (_ : ∀ (x : V), x ∈ M ↔ φ x ∈ N),
        FractionalIdeal.count K v I =
          FractionalIdeal.count K v
            (FractionalIdeal.spanSingleton A⁰ (algebraMap A K (LinearMap.det φ)))) := by sorry

theorem comparison_map_membership
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (M N : Submodule A V) [Module.Finite A ↥M] [Module.Finite A ↥N] :
    ∃ (φ : V →ₗ[A] V), ∀ (x : V), x ∈ M ↔ φ x ∈ N := by sorry

theorem comparison_map_det_ne_zero
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (M N : Submodule A V) [Module.Finite A ↥M] [Module.Finite A ↥N]
    (φ : V →ₗ[A] V) (hφ : ∀ (x : V), x ∈ M ↔ φ x ∈ N) :
    algebraMap A K (LinearMap.det φ) ≠ 0 := by sorry

theorem lattice_comparison_map_exists
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (M N : Submodule A V) [Module.Finite A ↥M] [Module.Finite A ↥N] :
    ∃ (φ : V →ₗ[A] V), (∀ (x : V), x ∈ M ↔ φ x ∈ N) ∧
      algebraMap A K (LinearMap.det φ) ≠ 0 := by
  obtain ⟨φ, hφ⟩ := comparison_map_membership K M N
  exact ⟨φ, hφ, comparison_map_det_ne_zero K M N φ hφ⟩

theorem snf_det_eq_prod_count_at_prime
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (M N : Submodule A V) [Module.Finite A ↥M] [Module.Finite A ↥N] (_ : N ≤ M) {n : ℕ} (J : Fin n → Ideal A)
    (_ : ∀ i, J i ≠ ⊥)
    (_ : (↥M ⧸ N.comap M.subtype) ≃ₗ[A] ⨁ i : Fin n, (A ⧸ J i))
    (φ : V →ₗ[A] V) (_ : ∀ (x : V), x ∈ M ↔ φ x ∈ N)
    (v : IsDedekindDomain.HeightOneSpectrum A) :
    FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton A⁰ (algebraMap A K (LinearMap.det φ))) =
      FractionalIdeal.count K v ((∏ i : Fin n, J i : Ideal A) : FractionalIdeal A⁰ K) := by sorry

theorem snf_local_ideal_eq_prod
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (M N : Submodule A V) [Module.Finite A ↥M] [Module.Finite A ↥N] (hle : N ≤ M) {n : ℕ} (J : Fin n → Ideal A)
    (hJ : ∀ i, J i ≠ ⊥)
    (hiso : (↥M ⧸ N.comap M.subtype) ≃ₗ[A] ⨁ i : Fin n, (A ⧸ J i))
    (φ : V →ₗ[A] V) (hφ : ∀ (x : V), x ∈ M ↔ φ x ∈ N)
    (P : Ideal A) (_ : P.IsMaximal) :
    Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.span {LinearMap.det φ}) =
      Ideal.map (algebraMap A (Localization.AtPrime P)) (∏ i : Fin n, J i) := by

  suffices h : Ideal.span {LinearMap.det φ} = ∏ i : Fin n, J i by rw [h]

  have hdet_ne : algebraMap A K (LinearMap.det φ) ≠ 0 :=
    comparison_map_det_ne_zero K M N φ hφ
  have hss_ne : FractionalIdeal.spanSingleton A⁰ (algebraMap A K (LinearMap.det φ)) ≠ 0 := by
    rwa [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]

  have hprod_ne_bot : ∏ i : Fin n, J i ≠ ⊥ := by
    simp only [ne_eq, ← Ideal.zero_eq_bot] at *
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hJ i)
  have hprod_ne : (↑(∏ i : Fin n, J i) : FractionalIdeal A⁰ K) ≠ 0 := by
    rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero]

  have hcounts : ∀ v : IsDedekindDomain.HeightOneSpectrum A,
      FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton A⁰ (algebraMap A K (LinearMap.det φ))) =
      FractionalIdeal.count K v (↑(∏ i : Fin n, J i) : FractionalIdeal A⁰ K) :=
    snf_det_eq_prod_count_at_prime K M N hle J hJ hiso φ hφ

  have hfrac : FractionalIdeal.spanSingleton A⁰ (algebraMap A K (LinearMap.det φ)) =
      (↑(∏ i : Fin n, J i) : FractionalIdeal A⁰ K) := by
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hss_ne,
        ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hprod_ne]
    simp_rw [hcounts]

  rw [← FractionalIdeal.coeIdeal_span_singleton] at hfrac
  exact FractionalIdeal.coeIdeal_injective hfrac

theorem snf_ideal_eq_prod
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (M N : Submodule A V) [Module.Finite A ↥M] [Module.Finite A ↥N] (hle : N ≤ M) {n : ℕ} (J : Fin n → Ideal A)
    (hJ : ∀ i, J i ≠ ⊥)
    (hiso : (↥M ⧸ N.comap M.subtype) ≃ₗ[A] ⨁ i : Fin n, (A ⧸ J i))
    (φ : V →ₗ[A] V) (hφ : ∀ (x : V), x ∈ M ↔ φ x ∈ N) :
    Ideal.span {LinearMap.det φ} = ∏ i : Fin n, J i :=
  Ideal.eq_of_localization_maximal fun P hP =>
    snf_local_ideal_eq_prod K M N hle J hJ hiso φ hφ P hP

theorem local_det_eq_prod_at_prime
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (M N : Submodule A V) [Module.Finite A ↥M] [Module.Finite A ↥N] (hle : N ≤ M) {n : ℕ} (J : Fin n → Ideal A)
    (hJ : ∀ i, J i ≠ ⊥)
    (hiso : (↥M ⧸ N.comap M.subtype) ≃ₗ[A] ⨁ i : Fin n, (A ⧸ J i))
    (φ : V →ₗ[A] V) (hφ : ∀ (x : V), x ∈ M ↔ φ x ∈ N)
    (P : Ideal A) (hP : P.IsMaximal) :
    Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.span {LinearMap.det φ}) =
      Ideal.map (algebraMap A (Localization.AtPrime P)) (∏ i : Fin n, J i) := by

  suffices h : Ideal.span {LinearMap.det φ} = ∏ i : Fin n, J i by rw [h]

  have hdet_ne : algebraMap A K (LinearMap.det φ) ≠ 0 :=
    comparison_map_det_ne_zero K M N φ hφ
  have hss_ne : FractionalIdeal.spanSingleton A⁰ (algebraMap A K (LinearMap.det φ)) ≠ 0 := by
    rwa [ne_eq, FractionalIdeal.spanSingleton_eq_zero_iff]
  have hprod_ne_bot : ∏ i : Fin n, J i ≠ ⊥ := by
    simp only [ne_eq, ← Ideal.zero_eq_bot] at *
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hJ i)
  have hprod_ne : (↑(∏ i : Fin n, J i) : FractionalIdeal A⁰ K) ≠ 0 := by
    rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero]

  have hfrac : FractionalIdeal.spanSingleton A⁰ (algebraMap A K (LinearMap.det φ)) =
      (↑(∏ i : Fin n, J i) : FractionalIdeal A⁰ K) := by
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hss_ne,
        ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hprod_ne]
    simp_rw [snf_det_eq_prod_count_at_prime K M N hle J hJ hiso φ hφ]

  rw [← FractionalIdeal.coeIdeal_span_singleton] at hfrac
  exact FractionalIdeal.coeIdeal_injective hfrac

theorem smith_normal_form_det_eq_prod_global
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (M N : Submodule A V) [Module.Finite A ↥M] [Module.Finite A ↥N] (hle : N ≤ M) {n : ℕ} (J : Fin n → Ideal A)
    (hJ : ∀ i, J i ≠ ⊥)
    (hiso : (↥M ⧸ N.comap M.subtype) ≃ₗ[A] ⨁ i : Fin n, (A ⧸ J i))
    (φ : V →ₗ[A] V) (hφ : ∀ (x : V), x ∈ M ↔ φ x ∈ N) :
    Ideal.span {LinearMap.det φ} = ∏ i : Fin n, J i :=
  Ideal.eq_of_localization_maximal fun P hP =>
    local_det_eq_prod_at_prime K M N hle J hJ hiso φ hφ P hP

theorem smith_normal_form_local_at_prime
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (M N : Submodule A V) [Module.Finite A ↥M] [Module.Finite A ↥N] (hle : N ≤ M) {n : ℕ} (J : Fin n → Ideal A)
    (hJ : ∀ i, J i ≠ ⊥)
    (hiso : (↥M ⧸ N.comap M.subtype) ≃ₗ[A] ⨁ i : Fin n, (A ⧸ J i))
    (φ : V →ₗ[A] V) (hφ : ∀ (x : V), x ∈ M ↔ φ x ∈ N)
    (P : Ideal A) (_ : P.IsMaximal) :
    Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.span {LinearMap.det φ}) =
      Ideal.map (algebraMap A (Localization.AtPrime P)) (∏ i : Fin n, J i) := by
  rw [smith_normal_form_det_eq_prod_global K M N hle J hJ hiso φ hφ]

theorem lattice_comparison_det_eq_prod
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (M N : Submodule A V) [Module.Finite A ↥M] [Module.Finite A ↥N] (hle : N ≤ M) {n : ℕ} (J : Fin n → Ideal A)
    (hJ : ∀ i, J i ≠ ⊥)
    (hiso : (↥M ⧸ N.comap M.subtype) ≃ₗ[A] ⨁ i : Fin n, (A ⧸ J i))
    (φ : V →ₗ[A] V) (hφ : ∀ (x : V), x ∈ M ↔ φ x ∈ N) :
    Ideal.span {LinearMap.det φ} = ∏ i : Fin n, J i :=
  smith_normal_form_det_eq_prod_global K M N hle J hJ hiso φ hφ

theorem smith_normal_form_det_eq_prod_count
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (M N : Submodule A V) [Module.Finite A ↥M] [Module.Finite A ↥N] (_ : N ≤ M) {n : ℕ} (J : Fin n → Ideal A)
    (_ : ∀ i, J i ≠ ⊥)
    (_ : (↥M ⧸ N.comap M.subtype) ≃ₗ[A] ⨁ i : Fin n, (A ⧸ J i))
    (φ : V →ₗ[A] V) (_ : ∀ (x : V), x ∈ M ↔ φ x ∈ N) :
    ∀ (v : IsDedekindDomain.HeightOneSpectrum A),
      FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton A⁰ (algebraMap A K (LinearMap.det φ))) =
      FractionalIdeal.count K v (↑(∏ i : Fin n, J i) : FractionalIdeal A⁰ K) := by
  intro v

  have h_ideal := lattice_comparison_det_eq_prod K M N ‹_› J ‹_› ‹_› φ ‹_›


  rw [← FractionalIdeal.coeIdeal_span_singleton, h_ideal]

theorem product_property_from_local_analysis
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (M N : Submodule A V) [Module.Finite A ↥M] [Module.Finite A ↥N]
    (I : FractionalIdeal A⁰ K) (hI : I ≠ 0)
    (hcount : ∀ (v : IsDedekindDomain.HeightOneSpectrum A) (φ : V →ₗ[A] V)
        (_ : ∀ (x : V), x ∈ M ↔ φ x ∈ N),
        FractionalIdeal.count K v I =
          FractionalIdeal.count K v
            (FractionalIdeal.spanSingleton A⁰ (algebraMap A K (LinearMap.det φ)))) :
    ∀ (_ : N ≤ M) {n : ℕ} (J : Fin n → Ideal A) (_ : ∀ i, J i ≠ ⊥)
        (_ : (↥M ⧸ N.comap M.subtype) ≃ₗ[A] ⨁ (i : Fin n), (A ⧸ J i)),
        I = (↑(∏ i : Fin n, J i) : FractionalIdeal A⁰ K) := by
  intro hle n J hJ hiso

  obtain ⟨φ, hφ, hdet⟩ := lattice_comparison_map_exists K M N

  have hprod_ne_bot : ∏ i : Fin n, J i ≠ ⊥ := by
    simp only [ne_eq, ← Ideal.zero_eq_bot] at *
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hJ i)
  have hprod_ne_zero : (↑(∏ i : Fin n, J i) : FractionalIdeal A⁰ K) ≠ 0 := by
    rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero]

  have hcounts_eq : ∀ v : IsDedekindDomain.HeightOneSpectrum A,
      FractionalIdeal.count K v I =
        FractionalIdeal.count K v (↑(∏ i : Fin n, J i) : FractionalIdeal A⁰ K) := by
    intro v

    rw [hcount v φ hφ]

    exact smith_normal_form_det_eq_prod_count K M N hle J hJ hiso φ hφ v

  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hprod_ne_zero]
  simp_rw [hcounts_eq]

theorem dedekind_domain_glue_local_to_global
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (M N : Submodule A V) [Module.Finite A ↥M] [Module.Finite A ↥N] :
    ∃ (I : FractionalIdeal A⁰ K),
      I ≠ 0 ∧
      (∀ (_ : N ≤ M) {n : ℕ} (J : Fin n → Ideal A) (_ : ∀ i, J i ≠ ⊥)
        (_ : (↥M ⧸ N.comap M.subtype) ≃ₗ[A] ⨁ (i : Fin n), (A ⧸ J i)),
        I = (↑(∏ i : Fin n, J i) : FractionalIdeal A⁰ K)) ∧
      (∀ (v : IsDedekindDomain.HeightOneSpectrum A) (φ : V →ₗ[A] V)
        (_ : ∀ (x : V), x ∈ M ↔ φ x ∈ N),
        FractionalIdeal.count K v I =
          FractionalIdeal.count K v
            (FractionalIdeal.spanSingleton A⁰ (algebraMap A K (LinearMap.det φ)))) := by


  obtain ⟨I, hI, hcount⟩ := locally_free_becomes_free_after_inverting K M N


  have hprod := product_property_from_local_analysis K M N I hI hcount

  exact ⟨I, hI, hprod, hcount⟩

theorem moduleIndex_exists_with_product
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (M N : Submodule A V) [Module.Finite A ↥M] [Module.Finite A ↥N] :
    ∃ (I : FractionalIdeal A⁰ K),
      I ≠ 0 ∧
      ∀ (_ : N ≤ M) {n : ℕ} (J : Fin n → Ideal A) (_ : ∀ i, J i ≠ ⊥)
        (_ : (↥M ⧸ N.comap M.subtype) ≃ₗ[A] ⨁ (i : Fin n), (A ⧸ J i)),
        I = (↑(∏ i : Fin n, J i) : FractionalIdeal A⁰ K) := by
  obtain ⟨I, hne, hprod, _⟩ := dedekind_domain_glue_local_to_global K M N
  exact ⟨I, hne, hprod⟩

noncomputable def moduleIndex
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (M N : Submodule A V) [Module.Finite A ↥M] [Module.Finite A ↥N] : FractionalIdeal A⁰ K :=
  (dedekind_domain_glue_local_to_global K M N).choose

theorem moduleIndex_ne_zero
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (M N : Submodule A V) [Module.Finite A ↥M] [Module.Finite A ↥N] :
    moduleIndex K M N ≠ 0 :=
  (dedekind_domain_glue_local_to_global K M N).choose_spec.1

theorem moduleIndex_count_eq_local
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (M N : Submodule A V) [Module.Finite A ↥M] [Module.Finite A ↥N]
    (v : IsDedekindDomain.HeightOneSpectrum A) (φ : V →ₗ[A] V)
    (hφ : ∀ (x : V), x ∈ M ↔ φ x ∈ N) :
    FractionalIdeal.count K v (moduleIndex K M N) =
      FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton A⁰ (algebraMap A K (LinearMap.det φ))) :=
  (dedekind_domain_glue_local_to_global K M N).choose_spec.2.2 v φ hφ

theorem proposition_6_2
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
    [FiniteDimensional K V]
    (M N : Submodule A V) [Module.Finite A ↥M] [Module.Finite A ↥N] :
    moduleIndex K M N ≠ 0 ∧
      ∀ (v : IsDedekindDomain.HeightOneSpectrum A) (φ : V →ₗ[A] V),
        (∀ x, x ∈ M ↔ φ x ∈ N) →
          FractionalIdeal.count K v (moduleIndex K M N) =
            FractionalIdeal.count K v
              (FractionalIdeal.spanSingleton A⁰ (algebraMap A K (LinearMap.det φ))) :=
  ⟨moduleIndex_ne_zero K M N, fun v φ hφ => moduleIndex_count_eq_local K M N v φ hφ⟩

theorem moduleIndex_mul
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (M N P : Submodule A V) [Module.Finite A ↥M] [Module.Finite A ↥N] [Module.Finite A ↥P] :
    moduleIndex K M P = moduleIndex K M N * moduleIndex K N P := by

  obtain ⟨φ₁, hφ₁, hdet₁⟩ := lattice_comparison_map_exists K M N
  obtain ⟨φ₂, hφ₂, hdet₂⟩ := lattice_comparison_map_exists K N P

  have hφ : ∀ x, x ∈ M ↔ (φ₂ ∘ₗ φ₁) x ∈ P := by
    intro x; simp only [LinearMap.comp_apply]; rw [hφ₁, hφ₂]

  have hne_MP := moduleIndex_ne_zero K M P
  have hne_MN := moduleIndex_ne_zero K M N
  have hne_NP := moduleIndex_ne_zero K N P

  have hne_s1 : FractionalIdeal.spanSingleton A⁰ (algebraMap A K (LinearMap.det φ₁)) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hdet₁
  have hne_s2 : FractionalIdeal.spanSingleton A⁰ (algebraMap A K (LinearMap.det φ₂)) ≠ 0 :=
    FractionalIdeal.spanSingleton_ne_zero_iff.mpr hdet₂

  have hcount : ∀ v : IsDedekindDomain.HeightOneSpectrum A,
      FractionalIdeal.count K v (moduleIndex K M P) =
        FractionalIdeal.count K v (moduleIndex K M N * moduleIndex K N P) := by
    intro v

    have hL := moduleIndex_count_eq_local K M P v (φ₂ ∘ₗ φ₁) hφ
    have hL1 := moduleIndex_count_eq_local K M N v φ₁ hφ₁
    have hL2 := moduleIndex_count_eq_local K N P v φ₂ hφ₂

    rw [hL]

    rw [LinearMap.det_comp, map_mul, ← FractionalIdeal.spanSingleton_mul_spanSingleton]

    rw [FractionalIdeal.count_mul K v hne_MN hne_NP, hL1, hL2]

    rw [FractionalIdeal.count_mul K v hne_s2 hne_s1]
    ring

  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hne_MP,
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K
        (mul_ne_zero hne_MN hne_NP)]
  simp_rw [hcount]

theorem moduleIndex_self
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (M : Submodule A V) [Module.Finite A ↥M] :
    moduleIndex K M M = 1 := by
  have hne : moduleIndex K M M ≠ 0 := moduleIndex_ne_zero K M M
  have hcount : ∀ v : IsDedekindDomain.HeightOneSpectrum A,
      FractionalIdeal.count K v (moduleIndex K M M) = FractionalIdeal.count K v 1 := by
    intro v
    have h := moduleIndex_count_eq_local K M M v LinearMap.id (fun x => Iff.rfl)
    simp only [LinearMap.det_id, map_one, FractionalIdeal.spanSingleton_one] at h
    exact h
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hne]
  simp_rw [hcount, FractionalIdeal.count_one, zpow_zero, finprod_one]

theorem moduleIndex_swap
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (M N : Submodule A V) [Module.Finite A ↥M] [Module.Finite A ↥N] :
    moduleIndex K N M = (moduleIndex K M N)⁻¹ := by
  have h1 : moduleIndex K M N * moduleIndex K N M = 1 := by
    rw [← moduleIndex_mul K M N M, moduleIndex_self]
  rw [eq_comm, inv_eq_of_mul_eq_one_right h1]

end GlobalModuleIndex

section CyclicQuotient

theorem moduleIndex_eq_prod
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V] [FiniteDimensional K V]
    (M : Submodule A V) (N : Submodule A V) [Module.Finite A ↥M] [Module.Finite A ↥N] (hNM : N ≤ M)
    {n : ℕ} (I : Fin n → Ideal A) (hI : ∀ i, I i ≠ ⊥)
    (hiso : (↥M ⧸ N.comap M.subtype) ≃ₗ[A] ⨁ (i : Fin n), (A ⧸ I i)) :
    moduleIndex K M N = (↑(∏ i : Fin n, I i) : FractionalIdeal A⁰ K) :=
  (dedekind_domain_glue_local_to_global K M N).choose_spec.2.1 hNM I hI hiso

end CyclicQuotient


section ConcreteModuleIndex

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

noncomputable def concreteModuleIndex (N : Submodule R M) : ℕ :=
  Nat.card (M ⧸ N)

theorem concreteModuleIndex_eq_cardQuot (N : Submodule R M) :
    concreteModuleIndex N = Submodule.cardQuot N :=
  (Submodule.cardQuot_apply N).symm

@[simp]
theorem concreteModuleIndex_top :
    concreteModuleIndex (⊤ : Submodule R M) = 1 := by
  rw [concreteModuleIndex_eq_cardQuot, Submodule.cardQuot_top]

theorem concreteModuleIndex_mul_tower (N P : Submodule R M) (hPN : P ≤ N) :
    Nat.card ↥(N.map P.mkQ) * Nat.card (M ⧸ N) = Nat.card (M ⧸ P) :=
  Submodule.card_quotient_mul_card_quotient N P hPN

theorem concreteModuleIndex_ideal_mul {S : Type*} [CommRing S] [IsDedekindDomain S]
    [Module.Free ℤ S] (I J : Ideal S) :
    Nat.card (S ⧸ (I * J : Ideal S)) = Nat.card (S ⧸ I) * Nat.card (S ⧸ J) := by
  rw [← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply]
  exact cardQuot_mul I J

end ConcreteModuleIndex

section DetFormula

variable {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]

open Module in
theorem concreteModuleIndex_eq_natAbs_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℤ M) (N : Submodule ℤ M) (bN : Basis ι ℤ N) :
    (b.det ((↑) ∘ bN)).natAbs = concreteModuleIndex N :=
  Submodule.natAbs_det_basis_change b N bN

open Module in
theorem concreteModuleIndex_eq_natAbs_det_equiv (N : Submodule ℤ M) {E : Type*}
    [EquivLike E M N] [AddEquivClass E M N] (e : E) :
    Int.natAbs (LinearMap.det (N.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : M →+ N))) =
      concreteModuleIndex N :=
  Submodule.natAbs_det_equiv N e

end DetFormula

section NormConcreteIndex

open NumberField

theorem idealNorm_eq_concreteModuleIndex {K : Type*} [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) :
    Ideal.absNorm I = concreteModuleIndex (I : Submodule (𝓞 K) (𝓞 K)) := by
  rw [concreteModuleIndex, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem absNorm_mul_eq {K : Type*} [Field K] [NumberField K]
    (I J : Ideal (𝓞 K)) :
    Ideal.absNorm (I * J) = Ideal.absNorm I * Ideal.absNorm J :=
  map_mul (Ideal.absNorm) I J

end NormConcreteIndex


open Ideal Polynomial UniqueFactorizationMonoid

namespace DedekindKummer

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [IsDomain R] [IsIntegrallyClosed R] [IsDedekindDomain S] [Module.IsTorsionFree R S]
variable {x : S} {I : Ideal R}

attribute [local instance] Ideal.Quotient.field

open Classical in
noncomputable def dedekind_kummer_bijection
    (hI : I.IsMaximal) (hI' : I ≠ ⊥)
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (hx' : IsIntegral R x) :
    {J : Ideal S | J ∈ normalizedFactors (I.map (algebraMap R S))} ≃
      {d : (R ⧸ I)[X] |
        d ∈ normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))} :=
  KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx'

open Classical in
theorem dedekind_kummer_multiplicity
    (hI : I.IsMaximal) (hI' : I ≠ ⊥)
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (hx' : IsIntegral R x)
    {J : Ideal S} (hJ : J ∈ normalizedFactors (I.map (algebraMap R S))) :
    emultiplicity J (I.map (algebraMap R S)) =
      emultiplicity
        (↑(dedekind_kummer_bijection hI hI' hx hx' ⟨J, hJ⟩))
        (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) :=
  KummerDedekind.emultiplicity_factors_map_eq_emultiplicity hI hI' hx hx' hJ

open Classical in
set_option backward.isDefEq.respectTransparency false in
theorem dedekind_kummer_prime_formula
    (hI : I.IsMaximal)
    {Q : R[X]}
    (hQ : Q.map (Ideal.Quotient.mk I) ∈
      normalizedFactors ((minpoly R x).map (Ideal.Quotient.mk I)))
    (hI' : I ≠ ⊥)
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (hx' : IsIntegral R x) :
    ((dedekind_kummer_bijection hI hI' hx hx').symm ⟨_, hQ⟩).val =
      Ideal.span (↑(I.map (algebraMap R S)) ∪ {Polynomial.aeval x Q}) :=
  KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span
    hI hQ hI' hx hx'

open Classical in
set_option backward.isDefEq.respectTransparency false in
theorem dedekind_kummer
    (hI : I.IsMaximal) (hI' : I ≠ ⊥)
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (hx' : IsIntegral R x) :
    normalizedFactors (I.map (algebraMap R S)) =
      Multiset.map
        (fun f =>
          ((dedekind_kummer_bijection hI hI' hx hx').symm f : Ideal S))
        (normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))).attach :=
  KummerDedekind.normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map hI hI' hx hx'

end DedekindKummer


section IdealNorm

variable (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsDedekindDomain A]
variable {B : Type*} [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsDedekindDomain B]
variable [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]

noncomputable def idealNorm : Ideal B →*₀ Ideal A := Ideal.relNorm A

@[simp] theorem idealNorm_def : (idealNorm A : Ideal B →*₀ Ideal A) = Ideal.relNorm A := rfl

theorem idealNorm_apply (I : Ideal B) :
    idealNorm A I = Ideal.span (Algebra.intNorm A B '' (I : Set B)) :=
  Ideal.relNorm_apply A I

@[simp] theorem idealNorm_zero : idealNorm A (0 : Ideal B) = 0 := map_zero (idealNorm A)

theorem idealNorm_ne_zero {I : Ideal B} (hI : I ≠ 0) : idealNorm A I ≠ 0 := by
  simp only [idealNorm, ne_eq]
  rw [show (0 : Ideal A) = ⊥ from rfl, Ideal.relNorm_eq_bot_iff,
      show (⊥ : Ideal B) = 0 from rfl]
  exact hI

theorem idealNorm_eq_zero_iff {I : Ideal B} : idealNorm A I = 0 ↔ I = 0 := by
  simp only [idealNorm, show (0 : Ideal A) = ⊥ from rfl, show (0 : Ideal B) = ⊥ from rfl,
    Ideal.relNorm_eq_bot_iff]

theorem idealNorm_mono {I J : Ideal B} (h : I ≤ J) : idealNorm A I ≤ idealNorm A J :=
  Ideal.relNorm_mono A h

theorem idealNorm_principal (α : B) :
    idealNorm A (Ideal.span {α}) = Ideal.span {Algebra.intNorm A B α} :=
  Ideal.relNorm_singleton A α

theorem idealNorm_principal_free [Module.Free A B] (α : B) :
    idealNorm A (Ideal.span {α}) = Ideal.span {Algebra.norm A α} := by
  rw [idealNorm_principal, Algebra.intNorm_eq_norm]

theorem idealNorm_mul (I J : Ideal B) :
    idealNorm A (I * J) = idealNorm A I * idealNorm A J :=
  map_mul (idealNorm A) I J

theorem idealNorm_one : idealNorm A (1 : Ideal B) = 1 := map_one (idealNorm A)

theorem relNorm_ne_bot_of_ne_bot
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    (I : Ideal B) (_ : I ≠ ⊥) :
    Ideal.relNorm A I ≠ ⊥ := by
  rwa [ne_eq, Ideal.relNorm_eq_bot_iff]

theorem relNorm_det_local_generator
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
    (I : Ideal B) (hI : I ≠ ⊥)
    (v : IsDedekindDomain.HeightOneSpectrum A)
    (φ : L →ₗ[A] L)
    (hφ : ∀ (x : L), x ∈ (⊤ : Submodule A L) ↔
      φ x ∈ (I.map (algebraMap B L)).restrictScalars A) :
    ∃ (b : B), b ≠ 0 ∧
      FractionalIdeal.count K v (↑(Ideal.relNorm A I) : FractionalIdeal A⁰ K) =
        FractionalIdeal.count K v
          (↑(Ideal.span {Algebra.intNorm A B b}) : FractionalIdeal A⁰ K) ∧
      FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton A⁰ (algebraMap A K (LinearMap.det φ))) =
        FractionalIdeal.count K v
          (↑(Ideal.span {Algebra.intNorm A B b}) : FractionalIdeal A⁰ K) := by sorry

theorem relNorm_count_eq_comparison_det
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
    (I : Ideal B) (hI : I ≠ ⊥)
    (v : IsDedekindDomain.HeightOneSpectrum A)
    (φ : L →ₗ[A] L)
    (hφ : ∀ (x : L), x ∈ (⊤ : Submodule A L) ↔
      φ x ∈ (I.map (algebraMap B L)).restrictScalars A) :
    FractionalIdeal.count K v (↑(Ideal.relNorm A I) : FractionalIdeal A⁰ K) =
      FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton A⁰ (algebraMap A K (LinearMap.det φ))) := by
  obtain ⟨b, _, h_relNorm, h_det⟩ := relNorm_det_local_generator K I hI v φ hφ
  rw [h_relNorm, ← h_det]

theorem relNorm_eq_moduleIndex_fractional_localization
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
    [Module.Finite A L]
    (I : Ideal B) (hI : I ≠ ⊥) :
    (↑(Ideal.relNorm A I) : FractionalIdeal A⁰ K) =
      moduleIndex K (⊤ : Submodule A L) ((I.map (algebraMap B L)).restrictScalars A) := by
  set N := (I.map (algebraMap B L)).restrictScalars A
  have hLHS : (↑(Ideal.relNorm A I) : FractionalIdeal A⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (relNorm_ne_bot_of_ne_bot I hI)
  have hRHS : moduleIndex K (⊤ : Submodule A L) N ≠ 0 :=
    moduleIndex_ne_zero K _ _
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hLHS,
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hRHS]
  apply finprod_congr
  intro v
  obtain ⟨φ, hφ⟩ := comparison_map_membership K (⊤ : Submodule A L) N
  congr 1
  rw [relNorm_count_eq_comparison_det K I hI v φ (by
    intro x
    exact hφ x)]
  exact (moduleIndex_count_eq_local K _ _ v φ hφ).symm

theorem relNorm_count_eq_det_spanSingleton_local
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
    [Module.Finite A L]
    (I : Ideal B) (hI : I ≠ ⊥)
    (v : IsDedekindDomain.HeightOneSpectrum A)
    (φ : L →ₗ[A] L)
    (hφ : ∀ (x : L), x ∈ (⊤ : Submodule A L) ↔
      φ x ∈ (I.map (algebraMap B L)).restrictScalars A) :
    FractionalIdeal.count K v (↑(Ideal.relNorm A I) : FractionalIdeal A⁰ K) =
      FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton A⁰ (algebraMap A K (LinearMap.det φ))) := by
  rw [relNorm_eq_moduleIndex_fractional_localization (L := L) K I hI]
  exact moduleIndex_count_eq_local K _ _ v φ hφ

theorem relNorm_count_eq_moduleIndex_count_axiom
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
    [Module.Finite A L]
    (I : Ideal B) (hI : I ≠ ⊥)
    (v : IsDedekindDomain.HeightOneSpectrum A) :
    FractionalIdeal.count K v (↑(Ideal.relNorm A I) : FractionalIdeal A⁰ K) =
      FractionalIdeal.count K v
        (moduleIndex K (⊤ : Submodule A L) ((I.map (algebraMap B L)).restrictScalars A)) := by
  obtain ⟨φ, hφ⟩ := comparison_map_membership K
    (⊤ : Submodule A L) ((I.map (algebraMap B L)).restrictScalars A)
  rw [relNorm_count_eq_det_spanSingleton_local K I hI v φ hφ]
  exact (moduleIndex_count_eq_local K _ _ v φ hφ).symm

theorem relNorm_count_eq_moduleIndex_count_local
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
    [Module.Finite A L]
    (I : Ideal B) (hI : I ≠ ⊥)
    (v : IsDedekindDomain.HeightOneSpectrum A) :
    FractionalIdeal.count K v (↑(Ideal.relNorm A I) : FractionalIdeal A⁰ K) =
      FractionalIdeal.count K v
        (moduleIndex K (⊤ : Submodule A L) ((I.map (algebraMap B L)).restrictScalars A)) :=
  relNorm_count_eq_moduleIndex_count_axiom K I hI v

theorem relNorm_eq_moduleIndex_fractional
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
    [Module.Finite A L]
    (I : Ideal B) (hI : I ≠ ⊥) :
    (↑(Ideal.relNorm A I) : FractionalIdeal A⁰ K) =
      moduleIndex K (⊤ : Submodule A L) ((I.map (algebraMap B L)).restrictScalars A) := by
  have hLHS : (↑(Ideal.relNorm A I) : FractionalIdeal A⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (relNorm_ne_bot_of_ne_bot I hI)
  have hRHS : moduleIndex K (⊤ : Submodule A L)
      ((I.map (algebraMap B L)).restrictScalars A) ≠ 0 :=
    moduleIndex_ne_zero K _ _
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hLHS,
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hRHS]
  apply finprod_congr
  intro v
  rw [relNorm_count_eq_moduleIndex_count_local (L := L) K I hI v]

theorem relNorm_count_eq_det_count
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
    [Module.Finite A L]
    (I : Ideal B) (hI : I ≠ ⊥)
    (v : IsDedekindDomain.HeightOneSpectrum A)
    (φ : L →ₗ[A] L)
    (hφ : ∀ (x : L), x ∈ (⊤ : Submodule A L) ↔
      φ x ∈ (I.map (algebraMap B L)).restrictScalars A) :
    FractionalIdeal.count K v (↑(Ideal.relNorm A I) : FractionalIdeal A⁰ K) =
      FractionalIdeal.count K v
        (FractionalIdeal.spanSingleton A⁰ (algebraMap A K (LinearMap.det φ))) := by
  rw [relNorm_eq_moduleIndex_fractional (L := L) K I hI]
  exact moduleIndex_count_eq_local K _ _ v φ hφ

theorem idealNorm_eq_moduleIndex
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
    [Module.Finite A L]
    (I : Ideal B) (hI : I ≠ ⊥) :
    (↑(Ideal.relNorm A I) : FractionalIdeal A⁰ K) =
      moduleIndex K (⊤ : Submodule A L) ((I.map (algebraMap B L)).restrictScalars A) :=
  relNorm_eq_moduleIndex_fractional K I hI

theorem moduleIndex_eq_idealNorm_inv_mul
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
    [Module.Finite A L]
    (I J : Ideal B) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    moduleIndex K
      ((I.map (algebraMap B L)).restrictScalars A)
      ((J.map (algebraMap B L)).restrictScalars A) =
    (↑(Ideal.relNorm A I) : FractionalIdeal A⁰ K)⁻¹ *
      (↑(Ideal.relNorm A J) : FractionalIdeal A⁰ K) := by

  rw [moduleIndex_mul K
    ((I.map (algebraMap B L)).restrictScalars A)
    (⊤ : Submodule A L)
    ((J.map (algebraMap B L)).restrictScalars A)]

  rw [moduleIndex_swap K (⊤ : Submodule A L) ((I.map (algebraMap B L)).restrictScalars A)]

  rw [← idealNorm_eq_moduleIndex K I hI, ← idealNorm_eq_moduleIndex K J hJ]

noncomputable def fractionalIdealNorm
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B]
    [Algebra A B] [Algebra B L] [IsScalarTower A B L]
    [Module.Finite A L]
    (𝔍 : FractionalIdeal B⁰ L) : FractionalIdeal A⁰ K :=
  moduleIndex K (⊤ : Submodule A L) (𝔍.coeToSubmodule.restrictScalars A)

theorem fractionalIdealNorm_coeIdeal
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
    [Module.Finite A L]
    (I : Ideal B) (hI : I ≠ ⊥) :
    fractionalIdealNorm K (↑I : FractionalIdeal B⁰ L) =
      (↑(Ideal.relNorm A I) : FractionalIdeal A⁰ K) := by
  simp only [fractionalIdealNorm]
  have hLHS : moduleIndex K (⊤ : Submodule A L)
      ((↑I : FractionalIdeal B⁰ L).coeToSubmodule.restrictScalars A) ≠ 0 :=
    moduleIndex_ne_zero K _ _
  have hRHS : (↑(Ideal.relNorm A I) : FractionalIdeal A⁰ K) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr (relNorm_ne_bot_of_ne_bot I hI)
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hLHS,
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hRHS]
  apply finprod_congr
  intro v

  obtain ⟨φ, hφ⟩ := comparison_map_membership K
    (⊤ : Submodule A L) ((↑I : FractionalIdeal B⁰ L).coeToSubmodule.restrictScalars A)

  have h_sub : ∀ y : L, y ∈ (↑(↑I : FractionalIdeal B⁰ L) : Submodule B L) →
      y ∈ (I.map (algebraMap B L) : Ideal L) := by
    intro y hy
    rw [FractionalIdeal.coe_coeIdeal] at hy
    rw [IsLocalization.mem_coeSubmodule] at hy
    obtain ⟨b, hb, rfl⟩ := hy
    exact Ideal.mem_map_of_mem _ hb
  have hφ' : ∀ (x : L), x ∈ (⊤ : Submodule A L) ↔
      φ x ∈ (I.map (algebraMap B L)).restrictScalars A := by
    intro x
    simp only [Submodule.mem_top, Submodule.restrictScalars_mem, true_iff]
    have := (hφ x).mp (Submodule.mem_top)
    rw [Submodule.restrictScalars_mem] at this
    exact h_sub _ this

  rw [moduleIndex_count_eq_local K _ _ v φ hφ]
  rw [relNorm_count_eq_det_spanSingleton_local (L := L) K I hI v φ hφ']


end IdealNorm

theorem fractionalIdeal_multiplicative_comparison_map
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
    [Module.Finite A L]
    (𝔍₁ 𝔍₂ : FractionalIdeal B⁰ L) :
    ∃ (φ : L →ₗ[A] L),
      (∀ (x : L), x ∈ (⊤ : Submodule A L) ↔
        φ x ∈ (𝔍₂.coeToSubmodule.restrictScalars A)) ∧
      (∀ (x : L), x ∈ (𝔍₁.coeToSubmodule.restrictScalars A) ↔
        φ x ∈ ((𝔍₁ * 𝔍₂).coeToSubmodule.restrictScalars A)) ∧
      algebraMap A K (LinearMap.det φ) ≠ 0 := by sorry

section IdealNorm

variable (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsDedekindDomain A]
variable {B : Type*} [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsDedekindDomain B]
variable [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]

theorem fractionalIdealNorm_mul
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
    [Module.Finite A L]
    (𝔍₁ 𝔍₂ : FractionalIdeal B⁰ L) :
    fractionalIdealNorm K (𝔍₁ * 𝔍₂) =
      (fractionalIdealNorm K 𝔍₁ : FractionalIdeal A⁰ K) * fractionalIdealNorm K 𝔍₂ := by

  unfold fractionalIdealNorm

  rw [moduleIndex_mul K
    (⊤ : Submodule A L)
    (𝔍₁.coeToSubmodule.restrictScalars A)
    ((𝔍₁ * 𝔍₂).coeToSubmodule.restrictScalars A)]

  congr 1

  have hLHS := moduleIndex_ne_zero K
    (𝔍₁.coeToSubmodule.restrictScalars A)
    ((𝔍₁ * 𝔍₂).coeToSubmodule.restrictScalars A)
  have hRHS := moduleIndex_ne_zero K
    (⊤ : Submodule A L)
    (𝔍₂.coeToSubmodule.restrictScalars A)
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hLHS,
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hRHS]
  apply finprod_congr
  intro v


  obtain ⟨φ, hφ₂, hφ₁₂, _⟩ :=
    fractionalIdeal_multiplicative_comparison_map (A := A) K 𝔍₁ 𝔍₂

  congr 1
  rw [moduleIndex_count_eq_local K _ _ v φ hφ₁₂,
      moduleIndex_count_eq_local K _ _ v φ hφ₂]

theorem fractionalIdealNorm_inv
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
    [Module.Finite A L]
    (𝔍 : FractionalIdeal B⁰ L) :
    fractionalIdealNorm K 𝔍⁻¹ =
      (fractionalIdealNorm K 𝔍 : FractionalIdeal A⁰ K)⁻¹ := by

  set N := (fractionalIdealNorm (A := A) K : FractionalIdeal B⁰ L → FractionalIdeal A⁰ K) with hN_def

  have hN_ne : ∀ I : FractionalIdeal B⁰ L, N I ≠ 0 := fun I =>
    moduleIndex_ne_zero K (⊤ : Submodule A L) (I.coeToSubmodule.restrictScalars A)

  have hN_mul : ∀ I J : FractionalIdeal B⁰ L, N (I * J) = N I * N J :=
    fun I J => fractionalIdealNorm_mul (A := A) K I J

  have hN_one : N 1 = 1 := by
    have h := hN_mul 1 𝔍
    rw [one_mul] at h

    exact mul_right_cancel₀ (hN_ne 𝔍) (h.symm.trans (one_mul _).symm)
  by_cases h𝔍 : 𝔍 = 0
  ·
    subst h𝔍

    have h0 := hN_mul 0 0
    rw [mul_zero] at h0

    have hN0 : N 0 = 1 :=
      mul_right_cancel₀ (hN_ne 0) (h0.symm.trans (one_mul _).symm)
    simp only [FractionalIdeal.inv_zero', hN0, inv_one]
  ·
    have hmul : 𝔍 * 𝔍⁻¹ = 1 := mul_inv_cancel₀ h𝔍

    have h1 : N 𝔍 * N 𝔍⁻¹ = 1 := by rw [← hN_mul, hmul, hN_one]
    exact eq_inv_of_mul_eq_one_right h1

theorem moduleIndex_eq_fractionalIdealNorm_inv_mul
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
    [Module.Finite A L]
    (I J : Ideal B) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    moduleIndex K
      ((I.map (algebraMap B L)).restrictScalars A)
      ((J.map (algebraMap B L)).restrictScalars A) =
    fractionalIdealNorm K
      ((↑I : FractionalIdeal B⁰ L)⁻¹ * (↑J : FractionalIdeal B⁰ L)) := by


  rw [moduleIndex_eq_idealNorm_inv_mul K I J hI hJ]
  rw [fractionalIdealNorm_mul]
  rw [fractionalIdealNorm_coeIdeal K J hJ]


  congr 1

  rw [← fractionalIdealNorm_coeIdeal (L := L) K I hI]

  exact (fractionalIdealNorm_inv K _).symm

theorem moduleIndex_eq_fractionalIdealNorm_div
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
    [Module.Finite A L]
    (I J : Ideal B) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    moduleIndex K
      ((I.map (algebraMap B L)).restrictScalars A)
      ((J.map (algebraMap B L)).restrictScalars A) =
    fractionalIdealNorm K
      ((↑J : FractionalIdeal B⁰ L) / (↑I : FractionalIdeal B⁰ L)) := by
  rw [div_eq_mul_inv, mul_comm]
  exact moduleIndex_eq_fractionalIdealNorm_inv_mul K I J hI hJ

theorem moduleIndex_eq_idealNorm_eq_fractionalIdealNorm
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
    [Module.Finite A L]
    (I J : Ideal B) (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    moduleIndex K
      ((I.map (algebraMap B L)).restrictScalars A)
      ((J.map (algebraMap B L)).restrictScalars A) =
    (↑(Ideal.relNorm A I) : FractionalIdeal A⁰ K)⁻¹ *
      (↑(Ideal.relNorm A J) : FractionalIdeal A⁰ K) ∧
    moduleIndex K
      ((I.map (algebraMap B L)).restrictScalars A)
      ((J.map (algebraMap B L)).restrictScalars A) =
    fractionalIdealNorm K
      ((↑I : FractionalIdeal B⁰ L)⁻¹ * (↑J : FractionalIdeal B⁰ L)) ∧
    moduleIndex K
      ((I.map (algebraMap B L)).restrictScalars A)
      ((J.map (algebraMap B L)).restrictScalars A) =
    fractionalIdealNorm K
      ((↑J : FractionalIdeal B⁰ L) / (↑I : FractionalIdeal B⁰ L)) :=
  ⟨moduleIndex_eq_idealNorm_inv_mul K I J hI hJ,
   moduleIndex_eq_fractionalIdealNorm_inv_mul K I J hI hJ,
   moduleIndex_eq_fractionalIdealNorm_div K I J hI hJ⟩

theorem idealNorm_eq_span_norms (I : Ideal B) :
    idealNorm A I = Ideal.span (Algebra.intNorm A B '' (I : Set B)) :=
  Ideal.relNorm_apply A I

theorem idealNorm_eq_span_fieldNorms [Module.Free A B] (I : Ideal B) :
    idealNorm A I = Ideal.span (Algebra.norm A '' (I : Set B)) := by
  rw [idealNorm_eq_span_norms]
  congr 1
  ext x
  simp only [Set.mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, by rw [Algebra.intNorm_eq_norm]⟩
  · rintro ⟨b, hb, rfl⟩; exact ⟨b, hb, by rw [Algebra.intNorm_eq_norm]⟩

end IdealNorm


theorem fractionalIdealNorm_eq_span_fieldNorms
    {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A] [IsIntegrallyClosed A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L]
    {B : Type*} [CommRing B] [IsDomain B] [IsDedekindDomain B] [IsIntegrallyClosed B]
    [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    [Algebra B L] [IsScalarTower A B L] [IsFractionRing B L]
    [Module.Finite A L]
    (I : FractionalIdeal B⁰ L) :
    (fractionalIdealNorm K I).coeToSubmodule =
      Submodule.span A (Algebra.norm K '' (I : Set L)) := by sorry

section IdealNormPrime

variable {A : Type*} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsDedekindDomain A]
variable {B : Type*} [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [IsDedekindDomain B]
variable [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]

theorem idealNorm_prime [PerfectField (FractionRing A)]
    (Q : Ideal B) (p : Ideal A) [Q.LiesOver p] [Q.IsMaximal] [p.IsMaximal] :
    idealNorm A Q = p ^ p.inertiaDeg Q :=
  Ideal.relNorm_eq_pow_of_isMaximal Q p

attribute [local instance] FractionRing.liftAlgebra in
theorem idealNorm_map_eq_pow (B : Type*) [CommRing B] [IsDomain B] [IsIntegrallyClosed B]
    [IsDedekindDomain B] [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]
    (I : Ideal A) :
    idealNorm A (I.map (algebraMap A B)) =
      I ^ Module.finrank (FractionRing A) (FractionRing B) :=
  Ideal.relNorm_algebraMap B I

end IdealNormPrime


section NormNumberField

open NumberField

theorem absNorm_eq_card_quot {K : Type*} [Field K] [NumberField K]
    (I : Ideal (𝓞 K)) :
    Ideal.absNorm I = Nat.card ((𝓞 K) ⧸ I) := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem absNorm_mul_card_quotient_eq {K : Type*} [Field K] [NumberField K]
    (I J : Ideal (𝓞 K)) (hle : J ≤ I) :
    Ideal.absNorm I *
      Nat.card (Submodule.map (Submodule.mkQ (J : Submodule (𝓞 K) (𝓞 K)))
        (I : Submodule (𝓞 K) (𝓞 K))) =
    Ideal.absNorm J := by
  rw [mul_comm, Ideal.absNorm_apply, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Submodule.card_quotient_mul_card_quotient _ _ hle

theorem moduleIndex_eq_absNorm_quotient {K : Type*} [Field K] [NumberField K]
    (I J : Ideal (𝓞 K)) (hI : I ≠ ⊥) (hle : J ≤ I)
    (C : Ideal (𝓞 K)) (hC : J = I * C) :
    Nat.card (Submodule.map (Submodule.mkQ (J : Submodule (𝓞 K) (𝓞 K)))
        (I : Submodule (𝓞 K) (𝓞 K))) =
    Ideal.absNorm C := by
  have tower := absNorm_mul_card_quotient_eq I J hle
  have mul_norm : Ideal.absNorm J = Ideal.absNorm I * Ideal.absNorm C := by
    rw [hC, map_mul]
  have hI_pos : 0 < Ideal.absNorm I :=
    Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  exact Nat.eq_of_mul_eq_mul_left hI_pos (tower.trans mul_norm)

end NormNumberField

namespace DedekindKummer.NF

open Ideal Polynomial UniqueFactorizationMonoid KummerDedekind NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {p : ℕ} [Fact (Nat.Prime p)]

theorem inertiaDeg_eq_natDegree
    (hp : ¬ p ∣ RingOfIntegers.exponent θ)
    {Q : (ZMod p)[X]}
    (hQ : Q ∈ RingOfIntegers.monicFactorsMod θ p) :
    inertiaDeg (span {(p : ℤ)})
      ((Ideal.primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) =
        Q.natDegree :=
  NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hp hQ

theorem ramificationIdx_eq_multiplicity
    (hp : ¬ p ∣ RingOfIntegers.exponent θ)
    {Q : (ZMod p)[X]}
    (hQ : Q ∈ RingOfIntegers.monicFactorsMod θ p) :
    (span {(p : ℤ)}).ramificationIdx
      ((Ideal.primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) =
        multiplicity Q ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) :=
  NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' hp hQ

end DedekindKummer.NF
