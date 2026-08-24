/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.Prop2221

noncomputable section

open NumberField RayClassField GlobalCFT

namespace CosetDensity

universe u

theorem dirichletDensity_coprime_primes_eq_one (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (_h_cong : IsCongruenceSubgroup K 𝔪 𝒞) :
    DirichletDensity K {𝔭 : Prime' K | ∃ (_ : 𝔪 (Place.finite 𝔭) = 0), True} = some 1 := by
  exact GlobalCFT.dirichletDensity_coprime_primes_eq_one K 𝔪 𝒞 _h_cong

theorem dirichletDensity_coset_partition_sum (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (n : ℕ) (hn : 𝒞.index = n) (hn_pos : 0 < n)
    (reps : Fin n → FracIdealsCoprime K 𝔪)
    (h_reps : Function.Injective (fun i => QuotientGroup.mk (s := 𝒞) (reps i))) :
    (DirichletDensity K {𝔭 : Prime' K | ∃ (_ : 𝔪 (Place.finite 𝔭) = 0), True}).getD 0 =
      ∑ i : Fin n, dirichletDensityCoset K 𝔪 𝒞 h_cong (reps i) := by
  exact GlobalCFT.dirichletDensity_coset_partition_sum K 𝔪 𝒞 h_cong n hn hn_pos reps h_reps

theorem density_cosets_sum_one (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (n : ℕ) (hn : 𝒞.index = n) (hn_pos : 0 < n)
    (reps : Fin n → FracIdealsCoprime K 𝔪)
    (h_reps : Function.Injective (fun i => QuotientGroup.mk (s := 𝒞) (reps i))) :
    ∑ i : Fin n, dirichletDensityCoset K 𝔪 𝒞 h_cong (reps i) = 1 := by

  have h_sum := dirichletDensity_coset_partition_sum K 𝔪 𝒞 h_cong n hn hn_pos reps h_reps

  have h_one := dirichletDensity_coprime_primes_eq_one K 𝔪 𝒞 h_cong

  rw [h_one] at h_sum
  simp [Option.getD] at h_sum
  linarith

theorem corollary_22_22 (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (n : ℕ) (hn : 𝒞.index = n) (hn_pos : 0 < n)
    (reps : Fin n → FracIdealsCoprime K 𝔪)
    (h_reps : Function.Injective (fun i => QuotientGroup.mk (s := 𝒞) (reps i))) :
    AllLValuesNonzero K 𝔪 𝒞 ∧
    ∀ (I : FracIdealsCoprime K 𝔪),
      dirichletDensityCoset K 𝔪 𝒞 h_cong I = 1 / (n : ℚ) := by

  have h_sum := density_cosets_sum_one K 𝔪 𝒞 h_cong n hn hn_pos reps h_reps

  have h_each : ∀ i : Fin n,
      (AllLValuesNonzero K 𝔪 𝒞 →
        dirichletDensityCoset K 𝔪 𝒞 h_cong (reps i) = 1 / (n : ℚ)) ∧
      (¬ AllLValuesNonzero K 𝔪 𝒞 →
        dirichletDensityCoset K 𝔪 𝒞 h_cong (reps i) = 0) :=
    fun i => Prop2221.proposition_22_21 K 𝔪 𝒞 h_cong n hn hn_pos (reps i)


  have hL : AllLValuesNonzero K 𝔪 𝒞 := by
    by_contra hL
    have h_zero : ∀ i : Fin n,
        dirichletDensityCoset K 𝔪 𝒞 h_cong (reps i) = 0 :=
      fun i => (h_each i).2 hL
    simp only [h_zero, Finset.sum_const_zero] at h_sum
    exact one_ne_zero h_sum.symm


  exact ⟨hL, fun I => (Prop2221.proposition_22_21 K 𝔪 𝒞 h_cong n hn hn_pos I).1 hL⟩

end CosetDensity

namespace Cor2222

export CosetDensity (dirichletDensity_coprime_primes_eq_one dirichletDensity_coset_partition_sum
  density_cosets_sum_one corollary_22_22)
end Cor2222
