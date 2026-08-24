/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.Theorem2220

noncomputable section

open NumberField RayClassField GlobalCFT

namespace CosetDensity

universe u

variable (K : Type u) [Field K] [NumberField K]
  (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
  (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)

theorem coset_density_eq_formula (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (n : ℕ) (hn : 𝒞.index = n) (hn_pos : 0 < n)
    (I : FracIdealsCoprime K 𝔪) :
    dirichletDensityCoset K 𝔪 𝒞 h_cong I =
      (1 - (DirichletDensity.sumOrdersNonprincipal K 𝔪 𝒞 h_cong : ℚ)) / (n : ℚ) := by
  rw [dirichletDensityCoset_eq_congruence]
  simp only [dirichletDensityCongruence, DirichletDensity.sumOrdersNonprincipal, hn]

theorem coset_density_nonneg (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (I : FracIdealsCoprime K 𝔪) :
    0 ≤ dirichletDensityCoset K 𝔪 𝒞 h_cong I := by
  rw [dirichletDensityCoset_eq_congruence K 𝔪 𝒞 h_cong I]
  exact dirichletDensityCongruence_nonneg K 𝔪 𝒞 h_cong

theorem proposition_22_21 (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (n : ℕ) (hn : 𝒞.index = n) (hn_pos : 0 < n)
    (I : FracIdealsCoprime K 𝔪) :
    (AllLValuesNonzero K 𝔪 𝒞 →
      dirichletDensityCoset K 𝔪 𝒞 h_cong I = 1 / (n : ℚ)) ∧
    (¬ AllLValuesNonzero K 𝔪 𝒞 →
      dirichletDensityCoset K 𝔪 𝒞 h_cong I = 0) := by

  set E := DirichletDensity.sumOrdersNonprincipal K 𝔪 𝒞 h_cong with hE_def

  have h_formula := coset_density_eq_formula K 𝔪 𝒞 h_cong n hn hn_pos I

  have h_nonneg := coset_density_nonneg K 𝔪 𝒞 h_cong I

  have h_equiv := DirichletDensity.allLValuesNonzero_iff_sumOrders_eq_zero K 𝔪 𝒞 h_cong

  have hn_pos_rat : (0 : ℚ) < (n : ℚ) := Nat.cast_pos.mpr hn_pos
  have hn_ne : (n : ℚ) ≠ 0 := ne_of_gt hn_pos_rat

  rw [h_formula] at h_nonneg
  have h_num_nonneg : 0 ≤ 1 - (E : ℚ) := by
    rwa [le_div_iff₀ hn_pos_rat, zero_mul] at h_nonneg

  have hE_le : E ≤ 1 := by
    have : (E : ℚ) ≤ 1 := by linarith
    exact_mod_cast this

  constructor
  ·
    intro h_all
    rw [h_equiv] at h_all
    rw [h_formula, h_all]
    simp
  ·
    intro h_not_all
    rw [h_equiv] at h_not_all

    have hE_eq : E = 1 := by omega
    rw [h_formula]
    rw [show DirichletDensity.sumOrdersNonprincipal K 𝔪 𝒞 h_cong = 1 from hE_eq]
    simp

end CosetDensity


namespace Prop2221

universe u in
theorem proposition_22_21 (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (n : ℕ) (hn : 𝒞.index = n) (hn_pos : 0 < n)
    (I : FracIdealsCoprime K 𝔪) :
    (AllLValuesNonzero K 𝔪 𝒞 →
      dirichletDensityCoset K 𝔪 𝒞 h_cong I = 1 / (n : ℚ)) ∧
    (¬ AllLValuesNonzero K 𝔪 𝒞 →
      dirichletDensityCoset K 𝔪 𝒞 h_cong I = 0) :=
  CosetDensity.proposition_22_21 K 𝔪 𝒞 h_cong n hn hn_pos I

end Prop2221
