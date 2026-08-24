/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.GlobalCFT

noncomputable section

open NumberField RayClassField GlobalCFT

namespace DirichletDensity

universe u

variable (K : Type u) [Field K] [NumberField K]
  (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
  (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)

theorem allLValuesNonzero_iff_orders_zero (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪)) :
    AllLValuesNonzero K 𝔪 𝒞 ↔
      ∀ χ : PrimitiveCharsContaining K 𝔪 𝒞,
        ¬GlobalCFT.isPrincipalPrimitive K 𝔪 𝒞 χ → GlobalCFT.orderOfVanishingPrimitive K 𝔪 𝒞 χ = 0 :=
  Iff.rfl

def sumOrdersNonprincipal (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (_h_cong : IsCongruenceSubgroup K 𝔪 𝒞) : ℕ :=
  haveI := _h_cong.finiteIndex
  ∑ χ : PrimitiveCharsContaining K 𝔪 𝒞,
    if GlobalCFT.isPrincipalPrimitive K 𝔪 𝒞 χ then 0
    else GlobalCFT.orderOfVanishingPrimitive K 𝔪 𝒞 χ

theorem allLValuesNonzero_iff_sumOrders_eq_zero (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞) :
    AllLValuesNonzero K 𝔪 𝒞 ↔ sumOrdersNonprincipal K 𝔪 𝒞 h_cong = 0 := by

  rw [allLValuesNonzero_iff_orders_zero]

  unfold sumOrdersNonprincipal

  simp only [Finset.sum_eq_zero_iff, Finset.mem_univ, true_implies]

  constructor
  · intro h χ
    split_ifs with hp
    · rfl
    · exact h χ hp
  · intro h χ hχ
    have := h χ
    simp only [hχ, ↓reduceIte] at this
    exact this

theorem dirichlet_density_congruence_subgroup (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (n : ℕ) (hn : 𝒞.index = n) (hn_pos : 0 < n) :
    (AllLValuesNonzero K 𝔪 𝒞 →
      dirichletDensityCongruence K 𝔪 𝒞 h_cong = 1 / (n : ℚ)) ∧
    (¬ AllLValuesNonzero K 𝔪 𝒞 →
      dirichletDensityCongruence K 𝔪 𝒞 h_cong = 0) :=
  GlobalCFT.theorem_22_20 K 𝔪 𝒞 h_cong n hn hn_pos

end DirichletDensity
