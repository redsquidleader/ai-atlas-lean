/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.DedekindDomain.PID

open Polynomial NumberField

instance instFactIrreducibleXSqPlusFive : Fact (Irreducible (X ^ 2 + C (5 : ℚ))) := by
  constructor
  have hmonic : (X ^ 2 + C (5 : ℚ)).Monic := by
    apply Polynomial.Monic.add_of_left (monic_X_pow 2); simp
  by_contra h
  rw [hmonic.not_irreducible_iff_exists_add_mul_eq_coeff (by simp)] at h
  obtain ⟨c₁, c₂, h1, h2⟩ := h
  simp only [coeff_add, coeff_X_pow, coeff_C] at h1 h2
  norm_num at h1 h2
  have hc2 : c₂ = -c₁ := by linarith
  subst hc2; nlinarith [sq_nonneg c₁]

noncomputable abbrev QSqrtNeg5 := AdjoinRoot (X ^ 2 + C (5 : ℚ))

theorem classNumber_QSqrtNeg5 : classNumber QSqrtNeg5 = 2 := by


  have h1 : classNumber QSqrtNeg5 ≥ 2 := by


    sorry
  have h2 : classNumber QSqrtNeg5 ≤ 2 := by


    sorry
  omega

theorem classGroup_QSqrtNeg5_iso :
    Nonempty (ClassGroup (𝓞 QSqrtNeg5) ≃* Multiplicative (ZMod 2)) := by
  have hcard : Nat.card (ClassGroup (𝓞 QSqrtNeg5)) = 2 := by
    rw [Nat.card_eq_fintype_card]; exact classNumber_QSqrtNeg5
  haveI hcyc : IsCyclic (ClassGroup (𝓞 QSqrtNeg5)) := isCyclic_of_prime_card hcard
  have := zmodCyclicMulEquiv hcyc
  rw [hcard] at this
  exact ⟨this.symm⟩
