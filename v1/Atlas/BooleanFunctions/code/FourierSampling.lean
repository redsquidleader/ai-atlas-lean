/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.FourierExpansion
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace BooleanFourier

theorem fourierCoeff_eq_expectation {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (S : Finset (Fin n)) :
    fourierCoeff f S = (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, f x * chi S x := by
  rfl

theorem abs_chi_eq_one {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    |chi S x| = 1 := by
  have h := chi_sq S x
  have hne := chi_ne_zero S x
  have habs_sq : |chi S x| ^ 2 = 1 := by
    rw [sq_abs]; exact h
  have habs_nn : (0 : ℝ) ≤ |chi S x| := abs_nonneg _
  nlinarith [sq_nonneg (|chi S x| - 1)]

theorem sample_bounded {n : ℕ} (f : (Fin n → Bool) → ℝ) (S : Finset (Fin n))
    (hf : ∀ x, |f x| ≤ 1) (x : Fin n → Bool) :
    |f x * chi S x| ≤ 1 := by
  rw [abs_mul, abs_chi_eq_one S x, mul_one]
  exact hf x

theorem fourier_sampling_hoeffding_bound
    {n : ℕ} (f : (Fin n → Bool) → ℝ) (S : Finset (Fin n))
    (hf : ∀ x, |f x| ≤ 1) (ε : ℝ) (hε : 0 < ε) (m : ℕ) (hm : 1 ≤ m) :
    ((Finset.univ.filter (fun samples : Fin m → (Fin n → Bool) =>
      |((1 : ℝ) / m) * ∑ i : Fin m, f (samples i) * chi S (samples i)
        - fourierCoeff f S| ≥ ε)).card : ℝ) / ((2 : ℝ) ^ n) ^ m
      ≤ 2 * Real.exp (-(↑m * ε ^ 2 / 2)) := by sorry

theorem claim_1_2_fourier_sampling
    {n : ℕ} (f : (Fin n → Bool) → ℝ) (S : Finset (Fin n))
    (hf : ∀ x, |f x| ≤ 1) (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ ⌈2 * Real.log (2 / δ) / ε ^ 2⌉₊ ∧
      ((Finset.univ.filter (fun samples : Fin m → (Fin n → Bool) =>
        |((1 : ℝ) / m) * ∑ i : Fin m, f (samples i) * chi S (samples i)
          - fourierCoeff f S| ≥ ε)).card : ℝ) / ((2 : ℝ) ^ n) ^ m
        ≤ δ := by
  set m := ⌈2 * Real.log (2 / δ) / ε ^ 2⌉₊
  have hε2 : (0 : ℝ) < ε ^ 2 := pow_pos hε 2
  have h2d : (0 : ℝ) < 2 / δ := div_pos two_pos hδ
  have hlog : (0 : ℝ) < Real.log (2 / δ) :=
    Real.log_pos (by rw [one_lt_div hδ]; linarith)
  have hm1 : 1 ≤ m := by
    rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, Nat.ceil_pos]
    exact div_pos (mul_pos two_pos hlog) hε2
  refine ⟨m, hm1, le_refl m, ?_⟩
  have hHoeff := fourier_sampling_hoeffding_bound f S hf ε hε m hm1
  have hceil : 2 * Real.log (2 / δ) / ε ^ 2 ≤ (m : ℝ) := Nat.le_ceil _
  have hme : Real.log (2 / δ) ≤ (m : ℝ) * ε ^ 2 / 2 := by
    have h1 := (div_le_iff₀ hε2).mp hceil
    linarith
  have hexp : Real.exp (-((m : ℝ) * ε ^ 2 / 2)) ≤ Real.exp (-(Real.log (2 / δ))) :=
    Real.exp_le_exp.mpr (neg_le_neg hme)
  have hinv : Real.exp (-(Real.log (2 / δ))) = δ / 2 := by
    rw [Real.exp_neg, Real.exp_log h2d, inv_div]
  have hbound : 2 * Real.exp (-((m : ℝ) * ε ^ 2 / 2)) ≤ δ :=
    calc 2 * Real.exp (-((m : ℝ) * ε ^ 2 / 2))
        ≤ 2 * Real.exp (-(Real.log (2 / δ))) :=
          mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ = 2 * (δ / 2) := by rw [hinv]
      _ = δ := by ring
  linarith

end BooleanFourier
