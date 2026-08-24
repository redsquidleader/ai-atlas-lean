/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Juntas
import Atlas.BooleanFunctions.code.InfluenceFourier
import Atlas.BooleanFunctions.code.MonotoneFourier
import Atlas.BooleanFunctions.code.Talagrand
import Atlas.BooleanFunctions.code.Theorems

namespace BooleanFourier

open Finset BigOperators

lemma fourierInfluence_eq_influenceReal {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (i : Fin n) :
    fourierInfluence f i = influenceReal f i := by
  rw [influenceReal_eq_sum_fourierCoeff_sq]
  unfold fourierInfluence
  rw [← Finset.sum_filter]

lemma fourierInfluence_liftPM_eq_influence {n : ℕ} (f : (Fin n → Bool) → Bool)
    (i : Fin n) :
    fourierInfluence (liftPM f) i = influence f i := by
  rw [fourierInfluence_eq_influenceReal]
  have : liftPM f = fun x => boolToReal (f x) := rfl
  rw [this, ← influence_eq_influenceReal]

lemma influence_lt_of_not_mem_highInfluenceCoords {n : ℕ} (f : (Fin n → Bool) → Bool)
    (τ : ℝ) (i : Fin n) (hi : i ∉ highInfluenceCoords f τ) :
    influence f i < τ := by
  simp only [highInfluenceCoords, Finset.mem_filter, Finset.mem_univ, true_and,
    not_le] at hi
  exact hi

lemma fourierInfluence_lt_of_not_mem_J {n : ℕ} (f : (Fin n → Bool) → Bool)
    (τ : ℝ) (i : Fin n) (hi : i ∉ highInfluenceCoords f τ) :
    fourierInfluence (liftPM f) i < τ := by
  rw [fourierInfluence_liftPM_eq_influence]
  exact influence_lt_of_not_mem_highInfluenceCoords f τ i hi

theorem fourierCoeff_sq_lt_of_not_subset_J {n : ℕ} (f : (Fin n → Bool) → Bool)
    (τ : ℝ) (S : Finset (Fin n))
    (hS : ¬(S ⊆ highInfluenceCoords f τ)) :
    fourierCoeff (liftPM f) S ^ 2 < τ := by

  rw [Finset.not_subset] at hS
  obtain ⟨i, hi_S, hi_nJ⟩ := hS
  calc fourierCoeff (liftPM f) S ^ 2
      ≤ fourierInfluence (liftPM f) i :=
        fourierCoeff_sq_le_fourierInfluence (liftPM f) S i hi_S
    _ < τ := fourierInfluence_lt_of_not_mem_J f τ i hi_nJ

lemma log_inv_pos_of_tau {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    Real.log (1 / τ) > 0 := by
  rw [Real.log_div (by linarith : (1 : ℝ) ≠ 0) (ne_of_gt hτ0)]
  simp only [Real.log_one, zero_sub]
  exact neg_pos.mpr (Real.log_neg hτ0 hτ1)

theorem spectral_entropy_le_two_totalInfluence {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => fourierCoeff (liftPM f) S ≠ 0),
      fourierCoeff (liftPM f) S ^ 2 * Real.log (1 / (fourierCoeff (liftPM f) S ^ 2)) ≤
      2 * totalInfluence f := by sorry

lemma fourierCoeff_sq_le_one_of_liftPM {n : ℕ} (f : (Fin n → Bool) → Bool)
    (S : Finset (Fin n)) :
    fourierCoeff (liftPM f) S ^ 2 ≤ 1 := by
  have hpars : ∑ T : Finset (Fin n), fourierCoeff (liftPM f) T ^ 2 = 1 := by
    have : liftPM f = fun x => boolToReal (f x) := rfl
    rw [this]
    exact parseval_signed f
  have hS_mem : S ∈ (Finset.univ : Finset (Finset (Fin n))) := Finset.mem_univ S
  have h_le := Finset.single_le_sum (f := fun T => fourierCoeff (liftPM f) T ^ 2)
    (fun T _ => sq_nonneg _) hS_mem
  linarith

theorem friedgut_weighted_fourier_bound {n : ℕ} (f : (Fin n → Bool) → Bool) (τ : ℝ)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => ¬(S ⊆ highInfluenceCoords f τ)),
      fourierCoeff (liftPM f) S ^ 2) * Real.log (1 / τ) ≤ 2 * totalInfluence f := by
  set g := liftPM f
  set J := highInfluenceCoords f τ

  rw [Finset.sum_mul]

  have h_step1 : ∑ S ∈ univ.filter (fun S => ¬(S ⊆ J)),
      fourierCoeff g S ^ 2 * Real.log (1 / τ) ≤
      ∑ S ∈ univ.filter (fun S => ¬(S ⊆ J)),
      fourierCoeff g S ^ 2 * Real.log (1 / (fourierCoeff g S ^ 2)) := by
    apply Finset.sum_le_sum
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
    by_cases hcoeff : fourierCoeff g S = 0
    · simp [hcoeff]
    ·
      have h_sq_pos : (0 : ℝ) < fourierCoeff g S ^ 2 := by positivity
      have h_sq_lt : fourierCoeff g S ^ 2 < τ :=
        fourierCoeff_sq_lt_of_not_subset_J f τ S hS

      have h_inv_le : (1 : ℝ) / τ ≤ 1 / (fourierCoeff g S ^ 2) := by
        apply div_le_div_of_nonneg_left (by linarith : (0 : ℝ) < 1).le h_sq_pos h_sq_lt.le

      have h_log_le : Real.log (1 / τ) ≤ Real.log (1 / (fourierCoeff g S ^ 2)) := by
        apply Real.log_le_log
        · positivity
        · exact h_inv_le

      exact mul_le_mul_of_nonneg_left h_log_le (sq_nonneg _)


  have h_step2 : ∑ S ∈ univ.filter (fun S => ¬(S ⊆ J)),
      fourierCoeff g S ^ 2 * Real.log (1 / (fourierCoeff g S ^ 2)) ≤
      ∑ S ∈ univ.filter (fun S => fourierCoeff g S ≠ 0),
      fourierCoeff g S ^ 2 * Real.log (1 / (fourierCoeff g S ^ 2)) := by

    have h_nonneg : ∀ S ∈ (univ : Finset (Finset (Fin n))),
        S ∉ univ.filter (fun S => ¬(S ⊆ J)) →
        0 ≤ fourierCoeff g S ^ 2 * Real.log (1 / (fourierCoeff g S ^ 2)) := by
      intro S _ _
      by_cases hS : fourierCoeff g S = 0
      · simp [hS]
      · apply mul_nonneg (sq_nonneg _)
        apply Real.log_nonneg
        have h_sq_pos' : (0 : ℝ) < fourierCoeff g S ^ 2 := by positivity
        rw [le_div_iff₀ h_sq_pos']
        simp only [one_mul]
        exact fourierCoeff_sq_le_one_of_liftPM f S

    have h_le_univ : ∑ S ∈ univ.filter (fun S => ¬(S ⊆ J)),
        fourierCoeff g S ^ 2 * Real.log (1 / (fourierCoeff g S ^ 2)) ≤
        ∑ S ∈ (univ : Finset (Finset (Fin n))),
        fourierCoeff g S ^ 2 * Real.log (1 / (fourierCoeff g S ^ 2)) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) h_nonneg

    have h_univ_eq : ∑ S ∈ (univ : Finset (Finset (Fin n))),
        fourierCoeff g S ^ 2 * Real.log (1 / (fourierCoeff g S ^ 2)) =
        ∑ S ∈ univ.filter (fun S => fourierCoeff g S ≠ 0),
        fourierCoeff g S ^ 2 * Real.log (1 / (fourierCoeff g S ^ 2)) := by
      symm
      apply Finset.sum_filter_of_ne
      intro S _ hterm
      by_contra hcoeff
      exact hterm (by simp [hcoeff])
    linarith

  have h_step3 : ∑ S ∈ univ.filter (fun S => fourierCoeff g S ≠ 0),
      fourierCoeff g S ^ 2 * Real.log (1 / (fourierCoeff g S ^ 2)) ≤
      2 * totalInfluence f :=
    spectral_entropy_le_two_totalInfluence f
  linarith

theorem friedgut_tight_concentration {n : ℕ} (f : (Fin n → Bool) → Bool)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    ∑ S ∈ (univ : Finset (Finset (Fin n))).filter
      (fun S => ¬(S ⊆ highInfluenceCoords f τ)),
      fourierCoeff (liftPM f) S ^ 2 ≤
        2 * totalInfluence f / Real.log (1 / τ) := by
  have hlog_pos : Real.log (1 / τ) > 0 := log_inv_pos_of_tau hτ0 hτ1
  have h_key := friedgut_weighted_fourier_bound f τ hτ0 hτ1
  have h_sum_nonneg : 0 ≤ ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => ¬(S ⊆ highInfluenceCoords f τ)),
      fourierCoeff (liftPM f) S ^ 2 := by
    apply Finset.sum_nonneg; intros; positivity
  rw [le_div_iff₀ hlog_pos]
  linarith

end BooleanFourier
