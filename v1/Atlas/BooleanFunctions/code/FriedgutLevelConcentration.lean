/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Friedgut
import Atlas.BooleanFunctions.code.UncoveredBatch2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace BooleanFourier

open Finset Real

theorem friedgut_level_concentration {n : ℕ} (f : (Fin n → Bool) → Bool)
    (ε : ℝ) (hε : 0 < ε) (hVar : varianceReal (liftPM f) > 0) :
    ∃ J : Finset (Fin n),
      (J.card : ℝ) ≤ (2 : ℝ) ^ (4 * totalInfluence f / (ε * varianceReal (liftPM f))) ∧
      ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (fun S => ¬(S ⊆ J)),
        fourierCoeff (liftPM f) S ^ 2 ≤ ε ^ 2 / 4 := by sorry

theorem friedgut_junta_theorem_2_1 :
    ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (ε : ℝ),
      varianceReal (liftPM f) > 0 → ε > 0 →
        ∃ (g : (Fin n → Bool) → Bool) (J : ℕ),
          IsBoolFnJunta g J ∧
            (J : ℝ) ≤ (2 : ℝ) ^ (C * totalInfluence f / (ε * varianceReal (liftPM f))) ∧
            boolL2Dist f g ≤ ε := by
  refine ⟨4, by norm_num, fun n f ε hVar hε => ?_⟩

  obtain ⟨J, hJ_size, hJ_tail⟩ := friedgut_level_concentration f ε hε hVar

  obtain ⟨g, hg_junta, hg_l2⟩ := friedgut_l2_bridge f J

  refine ⟨g, J.card, hg_junta, hJ_size, ?_⟩


  calc boolL2Dist f g
      ≤ 2 * Real.sqrt (∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
          (fun S => ¬(S ⊆ J)), fourierCoeff (liftPM f) S ^ 2) := hg_l2
    _ ≤ 2 * Real.sqrt (ε ^ 2 / 4) := by
        apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hJ_tail) (by norm_num : (0:ℝ) ≤ 2)
    _ = ε := by
        rw [show ε ^ 2 / 4 = (ε / 2) ^ 2 from by ring]
        rw [Real.sqrt_sq (by linarith : (0 : ℝ) ≤ ε / 2)]
        ring

theorem friedgut_junta_corollary_bound {n : ℕ}
    (f : (Fin n → Bool) → Bool) (K : ℝ)
    (hVar : varianceReal (liftPM f) > 0)
    (hK1 : K ≥ 1)
    (hIK : totalInfluence f ≤ K * varianceReal (liftPM f)) :
    ∃ i : Fin n, influence f i ≥ Real.exp (-5 * K) := by

  set τ := Real.exp (-5 * K)
  have hτ_pos : (0 : ℝ) < τ := Real.exp_pos _
  have hτ_lt_one : τ < 1 := by
    exact Real.exp_lt_one_iff.mpr (by linarith)

  have h_tight := friedgut_tight_concentration f τ hτ_pos hτ_lt_one

  have hlog_val : Real.log (1 / τ) = 5 * K := by
    have h1 : (1 : ℝ) / τ = Real.exp (5 * K) := by
      show 1 / Real.exp (-5 * K) = Real.exp (5 * K)
      rw [show (-5 : ℝ) * K = -(5 * K) from by ring, Real.exp_neg, one_div, inv_inv]
    rw [h1, Real.log_exp]
  rw [hlog_val] at h_tight


  have hK_pos : (0 : ℝ) < K := by linarith
  have h5K_pos : (0 : ℝ) < 5 * K := by linarith
  have h_tail_le : 2 * totalInfluence f / (5 * K) ≤ 2 * varianceReal (liftPM f) / 5 := by
    rw [div_le_div_iff₀ h5K_pos (by norm_num : (0:ℝ) < 5)]
    nlinarith

  by_contra h_none
  push Not at h_none


  have hJ_empty : highInfluenceCoords f τ = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i
    simp only [highInfluenceCoords, Finset.mem_filter, Finset.mem_univ, true_and, not_le]
    exact h_none i

  have h_filter_eq : (univ : Finset (Finset (Fin n))).filter
      (fun S => ¬(S ⊆ highInfluenceCoords f τ)) =
      (univ : Finset (Finset (Fin n))).filter (· ≠ ∅) := by
    congr 1; ext S
    simp only [hJ_empty, Finset.subset_empty, ne_eq]

  rw [h_filter_eq] at h_tight

  have h_var_eq : ∑ S ∈ (univ : Finset (Finset (Fin n))).filter (· ≠ ∅),
      fourierCoeff (liftPM f) S ^ 2 = varianceReal (liftPM f) := by
    unfold varianceReal
    rfl
  rw [h_var_eq] at h_tight

  have h_absurd : varianceReal (liftPM f) ≤ 2 * varianceReal (liftPM f) / 5 := by
    linarith

  linarith

theorem friedgut_junta_theorem :
    ∃ C : ℝ, C > 0 ∧ ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (K : ℝ),
      varianceReal (liftPM f) > 0 →
      K ≥ 1 →
      totalInfluence f ≤ K * varianceReal (liftPM f) →
      ∃ i : Fin n, influence f i ≥ Real.exp (-C * K) := by
  refine ⟨5, by norm_num, fun n f K hVar hK1 hIK => ?_⟩
  exact friedgut_junta_corollary_bound f K hVar hK1 hIK

end BooleanFourier
