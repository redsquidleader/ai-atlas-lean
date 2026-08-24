/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.MajorityStablest

noncomputable section

open Finset BigOperators MeasureTheory ProbabilityTheory

namespace BooleanFourier

lemma isBooleanValued_hasBoundedRange {n : ℕ} {f : (Fin n → Bool) → ℝ}
    (hf : IsBooleanValued f) : HasBoundedRange f := by
  intro x
  rcases hf x with h | h <;> rw [h] <;> constructor <;> norm_num

theorem majority_is_stablest_boolean
    (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ),
      IsBooleanValued f →
      maxInfluence f ≤ δ →
      noiseStability ρ f ≤ halfspaceNoiseStability ρ (boolExpectation f) + ε := by
  obtain ⟨δ, hδ_pos, hδ⟩ := majority_is_stablest_general ρ hρ₀ hρ₁ ε hε
  exact ⟨δ, hδ_pos, fun n f hBool hInf =>
    hδ n f (isBooleanValued_hasBoundedRange hBool) hInf⟩

end BooleanFourier

end
