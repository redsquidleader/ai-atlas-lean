/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.InvarianceDefs
import Mathlib.Probability.Distributions.Gaussian.Real

noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace BooleanFourier


theorem gaussianReal_third_abs_moment_le_two :
    ∫ t, |t| ^ 3 ∂(gaussianReal (0 : ℝ) 1) ≤ 2 := by sorry


theorem rademacher_avg_taylor (Ψ : ℝ → ℝ) (hΨ : IsC3Bounded Ψ) (c a : ℝ) :
    |(Ψ (c + a) + Ψ (c - a)) / 2 - Ψ c -
      (1 / 2) * iteratedDeriv 2 Ψ c * a ^ 2| ≤
    (1 / 6) * hΨ.thirdDerivBound * |a| ^ 3 := by sorry


theorem gaussian_integral_taylor (Ψ : ℝ → ℝ) (hΨ : IsC3Bounded Ψ) (c a : ℝ) :
    |∫ t, Ψ (c + a * t) ∂(gaussianReal (0 : ℝ) 1) - Ψ c -
      (1 / 2) * iteratedDeriv 2 Ψ c * a ^ 2| ≤
    (1 / 6) * hΨ.thirdDerivBound * |a| ^ 3 *
      ∫ t, |t| ^ 3 ∂(gaussianReal (0 : ℝ) 1) := by sorry

lemma lindeberg_one_dim_comparison (Ψ : ℝ → ℝ) (hΨ : IsC3Bounded Ψ) (c a : ℝ) :
    |((Ψ (c + a) + Ψ (c - a)) / 2) -
      ∫ t, Ψ (c + a * t) ∂(gaussianReal 0 1)| ≤
    (1 / 2) * hΨ.thirdDerivBound * |a| ^ 3 := by


  have h_rad := rademacher_avg_taylor Ψ hΨ c a
  have h_gauss := gaussian_integral_taylor Ψ hΨ c a
  have h_moment := gaussianReal_third_abs_moment_le_two
  have hM := hΨ.thirdDerivBound_nonneg

  set R := (Ψ (c + a) + Ψ (c - a)) / 2
  set G := ∫ t, Ψ (c + a * t) ∂(gaussianReal (0 : ℝ) 1)
  set P := Ψ c + (1 / 2) * iteratedDeriv 2 Ψ c * a ^ 2

  have h_tri : |R - G| ≤ |R - P| + |G - P| := by
    have h_eq : R - G = (R - P) + (P - G) := by ring
    have h_abs_neg : |P - G| = |G - P| := abs_sub_comm P G
    calc |R - G| = |(R - P) + (P - G)| := by rw [h_eq]
      _ ≤ |R - P| + |P - G| := abs_add_le (R - P) (P - G)
      _ = |R - P| + |G - P| := by rw [h_abs_neg]

  have h1 : |R - P| ≤ (1 / 6) * hΨ.thirdDerivBound * |a| ^ 3 := by
    convert h_rad using 2
    simp only [R, P]; ring

  have h2 : |G - P| ≤ (1 / 6) * hΨ.thirdDerivBound * |a| ^ 3 *
      ∫ t, |t| ^ 3 ∂(gaussianReal (0 : ℝ) 1) := by
    convert h_gauss using 2
    simp only [G, P]; ring

  calc |R - G|
      ≤ |R - P| + |G - P| := h_tri
    _ ≤ (1 / 6) * hΨ.thirdDerivBound * |a| ^ 3 +
        (1 / 6) * hΨ.thirdDerivBound * |a| ^ 3 *
          ∫ t, |t| ^ 3 ∂(gaussianReal (0 : ℝ) 1) := add_le_add h1 h2
    _ = (1 / 6) * hΨ.thirdDerivBound * |a| ^ 3 *
        (1 + ∫ t, |t| ^ 3 ∂(gaussianReal (0 : ℝ) 1)) := by ring
    _ ≤ (1 / 6) * hΨ.thirdDerivBound * |a| ^ 3 * (1 + 2) := by
        have hp : (0 : ℝ) ≤ (1 / 6) * hΨ.thirdDerivBound * |a| ^ 3 := by positivity
        have hm : ∫ t, |t| ^ 3 ∂(gaussianReal (0 : ℝ) 1) ≤ 2 := h_moment
        nlinarith
    _ = (1 / 2) * hΨ.thirdDerivBound * |a| ^ 3 := by ring

end BooleanFourier

end
