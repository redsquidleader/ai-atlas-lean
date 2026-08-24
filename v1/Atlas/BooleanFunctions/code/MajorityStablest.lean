/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.Stability
import Atlas.BooleanFunctions.code.GaussianStability
import Atlas.BooleanFunctions.code.InfluenceFourier

noncomputable section

open Finset BigOperators MeasureTheory ProbabilityTheory

namespace BooleanFourier

noncomputable def boolExpectation {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℝ :=
  (1 / (2 : ℝ) ^ n) * ∑ x : Fin n → Bool, f x

def IsBalanced {n : ℕ} (f : (Fin n → Bool) → ℝ) : Prop :=
  boolExpectation f = 0

def IsBooleanValued {n : ℕ} (f : (Fin n → Bool) → ℝ) : Prop :=
  ∀ x : Fin n → Bool, f x = 1 ∨ f x = -1

def maxInfluence {n : ℕ} (f : (Fin n → Bool) → ℝ) : ℝ :=
  ⨆ i : Fin n, influenceReal f i

def gaussianCDF (t : ℝ) : ℝ :=
  ((gaussianReal 0 1) (Set.Iic t)).toReal

def gaussianCDFInv (p : ℝ) : ℝ :=
  Function.invFun gaussianCDF p

def halfspaceNoiseStability01 (ρ μ : ℝ) : ℝ :=
  let t := gaussianCDFInv μ
  let γ := GaussianStability.rhoCorrelatedGaussian ρ
  (γ (Set.Iic t ×ˢ Set.Iic t)).toReal

def halfspaceNoiseStability (ρ μ : ℝ) : ℝ :=
  let t := gaussianCDFInv ((1 + μ) / 2)
  let γ := GaussianStability.rhoCorrelatedGaussian ρ
  4 * (γ (Set.Iic t ×ˢ Set.Iic t)).toReal - 4 * gaussianCDF t + 1

def HasBoundedRange01 {n : ℕ} (f : (Fin n → Bool) → ℝ) : Prop :=
  ∀ x, f x ∈ Set.Icc (0 : ℝ) 1

def HasBoundedRange {n : ℕ} (f : (Fin n → Bool) → ℝ) : Prop :=
  ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1

theorem majority_is_stablest_theorem01
    (ρ : ℝ) (hρ₀ : 0 < ρ) (hρ₁ : ρ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ),
      HasBoundedRange01 f →
      boolExpectation f = 1 / 2 →
      (∀ i : Fin n, influenceReal f i ≤ δ) →
      noiseStability ρ f ≤ halfspaceNoiseStability01 ρ (1 / 2) + ε := by sorry

theorem majority_is_stablest_general
    (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ),
      HasBoundedRange f →
      maxInfluence f ≤ δ →
      noiseStability ρ f ≤ halfspaceNoiseStability ρ (boolExpectation f) + ε := by sorry

end BooleanFourier

end
