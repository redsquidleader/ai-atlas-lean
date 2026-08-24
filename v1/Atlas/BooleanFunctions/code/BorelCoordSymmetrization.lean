/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.BorelOneD

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace GaussianStability

variable {n : ℕ}

def EuclideanSpace.updateCoord (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) (t : ℝ) :
    EuclideanSpace ℝ (Fin n) :=
  (WithLp.equiv 2 (Fin n → ℝ)).symm
    (Function.update ((WithLp.equiv 2 (Fin n → ℝ)) x) i t)

@[simp]
lemma EuclideanSpace.updateCoord_same (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) (t : ℝ) :
    (EuclideanSpace.updateCoord x i t) i = t := by
  simp [EuclideanSpace.updateCoord, WithLp.equiv, Function.update_self]

@[simp]
lemma EuclideanSpace.updateCoord_ne (x : EuclideanSpace ℝ (Fin n)) (i j : Fin n)
    (t : ℝ) (hij : j ≠ i) :
    (EuclideanSpace.updateCoord x i t) j = x j := by
  simp [EuclideanSpace.updateCoord, WithLp.equiv, Function.update_of_ne hij]

def conditionalMean (i : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ t, f (EuclideanSpace.updateCoord x i t) ∂(gaussianReal 0 1)

def symmetrize_coord (i : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => thresholdFn (conditionalMean i f x) (x i)

def fiberNoiseStability1D (i : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ t, (f (EuclideanSpace.updateCoord x i t)) *
    (∫ z, f (EuclideanSpace.updateCoord x i (ρ * t + √(1 - ρ^2) * z))
      ∂(gaussianReal 0 1))
    ∂(gaussianReal 0 1)

def fiberNoiseStability1D_symmetrized (i : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (ρ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∫ t, (thresholdFn (conditionalMean i f x) t) *
    (∫ z, (thresholdFn (conditionalMean i f x)) (ρ * t + √(1 - ρ^2) * z)
      ∂(gaussianReal 0 1))
    ∂(gaussianReal 0 1)

lemma fiber_stability_le_symmetrized (i : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_range : ∀ x, f x ∈ Icc (-1 : ℝ) 1)
    (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1)
    (x : EuclideanSpace ℝ (Fin n)) :
    fiberNoiseStability1D i f ρ x ≤
    fiberNoiseStability1D_symmetrized i f ρ x := by
  unfold fiberNoiseStability1D fiberNoiseStability1D_symmetrized
  have hg_range : ∀ t, f (EuclideanSpace.updateCoord x i t) ∈ Icc (-1 : ℝ) 1 :=
    fun t => hf_range _
  have hg_mean : ∫ t, f (EuclideanSpace.updateCoord x i t) ∂(gaussianReal 0 1) =
      conditionalMean i f x := rfl
  exact one_dim_noise_stability_le_threshold
    (fun t => f (EuclideanSpace.updateCoord x i t))
    hg_range
    (conditionalMean i f x)
    hg_mean
    ρ hρ₀ hρ₁


theorem gaussianNoiseStability_eq_integral_fiber
    {n : ℕ} (i : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_range : ∀ x, f x ∈ Icc (-1 : ℝ) 1)
    (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
    gaussianNoiseStability ρ hρ₀ hρ₁ f =
    ∫ x, fiberNoiseStability1D i f ρ x
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) := by sorry

theorem gaussianNoiseStability_symmetrized_eq_integral_fiber
    {n : ℕ} (i : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_range : ∀ x, f x ∈ Icc (-1 : ℝ) 1)
    (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
    gaussianNoiseStability ρ hρ₀ hρ₁ (symmetrize_coord i f) =
    ∫ x, fiberNoiseStability1D_symmetrized i f ρ x
      ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) := by sorry

theorem integrable_fiberNoiseStability1D
    {n : ℕ} (i : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_range : ∀ x, f x ∈ Icc (-1 : ℝ) 1)
    (ρ : ℝ) :
    Integrable (fiberNoiseStability1D i f ρ)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by sorry

theorem integrable_fiberNoiseStability1D_symmetrized
    {n : ℕ} (i : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_range : ∀ x, f x ∈ Icc (-1 : ℝ) 1)
    (ρ : ℝ) :
    Integrable (fiberNoiseStability1D_symmetrized i f ρ)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := by sorry

theorem coordinate_symmetrization_increases_stability
    {n : ℕ} (i : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_range : ∀ x, f x ∈ Icc (-1 : ℝ) 1)
    (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
    gaussianNoiseStability ρ hρ₀ hρ₁ f ≤
    gaussianNoiseStability ρ hρ₀ hρ₁ (symmetrize_coord i f) := by
  rw [gaussianNoiseStability_eq_integral_fiber i f hf_range ρ hρ₀ hρ₁,
      gaussianNoiseStability_symmetrized_eq_integral_fiber i f hf_range ρ hρ₀ hρ₁]
  exact integral_mono
    (integrable_fiberNoiseStability1D i f hf_range ρ)
    (integrable_fiberNoiseStability1D_symmetrized i f hf_range ρ)
    (fun x => fiber_stability_le_symmetrized i f hf_range ρ hρ₀ hρ₁ x)

end GaussianStability

end
