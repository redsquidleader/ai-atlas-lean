/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Atlas.BooleanFunctions.code.GaussianStability
import Atlas.BooleanFunctions.code.Sheppard
import Atlas.BooleanFunctions.code.BorelCoordSymmetrization
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace GaussianStability

variable {n : ℕ}


lemma integral_stdGaussian_comp_coord {n : ℕ} (i : Fin n) (f : ℝ → ℝ)
    (hf : AEStronglyMeasurable f (gaussianReal 0 1)) :
    ∫ x : EuclideanSpace ℝ (Fin n), f (x i) ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) =
    ∫ t, f t ∂(gaussianReal 0 1) := by
  have hmp : MeasurePreserving (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
      (Measure.pi (fun _ : Fin n => gaussianReal 0 1))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) :=
    ⟨(MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable, map_pi_eq_stdGaussian⟩
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
  rw [← hmp.integral_comp hemb]
  show ∫ v : Fin n → ℝ, f (v i) ∂(Measure.pi (fun _ => gaussianReal 0 1)) = _
  exact integral_comp_eval hf

theorem sheppard_halfspace_stability_local
  {n : ℕ} (hn : 0 < n) (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
  gaussianNoiseStability ρ hρ₀ hρ₁
    (fun x : EuclideanSpace ℝ (Fin n) =>
      if (0 : ℝ) ≤ x (⟨0, hn⟩ : Fin n) then 1 else -1) =
    2 / π * arcsin ρ := by

  unfold gaussianNoiseStability gaussianNoiseOperator

  have h_inner : ∀ x : EuclideanSpace ℝ (Fin n),
      (∫ w : EuclideanSpace ℝ (Fin n),
        (if (0:ℝ) ≤ (ρ • x + √(1 - ρ^2) • w) (⟨0, hn⟩ : Fin n) then (1:ℝ) else -1)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))) =
      (∫ t : ℝ, (if (0:ℝ) ≤ ρ * (x (⟨0, hn⟩ : Fin n)) + √(1 - ρ^2) * t then (1:ℝ) else -1)
        ∂(gaussianReal 0 1)) := by
    intro x
    have heq : ∀ w : EuclideanSpace ℝ (Fin n),
        (if (0:ℝ) ≤ (ρ • x + √(1 - ρ^2) • w) (⟨0, hn⟩ : Fin n) then (1:ℝ) else -1) =
        (fun t : ℝ => if (0:ℝ) ≤ ρ * (x (⟨0, hn⟩ : Fin n)) + √(1 - ρ^2) * t then (1:ℝ) else -1)
          (w (⟨0, hn⟩ : Fin n)) := fun w => rfl
    simp_rw [heq]
    exact integral_stdGaussian_comp_coord ⟨0, hn⟩ _
      ((measurable_const.ite
        (measurableSet_le measurable_const (measurable_const.add (measurable_const.mul measurable_id)))
        measurable_const).aestronglyMeasurable)
  simp_rw [h_inner]

  have h_outer_asm : AEStronglyMeasurable
      (fun s => (if (0:ℝ) ≤ s then (1:ℝ) else -1) *
        ∫ t : ℝ, (if (0:ℝ) ≤ ρ * s + √(1 - ρ^2) * t then (1:ℝ) else -1) ∂(gaussianReal 0 1))
      (gaussianReal 0 1) := by
    apply AEStronglyMeasurable.mul
    · exact (measurable_const.ite measurableSet_Ici measurable_const).aestronglyMeasurable
    · apply StronglyMeasurable.aestronglyMeasurable
      apply StronglyMeasurable.integral_prod_right (ν := gaussianReal 0 1)
      apply Measurable.stronglyMeasurable
      exact measurable_const.ite
        (measurableSet_le measurable_const
          ((measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd)))
        measurable_const
  have h_outer := integral_stdGaussian_comp_coord (n := n) ⟨0, hn⟩
    (fun s => (if (0:ℝ) ≤ s then (1:ℝ) else -1) *
      ∫ t : ℝ, (if (0:ℝ) ≤ ρ * s + √(1 - ρ^2) * t then (1:ℝ) else -1) ∂(gaussianReal 0 1))
    h_outer_asm
  rw [h_outer]


  have h_eq_sign : (∫ s : ℝ, (if (0:ℝ) ≤ s then (1:ℝ) else -1) *
      ∫ t : ℝ, (if (0:ℝ) ≤ ρ * s + √(1 - ρ^2) * t then (1:ℝ) else -1) ∂(gaussianReal 0 1)
      ∂(gaussianReal 0 1)) = gaussianNoiseStabilitySign ρ := by

    unfold gaussianNoiseStabilitySign rhoCorrelatedGaussian signFn
    have hmeas_map : Measurable (fun p : ℝ × ℝ => (p.1, ρ * p.1 + √(1 - ρ^2) * p.2)) := by
      fun_prop
    have hf_meas : AEStronglyMeasurable
        (fun p : ℝ × ℝ => (if p.1 ≥ 0 then (1:ℝ) else -1) * (if p.2 ≥ 0 then (1:ℝ) else -1))
        (((gaussianReal 0 1).prod (gaussianReal 0 1)).map
          (fun p : ℝ × ℝ => (p.1, ρ * p.1 + √(1 - ρ^2) * p.2))) :=
      ((measurable_const.ite (measurableSet_Ici.preimage measurable_fst) measurable_const).mul
        (measurable_const.ite (measurableSet_Ici.preimage measurable_snd) measurable_const)).aestronglyMeasurable
    rw [integral_map hmeas_map.aemeasurable hf_meas]

    have h_integrable : Integrable
        (fun p : ℝ × ℝ => (if p.1 ≥ 0 then (1:ℝ) else -1) *
          (if (ρ * p.1 + √(1 - ρ^2) * p.2) ≥ 0 then (1:ℝ) else -1))
        ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      apply Integrable.of_bound (C := 1)
      · exact ((measurable_const.ite (measurableSet_Ici.preimage measurable_fst) measurable_const).mul
          (measurable_const.ite (measurableSet_Ici.preimage
            ((measurable_const.mul measurable_fst).add (measurable_const.mul measurable_snd)))
            measurable_const)).aestronglyMeasurable
      · filter_upwards with ⟨s, t⟩
        simp only [Real.norm_eq_abs]
        split_ifs <;> simp [abs_of_pos, abs_of_nonpos]

    rw [integral_prod _ h_integrable]

    congr 1; ext s
    rw [← integral_const_mul]
  rw [h_eq_sign]
  exact sheppard_formula ρ ⟨le_trans (neg_nonpos_of_nonneg zero_le_one) hρ₀, hρ₁⟩


def iterateSymmetrize {n : ℕ} (hn : 0 < n) :
    ℕ → (EuclideanSpace ℝ (Fin n) → ℝ) → (EuclideanSpace ℝ (Fin n) → ℝ)
  | 0, f => f
  | k + 1, f => if h : k < n then
      symmetrize_coord ⟨k, h⟩ (iterateSymmetrize hn k f)
    else iterateSymmetrize hn k f

lemma symmetrize_coord_range {n : ℕ} (i : Fin n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    symmetrize_coord i f x ∈ Set.Icc (-1 : ℝ) 1 := by
  unfold symmetrize_coord
  exact thresholdFn_range _ _

lemma iterateSymmetrize_range {n : ℕ} (hn : 0 < n) (k : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_range : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) :
    ∀ x, iterateSymmetrize hn k f x ∈ Set.Icc (-1 : ℝ) 1 := by
  induction k with
  | zero => exact hf_range
  | succ k ih =>
    intro x
    simp only [iterateSymmetrize]
    split_ifs with h
    · exact symmetrize_coord_range _ _ _
    · exact ih x

lemma iterateSymmetrize_mono_stability {n : ℕ} (hn : 0 < n) (k : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_range : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
    gaussianNoiseStability ρ hρ₀ hρ₁ f ≤
    gaussianNoiseStability ρ hρ₀ hρ₁ (iterateSymmetrize hn k f) := by
  induction k with
  | zero => simp [iterateSymmetrize]
  | succ k ih =>
    have hk_range := iterateSymmetrize_range hn k f hf_range
    simp only [iterateSymmetrize]
    split_ifs with h
    · calc gaussianNoiseStability ρ hρ₀ hρ₁ f
          ≤ gaussianNoiseStability ρ hρ₀ hρ₁ (iterateSymmetrize hn k f) := ih
        _ ≤ gaussianNoiseStability ρ hρ₀ hρ₁
              (symmetrize_coord ⟨k, h⟩ (iterateSymmetrize hn k f)) :=
            coordinate_symmetrization_increases_stability ⟨k, h⟩
              (iterateSymmetrize hn k f) hk_range ρ hρ₀ hρ₁
    · exact ih


theorem iterateSymmetrize_balanced_eq_halfspace_stability
    {n : ℕ} (hn : 0 < n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_range : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hf_balanced : ∫ x, f x ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) = 0)
    (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
    gaussianNoiseStability ρ hρ₀ hρ₁ (iterateSymmetrize hn n f) ≤
    gaussianNoiseStability ρ hρ₀ hρ₁
      (fun x : EuclideanSpace ℝ (Fin n) =>
        if (0 : ℝ) ≤ x (⟨0, hn⟩ : Fin n) then 1 else -1) := by sorry

theorem noise_stability_le_balanced_halfspace
  {n : ℕ} (hn : 0 < n) (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (hf_range : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
  (hf_balanced : ∫ x, f x ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) = 0)
  (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
  gaussianNoiseStability ρ hρ₀ hρ₁ f ≤
    gaussianNoiseStability ρ hρ₀ hρ₁
      (fun x : EuclideanSpace ℝ (Fin n) =>
        if (0 : ℝ) ≤ x (⟨0, hn⟩ : Fin n) then 1 else -1) :=
  calc gaussianNoiseStability ρ hρ₀ hρ₁ f
      ≤ gaussianNoiseStability ρ hρ₀ hρ₁ (iterateSymmetrize hn n f) :=
        iterateSymmetrize_mono_stability hn n f hf_range ρ hρ₀ hρ₁
    _ ≤ gaussianNoiseStability ρ hρ₀ hρ₁
          (fun x : EuclideanSpace ℝ (Fin n) =>
            if (0 : ℝ) ≤ x (⟨0, hn⟩ : Fin n) then 1 else -1) :=
        iterateSymmetrize_balanced_eq_halfspace_stability hn f hf_range hf_balanced ρ hρ₀ hρ₁

theorem borel_isoperimetric_core
  {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (hf_range : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
  (hf_balanced : ∫ x, f x ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) = 0)
  (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
  gaussianNoiseStability ρ hρ₀ hρ₁ f ≤ 2 / π * arcsin ρ := by

  rcases Nat.eq_zero_or_pos n with hn0 | hn
  ·

    subst hn0
    have huniq : ∀ x : EuclideanSpace ℝ (Fin 0), x = default :=
      fun x => Subsingleton.elim x _

    have hf0 : f default = 0 := by
      have h := integral_unique (μ := stdGaussian (EuclideanSpace ℝ (Fin 0))) f
      rw [hf_balanced] at h
      have hprob : (stdGaussian (EuclideanSpace ℝ (Fin 0))).real Set.univ = 1 := by
        rw [Measure.real]; simp [measure_univ]
      rw [hprob, one_smul] at h
      have hd : @default (EuclideanSpace ℝ (Fin 0)) Unique.instInhabited =
                @default (EuclideanSpace ℝ (Fin 0)) (instInhabitedPiLp 2 fun _ => ℝ) :=
        Subsingleton.elim _ _
      rw [← hd]; exact h.symm

    have hstab : gaussianNoiseStability ρ hρ₀ hρ₁ f = 0 := by
      unfold gaussianNoiseStability gaussianNoiseOperator
      simp_rw [huniq _, hf0, zero_mul, integral_zero]
    rw [hstab]
    exact mul_nonneg (div_nonneg (by norm_num : (0:ℝ) ≤ 2) (le_of_lt pi_pos))
      (arcsin_nonneg.mpr hρ₀)
  ·

    have h_le := noise_stability_le_balanced_halfspace hn f hf_range hf_balanced ρ hρ₀ hρ₁

    have h_eq := sheppard_halfspace_stability_local hn ρ hρ₀ hρ₁
    linarith

theorem borel_isoperimetric_theorem
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (hf_range : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
  (hf_balanced : ∫ x, f x ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) = 0)
  (ρ : ℝ) (hρ₀ : 0 ≤ ρ) (hρ₁ : ρ ≤ 1) :
  gaussianNoiseStability ρ hρ₀ hρ₁ f ≤ 1 - (2 / π) * arccos ρ := by

  have h_core := borel_isoperimetric_core f hf_range hf_balanced ρ hρ₀ hρ₁

  have h_eq : (2 / π) * arcsin ρ = 1 - (2 / π) * arccos ρ := by
    rw [arccos_eq_pi_div_two_sub_arcsin]
    have hpi : (π : ℝ) ≠ 0 := pi_ne_zero
    field_simp
    ring

  linarith

end GaussianStability

end
