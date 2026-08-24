/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Fin.VecNotation

namespace Reparametrization


theorem smooth_increasing_has_smooth_inverse
    (I_tilde : Set ℝ) (hI : Convex ℝ I_tilde)
    (ψ : ℝ → ℝ) (hψ_smooth : ContDiffOn ℝ ⊤ ψ I_tilde)
    (hψ_pos : ∀ t ∈ I_tilde, 0 < derivWithin ψ I_tilde t) :

    Convex ℝ (ψ '' I_tilde) ∧

    Set.InjOn ψ I_tilde ∧

    ∃ (φ : ℝ → ℝ),

      ContDiffOn ℝ ⊤ φ (ψ '' I_tilde) ∧

      (∀ t ∈ I_tilde, φ (ψ t) = t) ∧

      (∀ s ∈ ψ '' I_tilde, ψ (φ s) = s) ∧

      (∀ t ∈ I_tilde, derivWithin φ (ψ '' I_tilde) (ψ t) =
        (derivWithin ψ I_tilde t)⁻¹) := by sorry


theorem smooth_increasing_has_smooth_inverse_global
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ⊤ ψ)
    (hψ' : ∀ t, 0 < deriv ψ t) :
    Function.Injective ψ ∧
      ∃ (φ : ℝ → ℝ), Function.LeftInverse φ ψ ∧ Function.RightInverse φ ψ ∧
        ContDiff ℝ ⊤ φ ∧ ∀ t, deriv φ (ψ t) = (deriv ψ t)⁻¹ := by sorry

theorem reparametrize_to_graph (d : ℝ → Fin 2 → ℝ) (hd : ContDiff ℝ ⊤ d)
    (hd1 : ∀ t, 0 < deriv (fun s => d s 0) t) :
    ∃ (f : ℝ → ℝ) (φ : ℝ → ℝ), ContDiff ℝ ⊤ f ∧ ContDiff ℝ ⊤ φ ∧
      ∀ t, d (φ t) = ![t, f t] := by

  set ψ := fun s => d s 0 with hψ_def
  have hψ_smooth : ContDiff ℝ ⊤ ψ := (contDiff_apply ℝ ℝ 0).comp hd

  obtain ⟨_, φ, _, hφ_right, hφ_smooth, _⟩ :=
    smooth_increasing_has_smooth_inverse_global ψ hψ_smooth hd1

  set f := fun t => d (φ t) 1
  refine ⟨f, φ, ?_, hφ_smooth, ?_⟩
  ·
    exact ((contDiff_apply ℝ ℝ 1).comp hd).comp hφ_smooth
  ·
    intro t
    funext i
    fin_cases i
    ·
      exact hφ_right t
    ·
      rfl


theorem exists_smooth_arclength
    (d : ℝ → Fin 2 → ℝ) (hd : ContDiff ℝ ⊤ d)
    (hreg : ∀ t, deriv d t ≠ 0) :
    ∃ (ψ : ℝ → ℝ), ContDiff ℝ ⊤ ψ ∧ ∀ t, deriv ψ t = ‖deriv d t‖ := by sorry

theorem exists_unit_speed_reparametrization (d : ℝ → Fin 2 → ℝ) (hd : ContDiff ℝ ⊤ d)
    (hreg : ∀ t, deriv d t ≠ 0) :
    ∃ (φ : ℝ → ℝ), ContDiff ℝ ⊤ φ ∧ (∀ t, deriv φ t > 0) ∧
      ∀ t, ‖deriv (d ∘ φ) t‖ = 1 := by

  obtain ⟨ψ, hψ_smooth, hψ_deriv⟩ := exists_smooth_arclength d hd hreg

  have hψ_pos : ∀ t, 0 < deriv ψ t := by
    intro t; rw [hψ_deriv]; exact norm_pos_iff.mpr (hreg t)

  obtain ⟨_, φ, hφ_left, hφ_right, hφ_smooth, hφ_deriv⟩ :=
    smooth_increasing_has_smooth_inverse_global ψ hψ_smooth hψ_pos
  refine ⟨φ, hφ_smooth, ?_, ?_⟩
  ·


    intro t
    conv_lhs => rw [(hφ_right t).symm]
    rw [hφ_deriv]
    exact inv_pos_of_pos (hψ_pos _)
  ·
    intro t

    have hd_diff : DifferentiableAt ℝ d (φ t) :=
      (hd.differentiable (by simp)).differentiableAt
    have hφ_diff : DifferentiableAt ℝ φ t :=
      (hφ_smooth.differentiable (by simp)).differentiableAt
    rw [deriv.scomp t hd_diff hφ_diff]

    rw [norm_smul]

    have h_eq : deriv φ t = ‖deriv d (φ t)‖⁻¹ := by
      conv_lhs => rw [(hφ_right t).symm]
      rw [hφ_deriv, hψ_deriv]
    rw [h_eq, Real.norm_eq_abs, abs_of_pos (inv_pos_of_pos (norm_pos_iff.mpr (hreg _)))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hreg _))

end Reparametrization
