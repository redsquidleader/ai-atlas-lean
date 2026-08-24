/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.DifferentialOperators

open scoped SchwartzMap
open TemperedDistribution MvPolynomial Set Function MeasureTheory

noncomputable section

namespace DifferentialOperators

variable {n : ℕ}

/-- A tempered distribution `u` is *smooth* if it is represented by integration against a
smooth function `f : ℝⁿ → ℂ`, i.e. `u(ψ) = ∫ ψ · f` for all Schwartz test functions `ψ`. -/
def IsSmooth (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∃ f : EuclideanSpace ℝ (Fin n) → ℂ, ContDiff ℝ ⊤ f ∧
    ∀ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), u ψ = ∫ x, ψ x • f x

/-- A smooth cutoff function: a `C^∞` complex-valued function on `ℝⁿ` with compact support. -/
def IsSmoothCutoff (φ : EuclideanSpace ℝ (Fin n) → ℂ) : Prop :=
  ContDiff ℝ ⊤ φ ∧ HasCompactSupport φ

/-- The singular support of a tempered distribution `u`: the set of points `x₀` for which no
smooth cutoff function `φ` with `φ x₀ ≠ 0` makes the localised distribution `φ · u` smooth. -/
def singSupp (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x₀ | ¬ ∃ φ : EuclideanSpace ℝ (Fin n) → ℂ,
    IsSmoothCutoff φ ∧ φ x₀ ≠ 0 ∧ IsSmooth (smulLeftCLM ℂ φ u)}


/-- Near any point outside the singular support of `u`, one can choose a smooth cutoff `φ`
that equals `1` on a neighbourhood of the point and such that `φ · u` is smooth. -/
theorem cutoff_identity_near
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (x₀ : EuclideanSpace ℝ (Fin n))
    (hx : x₀ ∉ singSupp u) :
    ∃ φ : EuclideanSpace ℝ (Fin n) → ℂ,
      IsSmoothCutoff φ ∧
      (∃ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U ∧ x₀ ∈ U ∧ ∀ y ∈ U, φ y = 1) ∧
      IsSmooth (smulLeftCLM ℂ φ u) := by sorry


/-- Partition of unity decomposition for distributions: any tempered distribution `u` splits
as `φ · u + (1 - φ) · u = u` for any smooth function `φ`. -/
theorem smul_decomposition
    (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    smulLeftCLM ℂ φ u + smulLeftCLM ℂ (1 - φ) u = u := by sorry


/-- A constant-coefficient differential operator `P(D)` maps smooth distributions to smooth
distributions: if `u` is represented by a smooth function then so is `P(D) u`. -/
theorem constCoeffDiffOp_preserves_smooth
    (P : MvPolynomial (Fin n) ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hu : IsSmooth u) :
    IsSmooth (constCoeffDiffOp n P u) := by sorry


/-- Locality of differential operators: if the cutoff `ψ` is supported where `φ = 1`, then
`ψ · P(D) ((1 - φ) · u) = 0` because `1 - φ` vanishes on the support of `ψ`. -/
theorem locality_vanishing
    (P : MvPolynomial (Fin n) ℂ)
    (φ ψ : EuclideanSpace ℝ (Fin n) → ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hψ : IsSmoothCutoff ψ)
    (hsup : ∀ x, ψ x ≠ 0 → φ x = 1) :
    smulLeftCLM ℂ ψ (constCoeffDiffOp n P (smulLeftCLM ℂ (1 - φ) u)) = 0 := by sorry


/-- Multiplication by a smooth cutoff preserves smoothness of distributions: if `u` is
smooth and `ψ` is a smooth compactly supported function, then `ψ · u` is smooth. -/
theorem smul_cutoff_smooth
    (ψ : EuclideanSpace ℝ (Fin n) → ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hψ : IsSmoothCutoff ψ)
    (hu : IsSmooth u) :
    IsSmooth (smulLeftCLM ℂ ψ u) := by sorry


/-- For any open set `U` and point `x₀ ∈ U`, there exists a smooth cutoff `ψ` with
`ψ x₀ ≠ 0` and whose support is contained in `U`. -/
theorem exists_cutoff_in_open
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (hx : x₀ ∈ U) :
    ∃ ψ : EuclideanSpace ℝ (Fin n) → ℂ,
      IsSmoothCutoff ψ ∧ ψ x₀ ≠ 0 ∧ ∀ y, ψ y ≠ 0 → y ∈ U := by sorry

/-- Pseudolocal property of differential operators: a constant-coefficient differential
operator does not enlarge the singular support, i.e. `singSupp (P(D) u) ⊆ singSupp u`.
This is the key step in proving elliptic regularity. -/
theorem singSupp_constCoeffDiffOp_subset
    (P : MvPolynomial (Fin n) ℂ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    singSupp (constCoeffDiffOp n P u) ⊆ singSupp u := by

  intro x₀ hx₀
  simp only [singSupp, mem_setOf_eq] at hx₀ ⊢
  intro hsmooth_u
  apply hx₀

  have h_not_sing : x₀ ∉ singSupp u := by
    simp only [singSupp, mem_setOf_eq, not_not]
    exact hsmooth_u

  obtain ⟨φ, hφ_cutoff, ⟨U, hU_open, hx₀_U, hφ_one⟩, hφu_smooth⟩ :=
    cutoff_identity_near u x₀ h_not_sing

  obtain ⟨ψ, hψ_cutoff, hψ_x₀, hψ_supp⟩ := exists_cutoff_in_open U hU_open x₀ hx₀_U

  refine ⟨ψ, hψ_cutoff, hψ_x₀, ?_⟩

  have hdecomp : constCoeffDiffOp n P u =
    constCoeffDiffOp n P (smulLeftCLM ℂ φ u) +
    constCoeffDiffOp n P (smulLeftCLM ℂ (1 - φ) u) := by
    rw [← map_add, smul_decomposition]

  have hvanish : smulLeftCLM ℂ ψ (constCoeffDiffOp n P (smulLeftCLM ℂ (1 - φ) u)) = 0 :=
    locality_vanishing P φ ψ u hψ_cutoff (fun x hx => hφ_one x (hψ_supp x hx))

  have hPφu_smooth : IsSmooth (constCoeffDiffOp n P (smulLeftCLM ℂ φ u)) :=
    constCoeffDiffOp_preserves_smooth P (smulLeftCLM ℂ φ u) hφu_smooth

  rw [hdecomp, map_add (smulLeftCLM ℂ ψ), hvanish, add_zero]

  exact smul_cutoff_smooth ψ (constCoeffDiffOp n P (smulLeftCLM ℂ φ u)) hψ_cutoff hPφu_smooth

end DifferentialOperators

end
