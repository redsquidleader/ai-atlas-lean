/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.PseudoDiffOps

open DifferentialOperators
open TemperedDistribution MvPolynomial
open scoped SchwartzMap Pointwise

noncomputable section

namespace DifferentialOperators

variable {n : ℕ}


/-- A constant-coefficient differential operator preserves compact support: if the tempered
distribution `F` vanishes outside a compact `K`, then so does `P(D) F`. -/
theorem constCoeffDiffOp_hasCompactSupport
    (P : MvPolynomial (Fin n) ℂ)
    (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hFcs : ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (∀ y, y ∈ K → φ y = 0) → F φ = 0) :
    HasCompactSupport (constCoeffDiffOp n P F) := by sorry


/-- The Dirac delta distribution `δ_0` has compact support, namely `{0}`. -/
theorem delta_hasCompactSupport :
    HasCompactSupport
      (TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))) := by sorry


/-- Subtraction of two compactly supported distributions has compact support. -/
theorem sub_hasCompactSupport
    (μ ν : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ) (hν : HasCompactSupport ν) :
    HasCompactSupport (μ - ν) := by sorry


/-- Adding a globally smooth distribution does not enlarge the singular support: if `v` is
smooth everywhere, then `singularSupport u ⊆ singularSupport (u - v)`. -/
theorem singularSupport_subset_sub_smooth
    (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hv_smooth : ∀ y, isSmoothNear v y) :
    singularSupport u ⊆ singularSupport (u - v) := by sorry


/-- Subtracting a globally smooth distribution does not enlarge the singular support, giving
the reverse inclusion `singularSupport (u - v) ⊆ singularSupport u`. -/
theorem singularSupport_sub_smooth_subset
    (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hv_smooth : ∀ y, isSmoothNear v y) :
    singularSupport (u - v) ⊆ singularSupport u := by sorry


/-- Parametrix singular-support bound via distributional convolution: writing `P(D) F = δ + ψ`
where `ψ = P(D) F - δ` has compact support, the singular support of `u - ψ * u` is contained
in `singularSupport F + singularSupport (P(D) u)`. This is the convolution form of the
parametrix identity used in pseudolocal elliptic regularity. -/
theorem parametrix_distribConvolution_singSupp_bound
    (P : MvPolynomial (Fin n) ℂ)
    (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hFparam : IsParametrix P F)
    (hFcs : ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (∀ y, y ∈ K → φ y = 0) → F φ = 0)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hpsi_cs : HasCompactSupport (constCoeffDiffOp n P F -
        TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n)))) :
    singularSupport (u - distribConvolution
      (constCoeffDiffOp n P F - TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n)))
      u hpsi_cs)
    ⊆ singularSupport F + singularSupport (constCoeffDiffOp n P u) := by sorry

/-- Pseudolocal elliptic regularity via the parametrix: for any tempered distribution `u`,
`singularSupport u ⊆ singularSupport F + singularSupport (P(D) u)`, where `F` is a parametrix
for `P`. In particular, when `Pu` is smooth, `u` is smooth wherever `F` is smooth — the heart
of the parametrix method. -/
theorem parametrix_singSupp_u_bound
    (P : MvPolynomial (Fin n) ℂ)
    (F : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hFparam : IsParametrix P F)
    (hFcs : ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (∀ y, y ∈ K → φ y = 0) → F φ = 0)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    singularSupport u ⊆ singularSupport F + singularSupport (constCoeffDiffOp n P u) := by
  set psi := constCoeffDiffOp n P F -
    TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n))
  have hpsi_cs : HasCompactSupport psi :=
    sub_hasCompactSupport _ _
      (constCoeffDiffOp_hasCompactSupport P F hFcs)
      delta_hasCompactSupport
  have hpsi_smooth : ∀ y, isSmoothNear psi y := by
    intro y
    rw [IsParametrix, singularSupport] at hFparam
    simp only [Set.eq_empty_iff_forall_notMem, Set.mem_setOf_eq, not_not] at hFparam
    exact hFparam y
  set v0 := distribConvolution psi u hpsi_cs
  have hv0_smooth : ∀ y, isSmoothNear v0 y :=
    fun y => isSmoothNear_distribConvolution_of_smooth_left psi u hpsi_cs hpsi_smooth y


  exact (singularSupport_subset_sub_smooth u v0 hv0_smooth).trans
    (parametrix_distribConvolution_singSupp_bound P F hFparam hFcs u hpsi_cs)

end DifferentialOperators
