/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Atlas.DifferentialAnalysis.code.DifferentialOperators

open scoped SchwartzMap
open MvPolynomial SchwartzMap

noncomputable section

namespace SmoothingOperators

open scoped LineDeriv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]


/-- Smoothing by a tempered distribution: convolving a tempered distribution
`u` with a Schwartz function `φ` (via the family of translations
`x ↦ u(φ(·−x))`) produces a smooth function. -/
theorem smoothing_produces_smooth
    (u : 𝓢'(E, ℂ)) (φ : 𝓢(E, ℂ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : E => u (compSubConstCLM ℂ x φ)) :=
  DifferentialOperators.contDiff_schwartz_translation_clm u φ


omit [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The Fréchet derivative of `z ↦ L(ψ(·−z))` at `x` evaluated on `h` equals
`L(∂_{-h} ψ (·−x))`: differentiating the family of translations in the
spatial variable produces a line derivative of `ψ` (in the opposite
direction) inside `L`. -/
theorem schwartz_translation_fderiv_apply
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : 𝓢(E, ℂ) →L[ℂ] F) (ψ : 𝓢(E, ℂ)) (x h : E) :
    fderiv ℝ (fun z => L (compSubConstCLM ℂ z ψ)) x h =
      L (compSubConstCLM ℂ x (∂_{-h} ψ)) := by

  have hlinederiv_eq : (∂_{-h} ψ : 𝓢(E, ℂ)) =
      -(SchwartzMap.evalCLM ℂ E ℂ h (SchwartzMap.fderivCLM ℂ E ℂ ψ)) := by
    ext y
    simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.neg_apply,
      SchwartzMap.evalCLM_apply_apply, SchwartzMap.fderivCLM_apply, map_neg]

  set ψ' := SchwartzMap.fderivCLM ℂ E ℂ ψ
  set g : E →L[ℝ] F :=
    -({ toFun := fun v => L (compSubConstCLM ℂ x (SchwartzMap.evalCLM ℂ E ℂ v ψ'))
        map_add' := by
          intro h₁ h₂
          have : SchwartzMap.evalCLM ℂ E ℂ (h₁ + h₂) ψ' =
                 SchwartzMap.evalCLM ℂ E ℂ h₁ ψ' + SchwartzMap.evalCLM ℂ E ℂ h₂ ψ' := by
            ext y; simp only [SchwartzMap.evalCLM_apply_apply, map_add, SchwartzMap.add_apply]
          rw [this, map_add, map_add]
        map_smul' := by
          intro r v
          simp only [RingHom.id_apply]
          have : SchwartzMap.evalCLM ℂ E ℂ (r • v) ψ' =
                 (r : ℂ) • SchwartzMap.evalCLM ℂ E ℂ v ψ' := by
            ext y
            simp only [SchwartzMap.evalCLM_apply_apply, SchwartzMap.smul_apply, map_smul]; rfl
          rw [this, map_smul, map_smul]; rfl } : E →ₗ[ℝ] F).toContinuousLinearMap

  suffices hfd : HasFDerivAt (fun z => L (compSubConstCLM ℂ z ψ)) g x by
    rw [hfd.fderiv]

    show g h = L (compSubConstCLM ℂ x (∂_{-h} ψ))
    simp only [g, ContinuousLinearMap.neg_apply]
    show -L (compSubConstCLM ℂ x (SchwartzMap.evalCLM ℂ E ℂ h ψ')) =
      L (compSubConstCLM ℂ x (∂_{-h} ψ))
    rw [hlinederiv_eq, map_neg, map_neg]

  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hrw : ∀ v : E,
      L (compSubConstCLM ℂ (x + v) ψ) - L (compSubConstCLM ℂ x ψ) - g v =
      L (compSubConstCLM ℂ x
        (compSubConstCLM ℂ v ψ - ψ + SchwartzMap.evalCLM ℂ E ℂ v ψ')) := by
    intro v
    have hcomp : compSubConstCLM ℂ (x + v) ψ =
        compSubConstCLM ℂ x (compSubConstCLM ℂ v ψ) := by
      rw [SchwartzMap.compSubConstCLM_comp]; congr 1; abel
    have hg : g v = -L (compSubConstCLM ℂ x (SchwartzMap.evalCLM ℂ E ℂ v ψ')) := rfl
    rw [hcomp, hg, sub_neg_eq_add, ← map_sub L, ← map_add L,
        ← map_sub (compSubConstCLM ℂ x), ← map_add (compSubConstCLM ℂ x)]
  simp_rw [hrw]
  exact DifferentialOperators.schwartz_taylor_remainder_isLittleO L ψ x


/-- Line derivative of the smoothed function: the directional derivative of
`x ↦ u(φ(·−x))` along `m` equals `u` applied to `∂_{-m} φ` translated to `x`.
This is the distributional identity used to differentiate the smoothing. -/
theorem smoothing_lineDeriv
    (u : 𝓢'(E, ℂ)) (φ : 𝓢(E, ℂ)) (m : E) (x : E) :
    lineDeriv ℝ (fun z : E => u (compSubConstCLM ℂ z φ)) x m =
      u (compSubConstCLM ℂ x (∂_{-m} φ)) := by
  have hdiff : DifferentiableAt ℝ (fun z => u (compSubConstCLM ℂ z φ)) x :=
    (DifferentialOperators.contDiff_schwartz_translation_clm u φ).differentiable (by simp)
      |>.differentiableAt
  rw [hdiff.lineDeriv_eq_fderiv]
  exact schwartz_translation_fderiv_apply u φ x m

end SmoothingOperators

namespace DifferentialOperators

variable {n : ℕ}

/-- Evaluation of a multivariate complex polynomial at a real Euclidean point,
viewed as a function `EuclideanSpace ℝ (Fin n) → ℂ`. -/
def evalAtReal (P : MvPolynomial (Fin n) ℂ) (ξ : EuclideanSpace ℝ (Fin n)) : ℂ :=
  MvPolynomial.eval (fun i => (ξ i : ℂ)) P

/-- The polynomial `P` has a polynomial lower bound of degree `m` with
constant `C > 0` if, for every `ξ` of norm larger than `1/C`, the
inequality `‖P(ξ)‖ ≥ C · ‖ξ‖^m` holds. -/
def HasPolyLowerBound (P : MvPolynomial (Fin n) ℂ) (m : ℕ) (C : ℝ) : Prop :=
  0 < C ∧ ∀ ξ : EuclideanSpace ℝ (Fin n),
    ‖ξ‖ > 1 / C → ‖evalAtReal P ξ‖ ≥ C * ‖ξ‖ ^ m

/-- The pointwise reciprocal of a polynomial: `ξ ↦ 1 / P(ξ)`, with
`P(ξ) = 0` mapped to `0` by the inverse convention. -/
def polyReciprocal (P : MvPolynomial (Fin n) ℂ) : EuclideanSpace ℝ (Fin n) → ℂ :=
  fun ξ => (evalAtReal P ξ)⁻¹


end DifferentialOperators

end
