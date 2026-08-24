/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option maxHeartbeats 800000

noncomputable section

open Metric Set

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The real-valued quadratic form `φ ↦ Re⟨A φ, φ⟩` associated with an operator
`A` on a complex Hilbert space. -/
def innerQuadForm (A : H →L[ℂ] H) (φ : H) : ℝ :=
  Complex.re (@inner ℂ H _ (A φ) φ)

/-- The infimum of the numerical range of `A`: `m(A) = inf_{‖φ‖=1} Re⟨A φ, φ⟩`. -/
def numericalRangeInf (A : H →L[ℂ] H) : ℝ :=
  ⨅ φ : sphere (0 : H) 1, innerQuadForm A φ.1

/-- The supremum of the numerical range of `A`: `M(A) = sup_{‖φ‖=1} Re⟨A φ, φ⟩`. -/
def numericalRangeSup (A : H →L[ℂ] H) : ℝ :=
  ⨆ φ : sphere (0 : H) 1, innerQuadForm A φ.1

/-- Proposition 16.1 (compactness): the spectrum of a bounded operator on a
nontrivial complex Hilbert space is compact. -/
theorem prop_16_1_isCompact [Nontrivial H] (T : H →L[ℂ] H) :
    IsCompact (spectrum ℂ T) :=
  spectrum.isCompact T

/-- Proposition 16.1 (norm bound): the spectrum of `T` is contained in the closed
ball of radius `‖T‖` around the origin in `ℂ`. -/
theorem prop_16_1_subset_closedBall [Nontrivial H] (T : H →L[ℂ] H) :
    spectrum ℂ T ⊆ closedBall 0 ‖T‖ := by
  intro k hk
  simp only [mem_closedBall, dist_zero_right]
  exact spectrum.norm_le_norm_of_mem hk

/-- Proposition 16.1 (combined): the spectrum of `T` is compact and contained in
`closedBall 0 ‖T‖`. -/
theorem prop_16_1 [Nontrivial H] (T : H →L[ℂ] H) :
    IsCompact (spectrum ℂ T) ∧ spectrum ℂ T ⊆ closedBall 0 ‖T‖ :=
  ⟨prop_16_1_isCompact T, prop_16_1_subset_closedBall T⟩

/-- Proposition 16.2: for a self-adjoint operator `A`, both endpoints of the
numerical range `m, M` lie in the spectrum, and the spectrum is real and
contained in the real interval `[m, M]`. -/
theorem prop_16_2 [Nontrivial H] (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) :
    let m := numericalRangeInf A
    let M := numericalRangeSup A
    ({(m : ℂ), (M : ℂ)} ⊆ spectrum ℂ A) ∧
    (spectrum ℂ A ⊆ Complex.ofReal '' Icc m M) := by sorry

/-- Proposition 16.3 (spectral mapping bound): for a self-adjoint `A` and a
nonzero real polynomial `p`, the operator norm of `p(A)` is bounded by the
supremum of `|p(t)|` over the spectral interval `[m, M]`. -/
theorem prop_16_3 [Nontrivial H] (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)
    (p : Polynomial ℝ) (hp : p ≠ 0) :
    let m := numericalRangeInf A
    let M := numericalRangeSup A
    ‖Polynomial.aeval A p‖ ≤
      sSup ((fun t => |Polynomial.eval t p|) '' Icc m M) := by sorry

end
