/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

namespace MeasureTheory

open MeasureTheory Finset

/-- The running maximum of `|f k ω|` over `0 ≤ k ≤ n`, i.e.
`maxProcess f n ω = max_{0 ≤ k ≤ n} |f k ω|`. -/
noncomputable def maxProcess {Ω : Type*} (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range (n + 1)).sup' ⟨0, Finset.mem_range.mpr (by omega)⟩ (fun k => |f k ω|)

/-- The **predictable quadratic variation** of `f` with respect to `ℱ` and `μ`,
defined pointwise by
`A_n(ω) = ∑_{k=0}^{n-1} E[(f_{k+1} - f_k)² | ℱ_k] (ω)`. -/
noncomputable def predictableQuadraticVariation {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) (ℱ : Filtration ℕ m0) (f : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (Finset.range n).sum (fun k =>
    (condExp (ℱ k) μ (fun ω' => (f (k + 1) ω' - f k ω') ^ 2)) ω)

/-- **Square integrable martingale maximal inequality (finite horizon).** For a
square-integrable martingale `Xₙ`, the expected square of `max_{0 ≤ k ≤ n} |X_k|`
is bounded by `4 · E[A_n]`, where `A_n = ∑_{k<n} E[(X_{k+1} - X_k)² | ℱ_k]` is the
predictable quadratic variation. -/
theorem doob_sq_maximal_ineq
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
    [IsProbabilityMeasure μ]
    (hmart : Martingale f ℱ μ)
    (hL2 : ∀ n, MemLp (f n) 2 μ)
    (n : ℕ) :
    ∫ ω, (maxProcess f n ω) ^ 2 ∂μ ≤
    4 * ∫ ω, predictableQuadraticVariation μ ℱ f n ω ∂μ := by sorry

/-- **Square integrable martingale maximal inequality (infinite horizon).** For a
square-integrable martingale `Xₙ`, `E[sup_n |X_n|²] ≤ 4 · E[A_∞]`, where
`A_∞ = ∑_{k≥0} E[(X_{k+1} - X_k)² | ℱ_k]`. This is the ENNReal-valued form
applicable to the supremum over all `n`. -/
theorem doob_sq_maximal_ineq_iSup
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
    [IsProbabilityMeasure μ]
    (hmart : Martingale f ℱ μ)
    (hL2 : ∀ n, MemLp (f n) 2 μ) :
    ∫⁻ ω, ⨆ n, ENNReal.ofReal (|f n ω| ^ 2) ∂μ ≤
    4 * ∫⁻ ω, ⨆ n, ENNReal.ofReal (predictableQuadraticVariation μ ℱ f n ω) ∂μ := by sorry

end MeasureTheory
