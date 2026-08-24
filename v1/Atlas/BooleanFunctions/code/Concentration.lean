/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open MeasureTheory ProbabilityTheory Real Finset

namespace Concentration


theorem hoeffding_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {Y : Fin n → Ω → ℝ}
    (hindep : iIndepFun (m := fun _ => inferInstance) Y μ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |Y i ω| ≤ 1)
    {ε : ℝ} (hε : 0 < ε) :
    μ.real {ω | ε * n ≤ (∑ i : Fin n, Y i ω) - ∑ i : Fin n, ∫ ω', Y i ω' ∂μ} ≤
      2 * exp (-(ε ^ 2 / (2 + ε)) * n) := by sorry

end Concentration
