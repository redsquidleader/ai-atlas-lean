/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Real Topology NNReal ENNReal

/-- The density of the standard normal distribution:
`stdNormalDensity t = (2π)^{-1/2} exp(-t²/2)`. -/
noncomputable def stdNormalDensity (t : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2) / 2)

/-- The cumulative distribution function of the standard normal:
`Φ(x) = ∫_{-∞}^{x} (2π)^{-1/2} e^{-t²/2} dt`. -/
noncomputable def standardNormalCDF (x : ℝ) : ℝ :=
  ∫ t in Set.Iic x, stdNormalDensity t

/-- **Berry-Esseen theorem.** Let `X_1, X_2, …` be i.i.d. real-valued random
variables with mean zero, finite variance `σ² > 0`, and finite third absolute
moment `ρ = E|X_1|^3 < ∞`. Let `F_n` be the distribution function of
`(X_1 + … + X_n)/(σ √n)`. Then for every `x ∈ ℝ`,
`|F_n(x) - Φ(x)| ≤ 3ρ/(σ³ √n)`,
where `Φ` is the standard normal CDF (Durrett, Lecture 16). -/
theorem berry_esseen
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ}
    (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (hmean : ∫ ω, X 0 ω ∂P = 0)
    (hσ_pos : 0 < ∫ ω, (X 0 ω) ^ 2 ∂P)
    (hρ : Integrable (fun ω => |X 0 ω| ^ (3 : ℕ)) P) :
    ∀ (n : ℕ) (_ : 0 < n) (x : ℝ),
      |((P.map (fun ω =>
          (Real.sqrt (∫ ω', (X 0 ω') ^ 2 ∂P) * Real.sqrt (↑n))⁻¹ *
          ∑ k ∈ Finset.range n, X k ω)).real (Set.Iic x))
        - standardNormalCDF x|
      ≤ 3 * (∫ ω, |X 0 ω| ^ (3 : ℕ) ∂P) /
          ((Real.sqrt (∫ ω, (X 0 ω) ^ 2 ∂P)) ^ 3 * Real.sqrt (↑n)) := by sorry

end
