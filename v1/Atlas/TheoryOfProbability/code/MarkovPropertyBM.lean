/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Process.Filtration
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic.Linarith.NNRealPreprocessor

open MeasureTheory ProbabilityTheory MeasurableSpace Filter
open scoped NNReal ENNReal

noncomputable section

namespace BrownianMotion

variable {d : ℕ} {Ω : Type*} {m : MeasurableSpace Ω}

local notation "E" => EuclideanSpace ℝ (Fin d)

/-- `IsBrownianMotion B ℱ μ` asserts that the family `B : ℝ≥0 → Ω → E` is a `d`-dimensional
Brownian motion under `μ` adapted to the filtration `ℱ`. It packages the standard defining
properties: `B 0 = 0` almost surely, independent increments with respect to the filtration,
adaptedness, almost-sure continuous paths, and measurability of each increment. -/
structure IsBrownianMotion (B : ℝ≥0 → Ω → E) (ℱ : Filtration ℝ≥0 m) (μ : Measure Ω) : Prop where
  zero : ∀ᵐ ω ∂μ, B 0 ω = 0
  indep_increment : ∀ (s t : ℝ≥0), s ≤ t →
    Indep (ℱ s) (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) μ
  adapted : ∀ (t : ℝ≥0), Measurable[ℱ t] (B t)
  continuous_path : ∀ᵐ ω ∂μ, Continuous (fun t => B t ω)
  meas_increment : ∀ (s t : ℝ≥0), s ≤ t → Measurable (fun ω => B t ω - B s ω)

/-- The time-shifted path of a Brownian motion: `shiftPath B s ω` is the function
`t ↦ B (s + t) ω`, i.e. the path of `B` starting from time `s` instead of `0`. -/
def shiftPath (B : ℝ≥0 → Ω → E) (s : ℝ≥0) : Ω → (ℝ≥0 → E) :=
  fun ω t => B (s + t) ω

/-- The law on path space of the centered shifted path `t ↦ B (s + t) ω - B s ω`. By
independence and stationarity of Brownian increments, this measure does not depend on `s`
and equals the law of standard Brownian motion. -/
def shiftedPathLaw (B : ℝ≥0 → Ω → E) (μ : Measure Ω) (s : ℝ≥0) :
    Measure (ℝ≥0 → E) :=
  Measure.map (fun ω t => B (s + t) ω - B s ω) μ

/-- The expectation of a path functional `Y` under the law of Brownian motion started from
the point `x ∈ E`. Operationally, it integrates `Y (t ↦ x + f t)` against the law of the
centered shifted path `f`. This is the function `φ(x) = E_x Y` that appears as the
conditional expectation in the Markov property. -/
def pathExpectation (B : ℝ≥0 → Ω → E) (μ : Measure Ω) (s : ℝ≥0)
    (Y : (ℝ≥0 → E) → ℝ) (x : E) : ℝ :=
  ∫ f, Y (fun t => x + f t) ∂(shiftedPathLaw B μ s)

/-- Set-integral form of the Markov property for Brownian motion: for any bounded
measurable path functional `Y` and any event `A ∈ ℱ s`,

  `∫_A Y (shiftPath B s ω) dμ = ∫_A pathExpectation B μ s Y (B s ω) dμ`. -/
theorem setIntegral_shift_eq_pathExpectation
    {B : ℝ≥0 → Ω → E} {ℱ : Filtration ℝ≥0 m}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hB : IsBrownianMotion B ℱ μ)
    (s : ℝ≥0) (Y : (ℝ≥0 → E) → ℝ) (hY_meas : Measurable Y)
    (hY_bdd : ∃ C : ℝ, ∀ f, |Y f| ≤ C)
    (A : Set Ω) (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, Y (shiftPath B s ω) ∂μ =
      ∫ ω in A, pathExpectation B μ s Y (B s ω) ∂μ := by sorry

/-- **Markov property for Brownian motion** (conditional-expectation form). For any bounded
measurable path functional `Y` and any `s ≥ 0`,

  `E[Y(shiftPath B s ·) | ℱ s] = E_{B s} Y`  `μ`-a.e.,

where `E_x Y := pathExpectation B μ s Y x` is the expectation of `Y` under Brownian motion
started at `x`. This is the formalization of the textbook Markov property
`E_x(Y ∘ θ_s | ℱ_s⁺) = E_{B_s} Y`. -/
theorem markov_property_condExp {B : ℝ≥0 → Ω → E} {ℱ : Filtration ℝ≥0 m} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hB : IsBrownianMotion B ℱ μ)
    (s : ℝ≥0)
    (Y : (ℝ≥0 → E) → ℝ)
    (hY_meas : Measurable Y)
    (hY_bdd : ∃ C : ℝ, ∀ f, |Y f| ≤ C)
    (hg_int : Integrable (fun ω => pathExpectation B μ s Y (B s ω)) μ)
    (hg_meas : AEStronglyMeasurable[ℱ s]
      (fun ω => pathExpectation B μ s Y (B s ω)) μ) :
    μ[(fun ω => Y (shiftPath B s ω)) | ℱ s] =ᵐ[μ]
      fun ω => pathExpectation B μ s Y (B s ω) := by
  haveI : SigmaFinite (μ.trim (ℱ.le s)) := inferInstance
  obtain ⟨C, hC⟩ := hY_bdd
  have hmeas_shift : Measurable (shiftPath B s) :=
    measurable_pi_lambda _ fun t => (hB.adapted (s + t)).mono (ℱ.le _) le_rfl
  have hY_int : Integrable (fun ω => Y (shiftPath B s ω)) μ :=
    Integrable.of_bound (hY_meas.comp hmeas_shift).aestronglyMeasurable C
      (Eventually.of_forall fun ω => by simp only [Real.norm_eq_abs]; exact hC _)
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) hY_int ?_ ?_ ?_).symm
  · intro A _ _
    exact hg_int.integrableOn
  · intro A hA _
    exact (setIntegral_shift_eq_pathExpectation hB s Y hY_meas ⟨C, hC⟩ A hA).symm
  · exact hg_meas

end BrownianMotion
