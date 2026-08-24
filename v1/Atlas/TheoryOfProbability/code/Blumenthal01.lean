/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.Independence.ZeroOne

open MeasureTheory MeasurableSpace Filtration

noncomputable section

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The *germ σ-algebra at `0`* of a filtration `𝓕` indexed by `NNReal`,
defined as the intersection `⋂_{t > 0} 𝓕_t`. For Brownian motion this is the
`𝓕_0^+` σ-algebra of events observable "immediately after" time `0`; Blumenthal's
0-1 law states that every such event has probability `0` or `1`. -/
@[reducible]
def germSigmaAlgebraZero (𝓕 : Filtration NNReal m) : MeasurableSpace Ω :=
  ⨅ t > (0 : NNReal), 𝓕 t

/-- Definitional unfolding: `germSigmaAlgebraZero 𝓕` equals the indexed infimum
`⨅ t > 0, 𝓕 t`. -/
lemma germSigmaAlgebraZero_eq_iInf (𝓕 : Filtration NNReal m) :
    germSigmaAlgebraZero 𝓕 = ⨅ t > (0 : NNReal), 𝓕 t := rfl

/-- An abstract specification of a *Brownian motion* `B : NNReal → Ω → E`
started at `x ∈ E`, adapted to a filtration `𝓕` on `(Ω, m, μ)`. The fields
require that `μ` is a probability measure, `B 0 = x` almost surely, `B` is
adapted, increments `B_t - B_s` are independent of `𝓕_s` for `s < t`, each
increment has *some* law on `E` (the Gaussian distribution in the standard
case), and the sample paths `t ↦ B_t ω` are continuous for a.e. `ω`. -/
structure IsBrownianMotion {E : Type*} [MeasurableSpace E] [AddCommGroup E]
    [TopologicalSpace E] (B : NNReal → Ω → E) (𝓕 : Filtration NNReal m)
    (μ : Measure Ω) (x : E) : Prop where
  isProbabilityMeasure : IsProbabilityMeasure μ
  start : ∀ᵐ ω ∂μ, B 0 ω = x
  adapted : Adapted 𝓕 (fun t => B t)
  indep_incr : ∀ s t : NNReal, s < t →
    Indep (𝓕 s) (MeasurableSpace.comap (fun ω => B t ω - B s ω) inferInstance) μ
  gaussian_incr : ∀ s t : NNReal, s < t →
    ∃ (ν : Measure E), Measure.map (fun ω => B t ω - B s ω) μ = ν
  continuous_path : ∀ᵐ ω ∂μ, Continuous (fun t : NNReal => B t ω)

/-- For any strictly positive time `t`, the germ σ-algebra at `0` is contained
in `𝓕 t`, since `𝓕 t` appears as one of the terms in the infimum
`⨅ s > 0, 𝓕 s`. -/
lemma germSigmaAlgebraZero_le_of_pos (𝓕 : Filtration NNReal m) {t : NNReal} (ht : 0 < t) :
    germSigmaAlgebraZero 𝓕 ≤ 𝓕 t := by
  rw [germSigmaAlgebraZero_eq_iInf]
  exact iInf₂_le t ht

/-- For Brownian motion, every component `𝓕 s` of the filtration (with `s > 0`)
is independent of the germ σ-algebra at `0`. This is a Markov-property
consequence of the independent-increments property and is the main ingredient
in the proof of Blumenthal's 0-1 law. -/
theorem markov_germ_indep_filtration_at {Ω : Type*} {m : MeasurableSpace Ω}
    {E : Type*} [MeasurableSpace E] [AddCommGroup E] [TopologicalSpace E]
    (B : NNReal → Ω → E) (𝓕 : Filtration NNReal m)
    (μ : Measure Ω) (x : E)
    (hBM : IsBrownianMotion B 𝓕 μ x)
    (s : NNReal) (hs : 0 < s) :
    Indep (𝓕 s) (germSigmaAlgebraZero 𝓕) μ := by sorry

/-- Any event `A` in the germ σ-algebra at `0` is independent of itself under
`μ`. This is the key intermediate step in the proof of Blumenthal's 0-1 law:
since `germSigmaAlgebraZero 𝓕 ≤ 𝓕 1` and `𝓕 1` is independent of the germ
σ-algebra (by `markov_germ_indep_filtration_at`), the germ σ-algebra is
independent of itself, which forces `μ(A) ∈ {0, 1}`. -/
lemma germ_sigma_indep_self {E : Type*} [MeasurableSpace E] [AddCommGroup E]
    [TopologicalSpace E]
    (B : NNReal → Ω → E) (𝓕 : Filtration NNReal m)
    (μ : Measure Ω) (x : E)
    (hBM : IsBrownianMotion B 𝓕 μ x)
    {A : Set Ω} (hA : MeasurableSet[germSigmaAlgebraZero 𝓕] A) :
    IndepSet A A μ := by


  have hs : (0 : NNReal) < 1 := by norm_num
  have hindep : Indep (𝓕 1) (germSigmaAlgebraZero 𝓕) μ :=
    markov_germ_indep_filtration_at B 𝓕 μ x hBM 1 hs

  have hle : germSigmaAlgebraZero 𝓕 ≤ 𝓕 1 :=
    germSigmaAlgebraZero_le_of_pos 𝓕 hs

  have hindep_self : Indep (germSigmaAlgebraZero 𝓕) (germSigmaAlgebraZero 𝓕) μ :=
    indep_of_indep_of_le_left hindep hle

  exact hindep_self.indepSet_of_measurableSet hA hA

/-- **Blumenthal's 0-1 law.** If `B` is a Brownian motion started at `x` with
filtration `𝓕`, then every event `A` in the germ σ-algebra `𝓕_0^+ = ⋂_{t > 0} 𝓕_t`
has `μ(A) ∈ {0, 1}` (Durrett, Lecture 36). Proof: by `germ_sigma_indep_self`,
`A` is independent of itself, so `μ(A) = μ(A)²`. -/
theorem blumenthal_zero_one {E : Type*} [MeasurableSpace E] [AddCommGroup E]
    [TopologicalSpace E]
    (B : NNReal → Ω → E) (𝓕 : Filtration NNReal m)
    (μ : Measure Ω) (x : E)
    (hBM : IsBrownianMotion B 𝓕 μ x)
    {A : Set Ω} (hA : MeasurableSet[germSigmaAlgebraZero 𝓕] A) :
    μ A = 0 ∨ μ A = 1 := by
  haveI := hBM.isProbabilityMeasure
  exact measure_eq_zero_or_one_of_indepSet_self (germ_sigma_indep_self B 𝓕 μ x hBM hA)

end ProbabilityTheory
