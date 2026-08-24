/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfProbability.code.MartingaleConvergence
import Atlas.TheoryOfProbability.code.UnifIntegrableLp

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

/--
Auxiliary lemma: if a submartingale `f` on a probability space has
`L^p`-norms uniformly bounded by `R` for some `1 < p < ∞`, then the family
`f` is `L^p`-uniformly integrable. Used in the proof of the `L^p` martingale
convergence theorem (Lecture 28).
-/
theorem unifIntegrable_p_at_p_of_submartingale
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
    {p : ENNReal} (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hsub : Submartingale f ℱ μ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    {R : NNReal} (hbdd : ∀ n, eLpNorm (f n) p μ ≤ R) :
    UnifIntegrable f p μ := by sorry

/--
`L^p` martingale convergence theorem (Lecture 28): if `f` is a submartingale
on a probability space with `sup_n ‖f n‖_p < ∞` for some `1 < p < ∞`, then
`f n` converges almost surely to a limit process `X`, and moreover the
convergence holds in `L^p` (i.e. `‖f n - X‖_p → 0`).
-/
theorem martingale_Lp_convergence_ae
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
    {p : ENNReal} {R : NNReal}
    (hsub : Submartingale f ℱ μ)
    (hp1 : 1 < p) (hp_top : p ≠ ⊤)
    (hbdd : ∀ n, eLpNorm (f n) p μ ≤ R) :
    (∀ᵐ ω ∂μ, Tendsto (fun n => f n ω) atTop (𝓝 (ℱ.limitProcess f μ ω))) ∧
    Tendsto (fun n => eLpNorm (f n - ℱ.limitProcess f μ) p μ) atTop (𝓝 0) := by
  have hp1' : (1 : ℝ≥0∞) ≤ p := le_of_lt hp1
  have hf_ae : ∀ n, AEStronglyMeasurable (f n) μ := fun n =>
    ((hsub.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable

  have hR1 : ∀ n, eLpNorm (f n) 1 μ ≤ R := fun n =>
    (eLpNorm_le_eLpNorm_of_exponent_le hp1' (hf_ae n)).trans (hbdd n)

  have hae := hsub.ae_tendsto_limitProcess hR1

  have hlimLp := Filtration.memLp_limitProcess_of_eLpNorm_bdd (ℱ := ℱ) hf_ae hbdd

  have hui := unifIntegrable_p_at_p_of_submartingale hp1 hp_top hsub hf_ae hbdd

  have him := tendstoInMeasure_of_tendsto_ae hf_ae hae
  have hLp := tendsto_Lp_finite_of_tendstoInMeasure hp1' hp_top hf_ae hlimLp hui him
  exact ⟨hae, hLp⟩
