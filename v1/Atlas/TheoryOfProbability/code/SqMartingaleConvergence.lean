/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.BorelCantelli
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Atlas.TheoryOfProbability.code.MartingaleOrthogonality
import Atlas.TheoryOfProbability.code.MartingaleLpConvergence

open MeasureTheory Filter Topology

noncomputable section

/-- The **predictable quadratic variation** `Aₙ` of a process `f` with respect to a
filtration `ℱ`, defined as `Aₙ = ∑_{i=0}^{n-1} E[(f_{i+1} - f_i)² | ℱ_i]`. For a
square-integrable martingale this is the predictable increasing process arising
from Doob's decomposition of `f²`. -/
def predictableQuadVar {Ω : Type*} {m0 : MeasurableSpace Ω}
    (f : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m0) (μ : Measure Ω) : ℕ → Ω → ℝ :=
  fun n => ∑ i ∈ Finset.range n,
    μ[(fun ω => (f (i + 1) ω - f i ω) ^ 2) | ℱ i]

/-- Helper bound used in the square-integrable martingale convergence proof: if `f` is
a square-integrable martingale and `τ` is the first time the predictable quadratic
variation exceeds `M + 1`, then the stopped process `g = f^τ` is `L¹`-bounded
uniformly in `n`. -/
theorem stopped_martingale_L1_bound
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
    (hmart : Martingale f ℱ μ)
    (hinteg : ∀ n, Integrable (fun ω => (f n ω) ^ 2) μ)
    (M : ℕ) :
    let A := predictableQuadVar f ℱ μ
    let τ := leastGE (fun n => A (n + 1)) (↑M + 1)
    let g := stoppedProcess f τ
    ∃ (R : NNReal), ∀ n, eLpNorm (g n) 1 μ ≤ R := by sorry

/-- If a square-integrable martingale `f` has predictable quadratic variation bounded
by a constant `M` along the trajectory of `ω`, then `f n ω` converges as `n → ∞`,
for almost every such `ω`. This is the discrete analogue of bounded variation
ensuring convergence of a martingale. -/
lemma ae_convergent_of_bounded_predictable_quadvar
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
    (hmart : Martingale f ℱ μ)
    (hinteg : ∀ n, Integrable (fun ω => (f n ω) ^ 2) μ)
    (M : ℕ) :
    ∀ᵐ ω ∂μ,
      (∀ n, predictableQuadVar f ℱ μ n ω ≤ ↑M) →
      ∃ l, Tendsto (fun n => f n ω) atTop (𝓝 l) := by


  let A := predictableQuadVar f ℱ μ
  let τ := leastGE (fun n => A (n + 1)) (↑M + 1)
  let g := stoppedProcess f τ

  have hA_adapted : StronglyAdapted ℱ (fun n => A (n + 1)) := by
    intro n
    simp only [A, predictableQuadVar]
    apply Finset.stronglyMeasurable_sum
    intro i hi
    exact stronglyMeasurable_condExp.mono (ℱ.mono (by
      have := Finset.mem_range.mp hi; omega))

  have hτ : IsStoppingTime ℱ τ := hA_adapted.isStoppingTime_leastGE _

  have hg_sub : Submartingale g ℱ μ := hmart.submartingale.stoppedProcess hτ

  obtain ⟨R, hR⟩ := stopped_martingale_L1_bound hmart hinteg M

  have hg_conv : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => g n ω) atTop (𝓝 c) :=
    hg_sub.exists_ae_tendsto_of_bdd hR

  filter_upwards [hg_conv] with ω hω hbnd
  have hτ_top : τ ω = ⊤ := by
    rw [show τ = leastGE (fun n => A (n + 1)) (↑M + 1) from rfl]
    simp only [leastGE]
    rw [hittingAfter_eq_top_iff]
    intro n _
    simp only [Set.mem_Ici, not_le]
    have : A (n + 1) ω ≤ ↑M := hbnd (n + 1)
    linarith
  have hgf : ∀ n, g n ω = f n ω := by
    intro n
    show stoppedProcess f τ n ω = f n ω
    rw [stoppedProcess_eq_stoppedValue_apply]
    simp only [stoppedValue, hτ_top, min_top_right]
    rfl
  obtain ⟨c, hc⟩ := hω
  exact ⟨c, by rwa [show (fun n => f n ω) = (fun n => g n ω)
    from funext (fun n => (hgf n).symm)]⟩

/-- **Square integrable martingale convergence.** Suppose `Xₙ` is a martingale with
`E[Xₙ²] < ∞` for all `n` and let `Aₙ` be the associated predictable quadratic
variation. Then `lim_{n→∞} Xₙ` exists and is finite almost surely on the event
`{A_∞ < ∞}`. -/
theorem sq_martingale_convergence_on_predictable_quadvar_finite
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
    (hmart : Martingale f ℱ μ)
    (hinteg : ∀ n, Integrable (fun ω => (f n ω) ^ 2) μ) :
    ∀ᵐ ω ∂μ,
      (∃ l, Tendsto (fun n => predictableQuadVar f ℱ μ n ω) atTop (𝓝 l)) →
      ∃ l, Tendsto (fun n => f n ω) atTop (𝓝 l) := by

  have key : ∀ᵐ ω ∂μ, ∀ M : ℕ,
      (∀ n, predictableQuadVar f ℱ μ n ω ≤ ↑M) →
      ∃ l, Tendsto (fun n => f n ω) atTop (𝓝 l) := by
    rw [ae_all_iff]
    intro M
    exact ae_convergent_of_bounded_predictable_quadvar hmart hinteg M
  filter_upwards [key] with ω hω hconv
  obtain ⟨l, hl⟩ := hconv

  have hbdd : ∃ M : ℕ, ∀ n, predictableQuadVar f ℱ μ n ω ≤ ↑M := by
    have hbddunder := hl.isBoundedUnder_le
    obtain ⟨B, hB⟩ := hbddunder
    rw [eventually_map, eventually_atTop] at hB
    obtain ⟨N, hN⟩ := hB
    set u := fun n => predictableQuadVar f ℱ μ n ω
    have hglob : ∀ n, u n ≤
        max B (Finset.sup' (Finset.range (N + 1)) (by simp) u) := by
      intro n
      by_cases hn : N ≤ n
      · exact le_max_of_le_left (hN n hn)
      · have : n ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
        exact le_max_of_le_right (Finset.le_sup' u this)
    obtain ⟨M, hM⟩ := exists_nat_gt
      (max B (Finset.sup' (Finset.range (N + 1)) (by simp) u))
    exact ⟨M, fun n => (hglob n).trans (le_of_lt (by exact_mod_cast hM))⟩
  obtain ⟨M, hM⟩ := hbdd
  exact hω M hM

end
