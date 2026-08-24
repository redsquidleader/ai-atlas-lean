/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfProbability.code.RandomWalkTailMeasurability
import Atlas.TheoryOfProbability.code.KolmogorovZeroOne
import Mathlib.Probability.Independence.Kernel.IndepFun

set_option maxHeartbeats 4000000

open MeasureTheory ProbabilityTheory Filter Finset Topology MeasurableSpace
open RandomWalkTailMeasurability

/-- Almost surely, every realization of an i.i.d. random walk falls into one of the four
behavioral classes (converges to a finite limit, drifts to `+∞`, drifts to `-∞`, or
oscillates between `+∞` and `-∞`). Equivalently, the complement of the union of these
four events is `μ`-null. -/
theorem randomWalk_events_cover_ae {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hindep : iIndepFun (m := fun _ => inferInstance) X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    μ ({ω | ∃ l : ℝ, Tendsto (fun n => randomWalkPartialSum X n ω) atTop (𝓝 l)} ∪
       {ω | Tendsto (fun n => randomWalkPartialSum X n ω) atTop atTop} ∪
       {ω | Tendsto (fun n => randomWalkPartialSum X n ω) atTop atBot} ∪
       {ω | limsup (fun n => (randomWalkPartialSum X n ω : EReal)) atTop = ⊤ ∧
            liminf (fun n => (randomWalkPartialSum X n ω : EReal)) atTop = ⊥})ᶜ = 0 := by
  sorry

/-- **Random walk dichotomy** (Durrett, Lecture 23). If `X₁, X₂, …` are i.i.d. real-valued
random variables and `Sₙ = ∑_{i<n} Xᵢ`, then with probability one exactly one of the
following occurs:
* `Sₙ → l` for some finite `l` (degenerate case `Xᵢ ≡ 0`),
* `Sₙ → +∞`,
* `Sₙ → -∞`,
* `liminf Sₙ = -∞` and `limsup Sₙ = +∞` (the walk oscillates). -/
theorem random_walk_dichotomy {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ)
    (hindep : iIndepFun (m := fun _ => inferInstance) X μ)
    (hident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ConvergesFinite μ X ∨ DriftsToTop μ X ∨ DriftsToBot μ X ∨ Oscillates μ X := by

  have haem : ∀ i, AEMeasurable (X i) μ := fun i => (hident i).aemeasurable_fst
  let Y : ℕ → Ω → ℝ := fun i => (haem i).mk (X i)
  have hYmeas : ∀ i, Measurable (Y i) := fun i => (haem i).measurable_mk
  have hYae : ∀ i, X i =ᵐ[μ] Y i := fun i => (haem i).ae_eq_mk

  have hYindep : iIndepFun (m := fun _ => inferInstance) Y μ := by
    unfold iIndepFun at hindep ⊢
    apply Kernel.iIndepFun.congr' hindep
    intro i
    simp only [ae_dirac_eq, Filter.eventually_pure]
    exact hYae i

  have h_le : ∀ n, MeasurableSpace.comap (Y n) inferInstance ≤ ‹MeasurableSpace Ω› :=
    fun n => MeasurableSpace.comap_le_iff_le_map.mpr (hYmeas n)

  have h01_CF := kolmogorov_zero_one_of_iIndepFun Y h_le hYindep (measurableSet_convergesFinite Y)
  have h01_DT := kolmogorov_zero_one_of_iIndepFun Y h_le hYindep (measurableSet_driftsToTop Y)
  have h01_DB := kolmogorov_zero_one_of_iIndepFun Y h_le hYindep (measurableSet_driftsToBot Y)
  have h01_Osc := kolmogorov_zero_one_of_iIndepFun Y h_le hYindep (measurableSet_oscillates Y)

  have hXY_ae : ∀ᵐ ω ∂μ, ∀ i, X i ω = Y i ω :=
    ae_all_iff.mpr (fun i => hYae i)
  have hps_ae : ∀ᵐ ω ∂μ, ∀ n, randomWalkPartialSum X n ω = randomWalkPartialSum Y n ω := by
    filter_upwards [hXY_ae] with ω hω
    intro n
    simp only [randomWalkPartialSum]
    exact Finset.sum_congr rfl (fun i _ => hω i)

  have hCF_ae : (({ω | ∃ l : ℝ, Tendsto (fun n => randomWalkPartialSum X n ω) atTop (𝓝 l)} : Set Ω) =ᵐ[μ]
      ({ω | ∃ l : ℝ, Tendsto (fun n => randomWalkPartialSum Y n ω) atTop (𝓝 l)} : Set Ω)) := by
    filter_upwards [hps_ae] with ω hω
    exact propext ⟨fun ⟨l, hl⟩ => ⟨l, hl.congr (fun n => hω n)⟩,
           fun ⟨l, hl⟩ => ⟨l, hl.congr (fun n => (hω n).symm)⟩⟩
  have hDT_ae : (({ω | Tendsto (fun n => randomWalkPartialSum X n ω) atTop atTop} : Set Ω) =ᵐ[μ]
      ({ω | Tendsto (fun n => randomWalkPartialSum Y n ω) atTop atTop} : Set Ω)) := by
    filter_upwards [hps_ae] with ω hω
    exact propext ⟨fun h => h.congr (fun n => hω n), fun h => h.congr (fun n => (hω n).symm)⟩
  have hDB_ae : (({ω | Tendsto (fun n => randomWalkPartialSum X n ω) atTop atBot} : Set Ω) =ᵐ[μ]
      ({ω | Tendsto (fun n => randomWalkPartialSum Y n ω) atTop atBot} : Set Ω)) := by
    filter_upwards [hps_ae] with ω hω
    exact propext ⟨fun h => h.congr (fun n => hω n), fun h => h.congr (fun n => (hω n).symm)⟩
  have hOsc_ae : (({ω | limsup (fun n => (randomWalkPartialSum X n ω : EReal)) atTop = ⊤ ∧
        liminf (fun n => (randomWalkPartialSum X n ω : EReal)) atTop = ⊥} : Set Ω) =ᵐ[μ]
      ({ω | limsup (fun n => (randomWalkPartialSum Y n ω : EReal)) atTop = ⊤ ∧
        liminf (fun n => (randomWalkPartialSum Y n ω : EReal)) atTop = ⊥} : Set Ω)) := by
    filter_upwards [hps_ae] with ω hω
    have heq : (fun n => (randomWalkPartialSum X n ω : EReal)) =
        (fun n => (randomWalkPartialSum Y n ω : EReal)) :=
      funext (fun n => congrArg _ (hω n))
    exact propext ⟨fun ⟨h1, h2⟩ => ⟨heq ▸ h1, heq ▸ h2⟩,
                   fun ⟨h1, h2⟩ => ⟨heq ▸ h1, heq ▸ h2⟩⟩

  have hcover_X := randomWalk_events_cover_ae μ X hindep hident

  let ECF_Y : Set Ω := {ω | ∃ l : ℝ, Tendsto (fun n => randomWalkPartialSum Y n ω) atTop (𝓝 l)}
  let EDT_Y : Set Ω := {ω | Tendsto (fun n => randomWalkPartialSum Y n ω) atTop atTop}
  let EDB_Y : Set Ω := {ω | Tendsto (fun n => randomWalkPartialSum Y n ω) atTop atBot}
  let EOsc_Y : Set Ω := {ω | limsup (fun n => (randomWalkPartialSum Y n ω : EReal)) atTop = ⊤ ∧
       liminf (fun n => (randomWalkPartialSum Y n ω : EReal)) atTop = ⊥}

  let ECF_X : Set Ω := {ω | ∃ l : ℝ, Tendsto (fun n => randomWalkPartialSum X n ω) atTop (𝓝 l)}
  let EDT_X : Set Ω := {ω | Tendsto (fun n => randomWalkPartialSum X n ω) atTop atTop}
  let EDB_X : Set Ω := {ω | Tendsto (fun n => randomWalkPartialSum X n ω) atTop atBot}
  let EOsc_X : Set Ω := {ω | limsup (fun n => (randomWalkPartialSum X n ω : EReal)) atTop = ⊤ ∧
       liminf (fun n => (randomWalkPartialSum X n ω : EReal)) atTop = ⊥}
  have hunion_ae : (ECF_X ∪ EDT_X ∪ EDB_X ∪ EOsc_X : Set Ω) =ᵐ[μ]
      (ECF_Y ∪ EDT_Y ∪ EDB_Y ∪ EOsc_Y : Set Ω) :=
    ((hCF_ae.union hDT_ae).union hDB_ae).union hOsc_ae
  have hcover_Y : μ (ECF_Y ∪ EDT_Y ∪ EDB_Y ∪ EOsc_Y)ᶜ = 0 := by
    rw [← measure_congr hunion_ae.compl]
    exact hcover_X

  have h_one := exists_prob_one_of_cover hcover_Y h01_CF h01_DT h01_DB h01_Osc

  have htail_le : tailMeasurableSpaceOfFun Y ≤ ‹MeasurableSpace Ω› :=
    iInf_le_of_le 0 (iSup₂_le fun i _ => h_le i)
  have hCF_meas : MeasurableSet ECF_Y := htail_le _ (measurableSet_convergesFinite Y)
  have hDT_meas : MeasurableSet EDT_Y := htail_le _ (measurableSet_driftsToTop Y)
  have hDB_meas : MeasurableSet EDB_Y := htail_le _ (measurableSet_driftsToBot Y)
  have hOsc_meas : MeasurableSet EOsc_Y := htail_le _ (measurableSet_oscillates Y)

  have ae_of_one : ∀ {E_X E_Y : Set Ω}, MeasurableSet E_Y → μ E_Y = 1 →
      E_X =ᵐ[μ] E_Y → ∀ᵐ ω ∂μ, ω ∈ E_X := by
    intro E_X E_Y hm h1 hae_eq
    have hYc : μ E_Yᶜ = 0 := by
      have := measure_compl hm (by rw [h1]; exact ENNReal.one_ne_top)
      rw [h1] at this; simp at this; exact this
    have hXc : μ E_Xᶜ = 0 := (measure_congr hae_eq.compl).trans hYc
    rw [Filter.eventually_iff_exists_mem]
    exact ⟨E_X, mem_ae_iff.mpr hXc, fun _ hx => hx⟩

  rcases h_one with h | h | h | h
  · left; exact ae_of_one hCF_meas h hCF_ae
  · right; left; exact ae_of_one hDT_meas h hDT_ae
  · right; right; left; exact ae_of_one hDB_meas h hDB_ae
  · right; right; right; exact ae_of_one hOsc_meas h hOsc_ae
