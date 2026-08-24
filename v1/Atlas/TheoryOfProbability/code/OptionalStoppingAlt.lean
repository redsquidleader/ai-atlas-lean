/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Probability.Notation

open MeasureTheory Filter
open scoped ProbabilityTheory ENNReal

/-- Helper lemma: if `f` is a uniformly integrable submartingale adapted to `𝒢` and `N` is a
stopping time, then the sequence `n ↦ f_N · 1_{N ≤ n}` (the contribution to the stopped process
from indices that have already been stopped) is uniformly integrable in `L¹`. -/
theorem uniformIntegrable_stopped_second_term
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {𝒢 : Filtration ℕ m0}
    {f : ℕ → Ω → ℝ} {N : Ω → ℕ}
    (hf : Submartingale f 𝒢 μ)
    (hUI : UniformIntegrable f 1 μ)
    (hN : IsStoppingTime 𝒢 (fun ω => (N ω : ℕ∞))) :
    UniformIntegrable
      (fun n => fun ω => f (N ω) ω * Set.indicator {ω | N ω ≤ n} 1 ω) 1 μ := by

  have h_eq : ∀ n, (fun ω => f (N ω) ω * Set.indicator {ω | N ω ≤ n} 1 ω) =
      Set.indicator {ω | N ω ≤ n} (fun ω => f (N ω) ω) := by
    intro n; ext ω
    simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
    split_ifs with h <;> ring

  have h_meas_set : ∀ n, MeasurableSet {ω : Ω | N ω ≤ n} := by
    intro n
    have h_eq_set : {ω : Ω | N ω ≤ n} = {ω | (N ω : ℕ∞) ≤ ↑n} := by
      ext ω; simp only [Set.mem_setOf_eq, Nat.cast_le]
    rw [h_eq_set]
    exact (𝒢.le n) _ (hN n)

  obtain ⟨h_asm, h_ui, C, hC⟩ := hUI

  have h_norm_bound : ∀ n ω, ‖Set.indicator {ω | N ω ≤ n} (fun ω => f (N ω) ω) ω‖ ≤
      ‖f (min (N ω) n) ω‖ := by
    intro n ω
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs with h
    · rw [show min (N ω) n = N ω from Nat.min_eq_left h]
    · simp only [norm_zero]; exact norm_nonneg _

  refine ⟨?_, ?_, ?_⟩
  ·
    intro n
    show AEStronglyMeasurable (fun ω => f (N ω) ω * Set.indicator {ω | N ω ≤ n} 1 ω) μ
    rw [h_eq]


    have h_ae : (Set.indicator {ω | N ω ≤ n} (fun ω => f (N ω) ω)) =
        (Set.indicator {ω | N ω ≤ n} (fun ω => f (min (N ω) n) ω)) := by
      ext ω; simp only [Set.indicator_apply, Set.mem_setOf_eq]
      split_ifs with h
      · rw [show min (N ω) n = N ω from Nat.min_eq_left h]
      · rfl
    rw [h_ae]


    have h_stopped_sm : StronglyMeasurable (stoppedProcess f (fun ω => (↑(N ω) : ℕ∞)) n) :=
      hf.stronglyAdapted.stronglyMeasurable_stoppedProcess_of_discrete hN n
    have h_eq_stopped : (fun ω => f (min (N ω) n) ω) = stoppedProcess f (fun ω => (↑(N ω) : ℕ∞)) n := by
      ext ω
      by_cases h : N ω ≤ n
      · rw [show min (N ω) n = N ω from Nat.min_eq_left h]
        have := stoppedProcess_eq_of_ge (u := f) (τ := fun ω => (↑(N ω) : ℕ∞))
          (show (↑(N ω) : ℕ∞) ≤ ↑n from Nat.cast_le.mpr h)
        simp only [WithTop.untopA] at this
        exact this.symm
      · rw [show min (N ω) n = n from Nat.min_eq_right (by omega)]
        exact (stoppedProcess_eq_of_le (u := f) (τ := fun ω => (↑(N ω) : ℕ∞))
          (show (↑n : ℕ∞) ≤ ↑(N ω) from Nat.cast_le.mpr (by omega))).symm
    rw [h_eq_stopped]
    exact (h_stopped_sm.indicator (h_meas_set n)).aestronglyMeasurable
  ·
    intro ε hε
    obtain ⟨δ, hδ_pos, hδ⟩ := h_ui hε
    refine ⟨δ, hδ_pos, fun n s hs hμs => ?_⟩
    show eLpNorm (s.indicator (fun ω => f (N ω) ω * Set.indicator {ω | N ω ≤ n} 1 ω)) 1 μ ≤
      ENNReal.ofReal ε
    rw [show (fun ω => f (N ω) ω * Set.indicator {ω | N ω ≤ n} 1 ω) =
      Set.indicator {ω | N ω ≤ n} (fun ω => f (N ω) ω) from h_eq n]


    calc eLpNorm (s.indicator (Set.indicator {ω | N ω ≤ n} (fun ω => f (N ω) ω))) 1 μ
        ≤ eLpNorm (s.indicator (fun ω => f (min (N ω) n) ω)) 1 μ := by
          apply eLpNorm_mono_ae
          apply Filter.Eventually.of_forall; intro ω
          show ‖s.indicator (Set.indicator {ω | N ω ≤ n} (fun ω => f (N ω) ω)) ω‖ ≤
            ‖s.indicator (fun ω => f (min (N ω) n) ω) ω‖
          classical
          by_cases hs' : ω ∈ s
          · simp only [Set.indicator_of_mem hs']
            exact h_norm_bound n ω
          · simp only [Set.indicator_apply, if_neg hs']; exact le_refl _
      _ ≤ ENNReal.ofReal ε := by
          sorry
  ·
    refine ⟨C, fun n => ?_⟩
    show eLpNorm (fun ω => f (N ω) ω * Set.indicator {ω | N ω ≤ n} 1 ω) 1 μ ≤ ↑C
    rw [show (fun ω => f (N ω) ω * Set.indicator {ω | N ω ≤ n} 1 ω) =
      Set.indicator {ω | N ω ≤ n} (fun ω => f (N ω) ω) from h_eq n]
    calc eLpNorm (Set.indicator {ω | N ω ≤ n} (fun ω => f (N ω) ω)) 1 μ
        ≤ eLpNorm (fun ω => f (min (N ω) n) ω) 1 μ := by
          apply eLpNorm_mono_ae
          apply Filter.Eventually.of_forall; intro ω
          exact h_norm_bound n ω
      _ ≤ C := by


          sorry

/-- General optional stopping preservation of uniform integrability: if `f` is a uniformly
integrable submartingale adapted to `𝒢` and `N` is a stopping time, then the stopped process
`n ↦ f_{min(N, n)}` is also uniformly integrable. This is the key ingredient for the general
optional stopping theorem (Lecture 29). -/
theorem optional_stopping_alt_ui_preserved
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {𝒢 : Filtration ℕ m0}
    {f : ℕ → Ω → ℝ} {N : Ω → ℕ}
    (hf : Submartingale f 𝒢 μ)
    (hUI : UniformIntegrable f 1 μ)
    (hN : IsStoppingTime 𝒢 (fun ω => (N ω : ℕ∞))) :
    UniformIntegrable (fun n => fun ω => f (min (N ω) n) ω) 1 μ := by


  have hUI_alt : UniformIntegrable
      (fun n => fun ω => f n ω * Set.indicator {ω | N ω > n} 1 ω) 1 μ := by
    have h_eq : ∀ n, (fun ω => f n ω * Set.indicator {ω | N ω > n} 1 ω) =
        Set.indicator {ω | N ω > n} (f n) := by
      intro n; ext ω
      simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
      split_ifs with h <;> ring
    have h_meas_set : ∀ n, MeasurableSet {ω : Ω | N ω > n} := by
      intro n
      have h_le : MeasurableSet {ω | (N ω : ℕ∞) ≤ ↑n} := (𝒢.le n) _ (hN n)
      have h_eq_compl : {ω : Ω | N ω > n} = {ω | (N ω : ℕ∞) ≤ ↑n}ᶜ := by
        ext ω
        simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_le, Nat.cast_lt]
      rw [h_eq_compl]
      exact h_le.compl
    obtain ⟨h_asm, h_ui, C, hC⟩ := hUI
    refine ⟨?_, ?_, ?_⟩
    · intro n
      show AEStronglyMeasurable (fun ω => f n ω * Set.indicator {ω | N ω > n} 1 ω) μ
      rw [h_eq]
      exact (h_asm n).indicator (h_meas_set n)
    · intro ε hε
      obtain ⟨δ, hδ_pos, hδ⟩ := h_ui hε
      refine ⟨δ, hδ_pos, fun i s hs hμs => ?_⟩
      show eLpNorm (s.indicator (fun ω => f i ω * Set.indicator {ω | N ω > i} 1 ω)) 1 μ ≤
        ENNReal.ofReal ε
      rw [show (fun ω => f i ω * Set.indicator {ω | N ω > i} 1 ω) =
        Set.indicator {ω | N ω > i} (f i) from h_eq i]
      calc eLpNorm (s.indicator (Set.indicator {ω | N ω > i} (f i))) 1 μ
          = eLpNorm (Set.indicator {ω | N ω > i} (s.indicator (f i))) 1 μ := by
            congr 1; simp only [Set.indicator_indicator, Set.inter_comm]
        _ ≤ eLpNorm (s.indicator (f i)) 1 μ := eLpNorm_indicator_le _
        _ ≤ ENNReal.ofReal ε := hδ i s hs hμs
    · refine ⟨C, fun n => ?_⟩
      show eLpNorm (fun ω => f n ω * Set.indicator {ω | N ω > n} 1 ω) 1 μ ≤ ↑C
      rw [show (fun ω => f n ω * Set.indicator {ω | N ω > n} 1 ω) =
        Set.indicator {ω | N ω > n} (f n) from h_eq n]
      exact (eLpNorm_indicator_le _).trans (hC n)

  have h_decomp : ∀ n, (fun ω => f (min (N ω) n) ω) =ᵐ[μ]
      (fun ω => f n ω * Set.indicator {ω | N ω > n} 1 ω +
        f (N ω) ω * Set.indicator {ω | N ω ≤ n} 1 ω) := by
    intro n
    apply Filter.Eventually.of_forall
    intro ω
    simp only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply]
    split_ifs with h1 h2 h3
    · exfalso; omega
    · simp [show min (N ω) n = n from Nat.min_eq_right (le_of_lt h1)]
    · simp [show min (N ω) n = N ω from Nat.min_eq_left h3]
    · exfalso; omega

  have hUI_second := uniformIntegrable_stopped_second_term hf hUI hN

  obtain ⟨h1_meas, h1_unif, C1, hC1⟩ := hUI_alt
  obtain ⟨h2_meas, h2_unif, C2, hC2⟩ := hUI_second
  have h_sum_ui : UniformIntegrable
      (fun n => fun ω => f n ω * Set.indicator {ω | N ω > n} 1 ω +
        f (N ω) ω * Set.indicator {ω | N ω ≤ n} 1 ω) 1 μ := by
    refine ⟨fun n => (h1_meas n).add (h2_meas n), ?_, ?_⟩
    · exact h1_unif.add h2_unif le_rfl h1_meas h2_meas
    · exact ⟨C1 + C2, fun n =>
        (eLpNorm_add_le (h1_meas n) (h2_meas n) le_rfl).trans (add_le_add (hC1 n) (hC2 n))⟩

  exact h_sum_ui.ae_eq (fun n => (h_decomp n).symm)
