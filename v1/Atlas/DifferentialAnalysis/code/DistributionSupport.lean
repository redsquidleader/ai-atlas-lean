/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.Support
import Atlas.DifferentialAnalysis.code.SchwartzPartition
import Atlas.DifferentialAnalysis.code.SchwartzCutoffConvergence

noncomputable section

open scoped SchwartzMap
open Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℝ E]

namespace SchwartzMap

/-- The compactly-supported Schwartz functions form a dense subset of the
Schwartz space `𝓢(E, ℂ)`. The proof multiplies a Schwartz function `f` by a
sequence of bump cutoffs and uses that the Schwartz seminorms of
`bumpCutoffMul m f - f` tend to zero as `m → ∞`. -/
theorem compactlySupportedDense :
    Dense {φ : 𝓢(E, ℂ) | HasCompactSupport φ} := by
  intro f
  apply mem_closure_of_tendsto (f := fun m => bumpCutoffMul m f) (b := Filter.atTop)
  ·
    rw [(schwartz_withSeminorms ℂ E ℂ).tendsto_nhds _ f]
    intro ⟨k, j⟩ ε hε
    have h := seminorm_cutoff_sub_tendsto ℂ f k j
    rw [Metric.tendsto_atTop] at h
    obtain ⟨N, hN⟩ := h ε hε
    filter_upwards [Filter.Ici_mem_atTop N] with m hm
    simp only [SchwartzMap.schwartzSeminormFamily_apply]
    have h1 := hN m hm
    rw [Real.dist_0_eq_abs, abs_of_nonneg (apply_nonneg _ _)] at h1
    calc (SchwartzMap.seminorm ℂ k j) (bumpCutoffMul m f - f)
        = (SchwartzMap.seminorm ℂ k j) (f - bumpCutoffMul m f) := by
          rw [← map_neg_eq_map]; congr 1; abel
      _ < ε := h1
  ·
    exact Filter.Eventually.of_forall (fun m => bumpCutoffMul_hasCompactSupport m f)

end SchwartzMap

namespace TemperedDistribution

/-- If a tempered distribution `u` vanishes on every compactly-supported
Schwartz function, then it vanishes on every Schwartz function. This is the
density argument bridging local information about `u` to its global
behaviour. -/
theorem compactly_supported_dense_in_schwartz
    (u : 𝓢'(E, F)) (ψ : 𝓢(E, ℂ))
    (h : ∀ (φ : 𝓢(E, ℂ)), HasCompactSupport φ → u φ = 0) :
    u ψ = 0 := by


  have hclosed : IsClosed {φ : 𝓢(E, ℂ) | u φ = 0} :=
    isClosed_eq u.cont continuous_const
  have hsub : {φ : 𝓢(E, ℂ) | HasCompactSupport φ} ⊆ {φ : 𝓢(E, ℂ) | u φ = 0} :=
    fun φ hφ => h φ hφ
  have hdense : Dense {φ : 𝓢(E, ℂ) | HasCompactSupport φ} :=
    SchwartzMap.compactlySupportedDense

  have hcl : closure {φ : 𝓢(E, ℂ) | HasCompactSupport φ} ⊆ {φ : 𝓢(E, ℂ) | u φ = 0} :=
    closure_minimal hsub hclosed

  have hψ : ψ ∈ closure {φ : 𝓢(E, ℂ) | HasCompactSupport φ} := by
    rw [hdense.closure_eq]
    exact Set.mem_univ ψ
  exact hcl hψ

/-- Proposition 8.9 of Melrose: a tempered distribution `u` with empty
distributional support is the zero distribution. The proof covers `E` by
open sets on which `u` vanishes, applies a Schwartz partition of unity to
deduce that `u` vanishes on every compactly-supported Schwartz function,
and then extends this to all Schwartz functions by density. -/
theorem eq_zero_of_dsupport_eq_empty (u : 𝓢'(E, F)) (hu : dsupport u = ∅) : u = 0 := by

  have h_local : ∀ x : E, ∃ s : Set E, IsVanishingOn (⇑u) s ∧ IsOpen s ∧ x ∈ s := by
    intro x
    have : x ∉ dsupport u := by simp [hu]
    rwa [notMem_dsupport_iff] at this


  have h_compact : ∀ (φ : 𝓢(E, ℂ)), HasCompactSupport φ → u φ = 0 :=
    fun φ hφ => schwartz_partition_of_unity_vanishing u h_local φ hφ


  ext ψ
  show u ψ = 0
  exact compactly_supported_dense_in_schwartz u ψ h_compact

end TemperedDistribution

end
