/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.TestFunctions
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

open TestFunctions
open scoped ZeroAtInfty
open Filter Topology Metric

noncomputable section

namespace ConvolutionDensity

/-- The predicate `allPdBound k f δ` asserts that all partial derivatives of
`f` of order `≤ k` (taken with respect to standard basis directions) are
bounded by `δ` in norm.  Defined recursively in `k`. -/
def allPdBound {n : ℕ} : ℕ → (EuclideanSpace ℝ (Fin n) → ℂ) → ℝ → Prop
  | 0, f, δ => ∀ x, ‖f x‖ ≤ δ
  | k + 1, f, δ => allPdBound k f δ ∧
      ∀ j : Fin n, allPdBound k (fun x => fderiv ℝ f x (EuclideanSpace.single j 1)) δ

/-- If all partial derivatives of `f` of order `≤ k` are bounded by `δ`, then
the `Cᵏ` norm is bounded by `(n+1)^k · δ`. -/
lemma ckNorm_le_of_allPdBound {n : ℕ} :
    ∀ (k : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ) (δ : ℝ),
    0 ≤ δ → allPdBound k f δ → ckNorm n k f ≤ ((n : ℝ) + 1) ^ k * δ := by
  intro k; induction k with
  | zero =>
    intro f δ _ hb
    simp only [ckNorm, allPdBound, pow_zero, one_mul] at *
    exact ciSup_le hb
  | succ k ih =>
    intro f δ hδ ⟨hb_f, hb_deriv⟩
    simp only [ckNorm]
    calc ckNorm n k f +
          ∑ j : Fin n, ckNorm n k (fun x => fderiv ℝ f x (EuclideanSpace.single j 1))
        ≤ ((n : ℝ) + 1) ^ k * δ + ∑ _j : Fin n, ((n : ℝ) + 1) ^ k * δ := by
          gcongr with j _
          · exact ih f δ hδ hb_f
          · exact ih _ δ hδ (hb_deriv j)
      _ = ((n : ℝ) + 1) ^ k * δ + (n : ℝ) * (((n : ℝ) + 1) ^ k * δ) := by
          congr 1; rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      _ = ((n : ℝ) + 1) ^ (k + 1) * δ := by ring

/-- Pointwise bounds on the iterated Fréchet derivatives of `f` up to order
`k` imply the recursive bound `allPdBound k f δ` on the (axis-aligned)
partial derivatives. -/
lemma allPdBound_of_iteratedFDeriv_le {n : ℕ} :
    ∀ (k : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℂ) (δ : ℝ),
    ContDiff ℝ k f →
    (∀ (m : ℕ), m ≤ k → ∀ x, ‖iteratedFDeriv ℝ m f x‖ ≤ δ) →
    allPdBound k f δ := by
  intro k
  induction k with
  | zero =>
    intro f δ _ hbd x
    have := hbd 0 le_rfl x
    rwa [norm_iteratedFDeriv_zero] at this
  | succ k ih =>
    intro f δ hf hbd
    have hfk : ContDiff ℝ k f := hf.of_le (by norm_cast; omega)
    have hf_fderiv : ContDiff ℝ k (fderiv ℝ f) :=
      (contDiff_succ_iff_fderiv.mp (by exact_mod_cast hf)).2.2
    refine ⟨ih f δ hfk (fun m hm x => hbd m (le_trans hm (Nat.le_succ k)) x), ?_⟩
    intro j
    apply ih _ δ (((ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single j 1)).contDiff).comp hf_fderiv)
    intro m hm x
    have hm1 : m + 1 ≤ k + 1 := Nat.succ_le_succ hm
    have hcomp := ContinuousLinearMap.iteratedFDeriv_comp_left (x := x)
      (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single j 1))
      (hf_fderiv.contDiffAt) (i := m) (by norm_cast)
    rw [hcomp]
    calc ‖(ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single j 1)).compContinuousMultilinearMap
          (iteratedFDeriv ℝ m (fderiv ℝ f) x)‖
        ≤ ‖ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single (j : Fin n) (1 : ℝ))‖ *
          ‖iteratedFDeriv ℝ m (fderiv ℝ f) x‖ :=
          ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
      _ ≤ 1 * ‖iteratedFDeriv ℝ m (fderiv ℝ f) x‖ := by
          gcongr
          apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
          intro g; simp only [ContinuousLinearMap.apply_apply]
          calc ‖g (EuclideanSpace.single j 1)‖
              ≤ ‖g‖ * ‖EuclideanSpace.single (j : Fin n) (1 : ℝ)‖ :=
                ContinuousLinearMap.le_opNorm g _
            _ = ‖g‖ * 1 := by rw [PiLp.norm_single, norm_one]
            _ = 1 * ‖g‖ := by ring
      _ = ‖iteratedFDeriv ℝ (m + 1) f x‖ := by
          rw [one_mul, norm_iteratedFDeriv_fderiv]
      _ ≤ δ := hbd (m + 1) hm1 x


/-- For every `Cᵏ` function `u` that vanishes at infinity and every `δ > 0`,
there exists a radius `R` so large that for any smooth bump function with
inner radius `R` and outer radius `R + 1`, all iterated derivatives of
`u - φ · u` are at most `δ` in norm outside the ball of radius `R`. -/
theorem iteratedFDeriv_cutoff_bound
    {n : ℕ} (k : ℕ) (u : ContDiffZeroAtInftyN n k) (δ : ℝ) (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧
      ∀ (b : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))),
        b.rIn = R → b.rOut = R + 1 →
        ∀ (m : ℕ), m ≤ k → ∀ x,
          R ≤ ‖x‖ →
          ‖iteratedFDeriv ℝ m
            (fun x => u.toZeroAtInftyContinuousMap x -
              (↑(b x) : ℂ) * u.toZeroAtInftyContinuousMap x) x‖ ≤ δ := by sorry

set_option maxHeartbeats 1600000 in
/-- Combining `iteratedFDeriv_cutoff_bound` with
`allPdBound_of_iteratedFDeriv_le`: for every `δ > 0`, multiplying `u` by a
sufficiently far-out cutoff produces an error whose mixed partial derivatives
up to order `k` are bounded by `δ`. -/
theorem allPdBound_cutoff_mul
    {n : ℕ} (k : ℕ) (u : ContDiffZeroAtInftyN n k) (δ : ℝ) (hδ : 0 < δ) :
    ∃ R : ℝ, 0 < R ∧
      ∀ (b : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))),
        b.rIn = R → b.rOut = R + 1 →
        allPdBound k
          (fun x => u.toZeroAtInftyContinuousMap x -
            (↑(b x) : ℂ) * u.toZeroAtInftyContinuousMap x) δ := by

  obtain ⟨R, hR_pos, hR_bd⟩ := iteratedFDeriv_cutoff_bound k u δ hδ
  refine ⟨R, hR_pos, fun b hrIn hrOut => ?_⟩
  set g := fun x => u.toZeroAtInftyContinuousMap x -
    (↑(b x) : ℂ) * u.toZeroAtInftyContinuousMap x with hg_def

  have hg_smooth : ContDiff ℝ k g := by
    apply ContDiff.sub u.contDiff_k
    exact (Complex.ofRealCLM.contDiff.comp (b.contDiff (n := (k : ℕ∞)))).mul u.contDiff_k

  apply allPdBound_of_iteratedFDeriv_le k g δ hg_smooth
  intro m hm x

  by_cases hx : x ∈ ball (0 : EuclideanSpace ℝ (Fin n)) R
  ·
    have hb_eq : b =ᶠ[𝓝 x] 1 := b.eventuallyEq_one_of_mem_ball (hrIn ▸ hx)
    have hg_eq : g =ᶠ[𝓝 x] 0 := by
      filter_upwards [hb_eq] with y hy
      simp [hg_def, hy, Complex.ofReal_one]
    have h1 := (hg_eq.iteratedFDeriv ℝ m).self_of_nhds
    simp only [Pi.zero_def, iteratedFDeriv_fun_zero] at h1
    rw [h1]; simp [le_of_lt hδ]
  ·
    simp only [mem_ball, dist_zero_right, not_lt] at hx
    exact hR_bd b hrIn hrOut m hm x hx

set_option maxHeartbeats 800000 in
/-- Density: every `Cᵏ` function vanishing at infinity can be approximated in
`Cᵏ` norm by a smooth compactly supported function, with error less than any
prescribed `ε > 0`.  Concretely, multiply `u` by a sufficiently far-out
bump function. -/
theorem approx_by_compactly_supported_Ck
    {n : ℕ} (k : ℕ) (u : ContDiffZeroAtInftyN n k) (ε : ℝ) (hε : 0 < ε) :
    ∃ (v : EuclideanSpace ℝ (Fin n) → ℂ),
      HasCompactSupport v ∧ ContDiff ℝ k v ∧
      ckNorm n k (fun x => u.toZeroAtInftyContinuousMap x - v x) < ε := by
  set δ := ε / (2 * ((n : ℝ) + 1) ^ k) with hδ_def
  have hn1_pos : (0 : ℝ) < ((n : ℝ) + 1) ^ k := by positivity
  have hδ_pos : 0 < δ := by positivity
  obtain ⟨R, hR_pos, hR_bound⟩ := allPdBound_cutoff_mul k u δ hδ_pos
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨R, R + 1, hR_pos, by linarith⟩
  let v : EuclideanSpace ℝ (Fin n) → ℂ :=
    fun x => (↑(b x) : ℂ) * u.toZeroAtInftyContinuousMap x
  refine ⟨v, ?_, ?_, ?_⟩
  · exact (b.hasCompactSupport.comp_left (g := Complex.ofReal)
      Complex.ofReal_zero).mul_right
  · exact (Complex.ofRealCLM.contDiff.comp
      (b.contDiff (n := (k : ℕ∞)))).mul u.contDiff_k
  · have h_bound := hR_bound b rfl rfl
    calc ckNorm n k (fun x => u.toZeroAtInftyContinuousMap x - v x)
        ≤ ((n : ℝ) + 1) ^ k * δ :=
          ckNorm_le_of_allPdBound k _ δ (le_of_lt hδ_pos) h_bound
      _ = ε / 2 := by rw [hδ_def]; field_simp
      _ < ε := by linarith

end ConvolutionDensity

end
