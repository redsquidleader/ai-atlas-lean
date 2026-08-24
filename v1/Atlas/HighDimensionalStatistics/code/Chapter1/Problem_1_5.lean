/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter1.Def_1_2
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Probability.Independence.Basic

open MeasureTheory ProbabilityTheory Real Finset

noncomputable section

/-- The ℓq (quasi)norm on `Fin n → ℝ`:
`‖x‖_q = (∑ |xᵢ|^q)^{1/q}`. -/
noncomputable def lqNorm (n : ℕ) (q : ℝ) (x : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, |x i| ^ q) ^ (1 / q)

/-- **Problem 1.5(a).** Norm comparison: for `q ≥ 2`,
`‖x‖₂ ≤ ‖x‖_q · n^{1/2 - 1/q}` on `ℝⁿ`. -/
theorem problem_1_5a_norm_comparison
    (n : ℕ) (q : ℝ) (hq : 2 ≤ q) (x : Fin n → ℝ) :
    lqNorm n 2 x ≤ lqNorm n q x * (n : ℝ) ^ (1 / 2 - 1 / q) := by
  unfold lqNorm
  have hq_pos : (0:ℝ) < q := by linarith
  have hq_ne : q ≠ 0 := ne_of_gt hq_pos
  have hq2 : (1:ℝ) ≤ q / 2 := by linarith
  have h1q_pos : (0:ℝ) < 1 / q := by positivity

  have hS2 : (0:ℝ) ≤ ∑ i : Fin n, |x i| ^ (2:ℝ) :=
    Finset.sum_nonneg (fun i _ => rpow_nonneg (abs_nonneg _) _)
  have hSq : (0:ℝ) ≤ ∑ i : Fin n, |x i| ^ q :=
    Finset.sum_nonneg (fun i _ => rpow_nonneg (abs_nonneg _) _)
  have key : (∑ i : Fin n, |x i| ^ (2:ℝ)) ^ (q/2) ≤
      (↑n : ℝ) ^ (q / 2 - 1) * ∑ i : Fin n, |x i| ^ q := by
    have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (Finset.univ : Finset (Fin n))
      hq2 (fun i _ => rpow_nonneg (abs_nonneg (x i)) (2:ℝ))
    simp only [Finset.card_univ, Fintype.card_fin] at h
    convert h using 2
    apply Finset.sum_congr rfl
    intro i _
    rw [← rpow_mul (abs_nonneg _)]
    ring_nf
  have key2 : ((∑ i : Fin n, |x i| ^ (2:ℝ)) ^ (q/2)) ^ (1/q) ≤
      ((↑n : ℝ) ^ (q / 2 - 1) * ∑ i : Fin n, |x i| ^ q) ^ (1/q) :=
    rpow_le_rpow (rpow_nonneg hS2 _) key (le_of_lt h1q_pos)

  rw [← rpow_mul hS2, show q / 2 * (1 / q) = 1 / 2 from by field_simp] at key2

  have hexp : (q / 2 - 1) * (1 / q) = 1 / 2 - 1 / q := by field_simp
  rw [mul_rpow (rpow_nonneg (Nat.cast_nonneg n) _) hSq,
      ← rpow_mul (Nat.cast_nonneg n), hexp] at key2

  linarith [mul_comm ((∑ i : Fin n, |x i| ^ q) ^ (1 / q)) ((↑n : ℝ) ^ (1 / 2 - 1 / q))]

/-- **Problem 1.5(b).** For independent sub-Gaussian variables `X₁,…,Xₙ` with
proxy `σ²` and `q > 1`, `E ‖X‖_q ≤ 4 σ · n^{1/q} · √q`. -/
theorem problem_1_5b_lq_norm_bound
    {n : ℕ} (hn : 0 < n)
    {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω} (_ : IsProbabilityMeasure μ)
    {X : Fin n → Ω → ℝ} {σ : ℝ} (hσ : 0 ≤ σ)
    (hXmeas : ∀ i, Measurable (X i))
    (hXsubG : ∀ i, IsSubGaussian (X i) (σ ^ 2) μ)
    (hXindep : iIndepFun (β := fun _ : Fin n => ℝ) X μ)
    (q : ℝ) (hq : 1 < q) :
    ∫ ω, lqNorm n q (fun i => X i ω) ∂μ ≤
      4 * σ * (n : ℝ) ^ (1 / q) * Real.sqrt q := by sorry

/-- **Problem 1.5(c).** Maximal inequality: for `n ≥ 2`,
`E[max_i |X_i|] ≤ 4 e σ √(log n)` for independent sub-Gaussian `X_i`. -/
theorem problem_1_5c_max_bound
    {n : ℕ} (hn : 2 ≤ n)
    {Ω : Type*} {_ : MeasurableSpace Ω} {μ : Measure Ω} (_ : IsProbabilityMeasure μ)
    {X : Fin n → Ω → ℝ} {σ : ℝ} (hσ : 0 ≤ σ)
    (hXmeas : ∀ i, Measurable (X i))
    (hXsubG : ∀ i, IsSubGaussian (X i) (σ ^ 2) μ)
    (hXindep : iIndepFun (β := fun _ : Fin n => ℝ) X μ) :
    ∫ ω, (Finset.univ.sup' ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
      (fun i : Fin n => |X i ω|)) ∂μ ≤
      4 * Real.exp 1 * σ * Real.sqrt (Real.log n) := by sorry

end
