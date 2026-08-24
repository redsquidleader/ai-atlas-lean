/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.SobolevEmbeddingTheorem

open scoped ZeroAtInfty SchwartzMap

noncomputable section

namespace SobolevEmbedding


/-- Multiplying a `Cᵏ` function vanishing at infinity by the inverse of a
power of the Japanese bracket `⟨x⟩^{-p}` again gives a `Cᵏ` function
vanishing at infinity, with the prescribed pointwise formula. -/
noncomputable def contDiffZeroAtInftyN_mul_japaneseBracketInvPow {n k : ℕ} (p : ℕ)
    (v : TestFunctions.ContDiffZeroAtInftyN n k) :
    { w : TestFunctions.ContDiffZeroAtInftyN n k //
      ⇑w.toZeroAtInftyContinuousMap =
        fun x => (↑(TestFunctions.japaneseBracket n x ^ p) : ℂ)⁻¹ *
          v.toZeroAtInftyContinuousMap x } := by sorry

/-- Any natural power of the Japanese bracket is a nonzero complex number,
since `⟨x⟩ ≥ 1 > 0`. -/
theorem japaneseBracket_pow_ne_zero_complex {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    (↑(TestFunctions.japaneseBracket n x ^ k) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (pow_pos (TestFunctions.japaneseBracket_pos n x) k).ne'

/-- Step in Melrose Prop. 10.4: a function lying in every weighted Sobolev
space gives rise, for each smoothness index `j` and weight `l`, to a `Cⱼ`
function vanishing at infinity whose value at `x` is `⟨x⟩^l · f(x)`.
Combines the Sobolev embedding theorem with multiplication by an inverse
weight. -/
def weightedSobolev_to_contDiffZeroAtInfty {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : ∀ k : ℕ, ∃ u : SobolevSpace n k,
      u.toFun = fun x => (↑(TestFunctions.japaneseBracket n x ^ k) : ℂ) * f x)
    (j l : ℕ) :
    { v : TestFunctions.ContDiffZeroAtInftyN n j //
      ⇑v.toZeroAtInftyContinuousMap =
        fun x => (↑(TestFunctions.japaneseBracket n x ^ l) : ℂ) * f x } := by
  let K := j + l + n + 1
  let u := (hf K).choose
  have hu : u.toFun = fun x => (↑(TestFunctions.japaneseBracket n x ^ K) : ℂ) * f x :=
    (hf K).choose_spec
  have hjK : j ≤ K := by omega
  have hn : n < 2 * (K - j) := by omega
  let p := K - l
  have hKl : l + p = K := by omega
  let emb := sobolevEmbeddingThm hjK hn u
  let ⟨w, hw⟩ := contDiffZeroAtInftyN_mul_japaneseBracketInvPow p emb
  refine ⟨w, ?_⟩
  have hemb : ⇑emb.toZeroAtInftyContinuousMap = u.toFun :=
    sobolevEmbeddingThm_toFun hjK hn u
  funext x
  have hw_x : w.toZeroAtInftyContinuousMap x =
      (↑(TestFunctions.japaneseBracket n x ^ p) : ℂ)⁻¹ *
        emb.toZeroAtInftyContinuousMap x := congr_fun hw x
  rw [hw_x]
  have hemb_x : (emb.toZeroAtInftyContinuousMap x : ℂ) = u.toFun x := congr_fun hemb x
  rw [hemb_x, hu]
  dsimp only []
  have hne : (↑(TestFunctions.japaneseBracket n x ^ p) : ℂ) ≠ 0 :=
    japaneseBracket_pow_ne_zero_complex x p
  have hbr_cast : (↑(TestFunctions.japaneseBracket n x ^ K) : ℂ) =
      ↑(TestFunctions.japaneseBracket n x ^ l) * ↑(TestFunctions.japaneseBracket n x ^ p) := by
    have h : TestFunctions.japaneseBracket n x ^ K =
        TestFunctions.japaneseBracket n x ^ l * TestFunctions.japaneseBracket n x ^ p := by
      rw [← pow_add, hKl]
    simp only [h, Complex.ofReal_mul]
  rw [hbr_cast, mul_assoc, mul_left_comm _ (↑(TestFunctions.japaneseBracket n x ^ p) : ℂ),
    inv_mul_cancel_left₀ hne]

/-- Melrose Prop. 10.4: a function lying in every weighted Sobolev space is
a Schwartz function.  This constructs the Schwartz representative explicitly
from the family of weighted Sobolev witnesses. -/
def allWeightedSobolev_to_schwartz {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (hf : ∀ k : ℕ, ∃ u : SobolevSpace n k,
      u.toFun = fun x => (↑(TestFunctions.japaneseBracket n x ^ k) : ℂ) * f x) :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) := by
  refine (TestFunctions.SchwartzTestFunctionSpace.equivSchwartzMap n).toFun
    ⟨f, fun j l => ?_⟩
  let ⟨v, hv⟩ := weightedSobolev_to_contDiffZeroAtInfty f hf j l
  refine ⟨⟨v⟩, fun x => ?_⟩
  change f x = (↑(TestFunctions.japaneseBracket n x ^ l) : ℂ)⁻¹ *
    v.toZeroAtInftyContinuousMap x
  have hv_x : v.toZeroAtInftyContinuousMap x =
    (↑(TestFunctions.japaneseBracket n x ^ l) : ℂ) * f x := congr_fun hv x
  rw [hv_x]
  rw [inv_mul_cancel_left₀ (japaneseBracket_pow_ne_zero_complex x l)]

/-- Multiplying a Schwartz function by any natural power of the Japanese
bracket again gives a Schwartz function, with the prescribed pointwise
formula.  Uses the fact that `⟨x⟩^k` has temperate growth. -/
def schwartz_mul_japaneseBracket_pow {n k : ℕ}
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    { g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) //
      ∀ x, g x = (↑(TestFunctions.japaneseBracket n x ^ k) : ℂ) * f x } := by

  set φ : EuclideanSpace ℝ (Fin n) → ℂ :=
    fun x => (↑(TestFunctions.japaneseBracket n x ^ k) : ℂ) with hφ_def

  have hφ : Function.HasTemperateGrowth φ := by
    simp only [hφ_def, TestFunctions.japaneseBracket]

    have h1 : (fun x : EuclideanSpace ℝ (Fin n) =>
        (↑((Real.sqrt (1 + ‖x‖ ^ 2)) ^ k) : ℂ)) =
      Complex.ofReal ∘ (fun x => (Real.sqrt (1 + ‖x‖ ^ 2)) ^ k) := by
      ext x; simp
    rw [h1]
    apply Function.Complex.hasTemperateGrowth_ofReal.comp

    have h2 : (fun x : EuclideanSpace ℝ (Fin n) =>
        (Real.sqrt (1 + ‖x‖ ^ 2)) ^ k) =
      (fun x => (1 + ‖x‖ ^ 2) ^ (k / 2 : ℝ)) := by
      ext x
      have hpos : (0 : ℝ) ≤ 1 + ‖x‖ ^ 2 := by positivity
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hpos]
      ring_nf
    rw [h2]
    exact Function.hasTemperateGrowth_one_add_norm_sq_rpow _ _

  exact ⟨SchwartzMap.smulLeftCLM ℂ φ f, fun x => by
    rw [SchwartzMap.smulLeftCLM_apply_apply hφ]
    exact smul_eq_mul (φ x) (f x)⟩

open MeasureTheory in
/-- Every iterated Fréchet derivative of a Schwartz function lies in `L²` with
respect to Lebesgue measure on `ℝⁿ`. -/
theorem schwartz_iteratedFDeriv_memLp {n : ℕ}
    (g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (j : ℕ) :
    MemLp (fun x => iteratedFDeriv ℝ j (⇑g) x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  set_option synthInstance.maxHeartbeats 80000 in
  rw [memLp_two_iff_integrable_sq_norm
    ((g.smooth (j : ℕ∞)).continuous_iteratedFDeriv le_rfl).aestronglyMeasurable]

  obtain ⟨C, hCpos, hC⟩ := g.decay 0 j
  simp only [pow_zero, one_mul] at hC

  have hint := g.integrable_pow_mul_iteratedFDeriv volume 0 j
  simp only [pow_zero, one_mul] at hint

  apply Integrable.mono (hint.const_mul C)
  · set_option synthInstance.maxHeartbeats 80000 in
    exact (((g.smooth (j : ℕ∞)).continuous_iteratedFDeriv le_rfl).norm.pow 2).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    rw [norm_mul, Real.norm_of_nonneg hCpos.le, Real.norm_of_nonneg (norm_nonneg _)]
    calc ‖iteratedFDeriv ℝ j (⇑g) x‖ ^ 2
        = ‖iteratedFDeriv ℝ j (⇑g) x‖ * ‖iteratedFDeriv ℝ j (⇑g) x‖ := sq _
      _ ≤ C * ‖iteratedFDeriv ℝ j (⇑g) x‖ := by gcongr; exact hC x

end SobolevEmbedding

end
