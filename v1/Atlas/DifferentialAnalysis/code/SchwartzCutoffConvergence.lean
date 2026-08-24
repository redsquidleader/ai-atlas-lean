/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

open Filter Topology Metric
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [HasContDiffBump E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SchwartzMap

/-- A sequence of smooth bump functions `χ_m` on `E`, supported in
`B(0, m + 2)` and equal to one on `B(0, m + 1)`. -/
noncomputable def bumpSeq (m : ℕ) : ContDiffBump (0 : E) :=
  ⟨↑m + 1, ↑m + 2, by positivity, by linarith⟩

omit [NormedSpace ℝ E] [HasContDiffBump E] [FiniteDimensional ℝ E] in
/-- The inner radius of `bumpSeq m` is `m + 1`. -/
@[simp]
lemma bumpSeq_rIn (m : ℕ) : (bumpSeq (E := E) m).rIn = ↑m + 1 := rfl

omit [NormedSpace ℝ E] [HasContDiffBump E] [FiniteDimensional ℝ E] in
/-- The outer radius of `bumpSeq m` is `m + 2`. -/
@[simp]
lemma bumpSeq_rOut (m : ℕ) : (bumpSeq (E := E) m).rOut = ↑m + 2 := rfl

/-- The bump `bumpSeq m` is identically `1` on the closed ball of radius `m + 1`. -/
lemma bumpSeq_one_of_norm_le (m : ℕ) {x : E} (hx : ‖x‖ ≤ ↑m + 1) :
    bumpSeq (E := E) m x = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact hx

/-- Each `bumpSeq m` has temperate growth: it is compactly supported and smooth. -/
lemma bumpSeq_hasTemperateGrowth (m : ℕ) :
    Function.HasTemperateGrowth (fun x => (bumpSeq (E := E) m x : ℝ)) :=
  HasCompactSupport.hasTemperateGrowth (bumpSeq m).hasCompactSupport (bumpSeq m).contDiff

/-- Cutoff of a Schwartz function by `bumpSeq m`: multiplies `f` pointwise by the bump. -/
noncomputable def bumpCutoffMul (m : ℕ) (f : SchwartzMap E F) : SchwartzMap E F :=
  SchwartzMap.smulLeftCLM (𝕜 := ℝ) F (fun x => bumpSeq (E := E) m x) f

/-- Pointwise formula for the cutoff: `bumpCutoffMul m f x = χ_m(x) • f x`. -/
@[simp]
lemma bumpCutoffMul_apply (m : ℕ) (f : SchwartzMap E F) (x : E) :
    bumpCutoffMul m f x = bumpSeq (E := E) m x • f x := by
  unfold bumpCutoffMul
  rw [SchwartzMap.smulLeftCLM_apply (bumpSeq_hasTemperateGrowth m)]

/-- The cutoff `bumpCutoffMul m f` has compact support inside `B̄(0, m + 2)`. -/
lemma bumpCutoffMul_hasCompactSupport (m : ℕ) (f : SchwartzMap E F) :
    HasCompactSupport (bumpCutoffMul m f) := by
  apply HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall 0 (↑m + 2))
    (isCompact_closedBall 0 _)
  intro x hx
  rw [Function.mem_support] at hx
  simp only [bumpCutoffMul_apply] at hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra h
  push Not at h
  have hout : (bumpSeq (E := E) m).rOut ≤ dist x 0 := by
    rw [dist_zero_right]; simp only [bumpSeq]; linarith
  have := (bumpSeq m).zero_of_le_dist hout
  simp [this] at hx

/-- The difference `f - χ_m f` vanishes in a neighbourhood of any point inside
`B(0, m + 1)`, since `χ_m ≡ 1` there. -/
lemma sub_bumpCutoffMul_eventuallyEq_zero (m : ℕ) (f : SchwartzMap E F) {x : E}
    (hx : ‖x‖ < ↑m + 1) :
    (fun y => (f - bumpCutoffMul m f) y) =ᶠ[nhds x] (fun _ => (0 : F)) := by
  have hmem : x ∈ Metric.ball (0 : E) (bumpSeq (E := E) m).rIn := by
    simp only [Metric.mem_ball, dist_zero_right, bumpSeq]; exact hx
  have hev := (bumpSeq (E := E) m).eventuallyEq_one_of_mem_ball hmem
  filter_upwards [hev] with y hy
  simp only [SchwartzMap.sub_apply, bumpCutoffMul_apply, Pi.one_apply] at hy ⊢
  rw [hy, one_smul, sub_self]

/-- All iterated Fréchet derivatives of `f - χ_m f` vanish on `B(0, m + 1)`. -/
lemma iteratedFDeriv_sub_bumpCutoffMul_eq_zero (m : ℕ) (f : SchwartzMap E F)
    (n : ℕ) {x : E} (hx : ‖x‖ < ↑m + 1) :
    iteratedFDeriv ℝ n (fun y => (f - bumpCutoffMul m f) y) x = 0 := by
  have hev := sub_bumpCutoffMul_eventuallyEq_zero m f hx
  have h := (hev.iteratedFDeriv ℝ n).self_of_nhds
  rw [h]
  rcases eq_or_ne n 0 with rfl | hn
  · ext v; simp
  · simp [iteratedFDeriv_const_of_ne hn (0 : F)]

end SchwartzMap

/-- If the `j`-th iterated derivative of a Schwartz map `g` vanishes on `B(0, R)`, then
the `(k, j)`-Schwartz seminorm is bounded by the `(k + 1, j)`-seminorm divided by `R`. -/
lemma SchwartzMap.seminorm_le_div_of_vanish
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
    (g : SchwartzMap E F) (k j : ℕ) (R : ℝ) (hR : 0 < R)
    (hvanish : ∀ x : E, ‖x‖ < R → iteratedFDeriv ℝ j (⇑g) x = 0) :
    (SchwartzMap.seminorm 𝕜 k j) g ≤ (SchwartzMap.seminorm 𝕜 (k + 1) j) g / R := by
  rw [div_eq_inv_mul]
  apply SchwartzMap.seminorm_le_bound 𝕜 k j g (by positivity)
  intro x
  by_cases hx : ‖x‖ < R
  · rw [hvanish x hx, norm_zero, mul_zero]; positivity
  · push Not at hx
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ j (⇑g) x‖
        = R⁻¹ * (R * ‖x‖ ^ k) * ‖iteratedFDeriv ℝ j (⇑g) x‖ := by
          rw [inv_mul_cancel_left₀ (ne_of_gt hR)]
      _ ≤ R⁻¹ * (‖x‖ * ‖x‖ ^ k) * ‖iteratedFDeriv ℝ j (⇑g) x‖ := by
          gcongr
      _ = R⁻¹ * (‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ j (⇑g) x‖) := by
          rw [pow_succ]; ring
      _ ≤ R⁻¹ * (SchwartzMap.seminorm 𝕜 (k + 1) j) g := by
          gcongr; exact SchwartzMap.le_seminorm 𝕜 (k + 1) j g x


/-- Iterated Fréchet derivatives of a `ContDiffBump` on `E` admit a uniform bound `C`
depending only on the order `n` and the ratio `rOut/rIn`. -/
theorem ContDiffBump.norm_iteratedFDeriv_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] [FiniteDimensional ℝ E]
    (n : ℕ) (R_bound : ℝ) (hR : 1 < R_bound) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ContDiffBump (0 : E)),
      f.rOut / f.rIn ≤ R_bound → ∀ (N : ℕ), N ≤ n → ∀ (x : E),
        ‖iteratedFDeriv ℝ N (⇑f) x‖ ≤ C := by sorry

/-- The iterated Fréchet derivatives of the bumps `bumpSeq m` are uniformly bounded
in both `m` and the order `N ≤ n` by a constant `C`. -/
theorem SchwartzMap.bumpSeq_iteratedFDeriv_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] [FiniteDimensional ℝ E]
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (N : ℕ), N ≤ n → ∀ (x : E),
      ‖iteratedFDeriv ℝ N (fun y => (SchwartzMap.bumpSeq (E := E) m y : ℝ)) x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := ContDiffBump.norm_iteratedFDeriv_le (E := E) n 2 one_lt_two
  refine ⟨C, hC, fun m N hN x => hbound (SchwartzMap.bumpSeq m) ?_ N hN x⟩
  show (SchwartzMap.bumpSeq (E := E) m).rOut / (SchwartzMap.bumpSeq (E := E) m).rIn ≤ 2
  simp only [SchwartzMap.bumpSeq_rOut, SchwartzMap.bumpSeq_rIn]
  have hpos : (0 : ℝ) < (↑m : ℝ) + 1 := by positivity
  rw [div_le_iff₀ hpos]
  nlinarith

/-- The Schwartz seminorm of `χ_m f` is bounded uniformly in `m` by a constant
depending only on seminorms of `f`, via the Leibniz rule and the previous bump bound. -/
theorem SchwartzMap.seminorm_bumpCutoffMul_le_of_seminorm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]
    (f : SchwartzMap E F) (k j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ,
      (SchwartzMap.seminorm 𝕜 k j) (SchwartzMap.bumpCutoffMul m f) ≤ C := by
  obtain ⟨B, hB, hBd⟩ := SchwartzMap.bumpSeq_iteratedFDeriv_le (E := E) j
  refine ⟨∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * B * (SchwartzMap.seminorm 𝕜 k (j - i)) f, ?_, fun m => ?_⟩
  · apply Finset.sum_nonneg; intro i _; positivity
  · apply SchwartzMap.seminorm_le_bound 𝕜 k j _ (by
      apply Finset.sum_nonneg; intro i _; positivity)
    intro x
    have hfun_eq : ⇑(SchwartzMap.bumpCutoffMul m f) =
        fun y => (SchwartzMap.bumpSeq (E := E) m y) • f y := by
      ext y; exact SchwartzMap.bumpCutoffMul_apply m f y
    rw [hfun_eq]
    have hleib := ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear_of_le_one
      (@ContinuousLinearMap.lsmul ℝ F _ _ _ ℝ _ _ _ _ _)
      ((SchwartzMap.bumpSeq m).contDiff) (f.smooth') x (n := j) (by exact_mod_cast le_top)
      ContinuousLinearMap.opNorm_lsmul_le
    calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ j (fun y => (SchwartzMap.bumpSeq (E := E) m y : ℝ) • f y) x‖
        ≤ ‖x‖ ^ k * (∑ i ∈ Finset.range (j + 1), ↑(j.choose i) *
            ‖iteratedFDeriv ℝ i (fun y => (SchwartzMap.bumpSeq (E := E) m y : ℝ)) x‖ *
            ‖iteratedFDeriv ℝ (j - i) (⇑f) x‖) := by
          gcongr
          exact hleib
      _ = ∑ i ∈ Finset.range (j + 1), ↑(j.choose i) *
            ‖iteratedFDeriv ℝ i (fun y => (SchwartzMap.bumpSeq (E := E) m y : ℝ)) x‖ *
            (‖x‖ ^ k * ‖iteratedFDeriv ℝ (j - i) (⇑f) x‖) := by
          rw [Finset.mul_sum]; congr 1; ext i; ring
      _ ≤ ∑ i ∈ Finset.range (j + 1), ↑(j.choose i) * B *
            (SchwartzMap.seminorm 𝕜 k (j - i)) f := by
          apply Finset.sum_le_sum; intro i hi
          gcongr
          · exact hBd m i (Finset.mem_range_succ_iff.mp hi) x
          · exact SchwartzMap.le_seminorm 𝕜 k (j - i) f x


/-- Quantitative cutoff convergence: there exists a constant `C` such that
`‖f - χ_m f‖_{k,j} ≤ C / (m + 1)` for all `m`, expressing the geometric rate at
which `χ_m f → f` in the Schwartz topology. -/
theorem SchwartzMap.bumpCutoffMul_seminorm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [HasContDiffBump E] [FiniteDimensional ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 F]
    [SMulCommClass ℝ 𝕜 F]
    (f : SchwartzMap E F) (k j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ,
      (SchwartzMap.seminorm 𝕜 k j) (f - SchwartzMap.bumpCutoffMul m f) ≤ C / (↑m + 1) := by

  obtain ⟨B, hB, hBm⟩ := SchwartzMap.seminorm_bumpCutoffMul_le_of_seminorm 𝕜 f (k + 1) j

  refine ⟨(SchwartzMap.seminorm 𝕜 (k + 1) j) f + B, by positivity, fun m => ?_⟩

  have hstep : (SchwartzMap.seminorm 𝕜 k j) (f - SchwartzMap.bumpCutoffMul m f) ≤
      (SchwartzMap.seminorm 𝕜 (k + 1) j) (f - SchwartzMap.bumpCutoffMul m f) /
        ((↑m : ℝ) + 1) := by
    apply SchwartzMap.seminorm_le_div_of_vanish 𝕜 _ k j ((↑m : ℝ) + 1) (by positivity)
    intro x hx
    exact SchwartzMap.iteratedFDeriv_sub_bumpCutoffMul_eq_zero m f j hx

  have htri : (SchwartzMap.seminorm 𝕜 (k + 1) j) (f - SchwartzMap.bumpCutoffMul m f) ≤
      (SchwartzMap.seminorm 𝕜 (k + 1) j) f + B := by
    calc (SchwartzMap.seminorm 𝕜 (k + 1) j) (f - SchwartzMap.bumpCutoffMul m f)
        ≤ (SchwartzMap.seminorm 𝕜 (k + 1) j) f +
          (SchwartzMap.seminorm 𝕜 (k + 1) j) (SchwartzMap.bumpCutoffMul m f) :=
          map_sub_le_add _ _ _
      _ ≤ (SchwartzMap.seminorm 𝕜 (k + 1) j) f + B := by gcongr; exact hBm m

  calc (SchwartzMap.seminorm 𝕜 k j) (f - SchwartzMap.bumpCutoffMul m f)
      ≤ (SchwartzMap.seminorm 𝕜 (k + 1) j) (f - SchwartzMap.bumpCutoffMul m f) /
          ((↑m : ℝ) + 1) := hstep
    _ ≤ ((SchwartzMap.seminorm 𝕜 (k + 1) j) f + B) / ((↑m : ℝ) + 1) := by
        exact div_le_div_of_nonneg_right htri (by positivity)

namespace SchwartzMap

/-- Cutoff convergence (Melrose Lemma 8.8): every Schwartz seminorm of `f - χ_m f`
tends to `0` as `m → ∞`, hence `χ_m f → f` in the Schwartz topology. -/
theorem seminorm_cutoff_sub_tendsto (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 F]
    [SMulCommClass ℝ 𝕜 F]
    (f : SchwartzMap E F) (k j : ℕ) :
    Tendsto (fun m => (SchwartzMap.seminorm 𝕜 k j) (f - bumpCutoffMul m f)) atTop (nhds 0) := by
  obtain ⟨C, hC, hCm⟩ := bumpCutoffMul_seminorm_le 𝕜 f k j
  apply squeeze_zero (fun m => apply_nonneg _ _) hCm
  have h1 : Tendsto (fun n : ℕ => (1 : ℝ) / ((↑n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun n : ℕ => C * ((1 : ℝ) / ((↑n : ℝ) + 1))) atTop (nhds 0) := by
    convert h1.const_mul C using 1
    ext; ring
  exact h2.congr (fun n => by ring)

end SchwartzMap
