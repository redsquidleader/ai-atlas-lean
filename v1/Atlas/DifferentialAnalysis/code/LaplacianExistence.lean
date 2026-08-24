/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.HormanderFundamental
import Atlas.DifferentialAnalysis.code.ConvolutionTheorem

open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace DifferentialOperators

variable {n : ℕ}


/-- For `n ≥ 3`, the convolution `E ∗ f` of a tempered fundamental solution of the Laplacian with
a Schwartz function has iterated derivatives of order `m` bounded by `M (1 + ‖x‖)^{2 - n - m}`. -/
theorem laplacian_convolution_iteratedFDeriv_zpow_bound
    {n : ℕ} (hn : 3 ≤ n)
    (E : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hE : IsTemperedFundamentalSolution n laplacianPoly E)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (m : ℕ) :
    ∃ (M : ℝ), 0 < M ∧
      ∀ x : EuclideanSpace ℝ (Fin n),
        ‖iteratedFDeriv ℝ m (temperedConvolution E f) x‖ ≤
          M * (1 + ‖x‖) ^ (2 - (n : ℤ) - (m : ℤ)) := by sorry

/-- For `n ≥ 3`, every iterated derivative of the convolution `E ∗ f` is pointwise bounded by
`C / (1 + ‖x‖)`, since the exponent `2 - n - m ≤ -1`. -/
theorem laplacian_convolution_pointwise_decay_bound
    {n : ℕ} (hn : 3 ≤ n)
    (E : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hE : IsTemperedFundamentalSolution n laplacianPoly E)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (m : ℕ) :
    ∃ (C : ℝ), 0 < C ∧
      ∀ x : EuclideanSpace ℝ (Fin n),
        ‖iteratedFDeriv ℝ m (temperedConvolution E f) x‖ ≤ C / (1 + ‖x‖) := by

  obtain ⟨M, hM, hbdd⟩ := laplacian_convolution_iteratedFDeriv_zpow_bound hn E hE f m

  have hexp : (2 : ℤ) - (n : ℤ) - (m : ℤ) ≤ -1 := by omega
  refine ⟨M, hM, fun x => ?_⟩
  have hbase : (0 : ℝ) < 1 + ‖x‖ := by positivity
  calc ‖iteratedFDeriv ℝ m (temperedConvolution E f) x‖
      ≤ M * (1 + ‖x‖) ^ (2 - (n : ℤ) - (m : ℤ)) := hbdd x
    _ ≤ M * (1 + ‖x‖) ^ (-1 : ℤ) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hM)
        exact zpow_le_zpow_right₀ (by linarith [norm_nonneg x] : (1 : ℝ) ≤ 1 + ‖x‖) hexp
    _ = M / (1 + ‖x‖) := by
        rw [zpow_neg_one]
        ring

/-- For `n ≥ 3`, every iterated derivative of `E ∗ f` vanishes at infinity (tends to zero along
the cocompact filter). -/
theorem laplacian_fundamental_convolution_vanishes_at_infty
    {n : ℕ} (hn : 3 ≤ n)
    (E : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hE : IsTemperedFundamentalSolution n laplacianPoly E)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (m : ℕ) :
    Tendsto (fun x => ‖iteratedFDeriv ℝ m (temperedConvolution E f) x‖)
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := laplacian_convolution_pointwise_decay_bound hn E hE f m
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.hasBasis_cocompact.eventually_iff]
  refine ⟨Metric.closedBall 0 (C / ε), isCompact_closedBall 0 _, fun x hx => ?_⟩
  simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right] at hx
  push_neg at hx
  simp only [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)]
  have hCε : (0 : ℝ) < C / ε := div_pos hC hε
  calc ‖iteratedFDeriv ℝ m (temperedConvolution E f) x‖
      ≤ C / (1 + ‖x‖) := hbound x
    _ < C / (C / ε) := by
        apply div_lt_div_of_pos_left hC hCε
        linarith [norm_nonneg x]
    _ = ε := by field_simp


/-- Exchange identity: pairing the Fourier-side multiplication by `m` against `E ∗ f` agrees with
pairing `φ` against the convolution of `f` with the Fourier multiplier `m · E`. -/
theorem tempered_convolution_fourier_multiplier_exchange
    {n : ℕ}
    (E : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (m : EuclideanSpace ℝ (Fin n) → ℂ)
    (hm : Function.HasTemperateGrowth m) :
    ∫ (x : EuclideanSpace ℝ (Fin n)),
      (FourierTransform.fourier
        ((SchwartzMap.smulLeftCLM ℂ m) (FourierTransformInv.fourierInv φ))) x •
        temperedConvolution E f x =
      ∫ (x : EuclideanSpace ℝ (Fin n)),
        φ x • temperedConvolution (TemperedDistribution.fourierMultiplierCLM ℂ m E) f x := by sorry


/-- Pairing identity used in the Laplacian existence proof: integration of the Fourier-side
symbol against `E ∗ f` reduces to `∫ φ • f` thanks to the fundamental-solution property of `E`. -/
theorem fourier_multiplier_convolution_integral_eq
    {n : ℕ}
    (E : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hE : IsTemperedFundamentalSolution n laplacianPoly E)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∫ (x : EuclideanSpace ℝ (Fin n)),
      (FourierTransform.fourier
        ((SchwartzMap.smulLeftCLM ℂ (polySymbol n laplacianPoly))
          (FourierTransformInv.fourierInv φ))) x •
        temperedConvolution E f x =
      ∫ (x : EuclideanSpace ℝ (Fin n)), φ x • f x := by

  rw [tempered_convolution_fourier_multiplier_exchange E f φ
    (polySymbol n laplacianPoly) (polySymbol_hasTemperateGrowth n laplacianPoly)]


  congr 1; ext x
  simp only [temperedConvolution]
  have h : (TemperedDistribution.fourierMultiplierCLM ℂ (polySymbol n laplacianPoly) E)
      (schwartzTranslateReflect f x) = (TemperedDistribution.delta 0) (schwartzTranslateReflect f x) :=
    congr_fun (congr_arg DFunLike.coe hE) (schwartzTranslateReflect f x)
  rw [h, TemperedDistribution.delta_apply]
  congr 1
  show (schwartzTranslateReflect f x) 0 = f x
  exact show f (x - 0) = f x from by rw [sub_zero]


/-- If `u_td` is the tempered distribution given by integration against `E ∗ f`, then
`Δ u_td = f` as tempered distributions. -/
theorem laplacian_fundamental_convolution_distributional_eq
    {n : ℕ} (hn : 3 ≤ n)
    (E : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hE : IsTemperedFundamentalSolution n laplacianPoly E)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (u_td : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hu_td : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      u_td φ = ∫ x, φ x • (temperedConvolution E f x)) :
    laplacianOp u_td = (f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) := by
  ext φ
  simp only [laplacianOp, constCoeffDiffOp]
  rw [TemperedDistribution.fourierMultiplierCLM_apply_apply]
  rw [hu_td]
  simp only [SchwartzMap.toTemperedDistributionCLM_apply_apply]
  exact fourier_multiplier_convolution_integral_eq E hE f φ


set_option maxHeartbeats 800000 in
/-- A smooth function `g` of polynomial growth defines a tempered distribution via integration:
there is a continuous linear functional on Schwartz space whose value at `φ` is `∫ φ • g`. -/
theorem tempered_distribution_of_polynomial_growth
    {n : ℕ}
    (g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgrowth : ∃ (C : ℝ) (k : ℕ), 0 < C ∧
      ∀ x : EuclideanSpace ℝ (Fin n),
        ‖g x‖ ≤ C * (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2)) :
    ∃ u_td : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ),
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        u_td φ = ∫ x, φ x • g x := by
  obtain ⟨Cg, k, hCg, hgrowth⟩ := hgrowth

  obtain ⟨P, hP⟩ := (Measure.HasTemperateGrowth.exists_integrable :
    ∃ P : ℕ, Integrable (fun x : EuclideanSpace ℝ (Fin n) =>
      (1 + ‖x‖) ^ (-(P : ℝ))) volume)
  set m : ℕ × ℕ := (k + P, 0)

  let S (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :=
    (Finset.Iic m).sup (fun p => SchwartzMap.seminorm ℂ p.1 p.2) φ

  have hg_rpow : ∀ x : EuclideanSpace ℝ (Fin n),
      ‖g x‖ ≤ Cg * (1 + ‖x‖) ^ (k : ℝ) := by
    intro x
    have key : (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) ≤ (1 + ‖x‖) ^ (k : ℝ) := by
      have h1 : (0 : ℝ) ≤ 1 + ‖x‖ ^ 2 := by positivity
      have h2 : 1 + ‖x‖ ^ 2 ≤ (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
      have h3 : (0 : ℝ) ≤ (k : ℝ) / 2 := by positivity
      calc (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2)
          ≤ ((1 + ‖x‖) ^ 2) ^ ((k : ℝ) / 2) := Real.rpow_le_rpow h1 h2 h3
        _ = (1 + ‖x‖) ^ (k : ℝ) := by
            rw [← Real.rpow_natCast (1 + ‖x‖) 2, ← Real.rpow_mul (by positivity)]
            congr 1; push_cast; ring
    exact (hgrowth x).trans (mul_le_mul_of_nonneg_left key (le_of_lt hCg))

  have hphi_bound : ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
      (x : EuclideanSpace ℝ (Fin n)),
      ‖φ x‖ ≤ (1 + ‖x‖) ^ (-(↑(k + P) : ℝ)) * (2 ^ (k + P) * S φ) := by
    intro φ x
    rw [Real.rpow_neg (by positivity : (0:ℝ) ≤ 1 + ‖x‖), Real.rpow_natCast,
        ← div_eq_inv_mul, le_div_iff₀' (by positivity : (0:ℝ) < (1 + ‖x‖) ^ (k+P))]
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := m) (k := k + P) (n := 0)
      le_rfl le_rfl φ x
    simpa [norm_iteratedFDeriv_zero] using h

  have hcombined : ∀ (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
      (x : EuclideanSpace ℝ (Fin n)),
      ‖φ x • g x‖ ≤ (Cg * 2 ^ (k + P) * S φ) * (1 + ‖x‖) ^ (-(P : ℝ)) := by
    intro φ x
    rw [norm_smul]
    have hbase : (0 : ℝ) < 1 + ‖x‖ := by positivity
    have hrpow_eq : (1 + ‖x‖) ^ (-(↑(k + P) : ℝ)) * (1 + ‖x‖) ^ (k : ℝ) =
        (1 + ‖x‖) ^ (-(P : ℝ)) := by
      rw [← Real.rpow_add hbase]; congr 1; push_cast; ring
    calc ‖φ x‖ * ‖g x‖
        ≤ ((1 + ‖x‖) ^ (-(↑(k + P) : ℝ)) * (2 ^ (k + P) * S φ)) *
          (Cg * (1 + ‖x‖) ^ (k : ℝ)) := by
          gcongr; exact hphi_bound φ x; exact hg_rpow x
      _ = (Cg * 2 ^ (k + P) * S φ) * (1 + ‖x‖) ^ (-(P : ℝ)) := by
          linear_combination (Cg * 2 ^ (k + P) * S φ) * hrpow_eq

  have hint : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      Integrable (fun x => φ x • g x) volume := by
    intro φ
    apply (hP.const_mul _).mono
      (φ.continuous.smul hsmooth.continuous).aestronglyMeasurable
    apply ae_of_all; intro x
    exact (hcombined φ x).trans (le_abs_self _)

  refine ⟨SchwartzMap.mkCLMtoNormedSpace (fun φ => ∫ x, φ x • g x) ?_ ?_ ?_, fun φ => rfl⟩

  · intro f f'
    simp only [SchwartzMap.add_apply, add_smul]
    exact integral_add (hint f) (hint f')

  · intro a f
    simp only [SchwartzMap.smul_apply, smul_assoc, RingHom.id_apply]
    exact integral_smul a _

  · refine ⟨Finset.Iic m, Cg * 2 ^ (k + P) *
      ∫ x : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) ^ (-(P : ℝ)),
      by positivity, fun f => ?_⟩
    have hSf : S f = (Finset.Iic m).sup (schwartzSeminormFamily ℂ _ ℂ) f := rfl
    calc ‖∫ x, f x • g x‖
        ≤ ∫ x, ‖f x • g x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x : EuclideanSpace ℝ (Fin n),
            (Cg * 2 ^ (k + P) * S f) * (1 + ‖x‖) ^ (-(P : ℝ)) := by
          apply integral_mono_of_nonneg
            (ae_of_all _ (fun x => norm_nonneg _))
            (hP.const_mul _)
            (ae_of_all _ (fun x => hcombined f x))
      _ = (Cg * 2 ^ (k + P) *
            ∫ x : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) ^ (-(P : ℝ))) * S f := by
          rw [integral_const_mul]; ring
      _ = (Cg * 2 ^ (k + P) *
            ∫ x : EuclideanSpace ℝ (Fin n), (1 + ‖x‖) ^ (-(P : ℝ))) *
            (Finset.Iic m).sup (schwartzSeminormFamily ℂ _ ℂ) f := by
          rw [hSf]

/-- Convolving a tempered fundamental solution of the Laplacian with a Schwartz datum `f`
produces a smooth solution `u` vanishing at infinity together with all its derivatives, together
with the corresponding tempered distribution `u_td` satisfying `Δ u_td = f`. -/
theorem fundamental_solution_convolution_gives_C0infty_solution
    {n : ℕ} (hn : 3 ≤ n)
    (E : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hE : IsTemperedFundamentalSolution n laplacianPoly E)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∃ (u : SmoothZeroAtInfty n)
      (u_td : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)),
      (∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        u_td φ = ∫ x, φ x • u x) ∧
      laplacianOp u_td = (f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) := by

  set g := temperedConvolution E f

  have hg_smooth : ContDiff ℝ (⊤ : ℕ∞) g := hormander_convolution_smooth E f

  have hg_vanish : ∀ m : ℕ, Tendsto (fun x => ‖iteratedFDeriv ℝ m g x‖)
      (cocompact (EuclideanSpace ℝ (Fin n))) (𝓝 0) :=
    fun m => laplacian_fundamental_convolution_vanishes_at_infty hn E hE f m

  let u : SmoothZeroAtInfty n := ⟨g, hg_smooth, hg_vanish⟩

  have hg_growth := hormander_convolution_polynomial_growth E f
  obtain ⟨u_td, hu_td⟩ := tempered_distribution_of_polynomial_growth g hg_smooth hg_growth

  have hlap := laplacian_fundamental_convolution_distributional_eq hn E hE f u_td hu_td

  exact ⟨u, u_td, hu_td, hlap⟩

/-- Melrose Theorem 11.17 (Laplacian existence): for `n ≥ 3` and a Schwartz datum `f` on `ℝⁿ`,
the equation `Δ u = f` admits a smooth solution vanishing at infinity (with all derivatives),
and any two such solutions agree. -/
theorem laplacian_schwartz_existence_C0infty
    {n : ℕ} (hn : 3 ≤ n) (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    (∃ (u : SmoothZeroAtInfty n)
      (u_td : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)),
      (∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        u_td φ = ∫ x, φ x • u x) ∧
      laplacianOp u_td = (f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))) ∧
    (∀ (u₁ u₂ : SmoothZeroAtInfty n)
      (u_td₁ u_td₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)),
      (∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), u_td₁ φ = ∫ x, φ x • u₁ x) →
      laplacianOp u_td₁ = (f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) →
      (∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), u_td₂ φ = ∫ x, φ x • u₂ x) →
      laplacianOp u_td₂ = (f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) →
      u₁ = u₂) := by
  have hP : laplacianPoly (n := n) ≠ 0 := laplacianPoly_ne_zero (by omega : 1 ≤ n)
  obtain ⟨E, hE⟩ := constCoeffDiffOp_has_tempered_fundamental_solution n laplacianPoly hP
  exact ⟨fundamental_solution_convolution_gives_C0infty_solution hn E hE f,
         laplacian_schwartz_uniqueness_C0infty hn f⟩

end DifferentialOperators
