/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.WavefrontSet
import Atlas.DifferentialAnalysis.code.HormanderFundamental
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

noncomputable section

open scoped SchwartzMap
open MeasureTheory Set

namespace ConeSupport

variable {n : ℕ}


/-- For a continuous linear functional on `E n = EuclideanSpace ℝ (Fin n)`, the operator norm
is bounded by the sum of the absolute values on the standard basis vectors. -/
lemma clm_norm_le_sum_basis (L : E n →L[ℝ] ℂ) :
    ‖L‖ ≤ ∑ i : Fin n, ‖L (EuclideanSpace.single i 1)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  have hv_decomp : v = ∑ i : Fin n, (v i : ℝ) • EuclideanSpace.single i (1 : ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv_decomp]
  calc ‖L (∑ i, (v i : ℝ) • EuclideanSpace.single i 1)‖
      = ‖∑ i, (v i : ℝ) • L (EuclideanSpace.single i 1)‖ := by
        simp [map_sum, map_smul]
    _ ≤ ∑ i, ‖(v i : ℝ) • L (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
    _ = ∑ i, ‖v i‖ * ‖L (EuclideanSpace.single i 1)‖ := by simp
    _ ≤ ∑ i, ‖v‖ * ‖L (EuclideanSpace.single i 1)‖ := by
        gcongr with i _; exact PiLp.norm_apply_le v i
    _ = (∑ i : Fin n, ‖L (EuclideanSpace.single i 1)‖) * ‖v‖ := by
        simp_rw [mul_comm ‖v‖ _]; rw [← Finset.sum_mul]


/-- The norm of the iterated derivative of `fderiv f` at `x` is bounded by the sum over the
standard basis directions `eᵢ` of the iterated-derivative norms of the directional derivative
`y ↦ ⟨df y, eᵢ⟩`. -/
theorem norm_iteratedFDeriv_fderiv_le_sum
    {m : ℕ} (f : E n → ℂ) (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (x : E n) :
    ‖iteratedFDeriv ℝ m (fderiv ℝ f) x‖ ≤
      ∑ i : Fin n, ‖iteratedFDeriv ℝ m
        (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x‖ := by
  have hfderiv_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) :=
    hf.fderiv_right (by simp)
  have hcomp : ∀ i : Fin n,
      (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) =
      (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i (1 : ℝ))) ∘ (fderiv ℝ f) := by
    intro i; ext y; simp [ContinuousLinearMap.apply_apply]
  have hcomp2 : ∀ i : Fin n,
    iteratedFDeriv ℝ m (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x =
    (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i (1 : ℝ))).compContinuousMultilinearMap
      (iteratedFDeriv ℝ m (fderiv ℝ f) x) := by
    intro i
    rw [hcomp i]
    exact ContinuousLinearMap.iteratedFDeriv_comp_left _
      hfderiv_smooth.contDiffAt (WithTop.coe_le_coe.mpr le_top)
  set M := iteratedFDeriv ℝ m (fderiv ℝ f) x
  apply (ContinuousMultilinearMap.opNorm_le_iff (by positivity)).mpr
  intro v
  calc ‖M v‖
      ≤ ∑ i : Fin n, ‖M v (EuclideanSpace.single i 1)‖ :=
        clm_norm_le_sum_basis (M v)
    _ = ∑ i : Fin n, ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x v‖ := by
        congr 1; ext i; rw [hcomp2]; rfl
    _ ≤ ∑ i : Fin n, ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x‖ * ∏ j, ‖v j‖ := by
        gcongr with i _
        exact (iteratedFDeriv ℝ m (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x).le_opNorm v
    _ = (∑ i : Fin n, ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x‖) * ∏ j, ‖v j‖ := by
        rw [Finset.sum_mul]

set_option maxHeartbeats 800000 in
/-- All iterated derivatives of `u ∗ φ` for a tempered distribution `u` and Schwartz `φ` have
polynomial growth: there exist `k` and `C` so that `‖∂^m(u ∗ φ)(x)‖ ≤ C (1 + ‖x‖)^k`. -/
theorem temperedConvolution_iteratedFDeriv_polynomial_growth
    (u : TemperedDistribution (E n) ℂ)
    (φ : 𝓢(E n, ℂ))
    (m : ℕ) :
    ∃ (k : ℕ) (C : ℝ), ∀ x : E n,
      ‖iteratedFDeriv ℝ m (DifferentialOperators.temperedConvolution u φ) x‖ ≤
        C * (1 + ‖x‖) ^ k := by
  revert φ
  induction m with
  | zero =>
    intro φ
    obtain ⟨C, k, hC_pos, hbound⟩ :=
      DifferentialOperators.hormander_convolution_polynomial_growth u φ
    refine ⟨2 * k, C, fun x => ?_⟩
    simp only [iteratedFDeriv_zero_eq_comp]
    have h1 : (0 : ℝ) ≤ 1 + ‖x‖ := by positivity
    have h1' : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have h2 : (1 : ℝ) + ‖x‖ ^ 2 ≤ (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
    have h3 : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
    have rpow_bound : (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) ≤ (1 + ‖x‖) ^ (2 * k) := by
      calc (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2)
          ≤ ((1 + ‖x‖) ^ 2) ^ ((k : ℝ) / 2) :=
            Real.rpow_le_rpow h3.le h2 (by positivity)
        _ = (1 + ‖x‖) ^ ((↑(2 : ℕ) : ℝ) * ((k : ℝ) / 2)) := by
            rw [← Real.rpow_natCast (1 + ‖x‖) 2, ← Real.rpow_mul h1]
        _ = (1 + ‖x‖) ^ (↑k : ℝ) := by congr 1; push_cast; ring
        _ = (1 + ‖x‖) ^ (k : ℕ) := Real.rpow_natCast _ _
        _ ≤ (1 + ‖x‖) ^ (2 * k) := pow_le_pow_right₀ h1' (by omega)
    calc ‖(continuousMultilinearCurryFin0 ℝ (E n) ℂ).symm
            (DifferentialOperators.temperedConvolution u φ x)‖
        = ‖DifferentialOperators.temperedConvolution u φ x‖ :=
          LinearIsometryEquiv.norm_map _ _
      _ ≤ C * (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) := hbound x
      _ ≤ C * (1 + ‖x‖) ^ (2 * k) := by linarith [mul_le_mul_of_nonneg_left rpow_bound hC_pos.le]
  | succ m ih =>
    intro φ
    have hsmooth := DifferentialOperators.hormander_convolution_smooth u φ

    have hderiv : ∀ i : Fin n, ∃ (k : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ x : E n,
        ‖iteratedFDeriv ℝ m (fun y =>
          fderiv ℝ (DifferentialOperators.temperedConvolution u φ) y
            (EuclideanSpace.single i 1)) x‖ ≤ C * (1 + ‖x‖) ^ k := by
      intro i

      set ei : E n := EuclideanSpace.single i 1
      have hcomp : (fun y => fderiv ℝ (DifferentialOperators.temperedConvolution u φ) y ei) =
          DifferentialOperators.temperedConvolution u (LineDeriv.lineDerivOp ei φ) := by
        ext y
        rw [← (hsmooth.differentiable (by simp [WithTop.coe_ne_zero]) y).lineDeriv_eq_fderiv]
        exact DifferentialOperators.hormander_convolution_deriv_right u φ ei y

      rw [hcomp]
      obtain ⟨k, C, hC⟩ := ih (LineDeriv.lineDerivOp ei φ)
      exact ⟨k, max C 0, le_max_right _ _, fun x =>
        (hC x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))⟩
    choose ks Cs hCs_nn hCs_bound using hderiv
    set K := Finset.univ.sup ks
    have hunif : ∀ (i : Fin n) (x : E n),
        ‖iteratedFDeriv ℝ m (fun y =>
          fderiv ℝ (DifferentialOperators.temperedConvolution u φ) y
            (EuclideanSpace.single i 1)) x‖ ≤ Cs i * (1 + ‖x‖) ^ K := by
      intro i x
      calc _ ≤ Cs i * (1 + ‖x‖) ^ ks i := hCs_bound i x
        _ ≤ Cs i * (1 + ‖x‖) ^ K := by
            apply mul_le_mul_of_nonneg_left _ (hCs_nn i)
            exact pow_le_pow_right₀ (by linarith [norm_nonneg x])
              (Finset.le_sup (f := ks) (Finset.mem_univ i))
    refine ⟨K, (∑ i : Fin n, Cs i) + 1, fun x => ?_⟩
    rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ)]

    calc ‖iteratedFDeriv ℝ m (fderiv ℝ (DifferentialOperators.temperedConvolution u φ)) x‖
        ≤ ∑ i : Fin n, ‖iteratedFDeriv ℝ m (fun y =>
            fderiv ℝ (DifferentialOperators.temperedConvolution u φ) y
              (EuclideanSpace.single i 1)) x‖ :=
          norm_iteratedFDeriv_fderiv_le_sum _ hsmooth x
      _ ≤ ∑ i : Fin n, Cs i * (1 + ‖x‖) ^ K :=
          Finset.sum_le_sum (fun i _ => hunif i x)
      _ = (∑ i : Fin n, Cs i) * (1 + ‖x‖) ^ K := by rw [Finset.sum_mul]
      _ ≤ ((∑ i : Fin n, Cs i) + 1) * (1 + ‖x‖) ^ K := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith


/-- Pairing identity: testing the Schwartz convolution `u ∗ φ` against a Schwartz function `θ`
equals the integral of `θ` against the pointwise tempered convolution. -/
theorem schwartzConvolution_eq_integral
    (u : TemperedDistribution (E n) ℂ)
    (φ : 𝓢(E n, ℂ))
    (θ : 𝓢(E n, ℂ)) :
    (schwartzConvolution u φ) θ =
      ∫ x, θ x • DifferentialOperators.temperedConvolution u φ x := by sorry

/-- The Schwartz convolution `u ∗ φ` is represented as integration against a smooth function `g`
of polynomial (temperate) growth. -/
theorem schwartzConvolution_eq_temperateGrowth
    (u : TemperedDistribution (E n) ℂ)
    (φ : 𝓢(E n, ℂ)) :
    ∃ (g : E n → ℂ),
      Function.HasTemperateGrowth g ∧
      ∀ (θ : 𝓢(E n, ℂ)),
        (schwartzConvolution u φ) θ = ∫ x, θ x • g x := by
  refine ⟨DifferentialOperators.temperedConvolution u φ, ⟨?_, ?_⟩, ?_⟩
  · exact DifferentialOperators.hormander_convolution_smooth u φ
  · exact temperedConvolution_iteratedFDeriv_polynomial_growth u φ
  · exact schwartzConvolution_eq_integral u φ

/-- For any smooth compactly supported cutoff `ψ`, the product `ψ · (u ∗ φ)` is represented by a
Schwartz function. -/
theorem smulLeftCLM_schwartzConvolution_eq_schwartz
    (u : TemperedDistribution (E n) ℂ)
    (φ : 𝓢(E n, ℂ))
    (ψ : E n → ℂ)
    (hψ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ) :
    ∃ (f : SchwartzMap (E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ ψ (schwartzConvolution u φ) =
        (f : 𝓢'(E n, ℂ)) := by


  obtain ⟨g, hg_tempered, hg_eq⟩ := schwartzConvolution_eq_temperateGrowth u φ

  have hψg_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ψ x * g x) :=
    hψ_smooth.mul hg_tempered.1
  have hψg_compact : HasCompactSupport (fun x => ψ x * g x) :=
    hψ_compact.mul_right
  let f : 𝓢(E n, ℂ) := hψg_compact.toSchwartzMap hψg_smooth

  use f
  ext θ


  simp only [TemperedDistribution.smulLeftCLM_apply_apply]


  rw [hg_eq]

  rw [SchwartzMap.coe_apply]


  congr 1
  ext x


  by_cases hψ_tg : Function.HasTemperateGrowth ψ
  · simp only [SchwartzMap.smulLeftCLM_apply_apply hψ_tg]
    simp only [smul_eq_mul, f, HasCompactSupport.toSchwartzMap_toFun]
    ring
  ·
    have : SchwartzMap.smulLeftCLM ℂ ψ = (0 : 𝓢(E n, ℂ) →L[ℂ] 𝓢(E n, ℂ)) := by
      unfold SchwartzMap.smulLeftCLM
      exact dif_neg hψ_tg

    exfalso
    exact hψ_tg (hψ_compact.hasTemperateGrowth hψ_smooth)

/-- The Schwartz convolution `u ∗ φ` is smooth near every point: a cutoff times it agrees with a
Schwartz function on a neighbourhood of any point. -/
theorem isSmoothNear_schwartzConvolution
    (u : TemperedDistribution (E n) ℂ)
    (φ : 𝓢(E n, ℂ))
    (x₀ : E n) :
    IsSmoothNear (schwartzConvolution u φ) x₀ := by


  have hx_nhds : (Set.univ : Set (E n)) ∈ nhds x₀ := Filter.univ_mem
  obtain ⟨ψ₀, -, hψ₀_compact, hψ₀_smooth, -, hψ₀_x⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) hx_nhds

  let ψ : E n → ℂ := Complex.ofRealCLM ∘ ψ₀
  have hψ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ :=
    Complex.ofRealCLM.contDiff.comp hψ₀_smooth
  have hψ_compact : HasCompactSupport ψ := hψ₀_compact.comp_left (map_zero _)
  have hψ_x : ψ x₀ ≠ 0 := by
    simp only [ψ, Function.comp, Complex.ofRealCLM_apply, Complex.ofReal_ne_zero, hψ₀_x]
    exact one_ne_zero

  obtain ⟨f, hf⟩ := smulLeftCLM_schwartzConvolution_eq_schwartz u φ ψ hψ_smooth hψ_compact
  exact ⟨ψ, hψ_smooth, hψ_compact, hψ_x, f, hf⟩

/-- The singular support of `u ∗ φ` is empty: the convolution is smooth everywhere. -/
theorem singularSupport_schwartzConvolution_eq_empty
    (u : TemperedDistribution (E n) ℂ)
    (φ : 𝓢(E n, ℂ)) :
    singularSupport (schwartzConvolution u φ) = ∅ := by
  ext x₀
  simp only [singularSupport, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
  exact isSmoothNear_schwartzConvolution u φ x₀

/-- The cone singular support of `u ∗ φ` is contained in the spherical (direction-at-infinity)
part inherited from the conic singular support sphere of `u`. -/
theorem coneSingularSupport_schwartzConvolution_subset
    (u : TemperedDistribution (E n) ℂ)
    (φ : 𝓢(E n, ℂ)) :
    coneSingularSupport (schwartzConvolution u φ) ⊆
      Sum.inr '' ConicSingularSupportSphere u := by
  intro p hp
  simp only [coneSingularSupport, mem_union, mem_image] at hp
  rcases hp with ⟨x, hx, rfl⟩ | ⟨ω, hω, rfl⟩
  ·

    simp [singularSupport_schwartzConvolution_eq_empty u φ] at hx
  ·

    exact ⟨ω, css_schwartz_convolution u φ hω, rfl⟩

end ConeSupport

end
