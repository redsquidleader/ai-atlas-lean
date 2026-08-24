/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped SchwartzMap

noncomputable section

namespace HadamardDecomposition

variable (n : ℕ)

/-- The `j`-th coordinate function on `EuclideanSpace ℝ (Fin n)`, viewed as a
complex-valued function. -/
def coordFun (j : Fin n) : EuclideanSpace ℝ (Fin n) → ℂ :=
  fun x => (x j : ℂ)

/-- The `j`-th coordinate function on `EuclideanSpace ℝ (Fin n)`, packaged as
a continuous real-linear map into `ℂ`. -/
def coordCLM (j : Fin n) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (EuclideanSpace.proj j)

/-- The plain coordinate function `coordFun n j` agrees pointwise with its
continuous-linear-map version `coordCLM n j`. -/
lemma coordFun_eq_coordCLM (j : Fin n) : coordFun n j = coordCLM n j := by
  ext x; simp [coordFun, coordCLM, EuclideanSpace.proj]

/-- Each coordinate function on Euclidean space has temperate growth (it is
linear, hence at most linearly bounded). -/
lemma coordFun_hasTemperateGrowth (j : Fin n) :
    Function.HasTemperateGrowth (coordFun n j) := by
  rw [coordFun_eq_coordCLM]; exact ContinuousLinearMap.hasTemperateGrowth _

/-- The Hadamard decomposition coefficient functions: given a Schwartz
function `φ` and a coordinate index `j`, this is the function whose value at
`x` is `∫₀¹ (∂_j φ)(t · x) dt`.  These functions appear in the identity
`φ(x) = Σⱼ xⱼ · ψⱼ(x)` when `φ` vanishes at the origin. -/
def hadamardPsiFun (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (j : Fin n)
    (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∫ t in (0:ℝ)..1, fderiv ℝ (⇑φ) ((t : ℝ) • x) (EuclideanSpace.single j 1)


/-- The Hadamard coefficient function `hadamardPsiFun n φ j` is smooth
(`C^∞`). -/
theorem hadamardPsiFun_contDiff
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (j : Fin n) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (hadamardPsiFun n φ j) := by sorry


/-- The Hadamard coefficient function `hadamardPsiFun n φ j` satisfies all
Schwartz decay estimates: for every pair of nonnegative integers `(k, m)`
there is a constant `C` bounding `‖x‖^k · ‖D^m ψ(x)‖`. -/
theorem hadamardPsiFun_decay
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (j : Fin n) :
    ∀ (k m : ℕ), ∃ C, ∀ x : EuclideanSpace ℝ (Fin n),
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (hadamardPsiFun n φ j) x‖ ≤ C := by sorry

/-- Hadamard decomposition: a Schwartz function on `ℝⁿ` that vanishes at the
origin can be written as `φ(x) = Σⱼ xⱼ · ψⱼ(x)` for some Schwartz functions
`ψⱼ`. -/
theorem schwartz_vanishing_at_zero_eq_sum_coord_mul
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (hφ : φ 0 = 0) :
    ∃ ψ : Fin n → 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      ∀ x : EuclideanSpace ℝ (Fin n),
        φ x = ∑ j : Fin n, coordFun n j x • ψ j x := by

  refine ⟨fun j => SchwartzMap.mk (hadamardPsiFun n φ j)
    (hadamardPsiFun_contDiff n φ j) (hadamardPsiFun_decay n φ j), fun x => ?_⟩

  have hFTC : φ x = ∫ t in (0:ℝ)..1, fderiv ℝ (⇑φ) (t • x) x := by
    have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1,
        HasDerivAt (fun s => φ (s • x)) (fderiv ℝ (⇑φ) (t • x) x) t := by
      intro t _
      exact φ.differentiableAt.hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).smul_const x |>.congr_deriv (by simp))
    have hint : IntervalIntegrable (fun t => fderiv ℝ (⇑φ) (t • x) x)
        MeasureTheory.volume 0 1 := by
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.clm_apply
      · exact ((φ.smooth ⊤).continuous_fderiv (by simp)).comp_continuousOn
          (continuousOn_id.smul continuousOn_const)
      · exact continuousOn_const
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
    simp [hφ]

  have hLinear : ∀ (t : ℝ), fderiv ℝ (⇑φ) (t • x) x =
      ∑ j : Fin n, ((x j : ℝ) : ℂ) •
        fderiv ℝ (⇑φ) (t • x) (EuclideanSpace.single j 1) := by
    intro t
    set L := fderiv ℝ (⇑φ) (t • x)
    have hx : x = ∑ j : Fin n, (x j) • EuclideanSpace.single j (1 : ℝ) := by
      ext i; simp only [EuclideanSpace.single, PiLp.single]; simp [Pi.single_apply]
    conv_lhs => rw [hx, map_sum]
    exact Finset.sum_congr rfl fun j _ => by
      rw [show L (x.ofLp j • EuclideanSpace.single j 1) =
        (x.ofLp j : ℝ) • L (EuclideanSpace.single j 1) from L.map_smul _ _,
        Complex.real_smul, smul_eq_mul]
  rw [hFTC]
  simp_rw [hLinear]

  rw [intervalIntegral.integral_finset_sum (fun j _ => by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.smul continuousOn_const
    apply ContinuousOn.clm_apply
    · exact ((φ.smooth ⊤).continuous_fderiv (by simp)).comp_continuousOn
        (continuousOn_id.smul continuousOn_const)
    · exact continuousOn_const)]
  exact Finset.sum_congr rfl fun j _ => by
    rw [intervalIntegral.integral_smul]
    simp only [coordFun]
    congr 1

/-- If a tempered distribution `u` is annihilated by multiplication by every
coordinate function, then `u φ = 0` for every Schwartz function `φ` that
vanishes at the origin.  Proof uses the Hadamard decomposition. -/
theorem apply_eq_zero_of_eval_origin_eq_zero
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hu : ∀ j : Fin n, TemperedDistribution.smulLeftCLM ℂ (coordFun n j) u = 0)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (hφ : φ 0 = 0) :
    u φ = 0 := by
  obtain ⟨ψ, hψ⟩ := schwartz_vanishing_at_zero_eq_sum_coord_mul n φ hφ
  have hφ_eq : φ = ∑ j : Fin n, SchwartzMap.smulLeftCLM ℂ (coordFun n j) (ψ j) := by
    ext x
    rw [hψ x]
    induction (Finset.univ : Finset (Fin n)) using Finset.cons_induction with
    | empty => simp [SchwartzMap.zero_apply]
    | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons, SchwartzMap.add_apply,
        SchwartzMap.smulLeftCLM_apply_apply (coordFun_hasTemperateGrowth n a), ih]
  rw [hφ_eq, map_sum]
  apply Finset.sum_eq_zero
  intro j _
  change (TemperedDistribution.smulLeftCLM ℂ (coordFun n j) u) (ψ j) = 0
  simp [hu j]

/-- Characterisation of multiples of the Dirac delta at the origin: a tempered
distribution `u` is annihilated by multiplication by every coordinate
function iff `u = c · δ₀` for some scalar `c`. -/
theorem eq_smul_delta_of_forall_coordSmul_eq_zero
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hu : ∀ j : Fin n, TemperedDistribution.smulLeftCLM ℂ (coordFun n j) u = 0) :
    ∃ c : ℂ, u = c • TemperedDistribution.delta (0 : EuclideanSpace ℝ (Fin n)) := by
  by_cases h : u = 0
  · exact ⟨0, by simp [h]⟩
  ·
    obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀, u φ₀ ≠ 0 := by
      by_contra h'
      push Not at h'
      exact h (by ext φ; exact h' φ)

    have hφ₀_ne : φ₀ 0 ≠ 0 := by
      intro h_zero
      exact hφ₀ (apply_eq_zero_of_eval_origin_eq_zero n u hu φ₀ h_zero)

    refine ⟨u φ₀ * (φ₀ 0)⁻¹, ?_⟩
    ext φ

    have hvanish : (φ - (φ 0 * (φ₀ 0)⁻¹) • φ₀) 0 = 0 := by
      simp only [SchwartzMap.sub_apply, SchwartzMap.smul_apply, smul_eq_mul]
      field_simp
      ring
    have key := apply_eq_zero_of_eval_origin_eq_zero n u hu
      (φ - (φ 0 * (φ₀ 0)⁻¹) • φ₀) hvanish
    rw [map_sub, map_smul] at key

    have h1 : u φ = (φ 0 * (φ₀ 0)⁻¹) • u φ₀ := by rwa [sub_eq_zero] at key

    rw [h1]
    change (φ 0 * (φ₀ 0)⁻¹) • u φ₀ =
      (u φ₀ * (φ₀ 0)⁻¹) • (TemperedDistribution.delta 0 φ)
    rw [TemperedDistribution.delta_apply, smul_eq_mul, smul_eq_mul]
    ring

end HadamardDecomposition

end
