/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Atlas.DifferentialAnalysis.code.DifferentialOperators
import Atlas.DifferentialAnalysis.code.LaplacianExistence

noncomputable section

open scoped SchwartzMap
open Filter Topology MeasureTheory

namespace PoissonEquation

variable (n : ℕ)

/-- A smooth `ℂ`-valued function on `ℝⁿ` whose iterated derivatives of every order decay to zero at infinity (i.e. tend to `0` along the cocompact filter). -/
structure SmoothZeroAtInfty where
  toFun : EuclideanSpace ℝ (Fin n) → ℂ
  smooth' : ContDiff ℝ (⊤ : ℕ∞) toFun
  zero_at_infty' : ∀ m : ℕ,
    Tendsto (fun x => ‖iteratedFDeriv ℝ m toFun x‖) (cocompact _) (𝓝 0)

namespace SmoothZeroAtInfty

variable {n}

/-- Treat `SmoothZeroAtInfty n` as a `FunLike` so that an element can be applied like a function. -/
instance : FunLike (SmoothZeroAtInfty n) (EuclideanSpace ℝ (Fin n)) ℂ where
  coe := SmoothZeroAtInfty.toFun
  coe_injective' f g h := by cases f; cases g; congr

/-- Pointwise extensionality for `SmoothZeroAtInfty`. -/
@[ext]
theorem ext {f g : SmoothZeroAtInfty n} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.coe_injective (funext h)

/-- An element of `SmoothZeroAtInfty n` is `C^∞` smooth. -/
theorem smooth (f : SmoothZeroAtInfty n) : ContDiff ℝ (⊤ : ℕ∞) (⇑f) := f.smooth'

/-- The `m`-th iterated derivative norm of `f : SmoothZeroAtInfty n` tends to `0` at infinity. -/
theorem zero_at_infty (f : SmoothZeroAtInfty n) (m : ℕ) :
    Tendsto (fun x => ‖iteratedFDeriv ℝ m (⇑f) x‖) (cocompact _) (𝓝 0) :=
  f.zero_at_infty' m

end SmoothZeroAtInfty

/-- `IsLaplacianOf n f g` says that `g = -Δ f` pointwise, where `Δ` is the standard Laplacian on `ℝⁿ` defined via the iterated Fréchet derivative. -/
def IsLaplacianOf (n : ℕ) (f g : EuclideanSpace ℝ (Fin n) → ℂ) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n),
    g x = -∑ j : Fin n,
      (iteratedFDeriv ℝ 2 f x) (fun _ => EuclideanSpace.single j (1 : ℝ))


/-- Gradient estimate (mean value inequality) for a bounded harmonic function: `‖∇u(a)‖ ≤ n · C / R` for any radius `R > 0`. -/
theorem harmonic_fderiv_norm_le_div
    {n : ℕ} (hn : 1 ≤ n)
    (u : EuclideanSpace ℝ (Fin n) → ℂ)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (hharm : IsLaplacianOf n u 0)
    (C : ℝ) (hC : 0 ≤ C) (hbd : ∀ x, ‖u x‖ ≤ C)
    (R : ℝ) (hR : 0 < R) (a : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ u a‖ ≤ ↑n * C / R := by sorry

/-- Liouville-type derivative vanishing: a bounded harmonic function has zero Fréchet derivative everywhere. -/
theorem bounded_harmonic_fderiv_eq_zero
    {n : ℕ} (hn : 1 ≤ n)
    (u : EuclideanSpace ℝ (Fin n) → ℂ)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (hharm : IsLaplacianOf n u 0)
    (hbd : ∃ C : ℝ, ∀ x, ‖u x‖ ≤ C) :
    ∀ x, fderiv ℝ u x = 0 := by
  obtain ⟨C₀, hC₀⟩ := hbd
  set C := max C₀ 0
  have hC_nn : 0 ≤ C := le_max_right _ _
  have hbd' : ∀ x, ‖u x‖ ≤ C := fun x => (hC₀ x).trans (le_max_left _ _)
  intro x
  rw [← norm_le_zero_iff]
  by_contra h_pos
  push Not at h_pos
  have ha_pos : 0 < ‖fderiv ℝ u x‖ := h_pos
  set M := ↑n * C
  have hM : 0 ≤ M := by positivity
  rcases eq_or_lt_of_le hM with hM0 | hM_pos
  ·
    have hge := harmonic_fderiv_norm_le_div hn u hsmooth hharm C hC_nn hbd' 1 one_pos x
    have : ↑n * C = 0 := hM0.symm
    simp only [this, zero_div] at hge; linarith
  ·
    have hge := harmonic_fderiv_norm_le_div hn u hsmooth hharm C hC_nn hbd'
      (2 * M / ‖fderiv ℝ u x‖) (by positivity) x
    have : M / (2 * M / ‖fderiv ℝ u x‖) = ‖fderiv ℝ u x‖ / 2 := by field_simp
    rw [this] at hge; linarith

/-- Liouville's theorem: a bounded harmonic function on `ℝⁿ` is constant. -/
theorem bounded_harmonic_is_constant
    {n : ℕ} (hn : 1 ≤ n)
    (u : EuclideanSpace ℝ (Fin n) → ℂ)
    (hsmooth : ContDiff ℝ (⊤ : ℕ∞) u)
    (hharm : IsLaplacianOf n u 0)
    (hbd : ∃ C : ℝ, ∀ x, ‖u x‖ ≤ C) :
    ∃ c : ℂ, u = Function.const _ c := by
  have hfderiv := bounded_harmonic_fderiv_eq_zero hn u hsmooth hharm hbd
  refine ⟨u 0, funext fun x => ?_⟩
  simp only [Function.const]
  exact is_const_of_fderiv_eq_zero (hsmooth.differentiable (by simp)) hfderiv x 0


/-- Integration by parts: for a smooth, decaying `u` representing a tempered distribution `u_td`, the distributional Laplacian acts as the pointwise classical Laplacian against test functions. -/
theorem laplacianOp_smooth_eq_classical
    {n : ℕ} (hn : 3 ≤ n)
    (u : SmoothZeroAtInfty n)
    (u_td : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hu_td : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), u_td φ = ∫ x, φ x • u x) :
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (DifferentialOperators.laplacianOp u_td) φ =
        ∫ x, φ x • (-∑ j : Fin n,
          (iteratedFDeriv ℝ 2 (⇑u) x) (fun _ => EuclideanSpace.single j (1 : ℝ))) := by sorry


/-- Schwartz testing determines continuous functions pointwise: if two continuous functions integrate identically against every Schwartz test, they coincide. -/
theorem schwartz_determines_continuous
    {n : ℕ} (hn : 3 ≤ n)
    (u : SmoothZeroAtInfty n)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (h : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (∫ x, φ x • (-∑ j : Fin n,
        (iteratedFDeriv ℝ 2 (⇑u) x) (fun _ => EuclideanSpace.single j (1 : ℝ)))) =
      ∫ x, φ x • f x) :
    ∀ x : EuclideanSpace ℝ (Fin n),
      (f : EuclideanSpace ℝ (Fin n) → ℂ) x =
        -∑ j : Fin n,
          (iteratedFDeriv ℝ 2 (⇑u) x) (fun _ => EuclideanSpace.single j (1 : ℝ)) := by sorry

/-- The distributional Laplacian of `u` agrees with the pointwise Laplacian when both are defined and `u` is smooth and decaying. -/
theorem distributional_laplacian_eq_pointwise
    {n : ℕ} (hn : 3 ≤ n)
    (u : SmoothZeroAtInfty n)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (u_td : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hu_td : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), u_td φ = ∫ x, φ x • u x)
    (hlap : DifferentialOperators.laplacianOp u_td =
      (f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))) :
    IsLaplacianOf n (⇑u) (⇑f) := by


  have h_ibp := laplacianOp_smooth_eq_classical hn u u_td hu_td


  intro x


  have h_dist_eq : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (∫ x, φ x • (-∑ j : Fin n,
        (iteratedFDeriv ℝ 2 (⇑u) x) (fun _ => EuclideanSpace.single j (1 : ℝ)))) =
      ∫ x, φ x • f x := by
    intro φ
    have h1 := h_ibp φ
    have h2 : (DifferentialOperators.laplacianOp u_td) φ =
        (f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) φ := congr_fun (congr_arg _ hlap) φ
    rw [← h1, h2, SchwartzMap.coe_apply]


  exact schwartz_determines_continuous hn u f h_dist_eq x

/-- Existence of a smooth, decaying Laplacian inverse for a Schwartz right-hand side `f` in dimension `n ≥ 3`. -/
theorem fourier_laplacian_inverse_schwartz
    {n : ℕ} (hn : 3 ≤ n)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) g ∧
      (∀ m : ℕ, Tendsto (fun x => ‖iteratedFDeriv ℝ m g x‖) (cocompact _) (𝓝 0)) ∧
      IsLaplacianOf n g (⇑f) := by

  obtain ⟨⟨u_DO, u_td, hu_rep, hu_lap⟩, _⟩ :=
    DifferentialOperators.laplacian_schwartz_existence_C0infty hn f

  let u : SmoothZeroAtInfty n :=
    ⟨u_DO.toFun, u_DO.smooth', u_DO.iteratedFDeriv_zero_at_infty'⟩

  have hu_eq : (⇑u : EuclideanSpace ℝ (Fin n) → ℂ) = ⇑u_DO := rfl

  refine ⟨⇑u, u.smooth, u.zero_at_infty, ?_⟩

  have hu_rep' : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      u_td φ = ∫ x, φ x • u x := by
    intro φ; simp only [hu_rep, hu_eq]
  exact distributional_laplacian_eq_pointwise hn u f u_td hu_rep' hu_lap


/-- Injectivity of the Laplacian on `SmoothZeroAtInfty n`: two decaying solutions of `-Δuᵢ = f` agree. -/
theorem laplacian_injective
    {n : ℕ} (hn : 3 ≤ n)
    (u₁ u₂ : SmoothZeroAtInfty n) (f : EuclideanSpace ℝ (Fin n) → ℂ)
    (h₁ : IsLaplacianOf n (⇑u₁) f) (h₂ : IsLaplacianOf n (⇑u₂) f) :
    u₁ = u₂ := by
  have hn1 : 1 ≤ n := le_trans (by norm_num : 1 ≤ 3) hn
  haveI : Nonempty (Fin n) := ⟨⟨0, hn1⟩⟩
  haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
    refine ⟨⟨0, EuclideanSpace.single (⟨0, hn1⟩ : Fin n) 1, ?_⟩⟩
    simp [EuclideanSpace.single, PiLp.ext_iff]
  haveI : NoncompactSpace (EuclideanSpace ℝ (Fin n)) := inferInstance

  set v : EuclideanSpace ℝ (Fin n) → ℂ := fun x => u₁ x - u₂ x
  have hv_smooth : ContDiff ℝ (⊤ : ℕ∞) v := u₁.smooth.sub u₂.smooth
  have hv_eq : v = ⇑u₁ - ⇑u₂ := rfl

  have hv_norm_tend : Tendsto (fun x => ‖v x‖) (cocompact _) (𝓝 0) := by
    have h1 := u₁.zero_at_infty 0
    have h2 := u₂.zero_at_infty 0
    simp at h1 h2
    exact squeeze_zero (fun x => norm_nonneg _) (fun x => norm_sub_le _ _)
      (by simpa using h1.add h2)

  have hv_harm : IsLaplacianOf n v 0 := by
    intro x; simp only [Pi.zero_apply]
    have hsub2 : iteratedFDeriv ℝ 2 v x =
        iteratedFDeriv ℝ 2 (⇑u₁) x - iteratedFDeriv ℝ 2 (⇑u₂) x := by
      rw [hv_eq]
      exact congr_fun (iteratedFDeriv_sub (u₁.smooth.of_le (WithTop.coe_le_coe.mpr le_top))
        (u₂.smooth.of_le (WithTop.coe_le_coe.mpr le_top)) (i := 2)) x
    simp only [hsub2, ContinuousMultilinearMap.sub_apply, Finset.sum_sub_distrib]
    rw [eq_comm, neg_eq_zero, sub_eq_zero]
    exact neg_inj.mp ((h₁ x).symm.trans (h₂ x))

  have hv_bounded : ∃ C : ℝ, ∀ x, ‖v x‖ ≤ C := by
    have hev : ∀ᶠ x in cocompact _, ‖v x‖ < 1 := hv_norm_tend (Iio_mem_nhds one_pos)
    rw [Filter.hasBasis_cocompact.eventually_iff] at hev
    simp only [Set.mem_compl_iff] at hev
    obtain ⟨K, hK, hKv⟩ := hev
    by_cases hKne : K.Nonempty
    · obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hv_smooth.continuous.continuousOn
      exact ⟨max M 1, fun x => by
        by_cases hxK : x ∈ K
        · exact (hM x hxK).trans (le_max_left M 1)
        · exact (le_of_lt (hKv hxK)).trans (le_max_right M 1)⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hKne
      exact ⟨1, fun x => le_of_lt (hKv (by simp [hKne]))⟩

  obtain ⟨c, hc⟩ := bounded_harmonic_is_constant hn1 v hv_smooth hv_harm hv_bounded

  have hc_zero : c = 0 := by
    have : ∀ x, v x = c := fun x => congr_fun hc x
    simp_rw [this] at hv_norm_tend
    exact norm_eq_zero.mp (tendsto_nhds_unique hv_norm_tend tendsto_const_nhds).symm

  ext x
  have hx := congr_fun hc x
  change u₁ x - u₂ x = c at hx
  rw [hc_zero] at hx
  exact sub_eq_zero.mp hx

end PoissonEquation

end
