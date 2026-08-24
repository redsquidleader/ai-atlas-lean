/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
open MeasureTheory Filter

set_option maxHeartbeats 800000

noncomputable section

namespace HeatEquation

/-- The total thermal energy at time $t$ associated to $u(t, x)$, defined by
$\mathcal{T}(t) \stackrel{\text{def}}{=} \int_{\mathbb{R}^n} u(t, x) \, d^n x$.
(Definition 2.0.2.) -/
def totalThermalEnergy (n : ℕ) (u : ℝ → (Fin n → ℝ) → ℝ) (t : ℝ) : ℝ :=
  ∫ x : Fin n → ℝ, u t x

/-- Quantitative form of the divergence theorem: the integral of the Laplacian of $u$ over
a ball of radius $R$ is controlled by an $R^{n-1}$-weighted supremum of the gradient on the
sphere of radius $R$. Used as an abstract hypothesis to derive conservation of thermal energy. -/
theorem divergence_theorem_ball_bound
    {n : ℕ}
    (laplacian_u : ℝ → (Fin n → ℝ) → ℝ)
    (grad_u_norm : ℝ → (Fin n → ℝ) → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t R, 0 < R →
      |∫ x in Metric.ball (0 : Fin n → ℝ) R, laplacian_u t x| ≤
      C * sSup ((fun x => R ^ ((n : ℝ) - 1) * |grad_u_norm t x|) ''
        Metric.sphere (0 : Fin n → ℝ) R) := by sorry

/-- Under the decay assumption $\lim_{|x| \to \infty} |x|^{n-1} |\nabla_x u(t, x)| = 0$
together with integrability of the Laplacian and the divergence-theorem bound, the global
integral of the Laplacian over $\mathbb{R}^n$ vanishes:
$\int_{\mathbb{R}^n} \Delta u(t, x) \, d^n x = 0$. -/
theorem integral_laplacian_eq_zero
    {n : ℕ}
    (laplacian_u : ℝ → (Fin n → ℝ) → ℝ)
    (grad_u_norm : ℝ → (Fin n → ℝ) → ℝ)


    (hdecay : ∀ t, Tendsto
      (fun (R : ℝ) => sSup ((fun x => R ^ ((n : ℝ) - 1) * |grad_u_norm t x|) ''
        (Metric.sphere (0 : Fin n → ℝ) R)))
      atTop (nhds 0))
    (hlapl_int : ∀ t, Integrable (laplacian_u t))


    (hdiv_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ t R, 0 < R →
      |∫ x in Metric.ball (0 : Fin n → ℝ) R, laplacian_u t x| ≤
      C * sSup ((fun x => R ^ ((n : ℝ) - 1) * |grad_u_norm t x|) ''
        Metric.sphere (0 : Fin n → ℝ) R))
    (t : ℝ) :
    ∫ x : Fin n → ℝ, laplacian_u t x = 0 := by
  obtain ⟨C, hC_nn, hbound⟩ := hdiv_bound


  have hcover : AECover (volume : Measure (Fin n → ℝ)) atTop
      (fun R : ℝ => Metric.ball (0 : Fin n → ℝ) R) :=
    MeasureTheory.aecover_ball tendsto_id


  have htend : Tendsto (fun R => ∫ x in Metric.ball (0 : Fin n → ℝ) R, laplacian_u t x)
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simp only [Real.norm_eq_abs]
    apply squeeze_zero'
    · filter_upwards with R; exact abs_nonneg _
    · filter_upwards [Ioi_mem_atTop (0 : ℝ)] with R hR; exact hbound t R hR
    · rw [show (0 : ℝ) = C * 0 from by ring]; exact (hdecay t).const_mul C

  exact hcover.integral_eq_of_tendsto 0 (hlapl_int t) htend

/-- For a solution $u$ to the heat equation $\partial_t u = \Delta u$ on $\mathbb{R}^n$
with suitable decay and integrability hypotheses, the derivative of the total thermal
energy with respect to time vanishes: $\mathcal{T}'(t) = 0$. This is the differential
form of conservation of thermal energy (Lemma 2.0.3). -/
theorem deriv_totalThermalEnergy_eq_zero
    {n : ℕ}
    (u : ℝ → (Fin n → ℝ) → ℝ)

    (u_t : ℝ → (Fin n → ℝ) → ℝ)

    (laplacian_u : ℝ → (Fin n → ℝ) → ℝ)

    (grad_u_norm : ℝ → (Fin n → ℝ) → ℝ)

    (hpde : ∀ t (x : Fin n → ℝ), u_t t x = laplacian_u t x)

    (hderiv : ∀ (x : Fin n → ℝ) (t : ℝ), HasDerivAt (fun s => u s x) (u_t t x) t)


    (hdecay : ∀ t, Tendsto
      (fun (R : ℝ) => sSup ((fun x => R ^ ((n : ℝ) - 1) * |grad_u_norm t x|) ''
        (Metric.sphere (0 : Fin n → ℝ) R)))
      atTop (nhds 0))

    (f : (Fin n → ℝ) → ℝ)
    (_hf_nn : ∀ x, 0 ≤ f x)
    (hf_int : Integrable f)
    (hdom : ∀ t (x : Fin n → ℝ), |u_t t x| ≤ f x)

    (hu_meas : ∀ t, AEStronglyMeasurable (u t) volume)
    (hu_int : ∀ t, Integrable (u t))
    (hut_meas : ∀ t, AEStronglyMeasurable (u_t t) volume)
    (t : ℝ) :
    HasDerivAt (totalThermalEnergy n u) 0 t := by


  have leibniz : HasDerivAt (fun s => ∫ x, u s x) (∫ x, u_t t x) t := by
    exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (s := Set.univ) (F := u) (F' := u_t) (bound := f) (x₀ := t) (μ := volume)
      (by simp [Filter.univ_mem])
      (by filter_upwards with s
          exact hu_meas s)
      (hu_int t)
      (hut_meas t)
      (by filter_upwards with x
          intro s _; rw [Real.norm_eq_abs]; exact hdom s x)
      hf_int
      (by filter_upwards with x
          intro s _; exact hderiv x s)).2

  have heat_eq_integral : ∫ x : Fin n → ℝ, u_t t x = ∫ x : Fin n → ℝ, laplacian_u t x := by
    congr 1; ext x; exact hpde t x

  have hlapl_int : ∀ s, Integrable (laplacian_u s) := by
    intro s
    have heq : laplacian_u s = u_t s := by ext x; exact (hpde s x).symm
    rw [heq]
    exact Integrable.mono hf_int (hut_meas s) (ae_of_all _ (fun x => by
      rw [Real.norm_eq_abs]; exact (hdom s x).trans (le_abs_self _)))


  have div_thm : ∫ x : Fin n → ℝ, laplacian_u t x = 0 :=
    integral_laplacian_eq_zero laplacian_u grad_u_norm hdecay hlapl_int
      (divergence_theorem_ball_bound laplacian_u grad_u_norm) t

  have hut_zero : (∫ x : Fin n → ℝ, u_t t x) = 0 := by rw [heat_eq_integral, div_thm]
  rw [show (0 : ℝ) = ∫ x : Fin n → ℝ, u_t t x from hut_zero.symm]
  show HasDerivAt (totalThermalEnergy n u) (∫ x : Fin n → ℝ, u_t t x) t
  exact leibniz

/-- Conservation of thermal energy (Lemma 2.0.3): for a solution $u$ to the heat equation
$-\partial_t u + \Delta u = 0$ on $[0, \infty) \times \mathbb{R}^n$ satisfying the decay
and integrability hypotheses, the total thermal energy is constant in time:
$\mathcal{T}(t) = \mathcal{T}(0)$. -/
theorem totalThermalEnergy_constant
    {n : ℕ}
    (u : ℝ → (Fin n → ℝ) → ℝ)
    (u_t : ℝ → (Fin n → ℝ) → ℝ)
    (laplacian_u : ℝ → (Fin n → ℝ) → ℝ)
    (grad_u_norm : ℝ → (Fin n → ℝ) → ℝ)

    (hpde : ∀ t (x : Fin n → ℝ), u_t t x = laplacian_u t x)

    (hderiv : ∀ (x : Fin n → ℝ) (t : ℝ), HasDerivAt (fun s => u s x) (u_t t x) t)


    (hdecay : ∀ t, Tendsto
      (fun (R : ℝ) => sSup ((fun x => R ^ ((n : ℝ) - 1) * |grad_u_norm t x|) ''
        (Metric.sphere (0 : Fin n → ℝ) R)))
      atTop (nhds 0))

    (f : (Fin n → ℝ) → ℝ)
    (hf_nn : ∀ x, 0 ≤ f x)
    (hf_int : Integrable f)
    (hdom : ∀ t (x : Fin n → ℝ), |u_t t x| ≤ f x)

    (hu_meas : ∀ t, AEStronglyMeasurable (u t) volume)
    (hu_int : ∀ t, Integrable (u t))
    (hut_meas : ∀ t, AEStronglyMeasurable (u_t t) volume)
    (t : ℝ) :
    totalThermalEnergy n u t = totalThermalEnergy n u 0 := by

  have hzero : ∀ s, HasDerivAt (totalThermalEnergy n u) 0 s :=
    deriv_totalThermalEnergy_eq_zero u u_t laplacian_u grad_u_norm
      hpde hderiv hdecay f hf_nn hf_int hdom hu_meas hu_int hut_meas

  have hdiff : Differentiable ℝ (totalThermalEnergy n u) :=
    fun s => (hzero s).differentiableAt

  have hderiv_zero : ∀ s, deriv (totalThermalEnergy n u) s = 0 :=
    fun s => (hzero s).deriv


  exact is_const_of_deriv_eq_zero hdiff hderiv_zero t 0

end HeatEquation
