/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Convolution
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Fourier.FourierTransform

open MeasureTheory Function Set Metric
open scoped Convolution

noncomputable section

namespace BandlimitedBound

variable {d : ℕ}

/-- The Fourier transform `f̂` on `ℝ^d` (Euclidean space), defined via
`VectorFourier.fourierIntegral` using the standard character and inner product. -/
def fourierTransformRd (d : ℕ) (f : EuclideanSpace ℝ (Fin d) → ℂ) :
    EuclideanSpace ℝ (Fin d) → ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar volume
    (innerₗ (EuclideanSpace ℝ (Fin d))) f

/-- `g` has Fourier support contained in `S`, i.e. `supp ĝ ⊆ S`. -/
def HasFourierSupportIn (g : EuclideanSpace ℝ (Fin d) → ℂ)
    (S : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  Function.support (fourierTransformRd d g) ⊆ S

/-- A non-negative integrable majorant `ψ` at scale `r > 0`, used as an approximate
identity in the bandlimited bound. -/
structure IsApproxIdentityMajorant (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (r : ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ ψ x
  integrable : Integrable ψ (volume : Measure (EuclideanSpace ℝ (Fin d)))
  pos_scale : 0 < r

/-- If `supp ĝ ⊆ B(0, 1/r)`, then `g` admits a convolution representation
`g(x) = ∫ g(y) η(x − y) dy` for some integrable `η`, with the auxiliary `L²`
integrability properties needed to apply Hölder's inequality. -/
theorem exists_convolution_repr (d : ℕ) (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin d) → ℂ)
    (hg : HasFourierSupportIn g (Metric.ball 0 (1 / r))) :
    ∃ (η : EuclideanSpace ℝ (Fin d) → ℂ),
      Integrable (fun y => ‖η y‖) volume ∧
      (0 < ∫ y, ‖η y‖) ∧
      (∀ x, g x = ∫ y, g y * η (x - y)) ∧
      (∀ x, MemLp (fun y => (‖g y‖ * Real.sqrt (‖η (x - y)‖) : ℝ))
        (ENNReal.ofReal 2) volume) ∧
      (∀ x, MemLp (fun y => (Real.sqrt (‖η (x - y)‖) : ℝ))
        (ENNReal.ofReal 2) volume) ∧
      (∀ x, (∫ y, ‖η (x - y)‖) = ∫ y, ‖η y‖) := by sorry

/-- **Bandlimited bound** (Lemma, "Fourier method in Euclidean space"). If
`supp ĝ ⊆ B_{1/r}`, then `|g(x)|² ≲ (|g|² ∗ ψ_r)(x)` for some non-negative approximate
identity `ψ_r` at scale `r`. This is the key estimate that turns a Fourier support
hypothesis into a pointwise inequality controlling `|g|²` by its convolution against a
mollifier. -/
theorem sq_norm_le_convolution_approx_identity (d : ℕ) (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin d) → ℂ)
    (hg : HasFourierSupportIn g (Metric.ball 0 (1 / r))) :
    ∃ (C : ℝ) (_ : 0 < C) (ψ : EuclideanSpace ℝ (Fin d) → ℝ)
      (_ : IsApproxIdentityMajorant ψ r),
      ∀ x : EuclideanSpace ℝ (Fin d),
        ‖g x‖ ^ 2 ≤ C * ((fun y => ‖g y‖ ^ 2) ⋆[ContinuousLinearMap.mul ℝ ℝ] ψ) x := by

  obtain ⟨η, hη_int, hη_pos, hη_rep, hη_memLpF, hη_memLpG, hη_transl⟩ :=
    exists_convolution_repr d r hr g hg

  refine ⟨∫ y, ‖η y‖, hη_pos, fun y => ‖η y‖, ⟨fun y => norm_nonneg _, hη_int, hr⟩, ?_⟩

  intro x
  rw [hη_rep x]
  show ‖∫ y, g y * η (x - y)‖ ^ 2 ≤
    (∫ y, ‖η y‖) * ((fun y => ‖g y‖ ^ 2) ⋆[ContinuousLinearMap.mul ℝ ℝ] (fun y => ‖η y‖)) x
  have conv_eq : ((fun y => ‖g y‖ ^ 2) ⋆[ContinuousLinearMap.mul ℝ ℝ] (fun y => ‖η y‖)) x =
      ∫ t, ‖g t‖ ^ 2 * ‖η (x - t)‖ := rfl
  rw [conv_eq]

  have h_tri : ‖∫ y, g y * η (x - y)‖ ≤ ∫ y, ‖g y‖ * ‖η (x - y)‖ := by
    calc ‖∫ y, g y * η (x - y)‖
        ≤ ∫ y, ‖g y * η (x - y)‖ := norm_integral_le_integral_norm _
      _ = ∫ y, ‖g y‖ * ‖η (x - y)‖ := by congr 1; ext y; exact norm_mul _ _

  have h_holder := integral_mul_norm_le_Lp_mul_Lq
    (show (2:ℝ).HolderConjugate 2 from ⟨by norm_num, by norm_num, by norm_num⟩)
    (hη_memLpF x) (hη_memLpG x)

  have h_lhs : ∫ y, ‖(fun y => (‖g y‖ * Real.sqrt (‖η (x - y)‖) : ℝ)) y‖ *
      ‖(fun y => (Real.sqrt (‖η (x - y)‖) : ℝ)) y‖ = ∫ y, ‖g y‖ * ‖η (x - y)‖ := by
    congr 1; ext y
    simp only [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)),
               Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    rw [mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
  rw [h_lhs] at h_holder

  have h_Fsq : ∫ y, ‖(fun y => (‖g y‖ * Real.sqrt (‖η (x - y)‖) : ℝ)) y‖ ^ (2:ℝ) =
      ∫ y, ‖g y‖ ^ 2 * ‖η (x - y)‖ := by
    congr 1; ext y
    simp only [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))]
    rw [show (‖g y‖ * Real.sqrt (‖η (x - y)‖)) ^ (2:ℝ) =
        (‖g y‖ * Real.sqrt (‖η (x - y)‖)) ^ (2:ℕ) from Real.rpow_natCast _ 2]
    rw [mul_pow, sq (Real.sqrt _), Real.mul_self_sqrt (norm_nonneg _)]

  have h_Gsq : ∫ y, ‖(fun y => (Real.sqrt (‖η (x - y)‖) : ℝ)) y‖ ^ (2:ℝ) =
      ∫ y, ‖η (x - y)‖ := by
    congr 1; ext y
    simp only [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    rw [show Real.sqrt (‖η (x - y)‖) ^ (2:ℝ) =
        Real.sqrt (‖η (x - y)‖) ^ (2:ℕ) from Real.rpow_natCast _ 2]
    rw [sq, Real.mul_self_sqrt (norm_nonneg _)]
  rw [h_Fsq, h_Gsq] at h_holder


  have h_nn : (0:ℝ) ≤ ∫ y, ‖g y‖ * ‖η (x - y)‖ :=
    integral_nonneg (fun y => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have h_rhs_nn : (0:ℝ) ≤ (∫ t, ‖g t‖ ^ 2 * ‖η (x - t)‖) ^ ((1:ℝ)/2) *
      (∫ y, ‖η (x - y)‖) ^ ((1:ℝ)/2) :=
    mul_nonneg (Real.rpow_nonneg (integral_nonneg (fun y =>
      mul_nonneg (sq_nonneg _) (norm_nonneg _))) _)
      (Real.rpow_nonneg (integral_nonneg (fun y => norm_nonneg _)) _)

  calc ‖∫ y, g y * η (x - y)‖ ^ 2
      ≤ (∫ y, ‖g y‖ * ‖η (x - y)‖) ^ 2 :=
        sq_le_sq' (by linarith [norm_nonneg (∫ y, g y * η (x - y)), h_nn]) h_tri
    _ ≤ ((∫ t, ‖g t‖ ^ 2 * ‖η (x - t)‖) ^ ((1:ℝ)/2) *
         (∫ y, ‖η (x - y)‖) ^ ((1:ℝ)/2)) ^ 2 :=
        sq_le_sq' (by linarith [h_nn, h_rhs_nn]) h_holder
    _ = ((∫ t, ‖g t‖ ^ 2 * ‖η (x - t)‖) ^ ((1:ℝ)/2)) ^ 2 *
        ((∫ y, ‖η (x - y)‖) ^ ((1:ℝ)/2)) ^ 2 := mul_pow _ _ _
    _ = (∫ t, ‖g t‖ ^ 2 * ‖η (x - t)‖) * (∫ y, ‖η (x - y)‖) := by
        congr 1
        · rw [← Real.rpow_natCast ((∫ t, ‖g t‖ ^ 2 * ‖η (x - t)‖) ^ ((1:ℝ)/2)) 2,
              ← Real.rpow_mul (integral_nonneg (fun y =>
                mul_nonneg (sq_nonneg _) (norm_nonneg _)))]
          norm_num
        · rw [← Real.rpow_natCast ((∫ y, ‖η (x - y)‖) ^ ((1:ℝ)/2)) 2,
              ← Real.rpow_mul (integral_nonneg (fun y => norm_nonneg _))]
          norm_num
    _ = (∫ t, ‖g t‖ ^ 2 * ‖η (x - t)‖) * (∫ y, ‖η y‖) := by rw [hη_transl x]
    _ = (∫ y, ‖η y‖) * (∫ t, ‖g t‖ ^ 2 * ‖η (x - t)‖) := mul_comm _ _

end BandlimitedBound
