/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.SchurLemma
import Atlas.LieGroups.code.IsotypicPeterWeyl
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Trace

noncomputable section

open MeasureTheory ContinuousRep
open scoped ComplexConjugate

variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  (μ : Measure K) [μ.IsHaarMeasure]

theorem schur_orthogonality_different_reps
    (ρ₁ ρ₂ : IrrFinDimRep K)
    (hne : IsEmpty (RepEquiv ρ₁.rep ρ₂.rep))
    (v₁ w₁ : ρ₁.carrier) (v₂ w₂ : ρ₂.carrier) :
    ∫ g : K, @inner ℂ _ _ ((ρ₁.rep.toMonoidHom g) v₁) w₁ *
      conj (@inner ℂ _ _ ((ρ₂.rep.toMonoidHom g) v₂) w₂) ∂μ = 0 := by sorry

theorem schur_orthogonality_same_rep
    (ρ : IrrFinDimRep K)
    (v₁ v₂ w₁ w₂ : ρ.carrier) :
    ∫ g : K, @inner ℂ _ _ ((ρ.rep.toMonoidHom g) v₁) w₁ *
      conj (@inner ℂ _ _ ((ρ.rep.toMonoidHom g) v₂) w₂) ∂μ =
    @inner ℂ _ _ v₁ v₂ * conj (@inner ℂ _ _ w₁ w₂) /
      (Module.finrank ℂ ρ.carrier : ℂ) := by sorry

def matrixCoefficientOfEnd
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] [CompleteSpace W]
    (ρ : ContinuousRep K W) (A : W →L[ℂ] W) : K → ℂ :=
  fun g => (LinearMap.trace ℂ W) (A.comp (ρ.toMonoidHom g)).toLinearMap

lemma trace_eq_sum_inner {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : OrthonormalBasis ι ℂ E) (L : E →ₗ[ℂ] E) :
    (LinearMap.trace ℂ E) L = ∑ i, @inner ℂ _ _ (b i) (L (b i)) := by
  rw [LinearMap.trace_eq_matrix_trace ℂ b.toBasis]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  congr 1; ext i
  rw [OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  simp [OrthonormalBasis.coe_toBasis]

theorem schur_orthogonality_end
    (ρ : IrrFinDimRep K)
    (A B : ρ.carrier →L[ℂ] ρ.carrier) :
    ∫ g : K, matrixCoefficientOfEnd ρ.rep A g *
      conj (matrixCoefficientOfEnd ρ.rep B g) ∂μ =
    (LinearMap.trace ℂ ρ.carrier)
      (A.comp (ContinuousLinearMap.adjoint B)).toLinearMap /
      (Module.finrank ℂ ρ.carrier : ℂ) := by

  let b := stdOrthonormalBasis ℂ ρ.carrier
  set d := Module.finrank ℂ ρ.carrier with hd_def

  have h_expand : ∀ (L : ρ.carrier →L[ℂ] ρ.carrier) (g : K),
      matrixCoefficientOfEnd ρ.rep L g =
      ∑ i, @inner ℂ _ _ (b i) (L (ρ.rep.toMonoidHom g (b i))) := by
    intro L g
    simp only [matrixCoefficientOfEnd]
    rw [trace_eq_sum_inner b]
    simp

  have h_expand2 : ∀ (L : ρ.carrier →L[ℂ] ρ.carrier) (g : K),
      matrixCoefficientOfEnd ρ.rep L g =
      (starRingEnd ℂ) (∑ i, @inner ℂ _ _ (ρ.rep.toMonoidHom g (b i))
        (ContinuousLinearMap.adjoint L (b i))) := by
    intro L g
    rw [h_expand L g, map_sum]
    congr 1; ext i
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact (inner_conj_symm (𝕜 := ℂ) _ _).symm

  have h_integrand : ∀ g : K,
      matrixCoefficientOfEnd ρ.rep A g * (starRingEnd ℂ) (matrixCoefficientOfEnd ρ.rep B g) =
      ∑ j, ∑ i,
        @inner ℂ _ _ (ρ.rep.toMonoidHom g (b j)) (ContinuousLinearMap.adjoint B (b j)) *
        (starRingEnd ℂ) (@inner ℂ _ _ (ρ.rep.toMonoidHom g (b i))
          (ContinuousLinearMap.adjoint A (b i))) := by
    intro g
    rw [h_expand2 A g, h_expand2 B g, starRingEnd_self_apply, map_sum (starRingEnd ℂ)]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    congr 1; ext j; congr 1; ext i
    ring
  conv_lhs => arg 2; ext g; rw [h_integrand g]


  have hint : ∀ (j i : Fin d),
      Integrable (fun g =>
        @inner ℂ _ _ (ρ.rep.toMonoidHom g (b j)) (ContinuousLinearMap.adjoint B (b j)) *
        (starRingEnd ℂ) (@inner ℂ _ _ (ρ.rep.toMonoidHom g (b i))
          (ContinuousLinearMap.adjoint A (b i)))) μ := by
    intro j i
    apply Continuous.integrable_of_hasCompactSupport
    · apply Continuous.mul
      · exact Continuous.inner (stronglyContinuous_of_continuousRep ρ.rep (b j)) continuous_const
      · exact Complex.continuous_conj.comp
          (Continuous.inner (stronglyContinuous_of_continuousRep ρ.rep (b i)) continuous_const)
    · exact HasCompactSupport.of_compactSpace _

  have hint_sum : ∀ (j : Fin d),
      Integrable (fun g => ∑ i,
        @inner ℂ _ _ (ρ.rep.toMonoidHom g (b j)) (ContinuousLinearMap.adjoint B (b j)) *
        (starRingEnd ℂ) (@inner ℂ _ _ (ρ.rep.toMonoidHom g (b i))
          (ContinuousLinearMap.adjoint A (b i)))) μ := by
    intro j
    apply Continuous.integrable_of_hasCompactSupport
    · apply continuous_finset_sum; intro i _
      apply Continuous.mul
      · exact Continuous.inner (stronglyContinuous_of_continuousRep ρ.rep (b j)) continuous_const
      · exact Complex.continuous_conj.comp
          (Continuous.inner (stronglyContinuous_of_continuousRep ρ.rep (b i)) continuous_const)
    · exact HasCompactSupport.of_compactSpace _
  rw [integral_finset_sum _ (fun j _ => hint_sum j)]

  simp_rw [integral_finset_sum _ (fun i _ => hint _ i)]


  simp_rw [schur_orthogonality_same_rep μ ρ]


  simp_rw [← Finset.sum_div]
  congr 1


  rw [trace_eq_sum_inner b]
  congr 1; ext j


  simp_rw [orthonormal_iff_ite.mp b.orthonormal]


  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

  rw [inner_conj_symm (𝕜 := ℂ)]

  rw [ContinuousLinearMap.adjoint_inner_left]
  rfl

end
