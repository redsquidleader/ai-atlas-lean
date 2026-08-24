/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialGeometry.code.Hypersurfaces
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic.NoncommRing
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

noncomputable section

open Matrix Finset BigOperators

variable {n : ℕ}

namespace ChristoffelSymbols

def secondPartialDeriv (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (i j : Fin n) : Fin (n + 1) → ℝ :=
  fderiv ℝ (fun y => fderiv ℝ patch.f y (Pi.single j 1)) x (Pi.single i 1)

noncomputable def christoffelSymbol (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (i j k : Fin n) : ℝ :=
  let G := firstFundamentalForm patch x
  let d2f := secondPartialDeriv patch x i j
  let tangentialCoeffs : Fin n → ℝ := fun l => d2f ⬝ᵥ (patch.partialDeriv x l)
  ((G⁻¹) *ᵥ tangentialCoeffs) k

theorem secondPartialDeriv_symmetric (patch : HypersurfacePatch n) (x : Fin n → ℝ)
    (hx : x ∈ patch.domain) (i j : Fin n) :
    secondPartialDeriv patch x i j = secondPartialDeriv patch x j i := by
  simp only [secondPartialDeriv]
  have hfat : ContDiffAt ℝ ⊤ patch.f x :=
    patch.smooth.contDiffAt (patch.domain_open.mem_nhds hx)
  have hfderiv_diff : DifferentiableAt ℝ (fderiv ℝ patch.f) x :=
    (hfat.fderiv_right (m := ⊤) le_top).differentiableAt (by exact WithTop.top_ne_zero)
  have hconn : ∀ (v w : Fin n → ℝ),
      fderiv ℝ (fun y => fderiv ℝ patch.f y v) x w = (fderiv ℝ (fderiv ℝ patch.f) x w) v := by
    intro v w
    have hcomp : (fun y => fderiv ℝ patch.f y v) =
        (ContinuousLinearMap.apply ℝ (Fin (n + 1) → ℝ) v) ∘ (fderiv ℝ patch.f) := by
      ext y; simp [ContinuousLinearMap.apply_apply]
    rw [hcomp, fderiv_comp x]
    · simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    · exact (ContinuousLinearMap.apply ℝ (Fin (n + 1) → ℝ) v).differentiableAt
    · exact hfderiv_diff
  rw [hconn, hconn]
  exact hfat.isSymmSndFDerivAt_of_omega.eq (Pi.single i 1) (Pi.single j 1)

end ChristoffelSymbols

noncomputable def partialDeriv {n : ℕ} (i : Fin n) (g : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ g x (Pi.single i 1)

namespace ChristoffelFromMetric

open ChristoffelSymbols

lemma firstFundamentalForm_symmetric {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (i j : Fin n) :
    firstFundamentalForm patch x i j = firstFundamentalForm patch x j i := by
  simp [firstFundamentalForm, of_apply, dotProduct_comm]

lemma firstFundamentalForm_isHermitian {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : (firstFundamentalForm patch x).IsHermitian := by
  ext i j
  simp [star_trivial, firstFundamentalForm_symmetric patch x j i]

lemma firstFundamentalForm_inv_symmetric {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) (i j : Fin n) :
    (firstFundamentalForm patch x)⁻¹ i j = (firstFundamentalForm patch x)⁻¹ j i := by
  have hGinv := (firstFundamentalForm_isHermitian patch x).inv
  have h : ((firstFundamentalForm patch x)⁻¹)ᴴ = (firstFundamentalForm patch x)⁻¹ := hGinv.eq
  have := congr_fun (congr_fun h i) j
  simp [conjTranspose_apply, star_trivial] at this
  linarith


theorem metric_partialDeriv_eq {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) (a b m : Fin n) :
    partialDeriv m (fun y => (firstFundamentalForm patch y) a b) x =
    (secondPartialDeriv patch x m a) ⬝ᵥ (patch.partialDeriv x b) +
    (patch.partialDeriv x a) ⬝ᵥ (secondPartialDeriv patch x m b) := by sorry

lemma inner_secondPartial_eq_half_metric_derivs {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) (i j l : Fin n) :
    (secondPartialDeriv patch x i j) ⬝ᵥ (patch.partialDeriv x l) =
    (1/2) * (partialDeriv j (fun y => (firstFundamentalForm patch y) i l) x -
             partialDeriv l (fun y => (firstFundamentalForm patch y) i j) x +
             partialDeriv i (fun y => (firstFundamentalForm patch y) j l) x) := by
  have hsym : ∀ (a b : Fin n), secondPartialDeriv patch x a b = secondPartialDeriv patch x b a :=
    fun a b => secondPartialDeriv_symmetric patch x hx a b
  rw [metric_partialDeriv_eq patch x hx i l j,
      metric_partialDeriv_eq patch x hx i j l,
      metric_partialDeriv_eq patch x hx j l i]
  rw [hsym j i, hsym l i, hsym l j]


  linarith [dotProduct_comm (patch.partialDeriv x i) (secondPartialDeriv patch x j l),
            dotProduct_comm (patch.partialDeriv x j) (secondPartialDeriv patch x i l)]

theorem christoffel_from_metric {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) (i j l : Fin n) :
    christoffelSymbol patch x i j l =
    (1/2) * ∑ k, (firstFundamentalForm patch x)⁻¹ k l *
      (partialDeriv j (fun y => (firstFundamentalForm patch y) i k) x -
       partialDeriv k (fun y => (firstFundamentalForm patch y) i j) x +
       partialDeriv i (fun y => (firstFundamentalForm patch y) j k) x) := by


  simp only [christoffelSymbol, mulVec, dotProduct]

  have key : ∀ k : Fin n,
      (firstFundamentalForm patch x)⁻¹ l k *
        (∑ i_1, secondPartialDeriv patch x i j i_1 * patch.partialDeriv x k i_1) =
      1 / 2 * ((firstFundamentalForm patch x)⁻¹ k l *
        (partialDeriv j (fun y => firstFundamentalForm patch y i k) x -
         partialDeriv k (fun y => firstFundamentalForm patch y i j) x +
         partialDeriv i (fun y => firstFundamentalForm patch y j k) x)) := by
    intro k
    have h1 := inner_secondPartial_eq_half_metric_derivs patch x hx i j k
    have h2 := firstFundamentalForm_inv_symmetric patch x hx l k
    simp only [dotProduct] at h1
    rw [h1, h2]
    ring
  conv_rhs => rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => key k)

end ChristoffelFromMetric

namespace TensorDecomposition

variable {ι : Type*} {F : Type*} [Field F] [CharZero F]

noncomputable def tensorT (S : ι → ι → ι → F) (i j k : ι) : F :=
  (S i j k + S j k i - S k i j) / 2

theorem tensorT_symm_13 (S : ι → ι → ι → F) (hS : ∀ i j k, S i j k = S j i k)
    (i j k : ι) : tensorT S i j k = tensorT S k j i := by
  simp only [tensorT]
  rw [hS k j i, hS j i k, hS i k j]
  ring

theorem tensor_decomposition (S : ι → ι → ι → F) (hS : ∀ i j k, S i j k = S j i k)
    (i j k : ι) : S i j k = tensorT S i j k + tensorT S j i k := by
  simp only [tensorT]
  rw [hS j i k, hS i k j, hS k j i]
  ring

theorem exists_symmetric_tensor_decomposition (S : ι → ι → ι → F)
    (hS : ∀ i j k, S i j k = S j i k) :
    ∃ T : ι → ι → ι → F,
      (∀ i j k, T i j k = T k j i) ∧ (∀ i j k, S i j k = T i j k + T j i k) :=
  ⟨tensorT S, tensorT_symm_13 S hS, tensor_decomposition S hS⟩

end TensorDecomposition

namespace MovingFrame

open Matrix Matrix.Norms.Elementwise

variable {n : ℕ}

structure IsMovingBasis (patch : HypersurfacePatch n)
    (X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) : Prop where
  smooth : ContDiffOn ℝ ⊤ X patch.domain
  invertible : ∀ x ∈ patch.domain, IsUnit (X x)

structure IsMovingFrame (patch : HypersurfacePatch n)
    (X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) : Prop extends IsMovingBasis patch X where
  orthonormal : ∀ x ∈ patch.domain,
    (X x)ᵀ * firstFundamentalForm patch x * (X x) = 1

def christoffelMatrix (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i k => ChristoffelSymbols.christoffelSymbol patch x i j k

def matrixPartialDeriv
    (X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (j : Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fderiv ℝ X x (Pi.single j 1)

def connectionMatrix (patch : HypersurfacePatch n)
    (X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  let Xinv := (X x)⁻¹
  let dX := matrixPartialDeriv X x j
  let Γ := christoffelMatrix patch x j
  Xinv * dX + Xinv * Γ * (X x)

def curvatureMatrix (patch : HypersurfacePatch n)
    (X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (k j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  let A := connectionMatrix patch X
  let dkAj := fderiv ℝ (fun y => A y j) x (Pi.single k 1)
  let djAk := fderiv ℝ (fun y => A y k) x (Pi.single j 1)
  dkAj - djAk + (A x k) * (A x j) - (A x j) * (A x k)

def riemannCurvatureMatrix (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (k j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fderiv ℝ (fun y => christoffelMatrix patch y j) x (Pi.single k 1) -
  fderiv ℝ (fun y => christoffelMatrix patch y k) x (Pi.single j 1) +
  christoffelMatrix patch x k * christoffelMatrix patch x j -
  christoffelMatrix patch x j * christoffelMatrix patch x k


theorem connectionMatrix_fderiv_leibniz {n : ℕ} (patch : HypersurfacePatch n)
    (X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hX : IsMovingBasis patch X)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) (k j : Fin n) :
    fderiv ℝ (fun y =>
        (X y)⁻¹ * matrixPartialDeriv X y j + (X y)⁻¹ * christoffelMatrix patch y j * (X y))
        x (Pi.single k 1) =
      -(X x)⁻¹ * matrixPartialDeriv X x k * (X x)⁻¹ * matrixPartialDeriv X x j +
        fderiv ℝ (fun y => matrixPartialDeriv X y j) x (Pi.single k 1) -
        (X x)⁻¹ * matrixPartialDeriv X x k * (X x)⁻¹ * christoffelMatrix patch x j * (X x) +
        (X x)⁻¹ * fderiv ℝ (fun y => christoffelMatrix patch y j) x (Pi.single k 1) * (X x) +
        (X x)⁻¹ * christoffelMatrix patch x j * matrixPartialDeriv X x k := by sorry


theorem matrixPartialDeriv_comm {n : ℕ}
    (X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    {s : Set (Fin n → ℝ)} (hs : IsOpen s)
    (hX_smooth : ContDiffOn ℝ ⊤ X s)
    (x : Fin n → ℝ) (hx : x ∈ s) (k j : Fin n) :
    fderiv ℝ (fun y => matrixPartialDeriv X y j) x (Pi.single k 1) =
    fderiv ℝ (fun y => matrixPartialDeriv X y k) x (Pi.single j 1) := by sorry

theorem curvatureMatrix_eq_conjugate (patch : HypersurfacePatch n)
    (X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hX : IsMovingBasis patch X)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain)
    (k j : Fin n)
    : curvatureMatrix patch X x k j =
      (X x)⁻¹ * riemannCurvatureMatrix patch x k j * (X x) := by

  have hUnit : IsUnit (X x) := hX.invertible x hx
  have hDetUnit : IsUnit (X x).det := (Matrix.isUnit_iff_isUnit_det _).mp hUnit
  have hXinv : (X x)⁻¹ * (X x) = 1 := Matrix.nonsing_inv_mul _ hDetUnit
  have hXinv' : (X x) * (X x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hDetUnit

  have h_dkAj := connectionMatrix_fderiv_leibniz patch X hX x hx k j
  have h_djAk := connectionMatrix_fderiv_leibniz patch X hX x hx j k

  have h_mixed := matrixPartialDeriv_comm X patch.domain_open hX.smooth x hx k j

  unfold curvatureMatrix riemannCurvatureMatrix
  simp only [connectionMatrix, matrixPartialDeriv] at h_dkAj h_djAk ⊢
  simp only [matrixPartialDeriv] at h_mixed
  rw [h_dkAj, h_djAk, h_mixed]
  have key : ∀ (A B : Matrix (Fin n) (Fin n) ℝ), A * (X x) * ((X x)⁻¹ * B) = A * B := by
    intros A B; rw [mul_assoc, ← mul_assoc (X x), hXinv', one_mul]
  have key' : ∀ (A B : Matrix (Fin n) (Fin n) ℝ), A * (X x)⁻¹ * ((X x) * B) = A * B := by
    intros A B; rw [mul_assoc, ← mul_assoc (X x)⁻¹, hXinv, one_mul]
  noncomm_ring [hXinv, hXinv', key, key']

def metricPartialDeriv (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  matrixPartialDeriv (firstFundamentalForm patch) x j


theorem metricCompatibility_matrix {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) (j : Fin n) :
    metricPartialDeriv patch x j =
      (christoffelMatrix patch x j)ᵀ * firstFundamentalForm patch x +
      firstFundamentalForm patch x * christoffelMatrix patch x j := by sorry


theorem fderiv_tripleProduct_matrix {n : ℕ} (patch : HypersurfacePatch n)
    (X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hF : IsMovingFrame patch X)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) (j : Fin n) :
    fderiv ℝ (fun y => (X y)ᵀ * firstFundamentalForm patch y * (X y))
        x (Pi.single j 1) =
      (matrixPartialDeriv X x j)ᵀ * firstFundamentalForm patch x * (X x) +
      (X x)ᵀ * metricPartialDeriv patch x j * (X x) +
      (X x)ᵀ * firstFundamentalForm patch x * matrixPartialDeriv X x j := by sorry

theorem connectionMatrix_skewSymmetric (patch : HypersurfacePatch n)
    (X : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (hF : IsMovingFrame patch X) (x : Fin n → ℝ) (hx : x ∈ patch.domain)
    (j : Fin n) :
    (connectionMatrix patch X x j)ᵀ = -(connectionMatrix patch X x j) := by

  have hProdRule := fderiv_tripleProduct_matrix patch X hF x hx j
  have hMetricCompat := metricCompatibility_matrix patch x hx j

  have hConst : (fun y => (X y)ᵀ * firstFundamentalForm patch y * (X y)) =ᶠ[nhds x]
      fun _ => (1 : Matrix (Fin n) (Fin n) ℝ) := by
    have hmem : patch.domain ∈ nhds x := patch.domain_open.mem_nhds hx
    exact Filter.eventually_of_mem hmem (fun y hy => hF.orthonormal y hy)
  have hDerivZero : fderiv ℝ (fun y => (X y)ᵀ * firstFundamentalForm patch y * (X y))
      x (Pi.single j 1) = 0 := by
    rw [Filter.EventuallyEq.fderiv_eq hConst]
    simp [(hasFDerivAt_const (1 : Matrix (Fin n) (Fin n) ℝ) x).fderiv]

  have hSum : (matrixPartialDeriv X x j)ᵀ * firstFundamentalForm patch x * (X x) +
      (X x)ᵀ * metricPartialDeriv patch x j * (X x) +
      (X x)ᵀ * firstFundamentalForm patch x * matrixPartialDeriv X x j = 0 := by
    rw [← hProdRule, hDerivZero]

  rw [hMetricCompat] at hSum


  set G := firstFundamentalForm patch x
  set dX := matrixPartialDeriv X x j
  set Γ := christoffelMatrix patch x j
  set Xm := X x
  set A := connectionMatrix patch X x j

  have hInv : IsUnit Xm.det :=
    (Matrix.isUnit_iff_isUnit_det Xm).mp (hF.toIsMovingBasis.invertible x hx)
  have hXA : Xm * A = dX + Γ * Xm := by
    simp only [A, connectionMatrix, Matrix.mul_add, Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hInv,
        Matrix.mul_nonsing_inv_cancel_left _ _ hInv]

  have hAtXt : Aᵀ * Xmᵀ = dXᵀ + Xmᵀ * Γᵀ := by
    have := congr_arg Matrix.transpose hXA
    simp only [Matrix.transpose_mul, Matrix.transpose_add] at this
    exact this


  have hOrtho : Xmᵀ * G * Xm = 1 := hF.orthonormal x hx
  have hFinal : Aᵀ + A = 0 := by


    have hS1 : Aᵀ * (Xmᵀ * G * Xm) + (Xmᵀ * G * Xm) * A = 0 := by


      have expand : Aᵀ * (Xmᵀ * G * Xm) + (Xmᵀ * G * Xm) * A =
          (Aᵀ * Xmᵀ) * (G * Xm) + Xmᵀ * (G * (Xm * A)) := by
        simp only [Matrix.mul_assoc]
      rw [expand, hAtXt, hXA]


      convert hSum using 1
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      abel
    rw [hOrtho, Matrix.mul_one, Matrix.one_mul] at hS1
    exact hS1

  exact eq_neg_of_add_eq_zero_left hFinal


theorem skewSymm_commutator_01_eq_zero
    (A B : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : Aᵀ = -A) (hB : Bᵀ = -B) :
    (A * B - B * A) 0 1 = 0 := by

  have hA00 : A 0 0 = 0 := by
    have := congr_fun (congr_fun hA 0) 0
    simp [Matrix.transpose_apply, Matrix.neg_apply] at this
    linarith
  have hA11 : A 1 1 = 0 := by
    have := congr_fun (congr_fun hA 1) 1
    simp [Matrix.transpose_apply, Matrix.neg_apply] at this
    linarith
  have hA10 : A 1 0 = -(A 0 1) := by
    have := congr_fun (congr_fun hA 0) 1
    simp [Matrix.transpose_apply, Matrix.neg_apply] at this
    linarith
  have hB00 : B 0 0 = 0 := by
    have := congr_fun (congr_fun hB 0) 0
    simp [Matrix.transpose_apply, Matrix.neg_apply] at this
    linarith
  have hB11 : B 1 1 = 0 := by
    have := congr_fun (congr_fun hB 1) 1
    simp [Matrix.transpose_apply, Matrix.neg_apply] at this
    linarith
  have hB10 : B 1 0 = -(B 0 1) := by
    have := congr_fun (congr_fun hB 0) 1
    simp [Matrix.transpose_apply, Matrix.neg_apply] at this
    linarith

  simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hA00, hA11, hB00, hB11]
  ring

theorem riemannCurvatureMatrix_eq_gaussCurvature_mul_det
    (patch : HypersurfacePatch 2) (x : Fin 2 → ℝ) (hx : x ∈ patch.domain) :
    riemannCurvatureMatrix patch x 1 0 0 1 =
      gaussCurvature patch x * (firstFundamentalForm patch x).det := by sorry


theorem riemannCurvatureMatrix_metric_skew
    (patch : HypersurfacePatch 2) (x : Fin 2 → ℝ) (hx : x ∈ patch.domain)
    (k j : Fin 2) :
    (firstFundamentalForm patch x * riemannCurvatureMatrix patch x k j)ᵀ =
      -(firstFundamentalForm patch x * riemannCurvatureMatrix patch x k j) := by sorry


theorem riemannCurvatureMatrix_GR_entry
    (patch : HypersurfacePatch 2) (x : Fin 2 → ℝ) (hx : x ∈ patch.domain) :
    (firstFundamentalForm patch x * riemannCurvatureMatrix patch x 1 0) 0 1 =
      riemannCurvatureMatrix patch x 1 0 0 1 := by sorry


theorem conjScale_riemannCurvatureMatrix
    (patch : HypersurfacePatch 2) (X : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ)
    (hF : IsMovingFrame patch X) (x : Fin 2 → ℝ) (hx : x ∈ patch.domain) :
    ((X x)⁻¹ * riemannCurvatureMatrix patch x 1 0 * (X x)) 0 1 =
      riemannCurvatureMatrix patch x 1 0 0 1 * (X x).det := by
  set G := firstFundamentalForm patch x
  set R := riemannCurvatureMatrix patch x 1 0
  set Xm := X x

  have hXunit : IsUnit Xm := hF.toIsMovingBasis.invertible x hx
  have hDetUnit : IsUnit Xm.det := (Matrix.isUnit_iff_isUnit_det Xm).mp hXunit
  have hOrtho : Xmᵀ * G * Xm = 1 := hF.orthonormal x hx
  have hXinv_eq : Xm⁻¹ = Xmᵀ * G := by
    have h : Xmᵀ * G * Xm * Xm⁻¹ = 1 * Xm⁻¹ := by rw [hOrtho]
    rw [Matrix.mul_assoc (Xmᵀ * G), Matrix.mul_nonsing_inv Xm hDetUnit,
        mul_one, one_mul] at h
    exact h.symm

  have hRewrite : Xm⁻¹ * R * Xm = Xmᵀ * (G * R) * Xm := by
    rw [hXinv_eq]
    simp only [Matrix.mul_assoc]
  rw [hRewrite]

  have hGR_skew : (G * R)ᵀ = -(G * R) :=
    riemannCurvatureMatrix_metric_skew patch x hx 1 0

  have hS00 : (G * R) 0 0 = 0 := by
    have := congr_fun (congr_fun hGR_skew 0) 0
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this; linarith
  have hS11 : (G * R) 1 1 = 0 := by
    have := congr_fun (congr_fun hGR_skew 1) 1
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this; linarith
  have hS10 : (G * R) 1 0 = -((G * R) 0 1) := by
    have := congr_fun (congr_fun hGR_skew 0) 1
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at this; linarith
  have hIdentity : (Xmᵀ * (G * R) * Xm) 0 1 = (G * R) 0 1 * Xm.det := by
    have hS00' : G 0 0 * R 0 0 + G 0 1 * R 1 0 = 0 := by
      have := hS00; simp only [Matrix.mul_apply, Fin.sum_univ_two] at this; linarith
    have hS11' : G 1 0 * R 0 1 + G 1 1 * R 1 1 = 0 := by
      have := hS11; simp only [Matrix.mul_apply, Fin.sum_univ_two] at this; linarith
    have hS10' : G 1 0 * R 0 0 + G 1 1 * R 1 0 = -(G 0 0 * R 0 1 + G 0 1 * R 1 1) := by
      have := hS10; simp only [Matrix.mul_apply, Fin.sum_univ_two] at this; linarith
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.det_fin_two]
    linear_combination
      Xm 0 0 * Xm 0 1 * hS00' + Xm 1 0 * Xm 0 1 * hS10' + Xm 1 0 * Xm 1 1 * hS11'

  have hEntry : (G * R) 0 1 = R 0 1 :=
    riemannCurvatureMatrix_GR_entry patch x hx
  rw [hIdentity, hEntry]

theorem gaussCurvature_eq_curvatureMatrix_entry (patch : HypersurfacePatch 2)
    (X : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ)
    (hF : IsMovingFrame patch X) (x : Fin 2 → ℝ) (hx : x ∈ patch.domain)
    (hpos : 0 < (X x).det) :
    gaussCurvature patch x * Real.sqrt (firstFundamentalForm patch x).det =
      curvatureMatrix patch X x 1 0 0 1 := by

  have hLemma18_2 : curvatureMatrix patch X x 1 0 0 1 =
      ((X x)⁻¹ * riemannCurvatureMatrix patch x 1 0 * (X x)) 0 1 := by
    have h := curvatureMatrix_eq_conjugate patch X hF.toIsMovingBasis x hx 1 0
    exact congr_fun (congr_fun h 0) 1

  have hGaussEq := riemannCurvatureMatrix_eq_gaussCurvature_mul_det patch x hx

  have hConjScale := conjScale_riemannCurvatureMatrix patch X hF x hx

  have hDetScale : (firstFundamentalForm patch x).det * (X x).det =
      Real.sqrt (firstFundamentalForm patch x).det := by
    have horth := hF.orthonormal x hx
    have hdet_eq : (X x).det * (firstFundamentalForm patch x).det * (X x).det = 1 := by
      have := congr_arg Matrix.det horth
      simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at this
      linarith
    have hdet_sq : (X x).det ^ 2 * (firstFundamentalForm patch x).det = 1 := by
      nlinarith [sq_nonneg ((X x).det)]
    have hGpos : 0 < (firstFundamentalForm patch x).det := by
      nlinarith [sq_nonneg (X x).det, hpos]
    have hprod_pos : 0 < (firstFundamentalForm patch x).det * (X x).det :=
      mul_pos hGpos hpos
    rw [eq_comm]
    exact (Real.sqrt_eq_iff_mul_self_eq_of_pos hprod_pos).mpr (by nlinarith)

  rw [hLemma18_2, hConjScale, hGaussEq, mul_assoc]
  congr 1
  exact hDetScale.symm

end MovingFrame

namespace NormalCoordinates

open scoped MatrixOrder

variable {n : ℕ}

def transformedMetricLinear
    (G B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Bᵀ * G * B

theorem exists_linear_change_identity_metric (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ,
      Bᵀ = B ∧ IsUnit B.det ∧ transformedMetricLinear G B = 1 := by
  set S := CFC.sqrt G
  have hS_pd : S.PosDef := hG.isStrictlyPositive.sqrt.posDef
  have hS_sq : S * S = G := CFC.sqrt_mul_sqrt_self G (hG.posSemidef.nonneg)
  have hS_det : IsUnit S.det := isUnit_iff_ne_zero.mpr (ne_of_gt hS_pd.det_pos)
  have hS_symm : Sᵀ = S := by
    have h : Sᴴ = S := hS_pd.1
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  use S⁻¹
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [Matrix.transpose_nonsing_inv, hS_symm]
  ·
    rw [Matrix.det_nonsing_inv]
    exact hS_det.ringInverse
  ·

    unfold transformedMetricLinear
    rw [Matrix.transpose_nonsing_inv, hS_symm, ← hS_sq]
    rw [show S⁻¹ * (S * S) * S⁻¹ = (S⁻¹ * S) * (S * S⁻¹) from by
      simp only [Matrix.mul_assoc]]
    rw [Matrix.nonsing_inv_mul _ hS_det, Matrix.mul_nonsing_inv _ hS_det, mul_one]

theorem exists_reparam_identity_metric_at_point (patch : HypersurfacePatch n)
    (p : Fin n → ℝ) (_hp : p ∈ patch.domain)
    (hG : (firstFundamentalForm patch p).PosDef) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ,
      Bᵀ = B ∧ IsUnit B.det ∧
      transformedMetricLinear (firstFundamentalForm patch p) B = 1 :=
  exists_linear_change_identity_metric (firstFundamentalForm patch p) hG

theorem exists_normal_coordinates (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef)
    (S : Fin n → Fin n → Fin n → ℝ)
    (hS_symm : ∀ i j k, S i j k = S j i k) :
    ∃ (B : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Fin n → Fin n → ℝ),
      (Bᵀ = B ∧ IsUnit B.det ∧ transformedMetricLinear G B = 1) ∧
      (∀ i j k, T i j k = T k j i) ∧
      (∀ i j k, S i j k = T i j k + T j i k) := by
  obtain ⟨B, hBsymm, hBunit, hBmetric⟩ := exists_linear_change_identity_metric G hG

  let T : Fin n → Fin n → Fin n → ℝ := fun i j k =>
    (S i j k + S j k i - S k i j) / 2
  have hT_symm : ∀ i j k, T i j k = T k j i := by
    intro i j k
    simp only [T]
    rw [hS_symm k j i, hS_symm j i k, hS_symm i k j]
    ring
  have hT_decomp : ∀ i j k, S i j k = T i j k + T j i k := by
    intro i j k
    simp only [T]
    rw [hS_symm j i k, hS_symm i k j, hS_symm k j i]
    ring
  exact ⟨B, T, ⟨hBsymm, hBunit, hBmetric⟩, hT_symm, hT_decomp⟩

def metricDerivAfterQuadraticChange
    (S T : Fin n → Fin n → Fin n → ℝ) (i j k : Fin n) : ℝ :=
  S i j k - T i j k - T j i k

theorem metric_deriv_vanishes_of_decomposition
    (S T : Fin n → Fin n → Fin n → ℝ)
    (hDecomp : ∀ i j k, S i j k = T i j k + T j i k) :
    ∀ i j k, metricDerivAfterQuadraticChange S T i j k = 0 := by
  intro i j k
  simp only [metricDerivAfterQuadraticChange]
  linarith [hDecomp i j k]

theorem exists_normal_coordinates_vanishing_derivs_algebraic (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef)
    (S : Fin n → Fin n → Fin n → ℝ)
    (hS_symm : ∀ i j k, S i j k = S j i k) :
    ∃ (B : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Fin n → Fin n → ℝ),
      (Bᵀ = B ∧ IsUnit B.det ∧ transformedMetricLinear G B = 1) ∧
      (∀ i j k, T i j k = T k j i) ∧
      (∀ i j k, metricDerivAfterQuadraticChange S T i j k = 0) := by
  obtain ⟨B, T, hB, hT_symm, hT_decomp⟩ := exists_normal_coordinates G hG S hS_symm
  exact ⟨B, T, hB, hT_symm, metric_deriv_vanishes_of_decomposition S T hT_decomp⟩

theorem exists_normal_coordinates_vanishing_derivs (patch : HypersurfacePatch n)
    (p : Fin n → ℝ) (_hp : p ∈ patch.domain)
    (hG : (firstFundamentalForm patch p).PosDef)
    (hDiff : DifferentiableAt ℝ (firstFundamentalForm patch) p) :
    let S : Fin n → Fin n → Fin n → ℝ := fun i j k => (MovingFrame.metricPartialDeriv patch p k) i j
    ∃ (B : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Fin n → Fin n → ℝ),

      (Bᵀ = B ∧ IsUnit B.det ∧
        transformedMetricLinear (firstFundamentalForm patch p) B = 1) ∧

      (∀ i j k, T i j k = T k j i) ∧

      (∀ i j k, metricDerivAfterQuadraticChange S T i j k = 0) := by
  intro S


  have hS_symm : ∀ i j k, S i j k = S j i k := by
    intro i j k
    show (MovingFrame.metricPartialDeriv patch p k) i j = (MovingFrame.metricPartialDeriv patch p k) j i
    simp only [MovingFrame.metricPartialDeriv, MovingFrame.matrixPartialDeriv]


    have h1 : ∀ a, DifferentiableAt ℝ (fun y => firstFundamentalForm patch y a) p :=
      differentiableAt_pi.mp hDiff
    have fderiv_entry : ∀ (a b : Fin n),
        (fderiv ℝ (firstFundamentalForm patch) p (Pi.single k 1)) a b =
        (fderiv ℝ (fun y => firstFundamentalForm patch y a b) p) (Pi.single k 1) := by
      intro a b
      have h2 : ∀ c, DifferentiableAt ℝ (fun y => firstFundamentalForm patch y a c) p :=
        differentiableAt_pi.mp (h1 a)

      have hfp := fderiv_pi h1
      have step1 : (fderiv ℝ (firstFundamentalForm patch) p (Pi.single k 1)) a =
          (fderiv ℝ (fun y => firstFundamentalForm patch y a) p) (Pi.single k 1) := by
        have : (fderiv ℝ (firstFundamentalForm patch) p) = fderiv ℝ (fun x => fun i => firstFundamentalForm patch x i) p := rfl
        rw [this, hfp]
        rfl

      have hfp2 := fderiv_pi h2
      have step2 : (fderiv ℝ (fun y => firstFundamentalForm patch y a) p (Pi.single k 1)) b =
          (fderiv ℝ (fun y => firstFundamentalForm patch y a b) p) (Pi.single k 1) := by
        have : (fderiv ℝ (fun y => firstFundamentalForm patch y a) p) =
            fderiv ℝ (fun x => fun c => firstFundamentalForm patch x a c) p := rfl
        rw [this, hfp2]
        rfl
      rw [show (fderiv ℝ (firstFundamentalForm patch) p (Pi.single k 1)) a b =
          ((fderiv ℝ (firstFundamentalForm patch) p (Pi.single k 1)) a) b from rfl]
      rw [step1, step2]
    rw [fderiv_entry i j, fderiv_entry j i]


    have heq : (fun y => firstFundamentalForm patch y i j) =
               (fun y => firstFundamentalForm patch y j i) := by
      funext y
      exact ChristoffelFromMetric.firstFundamentalForm_symmetric patch y i j
    rw [heq]
  exact exists_normal_coordinates_vanishing_derivs_algebraic
    (firstFundamentalForm patch p) hG S hS_symm

end NormalCoordinates

namespace RiemannIntrinsic

open MovingFrame ChristoffelSymbols ChristoffelFromMetric

variable {n : ℕ}

def riemannCurvature (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (i j k s : Fin n) : ℝ :=
  riemannCurvatureMatrix patch x j k i s

lemma fderiv_eq_of_eq_on_open {n : ℕ}
    {f g : (Fin n → ℝ) → ℝ} {s : Set (Fin n → ℝ)} (hs : IsOpen s) {x : Fin n → ℝ} (hx : x ∈ s)
    (hfg : ∀ y ∈ s, f y = g y) : fderiv ℝ f x = fderiv ℝ g x := by
  have heq : f =ᶠ[nhds x] g :=
    Filter.eventually_of_mem (hs.mem_nhds hx) hfg
  exact heq.fderiv_eq

lemma partialDeriv_metric_eq {n : ℕ} (patch₁ patch₂ : HypersurfacePatch n)
    (_hdom : patch₁.domain = patch₂.domain)
    (hG : ∀ x ∈ patch₁.domain, firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x)
    (x : Fin n → ℝ) (hx : x ∈ patch₁.domain) (i j m : Fin n) :
    partialDeriv m (fun y => (firstFundamentalForm patch₁ y) i j) x =
    partialDeriv m (fun y => (firstFundamentalForm patch₂ y) i j) x := by
  simp only [partialDeriv]
  congr 1
  exact fderiv_eq_of_eq_on_open patch₁.domain_open hx
    (fun y hy => congr_fun (congr_fun (hG y hy) i) j)

lemma christoffelSymbol_eq_of_metric_eq {n : ℕ} (patch₁ patch₂ : HypersurfacePatch n)
    (hdom : patch₁.domain = patch₂.domain)
    (hG : ∀ x ∈ patch₁.domain, firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x)
    (x : Fin n → ℝ) (hx : x ∈ patch₁.domain) (i j l : Fin n) :
    christoffelSymbol patch₁ x i j l = christoffelSymbol patch₂ x i j l := by
  rw [christoffel_from_metric patch₁ x hx i j l,
      christoffel_from_metric patch₂ x (hdom ▸ hx) i j l]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have hGeq := hG x hx
  rw [hGeq,
      partialDeriv_metric_eq patch₁ patch₂ hdom hG x hx i k j,
      partialDeriv_metric_eq patch₁ patch₂ hdom hG x hx i j k,
      partialDeriv_metric_eq patch₁ patch₂ hdom hG x hx j k i]

lemma christoffelMatrix_eq_of_metric_eq {n : ℕ} (patch₁ patch₂ : HypersurfacePatch n)
    (hdom : patch₁.domain = patch₂.domain)
    (hG : ∀ x ∈ patch₁.domain, firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x)
    (x : Fin n → ℝ) (hx : x ∈ patch₁.domain) (j : Fin n) :
    christoffelMatrix patch₁ x j = christoffelMatrix patch₂ x j := by
  ext i k
  simp only [christoffelMatrix, Matrix.of_apply]
  exact christoffelSymbol_eq_of_metric_eq patch₁ patch₂ hdom hG x hx i j k

lemma fderiv_christoffelMatrix_eq_of_metric_eq {n : ℕ} (patch₁ patch₂ : HypersurfacePatch n)
    (hdom : patch₁.domain = patch₂.domain)
    (hG : ∀ x ∈ patch₁.domain, firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x)
    (x : Fin n → ℝ) (hx : x ∈ patch₁.domain) (j k : Fin n) :
    fderiv ℝ (fun y => christoffelMatrix patch₁ y j) x (Pi.single k 1) =
    fderiv ℝ (fun y => christoffelMatrix patch₂ y j) x (Pi.single k 1) := by
  have heq : (fun y => christoffelMatrix patch₁ y j) =ᶠ[nhds x]
      (fun y => christoffelMatrix patch₂ y j) :=
    Filter.eventually_of_mem (patch₁.domain_open.mem_nhds hx)
      (fun y hy => christoffelMatrix_eq_of_metric_eq patch₁ patch₂ hdom hG y hy j)
  rw [Filter.EventuallyEq.fderiv_eq heq]

theorem generalized_theorema_egregium {n : ℕ} (patch₁ patch₂ : HypersurfacePatch n)
    (hdom : patch₁.domain = patch₂.domain)
    (hG : ∀ x ∈ patch₁.domain, firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x) :
    ∀ x ∈ patch₁.domain, ∀ i j k s,
      riemannCurvature patch₁ x i j k s = riemannCurvature patch₂ x i j k s := by
  intro x hx i j k s
  simp only [riemannCurvature, riemannCurvatureMatrix]


  have hΓ : ∀ (y : Fin n → ℝ) (hy : y ∈ patch₁.domain) (m : Fin n),
      christoffelMatrix patch₁ y m = christoffelMatrix patch₂ y m :=
    fun y hy m => christoffelMatrix_eq_of_metric_eq patch₁ patch₂ hdom hG y hy m
  have hdΓ : ∀ (m₁ m₂ : Fin n),
      fderiv ℝ (fun y => christoffelMatrix patch₁ y m₁) x (Pi.single m₂ 1) =
      fderiv ℝ (fun y => christoffelMatrix patch₂ y m₁) x (Pi.single m₂ 1) :=
    fun m₁ m₂ => fderiv_christoffelMatrix_eq_of_metric_eq patch₁ patch₂ hdom hG x hx m₁ m₂
  rw [hdΓ k j, hdΓ j k, hΓ x hx j, hΓ x hx k]

end RiemannIntrinsic

namespace GaussEquation

open ChristoffelSymbols

noncomputable def riemannCurvature {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (i j k s : Fin n) : ℝ :=
  partialDeriv k (fun y => christoffelSymbol patch y i j s) x -
  partialDeriv j (fun y => christoffelSymbol patch y i k s) x +
  ∑ t, (christoffelSymbol patch x i j t * christoffelSymbol patch x k t s -
       christoffelSymbol patch x i k t * christoffelSymbol patch x j t s)

noncomputable def thirdPartialDeriv (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (i j k : Fin n) : Fin (n + 1) → ℝ :=
  fderiv ℝ (fun y => secondPartialDeriv patch y i j) x (Pi.single k 1)

noncomputable def thirdDerivTangComp (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (i j k s : Fin n) : ℝ :=
  ((firstFundamentalForm patch x)⁻¹ *ᵥ
    (fun l => (thirdPartialDeriv patch x i j k) ⬝ᵥ (patch.partialDeriv x l))) s

lemma thirdPartialDeriv_symm_jk (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) (i j k : Fin n) :
    thirdPartialDeriv patch x i j k = thirdPartialDeriv patch x i k j := by
  simp only [thirdPartialDeriv, secondPartialDeriv]


  have hfat : ContDiffAt ℝ ⊤ patch.f x :=
    patch.smooth.contDiffAt (patch.domain_open.mem_nhds hx)

  have hH_smooth : ContDiffAt ℝ ⊤ (fun y => fderiv ℝ patch.f y (Pi.single i 1)) x := by
    have h := (hfat.fderiv_right (m := ⊤) le_top).continuousLinearMap_comp
      (ContinuousLinearMap.apply ℝ _ (Pi.single i 1))
    simp only [Function.comp, ContinuousLinearMap.apply_apply] at h
    exact h


  have hfderiv_diff : DifferentiableAt ℝ (fderiv ℝ patch.f) x :=
    (hfat.fderiv_right (m := ⊤) le_top).differentiableAt (by exact WithTop.top_ne_zero)

  have hconn : ∀ (v w : Fin n → ℝ),
      fderiv ℝ (fun y => fderiv ℝ patch.f y v) x w = (fderiv ℝ (fderiv ℝ patch.f) x w) v := by
    intro v w
    have hcomp : (fun y => fderiv ℝ patch.f y v) =
        (ContinuousLinearMap.apply ℝ (Fin (n + 1) → ℝ) v) ∘ (fderiv ℝ patch.f) := by
      ext y; simp [ContinuousLinearMap.apply_apply]
    rw [hcomp, fderiv_comp x]
    · simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
    · exact (ContinuousLinearMap.apply ℝ (Fin (n + 1) → ℝ) v).differentiableAt
    · exact hfderiv_diff


  have hmem : patch.domain ∈ nhds x := patch.domain_open.mem_nhds hx
  have heq_ij : (fun y => fderiv ℝ (fun z => fderiv ℝ patch.f z (Pi.single j 1)) y (Pi.single i 1)) =ᶠ[nhds x]
      (fun y => fderiv ℝ (fun z => fderiv ℝ patch.f z (Pi.single i 1)) y (Pi.single j 1)) := by
    exact Filter.eventually_of_mem hmem (fun y hy => by
      have hfaty : ContDiffAt ℝ ⊤ patch.f y :=
        patch.smooth.contDiffAt (patch.domain_open.mem_nhds hy)
      have hfd : DifferentiableAt ℝ (fderiv ℝ patch.f) y :=
        (hfaty.fderiv_right (m := ⊤) le_top).differentiableAt (by exact WithTop.top_ne_zero)
      have hc1 : (fun z => fderiv ℝ patch.f z (Pi.single j 1)) =
          (ContinuousLinearMap.apply ℝ _ (Pi.single j 1)) ∘ (fderiv ℝ patch.f) := by
        ext z; simp [ContinuousLinearMap.apply_apply]
      have hc2 : (fun z => fderiv ℝ patch.f z (Pi.single i 1)) =
          (ContinuousLinearMap.apply ℝ _ (Pi.single i 1)) ∘ (fderiv ℝ patch.f) := by
        ext z; simp [ContinuousLinearMap.apply_apply]
      simp only [hc1, hc2]
      rw [fderiv_comp y (ContinuousLinearMap.apply ℝ _ (Pi.single j 1)).differentiableAt hfd,
          fderiv_comp y (ContinuousLinearMap.apply ℝ _ (Pi.single i 1)).differentiableAt hfd]
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
        ContinuousLinearMap.fderiv]
      exact (hfaty.isSymmSndFDerivAt_of_omega.eq (Pi.single i 1) (Pi.single j 1)))
  have heq_ik : (fun y => fderiv ℝ (fun z => fderiv ℝ patch.f z (Pi.single k 1)) y (Pi.single i 1)) =ᶠ[nhds x]
      (fun y => fderiv ℝ (fun z => fderiv ℝ patch.f z (Pi.single i 1)) y (Pi.single k 1)) := by
    exact Filter.eventually_of_mem hmem (fun y hy => by
      have hfaty : ContDiffAt ℝ ⊤ patch.f y :=
        patch.smooth.contDiffAt (patch.domain_open.mem_nhds hy)
      have hfd : DifferentiableAt ℝ (fderiv ℝ patch.f) y :=
        (hfaty.fderiv_right (m := ⊤) le_top).differentiableAt (by exact WithTop.top_ne_zero)
      have hc1 : (fun z => fderiv ℝ patch.f z (Pi.single k 1)) =
          (ContinuousLinearMap.apply ℝ _ (Pi.single k 1)) ∘ (fderiv ℝ patch.f) := by
        ext z; simp [ContinuousLinearMap.apply_apply]
      have hc2 : (fun z => fderiv ℝ patch.f z (Pi.single i 1)) =
          (ContinuousLinearMap.apply ℝ _ (Pi.single i 1)) ∘ (fderiv ℝ patch.f) := by
        ext z; simp [ContinuousLinearMap.apply_apply]
      simp only [hc1, hc2]
      rw [fderiv_comp y (ContinuousLinearMap.apply ℝ _ (Pi.single k 1)).differentiableAt hfd,
          fderiv_comp y (ContinuousLinearMap.apply ℝ _ (Pi.single i 1)).differentiableAt hfd]
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
        ContinuousLinearMap.fderiv]
      exact (hfaty.isSymmSndFDerivAt_of_omega.eq (Pi.single i 1) (Pi.single k 1)))

  rw [Filter.EventuallyEq.fderiv_eq heq_ij, Filter.EventuallyEq.fderiv_eq heq_ik]


  have h1 : (fun y => fderiv ℝ (fun z => fderiv ℝ patch.f z (Pi.single i 1)) y (Pi.single j 1)) =
      (ContinuousLinearMap.apply ℝ _ (Pi.single j 1)) ∘
        (fderiv ℝ (fun z => fderiv ℝ patch.f z (Pi.single i 1))) := by
    ext y; simp [ContinuousLinearMap.apply_apply]
  have h2 : (fun y => fderiv ℝ (fun z => fderiv ℝ patch.f z (Pi.single i 1)) y (Pi.single k 1)) =
      (ContinuousLinearMap.apply ℝ _ (Pi.single k 1)) ∘
        (fderiv ℝ (fun z => fderiv ℝ patch.f z (Pi.single i 1))) := by
    ext y; simp [ContinuousLinearMap.apply_apply]
  rw [h1, h2]
  have hHd : DifferentiableAt ℝ (fderiv ℝ (fun z => fderiv ℝ patch.f z (Pi.single i 1))) x :=
    (hH_smooth.fderiv_right (m := ⊤) le_top).differentiableAt (by exact WithTop.top_ne_zero)
  rw [fderiv_comp x (ContinuousLinearMap.apply ℝ _ (Pi.single j 1)).differentiableAt hHd,
      fderiv_comp x (ContinuousLinearMap.apply ℝ _ (Pi.single k 1)).differentiableAt hHd]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.fderiv,
    ContinuousLinearMap.apply_apply]
  exact hH_smooth.isSymmSndFDerivAt_of_omega.eq (Pi.single k 1) (Pi.single j 1)

lemma thirdDerivTangComp_symm_jk (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) (i j k s : Fin n) :
    thirdDerivTangComp patch x i j k s = thirdDerivTangComp patch x i k j s := by
  simp only [thirdDerivTangComp]
  congr 1; funext l; congr 1
  exact thirdPartialDeriv_symm_jk patch x hx i j k


theorem tangential_formula_eq {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) (i j k s : Fin n) :
    thirdDerivTangComp patch x i j k s =
    partialDeriv k (fun y => christoffelSymbol patch y i j s) x +
    (∑ t, christoffelSymbol patch x i j t * christoffelSymbol patch x k t s) -
    secondFundamentalForm patch x i j * shapeOperator patch x s k := by sorry


theorem tangential_component_third_deriv {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) (i j k s : Fin n) :
    partialDeriv k (fun y => christoffelSymbol patch y i j s) x +
    (∑ t, christoffelSymbol patch x i j t * christoffelSymbol patch x k t s) -
    secondFundamentalForm patch x i j * shapeOperator patch x s k =
    partialDeriv j (fun y => christoffelSymbol patch y i k s) x +
    (∑ t, christoffelSymbol patch x i k t * christoffelSymbol patch x j t s) -
    secondFundamentalForm patch x i k * shapeOperator patch x s j := by
  have hlhs := (tangential_formula_eq patch x hx i j k s).symm
  have hrhs := (tangential_formula_eq patch x hx i k j s).symm
  have hsymm := thirdDerivTangComp_symm_jk patch x hx i j k s
  linarith

theorem gauss_equation {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) (i j k s : Fin n) :
    (secondFundamentalForm patch x) i j * (shapeOperator patch x) s k -
    (secondFundamentalForm patch x) i k * (shapeOperator patch x) s j =
    riemannCurvature patch x i j k s := by
  have key := tangential_component_third_deriv patch x hx i j k s
  simp only [riemannCurvature]
  have hsum : ∑ t : Fin n, (christoffelSymbol patch x i j t * christoffelSymbol patch x k t s -
      christoffelSymbol patch x i k t * christoffelSymbol patch x j t s) =
      (∑ t, christoffelSymbol patch x i j t * christoffelSymbol patch x k t s) -
      (∑ t, christoffelSymbol patch x i k t * christoffelSymbol patch x j t s) := by
    rw [← Finset.sum_sub_distrib]
  linarith

end GaussEquation

namespace IntrinsicCurvatures

open MovingFrame ChristoffelSymbols ChristoffelFromMetric RiemannIntrinsic GaussEquation

variable {n : ℕ}

noncomputable def exteriorPowerShapeOp (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (i j k s : Fin n) : ℝ :=
  shapeOperator patch x i k * shapeOperator patch x j s -
  shapeOperator patch x i s * shapeOperator patch x j k

theorem principalCurvatureProducts_intrinsic {n : ℕ}
    (patch₁ patch₂ : HypersurfacePatch n)
    (hdom : patch₁.domain = patch₂.domain)
    (hG : ∀ x ∈ patch₁.domain,
      firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x) :
    ∀ x ∈ patch₁.domain, ∀ i j k s : Fin n,
      exteriorPowerShapeOp patch₁ x i j k s =
      exteriorPowerShapeOp patch₂ x i j k s := by
  intro x hx i j k s
  have hG_eq : firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x := hG x hx
  have hx₂ : x ∈ patch₂.domain := hdom ▸ hx
  have hPD₁ := firstFundamentalForm_posDef patch₁ x hx
  have hG_unit : IsUnit (firstFundamentalForm patch₁ x).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hPD₁.isUnit

  have hΓ : ∀ (a b c : Fin n),
      christoffelSymbol patch₁ x a b c = christoffelSymbol patch₂ x a b c :=
    fun a b c => christoffelSymbol_eq_of_metric_eq patch₁ patch₂ hdom hG x hx a b c

  have hR : ∀ (a b c d : Fin n),
      GaussEquation.riemannCurvature patch₁ x a b c d =
      GaussEquation.riemannCurvature patch₂ x a b c d := by
    intro a b c d
    simp only [GaussEquation.riemannCurvature]
    congr 1
    · congr 1
      · simp only [partialDeriv]
        have heq : (fun y => christoffelSymbol patch₁ y a b d) =ᶠ[nhds x]
            (fun y => christoffelSymbol patch₂ y a b d) :=
          Filter.eventually_of_mem (patch₁.domain_open.mem_nhds hx)
            (fun y hy => christoffelSymbol_eq_of_metric_eq patch₁ patch₂ hdom hG y hy a b d)
        rw [heq.fderiv_eq]
      · simp only [partialDeriv]
        have heq : (fun y => christoffelSymbol patch₁ y a c d) =ᶠ[nhds x]
            (fun y => christoffelSymbol patch₂ y a c d) :=
          Filter.eventually_of_mem (patch₁.domain_open.mem_nhds hx)
            (fun y hy => christoffelSymbol_eq_of_metric_eq patch₁ patch₂ hdom hG y hy a c d)
        rw [heq.fderiv_eq]
    · apply Finset.sum_congr rfl
      intro t _
      rw [hΓ a b t, hΓ c t d, hΓ a c t, hΓ b t d]


  have vec_eq₁ : ∀ a : Fin n,
      ∑ m : Fin n, (firstFundamentalForm patch₁ x) a m *
        exteriorPowerShapeOp patch₁ x m j k s =
      GaussEquation.riemannCurvature patch₁ x a k s j := by
    intro a

    have hg := gauss_equation patch₁ x hx a k s j


    have hH_eq : secondFundamentalForm patch₁ x =
        firstFundamentalForm patch₁ x * shapeOperator patch₁ x := by
      simp only [shapeOperator]
      exact (Matrix.mul_nonsing_inv_cancel_left _ _ hG_unit).symm

    rw [show (secondFundamentalForm patch₁ x) a k =
        ∑ m : Fin n, (firstFundamentalForm patch₁ x) a m *
          (shapeOperator patch₁ x) m k from by
      have := congr_fun (congr_fun hH_eq a) k
      simp only [Matrix.mul_apply] at this
      exact this] at hg
    rw [show (secondFundamentalForm patch₁ x) a s =
        ∑ m : Fin n, (firstFundamentalForm patch₁ x) a m *
          (shapeOperator patch₁ x) m s from by
      have := congr_fun (congr_fun hH_eq a) s
      simp only [Matrix.mul_apply] at this
      exact this] at hg


    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib] at hg
    convert hg using 1
    apply Finset.sum_congr rfl
    intro m _
    simp only [exteriorPowerShapeOp]
    ring
  have vec_eq₂ : ∀ a : Fin n,
      ∑ m : Fin n, (firstFundamentalForm patch₂ x) a m *
        exteriorPowerShapeOp patch₂ x m j k s =
      GaussEquation.riemannCurvature patch₂ x a k s j := by
    intro a
    have hg := gauss_equation patch₂ x hx₂ a k s j
    have hPD₂ := firstFundamentalForm_posDef patch₂ x hx₂
    have hG_unit₂ : IsUnit (firstFundamentalForm patch₂ x).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp hPD₂.isUnit
    have hH_eq : secondFundamentalForm patch₂ x =
        firstFundamentalForm patch₂ x * shapeOperator patch₂ x := by
      simp only [shapeOperator]
      exact (Matrix.mul_nonsing_inv_cancel_left _ _ hG_unit₂).symm
    rw [show (secondFundamentalForm patch₂ x) a k =
        ∑ m : Fin n, (firstFundamentalForm patch₂ x) a m *
          (shapeOperator patch₂ x) m k from by
      have := congr_fun (congr_fun hH_eq a) k
      simp only [Matrix.mul_apply] at this
      exact this] at hg
    rw [show (secondFundamentalForm patch₂ x) a s =
        ∑ m : Fin n, (firstFundamentalForm patch₂ x) a m *
          (shapeOperator patch₂ x) m s from by
      have := congr_fun (congr_fun hH_eq a) s
      simp only [Matrix.mul_apply] at this
      exact this] at hg
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib] at hg
    convert hg using 1
    apply Finset.sum_congr rfl
    intro m _
    simp only [exteriorPowerShapeOp]
    ring


  have vec_combined : ∀ a : Fin n,
      ∑ m : Fin n, (firstFundamentalForm patch₁ x) a m *
        exteriorPowerShapeOp patch₁ x m j k s =
      ∑ m : Fin n, (firstFundamentalForm patch₁ x) a m *
        exteriorPowerShapeOp patch₂ x m j k s := by
    intro a
    rw [vec_eq₁ a, hR a k s j, ← vec_eq₂ a, ← hG_eq]


  have mulVec_eq : (firstFundamentalForm patch₁ x).mulVec
      (fun m => exteriorPowerShapeOp patch₁ x m j k s) =
      (firstFundamentalForm patch₁ x).mulVec
      (fun m => exteriorPowerShapeOp patch₂ x m j k s) := by
    funext a
    simp only [Matrix.mulVec, dotProduct]
    exact vec_combined a

  have v_eq : (fun m => exteriorPowerShapeOp patch₁ x m j k s) =
      (fun m => exteriorPowerShapeOp patch₂ x m j k s) :=
    Matrix.mulVec_injective_of_isUnit hPD₁.isUnit mulVec_eq
  exact congr_fun v_eq i

noncomputable def exteriorPowerShapeOpMatrix (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Matrix (Fin n × Fin n) (Fin n × Fin n) ℝ :=
  Matrix.of (fun p q => exteriorPowerShapeOp patch x p.1 p.2 q.1 q.2)

theorem principalCurvatureProducts_matrix_intrinsic
    (patch₁ patch₂ : HypersurfacePatch n)
    (hdom : patch₁.domain = patch₂.domain)
    (hG : ∀ x ∈ patch₁.domain,
      firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x) :
    ∀ x ∈ patch₁.domain,
      exteriorPowerShapeOpMatrix patch₁ x = exteriorPowerShapeOpMatrix patch₂ x := by
  intro x hx
  ext ⟨i, j⟩ ⟨k, s⟩
  simp only [exteriorPowerShapeOpMatrix, Matrix.of_apply]
  exact principalCurvatureProducts_intrinsic patch₁ patch₂ hdom hG x hx i j k s

abbrev AntisymIndex (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

noncomputable def exteriorPowerShapeOpMatrix_antisym (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Matrix (AntisymIndex n) (AntisymIndex n) ℝ :=
  Matrix.of (fun p q => exteriorPowerShapeOp patch x p.val.1 p.val.2 q.val.1 q.val.2)

theorem compoundMatrix_diagonal_entries (D : Fin n → ℝ)
    (p q : AntisymIndex n) :
    (Matrix.diagonal D p.val.1 q.val.1 * Matrix.diagonal D p.val.2 q.val.2 -
     Matrix.diagonal D p.val.1 q.val.2 * Matrix.diagonal D p.val.2 q.val.1) =
    if p = q then D p.val.1 * D p.val.2 else 0 := by
  simp only [Matrix.diagonal_apply]
  by_cases heq : p = q
  · subst heq
    have hne : ¬(p.val.1 = p.val.2) := Fin.ne_of_lt p.property
    have hne' : ¬(p.val.2 = p.val.1) := (Fin.ne_of_lt p.property).symm
    simp [hne, hne']
  · simp only [heq, if_false]
    obtain ⟨⟨a, b⟩, hab⟩ := p
    obtain ⟨⟨c, d⟩, hcd⟩ := q
    simp only at hab hcd heq
    by_cases hac : a = c <;> by_cases hbd : b = d <;>
      by_cases had : a = d <;> by_cases hbc : b = c
    all_goals simp_all (config := { decide := true })
    all_goals omega

theorem compoundMatrix_diagonal_eq (D : Fin n → ℝ) :
    (Matrix.of (fun (p q : AntisymIndex n) =>
      Matrix.diagonal D p.val.1 q.val.1 * Matrix.diagonal D p.val.2 q.val.2 -
      Matrix.diagonal D p.val.1 q.val.2 * Matrix.diagonal D p.val.2 q.val.1)) =
    Matrix.diagonal (fun p : AntisymIndex n => D p.val.1 * D p.val.2) := by
  ext p q
  simp only [Matrix.of_apply, Matrix.diagonal_apply]
  exact compoundMatrix_diagonal_entries D p q

theorem principalCurvatureProducts_antisym_intrinsic
    (patch₁ patch₂ : HypersurfacePatch n)
    (hdom : patch₁.domain = patch₂.domain)
    (hG : ∀ x ∈ patch₁.domain,
      firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x) :
    ∀ x ∈ patch₁.domain,
      exteriorPowerShapeOpMatrix_antisym patch₁ x =
      exteriorPowerShapeOpMatrix_antisym patch₂ x := by
  intro x hx
  ext ⟨⟨i, j⟩, _⟩ ⟨⟨k, s⟩, _⟩
  simp only [exteriorPowerShapeOpMatrix_antisym, Matrix.of_apply]
  exact principalCurvatureProducts_intrinsic patch₁ patch₂ hdom hG x hx i j k s

theorem principalCurvatureProducts_antisym_charpoly_intrinsic
    (patch₁ patch₂ : HypersurfacePatch n)
    (hdom : patch₁.domain = patch₂.domain)
    (hG : ∀ x ∈ patch₁.domain,
      firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x) :
    ∀ x ∈ patch₁.domain,
      (exteriorPowerShapeOpMatrix_antisym patch₁ x).charpoly =
      (exteriorPowerShapeOpMatrix_antisym patch₂ x).charpoly := by
  intro x hx
  congr 1
  exact principalCurvatureProducts_antisym_intrinsic patch₁ patch₂ hdom hG x hx


theorem scalarCurvature_intrinsic {n : ℕ}
    (patch₁ patch₂ : HypersurfacePatch n)
    (hdom : patch₁.domain = patch₂.domain)
    (hG : ∀ x ∈ patch₁.domain,
      firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x) :
    ∀ x ∈ patch₁.domain,
      scalarCurvature patch₁ x = scalarCurvature patch₂ x := by sorry


theorem det_pow_eq_of_minors_eq {n : ℕ}
    (L₁ L₂ : Matrix (Fin n) (Fin n) ℝ)
    (hMinors : ∀ i j k s : Fin n,
      L₁ i k * L₁ j s - L₁ i s * L₁ j k =
      L₂ i k * L₂ j s - L₂ i s * L₂ j k) :
    L₁.det ^ (n - 1) = L₂.det ^ (n - 1) := by sorry

theorem gaussCurvature_pow_intrinsic {n : ℕ}
    (patch₁ patch₂ : HypersurfacePatch n)
    (hdom : patch₁.domain = patch₂.domain)
    (hG : ∀ x ∈ patch₁.domain,
      firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x) :
    ∀ x ∈ patch₁.domain,
      gaussCurvature patch₁ x ^ (n - 1) =
      gaussCurvature patch₂ x ^ (n - 1) := by
  intro x hx

  simp only [gaussCurvature]

  have hExt := principalCurvatureProducts_intrinsic patch₁ patch₂ hdom hG x hx

  have hMinors : ∀ i j k s : Fin n,
      shapeOperator patch₁ x i k * shapeOperator patch₁ x j s -
      shapeOperator patch₁ x i s * shapeOperator patch₁ x j k =
      shapeOperator patch₂ x i k * shapeOperator patch₂ x j s -
      shapeOperator patch₂ x i s * shapeOperator patch₂ x j k := by
    intro i j k s
    have h := hExt i j k s
    simp only [exteriorPowerShapeOp] at h
    linarith

  exact det_pow_eq_of_minors_eq _ _ hMinors

theorem gaussCurvature_intrinsic_even {n : ℕ} (hn : Even n) (hn_pos : 0 < n)
    (patch₁ patch₂ : HypersurfacePatch n)
    (hdom : patch₁.domain = patch₂.domain)
    (hG : ∀ x ∈ patch₁.domain,
      firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x) :
    ∀ x ∈ patch₁.domain,
      gaussCurvature patch₁ x = gaussCurvature patch₂ x := by
  intro x hx
  have hpow := gaussCurvature_pow_intrinsic patch₁ patch₂ hdom hG x hx


  have hn_sub_odd : Odd (n - 1) := by
    obtain ⟨m, hm⟩ := hn
    exact ⟨m - 1, by omega⟩
  exact hn_sub_odd.strictMono_pow.injective hpow

theorem absGaussCurvature_intrinsic_odd {n : ℕ} (hn : Odd n) (hn_ge : 3 ≤ n)
    (patch₁ patch₂ : HypersurfacePatch n)
    (hdom : patch₁.domain = patch₂.domain)
    (hG : ∀ x ∈ patch₁.domain,
      firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x) :
    ∀ x ∈ patch₁.domain,
      |gaussCurvature patch₁ x| = |gaussCurvature patch₂ x| := by
  intro x hx
  have hpow := gaussCurvature_pow_intrinsic patch₁ patch₂ hdom hG x hx


  have hn_sub_even : Even (n - 1) := by
    obtain ⟨m, hm⟩ := hn
    exact ⟨m, by omega⟩
  have h_ne : n - 1 ≠ 0 := by omega
  have h1 : |gaussCurvature patch₁ x| ^ (n - 1) = |gaussCurvature patch₂ x| ^ (n - 1) := by
    have hab1 := (Even.pow_abs hn_sub_even (gaussCurvature patch₁ x)).symm
    have hab2 := (Even.pow_abs hn_sub_even (gaussCurvature patch₂ x)).symm
    linarith
  exact (pow_left_inj₀ (abs_nonneg _) (abs_nonneg _) h_ne).mp h1

theorem scalarCurvature_gaussCurvature_intrinsic :

    (∀ {n : ℕ} (patch₁ patch₂ : HypersurfacePatch n)
      (hdom : patch₁.domain = patch₂.domain)
      (hG : ∀ x ∈ patch₁.domain,
        firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x),
      ∀ x ∈ patch₁.domain,
        scalarCurvature patch₁ x = scalarCurvature patch₂ x) ∧

    (∀ {n : ℕ} (patch₁ patch₂ : HypersurfacePatch n)
      (hdom : patch₁.domain = patch₂.domain)
      (hG : ∀ x ∈ patch₁.domain,
        firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x),
      ∀ x ∈ patch₁.domain,
        gaussCurvature patch₁ x ^ (n - 1) =
        gaussCurvature patch₂ x ^ (n - 1)) ∧

    (∀ {n : ℕ} (hn : Even n) (hn_pos : 0 < n)
      (patch₁ patch₂ : HypersurfacePatch n)
      (hdom : patch₁.domain = patch₂.domain)
      (hG : ∀ x ∈ patch₁.domain,
        firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x),
      ∀ x ∈ patch₁.domain,
        gaussCurvature patch₁ x = gaussCurvature patch₂ x) ∧

    (∀ {n : ℕ} (hn : Odd n) (hn_ge : 3 ≤ n)
      (patch₁ patch₂ : HypersurfacePatch n)
      (hdom : patch₁.domain = patch₂.domain)
      (hG : ∀ x ∈ patch₁.domain,
        firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x),
      ∀ x ∈ patch₁.domain,
        |gaussCurvature patch₁ x| = |gaussCurvature patch₂ x|) :=
  ⟨@scalarCurvature_intrinsic,
   @gaussCurvature_pow_intrinsic,
   @gaussCurvature_intrinsic_even,
   @absGaussCurvature_intrinsic_odd⟩

end IntrinsicCurvatures

namespace RigidityRank3

open Matrix Finset BigOperators

variable {n : ℕ}

theorem rank3_products_determine_sign (a b c a' b' c' : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a * b = a' * b')
    (hac : a * c = a' * c')
    (hbc : b * c = b' * c') :
    (a' = a ∧ b' = b ∧ c' = c) ∨
    (a' = -a ∧ b' = -b ∧ c' = -c) := by
  have ha' : a' ≠ 0 := by
    intro heq; rw [heq, zero_mul] at hab; exact absurd hab (mul_ne_zero ha hb)
  have hb'_eq : b' = a * b / a' := by field_simp at hab ⊢; linarith
  have hc'_eq : c' = a * c / a' := by field_simp at hac ⊢; linarith
  have key : b * c = (a * b / a') * (a * c / a') := by
    rw [← hb'_eq, ← hc'_eq]; exact hbc
  have key2 : a' ^ 2 = a ^ 2 := by
    have hbc_ne : b * c ≠ 0 := mul_ne_zero hb hc
    field_simp at key; nlinarith [key, hbc_ne]
  have ha'_cases : a' = a ∨ a' = -a := sq_eq_sq_iff_eq_or_eq_neg.mp key2
  rcases ha'_cases with rfl | rfl
  · left; refine ⟨rfl, ?_, ?_⟩
    · field_simp at hb'_eq; linarith
    · field_simp at hc'_eq; linarith
  · right; refine ⟨rfl, ?_, ?_⟩
    · rw [hb'_eq]; field_simp
    · rw [hc'_eq]; field_simp

theorem exteriorPower_rank3_implies_H_eq_or_neg {n : ℕ}
    (patch₁ patch₂ : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch₁.domain)
    (hdomain : patch₁.domain = patch₂.domain)
    (hG_eq : firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x)
    (hext : ∀ i j k s : Fin n,
      IntrinsicCurvatures.exteriorPowerShapeOp patch₁ x i j k s =
      IntrinsicCurvatures.exteriorPowerShapeOp patch₂ x i j k s)
    (hrank : 3 ≤ (secondFundamentalForm patch₁ x).rank) :
    secondFundamentalForm patch₁ x = secondFundamentalForm patch₂ x ∨
    secondFundamentalForm patch₁ x = -secondFundamentalForm patch₂ x := by sorry


theorem secondFF_sign_constant_on_connected {n : ℕ}
    (patch₁ patch₂ : HypersurfacePatch n)
    (hconn : IsConnected patch₁.domain)
    (hrank : ∀ x ∈ patch₁.domain, 3 ≤ (secondFundamentalForm patch₁ x).rank)
    (h_pw : ∀ x ∈ patch₁.domain,
      secondFundamentalForm patch₁ x = secondFundamentalForm patch₂ x ∨
      secondFundamentalForm patch₁ x = -secondFundamentalForm patch₂ x)
    (x₁ : Fin n → ℝ) (hx₁ : x₁ ∈ patch₁.domain)
    (hx₁_neg : secondFundamentalForm patch₁ x₁ = -secondFundamentalForm patch₂ x₁)
    (x₂ : Fin n → ℝ) (hx₂ : x₂ ∈ patch₁.domain)
    (hx₂_pos : secondFundamentalForm patch₁ x₂ = secondFundamentalForm patch₂ x₂) :
    False := by sorry


theorem secondFundamentalForm_eq_or_neg {n : ℕ}
    (patch₁ patch₂ : HypersurfacePatch n)
    (hconn : IsConnected patch₁.domain)
    (hdomain : patch₁.domain = patch₂.domain)
    (hG : ∀ x ∈ patch₁.domain,
      firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x)
    (hrank : ∀ x ∈ patch₁.domain,
      3 ≤ (secondFundamentalForm patch₁ x).rank) :
    (∀ x ∈ patch₁.domain,
      secondFundamentalForm patch₁ x = secondFundamentalForm patch₂ x) ∨
    (∀ x ∈ patch₁.domain,
      secondFundamentalForm patch₁ x = -secondFundamentalForm patch₂ x) := by

  have hext := IntrinsicCurvatures.principalCurvatureProducts_intrinsic patch₁ patch₂ hdomain hG

  have h_pw : ∀ x ∈ patch₁.domain,
      secondFundamentalForm patch₁ x = secondFundamentalForm patch₂ x ∨
      secondFundamentalForm patch₁ x = -secondFundamentalForm patch₂ x :=
    fun x hx => exteriorPower_rank3_implies_H_eq_or_neg patch₁ patch₂ x hx
      hdomain (hG x hx) (hext x hx) (hrank x hx)

  by_contra h_neg
  push_neg at h_neg
  obtain ⟨h_neg_pos, h_neg_neg⟩ := h_neg
  obtain ⟨x₁, hx₁, hx₁_ne⟩ := h_neg_pos
  obtain ⟨x₂, hx₂, hx₂_ne⟩ := h_neg_neg

  have hx₁_neg := (h_pw x₁ hx₁).resolve_left hx₁_ne
  have hx₂_pos := (h_pw x₂ hx₂).resolve_right hx₂_ne

  exact secondFF_sign_constant_on_connected patch₁ patch₂ hconn hrank h_pw
    x₁ hx₁ hx₁_neg x₂ hx₂ hx₂_pos


theorem rigidity_theorem_neg_H {n : ℕ} (patch₁ patch₂ : HypersurfacePatch n)
    (hconn : IsConnected patch₁.domain)
    (hdomain : patch₁.domain = patch₂.domain)
    (hG : ∀ x ∈ patch₁.domain,
      firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x)
    (hH : ∀ x ∈ patch₁.domain,
      secondFundamentalForm patch₁ x = -(secondFundamentalForm patch₂ x)) :
    ∃ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
      (b : Fin (n + 1) → ℝ),
      A ∈ Matrix.orthogonalGroup (Fin (n + 1)) ℝ ∧
      ∀ x ∈ patch₁.domain, patch₂.f x = A.mulVec (patch₁.f x) + b := by sorry

theorem rigidity_of_rank_geq_three {n : ℕ} (patch₁ patch₂ : HypersurfacePatch n)
    (hconn : IsConnected patch₁.domain)
    (hdomain : patch₁.domain = patch₂.domain)
    (hG : ∀ x ∈ patch₁.domain,
      firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x)
    (hrank : ∀ x ∈ patch₁.domain,
      3 ≤ (secondFundamentalForm patch₁ x).rank) :
    ∃ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
      (c : Fin (n + 1) → ℝ),
      A ∈ Matrix.orthogonalGroup (Fin (n + 1)) ℝ ∧
      ∀ x ∈ patch₁.domain, patch₂.f x = A.mulVec (patch₁.f x) + c := by

  have hH_or := secondFundamentalForm_eq_or_neg patch₁ patch₂ hconn hdomain hG hrank
  rcases hH_or with hH_pos | hH_neg
  ·
    obtain ⟨A, b, hA, _, hAb⟩ := rigidity_theorem patch₁ patch₂ hconn hdomain hG hH_pos
    exact ⟨A, b, hA, hAb⟩
  ·
    exact rigidity_theorem_neg_H patch₁ patch₂ hconn hdomain hG hH_neg

end RigidityRank3

namespace TheoremaEgregium

open GaussEquation ChristoffelSymbols

def riemannCurvature (patch : HypersurfacePatch 2)
    (x : Fin 2 → ℝ) (i j k s : Fin 2) : ℝ :=
  GaussEquation.riemannCurvature patch x i j k s

theorem theorema_egregium (patch : HypersurfacePatch 2)
    (x : Fin 2 → ℝ) (hx : x ∈ patch.domain) :
    gaussCurvature patch x =
    (∑ u, (firstFundamentalForm patch x) 1 u * riemannCurvature patch x 0 0 1 u) /
    (firstFundamentalForm patch x).det := by
  simp only [riemannCurvature]
  have hGauss : ∀ u : Fin 2, GaussEquation.riemannCurvature patch x 0 0 1 u =
      secondFundamentalForm patch x 0 0 * shapeOperator patch x u 1 -
      secondFundamentalForm patch x 0 1 * shapeOperator patch x u 0 := by
    intro u; linarith [gauss_equation patch x hx 0 0 1 u]
  simp_rw [hGauss]
  simp only [Fin.sum_univ_two]
  unfold gaussCurvature
  simp only [Matrix.det_fin_two]
  by_cases hGdet : (firstFundamentalForm patch x).det = 0
  · have hL_zero : shapeOperator patch x = 0 := by
      simp only [shapeOperator]
      have : (firstFundamentalForm patch x)⁻¹ = 0 :=
        nonsing_inv_apply_not_isUnit _ (by rwa [isUnit_iff_ne_zero, ne_eq, not_not])
      rw [this, Matrix.zero_mul]
    have h0 : ∀ i j : Fin 2, shapeOperator patch x i j = 0 := by
      intros i j; exact congr_fun (congr_fun hL_zero i) j
    simp [h0, hGdet]
  · have hGunit : IsUnit (firstFundamentalForm patch x).det :=
      isUnit_iff_ne_zero.mpr hGdet
    have hGL : firstFundamentalForm patch x * shapeOperator patch x =
        secondFundamentalForm patch x := by
      simp only [shapeOperator]
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hGunit, Matrix.one_mul]
    have hGL10 : firstFundamentalForm patch x 1 0 * shapeOperator patch x 0 0 +
        firstFundamentalForm patch x 1 1 * shapeOperator patch x 1 0 =
        secondFundamentalForm patch x 1 0 := by
      have := congr_fun (congr_fun hGL 1) 0
      simp [Matrix.mul_apply, Fin.sum_univ_two] at this; linarith
    have hGL11 : firstFundamentalForm patch x 1 0 * shapeOperator patch x 0 1 +
        firstFundamentalForm patch x 1 1 * shapeOperator patch x 1 1 =
        secondFundamentalForm patch x 1 1 := by
      have := congr_fun (congr_fun hGL 1) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two] at this; linarith
    have hdetH : secondFundamentalForm patch x 0 0 * secondFundamentalForm patch x 1 1 -
        secondFundamentalForm patch x 0 1 * secondFundamentalForm patch x 1 0 =
        (firstFundamentalForm patch x).det *
        (shapeOperator patch x 0 0 * shapeOperator patch x 1 1 -
         shapeOperator patch x 0 1 * shapeOperator patch x 1 0) := by
      have hd := Matrix.det_mul (firstFundamentalForm patch x) (shapeOperator patch x)
      rw [hGL] at hd; simp only [Matrix.det_fin_two] at hd ⊢; linarith
    have hkey : firstFundamentalForm patch x 1 0 *
        (secondFundamentalForm patch x 0 0 * shapeOperator patch x 0 1 -
         secondFundamentalForm patch x 0 1 * shapeOperator patch x 0 0) +
        firstFundamentalForm patch x 1 1 *
        (secondFundamentalForm patch x 0 0 * shapeOperator patch x 1 1 -
         secondFundamentalForm patch x 0 1 * shapeOperator patch x 1 0) =
        (firstFundamentalForm patch x).det *
        (shapeOperator patch x 0 0 * shapeOperator patch x 1 1 -
         shapeOperator patch x 0 1 * shapeOperator patch x 1 0) := by
      have heq : firstFundamentalForm patch x 1 0 *
          (secondFundamentalForm patch x 0 0 * shapeOperator patch x 0 1 -
           secondFundamentalForm patch x 0 1 * shapeOperator patch x 0 0) +
          firstFundamentalForm patch x 1 1 *
          (secondFundamentalForm patch x 0 0 * shapeOperator patch x 1 1 -
           secondFundamentalForm patch x 0 1 * shapeOperator patch x 1 0) =
          secondFundamentalForm patch x 0 0 *
          (firstFundamentalForm patch x 1 0 * shapeOperator patch x 0 1 +
           firstFundamentalForm patch x 1 1 * shapeOperator patch x 1 1) -
          secondFundamentalForm patch x 0 1 *
          (firstFundamentalForm patch x 1 0 * shapeOperator patch x 0 0 +
           firstFundamentalForm patch x 1 1 * shapeOperator patch x 1 0) := by ring
      rw [heq, hGL11, hGL10]; linarith [hdetH]
    rw [hkey]
    simp only [Matrix.det_fin_two]
    have hdet_ne : firstFundamentalForm patch x 0 0 * firstFundamentalForm patch x 1 1 -
        firstFundamentalForm patch x 0 1 * firstFundamentalForm patch x 1 0 ≠ 0 := by
      rwa [← Matrix.det_fin_two]
    exact (mul_div_cancel_left₀ _ hdet_ne).symm

end TheoremaEgregium

namespace GaussBonnetTorus

open MeasureTheory MovingFrame

theorem gauss_bonnet_torus_integration_step (patch : HypersurfacePatch 2) (T₁ T₂ : ℝ)
    (α₁ α₂ : ℝ → ℝ → ℝ)
    (hProp18_4 : ∀ x₁ x₂,
      gaussCurvature patch ![x₁, x₂] * Real.sqrt ((firstFundamentalForm patch ![x₁, x₂]).det) =
        deriv (α₁ x₁) x₂ - deriv (fun t => α₂ t x₂) x₁)
    (hα₁_per : ∀ x₁, α₁ x₁ T₂ = α₁ x₁ 0)
    (hα₂_per : ∀ x₂, α₂ T₁ x₂ = α₂ 0 x₂)
    (hα₁_deriv : ∀ x₁, ∀ x₂ ∈ Set.uIcc 0 T₂, HasDerivAt (α₁ x₁) (deriv (α₁ x₁) x₂) x₂)
    (hα₂_deriv : ∀ x₂, ∀ x₁ ∈ Set.uIcc 0 T₁,
      HasDerivAt (fun t => α₂ t x₂) (deriv (fun t => α₂ t x₂) x₁) x₁)
    (hα₁_int : ∀ x₁, IntervalIntegrable (deriv (α₁ x₁)) MeasureTheory.volume 0 T₂)
    (hα₂_int : ∀ x₂, IntervalIntegrable (deriv (fun t => α₂ t x₂)) MeasureTheory.volume 0 T₁)
    (hFubini : ∫ x₁ in (0:ℝ)..T₁, ∫ x₂ in (0:ℝ)..T₂, deriv (fun t => α₂ t x₂) x₁ =
      ∫ x₂ in (0:ℝ)..T₂, ∫ x₁ in (0:ℝ)..T₁, deriv (fun t => α₂ t x₂) x₁)
    (h_sub_int : ∀ x₁, IntervalIntegrable
      (fun x₂ => deriv (fun t => α₂ t x₂) x₁) MeasureTheory.volume 0 T₂) :
    ∫ x₁ in (0:ℝ)..T₁, ∫ x₂ in (0:ℝ)..T₂,
      gaussCurvature patch ![x₁, x₂] * Real.sqrt ((firstFundamentalForm patch ![x₁, x₂]).det) = 0 := by

  simp_rw [hProp18_4]

  have hsplit : ∀ x₁,
      ∫ x₂ in (0:ℝ)..T₂, (deriv (α₁ x₁) x₂ - deriv (fun t => α₂ t x₂) x₁) =
      (∫ x₂ in (0:ℝ)..T₂, deriv (α₁ x₁) x₂) - ∫ x₂ in (0:ℝ)..T₂, deriv (fun t => α₂ t x₂) x₁ := by
    intro x₁
    exact intervalIntegral.integral_sub (hα₁_int x₁) (h_sub_int x₁)
  simp_rw [hsplit]

  have hftc₁ : ∀ x₁, ∫ x₂ in (0:ℝ)..T₂, deriv (α₁ x₁) x₂ = 0 := by
    intro x₁
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (hα₁_deriv x₁) (hα₁_int x₁)]
    rw [hα₁_per x₁, sub_self]
  simp_rw [hftc₁, zero_sub]

  rw [intervalIntegral.integral_neg, neg_eq_zero]
  rw [hFubini]

  have hftc₂ : ∀ x₂, ∫ x₁ in (0:ℝ)..T₁, deriv (fun t => α₂ t x₂) x₁ = 0 := by
    intro x₂
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (hα₂_deriv x₂) (hα₂_int x₂)]
    rw [hα₂_per x₂, sub_self]
  simp_rw [hftc₂]
  simp [intervalIntegral.integral_zero]


theorem exists_periodic_orthonormal_frame (patch : HypersurfacePatch 2) (T₁ T₂ : ℝ)
    (hT₁ : T₁ > 0) (hT₂ : T₂ > 0)
    (hper₁ : ∀ x, patch.f (![x 0 + T₁, x 1]) = patch.f x)
    (hper₂ : ∀ x, patch.f (![x 0, x 1 + T₂]) = patch.f x) :
    ∃ (X : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ),
      IsMovingFrame patch X ∧
      (∀ x, 0 < (X x).det) ∧
      (∀ x, X (![x 0 + T₁, x 1]) = X x) ∧
      (∀ x, X (![x 0, x 1 + T₂]) = X x) := by sorry


theorem connectionMatrix_periodic (patch : HypersurfacePatch 2)
    (X : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ) (T₁ T₂ : ℝ)
    (hper₁ : ∀ x, patch.f (![x 0 + T₁, x 1]) = patch.f x)
    (hper₂ : ∀ x, patch.f (![x 0, x 1 + T₂]) = patch.f x)
    (hXper₁ : ∀ x, X (![x 0 + T₁, x 1]) = X x)
    (hXper₂ : ∀ x, X (![x 0, x 1 + T₂]) = X x) :
    (∀ x j, connectionMatrix patch X (![x 0 + T₁, x 1]) j =
      connectionMatrix patch X x j) ∧
    (∀ x j, connectionMatrix patch X (![x 0, x 1 + T₂]) j =
      connectionMatrix patch X x j) := by sorry


theorem connection_form_curvature_identity
    (patch : HypersurfacePatch 2)
    (X : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ)
    (hF : IsMovingFrame patch X) (hpos : ∀ x, 0 < (X x).det) :
    let α₁ : ℝ → ℝ → ℝ := fun x₁ x₂ => connectionMatrix patch X ![x₁, x₂] 0 0 1
    let α₂ : ℝ → ℝ → ℝ := fun x₁ x₂ => connectionMatrix patch X ![x₁, x₂] 1 0 1
    ∀ x₁ x₂,
      gaussCurvature patch ![x₁, x₂] * Real.sqrt ((firstFundamentalForm patch ![x₁, x₂]).det) =
        deriv (α₁ x₁) x₂ - deriv (fun t => α₂ t x₂) x₁ := by sorry


theorem connection_form_regularity
    (patch : HypersurfacePatch 2)
    (X : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ)
    (hF : IsMovingFrame patch X) (T₁ T₂ : ℝ) (hT₁ : T₁ > 0) (hT₂ : T₂ > 0) :
    let α₁ : ℝ → ℝ → ℝ := fun x₁ x₂ => connectionMatrix patch X ![x₁, x₂] 0 0 1
    let α₂ : ℝ → ℝ → ℝ := fun x₁ x₂ => connectionMatrix patch X ![x₁, x₂] 1 0 1
    (∀ x₁, ∀ x₂ ∈ Set.uIcc 0 T₂, HasDerivAt (α₁ x₁) (deriv (α₁ x₁) x₂) x₂) ∧
    (∀ x₂, ∀ x₁ ∈ Set.uIcc 0 T₁,
      HasDerivAt (fun t => α₂ t x₂) (deriv (fun t => α₂ t x₂) x₁) x₁) ∧
    (∀ x₁, IntervalIntegrable (deriv (α₁ x₁)) MeasureTheory.volume 0 T₂) ∧
    (∀ x₂, IntervalIntegrable (deriv (fun t => α₂ t x₂)) MeasureTheory.volume 0 T₁) ∧
    (∫ x₁ in (0:ℝ)..T₁, ∫ x₂ in (0:ℝ)..T₂, deriv (fun t => α₂ t x₂) x₁ =
      ∫ x₂ in (0:ℝ)..T₂, ∫ x₁ in (0:ℝ)..T₁, deriv (fun t => α₂ t x₂) x₁) ∧
    (∀ x₁, IntervalIntegrable
      (fun x₂ => deriv (fun t => α₂ t x₂) x₁) MeasureTheory.volume 0 T₂) := by sorry

theorem periodic_connection_forms_exist (patch : HypersurfacePatch 2) (T₁ T₂ : ℝ)
    (hT₁ : T₁ > 0) (hT₂ : T₂ > 0)
    (hper₁ : ∀ x, patch.f (![x 0 + T₁, x 1]) = patch.f x)
    (hper₂ : ∀ x, patch.f (![x 0, x 1 + T₂]) = patch.f x) :
    ∃ (α₁ α₂ : ℝ → ℝ → ℝ),
      (∀ x₁ x₂,
        gaussCurvature patch ![x₁, x₂] * Real.sqrt ((firstFundamentalForm patch ![x₁, x₂]).det) =
          deriv (α₁ x₁) x₂ - deriv (fun t => α₂ t x₂) x₁) ∧
      (∀ x₁, α₁ x₁ T₂ = α₁ x₁ 0) ∧
      (∀ x₂, α₂ T₁ x₂ = α₂ 0 x₂) ∧
      (∀ x₁, ∀ x₂ ∈ Set.uIcc 0 T₂, HasDerivAt (α₁ x₁) (deriv (α₁ x₁) x₂) x₂) ∧
      (∀ x₂, ∀ x₁ ∈ Set.uIcc 0 T₁,
        HasDerivAt (fun t => α₂ t x₂) (deriv (fun t => α₂ t x₂) x₁) x₁) ∧
      (∀ x₁, IntervalIntegrable (deriv (α₁ x₁)) MeasureTheory.volume 0 T₂) ∧
      (∀ x₂, IntervalIntegrable (deriv (fun t => α₂ t x₂)) MeasureTheory.volume 0 T₁) ∧
      (∫ x₁ in (0:ℝ)..T₁, ∫ x₂ in (0:ℝ)..T₂, deriv (fun t => α₂ t x₂) x₁ =
        ∫ x₂ in (0:ℝ)..T₂, ∫ x₁ in (0:ℝ)..T₁, deriv (fun t => α₂ t x₂) x₁) ∧
      (∀ x₁, IntervalIntegrable
        (fun x₂ => deriv (fun t => α₂ t x₂) x₁) MeasureTheory.volume 0 T₂) := by

  obtain ⟨X, hFrame, hpos, hXper₁, hXper₂⟩ :=
    exists_periodic_orthonormal_frame patch T₁ T₂ hT₁ hT₂ hper₁ hper₂

  have ⟨hAper₁, hAper₂⟩ := connectionMatrix_periodic patch X T₁ T₂ hper₁ hper₂ hXper₁ hXper₂

  let α₁ : ℝ → ℝ → ℝ := fun x₁ x₂ => connectionMatrix patch X ![x₁, x₂] 0 0 1
  let α₂ : ℝ → ℝ → ℝ := fun x₁ x₂ => connectionMatrix patch X ![x₁, x₂] 1 0 1
  refine ⟨α₁, α₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

  · exact connection_form_curvature_identity patch X hFrame hpos

  · intro x₁
    show connectionMatrix patch X ![x₁, T₂] 0 0 1 = connectionMatrix patch X ![x₁, 0] 0 0 1
    have h := hAper₂ ![x₁, 0] 0
    have hkey : (![x₁, T₂] : Fin 2 → ℝ) = ![(![x₁, (0 : ℝ)] : Fin 2 → ℝ) 0, (![x₁, (0 : ℝ)] : Fin 2 → ℝ) 1 + T₂] := by
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hkey]
    exact congr_fun (congr_fun h 0) 1

  · intro x₂
    show connectionMatrix patch X ![T₁, x₂] 1 0 1 = connectionMatrix patch X ![0, x₂] 1 0 1
    have h := hAper₁ ![0, x₂] 1
    have hkey : (![T₁, x₂] : Fin 2 → ℝ) = ![(![0, x₂] : Fin 2 → ℝ) 0 + T₁, (![0, x₂] : Fin 2 → ℝ) 1] := by
      simp [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hkey]
    exact congr_fun (congr_fun h 0) 1


  · exact (connection_form_regularity patch X hFrame T₁ T₂ hT₁ hT₂).1
  · exact (connection_form_regularity patch X hFrame T₁ T₂ hT₁ hT₂).2.1
  · exact (connection_form_regularity patch X hFrame T₁ T₂ hT₁ hT₂).2.2.1
  · exact (connection_form_regularity patch X hFrame T₁ T₂ hT₁ hT₂).2.2.2.1
  · exact (connection_form_regularity patch X hFrame T₁ T₂ hT₁ hT₂).2.2.2.2.1
  · exact (connection_form_regularity patch X hFrame T₁ T₂ hT₁ hT₂).2.2.2.2.2

theorem gauss_bonnet_torus (patch : HypersurfacePatch 2) (T₁ T₂ : ℝ)
    (hT₁ : T₁ > 0) (hT₂ : T₂ > 0)
    (hper₁ : ∀ x, patch.f (![x 0 + T₁, x 1]) = patch.f x)
    (hper₂ : ∀ x, patch.f (![x 0, x 1 + T₂]) = patch.f x) :
    ∫ x₁ in (0:ℝ)..T₁, ∫ x₂ in (0:ℝ)..T₂,
      gaussCurvature patch ![x₁, x₂] * Real.sqrt ((firstFundamentalForm patch ![x₁, x₂]).det) = 0 := by
  obtain ⟨α₁, α₂, hProp18_4, hα₁_per, hα₂_per, hα₁_deriv, hα₂_deriv,
    hα₁_int, hα₂_int, hFubini, h_sub_int⟩ :=
    periodic_connection_forms_exist patch T₁ T₂ hT₁ hT₂ hper₁ hper₂
  exact gauss_bonnet_torus_integration_step patch T₁ T₂ α₁ α₂
    hProp18_4 hα₁_per hα₂_per hα₁_deriv hα₂_deriv hα₁_int hα₂_int hFubini h_sub_int


theorem interval_integral_nonpos_eq_zero_imp
    (patch : HypersurfacePatch 2) (T₁ T₂ : ℝ)
    (hT₁ : T₁ > 0) (hT₂ : T₂ > 0)
    (hTotal : ∫ x₁ in (0:ℝ)..T₁, ∫ x₂ in (0:ℝ)..T₂,
      gaussCurvature patch ![x₁, x₂] * Real.sqrt ((firstFundamentalForm patch ![x₁, x₂]).det) = 0)
    (hNonpos : ∀ x ∈ patch.domain, gaussCurvature patch x ≤ 0) :
    ∀ x ∈ patch.domain, gaussCurvature patch x = 0 := by sorry


theorem interval_integral_nonneg_eq_zero_imp
    (patch : HypersurfacePatch 2) (T₁ T₂ : ℝ)
    (hT₁ : T₁ > 0) (hT₂ : T₂ > 0)
    (hTotal : ∫ x₁ in (0:ℝ)..T₁, ∫ x₂ in (0:ℝ)..T₂,
      gaussCurvature patch ![x₁, x₂] * Real.sqrt ((firstFundamentalForm patch ![x₁, x₂]).det) = 0)
    (hNonneg : ∀ x ∈ patch.domain, gaussCurvature patch x ≥ 0) :
    ∀ x ∈ patch.domain, gaussCurvature patch x = 0 := by sorry


theorem flat_torus_curvature_nonvanishing (patch : HypersurfacePatch 2) (T₁ T₂ : ℝ)
    (hT₁ : T₁ > 0) (hT₂ : T₂ > 0)
    (hper₁ : ∀ x, patch.f (![x 0 + T₁, x 1]) = patch.f x)
    (hper₂ : ∀ x, patch.f (![x 0, x 1 + T₂]) = patch.f x) :
    ∃ x ∈ patch.domain, gaussCurvature patch x ≠ 0 := by sorry

theorem torus_curvature_sign_change (patch : HypersurfacePatch 2) (T₁ T₂ : ℝ)
    (hT₁ : T₁ > 0) (hT₂ : T₂ > 0)
    (hper₁ : ∀ x, patch.f (![x 0 + T₁, x 1]) = patch.f x)
    (hper₂ : ∀ x, patch.f (![x 0, x 1 + T₂]) = patch.f x) :
    (∃ x ∈ patch.domain, gaussCurvature patch x > 0) ∧
    (∃ x ∈ patch.domain, gaussCurvature patch x < 0) := by

  have hTotal := gauss_bonnet_torus patch T₁ T₂ hT₁ hT₂ hper₁ hper₂

  obtain ⟨x₀, hx₀_mem, hx₀_ne⟩ :=
    flat_torus_curvature_nonvanishing patch T₁ T₂ hT₁ hT₂ hper₁ hper₂
  constructor
  ·


    by_contra h_not_pos
    push Not at h_not_pos
    have h_all_zero := interval_integral_nonpos_eq_zero_imp patch T₁ T₂ hT₁ hT₂ hTotal h_not_pos
    exact hx₀_ne (h_all_zero x₀ hx₀_mem)
  ·


    by_contra h_not_neg
    push Not at h_not_neg
    have h_all_zero := interval_integral_nonneg_eq_zero_imp patch T₁ T₂ hT₁ hT₂ hTotal h_not_neg
    exact hx₀_ne (h_all_zero x₀ hx₀_mem)

end GaussBonnetTorus

namespace AbstractRiemannianMetric

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

structure RiemannianMetric (n : ℕ) where
  domain : Set (Fin n → ℝ)
  domain_open : IsOpen domain
  domain_nonempty : domain.Nonempty
  G : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ
  smooth : ContDiffOn ℝ ⊤ G domain
  symmetric : ∀ x ∈ domain, (G x)ᵀ = G x
  posDef : ∀ x ∈ domain, (G x).PosDef

end AbstractRiemannianMetric

namespace AbstractGaussBonnet

open MeasureTheory

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

structure RiemannianMetric2D where
  G : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ
  smooth : ContDiff ℝ ⊤ G
  symmetric : ∀ x, (G x)ᵀ = G x
  posDef : ∀ x, (G x).PosDef

def scalarPartialDeriv (i : Fin 2) (f : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) : ℝ :=
  fderiv ℝ f x (Pi.single i 1)

def abstractChristoffel (g : RiemannianMetric2D) (x : Fin 2 → ℝ)
    (i j k : Fin 2) : ℝ :=
  (1/2) * ∑ l, (g.G x)⁻¹ l k *
    (scalarPartialDeriv j (fun y => g.G y i l) x +
     scalarPartialDeriv i (fun y => g.G y j l) x -
     scalarPartialDeriv l (fun y => g.G y i j) x)

def abstractGaussCurvature (g : RiemannianMetric2D) (x : Fin 2 → ℝ) : ℝ :=
  let Γ := abstractChristoffel g
  let R : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ := fun i j k s =>
    scalarPartialDeriv k (fun y => Γ y i j s) x -
    scalarPartialDeriv j (fun y => Γ y i k s) x +
    ∑ t, (Γ x i j t * Γ x k t s - Γ x i k t * Γ x j t s)
  (∑ u, (g.G x) 1 u * R 0 0 1 u) / (g.G x).det

def IsDoublyPeriodic (g : RiemannianMetric2D) (T₁ T₂ : ℝ) : Prop :=
  (∀ x : Fin 2 → ℝ, g.G (![x 0 + T₁, x 1]) = g.G x) ∧
  (∀ x : Fin 2 → ℝ, g.G (![x 0, x 1 + T₂]) = g.G x)


def loweredChristoffel (g : RiemannianMetric2D) (i j k : Fin 2)
    (x : Fin 2 → ℝ) : ℝ :=
  (1/2) * (scalarPartialDeriv j (fun y => g.G y i k) x +
           scalarPartialDeriv i (fun y => g.G y j k) x -
           scalarPartialDeriv k (fun y => g.G y i j) x)

def connectionFormF₁ (g : RiemannianMetric2D) (x : Fin 2 → ℝ) : ℝ :=
  -(loweredChristoffel g 0 1 1 x) / Real.sqrt ((g.G x).det)

def connectionFormF₂ (g : RiemannianMetric2D) (x : Fin 2 → ℝ) : ℝ :=
  (loweredChristoffel g 0 0 1 x) / Real.sqrt ((g.G x).det)


lemma gEntry_smooth (g : RiemannianMetric2D) (i j : Fin 2) :
    ContDiff ℝ ⊤ (fun x => g.G x i j) :=
  (contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (Fin 2 → ℝ) i).comp g.smooth)

lemma scalarPartialDeriv_smooth (g : RiemannianMetric2D) (i j : Fin 2)
    (k : Fin 2) : ContDiff ℝ ⊤ (fun x => scalarPartialDeriv k (fun y => g.G y i j) x) := by
  show ContDiff ℝ ⊤ (fun x => fderiv ℝ (fun y => g.G y i j) x (Pi.single k 1))
  exact ((gEntry_smooth g i j).fderiv_right le_top).clm_apply contDiff_const

lemma sqrtDetG_smooth (g : RiemannianMetric2D) :
    ContDiff ℝ ⊤ (fun x => Real.sqrt ((g.G x).det)) := by
  have hdet : ContDiff ℝ ⊤ (fun x => (g.G x).det) := by
    simp only [Matrix.det_fin_two]
    exact ((gEntry_smooth g 0 0).mul (gEntry_smooth g 1 1)).sub
      ((gEntry_smooth g 0 1).mul (gEntry_smooth g 1 0))
  exact hdet.sqrt (fun x => ne_of_gt (g.posDef x).det_pos)

lemma sqrtDetG_ne_zero (g : RiemannianMetric2D) (x : Fin 2 → ℝ) :
    Real.sqrt ((g.G x).det) ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr (g.posDef x).det_pos)

theorem connectionFormF₁_smooth (g : RiemannianMetric2D) :
    ContDiff ℝ ⊤ (connectionFormF₁ g) := by
  unfold connectionFormF₁ loweredChristoffel
  apply ContDiff.div
  · apply ContDiff.neg
    apply ContDiff.mul contDiff_const
    exact ((scalarPartialDeriv_smooth g 0 1 1).add (scalarPartialDeriv_smooth g 1 1 0)).sub
      (scalarPartialDeriv_smooth g 0 1 1)
  · exact sqrtDetG_smooth g
  · exact sqrtDetG_ne_zero g

theorem connectionFormF₂_smooth (g : RiemannianMetric2D) :
    ContDiff ℝ ⊤ (connectionFormF₂ g) := by
  unfold connectionFormF₂ loweredChristoffel
  apply ContDiff.div
  · apply ContDiff.mul contDiff_const
    exact ((scalarPartialDeriv_smooth g 0 1 0).add (scalarPartialDeriv_smooth g 0 1 0)).sub
      (scalarPartialDeriv_smooth g 0 0 1)
  · exact sqrtDetG_smooth g
  · exact sqrtDetG_ne_zero g

lemma fderiv_periodic {f : (Fin 2 → ℝ) → ℝ} (hf : ContDiff ℝ ⊤ f)
    {v : Fin 2 → ℝ} (hper : ∀ z, f (z + v) = f z) (x : Fin 2 → ℝ) :
    fderiv ℝ f (x + v) = fderiv ℝ f x := by
  have hfv : f ∘ (· + v) = f := funext hper
  have hdiff : DifferentiableAt ℝ f (x + v) :=
    (hf.differentiable WithTop.top_ne_zero).differentiableAt
  have hdiff_add : DifferentiableAt ℝ (· + v : (Fin 2 → ℝ) → (Fin 2 → ℝ)) x :=
    differentiableAt_id.add (differentiableAt_const v)
  have hchain := fderiv_comp x hdiff hdiff_add
  have hadd_deriv : fderiv ℝ (· + v : (Fin 2 → ℝ) → (Fin 2 → ℝ)) x =
      ContinuousLinearMap.id ℝ _ := by
    rw [show (· + v : (Fin 2 → ℝ) → (Fin 2 → ℝ)) = fun y => y + v from rfl]
    rw [fderiv_add_const v]; exact fderiv_id'
  rw [hadd_deriv, ContinuousLinearMap.comp_id] at hchain
  rw [← hchain, hfv]

lemma connectionForm_periodic_aux (g : RiemannianMetric2D) (v : Fin 2 → ℝ)
    (hGper : ∀ z : Fin 2 → ℝ, g.G (z + v) = g.G z) (i j k : Fin 2)
    (x : Fin 2 → ℝ) :
    loweredChristoffel g i j k (x + v) = loweredChristoffel g i j k x := by
  unfold loweredChristoffel scalarPartialDeriv
  congr 1
  have hentry_per : ∀ a b : Fin 2, ∀ z, (fun y => g.G y a b) (z + v) =
      (fun y => g.G y a b) z := fun a b z => by
    show g.G (z + v) a b = g.G z a b
    rw [hGper z]
  have hfderiv_per : ∀ a b : Fin 2, ∀ d,
      fderiv ℝ (fun y => g.G y a b) (x + v) d =
      fderiv ℝ (fun y => g.G y a b) x d := fun a b d => by
    rw [fderiv_periodic (gEntry_smooth g a b) (hentry_per a b) x]
  simp only [hfderiv_per]

lemma connectionFormF₁_periodic (g : RiemannianMetric2D) (v : Fin 2 → ℝ)
    (hGper : ∀ z : Fin 2 → ℝ, g.G (z + v) = g.G z)
    (x : Fin 2 → ℝ) :
    connectionFormF₁ g (x + v) = connectionFormF₁ g x := by
  unfold connectionFormF₁
  rw [connectionForm_periodic_aux g v hGper 0 1 1 x]
  congr 1; exact congr_arg (fun M => Real.sqrt M.det) (hGper x)

lemma connectionFormF₂_periodic (g : RiemannianMetric2D) (v : Fin 2 → ℝ)
    (hGper : ∀ z : Fin 2 → ℝ, g.G (z + v) = g.G z)
    (x : Fin 2 → ℝ) :
    connectionFormF₂ g (x + v) = connectionFormF₂ g x := by
  unfold connectionFormF₂
  rw [connectionForm_periodic_aux g v hGper 0 0 1 x]
  congr 1; exact congr_arg (fun M => Real.sqrt M.det) (hGper x)

theorem connectionFormF₁_periodic_x0 (g : RiemannianMetric2D) (T₁ T₂ : ℝ)
    (hper : IsDoublyPeriodic g T₁ T₂) (x₁ x₂ : ℝ) :
    connectionFormF₁ g ![x₁ + T₁, x₂] = connectionFormF₁ g ![x₁, x₂] := by
  have hv : ∀ z : Fin 2 → ℝ, g.G (z + Pi.single 0 T₁) = g.G z := by
    intro z; have := hper.1 z
    rwa [show ![z 0 + T₁, z 1] = z + Pi.single 0 T₁ from by
      ext i; fin_cases i <;> simp [Pi.single, Function.update]] at this
  have hpt : (![x₁ + T₁, x₂] : Fin 2 → ℝ) = ![x₁, x₂] + Pi.single 0 T₁ := by
    ext i; fin_cases i <;> simp [Pi.single, Function.update]
  rw [hpt]; exact connectionFormF₁_periodic g _ hv _

theorem connectionFormF₁_periodic_x1 (g : RiemannianMetric2D) (T₁ T₂ : ℝ)
    (hper : IsDoublyPeriodic g T₁ T₂) (x₁ x₂ : ℝ) :
    connectionFormF₁ g ![x₁, x₂ + T₂] = connectionFormF₁ g ![x₁, x₂] := by
  have hv : ∀ z : Fin 2 → ℝ, g.G (z + Pi.single 1 T₂) = g.G z := by
    intro z; have := hper.2 z
    rwa [show ![z 0, z 1 + T₂] = z + Pi.single 1 T₂ from by
      ext i; fin_cases i <;> simp [Pi.single, Function.update]] at this
  have hpt : (![x₁, x₂ + T₂] : Fin 2 → ℝ) = ![x₁, x₂] + Pi.single 1 T₂ := by
    ext i; fin_cases i <;> simp [Pi.single, Function.update]
  rw [hpt]; exact connectionFormF₁_periodic g _ hv _

theorem connectionFormF₂_periodic_x0 (g : RiemannianMetric2D) (T₁ T₂ : ℝ)
    (hper : IsDoublyPeriodic g T₁ T₂) (x₁ x₂ : ℝ) :
    connectionFormF₂ g ![x₁ + T₁, x₂] = connectionFormF₂ g ![x₁, x₂] := by
  have hv : ∀ z : Fin 2 → ℝ, g.G (z + Pi.single 0 T₁) = g.G z := by
    intro z; have := hper.1 z
    rwa [show ![z 0 + T₁, z 1] = z + Pi.single 0 T₁ from by
      ext i; fin_cases i <;> simp [Pi.single, Function.update]] at this
  have hpt : (![x₁ + T₁, x₂] : Fin 2 → ℝ) = ![x₁, x₂] + Pi.single 0 T₁ := by
    ext i; fin_cases i <;> simp [Pi.single, Function.update]
  rw [hpt]; exact connectionFormF₂_periodic g _ hv _

theorem connectionFormF₂_periodic_x1 (g : RiemannianMetric2D) (T₁ T₂ : ℝ)
    (hper : IsDoublyPeriodic g T₁ T₂) (x₁ x₂ : ℝ) :
    connectionFormF₂ g ![x₁, x₂ + T₂] = connectionFormF₂ g ![x₁, x₂] := by
  have hv : ∀ z : Fin 2 → ℝ, g.G (z + Pi.single 1 T₂) = g.G z := by
    intro z; have := hper.2 z
    rwa [show ![z 0, z 1 + T₂] = z + Pi.single 1 T₂ from by
      ext i; fin_cases i <;> simp [Pi.single, Function.update]] at this
  have hpt : (![x₁, x₂ + T₂] : Fin 2 → ℝ) = ![x₁, x₂] + Pi.single 1 T₂ := by
    ext i; fin_cases i <;> simp [Pi.single, Function.update]
  rw [hpt]; exact connectionFormF₂_periodic g _ hv _


theorem connectionForm_divergence_identity (g : RiemannianMetric2D)
    (x : Fin 2 → ℝ) :
    abstractGaussCurvature g x * Real.sqrt ((g.G x).det) =
    scalarPartialDeriv 0 (connectionFormF₁ g) x +
    scalarPartialDeriv 1 (connectionFormF₂ g) x := by sorry

theorem curvature_density_divergence_form (g : RiemannianMetric2D) (T₁ T₂ : ℝ)
    (hT₁ : T₁ > 0) (hT₂ : T₂ > 0)
    (hper : IsDoublyPeriodic g T₁ T₂) :
    ∃ (F₁ F₂ : (Fin 2 → ℝ) → ℝ),
      (ContDiff ℝ ⊤ F₁) ∧
      (ContDiff ℝ ⊤ F₂) ∧
      (∀ x₁ x₂, F₁ ![x₁ + T₁, x₂] = F₁ ![x₁, x₂]) ∧
      (∀ x₁ x₂, F₁ ![x₁, x₂ + T₂] = F₁ ![x₁, x₂]) ∧
      (∀ x₁ x₂, F₂ ![x₁ + T₁, x₂] = F₂ ![x₁, x₂]) ∧
      (∀ x₁ x₂, F₂ ![x₁, x₂ + T₂] = F₂ ![x₁, x₂]) ∧
      (∀ x : Fin 2 → ℝ,
        abstractGaussCurvature g x * Real.sqrt ((g.G x).det) =
        scalarPartialDeriv 0 F₁ x + scalarPartialDeriv 1 F₂ x) :=
  ⟨connectionFormF₁ g, connectionFormF₂ g,
   connectionFormF₁_smooth g,
   connectionFormF₂_smooth g,
   connectionFormF₁_periodic_x0 g T₁ T₂ hper,
   connectionFormF₁_periodic_x1 g T₁ T₂ hper,
   connectionFormF₂_periodic_x0 g T₁ T₂ hper,
   connectionFormF₂_periodic_x1 g T₁ T₂ hper,
   connectionForm_divergence_identity g⟩


theorem integral_divergence_periodic_rectangle
    (F₁ F₂ : (Fin 2 → ℝ) → ℝ) (T₁ T₂ : ℝ) (hT₁ : T₁ > 0) (hT₂ : T₂ > 0)
    (hF₁_smooth : ContDiff ℝ ⊤ F₁) (hF₂_smooth : ContDiff ℝ ⊤ F₂)
    (hF₁_per1 : ∀ x₁ x₂, F₁ ![x₁ + T₁, x₂] = F₁ ![x₁, x₂])
    (hF₁_per2 : ∀ x₁ x₂, F₁ ![x₁, x₂ + T₂] = F₁ ![x₁, x₂])
    (hF₂_per1 : ∀ x₁ x₂, F₂ ![x₁ + T₁, x₂] = F₂ ![x₁, x₂])
    (hF₂_per2 : ∀ x₁ x₂, F₂ ![x₁, x₂ + T₂] = F₂ ![x₁, x₂]) :
    ∫ x₁ in (0:ℝ)..T₁, ∫ x₂ in (0:ℝ)..T₂,
      (scalarPartialDeriv 0 F₁ ![x₁, x₂] + scalarPartialDeriv 1 F₂ ![x₁, x₂]) = 0 := by

  have h_cont_ins_snd : ∀ c : ℝ, Continuous (fun x₂ : ℝ => (![c, x₂] : Fin 2 → ℝ)) :=
    fun c => continuous_pi (fun i => by
      fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> fun_prop)
  have h_cont_pair : Continuous (fun p : ℝ × ℝ => (![p.1, p.2] : Fin 2 → ℝ)) :=
    continuous_pi (fun i => by
      fin_cases i <;> simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;> fun_prop)

  have h_cont_pd0 : Continuous (scalarPartialDeriv 0 F₁) := by
    unfold scalarPartialDeriv
    exact (ContinuousLinearMap.apply ℝ ℝ (Pi.single 0 (1 : ℝ))).continuous.comp
      (hF₁_smooth.continuous_fderiv (by simp : (⊤ : WithTop ℕ∞) ≠ 0))
  have h_cont_pd1 : Continuous (scalarPartialDeriv 1 F₂) := by
    unfold scalarPartialDeriv
    exact (ContinuousLinearMap.apply ℝ ℝ (Pi.single 1 (1 : ℝ))).continuous.comp
      (hF₂_smooth.continuous_fderiv (by simp : (⊤ : WithTop ℕ∞) ≠ 0))

  have h_int0 : ∀ x₁, IntervalIntegrable
      (fun x₂ => scalarPartialDeriv 0 F₁ ![x₁, x₂]) volume 0 T₂ :=
    fun x₁ => (h_cont_pd0.comp (h_cont_ins_snd x₁)).intervalIntegrable 0 T₂
  have h_int1 : ∀ x₁, IntervalIntegrable
      (fun x₂ => scalarPartialDeriv 1 F₂ ![x₁, x₂]) volume 0 T₂ :=
    fun x₁ => (h_cont_pd1.comp (h_cont_ins_snd x₁)).intervalIntegrable 0 T₂

  have hsplit : ∀ x₁, ∫ x₂ in (0:ℝ)..T₂,
      (scalarPartialDeriv 0 F₁ ![x₁, x₂] + scalarPartialDeriv 1 F₂ ![x₁, x₂]) =
      (∫ x₂ in (0:ℝ)..T₂, scalarPartialDeriv 0 F₁ ![x₁, x₂]) +
      (∫ x₂ in (0:ℝ)..T₂, scalarPartialDeriv 1 F₂ ![x₁, x₂]) :=
    fun x₁ => intervalIntegral.integral_add (h_int0 x₁) (h_int1 x₁)
  simp_rw [hsplit]

  have hftc2 : ∀ x₁, ∫ x₂ in (0:ℝ)..T₂, scalarPartialDeriv 1 F₂ ![x₁, x₂] = 0 := by
    intro x₁
    have h_hda : ∀ x₂ ∈ Set.uIcc 0 T₂,
        HasDerivAt (fun t => F₂ ![x₁, t]) (scalarPartialDeriv 1 F₂ ![x₁, x₂]) x₂ := by
      intros x₂ _; unfold scalarPartialDeriv
      have hpt : (![x₁, 0] : Fin 2 → ℝ) + x₂ • (Pi.single 1 1 : Fin 2 → ℝ) = ![x₁, x₂] := by
        ext i; fin_cases i <;>
          simp [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.single, Function.update]
      have heq : (fun t => F₂ ![x₁, t]) =
          F₂ ∘ (fun t => ![x₁, 0] + t • (Pi.single 1 1 : Fin 2 → ℝ)) := by
        ext t; congr 1; ext i
        fin_cases i <;>
          simp [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.single, Function.update]
      rw [heq, show (![x₁, x₂] : Fin 2 → ℝ) =
          ![x₁, 0] + x₂ • (Pi.single 1 1 : Fin 2 → ℝ) from hpt.symm]
      exact ((hF₂_smooth.differentiable
        (by simp : (⊤ : WithTop ℕ∞) ≠ 0)).differentiableAt.hasFDerivAt).comp_hasDerivAt x₂
        (((hasDerivAt_id x₂).smul_const
          (Pi.single 1 1 : Fin 2 → ℝ)).congr_deriv (one_smul _ _) |>.const_add _)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h_hda (h_int1 x₁)]
    have : F₂ ![x₁, T₂] = F₂ ![x₁, 0] := by
      have := hF₂_per2 x₁ 0; simp at this; exact this
    linarith
  simp_rw [hftc2, add_zero]


  set G : ℝ → ℝ := fun x₁ => ∫ x₂ in (0:ℝ)..T₂, F₁ ![x₁, x₂]

  have hG_deriv : ∀ x₁ ∈ Set.uIcc 0 T₁,
      HasDerivAt G (∫ x₂ in (0:ℝ)..T₂, scalarPartialDeriv 0 F₁ ![x₁, x₂]) x₁ := by
    intros x₁₀ _
    show HasDerivAt (fun x₁ => ∫ x₂ in (0:ℝ)..T₂, F₁ ![x₁, x₂])
      (∫ x₂ in (0:ℝ)..T₂, scalarPartialDeriv 0 F₁ ![x₁₀, x₂]) x₁₀

    have h_deriv : ∀ x₂ x₁ : ℝ,
        HasDerivAt (fun t => F₁ ![t, x₂]) (scalarPartialDeriv 0 F₁ ![x₁, x₂]) x₁ := by
      intros x₂ x₁; unfold scalarPartialDeriv
      have hpt : (![0, x₂] : Fin 2 → ℝ) + x₁ • (Pi.single 0 1 : Fin 2 → ℝ) = ![x₁, x₂] := by
        ext i; fin_cases i <;>
          simp [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.single, Function.update]
      have heq : (fun t => F₁ ![t, x₂]) =
          F₁ ∘ (fun t => ![0, x₂] + t • (Pi.single 0 1 : Fin 2 → ℝ)) := by
        ext t; congr 1; ext i
        fin_cases i <;>
          simp [Matrix.cons_val_zero, Matrix.cons_val_one, Pi.single, Function.update]
      rw [heq, show (![x₁, x₂] : Fin 2 → ℝ) =
          ![0, x₂] + x₁ • (Pi.single 0 1 : Fin 2 → ℝ) from hpt.symm]
      exact ((hF₁_smooth.differentiable
        (by simp : (⊤ : WithTop ℕ∞) ≠ 0)).differentiableAt.hasFDerivAt).comp_hasDerivAt x₁
        (((hasDerivAt_id x₁).smul_const
          (Pi.single 0 1 : Fin 2 → ℝ)).congr_deriv (one_smul _ _) |>.const_add _)

    have hcompact : IsCompact (Set.Icc (x₁₀ - 1) (x₁₀ + 1) ×ˢ Set.uIcc 0 T₂) :=
      isCompact_Icc.prod isCompact_uIcc
    have ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn
      ((h_cont_pd0.comp h_cont_pair).continuousOn)

    exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := volume)
      (Icc_mem_nhds (by linarith : x₁₀ - 1 < x₁₀) (by linarith : x₁₀ < x₁₀ + 1))
      (Filter.Eventually.of_forall (fun x =>
        (hF₁_smooth.continuous.comp (h_cont_ins_snd x)).aestronglyMeasurable.restrict))
      ((hF₁_smooth.continuous.comp (h_cont_ins_snd x₁₀)).intervalIntegrable 0 T₂)
      ((h_cont_pd0.comp (h_cont_ins_snd x₁₀)).aestronglyMeasurable.restrict)
      (ae_of_all volume (fun t (ht : t ∈ Set.uIoc 0 T₂) x
        (hx : x ∈ Set.Icc (x₁₀ - 1) (x₁₀ + 1)) =>
        hM (x, t) ⟨hx, Set.Ioc_subset_Icc_self ht⟩))
      (intervalIntegrable_const)
      (ae_of_all volume (fun t (_ht : t ∈ Set.uIoc 0 T₂) x
        (_hx : x ∈ Set.Icc (x₁₀ - 1) (x₁₀ + 1)) => h_deriv t x))).2

  have hG_int : IntervalIntegrable
      (fun x₁ => ∫ x₂ in (0:ℝ)..T₂, scalarPartialDeriv 0 F₁ ![x₁, x₂]) volume 0 T₁ := by
    have hc : Continuous (fun x₁ => ∫ x₂ in (0:ℝ)..T₂, scalarPartialDeriv 0 F₁ ![x₁, x₂]) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (show Continuous (Function.uncurry (fun x₁ x₂ => scalarPartialDeriv 0 F₁ ![x₁, x₂])) from
          (h_cont_pd0.comp h_cont_pair).comp (by fun_prop : Continuous (fun p : ℝ × ℝ => p)))
        0 T₂
    exact hc.intervalIntegrable 0 T₁

  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hG_deriv hG_int]

  have hG_per : G T₁ = G 0 := by
    show ∫ x₂ in (0:ℝ)..T₂, F₁ ![T₁, x₂] = ∫ x₂ in (0:ℝ)..T₂, F₁ ![0, x₂]
    congr 1; ext x₂
    have := hF₁_per1 0 x₂; simp at this; exact this
  linarith

theorem gauss_bonnet_doubly_periodic_abstract (g : RiemannianMetric2D) (T₁ T₂ : ℝ)
    (hT₁ : T₁ > 0) (hT₂ : T₂ > 0)
    (hper : IsDoublyPeriodic g T₁ T₂) :
    ∫ x₁ in (0:ℝ)..T₁, ∫ x₂ in (0:ℝ)..T₂,
      abstractGaussCurvature g ![x₁, x₂] *
      Real.sqrt ((g.G ![x₁, x₂]).det) = 0 := by

  obtain ⟨F₁, F₂, hF₁_smooth, hF₂_smooth, hF₁_per1, hF₁_per2, hF₂_per1, hF₂_per2, hDiv⟩ :=
    curvature_density_divergence_form g T₁ T₂ hT₁ hT₂ hper

  simp_rw [show ∀ x₁ x₂, abstractGaussCurvature g ![x₁, x₂] *
      Real.sqrt ((g.G ![x₁, x₂]).det) =
      scalarPartialDeriv 0 F₁ ![x₁, x₂] + scalarPartialDeriv 1 F₂ ![x₁, x₂] from
    fun x₁ x₂ => hDiv ![x₁, x₂]]

  exact integral_divergence_periodic_rectangle F₁ F₂ T₁ T₂ hT₁ hT₂
    hF₁_smooth hF₂_smooth hF₁_per1 hF₁_per2 hF₂_per1 hF₂_per2

end AbstractGaussBonnet

end
