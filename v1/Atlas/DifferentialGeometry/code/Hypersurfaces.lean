/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef

import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.Topology.Connected.Basic

noncomputable section

open Matrix Finset BigOperators

structure HypersurfacePatch (n : ℕ) where
  domain : Set (Fin n → ℝ)
  domain_open : IsOpen domain
  f : (Fin n → ℝ) → (Fin (n + 1) → ℝ)
  smooth : ContDiffOn ℝ ⊤ f domain
  immersion : ∀ x ∈ domain, Function.Injective (fderiv ℝ f x)

variable {n : ℕ}

def HypersurfacePatch.partialDeriv (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (i : Fin n) : Fin (n + 1) → ℝ :=
  fderiv ℝ patch.f x (Pi.single i 1)

def generalizedCross {n : ℕ} (v : Fin n → (Fin (n + 1) → ℝ)) :
    Fin (n + 1) → ℝ :=
  fun j => (-1 : ℝ) ^ (j : ℕ) * (Matrix.of (fun (i : Fin n) (k : Fin n) =>
    v i (Fin.succAbove j k))).det

def orientationMatrix (patch : HypersurfacePatch n) (x : Fin n → ℝ)
    (w : Fin (n + 1) → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun (row : Fin (n + 1)) (col : Fin (n + 1)) =>
    if h : col.val < n then
      patch.partialDeriv x ⟨col.val, h⟩ row
    else
      w row

def gaussNormal (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  let crossVec := generalizedCross (patch.partialDeriv x)
  let nrm := Real.sqrt (crossVec ⬝ᵥ crossVec)
  fun j => crossVec j / nrm

noncomputable def firstFundamentalForm (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  let Df := fun i => fderiv ℝ patch.f x (Pi.single i 1)
  Matrix.of (fun i j => (Df i) ⬝ᵥ (Df j))

noncomputable def jacobianMatrix (patch : HypersurfacePatch n) (x : Fin n → ℝ) :
    Matrix (Fin (n + 1)) (Fin n) ℝ :=
  Matrix.of (fun k i => fderiv ℝ patch.f x (Pi.single i 1) k)

lemma firstFundamentalForm_eq_conjTranspose_mul (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) :
    firstFundamentalForm patch x = (jacobianMatrix patch x)ᴴ * (jacobianMatrix patch x) := by
  ext i j
  simp [firstFundamentalForm, jacobianMatrix, mul_apply, of_apply, dotProduct]

lemma jacobian_mulVec_eq_fderiv (patch : HypersurfacePatch n) (x v : Fin n → ℝ) :
    jacobianMatrix patch x *ᵥ v = fderiv ℝ patch.f x v := by
  ext k
  simp only [jacobianMatrix, mulVec, dotProduct, of_apply]
  have hv : v = ∑ i : Fin n, v i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, Finset.mem_univ]
  conv_rhs => rw [hv, map_sum]
  simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem firstFundamentalForm_posDef (patch : HypersurfacePatch n) (x : Fin n → ℝ)
    (hx : x ∈ patch.domain) :
    (firstFundamentalForm patch x).PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos
  · rw [firstFundamentalForm_eq_conjTranspose_mul]
    exact isHermitian_conjTranspose_mul_self _
  · intro v hv
    rw [firstFundamentalForm_eq_conjTranspose_mul, ← mulVec_mulVec,
        dotProduct_mulVec, vecMul_conjTranspose, star_star]
    rw [dotProduct_star_self_pos_iff, jacobian_mulVec_eq_fderiv]
    intro h
    exact hv (patch.immersion x hx (h.trans (map_zero _).symm))

end


open Matrix in
theorem gaussNormal_unit {n : ℕ} (patch : HypersurfacePatch n) (x : Fin n → ℝ)
    (hx : x ∈ patch.domain) :
    Real.sqrt (gaussNormal patch x ⬝ᵥ gaussNormal patch x) = 1 := by sorry


open Matrix in
theorem gaussNormal_orthogonal {n : ℕ} (patch : HypersurfacePatch n) (x : Fin n → ℝ)
    (hx : x ∈ patch.domain) (i : Fin n) :
    gaussNormal patch x ⬝ᵥ patch.partialDeriv x i = 0 := by sorry


theorem gaussNormal_orientation {n : ℕ} (patch : HypersurfacePatch n) (x : Fin n → ℝ)
    (hx : x ∈ patch.domain) :
    (orientationMatrix patch x (gaussNormal patch x)).det > 0 := by sorry

noncomputable def secondFundamentalForm {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun i j =>
    (fderiv ℝ (fderiv ℝ patch.f · (Pi.single j 1)) x (Pi.single i 1)) ⬝ᵥ
    (gaussNormal patch x))

open Matrix in
theorem secondFundamentalForm_symmetric {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) (i j : Fin n) :
    secondFundamentalForm patch x i j = secondFundamentalForm patch x j i := by
  simp only [secondFundamentalForm, of_apply]
  congr 1
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
  exact (hfat.isSymmSndFDerivAt_of_omega).eq (Pi.single i 1) (Pi.single j 1)

noncomputable def shapeOperator {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (firstFundamentalForm patch x)⁻¹ * (secondFundamentalForm patch x)

open Matrix in
def IsPrincipalCurvature {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (κ : ℝ) : Prop :=
  (shapeOperator patch x).charpoly.IsRoot κ

lemma dotProduct_sum_smul {m k : ℕ} (v : Fin k → (Fin m → ℝ)) (a : Fin k → ℝ) (w : Fin m → ℝ) :
    (∑ j, a j • v j) ⬝ᵥ w = ∑ j, a j * (v j ⬝ᵥ w) := by
  simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1; ext k
  rw [Finset.mul_sum]
  congr 1; ext i; ring


theorem gaussNormal_deriv_in_tangent {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) (i : Fin n) :
    ∃ a : Fin n → ℝ, fderiv ℝ (gaussNormal patch) x (Pi.single i 1) =
    ∑ j : Fin n, a j • fderiv ℝ patch.f x (Pi.single j 1) := by sorry


theorem gaussNormal_deriv_dot_partial {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) (i j : Fin n) :
    (fderiv ℝ (gaussNormal patch) x (Pi.single i 1)) ⬝ᵥ
    (fderiv ℝ patch.f x (Pi.single j 1)) =
    -(secondFundamentalForm patch x i j) := by sorry

open Matrix in
theorem gauss_normal_derivative {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) (i : Fin n) :
    fderiv ℝ (gaussNormal patch) x (Pi.single i 1) =
    -∑ j, (shapeOperator patch x) j i • fderiv ℝ patch.f x (Pi.single j 1) := by
  obtain ⟨a, ha⟩ := gaussNormal_deriv_in_tangent patch x hx i

  have hGa : (firstFundamentalForm patch x) *ᵥ a =
      fun j => -(secondFundamentalForm patch x i j) := by
    funext j
    have hW := gaussNormal_deriv_dot_partial patch x hx i j
    rw [ha, dotProduct_sum_smul] at hW
    simp only [mulVec, dotProduct, firstFundamentalForm, of_apply]
    rw [← hW]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    ring

  have hG := firstFundamentalForm_posDef patch x hx
  have hdet : IsUnit (firstFundamentalForm patch x).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit
  have ha_eq : a = (firstFundamentalForm patch x)⁻¹ *ᵥ
      (fun j => -(secondFundamentalForm patch x i j)) := by
    have h := congr_arg ((firstFundamentalForm patch x)⁻¹ *ᵥ ·) hGa
    simp only at h
    rwa [mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, one_mulVec] at h

  have ha_coeff : ∀ k : Fin n, a k = -(shapeOperator patch x k i) := by
    intro k
    have hak : a k = ((firstFundamentalForm patch x)⁻¹ *ᵥ
        (fun j => -(secondFundamentalForm patch x i j))) k := congr_fun ha_eq k
    rw [hak]
    simp only [mulVec, dotProduct, shapeOperator, mul_apply]
    simp_rw [mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    funext j
    rw [secondFundamentalForm_symmetric patch x hx i j]

  rw [ha]
  funext l
  simp only [Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [ha_coeff, neg_mul, ← Finset.sum_neg_distrib]

noncomputable def meanCurvature {n : ℕ} (patch : HypersurfacePatch n) (x : Fin n → ℝ) : ℝ :=
  (shapeOperator patch x).trace

noncomputable def gaussCurvature {n : ℕ} (patch : HypersurfacePatch n) (x : Fin n → ℝ) : ℝ :=
  (shapeOperator patch x).det

noncomputable def scalarCurvature {n : ℕ} (patch : HypersurfacePatch n) (x : Fin n → ℝ) : ℝ :=
  ((shapeOperator patch x).trace ^ 2 - ((shapeOperator patch x) * (shapeOperator patch x)).trace) / 2

theorem rigidity_theorem {n : ℕ} (patch₁ patch₂ : HypersurfacePatch n)
    (hconn : IsConnected patch₁.domain)
    (hdomain : patch₁.domain = patch₂.domain)
    (hG : ∀ x ∈ patch₁.domain,
      firstFundamentalForm patch₁ x = firstFundamentalForm patch₂ x)
    (hH : ∀ x ∈ patch₁.domain,
      secondFundamentalForm patch₁ x = secondFundamentalForm patch₂ x) :
    ∃ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
      (b : Fin (n + 1) → ℝ),
      A ∈ Matrix.orthogonalGroup (Fin (n + 1)) ℝ ∧
      A.det = 1 ∧
      ∀ x ∈ patch₁.domain, patch₂.f x = A.mulVec (patch₁.f x) + b := by sorry

noncomputable section

open Matrix Finset BigOperators

def coordinateJacobian {n : ℕ} (φ : (Fin n → ℝ) → (Fin n → ℝ))
    (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => fderiv ℝ φ x (Pi.single j 1) i

lemma generalizedCross_linear_combination {n : ℕ}
    (v : Fin n → (Fin (n + 1) → ℝ)) (A : Matrix (Fin n) (Fin n) ℝ) :
    generalizedCross (fun i => ∑ j : Fin n, A j i • v j) =
    A.det • generalizedCross v := by
  ext j
  simp only [generalizedCross, Pi.smul_apply, smul_eq_mul]
  ring_nf
  congr 1
  have h : (Matrix.of (fun (i : Fin n) (k : Fin n) =>
      (∑ l : Fin n, A l i • v l) (Fin.succAbove j k))) =
      A.transpose * (Matrix.of (fun (i : Fin n) (k : Fin n) => v i (Fin.succAbove j k))) := by
    ext i k
    simp [mul_apply, transpose_apply, of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [h, det_mul, det_transpose]

theorem gaussNormal_coordinate_change {n : ℕ}
    (patch tildeP : HypersurfacePatch n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ)
    (h_eq : tildeP.f = patch.f ∘ φ)
    (hφ : DifferentiableAt ℝ φ x)
    (hf : DifferentiableAt ℝ patch.f (φ x))
    (hdet_pos : (coordinateJacobian φ x).det > 0) :
    gaussNormal tildeP x = gaussNormal patch (φ x) := by
  have hchain : fderiv ℝ tildeP.f x = (fderiv ℝ patch.f (φ x)).comp (fderiv ℝ φ x) := by
    conv_lhs => rw [h_eq]; exact fderiv_comp x hf hφ
  have hpartials : (fun i => fderiv ℝ tildeP.f x (Pi.single i 1)) =
      (fun i => ∑ k : Fin n, (coordinateJacobian φ x) k i •
        fderiv ℝ patch.f (φ x) (Pi.single k 1)) := by
    ext i
    rw [hchain, ContinuousLinearMap.comp_apply]
    have : (fderiv ℝ φ x (Pi.single i 1) : Fin n → ℝ) =
        ∑ k : Fin n, (fderiv ℝ φ x (Pi.single i 1) k) •
          (Pi.single k (1 : ℝ) : Fin n → ℝ) := by
      ext p; simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    rw [this, map_sum]
    simp only [ContinuousLinearMap.map_smul, coordinateJacobian, of_apply]
  have hpartials2 : tildeP.partialDeriv x =
      (fun i => ∑ k : Fin n, (coordinateJacobian φ x) k i •
        patch.partialDeriv (φ x) k) := by
    unfold HypersurfacePatch.partialDeriv
    exact hpartials
  unfold gaussNormal
  rw [hpartials2, generalizedCross_linear_combination]
  ext j
  simp only [Pi.smul_apply, smul_eq_mul, dotProduct]
  have h1 : ∑ i, (coordinateJacobian φ x).det *
      (generalizedCross (patch.partialDeriv (φ x))) i *
      ((coordinateJacobian φ x).det *
      (generalizedCross (patch.partialDeriv (φ x))) i) =
      (coordinateJacobian φ x).det ^ 2 * ∑ i,
      (generalizedCross (patch.partialDeriv (φ x))) i *
      (generalizedCross (patch.partialDeriv (φ x))) i := by
    rw [Finset.mul_sum]; congr 1; ext i; ring
  rw [h1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (le_of_lt hdet_pos)]
  field_simp

theorem firstFundamentalForm_coordinate_change {n : ℕ}
    (patch tildeP : HypersurfacePatch n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ)
    (h_eq : tildeP.f = patch.f ∘ φ)
    (hφ : DifferentiableAt ℝ φ x)
    (hf : DifferentiableAt ℝ patch.f (φ x)) :
    firstFundamentalForm tildeP x =
    (coordinateJacobian φ x).transpose * firstFundamentalForm patch (φ x) *
      (coordinateJacobian φ x) := by
  have hchain : fderiv ℝ tildeP.f x = (fderiv ℝ patch.f (φ x)).comp (fderiv ℝ φ x) := by
    conv_lhs => rw [h_eq]; exact fderiv_comp x hf hφ
  have expand : ∀ m : Fin n, fderiv ℝ tildeP.f x (Pi.single m 1) =
      ∑ k : Fin n, (fderiv ℝ φ x (Pi.single m 1) k) •
        fderiv ℝ patch.f (φ x) (Pi.single k 1) := by
    intro m
    have h1 : fderiv ℝ tildeP.f x (Pi.single m 1) =
        fderiv ℝ patch.f (φ x) (fderiv ℝ φ x (Pi.single m 1)) := by
      rw [hchain]; rfl
    rw [h1]
    have h2 : (fderiv ℝ φ x (Pi.single m 1) : Fin n → ℝ) =
        ∑ k : Fin n, (fderiv ℝ φ x (Pi.single m 1) k) •
          (Pi.single k (1 : ℝ) : Fin n → ℝ) := by
      ext p; simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    conv_lhs => rw [h2]
    rw [map_sum]
    simp only [ContinuousLinearMap.map_smul]
  ext i j
  simp only [firstFundamentalForm, of_apply, mul_apply, transpose_apply,
             coordinateJacobian, dotProduct, Finset.sum_mul]
  rw [expand i, expand j]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1; ext l
  rw [Finset.sum_comm]
  congr 1; ext k
  congr 1; ext p
  ring

theorem secondFundamentalForm_coordinate_change_of_entries {n : ℕ}
    (patch tildeP : HypersurfacePatch n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ)
    (h_chain : ∀ i j : Fin n, secondFundamentalForm tildeP x i j =
      ∑ k, ∑ l, (coordinateJacobian φ x) k i *
        secondFundamentalForm patch (φ x) k l *
        (coordinateJacobian φ x) l j) :
    secondFundamentalForm tildeP x =
    (coordinateJacobian φ x).transpose * secondFundamentalForm patch (φ x) *
      (coordinateJacobian φ x) := by
  ext i j
  rw [h_chain]
  simp only [mul_apply, transpose_apply, coordinateJacobian, of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]


open Matrix in
theorem secondFundamentalForm_entry_formula {n : ℕ}
    (patch tildeP : HypersurfacePatch n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ)
    (h_eq : tildeP.f = patch.f ∘ φ)
    (hφ_smooth : ContDiffAt ℝ ⊤ φ x)
    (hf_smooth : ContDiffAt ℝ ⊤ patch.f (φ x))
    (hx : x ∈ tildeP.domain)
    (hφx : φ x ∈ patch.domain)
    (hdet_pos : (coordinateJacobian φ x).det > 0)
    (i j : Fin n) :
    secondFundamentalForm tildeP x i j =
      ∑ k, ∑ l, (coordinateJacobian φ x) k i *
        secondFundamentalForm patch (φ x) k l *
        (coordinateJacobian φ x) l j := by sorry

theorem secondFundamentalForm_coordinate_change {n : ℕ}
    (patch tildeP : HypersurfacePatch n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ)
    (h_eq : tildeP.f = patch.f ∘ φ)
    (hφ_smooth : ContDiffAt ℝ ⊤ φ x)
    (hf_smooth : ContDiffAt ℝ ⊤ patch.f (φ x))
    (hx : x ∈ tildeP.domain)
    (hφx : φ x ∈ patch.domain)
    (hdet_pos : (coordinateJacobian φ x).det > 0) :
    secondFundamentalForm tildeP x =
    (coordinateJacobian φ x).transpose * secondFundamentalForm patch (φ x) *
      (coordinateJacobian φ x) := by
  apply secondFundamentalForm_coordinate_change_of_entries
  intro i j
  exact secondFundamentalForm_entry_formula patch tildeP φ x h_eq hφ_smooth hf_smooth hx hφx
    hdet_pos i j

theorem shapeOperator_coordinate_change {n : ℕ}
    (patch tildeP : HypersurfacePatch n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ)
    (hG : firstFundamentalForm tildeP x =
      (coordinateJacobian φ x).transpose * firstFundamentalForm patch (φ x) *
        (coordinateJacobian φ x))
    (hH : secondFundamentalForm tildeP x =
      (coordinateJacobian φ x).transpose * secondFundamentalForm patch (φ x) *
        (coordinateJacobian φ x))
    (hφ_det : IsUnit (coordinateJacobian φ x).det)
    (hG_det : IsUnit (firstFundamentalForm patch (φ x)).det) :
    shapeOperator tildeP x =
    (coordinateJacobian φ x)⁻¹ * shapeOperator patch (φ x) * (coordinateJacobian φ x) := by
  unfold shapeOperator
  rw [hG, hH]
  set Dφ := coordinateJacobian φ x
  set G := firstFundamentalForm patch (φ x)
  set H := secondFundamentalForm patch (φ x)
  have hAt : IsUnit Dφ.transpose.det := by rw [det_transpose]; exact hφ_det
  have hAtBA : IsUnit (Dφ.transpose * G * Dφ).det := by
    rw [det_mul, det_mul, det_transpose]; exact (hφ_det.mul hG_det).mul hφ_det
  have h : Dφ.transpose * G * Dφ * (Dφ⁻¹ * (G⁻¹ * H) * Dφ) = Dφ.transpose * H * Dφ := by
    have : Dφ.transpose * G * Dφ * (Dφ⁻¹ * (G⁻¹ * H) * Dφ) =
        Dφ.transpose * G * (Dφ * Dφ⁻¹) * (G⁻¹ * H) * Dφ := by
      simp only [mul_assoc]
    rw [this, mul_nonsing_inv _ hφ_det]
    simp only [mul_one, mul_assoc]
    rw [← mul_assoc G G⁻¹, mul_nonsing_inv _ hG_det, one_mul]
  have key := congr_arg ((Dφ.transpose * G * Dφ)⁻¹ * ·) h
  simp only at key
  rw [nonsing_inv_mul_cancel_left _ _ hAtBA] at key
  exact key.symm

theorem prop_13_1 {n : ℕ}
    (patch tildeP : HypersurfacePatch n)
    (φ : (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ)
    (h_eq : tildeP.f = patch.f ∘ φ)
    (hφ_smooth : ContDiffAt ℝ ⊤ φ x)
    (hf_smooth : ContDiffAt ℝ ⊤ patch.f (φ x))
    (hx : x ∈ tildeP.domain)
    (hφx : φ x ∈ patch.domain)
    (hdet_pos : (coordinateJacobian φ x).det > 0)
    (hG_det : IsUnit (firstFundamentalForm patch (φ x)).det) :
    gaussNormal tildeP x = gaussNormal patch (φ x) ∧
    firstFundamentalForm tildeP x =
      (coordinateJacobian φ x).transpose * firstFundamentalForm patch (φ x) *
        (coordinateJacobian φ x) ∧
    secondFundamentalForm tildeP x =
      (coordinateJacobian φ x).transpose * secondFundamentalForm patch (φ x) *
        (coordinateJacobian φ x) ∧
    shapeOperator tildeP x =
      (coordinateJacobian φ x)⁻¹ * shapeOperator patch (φ x) * (coordinateJacobian φ x) := by
  have hφ : DifferentiableAt ℝ φ x := hφ_smooth.differentiableAt (by simp)
  have hf : DifferentiableAt ℝ patch.f (φ x) := hf_smooth.differentiableAt (by simp)
  have hφ_det : IsUnit (coordinateJacobian φ x).det := IsUnit.mk0 _ (ne_of_gt hdet_pos)
  have h1 := gaussNormal_coordinate_change patch tildeP φ x h_eq hφ hf hdet_pos
  have h2 := firstFundamentalForm_coordinate_change patch tildeP φ x h_eq hφ hf
  have h3 := secondFundamentalForm_coordinate_change patch tildeP φ x h_eq hφ_smooth hf_smooth
    hx hφx hdet_pos
  have h4 := shapeOperator_coordinate_change patch tildeP φ x h2 h3 hφ_det hG_det
  exact ⟨h1, h2, h3, h4⟩

end

noncomputable section

open Matrix Finset BigOperators

def normalDerivMatrix {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun (row : Fin (n + 1)) (col : Fin (n + 1)) =>
    if h : col.val < n then
      fderiv ℝ (gaussNormal patch) x (Pi.single ⟨col.val, h⟩ 1) row
    else
      gaussNormal patch x row

end

noncomputable section

open Matrix Finset BigOperators

lemma firstFundamentalForm_eq_transpose_mul {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) :
    firstFundamentalForm patch x =
    (jacobianMatrix patch x).transpose * (jacobianMatrix patch x) := by
  have h := firstFundamentalForm_eq_conjTranspose_mul patch x
  rwa [conjTranspose_eq_transpose_of_trivial] at h

theorem shape_operator_parametrization_identification {n : ℕ}
    (patch : HypersurfacePatch n) (x : Fin n → ℝ) (hx : x ∈ patch.domain)
    (X : Fin n → ℝ) :
    jacobianMatrix patch x *ᵥ (shapeOperator patch x *ᵥ X) =
    -(fderiv ℝ (gaussNormal patch) x X) := by

  have hX : X = ∑ i : Fin n, X i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]

  conv_lhs => rw [hX]
  rw [mulVec_sum, mulVec_sum]
  simp_rw [mulVec_smul]
  conv_rhs => rw [hX, map_sum]
  simp_rw [(fderiv ℝ (gaussNormal patch) x).map_smul]
  rw [← Finset.sum_neg_distrib]

  congr 1
  funext i

  rw [← smul_neg]
  congr 1

  have hgnd := gauss_normal_derivative patch x hx i
  rw [hgnd, neg_neg]


  have hLei : shapeOperator patch x *ᵥ (Pi.single i (1 : ℝ) : Fin n → ℝ) =
      fun j => shapeOperator patch x j i := by
    ext j
    simp [mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ]
  rw [hLei]

  have hcol : (fun j => shapeOperator patch x j i) =
      ∑ j : Fin n, shapeOperator patch x j i • (Pi.single j (1 : ℝ) : Fin n → ℝ) := by
    ext k
    simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
          Finset.sum_ite_eq', Finset.mem_univ]
  rw [hcol, mulVec_sum]
  congr 1; funext j
  rw [mulVec_smul, jacobian_mulVec_eq_fderiv]

theorem firstFundamentalForm_eq_transpose_mul_and_shapeOperator_intertwine {n : ℕ}
    (patch : HypersurfacePatch n) (x : Fin n → ℝ) (hx : x ∈ patch.domain) :
    firstFundamentalForm patch x =
      (jacobianMatrix patch x).transpose * (jacobianMatrix patch x) ∧
    ∀ X : Fin n → ℝ, jacobianMatrix patch x *ᵥ (shapeOperator patch x *ᵥ X) =
      -(fderiv ℝ (gaussNormal patch) x X) :=
  ⟨firstFundamentalForm_eq_transpose_mul patch x,
   fun X => shape_operator_parametrization_identification patch x hx X⟩

end

noncomputable section

open Matrix Finset BigOperators

lemma dotProduct_self_eq_one_of_sqrt_eq_one {n : ℕ} (ν : Fin (n + 1) → ℝ)
    (h : Real.sqrt (ν ⬝ᵥ ν) = 1) : ν ⬝ᵥ ν = 1 := by
  have hnn : (0 : ℝ) ≤ ν ⬝ᵥ ν := by
    simp only [dotProduct]
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (ν i))
  nlinarith [Real.sq_sqrt hnn]

lemma orientationMatrix_transpose_mul_block {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) :
    ((orientationMatrix patch x (gaussNormal patch x)).transpose *
     (orientationMatrix patch x (gaussNormal patch x))).submatrix
      finSumFinEquiv finSumFinEquiv =
    fromBlocks (firstFundamentalForm patch x) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
  set ν := gaussNormal patch x
  have horth : ∀ i : Fin n, ν ⬝ᵥ (patch.partialDeriv x i) = 0 :=
    gaussNormal_orthogonal patch x hx
  have hnorm : ν ⬝ᵥ ν = 1 :=
    dotProduct_self_eq_one_of_sqrt_eq_one ν (gaussNormal_unit patch x hx)
  ext (i | i) (j | j)
  ·
    simp only [submatrix, mul_apply, transpose_apply, orientationMatrix, of_apply,
               finSumFinEquiv_apply_left, Fin.val_castAdd, fromBlocks_apply₁₁]
    have hi : (i : ℕ) < n := i.isLt
    have hj : (j : ℕ) < n := j.isLt
    simp only [hi, hj, dite_true, firstFundamentalForm, of_apply, dotProduct,
               HypersurfacePatch.partialDeriv]
  ·
    simp only [submatrix, mul_apply, transpose_apply, orientationMatrix, of_apply,
               finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
               Fin.val_castAdd, Fin.val_natAdd, fromBlocks_apply₁₂]
    have hi : (i : ℕ) < n := i.isLt
    have hj : ¬ (n + (j : ℕ) < n) := by omega
    simp only [hi, dite_true, hj, dite_false]
    change (patch.partialDeriv x ⟨i.val, hi⟩) ⬝ᵥ ν = 0
    rw [dotProduct_comm]
    exact horth ⟨i.val, hi⟩
  ·
    simp only [submatrix, mul_apply, transpose_apply, orientationMatrix, of_apply,
               finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
               Fin.val_castAdd, Fin.val_natAdd, fromBlocks_apply₂₁]
    have hi : ¬ (n + (i : ℕ) < n) := by omega
    have hj : (j : ℕ) < n := j.isLt
    simp only [hi, dite_false, hj, dite_true]
    change ν ⬝ᵥ (patch.partialDeriv x ⟨j.val, hj⟩) = 0
    exact horth ⟨j.val, hj⟩
  ·
    simp only [submatrix, mul_apply, transpose_apply, orientationMatrix, of_apply,
               finSumFinEquiv_apply_right, Fin.val_natAdd, fromBlocks_apply₂₂]
    have hi : ¬ (n + (i : ℕ) < n) := by omega
    have hj : ¬ (n + (j : ℕ) < n) := by omega
    simp only [hi, dite_false, hj, dite_false]
    change ν ⬝ᵥ ν = (1 : Matrix (Fin 1) (Fin 1) ℝ) i j
    fin_cases i; fin_cases j; simp [hnorm]

theorem orientationMatrix_det_eq_sqrt_det_G {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) :
    (orientationMatrix patch x (gaussNormal patch x)).det =
    Real.sqrt (firstFundamentalForm patch x).det := by
  set M := orientationMatrix patch x (gaussNormal patch x)
  have hpos : M.det > 0 := gaussNormal_orientation patch x hx

  have h_sq_eq_prod : M.det ^ 2 = (M.transpose * M).det := by
    rw [det_mul, det_transpose]; ring

  have h_block : (M.transpose * M).det = (firstFundamentalForm patch x).det := by
    have hsub : (M.transpose * M).det =
        ((M.transpose * M).submatrix finSumFinEquiv finSumFinEquiv).det := by
      rw [det_submatrix_equiv_self]
    rw [hsub, orientationMatrix_transpose_mul_block patch x hx, det_fromBlocks_zero₁₂]
    simp

  have h_sq : M.det ^ 2 = (firstFundamentalForm patch x).det := by linarith
  rw [← h_sq, Real.sqrt_sq (le_of_lt hpos)]

lemma det_gram_eq_cross_dotProduct_self (v : Fin 2 → (Fin 3 → ℝ)) :
    (Matrix.of (fun i j : Fin 2 => (v i) ⬝ᵥ (v j))).det =
    (generalizedCross v) ⬝ᵥ (generalizedCross v) := by
  have hc : generalizedCross v = ![v 0 1 * v 1 2 - v 0 2 * v 1 1,
                                     -(v 0 0 * v 1 2 - v 0 2 * v 1 0),
                                     v 0 0 * v 1 1 - v 0 1 * v 1 0] := by
    ext j
    fin_cases j <;> simp [generalizedCross, det_fin_two, of_apply, Fin.succAbove,
      Fin.castSucc, Fin.succ, Fin.lt_def]
  rw [hc]
  simp [det_fin_two, of_apply, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end

noncomputable section

open Matrix Finset BigOperators

def shapeOperatorLinkingMatrix {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun (row col : Fin (n + 1)) =>
    if hr : row.val < n then
      if hc : col.val < n then
        -(shapeOperator patch x ⟨row.val, hr⟩ ⟨col.val, hc⟩)
      else 0
    else
      if _hc : col.val < n then 0 else 1

lemma shapeOperatorLinkingMatrix_det {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) :
    (shapeOperatorLinkingMatrix patch x).det =
    (-1 : ℝ) ^ n * (shapeOperator patch x).det := by
  have heq : shapeOperatorLinkingMatrix patch x =
    ((Matrix.reindex finSumFinEquiv finSumFinEquiv)
      (Matrix.fromBlocks (-(shapeOperator patch x)) 0 0 (1 : Matrix (Fin 1) (Fin 1) ℝ))) := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [shapeOperatorLinkingMatrix, of_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply]
    by_cases hin : i < n <;> by_cases hjn : j < n
    · simp only [hin, hjn, dite_true]
      show -(shapeOperator patch x) ⟨i, hin⟩ ⟨j, hjn⟩ =
        Matrix.fromBlocks (-(shapeOperator patch x)) 0 0 1
          (finSumFinEquiv.symm ⟨i, hi⟩) (finSumFinEquiv.symm ⟨j, hj⟩)
      simp [finSumFinEquiv, Fin.addCases, hin, hjn, Fin.castLT, Matrix.fromBlocks]
    · simp only [hin, hjn, dite_true, dite_false]
      show (0 : ℝ) = Matrix.fromBlocks (-(shapeOperator patch x)) 0 0 1
        (finSumFinEquiv.symm ⟨i, hi⟩) (finSumFinEquiv.symm ⟨j, hj⟩)
      simp [finSumFinEquiv, Fin.addCases, hin, hjn, Fin.castLT, Fin.subNat, Matrix.fromBlocks]
    · simp only [hin, hjn, dite_false, dite_true]
      show (0 : ℝ) = Matrix.fromBlocks (-(shapeOperator patch x)) 0 0 1
        (finSumFinEquiv.symm ⟨i, hi⟩) (finSumFinEquiv.symm ⟨j, hj⟩)
      simp [finSumFinEquiv, Fin.addCases, hin, hjn, Fin.castLT, Fin.subNat, Matrix.fromBlocks]
    · simp only [hin, hjn, dite_false]
      show (1 : ℝ) = Matrix.fromBlocks (-(shapeOperator patch x)) 0 0 1
        (finSumFinEquiv.symm ⟨i, hi⟩) (finSumFinEquiv.symm ⟨j, hj⟩)
      simp [finSumFinEquiv, Fin.addCases, hin, hjn, Fin.castLT, Fin.subNat,
        Matrix.fromBlocks, Matrix.one_apply]
      omega
  rw [heq, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg,
    Fintype.card_fin, Matrix.det_one, mul_one]


theorem normalDerivMatrix_eq_mul {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) :
    normalDerivMatrix patch x =
    orientationMatrix patch x (gaussNormal patch x) * shapeOperatorLinkingMatrix patch x := by sorry

theorem gaussCurvature_normal_formula {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) :
    gaussCurvature patch x = (-1 : ℝ) ^ n *
      (normalDerivMatrix patch x).det / Real.sqrt (firstFundamentalForm patch x).det := by
  have hfactor : (normalDerivMatrix patch x).det =
      (orientationMatrix patch x (gaussNormal patch x)).det *
      (shapeOperatorLinkingMatrix patch x).det := by
    rw [normalDerivMatrix_eq_mul patch x hx, Matrix.det_mul]
  have horient := orientationMatrix_det_eq_sqrt_det_G patch x hx
  have hlink := shapeOperatorLinkingMatrix_det patch x
  have hPD : (firstFundamentalForm patch x).PosDef := firstFundamentalForm_posDef patch x hx
  have hdetG_pos : (0 : ℝ) < (firstFundamentalForm patch x).det :=
    Matrix.PosDef.det_pos hPD

  have hsqrt_ne : Real.sqrt (firstFundamentalForm patch x).det ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr hdetG_pos)
  unfold gaussCurvature
  rw [hfactor, horient, hlink]
  have h1 : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    rw [sq, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  have h2 : (shapeOperator patch x).det * ((-1:ℝ)^n)^2 = (shapeOperator patch x).det := by
    rw [h1, mul_one]
  field_simp
  linarith

end

def IsCompactHypersurface {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin (n + 1)))) : Prop :=
  IsCompact M
