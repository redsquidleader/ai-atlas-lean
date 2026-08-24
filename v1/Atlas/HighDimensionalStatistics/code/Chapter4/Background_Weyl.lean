/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter4.Def_4_1

open Matrix Real Finset

noncomputable section

/-- An SVD is *ordered* when its singular values are listed in nonincreasing order. -/
def SVD.IsOrdered {d T : ℕ} (S : SVD d T) : Prop :=
  ∀ i j : Fin S.r, i ≤ j → S.σval j ≤ S.σval i

/-- The SVD's recorded singular values coincide with the true (mathlib-defined)
singular values of the linear map associated to `A`. -/
def SVD.HasTrueSingularValues {d T : ℕ} (S : SVD d T)
    (A : Matrix (Fin d) (Fin T) ℝ) : Prop :=
  ∀ k : Fin S.r, S.σval k = (toEuclideanLin A).singularValues k.val

/-- The operator norm is symmetric under swapping the arguments of a subtraction:
$\|B - A\|_{op} = \|A - B\|_{op}$. -/
lemma matrixOpNorm_neg_sub {d T : ℕ} (A B : Matrix (Fin d) (Fin T) ℝ) :
    matrixOpNorm (B - A) = matrixOpNorm (A - B) := by
  unfold matrixOpNorm
  rw [show B - A = -(A - B) from (neg_sub A B).symm, map_neg,
      show (-toEuclideanLin (A - B)).toContinuousLinearMap =
           -(toEuclideanLin (A - B)).toContinuousLinearMap from map_neg _ _,
      ContinuousLinearMap.opNorm_neg]

/-- **Weyl's bound on singular values.** For any matrices `A` and `B`,
$\sigma_k(A) \le \sigma_k(B) + \|A - B\|_{op}$. -/
theorem weyl_singular_values_bound {d T : ℕ}
    (A B : Matrix (Fin d) (Fin T) ℝ)
    (k : ℕ) :
    (toEuclideanLin A).singularValues k ≤
    (toEuclideanLin B).singularValues k + matrixOpNorm (A - B) := by sorry

/-- Restatement of Weyl's bound for `SVD`s whose recorded singular values are the true ones. -/
lemma weyl_one_sided {d T : ℕ}
    (A B : Matrix (Fin d) (Fin T) ℝ)
    (S_A : SVD d T) (S_B : SVD d T)
    (hr : S_A.r = S_B.r)
    (hA_true : S_A.HasTrueSingularValues A)
    (hB_true : S_B.HasTrueSingularValues B)
    (k : Fin S_A.r) :
    S_A.σval k ≤ S_B.σval (Fin.cast hr k) + matrixOpNorm (A - B) := by
  rw [hA_true k, hB_true (Fin.cast hr k)]
  simp only [Fin.val_cast]
  exact weyl_singular_values_bound A B k.val

/-- **Weyl's inequality.** The difference of corresponding singular values of `A` and `B`
is bounded in absolute value by the operator norm of `A - B`. -/
theorem weyl_inequality {d T : ℕ}
    (A B : Matrix (Fin d) (Fin T) ℝ)
    (S_A : SVD d T) (S_B : SVD d T)
    (hr : S_A.r = S_B.r)
    (hA_true : S_A.HasTrueSingularValues A)
    (hB_true : S_B.HasTrueSingularValues B)
    (k : Fin S_A.r) :
    |S_A.σval k - S_B.σval (Fin.cast hr k)| ≤ matrixOpNorm (A - B) := by
  rw [abs_le]
  constructor
  ·
    have h := weyl_one_sided B A S_B S_A hr.symm hB_true hA_true (Fin.cast hr k)
    simp only [Fin.cast_cast, Fin.cast_eq_self] at h
    rw [matrixOpNorm_neg_sub] at h
    linarith
  ·
    have h := weyl_one_sided A B S_A S_B hr hA_true hB_true k
    linarith

/-- The maximal Weyl gap, $\max_k |\sigma_k(A) - \sigma_k(B)|$, is bounded by the operator
norm of `A - B`. -/
theorem weyl_inequality_max {d T : ℕ}
    (A B : Matrix (Fin d) (Fin T) ℝ)
    (S_A : SVD d T) (S_B : SVD d T)
    (hr : S_A.r = S_B.r) (hr_pos : 0 < S_A.r)
    (hA_true : S_A.HasTrueSingularValues A)
    (hB_true : S_B.HasTrueSingularValues B) :
    (Finset.univ.sup' ⟨⟨0, hr_pos⟩, Finset.mem_univ _⟩
      (fun k => ‖S_A.σval k - S_B.σval (Fin.cast hr k)‖₊)) ≤
    ‖matrixOpNorm (A - B)‖₊ := by
  apply Finset.sup'_le
  intro k _
  have h := weyl_inequality A B S_A S_B hr hA_true hB_true k
  suffices ‖S_A.σval k - S_B.σval (Fin.cast hr k)‖ ≤ ‖matrixOpNorm (A - B)‖ by
    exact_mod_cast this
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact le_trans h (le_abs_self _)

end
