/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter4.Lemma_4_2
import Mathlib

open MeasureTheory Matrix Real Finset

namespace Rigollet.Chapter4.Thm_4_4

noncomputable section

/-- Squared Frobenius norm, $\sum_{i,j} A_{ij}^2$. -/
def frobeniusNormSq {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin p, (A i j) ^ 2

/-- The squared Frobenius norm is nonnegative. -/
theorem frobeniusNormSq_nonneg {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) :
    0 ≤ frobeniusNormSq A := by
  unfold frobeniusNormSq
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

/-- The squared Frobenius norm of the zero matrix is zero. -/
theorem frobeniusNormSq_zero {m p : ℕ} :
    frobeniusNormSq (0 : Matrix (Fin m) (Fin p) ℝ) = 0 := by
  unfold frobeniusNormSq
  simp [Matrix.zero_apply, sq]

/-- Frobenius (entrywise) inner product of two matrices. -/
def frobeniusInner {m p : ℕ} (A B : Matrix (Fin m) (Fin p) ℝ) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin p, A i j * B i j

/-- Rank-penalized least-squares objective:
$\frac{1}{n}\|Y - X\Theta\|_F^2 + 2\tau^2 \cdot \mathrm{rank}(\Theta)$. -/
def rankPenObjective {n d T : ℕ}
    (Y : Matrix (Fin n) (Fin T) ℝ) (X : Matrix (Fin n) (Fin d) ℝ)
    (τ : ℝ) (Θ : Matrix (Fin d) (Fin T) ℝ) : ℝ :=
  (1 / (n : ℝ)) * frobeniusNormSq (Y - X * Θ) + 2 * τ ^ 2 * (Θ.rank : ℝ)

/-- `Θhat` is a rank-penalized estimator if it minimizes `rankPenObjective`. -/
def IsRankPenalizationEstimator {n d T : ℕ}
    (Y : Matrix (Fin n) (Fin T) ℝ) (X : Matrix (Fin n) (Fin d) ℝ)
    (τ : ℝ) (Θhat : Matrix (Fin d) (Fin T) ℝ) : Prop :=
  ∀ Θ : Matrix (Fin d) (Fin T) ℝ,
    rankPenObjective Y X τ Θhat ≤ rankPenObjective Y X τ Θ

/-- Prediction MSE: $\frac{1}{n}\|X\hat\Theta - X\Theta^*\|_F^2$. -/
def predictionMSE {n d T : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ) (Θhat Θstar : Matrix (Fin d) (Fin T) ℝ) : ℝ :=
  (1 / (n : ℝ)) * frobeniusNormSq (X * Θhat - X * Θstar)

/-- Polarization-style expansion of the squared Frobenius norm of a difference. -/
theorem frobeniusNormSq_sub_eq {m p : ℕ} (A B : Matrix (Fin m) (Fin p) ℝ) :
    frobeniusNormSq (A - B) =
      frobeniusNormSq A + frobeniusNormSq B -
        2 * ∑ i : Fin m, ∑ j : Fin p, A i j * B i j := by
  unfold frobeniusNormSq
  simp only [Matrix.sub_apply]
  have h1 : ∀ i : Fin m, ∑ j : Fin p, (A i j - B i j) ^ 2 =
      (∑ j, A i j ^ 2) + (∑ j, B i j ^ 2) - 2 * (∑ j, A i j * B i j) := by
    intro i
    have : ∀ j, (A i j - B i j) ^ 2 =
        A i j ^ 2 + B i j ^ 2 - 2 * (A i j * B i j) := by intro j; ring
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Adjoint identity for the Frobenius inner product:
$\langle E, X A\rangle_F = \langle X^\top E, A\rangle_F$. -/
theorem frobeniusInner_transpose_mul {n d T : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ) (E : Matrix (Fin n) (Fin T) ℝ)
    (A : Matrix (Fin d) (Fin T) ℝ) :
    frobeniusInner E (X * A) = frobeniusInner (Xᵀ * E) A := by
  simp only [frobeniusInner, Matrix.mul_apply, Matrix.transpose_apply]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  simp_rw [show ∀ (i : Fin n) (j : Fin T) (k : Fin d),
    E i j * (X i k * A k j) = X i k * E i j * A k j from fun i j k => by ring]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  congr 1; ext k
  rw [Finset.sum_comm]

/-- The rank of a difference is bounded by the sum of the ranks. -/
theorem rank_sub_le {m p : ℕ} (A B : Matrix (Fin m) (Fin p) ℝ) :
    (A - B).rank ≤ A.rank + B.rank := by
  have hneg : (-B).rank = B.rank := by
    unfold Matrix.rank
    have h : (-B).mulVecLin = -B.mulVecLin := by ext v; simp
    rw [show (-B).mulVecLin.range = B.mulVecLin.range from by rw [h, LinearMap.range_neg]]
  rw [sub_eq_add_neg]
  calc (A + (-B)).rank
      ≤ A.rank + (-B).rank := by
        unfold Matrix.rank
        have h_range : (A + (-B)).mulVecLin.range ≤
            A.mulVecLin.range ⊔ (-B).mulVecLin.range := by
          intro x hx
          rw [LinearMap.mem_range] at hx
          obtain ⟨v, hv⟩ := hx
          rw [Submodule.mem_sup]
          exact ⟨A.mulVecLin v, LinearMap.mem_range.mpr ⟨v, rfl⟩,
                 (-B).mulVecLin v, LinearMap.mem_range.mpr ⟨v, rfl⟩, by simp [← hv]⟩
        exact (Submodule.finrank_mono h_range).trans
          (Submodule.finrank_add_le_finrank_add_finrank _ _)
    _ = A.rank + B.rank := by rw [hneg]

/-- The rank of $X(\hat\Theta - \Theta^*)$ is bounded by $\mathrm{rank}(\hat\Theta) +
\mathrm{rank}(\Theta^*)$. -/
theorem rank_mul_sub_le_add {n d T : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ)
    (Θhat Θstar : Matrix (Fin d) (Fin T) ℝ) :
    (X * (Θhat - Θstar)).rank ≤ Θhat.rank + Θstar.rank :=
  (Matrix.rank_mul_le_right X _).trans (rank_sub_le _ _)

/-- The Frobenius inner product is homogeneous in its second argument. -/
lemma frobeniusInner_smul_right {m p : ℕ}
    (A B : Matrix (Fin m) (Fin p) ℝ) (c : ℝ) :
    frobeniusInner A (c • B) = c * frobeniusInner A B := by
  simp only [frobeniusInner, Matrix.smul_apply, smul_eq_mul]
  simp_rw [show ∀ (i : Fin m) (j : Fin p),
    A i j * (c * B i j) = c * (A i j * B i j) from fun i j => by ring]
  simp_rw [← Finset.mul_sum]

/-- $\langle A, A\rangle_F = \|A\|_F^2$. -/
lemma frobeniusInner_self {m p : ℕ} (A : Matrix (Fin m) (Fin p) ℝ) :
    frobeniusInner A A = frobeniusNormSq A := by
  simp only [frobeniusInner, frobeniusNormSq]; congr 1; ext i; congr 1; ext j; ring

/-- A matrix with zero squared Frobenius norm has all entries equal to zero. -/
lemma entries_zero_of_frobeniusNormSq_zero {m p : ℕ}
    (B : Matrix (Fin m) (Fin p) ℝ) (hB : frobeniusNormSq B = 0) :
    ∀ i j, B i j = 0 := by
  intro i j
  have h1 : ∀ x ∈ Finset.univ, (0 : ℝ) ≤ ∑ x_1, (B x x_1) ^ 2 :=
    fun x _ => Finset.sum_nonneg fun y _ => sq_nonneg _
  rw [frobeniusNormSq, Finset.sum_eq_zero_iff_of_nonneg h1] at hB
  have h2 : ∑ x_1, (B i x_1) ^ 2 = 0 := hB i (Finset.mem_univ _)
  have h3 : ∀ y ∈ Finset.univ, (0 : ℝ) ≤ (B i y) ^ 2 := fun y _ => sq_nonneg _
  rw [Finset.sum_eq_zero_iff_of_nonneg h3] at h2
  have h4 := h2 j (Finset.mem_univ _)
  exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h4

/-- If `B` has zero Frobenius norm then any inner product with it vanishes. -/
lemma frobeniusInner_zero_of_frobeniusNormSq_zero {m p : ℕ}
    (A B : Matrix (Fin m) (Fin p) ℝ) (hB : frobeniusNormSq B = 0) :
    frobeniusInner A B = 0 := by
  have hB_zero := entries_zero_of_frobeniusNormSq_zero B hB
  simp only [frobeniusInner]
  apply Finset.sum_eq_zero; intro i _
  apply Finset.sum_eq_zero; intro j _
  simp [hB_zero i j]

/-- Left-multiplication by an orthonormal `Φ` (i.e. $\Phi^\top \Phi = I$) preserves the
squared Frobenius norm. -/
lemma frobeniusNormSq_orth_left {n r T : ℕ} (Φ : Matrix (Fin n) (Fin r) ℝ) (hΦ : Φᵀ * Φ = 1)
    (C : Matrix (Fin r) (Fin T) ℝ) :
    frobeniusNormSq (Φ * C) = frobeniusNormSq C := by
  rw [← frobeniusInner_self, ← frobeniusInner_self]
  have h1 := frobeniusInner_transpose_mul Φ (Φ * C) C
  rw [← Matrix.mul_assoc, hΦ, Matrix.one_mul] at h1
  exact h1

/-- **Hölder-type trace inequality.** $\langle A, B\rangle_F^2 \le \|A\|_{op}^2 \cdot
\mathrm{rank}(B) \cdot \|B\|_F^2$, combining Cauchy–Schwarz with a rank bound. -/
theorem holder_trace_rank_bound {m p : ℕ}
    (A : Matrix (Fin m) (Fin p) ℝ) (B : Matrix (Fin m) (Fin p) ℝ) :
    (frobeniusInner A B) ^ 2 ≤
      matrixOpNorm A ^ 2 * (B.rank : ℝ) * frobeniusNormSq B := by sorry

/-- Left-multiplying by `Φ` with $\Phi^\top \Phi = I$ does not decrease rank. -/
lemma rank_le_of_left_inverse_mul {n r T : ℕ}
    (Φ : Matrix (Fin n) (Fin r) ℝ) (hΦ : Φᵀ * Φ = 1)
    (C : Matrix (Fin r) (Fin T) ℝ) :
    C.rank ≤ (Φ * C).rank := by
  have h : C = Φᵀ * (Φ * C) := by rw [← Matrix.mul_assoc, hΦ, Matrix.one_mul]
  calc C.rank = (Φᵀ * (Φ * C)).rank := by rw [← h]
    _ ≤ (Φ * C).rank := Matrix.rank_mul_le_right Φᵀ (Φ * C)

/-- Bound on the inner product $\langle E, \frac{X\Delta}{\|X\Delta\|_F}\rangle^2$ in terms
of $n \tau^2 \cdot \mathrm{rank}(X\Delta)$ via the orthonormal column factor `Φ` of `X`. -/
theorem svd_inner_product_rank_bound
    {n d T r : ℕ}
    (Φ : Matrix (Fin n) (Fin r) ℝ)
    (hΦ_orth : Φᵀ * Φ = 1)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (hX_col : ∃ M : Matrix (Fin r) (Fin d) ℝ, X = Φ * M)
    (E : Matrix (Fin n) (Fin T) ℝ)
    (Δ : Matrix (Fin d) (Fin T) ℝ)
    (τ : ℝ)
    (hΦE_bound : matrixOpNorm (Φᵀ * E) ^ 2 ≤ (n : ℝ) * τ ^ 2)
    (hXΔ_pos : 0 < frobeniusNormSq (X * Δ)) :
    (frobeniusInner E
      ((1 / Real.sqrt (frobeniusNormSq (X * Δ))) • (X * Δ))) ^ 2 ≤
      (n : ℝ) * τ ^ 2 * ((X * Δ).rank : ℝ) := by

  obtain ⟨M_mat, hX⟩ := hX_col
  set C := M_mat * Δ with hC_def
  have hXΔ_eq : X * Δ = Φ * C := by rw [hX, Matrix.mul_assoc]
  rw [hXΔ_eq]
  rw [hXΔ_eq] at hXΔ_pos

  rw [frobeniusInner_smul_right, frobeniusInner_transpose_mul Φ E C]

  rw [mul_pow]

  have hF_pos : 0 < frobeniusNormSq (Φ * C) := hXΔ_pos
  have h_scalar_sq : (1 / Real.sqrt (frobeniusNormSq (Φ * C))) ^ 2 =
      1 / frobeniusNormSq (Φ * C) := by
    rw [div_pow, one_pow, Real.sq_sqrt hF_pos.le]
  rw [h_scalar_sq, frobeniusNormSq_orth_left Φ hΦ_orth C]

  have hC_pos : 0 < frobeniusNormSq C := by
    rwa [← frobeniusNormSq_orth_left Φ hΦ_orth]

  have h_holder := holder_trace_rank_bound (Φᵀ * E) C
  have h_rank := rank_le_of_left_inverse_mul Φ hΦ_orth C
  calc (1 / frobeniusNormSq C) * (frobeniusInner (Φᵀ * E) C) ^ 2
      ≤ (1 / frobeniusNormSq C) *
        (matrixOpNorm (Φᵀ * E) ^ 2 * (C.rank : ℝ) * frobeniusNormSq C) := by
        apply mul_le_mul_of_nonneg_left h_holder; positivity
    _ = matrixOpNorm (Φᵀ * E) ^ 2 * (C.rank : ℝ) := by field_simp
    _ ≤ ((n : ℝ) * τ ^ 2) * ((Φ * C).rank : ℝ) := by
        apply mul_le_mul hΦE_bound (by exact_mod_cast h_rank) (Nat.cast_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    _ = (n : ℝ) * τ ^ 2 * ((Φ * C).rank : ℝ) := by ring

/-- Specialization of `svd_inner_product_rank_bound` to $\Delta = \hat\Theta - \Theta^*$,
yielding a bound in terms of $\mathrm{rank}(\hat\Theta) + \mathrm{rank}(\Theta^*)$. -/
theorem unit_inner_product_svd_bound
    {n d T r : ℕ}
    (Φ : Matrix (Fin n) (Fin r) ℝ)
    (hΦ_orth : Φᵀ * Φ = 1)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (hX_col : ∃ M : Matrix (Fin r) (Fin d) ℝ, X = Φ * M)
    (E : Matrix (Fin n) (Fin T) ℝ)
    (Θhat Θstar : Matrix (Fin d) (Fin T) ℝ)
    (τ : ℝ)
    (hΦE_bound : matrixOpNorm (Φᵀ * E) ^ 2 ≤ (n : ℝ) * τ ^ 2)
    (hXΔ_pos : 0 < frobeniusNormSq (X * Θhat - X * Θstar)) :
    (frobeniusInner E
      ((1 / Real.sqrt (frobeniusNormSq (X * Θhat - X * Θstar))) •
        (X * Θhat - X * Θstar))) ^ 2 ≤
      (n : ℝ) * τ ^ 2 * ((Θhat.rank : ℝ) + (Θstar.rank : ℝ)) := by

  have hXmul : X * Θhat - X * Θstar = X * (Θhat - Θstar) := by
    rw [Matrix.mul_sub]
  rw [hXmul] at hXΔ_pos ⊢
  have h_svd := svd_inner_product_rank_bound Φ hΦ_orth X hX_col E (Θhat - Θstar) τ
    hΦE_bound hXΔ_pos

  have h_rank := rank_mul_sub_le_add X Θhat Θstar

  calc (frobeniusInner E
        ((1 / Real.sqrt (frobeniusNormSq (X * (Θhat - Θstar)))) •
          (X * (Θhat - Θstar)))) ^ 2
      ≤ (n : ℝ) * τ ^ 2 * ((X * (Θhat - Θstar)).rank : ℝ) := h_svd
    _ ≤ (n : ℝ) * τ ^ 2 * ((Θhat.rank : ℝ) + (Θstar.rank : ℝ)) := by
        apply mul_le_mul_of_nonneg_left
        · exact_mod_cast h_rank
        · apply mul_nonneg
          · exact Nat.cast_nonneg _
          · exact sq_nonneg _

/-- Cross-term bound used in the rank-penalization analysis: applies Young's inequality to
combine $\langle E, X\Delta\rangle$ with the rank-based inner product bound. -/
theorem crossterm_svd_bound
    {n d T r : ℕ}
    (Φ : Matrix (Fin n) (Fin r) ℝ)
    (hΦ_orth : Φᵀ * Φ = 1)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (hX_col : ∃ M : Matrix (Fin r) (Fin d) ℝ, X = Φ * M)
    (E : Matrix (Fin n) (Fin T) ℝ)
    (Θhat Θstar : Matrix (Fin d) (Fin T) ℝ)
    (τ : ℝ)
    (hn : 0 < (n : ℝ))
    (hΦE_bound : matrixOpNorm (Φᵀ * E) ^ 2 ≤ (n : ℝ) * τ ^ 2) :
    (2 / (n : ℝ)) * frobeniusInner E (X * Θhat - X * Θstar) ≤
      (1 / (2 * (n : ℝ))) * frobeniusNormSq (X * Θhat - X * Θstar) +
      2 * τ ^ 2 * ((Θhat.rank : ℝ) + (Θstar.rank : ℝ)) := by
  set XΔ := X * Θhat - X * Θstar
  set F := frobeniusNormSq XΔ
  set r := (Θhat.rank : ℝ) + (Θstar.rank : ℝ)

  by_cases hF : F = 0
  ·
    have h_inner_zero := frobeniusInner_zero_of_frobeniusNormSq_zero E XΔ hF
    rw [h_inner_zero, hF]
    simp only [mul_zero, zero_add]
    apply mul_nonneg (mul_nonneg (by positivity) (sq_nonneg _))
    exact add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  ·
    have hF_pos : 0 < F := lt_of_le_of_ne (frobeniusNormSq_nonneg XΔ) (Ne.symm hF)

    set s := Real.sqrt F with hs_def
    have hs_pos : 0 < s := Real.sqrt_pos_of_pos hF_pos

    set U := (1 / s) • XΔ

    have h_decomp : frobeniusInner E XΔ = frobeniusInner E U * s := by
      rw [show U = (1 / s) • XΔ from rfl, frobeniusInner_smul_right]
      field_simp

    set a := frobeniusInner E U


    have h_young : 2 * a * s ≤ 2 * a ^ 2 + (1/2) * s ^ 2 := by
      nlinarith [sq_nonneg (2 * a - s)]

    have hs_sq : s ^ 2 = F := by
      rw [hs_def, Real.sq_sqrt hF_pos.le]

    have h_svd := unit_inner_product_svd_bound Φ hΦ_orth X hX_col E Θhat Θstar τ hΦE_bound hF_pos


    have h_a_sq : a ^ 2 ≤ (n : ℝ) * τ ^ 2 * r := h_svd

    have h_combined_n : 2 * a * s ≤ (1/2) * s ^ 2 + 2 * ((n : ℝ) * τ ^ 2 * r) := by
      have h2 : 2 * a ^ 2 ≤ 2 * ((n : ℝ) * τ ^ 2 * r) :=
        mul_le_mul_of_nonneg_left h_a_sq (by norm_num : (0:ℝ) ≤ 2)
      linarith [h_young]

    calc (2 / (n : ℝ)) * frobeniusInner E XΔ
        = (2 / (n : ℝ)) * (a * s) := by rw [h_decomp]
      _ = (1 / (n : ℝ)) * (2 * a * s) := by ring
      _ ≤ (1 / (n : ℝ)) * ((1/2) * s ^ 2 + 2 * ((n : ℝ) * τ ^ 2 * r)) := by
          apply mul_le_mul_of_nonneg_left h_combined_n
          positivity
      _ = (1 / (2 * (n : ℝ))) * F + 2 * τ ^ 2 * r := by
          rw [hs_sq]; field_simp

/-- Re-export of `crossterm_svd_bound` under the explicit hypothesis $\|\Phi^\top E\|_{op}^2
\le n\tau^2$. -/
theorem crossTermBound_from_opNorm
    {n d T r : ℕ}
    (Φ : Matrix (Fin n) (Fin r) ℝ)
    (hΦ_orth : Φᵀ * Φ = 1)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (hX_col : ∃ M : Matrix (Fin r) (Fin d) ℝ, X = Φ * M)
    (E : Matrix (Fin n) (Fin T) ℝ)
    (Θhat Θstar : Matrix (Fin d) (Fin T) ℝ)
    (τ : ℝ)
    (_hτ_pos : 0 < τ)
    (hn : 0 < (n : ℝ))
    (hΦE_bound : matrixOpNorm (Φᵀ * E) ^ 2 ≤ (n : ℝ) * τ ^ 2) :
    (2 / (n : ℝ)) * frobeniusInner E (X * Θhat - X * Θstar) ≤
      (1 / (2 * (n : ℝ))) * frobeniusNormSq (X * Θhat - X * Θstar) +
      2 * τ ^ 2 * ((Θhat.rank : ℝ) + (Θstar.rank : ℝ)) :=
  crossterm_svd_bound Φ hΦ_orth X hX_col E Θhat Θstar τ hn hΦE_bound

/-- Substituting the true parameter `Θstar` into the minimizer inequality `hRK` produces the
basic inequality used in the analysis of the rank-penalized estimator. -/
theorem minimizer_substituted {n d T : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ)
    (Θstar : Matrix (Fin d) (Fin T) ℝ)
    (E : Matrix (Fin n) (Fin T) ℝ)
    (Y : Matrix (Fin n) (Fin T) ℝ)
    (hY : Y = X * Θstar + E)
    (τ : ℝ)
    (Θhat : Matrix (Fin d) (Fin T) ℝ)
    (hRK : IsRankPenalizationEstimator Y X τ Θhat) :
    (1 / (n : ℝ)) * frobeniusNormSq (E - (X * Θhat - X * Θstar)) +
      2 * τ ^ 2 * (Θhat.rank : ℝ) ≤
    (1 / (n : ℝ)) * frobeniusNormSq E + 2 * τ ^ 2 * (Θstar.rank : ℝ) := by
  have hmin := hRK Θstar
  unfold rankPenObjective at hmin

  have h1 : Y - X * Θhat = E - (X * Θhat - X * Θstar) := by
    rw [hY]; abel

  have h2 : Y - X * Θstar = E := by
    rw [hY]; abel
  rw [h1, h2] at hmin
  exact hmin

/-- Deterministic form of **Theorem 4.4**: on the event $\|\Phi^\top E\|_{op}^2 \le n\tau^2$,
the rank-penalized estimator satisfies $\mathrm{predictionMSE} \le 8 \cdot \mathrm{rank}(\Theta^*)
\cdot \tau^2$. -/
theorem theorem_4_4_deterministic
    {n d T r : ℕ}
    (hn : 0 < (n : ℝ))
    (Φ : Matrix (Fin n) (Fin r) ℝ)
    (hΦ_orth : Φᵀ * Φ = 1)
    (X : Matrix (Fin n) (Fin d) ℝ)
    (hX_col : ∃ M : Matrix (Fin r) (Fin d) ℝ, X = Φ * M)
    (Θstar : Matrix (Fin d) (Fin T) ℝ)
    (E : Matrix (Fin n) (Fin T) ℝ)
    (Y : Matrix (Fin n) (Fin T) ℝ)
    (hY : Y = X * Θstar + E)
    (τ : ℝ) (hτ : 0 < τ)
    (Θhat : Matrix (Fin d) (Fin T) ℝ)
    (hRK : IsRankPenalizationEstimator Y X τ Θhat)
    (hΦE_bound : matrixOpNorm (Φᵀ * E) ^ 2 ≤ (n : ℝ) * τ ^ 2) :
    predictionMSE X Θhat Θstar ≤ 8 * (Θstar.rank : ℝ) * τ ^ 2 := by

  set XΔ := X * Θhat - X * Θstar with hXΔ_def

  have hmin := minimizer_substituted X Θstar E Y hY τ Θhat hRK

  have hexpand := frobeniusNormSq_sub_eq E XΔ

  rw [hexpand] at hmin


  have hn_pos : (0 : ℝ) < (n : ℝ) := hn

  have h_after_cancel :
      (1 / (n : ℝ)) * frobeniusNormSq XΔ ≤
        (2 / (n : ℝ)) * frobeniusInner E XΔ +
        2 * τ ^ 2 * (Θstar.rank : ℝ) - 2 * τ ^ 2 * (Θhat.rank : ℝ) := by


    have h_inner_eq : frobeniusInner E XΔ = ∑ i : Fin n, ∑ j : Fin T, E i j * XΔ i j := rfl

    have hdist : (1 / (n : ℝ)) *
        (frobeniusNormSq E + frobeniusNormSq XΔ -
          2 * frobeniusInner E XΔ) =
        (1 / (n : ℝ)) * frobeniusNormSq E + (1 / (n : ℝ)) * frobeniusNormSq XΔ -
        (2 / (n : ℝ)) * frobeniusInner E XΔ := by ring

    have hmin' : (1 / (n : ℝ)) *
        (frobeniusNormSq E + frobeniusNormSq XΔ -
          2 * frobeniusInner E XΔ) +
        2 * τ ^ 2 * (Θhat.rank : ℝ) ≤
        (1 / (n : ℝ)) * frobeniusNormSq E + 2 * τ ^ 2 * (Θstar.rank : ℝ) := by
      rw [h_inner_eq]; exact hmin
    nlinarith

  have h_cross := crossTermBound_from_opNorm Φ hΦ_orth X hX_col E Θhat Θstar τ hτ hn hΦE_bound


  unfold predictionMSE
  rw [show X * Θhat - X * Θstar = XΔ from rfl]

  have h_combined :
      (1 / (n : ℝ)) * frobeniusNormSq XΔ ≤
        (1 / (2 * (n : ℝ))) * frobeniusNormSq XΔ +
        4 * τ ^ 2 * (Θstar.rank : ℝ) := by
    calc (1 / (n : ℝ)) * frobeniusNormSq XΔ
        ≤ (2 / (n : ℝ)) * frobeniusInner E XΔ +
          2 * τ ^ 2 * (Θstar.rank : ℝ) - 2 * τ ^ 2 * (Θhat.rank : ℝ) := h_after_cancel
      _ ≤ ((1 / (2 * (n : ℝ))) * frobeniusNormSq XΔ +
          2 * τ ^ 2 * ((Θhat.rank : ℝ) + (Θstar.rank : ℝ))) +
          2 * τ ^ 2 * (Θstar.rank : ℝ) - 2 * τ ^ 2 * (Θhat.rank : ℝ) := by
            linarith [h_cross]
      _ = (1 / (2 * (n : ℝ))) * frobeniusNormSq XΔ +
          4 * τ ^ 2 * (Θstar.rank : ℝ) := by ring


  have h_frob_nn := frobeniusNormSq_nonneg XΔ


  have h_diff : (1 / (n : ℝ)) * frobeniusNormSq XΔ - (1 / (2 * (n : ℝ))) * frobeniusNormSq XΔ =
      (1 / (2 * (n : ℝ))) * frobeniusNormSq XΔ := by field_simp; ring
  have h_half : (1 / (2 * (n : ℝ))) * frobeniusNormSq XΔ ≤ 4 * τ ^ 2 * (Θstar.rank : ℝ) := by
    linarith
  have h_double : (1 / (n : ℝ)) * frobeniusNormSq XΔ =
      2 * ((1 / (2 * (n : ℝ))) * frobeniusNormSq XΔ) := by field_simp
  linarith

/-- Rate translation: with the canonical choice of threshold $\tau_0$, the rank-penalized
prediction MSE bound is at most $256 \log 12 \cdot \sigma_0 \cdot r \cdot (D + L)$. -/
theorem theorem_4_4_rate_bound
    (σ₀ : ℝ) (hσ₀ : 0 ≤ σ₀)
    (D : ℝ) (hD : 0 ≤ D)
    (L : ℝ) (hL : 0 ≤ L)
    (r : ℝ) (hr : 0 ≤ r) :
    let τ₀ := 4 * Real.sqrt σ₀ * Real.sqrt (Real.log 12 * D) +
              2 * Real.sqrt σ₀ * Real.sqrt (2 * L)
    8 * r * τ₀ ^ 2 ≤ 256 * Real.log 12 * σ₀ * r * (D + L) := by
  set τ₀ := 4 * Real.sqrt σ₀ * Real.sqrt (Real.log 12 * D) +
            2 * Real.sqrt σ₀ * Real.sqrt (2 * L)
  set a := 4 * Real.sqrt σ₀ * Real.sqrt (Real.log 12 * D) with ha_def
  set b := 2 * Real.sqrt σ₀ * Real.sqrt (2 * L) with hb_def
  have hlog12 : (0 : ℝ) ≤ Real.log 12 := (Real.log_pos (by norm_num : (1:ℝ) < 12)).le
  have ha_nn : 0 ≤ a := by positivity
  have hb_nn : 0 ≤ b := by positivity

  have hab_sq : τ₀ ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
    have h : τ₀ = a + b := rfl
    nlinarith [sq_nonneg (a - b)]

  have ha_sq : a ^ 2 = 16 * σ₀ * (Real.log 12 * D) := by
    rw [ha_def, mul_pow, mul_pow, Real.sq_sqrt hσ₀,
        Real.sq_sqrt (mul_nonneg hlog12 hD)]
    ring

  have hb_sq : b ^ 2 = 8 * σ₀ * L := by
    rw [hb_def, mul_pow, mul_pow, Real.sq_sqrt hσ₀,
        Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hL)]
    ring


  have hlog12_half : (1 : ℝ) / 2 ≤ Real.log 12 := by
    have h1 : Real.log 2 ≤ Real.log 12 :=
      Real.log_le_log (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≤ 12)
    linarith [Real.log_two_gt_d9]
  calc 8 * r * τ₀ ^ 2
      ≤ 8 * r * (2 * (a ^ 2 + b ^ 2)) :=
        mul_le_mul_of_nonneg_left hab_sq (by positivity)
    _ = 8 * r * (2 * (16 * σ₀ * (Real.log 12 * D) + 8 * σ₀ * L)) := by
        rw [ha_sq, hb_sq]
    _ = 256 * Real.log 12 * σ₀ * r * D + 128 * σ₀ * r * L := by ring
    _ ≤ 256 * Real.log 12 * σ₀ * r * D + 256 * Real.log 12 * σ₀ * r * L := by
        have hσrL : 0 ≤ σ₀ * r * L := by positivity
        have : 128 * σ₀ * r * L ≤ 256 * Real.log 12 * σ₀ * r * L := by
          have h : (128 : ℝ) ≤ 256 * Real.log 12 := by nlinarith [hlog12_half]
          calc 128 * σ₀ * r * L = 128 * (σ₀ * r * L) := by ring
            _ ≤ (256 * Real.log 12) * (σ₀ * r * L) :=
                mul_le_mul_of_nonneg_right h hσrL
            _ = 256 * Real.log 12 * σ₀ * r * L := by ring
        linarith
    _ = 256 * Real.log 12 * σ₀ * r * (D + L) := by ring

/-- **Theorem 4.4** (rank penalization, high-probability form). Under the sub-Gaussian
matrix model and a suitable choice of threshold $\tau$, the rank-penalized estimator's
prediction MSE exceeds $8 \cdot \mathrm{rank}(\Theta^*) \cdot \tau^2$ with probability at most
$\delta$. -/
theorem theorem_4_4_with_probability
    {n d T r : ℕ}
    (hn : 0 < (n : ℝ))
    (Φ : Matrix (Fin n) (Fin r) ℝ)
    (hΦ_orth : Φᵀ * Φ = 1)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [hprob : IsProbabilityMeasure μ]
    (X : Matrix (Fin n) (Fin d) ℝ)
    (hX_col : ∃ M : Matrix (Fin r) (Fin d) ℝ, X = Φ * M)
    (Θstar : Matrix (Fin d) (Fin T) ℝ)
    (E : Ω → Matrix (Fin n) (Fin T) ℝ)
    (Y : Ω → Matrix (Fin n) (Fin T) ℝ)
    (hY : ∀ ω, Y ω = X * Θstar + E ω)
    (σsq : ℝ) (hσ : 0 < σsq)
    (hE : @IsSubGaussianMatrix Ω _ r T (fun ω => Φᵀ * E ω) σsq μ hprob)
    (hr : 0 < r) (hT : 0 < T)
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (τ : ℝ)
    (hτ_def : τ = 4 * Real.sqrt σsq * Real.sqrt (Real.log 12 * ↑(r ⊔ T)) +
                  2 * Real.sqrt σsq * Real.sqrt (2 * Real.log (1 / δ)))
    (hτ : 0 < τ)
    (Θhat : Ω → Matrix (Fin d) (Fin T) ℝ)
    (hRK : ∀ ω, IsRankPenalizationEstimator (Y ω) X τ (Θhat ω)) :
    μ {ω | predictionMSE X (Θhat ω) Θstar >
        8 * (Θstar.rank : ℝ) * τ ^ 2} ≤
      ENNReal.ofReal δ := by

  have h_containment : {ω | predictionMSE X (Θhat ω) Θstar >
      8 * (Θstar.rank : ℝ) * τ ^ 2} ⊆
      {ω | matrixOpNorm (Φᵀ * E ω) > τ} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢

    by_contra h_not_gt
    push_neg at h_not_gt


    have h_one_le_n : (1 : ℝ) ≤ (n : ℝ) := by
      have h_n_pos : (0 : ℕ) < n := by exact_mod_cast hn
      exact_mod_cast h_n_pos
    have h_sq : matrixOpNorm (Φᵀ * E ω) ^ 2 ≤ (n : ℝ) * τ ^ 2 := by
      have h_nn : (0 : ℝ) ≤ matrixOpNorm (Φᵀ * E ω) := by
        unfold matrixOpNorm; exact norm_nonneg _
      have h1 : matrixOpNorm (Φᵀ * E ω) ^ 2 ≤ τ ^ 2 :=
        pow_le_pow_left₀ h_nn h_not_gt 2
      linarith [sq_nonneg τ, mul_le_mul_of_nonneg_right h_one_le_n (sq_nonneg τ)]
    have h_det := theorem_4_4_deterministic hn Φ hΦ_orth X hX_col Θstar (E ω) (Y ω)
      (hY ω) τ hτ (Θhat ω) (hRK ω) h_sq
    linarith

  have h_op_norm := @lemma_4_2_operator_norm_high_prob r T hr hT Ω _ μ hprob
    (fun ω => Φᵀ * E ω) σsq hσ hE δ hδ_pos hδ_lt

  calc μ {ω | predictionMSE X (Θhat ω) Θstar > 8 * (Θstar.rank : ℝ) * τ ^ 2}
      ≤ μ {ω | matrixOpNorm (Φᵀ * E ω) > τ} := measure_mono h_containment
    _ ≤ ENNReal.ofReal δ := by rw [hτ_def]; exact h_op_norm

end

end Rigollet.Chapter4.Thm_4_4
