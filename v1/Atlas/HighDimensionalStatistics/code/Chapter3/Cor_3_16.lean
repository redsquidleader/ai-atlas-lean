/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter3.Remark_3_1
import Atlas.HighDimensionalStatistics.code.Chapter3.Def_3_10
import Atlas.HighDimensionalStatistics.code.Chapter3.Thm_3_15
import Atlas.HighDimensionalStatistics.code.Chapter3.Lemma_3_14
import Atlas.HighDimensionalStatistics.code.Chapter3.Thm_3_4
import Atlas.HighDimensionalStatistics.code.Chapter3.Thm_3_5
import Atlas.HighDimensionalStatistics.code.Chapter1.Thm_1_6

set_option maxHeartbeats 4800000
set_option maxRecDepth 4096

open Real MeasureTheory

namespace Chapter3

/-- `θhat` is a BIC estimator for the trigonometric model with penalty parameter `τ²`:
for every `ω` it minimizes empirical squared error plus `τ²` times the support size
of the coefficient vector. -/
def IsBICEstimatorTrig {Ω : Type*} {n : ℕ}
    (Y : Ω → Fin n → ℝ) (θhat : Ω → Fin (n - 1) → ℝ) (τsq : ℝ) : Prop :=
  ∀ ω θ,
    (1 / (n : ℝ)) * ∑ i : Fin n,
      (Y ω i - trigLinComb (n - 1) (θhat ω) ((i : ℝ) / (n : ℝ))) ^ 2 +
      τsq * ↑((Finset.univ.filter (fun j => θhat ω j ≠ 0)).card) ≤
    (1 / (n : ℝ)) * ∑ i : Fin n,
      (Y ω i - trigLinComb (n - 1) θ ((i : ℝ) / (n : ℝ))) ^ 2 +
      τsq * ↑((Finset.univ.filter (fun j => θ j ≠ 0)).card)

/-- `θhat` is a Lasso estimator for the trigonometric model with regularization parameter
`τ`: for every `ω` it minimizes empirical squared error plus `2τ` times the `ℓ¹` norm of
the coefficient vector. -/
def IsLassoEstimatorTrig {Ω : Type*} {n : ℕ}
    (Y : Ω → Fin n → ℝ) (θhat : Ω → Fin (n - 1) → ℝ) (τ : ℝ) : Prop :=
  ∀ ω θ,
    (1 / (n : ℝ)) * ∑ i : Fin n,
      (Y ω i - trigLinComb (n - 1) (θhat ω) ((i : ℝ) / (n : ℝ))) ^ 2 +
      2 * τ * ∑ j : Fin (n - 1), |θhat ω j| ≤
    (1 / (n : ℝ)) * ∑ i : Fin n,
      (Y ω i - trigLinComb (n - 1) θ ((i : ℝ) / (n : ℝ))) ^ 2 +
      2 * τ * ∑ j : Fin (n - 1), |θ j|

/-- `θhat` is either a BIC or Lasso estimator with some positive tuning parameter. -/
def IsBICOrLassoEstimator {Ω : Type*} {n : ℕ}
    (Y : Ω → Fin n → ℝ) (θhat : Ω → Fin (n - 1) → ℝ) : Prop :=
  (∃ τsq : ℝ, 0 < τsq ∧ IsBICEstimatorTrig Y θhat τsq) ∨
  (∃ τ : ℝ, 0 < τ ∧ IsLassoEstimatorTrig Y θhat τ)

/-- Reformulating BIC optimality in matrix form via the trigonometric design matrix. -/
lemma IsBICEstimatorTrig_to_matrix_optimality
    {Ω : Type*} {n : ℕ} (hn : 0 < n)
    (Y : Ω → Fin n → ℝ) (θhat : Ω → Fin (n - 1) → ℝ)
    (τsq : ℝ)
    (hBIC : IsBICEstimatorTrig Y θhat τsq) :
    let Φ := trigDesignMatrix n (n - 1)
    ∀ ω θ,
      (1 / (n : ℝ)) * ∑ i : Fin n, (Y ω i - (Φ.mulVec (θhat ω)) i) ^ 2 +
        τsq * ↑((Finset.univ.filter (fun j => θhat ω j ≠ 0)).card) ≤
      (1 / (n : ℝ)) * ∑ i : Fin n, (Y ω i - (Φ.mulVec θ) i) ^ 2 +
        τsq * ↑((Finset.univ.filter (fun j => θ j ≠ 0)).card) := by
  intro Φ ω θ
  have h := hBIC ω θ

  have h_eq_hat : ∀ i : Fin n,
      trigLinComb (n - 1) (θhat ω) ((i : ℝ) / (n : ℝ)) =
      (trigDesignMatrix n (n - 1)).mulVec (θhat ω) i :=
    fun i => trigLinComb_eq_mulVec n (n - 1) hn (θhat ω) i
  have h_eq_θ : ∀ i : Fin n,
      trigLinComb (n - 1) θ ((i : ℝ) / (n : ℝ)) =
      (trigDesignMatrix n (n - 1)).mulVec θ i :=
    fun i => trigLinComb_eq_mulVec n (n - 1) hn θ i
  simp_rw [h_eq_hat, h_eq_θ] at h
  exact h

/-- Reformulating Lasso optimality in matrix form via the trigonometric design matrix. -/
lemma IsLassoEstimatorTrig_to_matrix_optimality
    {Ω : Type*} {n : ℕ} (hn : 0 < n)
    (Y : Ω → Fin n → ℝ) (θhat : Ω → Fin (n - 1) → ℝ)
    (τ : ℝ)
    (hLasso : IsLassoEstimatorTrig Y θhat τ) :
    let Φ := trigDesignMatrix n (n - 1)
    ∀ ω θ,
      (1 / (n : ℝ)) * ∑ i : Fin n, (Y ω i - (Φ.mulVec (θhat ω)) i) ^ 2 +
        2 * τ * ∑ j : Fin (n - 1), |θhat ω j| ≤
      (1 / (n : ℝ)) * ∑ i : Fin n, (Y ω i - (Φ.mulVec θ) i) ^ 2 +
        2 * τ * ∑ j : Fin (n - 1), |θ j| := by
  intro Φ ω θ
  have h := hLasso ω θ
  have h_eq_hat : ∀ i : Fin n,
      trigLinComb (n - 1) (θhat ω) ((i : ℝ) / (n : ℝ)) =
      (trigDesignMatrix n (n - 1)).mulVec (θhat ω) i :=
    fun i => trigLinComb_eq_mulVec n (n - 1) hn (θhat ω) i
  have h_eq_θ : ∀ i : Fin n,
      trigLinComb (n - 1) θ ((i : ℝ) / (n : ℝ)) =
      (trigDesignMatrix n (n - 1)).mulVec θ i :=
    fun i => trigLinComb_eq_mulVec n (n - 1) hn θ i
  simp_rw [h_eq_hat, h_eq_θ] at h
  exact h

/-- Expansion of `∫ (a - b)² dx` as `∫ a² dx + ∫ b² dx - 2 ∫ a b dx`. -/
theorem integral_split_sq_sub
    (a : ℝ → ℝ) (b : ℝ → ℝ)
    (ha : Integrable (fun x => a x ^ 2) (volume.restrict (Set.Icc 0 1)))
    (hb : Integrable (fun x => b x ^ 2) (volume.restrict (Set.Icc 0 1)))
    (hab : Integrable (fun x => a x * b x) (volume.restrict (Set.Icc 0 1))) :
    ∫ x in Set.Icc (0 : ℝ) 1,
      (a x ^ 2 - 2 * a x * b x + b x ^ 2) =
    (∫ x in Set.Icc (0 : ℝ) 1, a x ^ 2) +
    (∫ x in Set.Icc (0 : ℝ) 1, b x ^ 2) -
    2 * (∫ x in Set.Icc (0 : ℝ) 1, a x * b x) := by
  have hab2 : Integrable (fun x => (-2) * (a x * b x)) (volume.restrict (Set.Icc 0 1)) :=
    hab.const_mul (-2)
  have hab' : Integrable (fun x => a x ^ 2 + b x ^ 2) (volume.restrict (Set.Icc 0 1)) :=
    ha.add hb
  have heq : ∀ x, a x ^ 2 - 2 * a x * b x + b x ^ 2 =
    (a x ^ 2 + b x ^ 2) + (-2) * (a x * b x) := by intro x; ring
  simp_rw [heq]
  rw [integral_add hab' hab2]
  rw [integral_add ha hb]
  rw [integral_const_mul]
  ring

/-- A trigonometric linear combination is a continuous function of `x`. -/
lemma trigLinComb_continuous (N : ℕ) (θ : Fin N → ℝ) : Continuous (fun x => trigLinComb N θ x) := by
  unfold trigLinComb
  apply continuous_finset_sum
  intro j _
  exact continuous_const.mul (trigBasis_continuous (j.val + 1))

/-- The squared difference between a trigonometric linear combination and a continuous
function `f` is integrable on `[0,1]`. -/
lemma integrableOn_sq_trigLinComb_sub_f
    {N : ℕ} (f : ℝ → ℝ) (θ : Fin N → ℝ)
    (_hθ : ∀ j : Fin N, θ j = fourierCoeff f (j.val + 1))
    (hf_cont : Continuous f) :
    Integrable (fun x => (trigLinComb N θ x - f x) ^ 2)
      (volume.restrict (Set.Icc 0 1)) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  exact (((trigLinComb_continuous N θ).sub hf_cont).pow 2).continuousOn

/-- The product `(φ_θ_full - f) · φ_θ_tail` is integrable on `[0,1]` for continuous `f`. -/
lemma integrableOn_trigLinComb_sub_f_mul_trigLinComb
    {N : ℕ} (f : ℝ → ℝ) (θ_full θ_tail : Fin N → ℝ)
    (_hθ : ∀ j : Fin N, θ_full j = fourierCoeff f (j.val + 1))
    (hf_cont : Continuous f) :
    Integrable (fun x => (trigLinComb N θ_full x - f x) * trigLinComb N θ_tail x)
      (volume.restrict (Set.Icc 0 1)) := by
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  exact (((trigLinComb_continuous N θ_full).sub hf_cont).mul
    (trigLinComb_continuous N θ_tail)).continuousOn

/-- Orthogonality of cross terms: if `θ_full_j = ⟨f, φ_{j+1}⟩` are the Fourier coefficients,
then `∫₀¹ (φ_{θ_full} - f) · φ_{θ_tail} dx = 0` for any `θ_tail`. -/
theorem L2_cross_term_orthogonal
    {N : ℕ} (f : ℝ → ℝ)
    (θ_full : Fin N → ℝ)
    (θ_tail : Fin N → ℝ)
    (hθ : ∀ j : Fin N, θ_full j = fourierCoeff f (j.val + 1))
    (hf_cont : Continuous f) :
    ∫ x in Set.Icc (0 : ℝ) 1,
      (trigLinComb N θ_full x - f x) * trigLinComb N θ_tail x = 0 := by

  simp only [trigLinComb]


  have h_inner_zero : ∀ j' : Fin N,
      ∫ x in Set.Icc (0 : ℝ) 1,
        ((∑ j : Fin N, θ_full j * trigBasis (↑j + 1) x) - f x) *
        trigBasis (↑j' + 1) x = 0 := by
    intro j'

    have hj'_pos : 0 < (↑j' : ℕ) + 1 := Nat.succ_pos _

    have hA : ∫ x in Set.Icc (0 : ℝ) 1,
        (∑ j : Fin N, θ_full j * trigBasis (↑j + 1) x) * trigBasis (↑j' + 1) x =
        θ_full j' := by

      simp_rw [Finset.sum_mul]
      rw [integral_finset_sum Finset.univ (fun j _ => by
        apply ContinuousOn.integrableOn_compact isCompact_Icc
        apply ContinuousOn.mul
        · exact (continuous_const.mul (trigBasis_continuous _)).continuousOn
        · exact (trigBasis_continuous _).continuousOn)]


      simp_rw [mul_assoc, integral_const_mul]

      simp_rw [trigBasis_L2_orthonormal _ _ (Nat.succ_pos _) hj'_pos]

      simp only [mul_ite, mul_one, mul_zero]

      simp only [Nat.succ_eq_add_one, Nat.add_right_cancel_iff, Fin.val_inj]
      rw [Finset.sum_ite_eq' Finset.univ j' (fun j => θ_full j)]
      simp [Finset.mem_univ]


    have hB : ∫ x in Set.Icc (0 : ℝ) 1, f x * trigBasis (↑j' + 1) x =
        θ_full j' := by
      rw [hθ j']
      rfl

    have h_eq : ∀ x, ((∑ j : Fin N, θ_full j * trigBasis (↑j + 1) x) - f x) *
        trigBasis (↑j' + 1) x =
        (∑ j : Fin N, θ_full j * trigBasis (↑j + 1) x) * trigBasis (↑j' + 1) x -
        f x * trigBasis (↑j' + 1) x := by
      intro x; ring
    simp_rw [h_eq]

    rw [integral_sub
      (by apply ContinuousOn.integrableOn_compact isCompact_Icc
          apply ContinuousOn.mul
          · apply continuousOn_finset_sum; intro j _
            exact (continuous_const.mul (trigBasis_continuous _)).continuousOn
          · exact (trigBasis_continuous _).continuousOn)
      (by apply ContinuousOn.integrableOn_compact isCompact_Icc
          exact (hf_cont.mul (trigBasis_continuous _)).continuousOn)]
    linarith [hA, hB]


  have h_prod_sum : ∀ x : ℝ,
      (∑ j : Fin N, θ_full j * trigBasis (↑j + 1) x - f x) *
      (∑ j : Fin N, θ_tail j * trigBasis (↑j + 1) x) =
      ∑ j' : Fin N, θ_tail j' *
        ((∑ j : Fin N, θ_full j * trigBasis (↑j + 1) x - f x) * trigBasis (↑j' + 1) x) := by
    intro x
    simp_rw [Finset.mul_sum, mul_comm (θ_tail _) _, ← mul_assoc]
  simp_rw [h_prod_sum]
  rw [integral_finset_sum Finset.univ (fun j' _ => by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply ContinuousOn.mul
    · exact continuousOn_const
    · apply ContinuousOn.mul
      · apply ContinuousOn.sub
        · apply continuousOn_finset_sum; intro j _
          exact (continuous_const.mul (trigBasis_continuous _)).continuousOn
        · exact hf_cont.continuousOn
      · exact (trigBasis_continuous _).continuousOn)]
  simp_rw [integral_const_mul, h_inner_zero, mul_zero, Finset.sum_const_zero]

/-- Pythagorean decomposition for truncated Fourier expansions: the squared `L²` distance
between `f` and its Fourier truncation `(θstar_j)_{j<M}` decomposes as the sum of the squared
truncated coefficients (the aliasing/tail term) plus the residual `L²` error from the
full Fourier expansion. -/
theorem L2normSq_truncation_Pythagorean
    {n : ℕ} (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (_hθstar : ∀ j, θstar j = fourierCoeff f j)
    (M : ℕ) (_hM_le : M ≤ n - 1)
    (hf_cont : Continuous f) :
    L2normSq (fun x => trigLinComb (n - 1)
      (fun j : Fin (n - 1) => if (j : ℕ) < M then θstar (j.val + 1) else 0) x - f x) =
      (((Finset.univ : Finset (Fin (n - 1))).filter (fun j : Fin (n - 1) => ¬ (j : ℕ) < M)).sum
        (fun j : Fin (n - 1) => (θstar (j.val + 1)) ^ 2)) +
      L2normSq (fun x => trigLinComb (n - 1)
        (fun j : Fin (n - 1) => θstar (j.val + 1)) x - f x) := by

  set N := n - 1
  set θ_full : Fin N → ℝ := fun j => θstar (j.val + 1)
  set θ_tail : Fin N → ℝ := fun j => if (j : ℕ) < M then 0 else θstar (j.val + 1)
  set θ_trunc : Fin N → ℝ := fun j => if (j : ℕ) < M then θstar (j.val + 1) else 0

  have h_split : ∀ j : Fin N, θ_trunc j = θ_full j - θ_tail j := by
    intro j; simp only [θ_trunc, θ_full, θ_tail]; split_ifs <;> ring
  have h_fn : ∀ x, trigLinComb N θ_trunc x - f x =
      (trigLinComb N θ_full x - f x) - trigLinComb N θ_tail x := by
    intro x; simp only [trigLinComb]
    have : ∑ j : Fin N, θ_trunc j * trigBasis (j.val + 1) x =
        (∑ j : Fin N, θ_full j * trigBasis (j.val + 1) x) -
        ∑ j : Fin N, θ_tail j * trigBasis (j.val + 1) x := by
      rw [← Finset.sum_sub_distrib]
      congr 1; ext j; rw [h_split]; ring
    linarith [this]

  conv_lhs => rw [show (fun x => trigLinComb N θ_trunc x - f x) =
    (fun x => (trigLinComb N θ_full x - f x) - trigLinComb N θ_tail x) from funext h_fn]


  unfold L2normSq

  have h_expand : ∀ x, ((trigLinComb N θ_full x - f x) - trigLinComb N θ_tail x) ^ 2 =
      (trigLinComb N θ_full x - f x) ^ 2 - 2 * (trigLinComb N θ_full x - f x) * trigLinComb N θ_tail x +
      (trigLinComb N θ_tail x) ^ 2 := by
    intro x; ring
  simp_rw [h_expand]

  have hθ_fourier : ∀ j : Fin N, θ_full j = fourierCoeff f (j.val + 1) := by
    intro j; simp [θ_full]; exact _hθstar (j.val + 1)

  have h_int_sq_sub : Integrable (fun x => (trigLinComb N θ_full x - f x) ^ 2)
      (volume.restrict (Set.Icc 0 1)) :=
    integrableOn_sq_trigLinComb_sub_f f θ_full hθ_fourier hf_cont
  have h_int_sq_tail : Integrable (fun x => (trigLinComb N θ_tail x) ^ 2)
      (volume.restrict (Set.Icc 0 1)) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    exact (Continuous.pow (trigLinComb_continuous N θ_tail) 2).continuousOn
  have h_int_cross : Integrable (fun x => (trigLinComb N θ_full x - f x) * trigLinComb N θ_tail x)
      (volume.restrict (Set.Icc 0 1)) :=
    integrableOn_trigLinComb_sub_f_mul_trigLinComb f θ_full θ_tail hθ_fourier hf_cont

  rw [show ∫ x in Set.Icc (0 : ℝ) 1,
      (trigLinComb N θ_full x - f x) ^ 2 -
      2 * (trigLinComb N θ_full x - f x) * trigLinComb N θ_tail x +
      (trigLinComb N θ_tail x) ^ 2 =
    (∫ x in Set.Icc (0 : ℝ) 1, (trigLinComb N θ_full x - f x) ^ 2) +
    (∫ x in Set.Icc (0 : ℝ) 1, (trigLinComb N θ_tail x) ^ 2) -
    2 * (∫ x in Set.Icc (0 : ℝ) 1, (trigLinComb N θ_full x - f x) * trigLinComb N θ_tail x)
    from integral_split_sq_sub _ _ h_int_sq_sub h_int_sq_tail h_int_cross]
  have h_cross : ∫ x in Set.Icc (0 : ℝ) 1,
      (trigLinComb N θ_full x - f x) * trigLinComb N θ_tail x = 0 :=
    L2_cross_term_orthogonal f θ_full θ_tail hθ_fourier hf_cont
  rw [h_cross, mul_zero, sub_zero]

  have h_tail_sq : ∫ x in Set.Icc (0 : ℝ) 1, (trigLinComb N θ_tail x) ^ 2 =
      (Finset.univ.filter (fun j : Fin N => ¬(j : ℕ) < M)).sum
        (fun j : Fin N => (θstar (j.val + 1)) ^ 2) := by


    have := L2_norm_eq_sum_sq N θ_tail
    unfold L2normSq at this
    rw [show (fun x => ∑ j : Fin N, θ_tail j * trigBasis (↑j + 1) x) =
        (fun x => trigLinComb N θ_tail x) from by ext x; simp [trigLinComb]] at this
    rw [this]


    conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j : Fin N => (j : ℕ) < M)]
    simp only [not_lt]
    have h_zero : (Finset.univ.filter (fun j : Fin N => (j : ℕ) < M)).sum
        (fun j => θ_tail j ^ 2) = 0 := by
      apply Finset.sum_eq_zero; intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp [θ_tail, if_pos hj]
    rw [h_zero, zero_add]
    apply Finset.sum_congr
    · ext j; simp
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp [θ_tail, if_neg (not_lt.mpr hj)]
  rw [h_tail_sq]; ring

/-- Tail bound for Fourier coefficients of a Sobolev-class function summed beyond index
`n-1`: `∑_{j ≥ n-1} θstar_j² ≤ Q · (n-1)^{-2β}`. -/
theorem aliasing_tail_L2_bound
    (β : ℝ) (hβ_pos : 0 < β)
    (Q : ℝ) (hQ : 0 < Q)
    (θstar : ℕ → ℝ)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
    {n : ℕ} (hn : 2 ≤ n) :
    ∀ (K : ℕ), ∑ j ∈ Finset.Ico (n - 1) K, (θstar j) ^ 2 ≤
      Q * ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) := by
  intro K
  by_cases hK : n - 1 ≤ K
  ·
    have hM_pos : 0 < (n - 1 : ℕ) := by omega
    have hM_real_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hM_pos

    have hterm : ∀ j ∈ Finset.Ico (n - 1) K,
        (θstar ↑j) ^ 2 ≤ ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) *
          ((sobolevCoeff β (↑j + 1)) ^ 2 * (θstar ↑j) ^ 2) := by
      intro j hj
      simp only [Finset.mem_Ico] at hj
      have hMj : (n - 1 : ℕ) ≤ j := hj.1
      have hw := sobolev_weight_ge_rpow β hβ_pos (n - 1) j hMj

      by_cases hθ : θstar j = 0
      · simp [hθ]
      · have hMpow_pos : 0 < ((n - 1 : ℕ) : ℝ) ^ (2 * β) := rpow_pos_of_pos hM_real_pos _
        rw [rpow_neg hM_real_pos.le, ← div_eq_inv_mul]
        rw [le_div_iff₀ hMpow_pos]
        nlinarith [sq_nonneg (θstar j)]

    calc ∑ j ∈ Finset.Ico (n - 1) K, (θstar j) ^ 2
        ≤ ∑ j ∈ Finset.Ico (n - 1) K, ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) *
            ((sobolevCoeff β (↑j + 1)) ^ 2 * (θstar j) ^ 2) :=
          Finset.sum_le_sum hterm
      _ = ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) *
            ∑ j ∈ Finset.Ico (n - 1) K, (sobolevCoeff β (↑j + 1)) ^ 2 * (θstar j) ^ 2 := by
          rw [← Finset.mul_sum]
      _ ≤ ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) * Q := by
          gcongr


          have hSobK := hSobolev K
          calc ∑ j ∈ Finset.Ico (n - 1) K,
                  (sobolevCoeff β (↑j + 1)) ^ 2 * (θstar j) ^ 2
              ≤ ∑ j ∈ Finset.range K,
                  (sobolevCoeff β (↑j + 1)) ^ 2 * (θstar j) ^ 2 := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro x hx
                  simp only [Finset.mem_Ico] at hx
                  simp only [Finset.mem_range]
                  exact hx.2
                · intros i _ _; exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
            _ = ∑ j : Fin K, (sobolevCoeff β (↑j.val + 1)) ^ 2 * (θstar j.val) ^ 2 := by
                simp only [← Fin.sum_univ_eq_sum_range]
            _ ≤ Q := hSobK

      _ = Q * ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) := by ring

  ·
    push Not at hK

    have : Finset.Ico (n - 1) K = ∅ := Finset.Ico_eq_empty (by omega)
    simp [this]
    apply mul_nonneg
    · linarith
    · apply rpow_nonneg
      exact Nat.cast_nonneg _

/-- Combined statement of Fourier `L²` completeness and summability: the squared and
absolute Fourier coefficients of `f` are summable, and `f` equals its Fourier series
almost everywhere on `[0,1]`. -/
theorem fourier_completeness_and_summability
    (f : ℝ → ℝ)
    (θ : ℕ → ℝ)
    (hθ : ∀ j, θ j = fourierCoeff f j) :
    (Summable (fun j => (θ (j + 1)) ^ 2) ∧ Summable (fun j => θ (j + 1))) ∧
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc (0:ℝ) 1)),
      f x = ∑' j, θ (j + 1) * trigBasis (j + 1) x := by sorry

/-- Parseval identity for truncation: the squared `L²`-error of the `M`-term truncated
Fourier expansion equals `∑_{k ≥ 0} θ_{k+M+1}²`. -/
theorem fourier_truncation_L2_parseval
    (f : ℝ → ℝ)
    (θ : ℕ → ℝ)
    (hθ : ∀ j, θ j = fourierCoeff f j)
    (M : ℕ) :
    L2normSq (fun x => trigLinComb M
      (fun j : Fin M => θ (j.val + 1)) x - f x) =
      ∑' (j : ℕ), (θ (j + M + 1)) ^ 2 := by

  obtain ⟨⟨hSqSum, hAbsSum⟩, hComplete⟩ := fourier_completeness_and_summability f θ hθ

  set θ' : ℕ → ℝ := fun j => θ (j + 1) with hθ'_def

  have hSqSum' : Summable (fun j : ℕ => (θ' j) ^ 2) := hSqSum
  have hAbsSum' : Summable θ' := hAbsSum


  have hSM_eq : ∀ x, trigLinComb M (fun j : Fin M => θ (j.val + 1)) x =
      ∑ j ∈ Finset.range M, θ' j * trigBasis (j + 1) x := by
    intro x
    simp only [trigLinComb, hθ'_def]
    rw [← Fin.sum_univ_eq_sum_range]

  set S := fun x => ∑' j, θ' j * trigBasis (j + 1) x
  set P := fun x => ∑ j ∈ Finset.range M, θ' j * trigBasis (j + 1) x


  have hL2_eq : L2normSq (fun x => trigLinComb M (fun j : Fin M => θ (j.val + 1)) x - f x) =
      L2normSq (fun x => S x - P x) := by
    unfold L2normSq
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hComplete] with x hx
    simp only [hSM_eq x, S, P, hx]
    ring
  rw [hL2_eq]


  have hParseval := parseval_truncation_L2_error θ' M hSqSum' hAbsSum'

  show L2normSq (fun x => S x - P x) = ∑' (j : ℕ), (θ (j + M + 1)) ^ 2
  unfold L2normSq S P
  rw [hParseval]


  rw [show (fun j : ↑(Set.Ici M) => (θ' ↑j) ^ 2) = (fun j : ↑(Set.Ici M) => (θ (↑j + 1)) ^ 2) from rfl]


  let e : ↑(Set.Ici M) ≃ ℕ := {
    toFun := fun ⟨j, hj⟩ => j - M
    invFun := fun k => ⟨k + M, Nat.le_add_left M k⟩
    left_inv := by
      intro ⟨j, hj⟩
      simp only [Set.mem_Ici] at hj
      simp [Nat.sub_add_cancel hj]
    right_inv := by
      intro k
      simp
  }
  rw [← Equiv.tsum_eq e]
  congr 1
  ext ⟨j, hj⟩
  simp only [Set.mem_Ici] at hj
  show (θ (j + 1)) ^ 2 = (θ (j - M + M + 1)) ^ 2
  rw [Nat.sub_add_cancel hj]

/-- `L²` aliasing bound: for `f ∈ Θ(β, Q)`, the `L²`-error of the `(n-1)`-term truncated
Fourier expansion is at most `Q · (n-1)^{-2β}`. -/
theorem L2normSq_aliasing_bound
    (β : ℝ) (hβ_pos : 0 < β)
    (Q : ℝ) (hQ : 0 < Q)
    (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (hθstar : ∀ j, θstar j = fourierCoeff f j)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
    {n : ℕ} (hn : 2 ≤ n) :
    L2normSq (fun x => trigLinComb (n - 1)
      (fun j : Fin (n - 1) => θstar (j.val + 1)) x - f x) ≤
      Q * ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) := by

  rw [fourier_truncation_L2_parseval f θstar hθstar (n - 1)]


  have hrw : (fun j : ℕ => (θstar (j + (n - 1) + 1)) ^ 2) =
      (fun j : ℕ => (θstar (j + n)) ^ 2) := by ext j; congr 2; omega
  rw [hrw]


  have htail := aliasing_tail_L2_bound β hβ_pos Q hQ θstar hSobolev hn
  apply Real.tsum_le_of_sum_range_le
  · intro k; exact sq_nonneg _
  · intro K

    have h1 : ∑ k ∈ Finset.range K, (θstar (k + n)) ^ 2 =
              ∑ j ∈ Finset.Ico n (n + K), (θstar j) ^ 2 := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_left]
      congr 1; ext k; ring_nf
    rw [h1]

    calc ∑ j ∈ Finset.Ico n (n + K), (θstar j) ^ 2
        ≤ ∑ j ∈ Finset.Ico (n - 1) (n + K), (θstar j) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.Ico_subset_Ico (Nat.sub_le n 1) le_rfl
          · intros; exact sq_nonneg _
      _ ≤ Q * ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) := htail (n + K)

/-- Bound on the truncated tail of squared Fourier coefficients: for a Sobolev-class
function, `∑_{M ≤ j < n-1} θstar_{j+1}² ≤ Q · M^{-2β}`. -/
theorem coeff_tail_sq_sum_le_rpow
    (β : ℝ) (hβ_pos : 0 < β)
    (Q : ℝ) (_hQ : 0 < Q)
    (θstar : ℕ → ℝ)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
    {n : ℕ} (_hn : 2 ≤ n)
    (M : ℕ) (hM_pos : 0 < M) (_hM_le : M ≤ n - 1) :
    (((Finset.univ : Finset (Fin (n - 1))).filter (fun j : Fin (n - 1) => ¬ (j : ℕ) < M)).sum
      (fun j : Fin (n - 1) => (θstar (j.val + 1)) ^ 2)) ≤
      Q * (M : ℝ) ^ (-(2 * β)) := by


  have hM_real_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos

  have hterm : ∀ j : Fin (n - 1), ¬(j : ℕ) < M →
      (θstar (j.val + 1)) ^ 2 ≤
      (M : ℝ) ^ (-(2 * β)) * ((sobolevCoeff β (j.val + 2)) ^ 2 * (θstar (j.val + 1)) ^ 2) := by
    intro j hj
    push Not at hj

    have hw := sobolev_weight_ge_rpow β hβ_pos M (j.val + 1) (by omega)

    by_cases hθ : θstar (j.val + 1) = 0
    · simp [hθ]
    · have hMpow_pos : 0 < (M : ℝ) ^ (2 * β) := rpow_pos_of_pos hM_real_pos _
      rw [rpow_neg hM_real_pos.le, ← div_eq_inv_mul]
      rw [le_div_iff₀ hMpow_pos]
      nlinarith [sq_nonneg (θstar (j.val + 1))]


  have hShiftedSum : ((Finset.univ : Finset (Fin (n - 1))).sum
      (fun j : Fin (n - 1) => (sobolevCoeff β (j.val + 2)) ^ 2 * (θstar (j.val + 1)) ^ 2)) ≤ Q := by


    let g := fun k : ℕ => (sobolevCoeff β (k + 1)) ^ 2 * (θstar k) ^ 2
    have hg_nn : ∀ k, 0 ≤ g k := fun k => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    show (Finset.univ : Finset (Fin (n - 1))).sum
        (fun j : Fin (n - 1) => g (j.val + 1)) ≤ Q
    have hSobN : (Finset.univ : Finset (Fin n)).sum (fun j : Fin n => g j.val) ≤ Q :=
      hSobolev n

    rw [Fin.sum_univ_eq_sum_range] at hSobN


    have hconv : (Finset.univ : Finset (Fin (n - 1))).sum (fun j => g (↑j + 1)) =
        ∑ i ∈ Finset.range (n - 1), g (i + 1) := by
      rw [← Fin.sum_univ_eq_sum_range (fun i => g (i + 1))]
    rw [hconv]
    have hn_eq : n = (n - 1) + 1 := by omega
    rw [hn_eq] at hSobN
    rw [Finset.sum_range_succ'] at hSobN
    linarith [hg_nn 0]
  calc (((Finset.univ : Finset (Fin (n - 1))).filter
        (fun j : Fin (n - 1) => ¬(j : ℕ) < M)).sum
        (fun j : Fin (n - 1) => (θstar (j.val + 1)) ^ 2))
      ≤ (((Finset.univ : Finset (Fin (n - 1))).filter
        (fun j : Fin (n - 1) => ¬(j : ℕ) < M)).sum
        (fun j : Fin (n - 1) => (M : ℝ) ^ (-(2 * β)) *
          ((sobolevCoeff β (j.val + 2)) ^ 2 * (θstar (j.val + 1)) ^ 2))) := by
        apply Finset.sum_le_sum
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        exact hterm j hj
    _ = (M : ℝ) ^ (-(2 * β)) *
        (((Finset.univ : Finset (Fin (n - 1))).filter
          (fun j : Fin (n - 1) => ¬(j : ℕ) < M)).sum
          (fun j : Fin (n - 1) => (sobolevCoeff β (j.val + 2)) ^ 2 * (θstar (j.val + 1)) ^ 2)) := by
        rw [← Finset.mul_sum]
    _ ≤ (M : ℝ) ^ (-(2 * β)) * Q := by
        gcongr
        calc (((Finset.univ : Finset (Fin (n - 1))).filter
              (fun j : Fin (n - 1) => ¬(j : ℕ) < M)).sum
              (fun j : Fin (n - 1) => (sobolevCoeff β (j.val + 2)) ^ 2 * (θstar (j.val + 1)) ^ 2))
            ≤ ((Finset.univ : Finset (Fin (n - 1))).sum
              (fun j : Fin (n - 1) => (sobolevCoeff β (j.val + 2)) ^ 2 * (θstar (j.val + 1)) ^ 2)) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · exact Finset.filter_subset _ _
              · intros i _ _
                exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
          _ ≤ Q := hShiftedSum
    _ = Q * (M : ℝ) ^ (-(2 * β)) := by ring

/-- Sobolev approximation bridge: the squared `L²`-error of the `M`-term zero-padded
truncation of the Fourier expansion is bounded by `Q · M^{-2β} + Q · (n-1)^{-2β}`,
combining the truncation Pythagorean decomposition with the coefficient tail bound and
the aliasing bound. -/
theorem L2normSq_truncation_sobolev_bridge
    (β : ℝ) (hβ_pos : 0 < β)
    (Q : ℝ) (hQ : 0 < Q)
    (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (hθstar : ∀ j, θstar j = fourierCoeff f j)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
    {n : ℕ} (hn : 2 ≤ n)
    (M : ℕ) (hM_pos : 0 < M) (hM_le : M ≤ n - 1)
    (hf_cont : Continuous f) :
    L2normSq (fun x => trigLinComb (n - 1)
      (fun j : Fin (n - 1) => if (j : ℕ) < M then θstar (j.val + 1) else 0) x - f x) ≤
      Q * (M : ℝ) ^ (-(2 * β)) + Q * ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) := by

  rw [L2normSq_truncation_Pythagorean f θstar hθstar M hM_le hf_cont]

  have h1 := coeff_tail_sq_sum_le_rpow β hβ_pos Q hQ θstar hSobolev hn M hM_pos hM_le
  have h2 := L2normSq_aliasing_bound β hβ_pos Q hQ f θstar hθstar hSobolev hn
  linarith

open Matrix in
/-- The trigonometric linear combination at grid point `i/n` equals the `i`-th entry of
`(trigDesignMatrix n M).mulVec θ`. -/
lemma trigLinComb_eq_mulVec_apply (n M : ℕ) (hn : 0 < n) (θ : Fin M → ℝ) (i : Fin n) :
    trigLinComb M θ ((i : ℝ) / (n : ℝ)) = (trigDesignMatrix n M).mulVec θ i := by
  simp only [trigLinComb, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  rw [trigDesignMatrix_eq_trigBasis n M hn i j]
  ring

open Matrix in
/-- The empirical squared norm of `φ_θ - f` equals the mean squared error of
`trigDesignMatrix.mulVec θ` against the grid values of `f`. -/
lemma empiricalNormSq_eq_MSE_trigDesign (n : ℕ) (hn : 0 < n) (M : ℕ)
    (θ : Fin M → ℝ) (f : ℝ → ℝ) :
    empiricalNormSq n (fun x => trigLinComb M θ x - f x) =
    Rigollet.Chapter3.MSE_35 ((trigDesignMatrix n M).mulVec θ)
      (fun i => f ((i : ℝ) / (n : ℝ))) := by
  simp only [empiricalNormSq, Rigollet.Chapter3.MSE_35]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [trigLinComb_eq_mulVec_apply n M hn θ i]

/-- Column-norm bound for the trigonometric design matrix: each column has squared
ℓ²-norm at most `n`. -/
theorem trig_design_colnorm_bound
    (n : ℕ) (hn : 2 ≤ n) :
    ∀ j : Fin (n - 1), ∑ i : Fin n, (trigDesignMatrix n (n - 1) i j) ^ 2 ≤ ↑n := by
  intro j

  have h313 := lemma_3_13 n (n - 1) (by omega) (le_refl _)

  have h := congr_fun (congr_fun h313 j) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply] at h
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_one,
    ↓reduceIte] at h


  have key : ∀ i : Fin n, (trigDesignMatrix n (n - 1) i j) ^ 2 =
      trigDesignMatrix n (n - 1) i j * trigDesignMatrix n (n - 1) i j := by
    intro i; ring
  simp_rw [key]
  linarith

/-- A sub-Gaussian noise vector with variance proxy `σ²` yields the Rigollet-form
sub-Gaussian noise statement at the coordinate level. -/
lemma subGaussianNoiseVec_to_subGaussianNoise
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (ε : Ω → Fin n → ℝ) (σ : ℝ) (μ : MeasureTheory.Measure Ω)
    (h : IsSubGaussianNoiseVec ε (σ ^ 2) μ) :
    Rigollet.Chapter3.IsSubGaussianNoise ε σ μ :=
  h.bound

/-- Each coordinate `ε ω i` is sub-Gaussian (in the full Mathlib sense, including
integrability and zero-mean) provided the noise vector has the corresponding properties. -/
theorem subGaussianNoiseVec_to_IsSubGaussian
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    (ε : Ω → Fin n → ℝ) (σ : ℝ) (hσ : 0 < σ)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
    (hMeasε : ∀ i, Measurable (fun ω => ε ω i))
    (hZeroMean : ∀ i, ∫ ω, ε ω i ∂μ = 0) :
    ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) (σ ^ 2) μ := by
  intro i
  exact ⟨hsubG.integ i, hZeroMean i, hsubG.exp_integ i, hsubG.bound i⟩

/-- Pointwise (per-`ω`) "stage B" split oracle inequality for BIC or Lasso estimators:
on the high-probability event, the empirical fit of `θ̂` is bounded by `(1+α)` times any
competitor's fit plus a sparsity-and-noise penalty. -/
theorem bic_or_lasso_trig_split_stageB_pointwise
    {n : ℕ} (hn : 2 ≤ n)
    (f_grid : Fin n → ℝ)
    (Y_val : Fin n → ℝ)
    (ε_val : Fin n → ℝ)
    (hModel : ∀ i, Y_val i = f_grid i + ε_val i)
    (θhat : Fin (n - 1) → ℝ)
    (θ' : Fin (n - 1) → ℝ)
    (σ α δ : ℝ)
    (hσ : 0 < σ) (hα_pos : 0 < α) (hα_lt : α < 1)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)

    (hcol : ∀ j : Fin (n - 1),
      |∑ i : Fin n, ε_val i * (trigDesignMatrix n (n - 1)) i j| ≤
        σ * Real.sqrt (2 * ↑n * Real.log (2 * ↑(n - 1) / δ)))

    {Ω : Type*}
    (Y : Ω → Fin n → ℝ) (θhat_full : Ω → Fin (n - 1) → ℝ)
    (ω : Ω)
    (hEstimator : IsBICOrLassoEstimator Y θhat_full)
    (hY_eq : Y ω = Y_val)
    (hθhat_eq : θhat_full ω = θhat) :
    let Φ := trigDesignMatrix n (n - 1)
    (1 - α) * Rigollet.Chapter3.sqNorm (f_grid - Φ.mulVec θhat) ≤
      (1 + α) * Rigollet.Chapter3.sqNorm (f_grid - Φ.mulVec θ') +
        (1024 * σ ^ 2 * Real.log (Real.exp 1 * ↑(n - 1)) *
          ↑(Rigollet.Chapter3.support_size_35 θ') +
         1024 * σ ^ 2 * Real.log (1 / δ)) / α := by sorry

/-- Probabilistic "stage B" oracle bound: with probability at least `1 - δ`, for every
competitor `θ'`, the BIC/Lasso estimator satisfies the split oracle inequality with
sparsity-and-noise penalty terms. -/
theorem trig_design_split_oracle_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n)
    (f_grid : Fin n → ℝ)
    (ε : Ω → Fin n → ℝ)
    (Y : Ω → Fin n → ℝ)
    (hModel : ∀ ω i, Y ω i = f_grid i + ε ω i)
    (θhat : Ω → Fin (n - 1) → ℝ)
    (σ α δ : ℝ)
    (hσ : 0 < σ) (hα_pos : 0 < α) (hα_lt : α < 1)
    (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
    (hIndep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
    (hMeasε : ∀ i, Measurable (fun ω => ε ω i))
    (hZeroMean : ∀ i, ∫ ω, ε ω i ∂μ = 0)
    (hEstimator : IsBICOrLassoEstimator Y θhat) :
    let Φ := trigDesignMatrix n (n - 1)
    μ {ω | ∀ θ' : Fin (n - 1) → ℝ,
      (1 - α) * Rigollet.Chapter3.sqNorm (f_grid - Φ.mulVec (θhat ω)) ≤
        (1 + α) * Rigollet.Chapter3.sqNorm (f_grid - Φ.mulVec θ') +
          (1024 * σ ^ 2 * Real.log (Real.exp 1 * ↑(n - 1)) *
            ↑(Rigollet.Chapter3.support_size_35 θ') +
           1024 * σ ^ 2 * Real.log (1 / δ)) / α}
    ≥ ENNReal.ofReal (1 - δ) := by
  intro Φ

  have hn_pos : 0 < n := by omega
  have hM_pos : 0 < n - 1 := by omega

  have hsubG_noise : Rigollet.Chapter3.IsSubGaussianNoise ε σ μ :=
    subGaussianNoiseVec_to_subGaussianNoise ε σ μ hsubG
  have hsubG_full : ∀ i : Fin n, IsSubGaussian (fun ω => ε ω i) (σ ^ 2) μ :=
    subGaussianNoiseVec_to_IsSubGaussian ε σ hσ hsubG hMeasε hZeroMean

  have hColNorm : ∀ j : Fin (n - 1), ∑ i : Fin n, (Φ i j) ^ 2 ≤ ↑n :=
    trig_design_colnorm_bound n hn

  set E : Set Ω := {ω | ∀ j : Fin (n - 1),
      |∑ i : Fin n, ε ω i * Φ i j| ≤
        σ * Real.sqrt (2 * ↑n * Real.log (2 * ↑(n - 1) / δ))} with hE_def

  have hE_prob : μ E ≥ ENNReal.ofReal (1 - δ) :=
    Rigollet.Chapter3.refined_concentration_event_no_colnorm
      μ ε Φ σ δ hσ hδ_pos hδ_le hn_pos hM_pos
      hsubG_noise hsubG_full hIndep hMeasε hColNorm

  apply le_trans hE_prob
  apply MeasureTheory.measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro θ'

  exact bic_or_lasso_trig_split_stageB_pointwise hn
    f_grid (Y ω) (ε ω) (hModel ω) (θhat ω) θ'
    σ α δ hσ hα_pos hα_lt hδ_pos hδ_le hω
    Y θhat ω hEstimator rfl rfl

/-- Oracle inequality in MSE form for BIC/Lasso on the trigonometric design: with
probability `≥ 1 - δ`, the MSE of `Φ θ̂` is bounded by `(1+α)/(1-α)` times the oracle MSE
plus a sparsity penalty `s log(n e)/n` and a noise penalty `log(1/δ)/n`. -/
theorem lasso_oracle_trig_design_MSE
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1)
    (σ : ℝ) (hσ : 0 < σ)
    (ε : Ω → Fin n → ℝ)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
    (hIndep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
    (hMeasε : ∀ i, Measurable (fun ω => ε ω i))
    (hZeroMean : ∀ i, ∫ ω, ε ω i ∂μ = 0)
    (Y : Ω → Fin n → ℝ)
    (f_grid : Fin n → ℝ)
    (hModel : ∀ ω i, Y ω i = f_grid i + ε ω i)
    (θhat : Ω → Fin (n - 1) → ℝ)
    (hEstimator : IsBICOrLassoEstimator Y θhat)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) :
    let Φ := trigDesignMatrix n (n - 1)
    μ {ω | ∀ θ : Fin (n - 1) → ℝ,
      Rigollet.Chapter3.MSE_35 (Φ.mulVec (θhat ω)) f_grid ≤
        (1 + α) / (1 - α) *
          Rigollet.Chapter3.MSE_35 (Φ.mulVec θ) f_grid +
        1024 * σ ^ 2 / (α * (1 - α)) * ((↑((Finset.univ.filter (fun j => θ j ≠ 0)).card) : ℝ) *
          Real.log ((n : ℝ) * Real.exp 1) / (n : ℝ)) +
        1024 * σ ^ 2 / (α * (1 - α)) * (Real.log (1 / δ) / (n : ℝ))}
      ≥ ENNReal.ofReal (1 - δ) := by
  intro Φ

  have hn_pos : 0 < n := by omega
  have hM_pos : 0 < n - 1 := by omega
  have hn_real : (0 : ℝ) < ↑n := Nat.cast_pos.mpr hn_pos
  have hM_real : (0 : ℝ) < ↑(n - 1) := Nat.cast_pos.mpr hM_pos

  have hSplit := trig_design_split_oracle_bound hn
    f_grid ε Y hModel θhat σ α δ hσ hα_pos hα_lt hδ_pos hδ_le hsubG hIndep hMeasε hZeroMean hEstimator

  apply le_trans hSplit
  apply MeasureTheory.measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro θ

  have hStageB := hω θ
  have hMSE := Rigollet.Chapter3.tau_to_mse_conversion_split hn_pos hM_pos
    Φ f_grid (θhat ω) θ σ α δ hσ hα_pos hα_lt hδ_pos hδ_le hStageB

  have h1ma : 0 < 1 - α := by linarith
  have hC : 0 < α * (1 - α) := by positivity

  have hlog_mono : Real.log (Real.exp 1 * ↑(n - 1)) ≤ Real.log ((↑n : ℝ) * Real.exp 1) := by
    apply Real.log_le_log
    · positivity
    · have : (↑(n - 1) : ℝ) ≤ (↑n : ℝ) := by
        exact_mod_cast Nat.sub_le n 1
      nlinarith [Real.exp_pos 1]

  have hs_nn : (0 : ℝ) ≤ ↑(Finset.univ.filter (fun j => θ j ≠ 0)).card :=
    Nat.cast_nonneg' _
  calc Rigollet.Chapter3.MSE_35 (Φ.mulVec (θhat ω)) f_grid
      ≤ (1 + α) / (1 - α) * Rigollet.Chapter3.MSE_35 (Φ.mulVec θ) f_grid +
        1024 * σ ^ 2 / (α * (1 - α) * ↑n) *
          ↑(Rigollet.Chapter3.support_size_35 θ) *
          Real.log (Real.exp 1 * ↑(n - 1)) +
        1024 * σ ^ 2 / (α * (1 - α) * ↑n) *
          Real.log (1 / δ) := hMSE
    _ ≤ (1 + α) / (1 - α) * Rigollet.Chapter3.MSE_35 (Φ.mulVec θ) f_grid +
        1024 * σ ^ 2 / (α * (1 - α) * ↑n) *
          ↑(Rigollet.Chapter3.support_size_35 θ) *
          Real.log ((↑n : ℝ) * Real.exp 1) +
        1024 * σ ^ 2 / (α * (1 - α) * ↑n) *
          Real.log (1 / δ) := by
      gcongr
    _ = (1 + α) / (1 - α) * Rigollet.Chapter3.MSE_35 (Φ.mulVec θ) f_grid +
        1024 * σ ^ 2 / (α * (1 - α)) * ((↑(Rigollet.Chapter3.support_size_35 θ) : ℝ) *
          Real.log ((↑n : ℝ) * Real.exp 1) / (↑n : ℝ)) +
        1024 * σ ^ 2 / (α * (1 - α)) * (Real.log (1 / δ) / (↑n : ℝ)) := by
      field_simp
    _ = (1 + α) / (1 - α) * Rigollet.Chapter3.MSE_35 (Φ.mulVec θ) f_grid +
        1024 * σ ^ 2 / (α * (1 - α)) *
        (↑((Finset.univ.filter fun j => θ j ≠ 0).card) * Real.log (↑n * rexp 1) / ↑n) +
        1024 * σ ^ 2 / (α * (1 - α)) * (Real.log (1 / δ) / ↑n) := by
      simp only [Rigollet.Chapter3.support_size_35]

/-- Adapted oracle inequality for BIC/Lasso in empirical-norm form: replaces the MSE on
the design with the empirical `L²` norm of the residual on the uniform grid. -/
theorem adapted_oracle_ineq_trig_empirical
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1)
    (σ : ℝ) (hσ : 0 < σ)
    (ε : Ω → Fin n → ℝ)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
    (hIndep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
    (hMeasε : ∀ i, Measurable (fun ω => ε ω i))
    (hZeroMean : ∀ i, ∫ ω, ε ω i ∂μ = 0)
    (Y : Ω → Fin n → ℝ)
    (f : ℝ → ℝ)
    (hModel : ∀ ω i, Y ω i = f ((i : ℝ) / (n : ℝ)) + ε ω i)
    (θhat : Ω → Fin (n - 1) → ℝ)
    (hEstimator : IsBICOrLassoEstimator Y θhat)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) :
    μ {ω | ∀ θ : Fin (n - 1) → ℝ,
      empiricalNormSq n (fun x => trigLinComb (n - 1) (θhat ω) x - f x) ≤
        (1 + α) / (1 - α) *
          empiricalNormSq n (fun x => trigLinComb (n - 1) θ x - f x) +
        1024 * σ ^ 2 / (α * (1 - α)) * ((↑((Finset.univ.filter (fun j => θ j ≠ 0)).card) : ℝ) *
          Real.log ((n : ℝ) * Real.exp 1) / (n : ℝ)) +
        1024 * σ ^ 2 / (α * (1 - α)) * (Real.log (1 / δ) / (n : ℝ))}
      ≥ ENNReal.ofReal (1 - δ) := by

  have hn_pos : 0 < n := by omega
  set f_grid : Fin n → ℝ := fun i => f ((i : ℝ) / (n : ℝ)) with hf_grid_def

  have h_mse := lasso_oracle_trig_design_MSE hn α hα_pos hα_lt σ hσ ε hsubG hIndep hMeasε hZeroMean Y f_grid hModel
    θhat hEstimator δ hδ_pos hδ_le


  apply le_trans h_mse
  apply MeasureTheory.measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  intro θ

  rw [empiricalNormSq_eq_MSE_trigDesign n hn_pos (n - 1) (θhat ω) f,
      empiricalNormSq_eq_MSE_trigDesign n hn_pos (n - 1) θ f]
  exact hω θ

/-- BIC/Lasso oracle inequality in `L²` form, restricted to a competitor `θ_comp` with
support size at most `M`. -/
theorem bic_lasso_oracle_empirical
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1)
    (σ : ℝ) (hσ : 0 < σ)
    (ε : Ω → Fin n → ℝ)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
    (hIndep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
    (hMeasε : ∀ i, Measurable (fun ω => ε ω i))
    (hZeroMean : ∀ i, ∫ ω, ε ω i ∂μ = 0)
    (Y : Ω → Fin n → ℝ)
    (f : ℝ → ℝ)
    (hModel : ∀ ω i, Y ω i = f ((i : ℝ) / (n : ℝ)) + ε ω i)
    (θhat : Ω → Fin (n - 1) → ℝ)
    (hEstimator : IsBICOrLassoEstimator Y θhat)
    (θ_comp : Fin (n - 1) → ℝ)
    (M : ℕ) (hM_pos : 0 < M) (hM_le : M ≤ n - 1)
    (h_supp : (Finset.univ.filter (fun j => θ_comp j ≠ 0)).card ≤ M)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) :
    μ {ω | L2normSq (fun x => trigLinComb (n - 1) (θhat ω) x - f x) ≤
            (1 + α) / (1 - α) * L2normSq (fun x => trigLinComb (n - 1) θ_comp x - f x) +
            1024 * σ ^ 2 / (α * (1 - α)) * ((M : ℝ) * Real.log ((n : ℝ) * Real.exp 1) / (n : ℝ)) +
            1024 * σ ^ 2 / (α * (1 - α)) * (Real.log (1 / δ) / (n : ℝ))}
      ≥ ENNReal.ofReal (1 - δ) := by sorry

/-- Property ORT for the trigonometric basis: the empirical squared norm of `φ_θ` on the
uniform grid equals its `L²` squared norm. -/
theorem ORT_empirical_eq_L2
    {n : ℕ} (hn : 2 ≤ n)
    (M : ℕ) (hM : M ≤ n - 1)
    (θ : Fin M → ℝ) :
    empiricalNormSq n (fun x => trigLinComb M θ x) =
    L2normSq (fun x => trigLinComb M θ x) := by
  have hn_pos : 0 < n := by omega


  have hORT := ORT_L2_eq_empirical_normSq n M hn_pos hM θ

  unfold empiricalNormSq trigLinComb
  rw [← hORT]

/-- General `L²` form of the BIC/Lasso oracle inequality: identical to the empirical
form with `L²`-norms in place of empirical norms (justified by Property ORT). -/
theorem bic_lasso_oracle_L2_general
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1)
    (σ : ℝ) (hσ : 0 < σ)
    (ε : Ω → Fin n → ℝ)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
    (hIndep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
    (hMeasε : ∀ i, Measurable (fun ω => ε ω i))
    (hZeroMean : ∀ i, ∫ ω, ε ω i ∂μ = 0)
    (Y : Ω → Fin n → ℝ)
    (f : ℝ → ℝ)
    (hModel : ∀ ω i, Y ω i = f ((i : ℝ) / (n : ℝ)) + ε ω i)
    (θhat : Ω → Fin (n - 1) → ℝ)
    (hEstimator : IsBICOrLassoEstimator Y θhat)
    (θ_comp : Fin (n - 1) → ℝ)
    (M : ℕ) (hM_pos : 0 < M) (hM_le : M ≤ n - 1)
    (h_supp : (Finset.univ.filter (fun j => θ_comp j ≠ 0)).card ≤ M)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) :
    μ {ω | L2normSq (fun x => trigLinComb (n - 1) (θhat ω) x - f x) ≤
            (1 + α) / (1 - α) * L2normSq (fun x => trigLinComb (n - 1) θ_comp x - f x) +
            1024 * σ ^ 2 / (α * (1 - α)) * ((M : ℝ) * Real.log ((n : ℝ) * Real.exp 1) / (n : ℝ)) +
            1024 * σ ^ 2 / (α * (1 - α)) * (Real.log (1 / δ) / (n : ℝ))}
      ≥ ENNReal.ofReal (1 - δ) :=
  bic_lasso_oracle_empirical hn α hα_pos hα_lt σ hσ ε hsubG hIndep hMeasε hZeroMean Y f hModel
    θhat hEstimator θ_comp M hM_pos hM_le h_supp δ hδ_pos hδ_le

/-- Simplified form of the BIC/Lasso oracle inequality (with `α = 1/2` and `σ² ≤ 1`):
`‖φ_{θ̂} - f‖²_{L²} ≤ 3 · ‖φ_{θ_comp} - f‖²_{L²} + 4096 M log(n e)/n + 4096 σ² log(1/δ)/n`
with probability `≥ 1 - δ`. -/
theorem bic_lasso_oracle_L2_for_comparison
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n)
    (σ : ℝ) (hσ : 0 < σ) (hσ_le : σ ^ 2 ≤ 1)
    (ε : Ω → Fin n → ℝ)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
    (hIndep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
    (hMeasε : ∀ i, Measurable (fun ω => ε ω i))
    (hZeroMean : ∀ i, ∫ ω, ε ω i ∂μ = 0)
    (Y : Ω → Fin n → ℝ)
    (f : ℝ → ℝ)
    (hModel : ∀ ω i, Y ω i = f ((i : ℝ) / (n : ℝ)) + ε ω i)
    (θhat : Ω → Fin (n - 1) → ℝ)
    (hEstimator : IsBICOrLassoEstimator Y θhat)
    (θ_comp : Fin (n - 1) → ℝ)
    (M : ℕ) (hM_pos : 0 < M) (hM_le : M ≤ n - 1)
    (h_supp : (Finset.univ.filter (fun j => θ_comp j ≠ 0)).card ≤ M)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1) :
    μ {ω | L2normSq (fun x => trigLinComb (n - 1) (θhat ω) x - f x) ≤
            3 * L2normSq (fun x => trigLinComb (n - 1) θ_comp x - f x) +
            4096 * (M : ℝ) * Real.log ((n : ℝ) * Real.exp 1) / (n : ℝ) +
            4096 * σ ^ 2 * Real.log (1 / δ) / (n : ℝ)}
      ≥ ENNReal.ofReal (1 - δ) := by

  have hGeneral := bic_lasso_oracle_L2_general hn
    (1/2 : ℝ) (by norm_num) (by norm_num)
    σ hσ ε hsubG hIndep hMeasε hZeroMean Y f hModel θhat hEstimator θ_comp M hM_pos hM_le h_supp δ hδ_pos hδ_le


  apply le_trans hGeneral
  apply MeasureTheory.measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢

  have h_leading : (1 + (1:ℝ)/2) / (1 - 1/2) = 3 := by norm_num
  have h_coeff : (1024 : ℝ) * σ ^ 2 / ((1:ℝ)/2 * (1 - 1/2)) = 4096 * σ ^ 2 := by ring
  rw [h_leading, h_coeff] at hω


  have hpen_nn : (0 : ℝ) ≤ (↑M * Real.log (↑n * Real.exp 1) / ↑n) := by
    apply div_nonneg
    · apply mul_nonneg (Nat.cast_nonneg M)
      apply Real.log_nonneg
      calc (1 : ℝ) ≤ 2 := by norm_num
        _ ≤ (n : ℝ) := Nat.ofNat_le_cast.mpr hn
        _ = (n : ℝ) * 1 := (mul_one _).symm
        _ ≤ (n : ℝ) * Real.exp 1 := by
          gcongr; exact Real.one_le_exp (by norm_num : (0:ℝ) ≤ 1)
    · exact Nat.cast_nonneg n
  calc L2normSq (fun x => trigLinComb (n - 1) (θhat ω) x - f x)
      ≤ 3 * L2normSq (fun x => trigLinComb (n - 1) θ_comp x - f x) +
        4096 * σ ^ 2 * (↑M * Real.log (↑n * Real.exp 1) / ↑n) +
        4096 * σ ^ 2 * (Real.log (1 / δ) / ↑n) := hω
    _ ≤ 3 * L2normSq (fun x => trigLinComb (n - 1) θ_comp x - f x) +
        4096 * 1 * (↑M * Real.log (↑n * Real.exp 1) / ↑n) +
        4096 * σ ^ 2 * (Real.log (1 / δ) / ↑n) := by
      gcongr
    _ = 3 * L2normSq (fun x => trigLinComb (n - 1) θ_comp x - f x) +
        4096 * ↑M * Real.log (↑n * Real.exp 1) / ↑n +
        4096 * σ ^ 2 * Real.log (1 / δ) / ↑n := by ring

/-- Sobolev approximation bound: there exists an `M`-sparse coefficient vector `θ_comp`
in `Fin (n-1) → ℝ` whose trigonometric expansion approximates `f` in `L²` with squared
error at most `Q (M^{-2β} + (n-1)^{-2β})`. -/
theorem sobolev_approx_L2_bound
    (β : ℝ) (hβ_pos : 0 < β)
    (Q : ℝ) (hQ : 0 < Q)
    (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (hθstar : ∀ j, θstar j = fourierCoeff f j)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
    {n : ℕ} (hn : 2 ≤ n)
    (M : ℕ) (hM_pos : 0 < M) (hM_le : M ≤ n - 1)
    (hf_cont : Continuous f) :
    ∃ (θ_comp : Fin (n - 1) → ℝ),
      (Finset.univ.filter (fun j => θ_comp j ≠ 0)).card ≤ M ∧
      L2normSq (fun x => trigLinComb (n - 1) θ_comp x - f x) ≤
        Q * (M : ℝ) ^ (-(2 * β)) + Q * ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) := by


  refine ⟨fun j => if (j : ℕ) < M then θstar (j.val + 1) else 0, ?_, ?_⟩
  ·
    set S := Finset.univ.filter (fun j : Fin (n - 1) =>
      (if (j : ℕ) < M then θstar (j.val + 1) else 0) ≠ 0)
    set T := Finset.univ.filter (fun j : Fin (n - 1) => (j : ℕ) < M)
    have hST : S ⊆ T := by
      intro j hj
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      by_contra h_not
      simp only [not_lt] at h_not
      simp only [if_neg (by omega : ¬(j : ℕ) < M)] at hj
      exact hj rfl
    have hT : T.card ≤ M := by
      have : T = Finset.univ.image (fun j : Fin M => (⟨j.val, by omega⟩ : Fin (n - 1))) := by
        ext j
        simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hj; exact ⟨⟨j.val, hj⟩, by ext; simp⟩
        · intro ⟨i, hi⟩; rw [← hi]; simp [i.isLt]
      rw [this]
      calc (Finset.univ.image (fun j : Fin M => (⟨j.val, by omega⟩ : Fin (n - 1)))).card
          ≤ (Finset.univ : Finset (Fin M)).card := Finset.card_image_le
        _ = M := Finset.card_fin M
    exact le_trans (Finset.card_le_card hST) hT


  · exact L2normSq_truncation_sobolev_bridge β hβ_pos Q hQ f θstar hθstar hSobolev hn M hM_pos hM_le hf_cont

/-- Combining the sparse oracle inequality with the Sobolev approximation bound: with
probability `≥ 1 - δ`, the BIC/Lasso estimator satisfies
`‖φ_{θ̂} - f‖²_{L²} ≤ 3Q(M^{-2β} + (n-1)^{-2β}) + 4096 M log(n e)/n + 4096 σ² log(1/δ)/n`. -/
theorem sparse_oracle_ORT_sobolev_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n)
    (β : ℝ) (hβ_pos : 0 < β)
    (Q : ℝ) (hQ : 0 < Q)
    (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (hθstar : ∀ j, θstar j = fourierCoeff f j)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
    (σ : ℝ) (hσ : 0 < σ) (hσ_le : σ ^ 2 ≤ 1)
    (ε : Ω → Fin n → ℝ)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
    (hIndep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
    (hMeasε : ∀ i, Measurable (fun ω => ε ω i))
    (hZeroMean : ∀ i, ∫ ω, ε ω i ∂μ = 0)
    (Y : Ω → Fin n → ℝ)
    (hModel : ∀ ω i, Y ω i = f ((i : ℝ) / (n : ℝ)) + ε ω i)
    (θhat : Ω → Fin (n - 1) → ℝ)
    (hEstimator : IsBICOrLassoEstimator Y θhat)
    (M : ℕ) (hM_pos : 0 < M) (hM_le : M ≤ n - 1)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (hf_cont : Continuous f) :
    μ {ω | L2normSq (fun x => trigLinComb (n - 1) (θhat ω) x - f x) ≤
            3 * Q * (M : ℝ) ^ (-(2 * β)) + 3 * Q * ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) +
            4096 * (M : ℝ) * Real.log ((n : ℝ) * Real.exp 1) / (n : ℝ) +
            4096 * σ ^ 2 * Real.log (1 / δ) / (n : ℝ)}
      ≥ ENNReal.ofReal (1 - δ) := by

  obtain ⟨θ_comp, h_supp, h_approx⟩ := sobolev_approx_L2_bound β hβ_pos Q hQ f θstar
    hθstar hSobolev hn M hM_pos hM_le hf_cont

  have hOracle := bic_lasso_oracle_L2_for_comparison hn σ hσ hσ_le ε hsubG hIndep hMeasε hZeroMean Y f hModel
    θhat hEstimator θ_comp M hM_pos hM_le h_supp δ hδ_pos hδ_le

  apply le_trans hOracle
  apply MeasureTheory.measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢


  calc L2normSq (fun x => trigLinComb (n - 1) (θhat ω) x - f x)
      ≤ 3 * L2normSq (fun x => trigLinComb (n - 1) θ_comp x - f x) +
        4096 * (M : ℝ) * Real.log ((n : ℝ) * Real.exp 1) / (n : ℝ) +
        4096 * σ ^ 2 * Real.log (1 / δ) / (n : ℝ) := hω
    _ ≤ 3 * (Q * (M : ℝ) ^ (-(2 * β)) + Q * ((n - 1 : ℕ) : ℝ) ^ (-(2 * β))) +
        4096 * (M : ℝ) * Real.log ((n : ℝ) * Real.exp 1) / (n : ℝ) +
        4096 * σ ^ 2 * Real.log (1 / δ) / (n : ℝ) := by
      gcongr
    _ = 3 * Q * (M : ℝ) ^ (-(2 * β)) + 3 * Q * ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) +
        4096 * (M : ℝ) * Real.log ((n : ℝ) * Real.exp 1) / (n : ℝ) +
        4096 * σ ^ 2 * Real.log (1 / δ) / (n : ℝ) := by
      ring

/-- Integrating an exponential tail bound: if `P(X ≤ A + B log(1/δ)) ≥ 1 - δ` for all
`δ ∈ (0,1]`, then `E[X] ≤ A + B`. -/
theorem tail_integration_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : Ω → ℝ)
    (hMeas : Measurable X)
    (A : ℝ) (hA_pos : 0 < A)
    (B : ℝ) (hB_pos : 0 < B)
    (hTail : ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
      μ {ω | X ω ≤ A + B * Real.log (1 / δ)} ≥ ENNReal.ofReal (1 - δ)) :
    ∫ ω, X ω ∂μ ≤ A + B := by
  by_cases hInt : Integrable X μ
  ·
    have step1 : ∫ ω, X ω ∂μ = ∫ ω, (X ω - A) ∂μ + A := by
      rw [integral_sub hInt (integrable_const A), integral_const]
      simp [Measure.real, measure_univ]
    rw [step1]
    suffices h : ∫ ω, (X ω - A) ∂μ ≤ B by linarith

    have hIntXA : Integrable (fun ω => X ω - A) μ := hInt.sub (integrable_const A)
    have hIntMax : Integrable (fun ω => max (X ω - A) 0) μ := hIntXA.pos_part

    have hMeasMax : AEStronglyMeasurable (fun ω => max (X ω - A) 0) μ :=
      ((hMeas.sub measurable_const).max measurable_const).aestronglyMeasurable

    have hlint : ∫⁻ ω, ENNReal.ofReal (max (X ω - A) 0) ∂μ ≤ ENNReal.ofReal B := by
      rw [lintegral_eq_lintegral_meas_lt μ
        (by filter_upwards with ω; exact le_max_right _ _)
        ((hMeas.sub measurable_const).max measurable_const).aemeasurable]
      calc ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a | t < max (X a - A) 0}
          ≤ ∫⁻ (t : ℝ) in Set.Ioi 0, ENNReal.ofReal (Real.exp ((-1/B) * t)) := by
            apply lintegral_mono_ae
            filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
            simp only [Set.mem_Ioi] at ht
            have hset : {a | t < max (X a - A) 0} = {a | A + t < X a} := by
              ext a; simp only [Set.mem_setOf_eq, max_def]; split_ifs with h
              · constructor; intro h2; linarith; intro h2; linarith
              · push Not at h; constructor; intro h2; linarith; intro h2; linarith
            rw [hset]

            set δ := Real.exp ((-1/B) * t)
            have hδ_pos : 0 < δ := exp_pos _
            have hδ_le : δ ≤ 1 := exp_le_one_iff.mpr
              (mul_nonpos_of_nonpos_of_nonneg
                (div_nonpos_of_nonpos_of_nonneg (by norm_num) hB_pos.le) ht.le)
            have hTail' := hTail δ hδ_pos hδ_le
            have key : A + B * Real.log (1 / δ) = A + t := by
              congr 1; rw [one_div, Real.log_inv, Real.log_exp]; field_simp
            rw [key] at hTail'
            have hms : MeasurableSet {ω | X ω ≤ A + t} := hMeas measurableSet_Iic
            rw [show {a | A + t < X a} = {ω | X ω ≤ A + t}ᶜ from by
              ext ω; simp [not_le]]
            rw [measure_compl hms (measure_ne_top μ _), measure_univ]
            calc (1 : ENNReal) - μ {ω | X ω ≤ A + t}
                ≤ 1 - ENNReal.ofReal (1 - δ) := tsub_le_tsub_left hTail' _
              _ = ENNReal.ofReal δ := by
                  rw [show (1:ENNReal) = ENNReal.ofReal 1 from by simp]
                  rw [← ENNReal.ofReal_sub 1 (by linarith)]
                  congr 1; ring
        _ = ENNReal.ofReal B := by
            rw [← ofReal_integral_eq_lintegral_ofReal
              (integrableOn_exp_mul_Ioi (div_neg_of_neg_of_pos (by norm_num) hB_pos) 0)
              (by filter_upwards with t; exact (exp_pos _).le)]
            congr 1
            rw [integral_exp_mul_Ioi (div_neg_of_neg_of_pos (by norm_num) hB_pos)]
            simp [mul_zero, exp_zero]

    calc ∫ ω, (X ω - A) ∂μ
        ≤ ∫ ω, max (X ω - A) 0 ∂μ := by
          exact integral_mono_ae hIntXA hIntMax
            (by filter_upwards with ω; exact le_max_left _ _)
      _ = (∫⁻ ω, ENNReal.ofReal (max (X ω - A) 0) ∂μ).toReal := by
          exact integral_eq_lintegral_of_nonneg_ae
            (by filter_upwards with ω; exact le_max_right _ _) hMeasMax
      _ ≤ B := by
          rw [← ENNReal.toReal_ofReal hB_pos.le]
          exact ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hlint
  · rw [integral_undef hInt]; linarith

/-- Intermediate combined bound for Corollary 3.16: with probability `≥ 1 - δ`,
`‖φ_{θ̂} - f‖²_{L²} ≤ C (M^{-2β} + (n-1)^{-2β} + M log(n e)/n + σ² log(1/δ)/n)`. -/
theorem cor_3_16_combined_intermediate
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n)
    (β : ℝ) (hβ_pos : 0 < β)
    (Q : ℝ) (hQ : 0 < Q)
    (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (hθstar : ∀ j, θstar j = fourierCoeff f j)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
    (σ : ℝ) (hσ : 0 < σ) (hσ_le : σ ^ 2 ≤ 1)
    (ε : Ω → Fin n → ℝ)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
    (hIndep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
    (hMeasε : ∀ i, Measurable (fun ω => ε ω i))
    (hZeroMean : ∀ i, ∫ ω, ε ω i ∂μ = 0)
    (Y : Ω → Fin n → ℝ)
    (hModel : ∀ ω i, Y ω i = f ((i : ℝ) / (n : ℝ)) + ε ω i)
    (θhat : Ω → Fin (n - 1) → ℝ)
    (hEstimator : IsBICOrLassoEstimator Y θhat)
    (M : ℕ) (hM_pos : 0 < M) (hM_le : M ≤ n - 1)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (hf_cont : Continuous f) :
    ∃ (C : ℝ), 0 < C ∧
    μ {ω | L2normSq (fun x => trigLinComb (n - 1) (θhat ω) x - f x) ≤
            C * ((M : ℝ) ^ (-(2 * β)) + ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) +
                  (M : ℝ) * Real.log ((n : ℝ) * Real.exp 1) / (n : ℝ) +
                  σ ^ 2 * Real.log (1 / δ) / (n : ℝ))}
      ≥ ENNReal.ofReal (1 - δ) := by

  set C := 3 * Q + 4096
  have hC_pos : 0 < C := by positivity
  refine ⟨C, hC_pos, ?_⟩

  have h_oracle := sparse_oracle_ORT_sobolev_bound hn β hβ_pos Q hQ f θstar hθstar
    hSobolev σ hσ hσ_le ε hsubG hIndep hMeasε hZeroMean Y hModel θhat hEstimator M hM_pos hM_le δ hδ_pos hδ_le hf_cont


  apply le_trans h_oracle
  apply MeasureTheory.measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢

  set A := (M : ℝ) ^ (-(2 * β))
  set B := ((n - 1 : ℕ) : ℝ) ^ (-(2 * β))
  set D := (M : ℝ) * Real.log ((n : ℝ) * Real.exp 1) / (n : ℝ)
  set E := σ ^ 2 * Real.log (1 / δ) / (n : ℝ)
  have hA : 0 ≤ A := rpow_nonneg (Nat.cast_nonneg' M) _
  have hB : 0 ≤ B := rpow_nonneg (Nat.cast_nonneg' (n - 1)) _
  have hD : 0 ≤ D := by
    apply div_nonneg
    · apply mul_nonneg (Nat.cast_nonneg' M)
      apply Real.log_nonneg
      have hn_pos : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
      calc (1 : ℝ) ≤ 1 * 1 := by norm_num
        _ ≤ (n : ℝ) * Real.exp 1 := by
            apply mul_le_mul hn_pos (Real.one_le_exp (by positivity)) zero_le_one (by positivity)
    · exact Nat.cast_nonneg' n
  have hE : 0 ≤ E := by
    apply div_nonneg
    · exact mul_nonneg (sq_nonneg _) (Real.log_nonneg (by rw [le_div_iff₀ hδ_pos]; linarith))
    · exact Nat.cast_nonneg' n


  calc L2normSq (fun x => trigLinComb (n - 1) (θhat ω) x - f x)
      ≤ 3 * Q * A + 3 * Q * B + 4096 * D + 4096 * E := by
        convert hω using 1; simp only [A, B, D, E]; ring
    _ ≤ C * (A + B + D + E) := by nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 4096) hA,
                                              mul_nonneg (by norm_num : (0 : ℝ) ≤ 4096) hB,
                                              mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * Q) hD,
                                              mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * Q) hE]

/-- Rate computation for Corollary 3.16: the upper bound
`M^{-2β} + (n-1)^{-2β} + M log(n e)/n + σ² log(1/δ)/n` is dominated by
`C' n^{-2β/(2β+1)} + C' σ² log(1/δ)/n` (up to constants depending on `n`, `β`, `M`). -/
theorem cor_3_16_rate_computation
    (n : ℕ) (hn : 2 ≤ n)
    (β : ℝ) (_hβ_pos : 0 < β)
    (_hβ_lower : β ≥ (1 + Real.sqrt 5) / 4)
    (M : ℕ) (hM_pos : 0 < M) (_hM_le : M ≤ n - 1)
    (σ : ℝ) (_hσ : 0 < σ) :
    ∃ (C' : ℝ), 0 < C' ∧
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
    (M : ℝ) ^ (-(2 * β)) + ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) +
      (M : ℝ) * Real.log ((n : ℝ) * Real.exp 1) / (n : ℝ) +
      σ ^ 2 * Real.log (1 / δ) / (n : ℝ) ≤
    C' * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) +
    C' * σ ^ 2 * Real.log (1 / δ) / (n : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hM_real_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM_pos
  have hn1_real_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega)
  set r := (n : ℝ) ^ (-(2 * β) / (2 * β + 1))
  have hr_pos : 0 < r := rpow_pos_of_pos hn_pos _
  set A := (M : ℝ) ^ (-(2 * β)) + ((n - 1 : ℕ) : ℝ) ^ (-(2 * β)) +
            (M : ℝ) * Real.log ((n : ℝ) * Real.exp 1) / (n : ℝ)
  have hA_pos : 0 < A := by
    apply add_pos (add_pos _ _) _
    · exact rpow_pos_of_pos hM_real_pos _
    · exact rpow_pos_of_pos hn1_real_pos _
    · apply div_pos (mul_pos hM_real_pos _) hn_pos
      apply Real.log_pos
      have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
      linarith [mul_lt_mul_of_pos_left (one_lt_exp_iff.mpr one_pos) hn_pos]
  refine ⟨A / r + 1, by linarith [div_pos hA_pos hr_pos], ?_⟩
  intro δ hδ_pos hδ_le
  set L := σ ^ 2 * Real.log (1 / δ)
  have hL_nonneg : 0 ≤ L := by
    apply mul_nonneg (sq_nonneg σ)
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ_pos]; linarith
  suffices h : A + L / ↑n ≤ (A / r + 1) * r + (A / r + 1) * L / ↑n by
    convert h using 1; ring
  have h_expand_r : (A / r + 1) * r = A + r := by
    rw [add_mul, div_mul_cancel₀ A (ne_of_gt hr_pos), one_mul]
  have hAr_nonneg : 0 ≤ A / r := div_nonneg hA_pos.le hr_pos.le
  have h_expand_L : (A / r + 1) * L / ↑n ≥ L / ↑n := by
    apply div_le_div_of_nonneg_right _ hn_pos.le
    calc L = 1 * L := (one_mul L).symm
      _ ≤ (A / r + 1) * L := by
          apply mul_le_mul_of_nonneg_right _ hL_nonneg
          linarith
  linarith

/-- Expectation version of Corollary 3.16, derived from the tail bound:
`E ‖φ_{θ̂} - f‖²_{L²} ≲ σ² (log n / n)^{2β/(2β+1)}`. -/
theorem cor_3_16_expectation_from_tail
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n)
    (β : ℝ) (hβ_pos : 0 < β)
    (_hβ_lower : β ≥ (1 + Real.sqrt 5) / 4)
    (Q : ℝ) (hQ : 0 < Q)
    (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (hθstar : ∀ j, θstar j = fourierCoeff f j)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
    (σ : ℝ) (hσ : 0 < σ) (hσ_le : σ ^ 2 ≤ 1)
    (ε : Ω → Fin n → ℝ)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
    (hIndep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
    (hMeasε : ∀ i, Measurable (fun ω => ε ω i))
    (hZeroMean : ∀ i, ∫ ω, ε ω i ∂μ = 0)
    (Y : Ω → Fin n → ℝ)
    (hModel : ∀ ω i, Y ω i = f ((i : ℝ) / (n : ℝ)) + ε ω i)
    (θhat : Ω → Fin (n - 1) → ℝ)
    (hEstimator : IsBICOrLassoEstimator Y θhat)
    (hMeas : Measurable (fun ω => L2normSq (fun x => trigLinComb (n - 1) (θhat ω) x - f x)))
    (hf_cont : Continuous f) :
    ∃ (C : ℝ), 0 < C ∧
    ∫ ω, L2normSq (fun x => trigLinComb (n - 1) (θhat ω) x - f x) ∂μ ≤
      C * σ ^ 2 * (Real.log (n : ℝ) / (n : ℝ)) ^ ((2 * β) / (2 * β + 1)) := by

  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n from by omega))

  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have h2β1_pos : 0 < 2 * β + 1 := by linarith

  have hrate_pos : 0 < (Real.log (n : ℝ) / (n : ℝ)) ^ ((2 * β) / (2 * β + 1)) := by
    apply rpow_pos_of_pos
    exact div_pos hlogn hn_pos

  have hσsq_pos : 0 < σ ^ 2 := sq_pos_of_pos hσ

  have hRHS_factor_pos : 0 < σ ^ 2 * (Real.log (n : ℝ) / (n : ℝ)) ^ ((2 * β) / (2 * β + 1)) :=
    mul_pos hσsq_pos hrate_pos

  have hM_pos : 0 < n - 1 := by omega
  have hM_le : n - 1 ≤ n - 1 := le_refl _

  set A₀ := 3 * Q * (↑(n - 1) : ℝ) ^ (-(2 * β)) + 3 * Q * ((↑(n - 1) : ℝ)) ^ (-(2 * β)) +
            4096 * (↑(n - 1) : ℝ) * Real.log ((↑n : ℝ) * Real.exp 1) / (↑n : ℝ)
  set B₀ := 4096 * σ ^ 2 / (↑n : ℝ)
  have hM_real_pos : (0 : ℝ) < (↑(n - 1) : ℝ) := Nat.cast_pos.mpr hM_pos
  have hlog_ne_pos : 0 < Real.log ((↑n : ℝ) * Real.exp 1) := by
    apply Real.log_pos
    have hn1 : (1 : ℝ) < (↑n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    linarith [mul_lt_mul_of_pos_left (one_lt_exp_iff.mpr one_pos) hn_pos]
  have hA₀_pos : 0 < A₀ := by
    apply add_pos (add_pos _ _) _
    · exact mul_pos (mul_pos (by positivity) hQ) (rpow_pos_of_pos hM_real_pos _)
    · exact mul_pos (mul_pos (by positivity) hQ) (rpow_pos_of_pos hM_real_pos _)
    · exact div_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4096) hM_real_pos) hlog_ne_pos) hn_pos
  have hB₀_pos : 0 < B₀ := div_pos (mul_pos (by norm_num : (0 : ℝ) < 4096) hσsq_pos) hn_pos


  have hHighProb : ∀ (δ' : ℝ), 0 < δ' → δ' ≤ 1 →
      μ {ω | L2normSq (fun x => trigLinComb (n - 1) (θhat ω) x - f x) ≤
              A₀ + B₀ * Real.log (1 / δ')} ≥ ENNReal.ofReal (1 - δ') := by
    intro δ' hδ'_pos hδ'_le
    have hOracle := sparse_oracle_ORT_sobolev_bound hn β hβ_pos Q hQ f θstar hθstar
      hSobolev σ hσ hσ_le ε hsubG hIndep hMeasε hZeroMean Y hModel θhat hEstimator (n - 1) hM_pos hM_le δ' hδ'_pos hδ'_le hf_cont
    apply le_trans hOracle
    apply MeasureTheory.measure_mono
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢


    calc L2normSq (fun x => trigLinComb (n - 1) (θhat ω) x - f x)
        ≤ A₀ + 4096 * σ ^ 2 * Real.log (1 / δ') / ↑n := hω
      _ = A₀ + B₀ * Real.log (1 / δ') := by simp only [B₀]; ring

  have hExpBound := tail_integration_bound
    (fun ω => L2normSq (fun x => trigLinComb (n - 1) (θhat ω) x - f x))
    hMeas A₀ hA₀_pos B₀ hB₀_pos hHighProb


  refine ⟨(A₀ + B₀) / (σ ^ 2 * (Real.log (↑n : ℝ) / (↑n : ℝ)) ^ ((2 * β) / (2 * β + 1))) + 1,
         by linarith [div_pos (by linarith : 0 < A₀ + B₀) hRHS_factor_pos], ?_⟩
  calc ∫ ω, L2normSq (fun x => trigLinComb (n - 1) (θhat ω) x - f x) ∂μ
      ≤ A₀ + B₀ := hExpBound
    _ = 1 * (A₀ + B₀) := (one_mul _).symm
    _ ≤ ((A₀ + B₀) / (σ ^ 2 * (Real.log (↑n : ℝ) / (↑n : ℝ)) ^ ((2 * β) / (2 * β + 1))) + 1) *
        (σ ^ 2 * (Real.log (↑n : ℝ) / (↑n : ℝ)) ^ ((2 * β) / (2 * β + 1))) := by
      rw [add_mul, div_mul_cancel₀ (A₀ + B₀) (ne_of_gt hRHS_factor_pos), one_mul]
      linarith
    _ = ((A₀ + B₀) / (σ ^ 2 * (Real.log (↑n : ℝ) / (↑n : ℝ)) ^ ((2 * β) / (2 * β + 1))) + 1) *
        σ ^ 2 * (Real.log (↑n : ℝ) / (↑n : ℝ)) ^ ((2 * β) / (2 * β + 1)) := by ring

/-- High-probability part of Corollary 3.16: under the same assumptions as Theorem 3.15,
both BIC and Lasso estimators achieve, with probability `≥ 1 - δ`,
`‖φ_{θ̂} - f‖²_{L²} ≲ n^{-2β/(2β+1)} + σ² log(1/δ)/n`. -/
theorem cor_3_16_high_prob
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n)

    (β : ℝ) (hβ_pos : 0 < β)
    (hβ_lower : β ≥ (1 + Real.sqrt 5) / 4)
    (Q : ℝ) (hQ : 0 < Q)

    (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (hθstar : ∀ j, θstar j = fourierCoeff f j)

    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)

    (σ : ℝ) (hσ : 0 < σ) (hσ_le : σ ^ 2 ≤ 1)
    (ε : Ω → Fin n → ℝ)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
    (hIndep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
    (hMeasε : ∀ i, Measurable (fun ω => ε ω i))
    (hZeroMean : ∀ i, ∫ ω, ε ω i ∂μ = 0)

    (Y : Ω → Fin n → ℝ)
    (hModel : ∀ ω i, Y ω i = f ((i : ℝ) / (n : ℝ)) + ε ω i)

    (θhat : Ω → Fin (n - 1) → ℝ)
    (hEstimator : IsBICOrLassoEstimator Y θhat)
    (hf_cont : Continuous f) :


    ∃ (C : ℝ), 0 < C ∧
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
    μ {ω | L2normSq (fun x => trigLinComb (n - 1) (θhat ω) x - f x) ≤
            C * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) +
            C * σ ^ 2 * Real.log (1 / δ) / (n : ℝ)}
      ≥ ENNReal.ofReal (1 - δ) := by


  have hM_pos : 0 < n - 1 := by omega
  have hM_le : n - 1 ≤ n - 1 := le_refl _


  obtain ⟨C', hC'_pos, hrate⟩ := cor_3_16_rate_computation n hn β hβ_pos hβ_lower
    (n - 1) hM_pos hM_le σ hσ


  set C₁ := 3 * Q + (4096 : ℝ)
  have hC₁_pos : 0 < C₁ := by positivity
  refine ⟨C₁ * C', mul_pos hC₁_pos hC'_pos, ?_⟩

  intro δ hδ_pos hδ_le


  have h_oracle := sparse_oracle_ORT_sobolev_bound hn β hβ_pos Q hQ f θstar hθstar
    hSobolev σ hσ hσ_le ε hsubG hIndep hMeasε hZeroMean Y hModel θhat hEstimator
    (n - 1) hM_pos hM_le δ hδ_pos hδ_le hf_cont

  have hrate_δ := hrate δ hδ_pos hδ_le


  apply le_trans h_oracle
  apply MeasureTheory.measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢

  set A := (↑(n - 1) : ℝ) ^ (-(2 * β))
  set B := ((n - 1 : ℕ) : ℝ) ^ (-(2 * β))
  set D := (↑(n - 1) : ℝ) * Real.log ((n : ℝ) * Real.exp 1) / (n : ℝ)
  set E := σ ^ 2 * Real.log (1 / δ) / (n : ℝ)
  have hA : 0 ≤ A := rpow_nonneg (Nat.cast_nonneg' (n - 1)) _
  have hB : 0 ≤ B := rpow_nonneg (Nat.cast_nonneg' (n - 1)) _
  have hD : 0 ≤ D := by
    apply div_nonneg
    · apply mul_nonneg (Nat.cast_nonneg' (n - 1))
      apply Real.log_nonneg
      have hn_pos : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
      calc (1 : ℝ) ≤ 1 * 1 := by norm_num
        _ ≤ (n : ℝ) * Real.exp 1 := by
            apply mul_le_mul hn_pos (Real.one_le_exp (by positivity)) zero_le_one (by positivity)
    · exact Nat.cast_nonneg' n
  have hE : 0 ≤ E := by
    apply div_nonneg
    · exact mul_nonneg (sq_nonneg _) (Real.log_nonneg (by rw [le_div_iff₀ hδ_pos]; linarith))
    · exact Nat.cast_nonneg' n

  calc L2normSq (fun x => trigLinComb (n - 1) (θhat ω) x - f x)
      ≤ 3 * Q * A + 3 * Q * B + 4096 * D + 4096 * E := by
        convert hω using 1; simp only [A, B, D, E]; ring
    _ ≤ C₁ * (A + B + D + E) := by
        simp only [C₁]
        nlinarith [mul_nonneg (by norm_num : (0 : ℝ) ≤ 4096) hA,
                   mul_nonneg (by norm_num : (0 : ℝ) ≤ 4096) hB,
                   mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * Q) hD,
                   mul_nonneg (by linarith : (0 : ℝ) ≤ 3 * Q) hE]
    _ ≤ C₁ * (C' * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) +
            C' * σ ^ 2 * Real.log (1 / δ) / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hrate_δ (le_of_lt hC₁_pos)
    _ = C₁ * C' * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) +
        C₁ * C' * σ ^ 2 * Real.log (1 / δ) / (n : ℝ) := by ring

/-- Expectation part of Corollary 3.16: BIC and Lasso estimators achieve
`E ‖φ_{θ̂} - f‖²_{L²} ≲ σ² (log n / n)^{2β/(2β+1)}`. -/
theorem cor_3_16_expectation
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n)

    (β : ℝ) (hβ_pos : 0 < β)
    (hβ_lower : β ≥ (1 + Real.sqrt 5) / 4)
    (Q : ℝ) (hQ : 0 < Q)

    (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (hθstar : ∀ j, θstar j = fourierCoeff f j)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)

    (σ : ℝ) (hσ : 0 < σ) (hσ_le : σ ^ 2 ≤ 1)
    (ε : Ω → Fin n → ℝ)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
    (hIndep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
    (hMeasε : ∀ i, Measurable (fun ω => ε ω i))
    (hZeroMean : ∀ i, ∫ ω, ε ω i ∂μ = 0)

    (Y : Ω → Fin n → ℝ)
    (hModel : ∀ ω i, Y ω i = f ((i : ℝ) / (n : ℝ)) + ε ω i)

    (θhat : Ω → Fin (n - 1) → ℝ)
    (hEstimator : IsBICOrLassoEstimator Y θhat)

    (hMeas : Measurable (fun ω => L2normSq (fun x => trigLinComb (n - 1) (θhat ω) x - f x)))
    (hf_cont : Continuous f) :

    ∃ (C : ℝ), 0 < C ∧
    ∫ ω, L2normSq (fun x => trigLinComb (n - 1) (θhat ω) x - f x) ∂μ ≤
      C * σ ^ 2 * (Real.log (n : ℝ) / (n : ℝ)) ^ ((2 * β) / (2 * β + 1)) := by


  exact cor_3_16_expectation_from_tail hn β hβ_pos hβ_lower Q hQ f
    θstar hθstar hSobolev σ hσ hσ_le ε hsubG hIndep hMeasε hZeroMean Y hModel θhat hEstimator hMeas hf_cont

/-- **Corollary 3.16 (Adaptive estimation).** Under the same assumptions as Theorem 3.15,
both the BIC and Lasso estimators with the trigonometric design adapt to the unknown
Sobolev smoothness up to log factors:
- With probability `1 - δ`:
  `‖φ_{θ̂} - f‖²_{L²} ≲ n^{-2β/(2β+1)} + σ² log(1/δ)/n`.
- In expectation:
  `E ‖φ_{θ̂} - f‖²_{L²} ≲ σ² (log n / n)^{2β/(2β+1)}`. -/
theorem cor_3_16
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 2 ≤ n)
    (β : ℝ) (hβ_pos : 0 < β)
    (hβ_lower : β ≥ (1 + Real.sqrt 5) / 4)
    (Q : ℝ) (hQ : 0 < Q)
    (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (hθstar : ∀ j, θstar j = fourierCoeff f j)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
    (σ : ℝ) (hσ : 0 < σ) (hσ_le : σ ^ 2 ≤ 1)
    (ε : Ω → Fin n → ℝ)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
    (hIndep : ProbabilityTheory.iIndepFun (β := fun _ : Fin n => ℝ) (fun i ω => ε ω i) μ)
    (hMeasε : ∀ i, Measurable (fun ω => ε ω i))
    (hZeroMean : ∀ i, ∫ ω, ε ω i ∂μ = 0)
    (Y : Ω → Fin n → ℝ)
    (hModel : ∀ ω i, Y ω i = f ((i : ℝ) / (n : ℝ)) + ε ω i)
    (θhat : Ω → Fin (n - 1) → ℝ)
    (hEstimator : IsBICOrLassoEstimator Y θhat)
    (hMeas : Measurable (fun ω => L2normSq (fun x => trigLinComb (n - 1) (θhat ω) x - f x)))
    (hf_cont : Continuous f) :

    (∃ (C : ℝ), 0 < C ∧
      ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
      μ {ω | L2normSq (fun x => trigLinComb (n - 1) (θhat ω) x - f x) ≤
              C * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) +
              C * σ ^ 2 * Real.log (1 / δ) / (n : ℝ)}
        ≥ ENNReal.ofReal (1 - δ))
    ∧

    (∃ (C : ℝ), 0 < C ∧
      ∫ ω, L2normSq (fun x => trigLinComb (n - 1) (θhat ω) x - f x) ∂μ ≤
        C * σ ^ 2 * (Real.log (n : ℝ) / (n : ℝ)) ^ ((2 * β) / (2 * β + 1))) :=
  ⟨cor_3_16_high_prob hn β hβ_pos hβ_lower Q hQ f θstar hθstar hSobolev
      σ hσ hσ_le ε hsubG hIndep hMeasε hZeroMean Y hModel θhat hEstimator hf_cont,
   cor_3_16_expectation hn β hβ_pos hβ_lower Q hQ f θstar hθstar hSobolev
      σ hσ hσ_le ε hsubG hIndep hMeasε hZeroMean Y hModel θhat hEstimator hMeas hf_cont⟩

end Chapter3
