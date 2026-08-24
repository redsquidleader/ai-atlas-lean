/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.LindebergBound
import Atlas.BooleanFunctions.code.LindebergOneDim
import Atlas.BooleanFunctions.code.MajorityStablest

noncomputable section

open Finset BigOperators MeasureTheory

namespace BooleanFourier

def linearBooleanFunction {n : ℕ} (a : Fin n → ℝ) : (Fin n → Bool) → ℝ :=
  fun x => ∑ i : Fin n, a i * boolToReal (x i)

noncomputable def singletonCoeffs {n : ℕ} (a : Fin n → ℝ) :
    Finset (Fin n) → ℝ :=
  fun S => if h : ∃ i, S = {i} then a h.choose else 0

lemma singletonCoeffs_singleton {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    singletonCoeffs a {i} = a i := by
  simp only [singletonCoeffs]
  have h : ∃ j, ({i} : Finset (Fin n)) = {j} := ⟨i, rfl⟩
  rw [dif_pos h]
  congr 1
  exact Finset.singleton_injective h.choose_spec.symm

lemma singletonCoeffs_non_singleton {n : ℕ} (a : Fin n → ℝ)
    (S : Finset (Fin n)) (hS : ¬∃ i, S = {i}) :
    singletonCoeffs a S = 0 := by
  simp [singletonCoeffs, hS]

lemma singleton_filter_eq_image {n : ℕ} :
    (Finset.univ : Finset (Finset (Fin n))).filter (fun S => ∃ i, S = {i}) =
      Finset.image (fun i => ({i} : Finset (Fin n))) Finset.univ := by
  ext S
  constructor
  · intro hS
    rw [Finset.mem_filter] at hS
    obtain ⟨_, i, rfl⟩ := hS
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  · intro hS
    rw [Finset.mem_image] at hS
    obtain ⟨i, _, rfl⟩ := hS
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, i, rfl⟩

lemma singletonCoeffs_agree {n : ℕ} (a : Fin n → ℝ) (b : Fin n → Bool) :
    ∑ S : Finset (Fin n), singletonCoeffs a S * ∏ i ∈ S, boolToReal (b i) =
      linearBooleanFunction a b := by
  simp only [linearBooleanFunction]
  conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Finset (Fin n))) (fun S => ∃ i, S = {i})]
  have h_not : ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => ¬∃ i, S = {i}),
      singletonCoeffs a S * ∏ i ∈ S, boolToReal (b i) = 0 := by
    apply Finset.sum_eq_zero
    intro S hS
    rw [Finset.mem_filter] at hS
    rw [singletonCoeffs_non_singleton a S hS.2, zero_mul]
  rw [h_not, add_zero]
  rw [singleton_filter_eq_image]
  rw [Finset.sum_image (fun i _ j _ h => Finset.singleton_injective h)]
  congr 1; ext i
  rw [singletonCoeffs_singleton, Finset.prod_singleton]

lemma singletonCoeffs_eval {n : ℕ} (a : Fin n → ℝ) (z : Fin n → ℝ) :
    ∑ S : Finset (Fin n), singletonCoeffs a S * ∏ i ∈ S, z i =
      ∑ i : Fin n, a i * z i := by
  conv_lhs => rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Finset (Fin n))) (fun S => ∃ i, S = {i})]
  have h_not : ∑ S ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun S => ¬∃ i, S = {i}),
      singletonCoeffs a S * ∏ i ∈ S, z i = 0 := by
    apply Finset.sum_eq_zero
    intro S hS
    rw [Finset.mem_filter] at hS
    rw [singletonCoeffs_non_singleton a S hS.2, zero_mul]
  rw [h_not, add_zero]
  rw [singleton_filter_eq_image]
  rw [Finset.sum_image (fun i _ j _ h => Finset.singleton_injective h)]
  congr 1; ext i
  rw [singletonCoeffs_singleton, Finset.prod_singleton]

theorem linear_hybrid_fubini_bound
    {n : ℕ} (a : Fin n → ℝ) (Ψ : ℝ → ℝ) (hΨ : IsC3Bounded Ψ) (k : Fin n)
    (h_bound : ∀ c : ℝ,
      |((Ψ (c + a k) + Ψ (c - a k)) / 2) -
        ∫ t, Ψ (c + a k * t) ∂(ProbabilityTheory.gaussianReal 0 1)| ≤
      (1 / 2) * hΨ.thirdDerivBound * |a k| ^ 3) :
    |hybridExpectation (linearBooleanFunction a) Ψ k.val -
      hybridExpectation (linearBooleanFunction a) Ψ (k.val + 1)| ≤
    (1 / 2) * hΨ.thirdDerivBound * |a k| ^ 3 := by sorry

theorem lindeberg_per_step_bound_linear
  {n : ℕ} (a : Fin n → ℝ) (Ψ : ℝ → ℝ) (hΨ : IsC3Bounded Ψ) (k : Fin n) :
  |hybridExpectation (linearBooleanFunction a) Ψ k.val -
    hybridExpectation (linearBooleanFunction a) Ψ (k.val + 1)| ≤
    (1 / 2) * hΨ.thirdDerivBound * |a k| ^ 3 :=


  linear_hybrid_fubini_bound a Ψ hΨ k (fun c => lindeberg_one_dim_comparison Ψ hΨ c (a k))

theorem invariance_principle
  {n : ℕ}
  (a : Fin n → ℝ)
  (Ψ : ℝ → ℝ)
  (hΨ : IsC3Bounded Ψ) :
  |booleanExpectation (linearBooleanFunction a) Ψ -
    gaussianExpectation (linearBooleanFunction a) Ψ| ≤
    (1 / 2) * hΨ.thirdDerivBound * ∑ i : Fin n, |a i| ^ 3 := by
  rw [lindeberg_telescoping (linearBooleanFunction a) Ψ]
  calc |∑ k : Fin n, (hybridExpectation (linearBooleanFunction a) Ψ k.val -
        hybridExpectation (linearBooleanFunction a) Ψ (k.val + 1))|
      ≤ ∑ k : Fin n, |hybridExpectation (linearBooleanFunction a) Ψ k.val -
          hybridExpectation (linearBooleanFunction a) Ψ (k.val + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin n, ((1 / 2) * hΨ.thirdDerivBound * |a k| ^ 3) := by
        apply Finset.sum_le_sum
        intro k _
        exact lindeberg_per_step_bound_linear a Ψ hΨ k
    _ = (1 / 2) * hΨ.thirdDerivBound * ∑ i : Fin n, |a i| ^ 3 := by
        rw [← Finset.mul_sum]


theorem invariance_principle_general
  {n : ℕ}
  (f : (Fin n → Bool) → ℝ)
  (d : ℕ)
  (hdeg : degree f ≤ d)
  (Ψ : ℝ → ℝ)
  (hΨ : IsC3Bounded Ψ) :
  |booleanExpectation f Ψ - gaussianExpectation f Ψ| ≤
    (1 / 2) * (2 : ℝ) ^ ((3 : ℝ) * ↑d / 2) * hΨ.thirdDerivBound *
      ∑ i : Fin n, (fourierInfluence f i) ^ ((3 : ℝ) / 2) := by
  rw [lindeberg_telescoping f Ψ]
  calc |∑ k : Fin n, (hybridExpectation f Ψ k.val - hybridExpectation f Ψ (k.val + 1))|
      ≤ ∑ k : Fin n, |hybridExpectation f Ψ k.val - hybridExpectation f Ψ (k.val + 1)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k : Fin n, ((1 / 2) * (2 : ℝ) ^ ((3 : ℝ) * ↑d / 2) * hΨ.thirdDerivBound *
          (fourierInfluence f k) ^ ((3 : ℝ) / 2)) := by
        apply Finset.sum_le_sum
        intro k _
        exact lindeberg_per_step_bound f d hdeg Ψ hΨ k
    _ = (1 / 2) * (2 : ℝ) ^ ((3 : ℝ) * ↑d / 2) * hΨ.thirdDerivBound *
          ∑ i : Fin n, (fourierInfluence f i) ^ ((3 : ℝ) / 2) := by
        rw [← Finset.mul_sum]

def boolCDF {n : ℕ} (f : (Fin n → Bool) → ℝ) (t : ℝ) : ℝ :=
  ((Finset.univ.filter fun x => f x ≤ t).card : ℝ) / (2 : ℝ) ^ n

def HasUnitVariance {n : ℕ} (f : (Fin n → Bool) → ℝ) : Prop :=
  ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 = 1


theorem claim_2_2_invariance {n : ℕ} (f : (Fin n → Bool) → ℝ) (τ : ℝ) (_hτ : 0 ≤ τ)
    (hInf : ∀ i : Fin n, fourierInfluence f i ≤ τ) :
    ∑ i : Fin n, (fourierInfluence f i) ^ ((3 : ℝ) / 2) ≤
      τ ^ ((1 : ℝ) / 2) * ∑ i : Fin n, fourierInfluence f i := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hInf_nonneg : 0 ≤ fourierInfluence f i := by
    simp only [fourierInfluence]
    apply Finset.sum_nonneg
    intro S _
    split_ifs <;> positivity
  have hInf_le := hInf i


  have h_half_nonneg : (0 : ℝ) ≤ 1 / 2 := by norm_num
  calc (fourierInfluence f i) ^ ((3 : ℝ) / 2)
      = (fourierInfluence f i) ^ (1 + (1 : ℝ) / 2) := by ring_nf
    _ = (fourierInfluence f i) ^ (1 : ℝ) * (fourierInfluence f i) ^ ((1 : ℝ) / 2) := by
        rcases eq_or_lt_of_le hInf_nonneg with h | h
        · simp [← h, Real.zero_rpow (by norm_num : (1 : ℝ) + 2⁻¹ ≠ 0),
            Real.zero_rpow (by norm_num : (1 : ℝ) ≠ 0),
            Real.zero_rpow (by norm_num : (2 : ℝ)⁻¹ ≠ 0)]
        · exact Real.rpow_add h 1 (1/2)
    _ = fourierInfluence f i * (fourierInfluence f i) ^ ((1 : ℝ) / 2) := by
        rw [Real.rpow_one]
    _ ≤ fourierInfluence f i * τ ^ ((1 : ℝ) / 2) := by
        apply mul_le_mul_of_nonneg_left
        · exact Real.rpow_le_rpow hInf_nonneg hInf_le h_half_nonneg
        · exact hInf_nonneg
    _ = τ ^ ((1 : ℝ) / 2) * fourierInfluence f i := by ring

lemma fourierInfluence_eq_influenceReal {n : ℕ} (f : (Fin n → Bool) → ℝ) (i : Fin n) :
    fourierInfluence f i = influenceReal f i := by
  rw [influenceReal_eq_sum_fourierCoeff_sq]
  simp only [fourierInfluence]
  rw [← Finset.sum_filter]

lemma sum_fourierInfluence_eq_totalInfluenceReal {n : ℕ} (f : (Fin n → Bool) → ℝ) :
    ∑ i : Fin n, fourierInfluence f i = totalInfluenceReal f := by
  simp_rw [fourierInfluence_eq_influenceReal]
  rfl

lemma totalInfluenceReal_le_degree_mul_varianceReal {n : ℕ} (f : (Fin n → Bool) → ℝ)
    (d : ℕ) (hdeg : degree f ≤ d) :
    totalInfluenceReal f ≤ (d : ℝ) * varianceReal f := by
  rw [totalInfluenceReal_eq_sum_card_fourierCoeff_sq]
  unfold varianceReal
  rw [Finset.sum_filter]

  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S _
  by_cases hS : S = ∅
  · simp [hS]
  · simp only [ne_eq, hS, not_false_eq_true, ite_true]

    by_cases hcoeff : fourierCoeff f S = 0
    · simp [hcoeff]
    · have hsq : (0 : ℝ) ≤ fourierCoeff f S ^ 2 := sq_nonneg _
      apply mul_le_mul_of_nonneg_right _ hsq
      have h1 : S.card ≤ degree f := by
        unfold degree
        apply Finset.le_sup
        simp [hcoeff]
      exact_mod_cast h1.trans hdeg

theorem invariance_principle_corollary
    (C : ℝ) (hC : C > 0) (ε : ℝ) (hε : ε > 0) (d : ℕ) :
    ∃ τ > 0, ∀ (n : ℕ) (f : (Fin n → Bool) → ℝ),
      degree f ≤ d →
      (∀ i : Fin n, fourierInfluence f i ≤ τ) →
      varianceReal f ≤ C →
      ∀ (Ψ : ℝ → ℝ) (hΨ : IsC3Bounded Ψ),
        hΨ.thirdDerivBound ≤ C →
        |booleanExpectation f Ψ - gaussianExpectation f Ψ| ≤ ε := by

  set K : ℝ := (1 / 2) * (2 : ℝ) ^ ((3 : ℝ) * ↑d / 2) * C ^ 2 * ↑d + 1
  have hK_pos : K > 0 := by positivity

  refine ⟨(ε / K) ^ 2, by positivity, ?_⟩
  intro n f hdeg hInf hVar Ψ hΨ hΨ_bound

  have h_sum_infl : ∑ i : Fin n, fourierInfluence f i ≤ ↑d * C := by
    rw [sum_fourierInfluence_eq_totalInfluenceReal]
    exact (totalInfluenceReal_le_degree_mul_varianceReal f d hdeg).trans
      (mul_le_mul_of_nonneg_left hVar (Nat.cast_nonneg' d))
  have h_claim22 := claim_2_2_invariance f ((ε / K) ^ 2)
      (by positivity : (0 : ℝ) ≤ (ε / K) ^ 2) hInf

  have h_rpow_sq : ((ε / K) ^ 2) ^ ((1 : ℝ) / 2) = ε / K := by
    have hpos : (0 : ℝ) < ε / K := by positivity
    rw [← Real.rpow_natCast (ε / K) 2]
    rw [← Real.rpow_mul (le_of_lt hpos)]
    norm_num

  have hsum_bound : ∑ i : Fin n, (fourierInfluence f i) ^ ((3 : ℝ) / 2) ≤
      (ε / K) * (↑d * C) := by
    calc ∑ i : Fin n, (fourierInfluence f i) ^ ((3 : ℝ) / 2)
        ≤ ((ε / K) ^ 2) ^ ((1 : ℝ) / 2) * ∑ i : Fin n, fourierInfluence f i := h_claim22
      _ ≤ ((ε / K) ^ 2) ^ ((1 : ℝ) / 2) * (↑d * C) := by
          apply mul_le_mul_of_nonneg_left h_sum_infl
          positivity
      _ = (ε / K) * (↑d * C) := by rw [h_rpow_sq]

  have h_rhs_le_eps : (1 / 2) * (2 : ℝ) ^ ((3 : ℝ) * ↑d / 2) * hΨ.thirdDerivBound *
      ∑ i : Fin n, (fourierInfluence f i) ^ ((3 : ℝ) / 2) ≤ ε := by
    have h_bound_C : hΨ.thirdDerivBound ≤ C := hΨ_bound
    calc (1 / 2) * (2 : ℝ) ^ ((3 : ℝ) * ↑d / 2) * hΨ.thirdDerivBound *
          ∑ i : Fin n, (fourierInfluence f i) ^ ((3 : ℝ) / 2)
        ≤ (1 / 2) * (2 : ℝ) ^ ((3 : ℝ) * ↑d / 2) * C *
          ((ε / K) * (↑d * C)) := by
          have h1 : (0 : ℝ) ≤ (1 / 2) * (2 : ℝ) ^ ((3 : ℝ) * ↑d / 2) := by positivity
          have h2 : hΨ.thirdDerivBound * ∑ i : Fin n, (fourierInfluence f i) ^ ((3 : ℝ) / 2) ≤
              C * (ε / K * (↑d * C)) := by
            calc hΨ.thirdDerivBound * ∑ i : Fin n, (fourierInfluence f i) ^ ((3 : ℝ) / 2)
                ≤ C * ∑ i : Fin n, (fourierInfluence f i) ^ ((3 : ℝ) / 2) := by
                  apply mul_le_mul_of_nonneg_right h_bound_C
                  apply Finset.sum_nonneg; intro i _
                  exact Real.rpow_nonneg (by
                    simp only [fourierInfluence]
                    exact Finset.sum_nonneg (fun S _ => by split_ifs <;> positivity)) _
              _ ≤ C * (ε / K * (↑d * C)) := by
                  apply mul_le_mul_of_nonneg_left hsum_bound (le_of_lt hC)
          nlinarith
      _ = ((1 / 2) * (2 : ℝ) ^ ((3 : ℝ) * ↑d / 2) * C ^ 2 * ↑d) * (ε / K) := by ring
      _ ≤ (K - 1) * (ε / K) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          simp only [K]; linarith
      _ ≤ K * (ε / K) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          linarith
      _ = ε := by field_simp
  exact (invariance_principle_general f d hdeg Ψ hΨ).trans h_rhs_le_eps

end BooleanFourier

end
