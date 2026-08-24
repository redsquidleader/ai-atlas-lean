/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProjectionTheory.code.LinnikLargeSieve

open Finset Complex Real

noncomputable section

namespace LargeSieveSize

/-- The image $\pi_p(A) \subseteq \mathbb{Z}_p$ of `A ⊆ ℕ` under reduction modulo `p`. -/
def projImage (A : Finset ℕ) (p : ℕ) [NeZero p] : Finset (ZMod p) :=
  Finset.image (fun n : ℕ => (n : ZMod p)) A

/-- Predicate: `A` has small projections, meaning `|π_p(A)| ≤ 0.99 p` for every prime
`p ∈ P_{N^{1/2}}`. This is the hypothesis of Corollary 5. -/
def hasSmallProjections (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ p ∈ LinnikLargeSieve.primesInRange (Nat.sqrt N),
    ∀ hp : Nat.Prime p,
      haveI : NeZero p := ⟨hp.ne_zero⟩
      (projImage A p).card ≤ Nat.floor (0.99 * (p : ℝ))

/-- Indicator function `1_A : Fin N → ℂ`, where index `n : Fin N` corresponds to the integer
`n + 1 ∈ [1, N]`. -/
def indicatorFn (A : Finset ℕ) (N : ℕ) : Fin N → ℂ :=
  fun n => if (n : ℕ) + 1 ∈ A then 1 else 0


/-- Lower bound on the number of primes in the dyadic range `[M/2, M]`: for `M` large,
`|P_M| ≥ M / (4 log M)`. (A quantitative form of PNT.) -/
theorem primes_in_dyadic_range_lower_bound
    : ∃ (N₀ : ℕ), ∀ M : ℕ, N₀ ≤ M →
      (M : ℝ) / (4 * Real.log M) ≤ ((LinnikLargeSieve.primesInRange M).card : ℝ) := by sorry


/-- Centering identity in $L^2$: for `f : Fin N → ℂ`,
$\sum_n |f(n) - \bar f|^2 = \sum_n |f(n)|^2 - |\sum_i f(i)|^2/N$,
where $\bar f = (\sum_i f(i))/N$ is the mean. -/
lemma norm_sq_sub_mean_eq (N : ℕ) (hN : 0 < N) (f : Fin N → ℂ) :
    (∑ n : Fin N, ‖f n - (∑ i : Fin N, f i) / (N : ℂ)‖ ^ 2 : ℝ) =
    (∑ n : Fin N, ‖f n‖ ^ 2 : ℝ) - ‖∑ i : Fin N, f i‖ ^ 2 / N := by
  set S := ∑ i : Fin N, f i
  set c := S / (N : ℂ)
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hN_ne : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  simp_rw [Complex.sq_norm, Complex.normSq_sub]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  suffices h : (N : ℝ) * normSq c - ∑ x : Fin N, 2 * (f x * starRingEnd ℂ c).re =
      -(normSq S / N) by linarith
  have hc_normSq : (N : ℝ) * Complex.normSq c = Complex.normSq S / N := by
    have hcn : (N : ℝ) ^ 2 * Complex.normSq c = Complex.normSq S := by
      have hceq : c = S / (N : ℂ) := rfl
      rw [hceq, Complex.normSq_div]
      have hN_sq : Complex.normSq (N : ℂ) = (N : ℝ) ^ 2 := by
        simp [Complex.normSq_natCast]; ring
      rw [hN_sq]; field_simp
    have h2 : (N : ℝ) ^ 2 = N * N := by ring
    rw [h2] at hcn; field_simp at hcn ⊢; linarith
  have hsum_re : (∑ x : Fin N, 2 * (f x * starRingEnd ℂ c).re : ℝ) =
      2 * (Complex.normSq S / N) := by
    have h_sum_eq : (∑ x : Fin N, (f x * starRingEnd ℂ c).re : ℝ) =
        (S * starRingEnd ℂ c).re := by
      conv_rhs => rw [show S = ∑ x : Fin N, f x from rfl]; rw [Finset.sum_mul]
      exact (Complex.re_sum Finset.univ (fun x => f x * starRingEnd ℂ c)).symm
    rw [show (∑ x : Fin N, 2 * (f x * starRingEnd ℂ c).re : ℝ) =
        2 * ∑ x : Fin N, (f x * starRingEnd ℂ c).re from by rw [Finset.mul_sum]]
    rw [h_sum_eq]; congr 1
    have hc_conj : starRingEnd ℂ c = starRingEnd ℂ S / (N : ℂ) := by simp [c, map_div₀]
    rw [hc_conj, div_eq_mul_inv, ← mul_assoc, Complex.mul_conj]
    rw [show ((↑(normSq S) : ℂ) * ((N : ℂ)⁻¹)).re = (normSq S : ℝ) * (N : ℝ)⁻¹ from by
      rw [show ((N : ℂ)⁻¹) = ((N⁻¹ : ℝ) : ℂ) from by push_cast; ring]
      rw [← Complex.ofReal_mul, Complex.ofReal_re]]
    ring
  linarith


/-- The squared $L^2$ norm of an indicator function `indicatorFn A N` equals `|A|`. -/
lemma indicator_l2_eq_card (N : ℕ) (A : Finset ℕ) (hN : 0 < N)
    (hA : A ⊆ Finset.Icc 1 N) :
    (∑ n : Fin N, ‖indicatorFn A N n‖ ^ 2 : ℝ) = A.card := by
  simp only [indicatorFn]
  have h : ∀ n : Fin N, ‖(if (n : ℕ) + 1 ∈ A then (1 : ℂ) else 0)‖ ^ 2 =
      if (n : ℕ) + 1 ∈ A then (1 : ℝ) else 0 := by intro n; split_ifs <;> simp
  simp_rw [h]
  have h_card : (∑ n : Fin N, (if (↑n : ℕ) + 1 ∈ A then (1 : ℝ) else 0)) =
      ((Finset.univ.filter (fun n : Fin N => (n : ℕ) + 1 ∈ A)).card : ℝ) := by
    simp [Finset.sum_boole]
  rw [h_card]; congr 1
  apply Finset.card_bij (fun (n : Fin N) _ => (n : ℕ) + 1)
  · intro n hn; exact (Finset.mem_filter.mp hn).2
  · intro n₁ _ n₂ _ h; ext; omega
  · intro a ha
    have ha_range := hA ha; rw [Finset.mem_Icc] at ha_range
    have h1 : a - 1 < N := by omega
    refine ⟨⟨a - 1, h1⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      convert ha using 1; show a - 1 + 1 = a; omega
    · show a - 1 + 1 = a; omega


/-- Unfolds the high-frequency part as `f n - (mean of f)`. -/
lemma highFreqPart_eq_sub_div (N : ℕ) (f : Fin N → ℂ) (n : Fin N) :
    LinnikLargeSieve.highFreqPart N f n = f n - (∑ i : Fin N, f i) / N := by
  simp [LinnikLargeSieve.highFreqPart, LinnikLargeSieve.average]; ring


/-- The squared $L^2$ norm of the high-frequency part of an indicator function is at most
`|A|` (since the variance is bounded by the second moment). -/
theorem indicator_highfreq_l2_le
    (N : ℕ) (A : Finset ℕ) (hN : 0 < N) (hA : A ⊆ Finset.Icc 1 N)
    : (∑ n : Fin N, ‖LinnikLargeSieve.highFreqPart N (indicatorFn A N) n‖ ^ 2 : ℝ) ≤ A.card := by

  simp_rw [highFreqPart_eq_sub_div]

  rw [norm_sq_sub_mean_eq N hN (indicatorFn A N)]

  rw [indicator_l2_eq_card N A hN hA]

  linarith [div_nonneg (sq_nonneg ‖∑ i : Fin N, indicatorFn A N i‖)
    (Nat.cast_nonneg' N)]


/-- Centering identity in $L^2(\mathbb{Z}_p)$: subtracting the mean from `g : ZMod p → ℂ`
reduces the squared $L^2$ norm by `|∑ g|² / p`. -/
lemma norm_sq_sub_mean_zmod (p : ℕ) [NeZero p] (g : ZMod p → ℂ) :
    (∑ a : ZMod p, ‖g a - (∑ b : ZMod p, g b) / (p : ℂ)‖ ^ 2 : ℝ) =
    (∑ a : ZMod p, ‖g a‖ ^ 2 : ℝ) - ‖∑ b : ZMod p, g b‖ ^ 2 / p := by
  set S := ∑ b : ZMod p, g b
  set c := S / (p : ℂ)
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr (NeZero.pos p)
  have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  simp_rw [Complex.sq_norm, Complex.normSq_sub]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  suffices h : (p : ℝ) * normSq c - ∑ x : ZMod p, 2 * (g x * starRingEnd ℂ c).re =
      -(normSq S / p) by linarith
  have hc_normSq : (p : ℝ) * Complex.normSq c = Complex.normSq S / p := by
    have hcn : (p : ℝ) ^ 2 * Complex.normSq c = Complex.normSq S := by
      have hceq : c = S / (p : ℂ) := rfl
      rw [hceq, Complex.normSq_div]
      have hp_sq : Complex.normSq (p : ℂ) = (p : ℝ) ^ 2 := by
        simp [Complex.normSq_natCast]; ring
      rw [hp_sq]; field_simp
    have h2 : (p : ℝ) ^ 2 = p * p := by ring
    rw [h2] at hcn; field_simp at hcn ⊢; linarith
  have hsum_re : (∑ x : ZMod p, 2 * (g x * starRingEnd ℂ c).re : ℝ) =
      2 * (Complex.normSq S / p) := by
    have h_sum_eq : (∑ x : ZMod p, (g x * starRingEnd ℂ c).re : ℝ) =
        (S * starRingEnd ℂ c).re := by
      conv_rhs => rw [show S = ∑ x : ZMod p, g x from rfl]; rw [Finset.sum_mul]
      exact (Complex.re_sum Finset.univ (fun x => g x * starRingEnd ℂ c)).symm
    rw [show (∑ x : ZMod p, 2 * (g x * starRingEnd ℂ c).re : ℝ) =
        2 * ∑ x : ZMod p, (g x * starRingEnd ℂ c).re from by rw [Finset.mul_sum]]
    rw [h_sum_eq]; congr 1
    have hc_conj : starRingEnd ℂ c = starRingEnd ℂ S / (p : ℂ) := by simp [c, map_div₀]
    rw [hc_conj, div_eq_mul_inv, ← mul_assoc, Complex.mul_conj]
    rw [show ((↑(normSq S) : ℂ) * ((p : ℂ)⁻¹)).re = (normSq S : ℝ) * (p : ℝ)⁻¹ from by
      rw [show ((p : ℂ)⁻¹) = ((p⁻¹ : ℝ) : ℂ) from by push_cast; ring]
      rw [← Complex.ofReal_mul, Complex.ofReal_re]]
    ring
  linarith


/-- Rewrites the high-frequency $L^2$ norm of the mod-`p` projection as
`∑ |π_p f(a)|² - |∑ π_p f(a)|² / p`. -/
lemma projHighFreqL2Sq_eq_sub (N p : ℕ) [NeZero p] (f : Fin N → ℂ) :
    LinnikLargeSieve.projHighFreqL2Sq N p f =
    (∑ a : ZMod p, ‖LinnikLargeSieve.modProjection N p f a‖ ^ 2 : ℝ) -
    ‖∑ a : ZMod p, LinnikLargeSieve.modProjection N p f a‖ ^ 2 / p := by
  have h := norm_sq_sub_mean_zmod p (LinnikLargeSieve.modProjection N p f)
  simp only [LinnikLargeSieve.projHighFreqL2Sq, LinnikLargeSieve.l2NormSq_ZMod,
    LinnikLargeSieve.highFreqPart_ZMod]
  refine Eq.trans ?_ h
  congr 1
  ext a; congr 1; ring


/-- The sum of the mod-`p` projection over `ZMod p` equals the full sum of `f`. -/
lemma sum_modProjection_eq (N p : ℕ) [NeZero p] (f : Fin N → ℂ) :
    ∑ a : ZMod p, LinnikLargeSieve.modProjection N p f a = ∑ n : Fin N, f n := by
  simp only [LinnikLargeSieve.modProjection]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]


/-- The sum of the indicator function `1_A : Fin N → ℂ` over `Fin N` equals `|A|`. -/
lemma indicator_sum_eq_card (N : ℕ) (A : Finset ℕ) (hN : 0 < N)
    (hA : A ⊆ Finset.Icc 1 N) :
    (∑ n : Fin N, indicatorFn A N n) = (A.card : ℂ) := by
  simp only [indicatorFn]
  rw [show (∑ n : Fin N, (if (n : ℕ) + 1 ∈ A then (1 : ℂ) else 0)) =
      ((Finset.univ.filter (fun n : Fin N => (n : ℕ) + 1 ∈ A)).card : ℂ) from by
    rw [← Finset.sum_filter]; simp [Finset.sum_const]]
  congr 1
  apply Finset.card_bij (fun (n : Fin N) _ => (n : ℕ) + 1)
  · intro n hn; exact (Finset.mem_filter.mp hn).2
  · intro n₁ _ n₂ _ h; ext; omega
  · intro a ha
    have ha_range := hA ha; rw [Finset.mem_Icc] at ha_range
    refine ⟨⟨a - 1, by omega⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      convert ha using 1; show a - 1 + 1 = a; omega
    · show a - 1 + 1 = a; omega


/-- Lower bound on the Linnik LHS for indicator functions of sets with small projections:
if `|π_p(A)| ≤ 0.99 p` for each `p ∈ P_{N^{1/2}}`, then
`(1/100) · |P_{N^{1/2}}| · |A|² / N^{1/2} ≤ linnikLHS N (N^{1/2}) 1_A`. -/
theorem high_freq_energy_lower_bound
    (N : ℕ) (A : Finset ℕ) (hN : 4 ≤ N) (hA : A ⊆ Finset.Icc 1 N)
    (hSmall : hasSmallProjections A N)
    : (1 / 100 : ℝ) * (LinnikLargeSieve.primesInRange (Nat.sqrt N)).card *
      ((A.card : ℝ) ^ 2 / (Nat.sqrt N : ℝ)) ≤
      LinnikLargeSieve.linnikLHS N (Nat.sqrt N) (indicatorFn A N) := by
  set M := Nat.sqrt N
  set f := indicatorFn A N

  rw [show (1 / 100 : ℝ) * (LinnikLargeSieve.primesInRange M).card *
      ((A.card : ℝ) ^ 2 / (M : ℝ)) =
      ∑ _p ∈ LinnikLargeSieve.primesInRange M, (1 / 100 : ℝ) * (A.card : ℝ) ^ 2 / M from by
    rw [Finset.sum_const, nsmul_eq_mul]; ring]

  simp only [LinnikLargeSieve.linnikLHS]
  apply Finset.sum_le_sum
  intro p hp

  have hp_prime : Nat.Prime p := by
    simp [LinnikLargeSieve.primesInRange, Finset.mem_filter] at hp; exact hp.2
  have hp_ne : p ≠ 0 := hp_prime.ne_zero
  simp only [dif_neg hp_ne]
  haveI : NeZero p := ⟨hp_ne⟩

  have hp_le_M : p ≤ M := by
    simp [LinnikLargeSieve.primesInRange, Finset.mem_filter, Finset.mem_Icc] at hp; exact hp.1.2
  have hM_pos : (0 : ℝ) < (M : ℝ) := by
    have : 2 ≤ M := Nat.le_sqrt'.mpr (by omega)
    exact_mod_cast show 0 < M by omega
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp_prime.pos


  suffices h : (1 / 100 : ℝ) * (A.card : ℝ) ^ 2 / (p : ℝ) ≤
      LinnikLargeSieve.projHighFreqL2Sq N p f by
    calc (1 / 100 : ℝ) * (A.card : ℝ) ^ 2 / M
        ≤ (1 / 100 : ℝ) * (A.card : ℝ) ^ 2 / p := by
          apply div_le_div_of_nonneg_left (by positivity) hp_pos (by exact_mod_cast hp_le_M)
      _ ≤ LinnikLargeSieve.projHighFreqL2Sq N p f := h


  rw [projHighFreqL2Sq_eq_sub]

  have hN_pos : 0 < N := by omega
  have h_sum_f : ∑ n : Fin N, f n = (A.card : ℂ) :=
    indicator_sum_eq_card N A hN_pos hA
  have h_sum_g : ∑ a : ZMod p, LinnikLargeSieve.modProjection N p f a = (A.card : ℂ) := by
    rw [sum_modProjection_eq]; exact h_sum_f

  have h_norm_sum : ‖∑ a : ZMod p, LinnikLargeSieve.modProjection N p f a‖ ^ 2 =
      (A.card : ℝ) ^ 2 := by
    rw [h_sum_g]; simp [Complex.norm_natCast]
  rw [h_norm_sum]


  suffices h_l2_lower : (A.card : ℝ) ^ 2 / (0.99 * p) ≤
      ∑ a : ZMod p, ‖LinnikLargeSieve.modProjection N p f a‖ ^ 2 by
    have h1 : (1 / 100 : ℝ) * (A.card : ℝ) ^ 2 / p + (A.card : ℝ) ^ 2 / p =
        (101 / 100 : ℝ) * ((A.card : ℝ) ^ 2 / p) := by ring
    have h2 : (101 / 100 : ℝ) * ((A.card : ℝ) ^ 2 / p) ≤ (A.card : ℝ) ^ 2 / (0.99 * p) := by
      have hp_pos' : (0 : ℝ) < p := hp_pos
      have hA_div_pos : (0 : ℝ) ≤ (A.card : ℝ) ^ 2 / p := div_nonneg (sq_nonneg _) hp_pos'.le
      have h_ineq : (101 : ℝ) / 100 ≤ 1 / 0.99 := by norm_num
      calc (101 / 100 : ℝ) * ((A.card : ℝ) ^ 2 / p)
          ≤ (1 / 0.99 : ℝ) * ((A.card : ℝ) ^ 2 / p) := by nlinarith
        _ = (A.card : ℝ) ^ 2 / (0.99 * p) := by field_simp
    linarith

  set g := LinnikLargeSieve.modProjection N p f
  suffices h_Asq : (A.card : ℝ) ^ 2 ≤ 0.99 * p * ∑ a : ZMod p, ‖g a‖ ^ 2 by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 0.99 * p)]; linarith
  have h_A_le : (A.card : ℝ) ≤ ∑ a : ZMod p, ‖g a‖ := by
    have h1 : (A.card : ℝ) = ‖∑ a : ZMod p, g a‖ := by
      rw [h_sum_g]; simp only [Complex.norm_natCast]
    rw [h1]; exact norm_sum_le _ _
  have h_proj_card : ((projImage A p).card : ℝ) ≤ 0.99 * p := by
    calc ((projImage A p).card : ℝ)
        ≤ (Nat.floor (0.99 * (p : ℝ)) : ℝ) := by exact_mod_cast hSmall p hp hp_prime
      _ ≤ 0.99 * p := Nat.floor_le (by positivity)

  set S := Finset.univ.filter (fun a : ZMod p => g a ≠ 0)
  have h_supp_le : (S.card : ℝ) ≤ 0.99 * p := by
    have h_card_le : S.card ≤ (projImage A p).card := by
      apply Finset.card_le_card_of_injOn (· + 1) (fun a ha => ?_) (fun a _ b _ h => add_right_cancel h)
      simp only [S, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha
      simp only [g, LinnikLargeSieve.modProjection, f, indicatorFn] at ha
      simp only [projImage, Finset.mem_coe, Finset.mem_image]
      by_contra h_abs
      exact ha (Finset.sum_eq_zero (fun n _ => by
        split_ifs with h1 h2
        · exact absurd ⟨(n : ℕ) + 1, h2, by push_cast; rw [h1]⟩ h_abs
        all_goals rfl))
    calc (S.card : ℝ) ≤ (projImage A p).card := by exact_mod_cast h_card_le
      _ ≤ 0.99 * p := h_proj_card

  have h_sum_eq : ∑ a : ZMod p, ‖g a‖ = ∑ a ∈ S, ‖g a‖ := by
    symm; apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a _ ha
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at ha; simp [ha]
  have h_sum_sq_eq : ∑ a : ZMod p, ‖g a‖ ^ 2 = ∑ a ∈ S, ‖g a‖ ^ 2 := by
    symm; apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a _ ha
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at ha; simp [ha]
  calc (A.card : ℝ) ^ 2
      ≤ (∑ a : ZMod p, ‖g a‖) ^ 2 := sq_le_sq' (by linarith [h_A_le]) h_A_le
    _ = (∑ a ∈ S, ‖g a‖) ^ 2 := by rw [h_sum_eq]
    _ ≤ S.card * ∑ a ∈ S, ‖g a‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    _ ≤ (0.99 * p) * ∑ a ∈ S, ‖g a‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_right h_supp_le
        exact Finset.sum_nonneg (fun a _ => sq_nonneg _)
    _ = 0.99 * p * ∑ a : ZMod p, ‖g a‖ ^ 2 := by rw [← h_sum_sq_eq]

/-- Corollary 5 (Large sieve, size bound): if `A ⊆ [N]` and `|π_p(A)| ≤ 0.99 p` for every
prime `p ∈ P_{N^{1/2}}`, then `|A| ≲ N^{1/2}` (up to logarithmic factors:
`|A| ≤ C · √N · log N`). -/
theorem corollary5_large_sieve_size :
    ∃ C : ℝ, C > 0 ∧ ∃ (N₀ : ℕ), ∀ (N : ℕ) (A : Finset ℕ),
      N₀ ≤ N →
      A ⊆ Finset.Icc 1 N →
      hasSmallProjections A N →
      (A.card : ℝ) ≤ C * Real.sqrt N * Real.log N := by
  obtain ⟨C_ls, hC_ls_pos, h_linnik⟩ := LinnikLargeSieve.linnik_large_sieve
  obtain ⟨N₀_primes, h_primes⟩ := primes_in_dyadic_range_lower_bound
  refine ⟨800 * C_ls + 1, by positivity, ⟨max (N₀_primes ^ 2 + 1) 16, ?_⟩⟩
  intro N A hN_large hAsub hSmall
  have hN_ge16 : 16 ≤ N := le_trans (le_max_right _ _) hN_large
  have hN_pos : (0 : ℕ) < N := by omega
  have hN_real_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  have hsqrt_pos : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr hN_real_pos
  have hlogN_pos : (0 : ℝ) < Real.log N := Real.log_pos (by exact_mod_cast show 1 < N by omega)
  set M := Nat.sqrt N
  have hM_ge4 : 4 ≤ M := Nat.le_sqrt'.mpr (show 4 ^ 2 ≤ N by omega)
  have hM_pos : (0 : ℕ) < M := by omega
  have hM_real_pos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM_pos
  have hM_sq_le : M ^ 2 ≤ N := Nat.sqrt_le' N
  rcases Nat.eq_zero_or_pos A.card with hA0 | hA_pos
  · simp [hA0]; positivity
  have hAcard_pos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hA_pos
  have hN0_le_M : N₀_primes ≤ M := Nat.le_sqrt'.mpr
    (show N₀_primes ^ 2 ≤ N from le_trans (Nat.le_of_lt_succ (by omega)) (le_trans (le_max_left _ _) hN_large))
  have h_prime_count := h_primes M hN0_le_M
  have hlogM_pos : (0 : ℝ) < Real.log M :=
    Real.log_pos (by exact_mod_cast show 1 < M by omega)
  have hP_card_pos : (0 : ℝ) < ((LinnikLargeSieve.primesInRange M).card : ℝ) := by
    have : (0 : ℝ) < (M : ℝ) / (4 * Real.log M) := div_pos hM_real_pos (by positivity)
    linarith

  have h_upper := h_linnik N M hN_pos hM_pos hM_sq_le (indicatorFn A N)
  have h_l2 := indicator_highfreq_l2_le N A hN_pos hAsub
  have h_linnik_bound : LinnikLargeSieve.linnikLHS N M (indicatorFn A N) ≤
      C_ls * ((N : ℝ) / (M : ℝ)) * (A.card : ℝ) := by
    calc LinnikLargeSieve.linnikLHS N M (indicatorFn A N)
        ≤ C_ls * ((N : ℝ) / (M : ℝ)) *
          ∑ n : Fin N, ‖LinnikLargeSieve.highFreqPart N (indicatorFn A N) n‖ ^ 2 := h_upper
      _ ≤ C_ls * ((N : ℝ) / (M : ℝ)) * (A.card : ℝ) := by gcongr

  have h_lower := high_freq_energy_lower_bound N A (by omega : 4 ≤ N) hAsub hSmall

  have h_key : (1 / 100 : ℝ) * (LinnikLargeSieve.primesInRange M).card *
      (A.card : ℝ) ≤ C_ls * (N : ℝ) := by
    have h_combined : (1 / 100 : ℝ) * ↑(LinnikLargeSieve.primesInRange M).card *
        ((A.card : ℝ) ^ 2 / (M : ℝ)) ≤
        C_ls * ((N : ℝ) / (M : ℝ)) * (A.card : ℝ) :=
      le_trans h_lower h_linnik_bound

    have h1 : (1 / 100 : ℝ) * ↑(LinnikLargeSieve.primesInRange M).card *
        (A.card : ℝ) ^ 2 ≤ C_ls * (N : ℝ) * (A.card : ℝ) := by
      have hM_ne : (M : ℝ) ≠ 0 := ne_of_gt hM_real_pos
      have lhs_eq : (1 / 100 : ℝ) * ↑(LinnikLargeSieve.primesInRange M).card *
          ((A.card : ℝ) ^ 2 / (M : ℝ)) * M =
          (1 / 100 : ℝ) * ↑(LinnikLargeSieve.primesInRange M).card * (A.card : ℝ) ^ 2 := by
        field_simp
      have rhs_eq : C_ls * ((N : ℝ) / (M : ℝ)) * (A.card : ℝ) * M =
          C_ls * (N : ℝ) * (A.card : ℝ) := by
        field_simp
      nlinarith [mul_le_mul_of_nonneg_right h_combined (le_of_lt hM_real_pos)]

    nlinarith [sq_nonneg (A.card : ℝ)]

  have h_A_le : (A.card : ℝ) ≤ 100 * C_ls * (N : ℝ) /
      ((LinnikLargeSieve.primesInRange M).card : ℝ) := by
    rw [le_div_iff₀ hP_card_pos]; linarith

  have h_NdivM : (N : ℝ) / (M : ℝ) ≤ 2 * Real.sqrt N := by
    rw [div_le_iff₀ hM_real_pos]
    have h_sqrt_N : Real.sqrt N * Real.sqrt N = (N : ℝ) :=
      Real.mul_self_sqrt (show (0 : ℝ) ≤ N by positivity)
    have h_M_ge_half : (M : ℝ) ≥ Real.sqrt N - 1 := by
      have hlt : N < (M + 1) ^ 2 := Nat.lt_succ_sqrt' N
      have hlt_real : (N : ℝ) < ((M : ℝ) + 1) ^ 2 := by exact_mod_cast hlt
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ N from by positivity)]
    have hsqrt_ge2 : (2 : ℝ) ≤ Real.sqrt N := by
      have h4 : (4 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 4 ≤ N by omega)
      have := Real.sqrt_le_sqrt h4
      have h_sqrt4 : Real.sqrt 4 = 2 := by norm_num
      linarith
    nlinarith

  have h_logM : Real.log (M : ℝ) ≤ Real.log N :=
    Real.log_le_log (by positivity) (Nat.cast_le.mpr (Nat.sqrt_le_self N))

  calc (A.card : ℝ)
      ≤ 100 * C_ls * (N : ℝ) / ((LinnikLargeSieve.primesInRange M).card : ℝ) := h_A_le
    _ ≤ 100 * C_ls * (N : ℝ) / ((M : ℝ) / (4 * Real.log M)) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity) h_prime_count
    _ = 400 * C_ls * ((N : ℝ) / (M : ℝ)) * Real.log M := by
        rw [div_div_eq_mul_div]; ring
    _ ≤ 400 * C_ls * (2 * Real.sqrt N) * Real.log N := by
        gcongr
    _ = 800 * C_ls * Real.sqrt N * Real.log N := by ring
    _ ≤ (800 * C_ls + 1) * Real.sqrt N * Real.log N := by nlinarith

end LargeSieveSize

end
