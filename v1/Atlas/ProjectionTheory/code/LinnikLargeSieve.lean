/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset Complex

noncomputable section

namespace LinnikLargeSieve

/-- The set `P_M` of primes lying in the dyadic interval `[M/2, M]`. -/
def primesInRange (M : ℕ) : Finset ℕ :=
  (Finset.Icc (M / 2) M).filter Nat.Prime

/-- Mod-`p` projection of `f : Fin N → ℂ`: $(\pi_p f)(a) = \sum_{n \equiv a \pmod p} f(n)$. -/
def modProjection (N : ℕ) (p : ℕ) (f : Fin N → ℂ) (a : ZMod p) : ℂ :=
  ∑ n : Fin N, if ((n : ℕ) : ZMod p) = a then f n else 0

/-- Average value of `f : Fin N → ℂ`: $\bar f = \tfrac{1}{N} \sum_n f(n)$. -/
def average (N : ℕ) (f : Fin N → ℂ) : ℂ :=
  (1 / (N : ℂ)) * ∑ n : Fin N, f n

/-- High-frequency part `f_H = f - \bar f` of `f : Fin N → ℂ`. -/
def highFreqPart (N : ℕ) (f : Fin N → ℂ) : Fin N → ℂ :=
  fun n => f n - average N f

/-- Squared $L^2$ norm of `g : ZMod p → ℂ`. -/
def l2NormSq_ZMod (p : ℕ) [NeZero p] (g : ZMod p → ℂ) : ℝ :=
  ∑ a : ZMod p, ‖g a‖ ^ 2

/-- High-frequency part of `g : ZMod p → ℂ`: `g(a) - (1/p) ∑_b g(b)`. -/
def highFreqPart_ZMod (p : ℕ) [NeZero p] (g : ZMod p → ℂ) : ZMod p → ℂ :=
  fun a => g a - (1 / (p : ℂ)) * ∑ b : ZMod p, g b

/-- Squared $L^2$ norm of the high-frequency part of the mod-`p` projection:
`‖(π_p f)_H‖_{L^2}^2`. -/
def projHighFreqL2Sq (N : ℕ) (p : ℕ) [NeZero p] (f : Fin N → ℂ) : ℝ :=
  l2NormSq_ZMod p (highFreqPart_ZMod p (modProjection N p f))

/-- Left-hand side of Linnik's large sieve inequality:
$\sum_{p \in P_M} \|(\pi_p f)_H\|_{L^2}^2$. -/
def linnikLHS (N M : ℕ) (f : Fin N → ℂ) : ℝ :=
  ∑ p ∈ primesInRange M,
    if hp : p = 0 then 0
    else haveI : NeZero p := ⟨hp⟩; projHighFreqL2Sq N p f

/-- Fourier transform on $\mathbb{Z}$: $\hat f(\xi) = \sum_n f(n) e^{-2\pi i \xi n}$. -/
def fourierZ (N : ℕ) (f : Fin N → ℂ) (ξ : ℝ) : ℂ :=
  ∑ n : Fin N, f n * Complex.exp (-2 * ↑Real.pi * Complex.I * ↑ξ * ↑(n : ℕ))

/-- Bombieri–Davenport form of the analytic large sieve: for any `1/N`-separated set
`S ⊆ [0, 1)`, $\sum_{\xi \in S} |\hat f(\xi)|^2 \le (2N - 1) \sum_n |f(n)|^2$. -/
theorem bombieri_davenport_bound (N : ℕ) (hN : 0 < N) (S : Finset ℝ)
    (hrange : ∀ x ∈ S, 0 ≤ x ∧ x < 1)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → (1 : ℝ) / N ≤ |x - y|)
    (f : Fin N → ℂ) :
    (∑ ξ ∈ S, ‖fourierZ N f ξ‖ ^ 2 : ℝ) ≤ (2 * ↑N - 1) * ∑ n : Fin N, ‖f n‖ ^ 2 := by sorry

/-- Classical large sieve inequality (existence form): there exists a constant `C > 0` such
that for any `1/N`-separated `S ⊆ [0, 1)`,
$\sum_{\xi \in S} |\hat f(\xi)|^2 \le C N \sum_n |f(n)|^2$. -/
theorem classical_large_sieve
    : ∃ C : ℝ, C > 0 ∧ ∀ (N : ℕ) (_ : 0 < N) (S : Finset ℝ),
      (∀ x ∈ S, 0 ≤ x ∧ x < 1) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → (1 : ℝ) / N ≤ |x - y|) →
      ∀ (f : Fin N → ℂ),
        (∑ ξ ∈ S, ‖fourierZ N f ξ‖ ^ 2 : ℝ) ≤
          C * N * ∑ n : Fin N, ‖f n‖ ^ 2 := by
  refine ⟨2, by norm_num, fun N hN S hrange hsep f => ?_⟩
  have hbd := bombieri_davenport_bound N hN S hrange hsep f
  have hN_pos : (0 : ℝ) < ↑N := Nat.cast_pos.mpr hN
  have hsum_nonneg : (0 : ℝ) ≤ ∑ n : Fin N, ‖f n‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => sq_nonneg _
  calc (∑ ξ ∈ S, ‖fourierZ N f ξ‖ ^ 2 : ℝ)
      ≤ (2 * ↑N - 1) * ∑ n : Fin N, ‖f n‖ ^ 2 := hbd
    _ ≤ 2 * ↑N * ∑ n : Fin N, ‖f n‖ ^ 2 := by nlinarith

/-- The Farey set $Q_M = \{\alpha/p : p \in P_M, 1 \le \alpha \le p - 1\}$ of reduced
fractions with prime denominator in `P_M`. -/
def fareySet (M : ℕ) : Finset ℝ :=
  (primesInRange M).biUnion fun p =>
    (Finset.Icc 1 (p - 1)).image fun (α : ℕ) => (α : ℝ) / (p : ℝ)

/-- Every element of `fareySet M` lies in `[0, 1)`. -/
lemma fareySet_range (M : ℕ) :
    ∀ x ∈ fareySet M, 0 ≤ x ∧ x < 1 := by
  intro x hx
  simp only [fareySet, mem_biUnion, mem_image, Finset.mem_Icc] at hx
  obtain ⟨p, hp_mem, α, ⟨hα_lo, hα_hi⟩, rfl⟩ := hx
  simp only [primesInRange, mem_filter, Finset.mem_Icc] at hp_mem
  have hp_prime := hp_mem.2
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp_prime.pos
  constructor
  · exact div_nonneg (by positivity) hp_pos.le
  · rw [div_lt_one hp_pos]
    exact_mod_cast Nat.lt_of_le_of_lt hα_hi (Nat.sub_lt hp_prime.pos Nat.one_pos)

/-- Separation property of the Farey set: any two distinct $\alpha_1/p_1, \alpha_2/p_2 \in Q_M$
satisfy $|\alpha_1/p_1 - \alpha_2/p_2| \ge 1/M^2$. -/
lemma fareySet_separated (M : ℕ) :
    ∀ x ∈ fareySet M, ∀ y ∈ fareySet M, x ≠ y → (1 : ℝ) / (M ^ 2 : ℝ) ≤ |x - y| := by
  intro x hx y hy hxy
  simp only [fareySet, mem_biUnion, mem_image, Finset.mem_Icc, primesInRange, mem_filter] at hx hy
  obtain ⟨p₁, ⟨hp₁_range, hp₁_prime⟩, α₁, ⟨hα₁_lo, hα₁_hi⟩, hx_eq⟩ := hx
  obtain ⟨p₂, ⟨hp₂_range, hp₂_prime⟩, α₂, ⟨hα₂_lo, hα₂_hi⟩, hy_eq⟩ := hy
  subst hx_eq; subst hy_eq
  have hp₁_pos : (0 : ℝ) < p₁ := Nat.cast_pos.mpr hp₁_prime.pos
  have hp₂_pos : (0 : ℝ) < p₂ := Nat.cast_pos.mpr hp₂_prime.pos
  have hM₁ : p₁ ≤ M := hp₁_range.2
  have hM₂ : p₂ ≤ M := hp₂_range.2
  have hdiff : (α₁ : ℝ) / p₁ - (α₂ : ℝ) / p₂ =
      ((α₁ : ℝ) * p₂ - (α₂ : ℝ) * p₁) / (p₁ * p₂) := by field_simp
  rw [hdiff]
  have hnum_ne : (α₁ : ℤ) * p₂ - (α₂ : ℤ) * p₁ ≠ 0 := by
    intro h
    apply hxy
    have h2 : (α₁ : ℝ) * p₂ = (α₂ : ℝ) * p₁ := by
      have : ((α₁ : ℤ) * (p₂ : ℤ) : ℤ) = ((α₂ : ℤ) * (p₁ : ℤ) : ℤ) := by omega
      exact_mod_cast this
    field_simp; linarith
  have hnum_abs : (1 : ℝ) ≤ |((α₁ : ℝ) * (p₂ : ℝ) - (α₂ : ℝ) * (p₁ : ℝ))| := by
    have h1 : (1 : ℤ) ≤ |((α₁ : ℤ) * p₂ - (α₂ : ℤ) * p₁)| := Int.one_le_abs hnum_ne
    exact_mod_cast h1
  have hprod_le : (p₁ : ℝ) * p₂ ≤ (M : ℝ) ^ 2 := by
    have h : (p₁ * p₂ : ℕ) ≤ M ^ 2 := by
      calc p₁ * p₂ ≤ M * M := Nat.mul_le_mul hM₁ hM₂
        _ = M ^ 2 := (Nat.pow_two M).symm
    exact_mod_cast h
  have hprod_pos : (0 : ℝ) < (p₁ : ℝ) * p₂ := mul_pos hp₁_pos hp₂_pos
  have hM_pos : (0 : ℕ) < M := Nat.pos_of_ne_zero (by
    intro hM0; subst hM0; exact absurd (Nat.le_zero.mp hM₁) (Nat.Prime.ne_zero hp₁_prime))
  have hM2_pos : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
  rw [abs_div, abs_of_pos hprod_pos]
  rw [div_le_div_iff₀ hM2_pos hprod_pos, one_mul]
  calc (p₁ : ℝ) * p₂ ≤ (M : ℝ) ^ 2 := hprod_le
    _ = 1 * (M : ℝ) ^ 2 := (one_mul _).symm
    _ ≤ |((α₁ : ℝ) * (p₂ : ℝ) - (α₂ : ℝ) * (p₁ : ℝ))| * (M : ℝ) ^ 2 := by gcongr


/-- Per-prime bound expressing $\|(\pi_p f)_H\|_{L^2}^2$ via Fourier coefficients of `f_H`
at fractions `α/p` for $\alpha = 1, \ldots, p - 1$. -/
theorem projHighFreq_le_farey_term
    (N M p : ℕ) [NeZero p] (hp : Nat.Prime p) (hpM : p ∈ primesInRange M)
    (hM : 0 < M) (f : Fin N → ℂ) :
    projHighFreqL2Sq N p f ≤
      (2 : ℝ) / ↑M * ∑ α ∈ (Finset.Icc 1 (p - 1)),
        ‖fourierZ N (highFreqPart N f) ((↑α : ℝ) / (↑p : ℝ))‖ ^ 2 := by sorry

/-- For distinct primes `p₁, p₂ ∈ P_M`, the corresponding sets of fractions
`{α/p : 1 ≤ α ≤ p - 1}` are disjoint. -/
lemma fareySet_pairwiseDisjoint (M : ℕ) :
    (↑(primesInRange M) : Set ℕ).PairwiseDisjoint fun p =>
      (Finset.Icc 1 (p - 1)).image fun (α : ℕ) => (α : ℝ) / (p : ℝ) := by
  intro p₁ hp₁ p₂ hp₂ hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [mem_image, Finset.mem_Icc] at hx₁ hx₂
  obtain ⟨α₁, ⟨hα₁_lo, hα₁_hi⟩, hx₁_eq⟩ := hx₁
  obtain ⟨α₂, ⟨hα₂_lo, hα₂_hi⟩, hx₂_eq⟩ := hx₂
  have hp₁_prime : Nat.Prime p₁ := by
    simp only [primesInRange, mem_coe, mem_filter, Finset.mem_Icc] at hp₁; exact hp₁.2
  have hp₂_prime : Nat.Prime p₂ := by
    simp only [primesInRange, mem_coe, mem_filter, Finset.mem_Icc] at hp₂; exact hp₂.2
  have hp₁_pos : (0 : ℝ) < ↑p₁ := Nat.cast_pos.mpr hp₁_prime.pos
  have hp₂_pos : (0 : ℝ) < ↑p₂ := Nat.cast_pos.mpr hp₂_prime.pos
  have heq : (↑α₁ : ℝ) * ↑p₂ = (↑α₂ : ℝ) * ↑p₁ := by
    have h : (↑α₁ : ℝ) / ↑p₁ = (↑α₂ : ℝ) / ↑p₂ := by linarith
    field_simp at h; linarith
  have heq3 : α₁ * p₂ = α₂ * p₁ := by exact_mod_cast heq
  have hdvd : p₁ ∣ α₁ := by
    have h : p₁ ∣ α₁ * p₂ := ⟨α₂, by linarith⟩
    rcases hp₁_prime.dvd_mul.mp h with h | h
    · exact h
    · exfalso
      rcases hp₂_prime.eq_one_or_self_of_dvd p₁ h with rfl | rfl
      · linarith [hp₁_prime.one_lt]
      · exact hne rfl
  exact absurd (Nat.le_of_dvd (by omega) hdvd) (by omega)

/-- Sums over the Farey set decompose into double sums over `(p, α)` with `p ∈ P_M`
and `1 ≤ α ≤ p - 1`. -/
lemma sum_over_fareySet (M : ℕ) (g : ℝ → ℝ) :
    ∑ ξ ∈ fareySet M, g ξ =
    ∑ p ∈ primesInRange M, ∑ α ∈ Finset.Icc 1 (p - 1), g ((↑α : ℝ) / (↑p : ℝ)) := by
  unfold fareySet
  rw [Finset.sum_biUnion (fareySet_pairwiseDisjoint M)]
  congr 1; ext p
  apply Finset.sum_image
  intro α₁ hα₁ α₂ _ heq
  have hα₁' := Finset.mem_Icc.mp hα₁
  have hp_pos : (0 : ℝ) < (↑p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  exact_mod_cast (div_left_inj' (ne_of_gt hp_pos)).mp heq

/-- Reduction step: there exists a `1/M^2`-separated set `S ⊆ [0, 1)` (namely the Farey set
`Q_M`) such that
`linnikLHS N M f ≤ (2/M) ∑_{ξ ∈ S} |\widehat{f_H}(ξ)|²`. -/
theorem linnikLHS_le_farey_sum
    (N M : ℕ) (_ : 0 < N) (hM : 0 < M) (f : Fin N → ℂ)
    : ∃ (S : Finset ℝ),
      (∀ x ∈ S, 0 ≤ x ∧ x < 1) ∧
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → (1 : ℝ) / (M ^ 2 : ℝ) ≤ |x - y|) ∧
      linnikLHS N M f ≤ (2 : ℝ) / M *
        ∑ ξ ∈ S, ‖fourierZ N (highFreqPart N f) ξ‖ ^ 2 := by
  refine ⟨fareySet M, fareySet_range M, fareySet_separated M, ?_⟩

  simp only [linnikLHS]
  have hle : ∀ p ∈ primesInRange M,
      (if hp : p = 0 then (0 : ℝ)
       else haveI : NeZero p := ⟨hp⟩; projHighFreqL2Sq N p f) ≤
      (2 : ℝ) / ↑M * ∑ α ∈ Finset.Icc 1 (p - 1),
        ‖fourierZ N (highFreqPart N f) ((↑α : ℝ) / (↑p : ℝ))‖ ^ 2 := by
    intro p hp_mem
    have hp_prime : Nat.Prime p := by
      simp only [primesInRange, mem_filter, Finset.mem_Icc] at hp_mem; exact hp_mem.2
    have hp_ne : p ≠ 0 := hp_prime.ne_zero
    simp only [dif_neg hp_ne]
    exact @projHighFreq_le_farey_term N M p ⟨hp_ne⟩ hp_prime hp_mem hM f

  calc ∑ p ∈ primesInRange M,
        (if hp : p = 0 then (0 : ℝ)
         else haveI : NeZero p := ⟨hp⟩; projHighFreqL2Sq N p f)
      ≤ ∑ p ∈ primesInRange M,
        ((2 : ℝ) / ↑M * ∑ α ∈ Finset.Icc 1 (p - 1),
          ‖fourierZ N (highFreqPart N f) ((↑α : ℝ) / (↑p : ℝ))‖ ^ 2) :=
        Finset.sum_le_sum hle
    _ = (2 : ℝ) / ↑M * ∑ p ∈ primesInRange M,
        ∑ α ∈ Finset.Icc 1 (p - 1),
          ‖fourierZ N (highFreqPart N f) ((↑α : ℝ) / (↑p : ℝ))‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ = (2 : ℝ) / ↑M *
        ∑ ξ ∈ fareySet M, ‖fourierZ N (highFreqPart N f) ξ‖ ^ 2 := by
        congr 1
        exact (sum_over_fareySet M
          (fun ξ => ‖fourierZ N (highFreqPart N f) ξ‖ ^ 2)).symm

/-- Linnik's large sieve inequality: there exists `C > 0` such that for any
`f : [N] → ℂ` and any `M ≤ N^{1/2}`,
$$\sum_{p \in P_M} \|(\pi_p f)_H\|_{L^2}^2 \lesssim \frac{N}{M} \sum_n |f_H(n)|^2.$$ -/
theorem linnik_large_sieve :
    ∃ C : ℝ, C > 0 ∧ ∀ (N M : ℕ), 0 < N → 0 < M → M ^ 2 ≤ N →
      ∀ (f : Fin N → ℂ),
        linnikLHS N M f ≤
          C * ((N : ℝ) / (M : ℝ)) *
            ∑ n : Fin N, ‖highFreqPart N f n‖ ^ 2 := by
  obtain ⟨C_ls, hC_pos, h_ls⟩ := classical_large_sieve
  refine ⟨2 * C_ls, by positivity, ?_⟩
  intro N M hN hM hM2N f
  obtain ⟨S, hS_range, hS_sep, hLHS_le⟩ := linnikLHS_le_farey_sum N M hN hM f

  have hSep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → (1 : ℝ) / N ≤ |x - y| := by
    intro x hx y hy hxy
    have h := hS_sep x hx y hy hxy
    calc (1 : ℝ) / N ≤ 1 / (M ^ 2 : ℝ) := by gcongr; exact_mod_cast hM2N
      _ ≤ |x - y| := h

  have h_bound := h_ls N hN S hS_range hSep (highFreqPart N f)

  calc linnikLHS N M f
      ≤ 2 / ↑M * ∑ ξ ∈ S, ‖fourierZ N (highFreqPart N f) ξ‖ ^ 2 := hLHS_le
    _ ≤ 2 / ↑M * (C_ls * ↑N * ∑ n : Fin N, ‖highFreqPart N f n‖ ^ 2) := by gcongr
    _ = 2 * C_ls * (↑N / ↑M) * ∑ n : Fin N, ‖highFreqPart N f n‖ ^ 2 := by ring

end LinnikLargeSieve

end
