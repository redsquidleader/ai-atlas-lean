/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProjectionTheory.code.LargeSieveAvg

open Finset Real

namespace LargeSieve

/-- The set of primes in the dyadic interval `[M/2, M]`. -/
noncomputable def primesDyadic (M : ℕ) : Finset ℕ :=
  (Finset.Icc (M / 2) M).filter Nat.Prime

/-- The cardinality of the fiber of `A` over `a ∈ ZMod p`, i.e. the number of `n ∈ A` with
`n ≡ a (mod p)`. -/
def fiberCard (A : Finset ℕ) (p : ℕ) (a : ZMod p) : ℕ :=
  (A.filter (fun (n : ℕ) => (n : ZMod p) = a)).card

/-- Average deviation from equidistribution modulo `p`:
$\frac{1}{p} \sum_{a \in \mathbb{Z}_p} \big|\, |A \cap (a + p\mathbb{Z})| - |A|/p \,\big|$. -/
noncomputable def avgDeviationMod (A : Finset ℕ) (p : ℕ) : ℝ :=
  if hp : p = 0 then 0
  else
    haveI : NeZero p := ⟨hp⟩
    (1 / (p : ℝ)) * ∑ a : ZMod p, |((fiberCard A p a : ℝ) - (A.card : ℝ) / (p : ℝ))|

/-- The average deviation `avgDeviationMod A p` is non-negative. -/
lemma avgDeviationMod_nonneg (A : Finset ℕ) (p : ℕ) : 0 ≤ avgDeviationMod A p := by
  unfold avgDeviationMod
  split_ifs with hp
  · linarith
  · apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun a _ => abs_nonneg _)

/-- The indicator function `1_A : Fin N → ℂ`, where index `n` corresponds to the integer
`n.val + 1 ∈ [1, N]`. -/
noncomputable def indicatorFin (N : ℕ) (A : Finset ℕ) : Fin N → ℂ :=
  fun n => if (n.val + 1) ∈ A then 1 else 0

/-- $L^2$ version of the average large sieve bound: for `A ⊆ [1, N]`, the average over primes
`p ∈ P_{N^{1/2}}` of `(avgDeviationMod A p)^2` is at most `C₁ · (log N)^2 · N^{1/2}`. -/
theorem large_sieve_L2_avg_bound :
    ∃ C₁ : ℝ, C₁ > 0 ∧ ∀ (N : ℕ) (A : Finset ℕ),
      1 ≤ N →
      A ⊆ Finset.Icc 1 N →
      (1 / (primesDyadic (Nat.sqrt N)).card : ℝ) *
        ∑ p ∈ primesDyadic (Nat.sqrt N), (avgDeviationMod A p) ^ 2
      ≤ C₁ * (Real.log N) ^ 2 * (N : ℝ) ^ ((1 : ℝ) / 2) := by sorry

/-- Large sieve corollary on equidistribution mod primes: if `A ⊆ [N]` then
$$\operatorname{Avg}_{p \in P_{N^{1/2}}} \operatorname{Avg}_{a \in \mathbb{Z}_p}
\big| \pi_p \mathbf{1}_A(a) - |A|/p \big| \lessapprox N^{1/4}.$$
(Obtained from `large_sieve_L2_avg_bound` via Cauchy–Schwarz.) -/
theorem large_sieve_equidistribution_mod_primes :
    ∃ C : ℝ, C > 0 ∧ ∀ (N : ℕ) (A : Finset ℕ),
      1 ≤ N →
      A ⊆ Finset.Icc 1 N →
      (1 / (primesDyadic (Nat.sqrt N)).card : ℝ) *
        ∑ p ∈ primesDyadic (Nat.sqrt N), avgDeviationMod A p
      ≤ C * Real.log N * (N : ℝ) ^ ((1 : ℝ) / 4) := by

  obtain ⟨C₁, hC₁_pos, hL2⟩ := large_sieve_L2_avg_bound

  use Real.sqrt C₁ + 1
  refine ⟨by linarith [Real.sqrt_nonneg C₁], ?_⟩
  intro N A hN hA
  set P := primesDyadic (Nat.sqrt N)

  by_cases hP_empty : P.card = 0
  · simp [hP_empty]; positivity
  have hP_pos : 0 < P.card := Nat.pos_of_ne_zero hP_empty
  have hP_pos_real : (0 : ℝ) < (P.card : ℝ) := Nat.cast_pos.mpr hP_pos


  have hCS : ((1 / (P.card : ℝ)) * ∑ p ∈ P, avgDeviationMod A p) ^ 2
      ≤ (1 / (P.card : ℝ)) * ∑ p ∈ P, (avgDeviationMod A p) ^ 2 := by
    have h1 : ((1 / (P.card : ℝ)) * ∑ p ∈ P, avgDeviationMod A p) ^ 2
        = (∑ p ∈ P, avgDeviationMod A p) ^ 2 / (P.card : ℝ) ^ 2 := by field_simp
    have h2 : (1 / (P.card : ℝ)) * ∑ p ∈ P, (avgDeviationMod A p) ^ 2
        = (∑ p ∈ P, (avgDeviationMod A p) ^ 2) / (P.card : ℝ) := by field_simp
    rw [h1, h2, div_le_div_iff₀ (sq_pos_of_pos hP_pos_real) hP_pos_real]
    nlinarith [@sq_sum_le_card_mul_sum_sq _ ℝ _ _ _ _ P (avgDeviationMod A),
              sq_nonneg (P.card : ℝ)]

  have hL2_NA := hL2 N A hN hA
  have hLHS_sq : ((1 / (P.card : ℝ)) * ∑ p ∈ P, avgDeviationMod A p) ^ 2
      ≤ C₁ * (Real.log N) ^ 2 * (N : ℝ) ^ ((1 : ℝ) / 2) :=
    le_trans hCS hL2_NA

  have hLHS_nn : 0 ≤ (1 / (P.card : ℝ)) * ∑ p ∈ P, avgDeviationMod A p := by
    apply mul_nonneg (by positivity)
    exact Finset.sum_nonneg (fun p _ => avgDeviationMod_nonneg A p)
  have hRHS_nn : 0 ≤ C₁ * (Real.log N) ^ 2 * (N : ℝ) ^ ((1 : ℝ) / 2) := by positivity
  have hLHS_le_sqrt : (1 / (P.card : ℝ)) * ∑ p ∈ P, avgDeviationMod A p
      ≤ Real.sqrt (C₁ * (Real.log N) ^ 2 * (N : ℝ) ^ ((1 : ℝ) / 2)) := by
    rwa [Real.le_sqrt hLHS_nn hRHS_nn]


  calc (1 / (P.card : ℝ)) * ∑ p ∈ P, avgDeviationMod A p
      ≤ Real.sqrt (C₁ * (Real.log N) ^ 2 * (N : ℝ) ^ ((1 : ℝ) / 2)) := hLHS_le_sqrt
    _ = Real.sqrt C₁ * Real.sqrt ((Real.log N) ^ 2) *
        Real.sqrt ((N : ℝ) ^ ((1 : ℝ) / 2)) := by
        rw [show C₁ * (Real.log ↑N) ^ 2 * (↑N : ℝ) ^ ((1:ℝ)/2) =
            (C₁ * (Real.log ↑N) ^ 2) * ((↑N : ℝ) ^ ((1:ℝ)/2)) from by ring]
        rw [Real.sqrt_mul (mul_nonneg (le_of_lt hC₁_pos) (sq_nonneg _))]
        rw [Real.sqrt_mul (le_of_lt hC₁_pos)]
    _ = Real.sqrt C₁ * |Real.log N| * (N : ℝ) ^ ((1 : ℝ) / 4) := by
        congr 1
        · congr 1; exact Real.sqrt_sq_eq_abs _
        · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg N)]; norm_num
    _ = Real.sqrt C₁ * Real.log N * (N : ℝ) ^ ((1 : ℝ) / 4) := by
        rw [abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hN))]
    _ ≤ (Real.sqrt C₁ + 1) * Real.log N * (N : ℝ) ^ ((1 : ℝ) / 4) := by
        gcongr; linarith

end LargeSieve
