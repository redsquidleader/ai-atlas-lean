/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Factorization.Basic

set_option maxHeartbeats 400000

open Filter Real Finset

noncomputable section

namespace HardyRamanujan

/-- $\omega(n)$, the number of distinct prime factors of $n$. -/
def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- Mertens' theorem: there exists a constant $C$ such that for all $n \ge 2$,
    $\Bigl| \sum_{p \le n, p\text{ prime}} 1/p - \log \log n \Bigr| \le C$. -/
theorem mertens_theorem :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      |((Finset.filter Nat.Prime (Finset.range (n + 1))).sum
        (fun p => (1 : ℝ) / (p : ℝ))) - Real.log (Real.log (n : ℝ))| ≤ C := by sorry

/-- Variance bound on $\omega$ around $\log \log N$ (a key step toward Hardy–Ramanujan):
    there is $C > 0$ such that, for all sufficiently large $N$,
    $\sum_{x = 1}^N (\omega(x) - \log \log N)^2 \le C \cdot N \log \log N$. -/
theorem omega_variance_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ (N : ℕ) in atTop,
      (∑ x ∈ Finset.Icc 1 N, ((omega x : ℝ) - Real.log (Real.log (N : ℝ))) ^ 2)
        ≤ C * (N : ℝ) * Real.log (Real.log (N : ℝ)) := by sorry

/-- Chebyshev-type step turning the variance bound into a density bound:
    if $\sum_{x = 1}^N (\omega(x) - \mu)^2 \le C N \mu$, then the proportion of
    $x \in [1, N]$ with $|\omega(x) - \mu| \ge f_N \sqrt{\mu}$ is at most $C / f_N^2$. -/
theorem chebyshev_step {N : ℕ} (hN : 0 < N) {C fN μ : ℝ}
    (hfN : 0 < fN) (hμ : 0 < μ)
    (hVarN : (∑ x ∈ Finset.Icc 1 N, ((omega x : ℝ) - μ) ^ 2) ≤ C * (N : ℝ) * μ) :
    ((Finset.filter
        (fun x => fN * Real.sqrt μ ≤ |(omega x : ℝ) - μ|)
        (Finset.Icc 1 N)).card : ℝ) / (N : ℝ) ≤ C / fN ^ 2 := by
  have hN' : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  set S := Finset.filter (fun x => fN * Real.sqrt μ ≤ |(omega x : ℝ) - μ|)
      (Finset.Icc 1 N)

  have h_sq_bound : (S.card : ℝ) * (fN ^ 2 * μ) ≤ C * (N : ℝ) * μ := by
    have h1 : (S.card : ℝ) * (fN * Real.sqrt μ) ^ 2 ≤
        ∑ x ∈ Finset.Icc 1 N, ((omega x : ℝ) - μ) ^ 2 := by
      calc (S.card : ℝ) * (fN * Real.sqrt μ) ^ 2
          = ∑ _x ∈ S, (fN * Real.sqrt μ) ^ 2 := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ x ∈ S, ((omega x : ℝ) - μ) ^ 2 := by
            apply Finset.sum_le_sum
            intro x hx
            have hxf : fN * Real.sqrt μ ≤ |(omega x : ℝ) - μ| :=
              (Finset.mem_filter.mp hx).2
            nlinarith [sq_abs ((omega x : ℝ) - μ),
              sq_nonneg (|(omega x : ℝ) - μ| - fN * Real.sqrt μ),
              mul_nonneg (le_of_lt hfN) (Real.sqrt_nonneg μ)]
        _ ≤ ∑ x ∈ Finset.Icc 1 N, ((omega x : ℝ) - μ) ^ 2 := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            intro x _ _; exact sq_nonneg _
    have h2 : (fN * Real.sqrt μ) ^ 2 = fN ^ 2 * μ := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hμ)]
    linarith [h2 ▸ h1]

  have h_cancel : (S.card : ℝ) * fN ^ 2 ≤ C * (N : ℝ) := by
    nlinarith [h_sq_bound, mul_assoc (S.card : ℝ) (fN ^ 2) μ]

  rw [div_le_div_iff₀ hN' (pow_pos hfN 2)]
  linarith

/-- Hardy–Ramanujan theorem (Theorem 4.5.1): for any $f(N) \to \infty$, the proportion of
    $x \in [1, N]$ with $|\omega(x) - \log \log N| \ge f(N) \sqrt{\log \log N}$ tends to $0$;
    equivalently, $\omega(x) = (1 + o(1)) \log \log N$ for almost all $x \le N$. -/
theorem hardy_ramanujan
    (f : ℕ → ℝ) (hf_pos : ∀ᶠ N in atTop, 0 < f N)
    (hf_tendsto : Tendsto f atTop atTop) :
    Tendsto (fun N =>
      ((Finset.filter
        (fun x => f N * Real.sqrt (Real.log (Real.log (N : ℝ)))
          ≤ |(omega x : ℝ) - Real.log (Real.log (N : ℝ))|)
        (Finset.Icc 1 N)).card : ℝ) / (N : ℝ))
      atTop (nhds 0) := by

  obtain ⟨C, hC, hVar⟩ := omega_variance_bound

  have hLogLog : ∀ᶠ (N : ℕ) in atTop, (0 : ℝ) < Real.log (Real.log ↑N) := by
    filter_upwards [eventually_ge_atTop 16] with N hN
    have hN' : (16 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hexp : Real.exp 1 < 3 := by
      have hbound := @Real.exp_bound (x := 1) (by norm_num : |(1 : ℝ)| ≤ 1) (n := 4) (by norm_num)
      have hsum : ∑ m ∈ Finset.range 4, (1 : ℝ) ^ m / ↑(Nat.factorial m) = 8/3 := by
        simp [Finset.sum_range_succ, Nat.factorial]; norm_num
      rw [hsum] at hbound
      simp [abs_of_nonneg, abs_le] at hbound
      linarith [hbound.1, hbound.2]
    have h1 : (1 : ℝ) < Real.log (N : ℝ) := by
      rw [show (1 : ℝ) = Real.log (Real.exp 1) from (Real.log_exp 1).symm]
      apply Real.log_lt_log (Real.exp_pos 1)
      calc Real.exp 1 < 3 := hexp
        _ ≤ (16 : ℝ) := by norm_num
        _ ≤ (N : ℝ) := hN'
    exact Real.log_pos h1

  apply squeeze_zero' (g := fun N => C / (f N) ^ 2)
  ·
    filter_upwards with N
    positivity
  ·
    filter_upwards [hVar, hf_pos, hLogLog,
      (eventually_atTop.mpr ⟨1, fun n hn => by omega⟩ : ∀ᶠ (N : ℕ) in atTop, 0 < N)]
      with N hVarN hfN hLL hNpos
    exact chebyshev_step hNpos hfN hLL hVarN
  ·
    exact (tendsto_const_nhds (x := C)).div_atTop
      (Filter.Tendsto.comp (Filter.tendsto_pow_atTop (α := ℝ) two_ne_zero) hf_tendsto)

end HardyRamanujan
