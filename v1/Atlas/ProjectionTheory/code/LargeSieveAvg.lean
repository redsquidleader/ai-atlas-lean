/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProjectionTheory.code.LinnikLargeSieve

open Finset Complex

noncomputable section

namespace LinnikLargeSieve


/-- Lower bound on the number of primes in a dyadic interval: there exists `c > 0` and
`M₀ ≥ 2` such that for all `M ≥ M₀`, the count `|P_M|` of primes in `[M/2, M]` satisfies
`c · M ≤ |P_M|`. (This is essentially a quantitative form of the Prime Number Theorem.) -/
theorem primesInRange_card_lower_bound
    : ∃ (c : ℝ) (M₀ : ℕ), c > 0 ∧ 2 ≤ M₀ ∧ ∀ M : ℕ, M₀ ≤ M →
      c * (M : ℝ) ≤ ((primesInRange M).card : ℝ) := by sorry

/-- Average over primes `p ∈ P_M` of the squared $L^2$ norm of the high-frequency part of the
mod-`p` projection: `Avg_{p ∈ P_M} ‖(π_p f)_H‖_{L^2}^2 = (1/|P_M|) · linnikLHS N M f`. -/
def avgProjHighFreqL2Sq (N M : ℕ) (f : Fin N → ℂ) : ℝ :=
  (1 / ((primesInRange M).card : ℝ)) * linnikLHS N M f

/-- Corollary 4 (Large sieve average): for `f : [N] → ℂ` and `M ≤ N^{1/2}`,
$$\operatorname{Avg}_{p \in P_M} \|(\pi_p f)_H\|_{L^2}^2 \lesssim \frac{N}{M^2} \sum_n |f_H(n)|^2.$$
-/
theorem large_sieve_avg :
    ∃ C : ℝ, C > 0 ∧ ∃ M₀ : ℕ, ∀ (N M : ℕ), 0 < N → M₀ ≤ M → M ^ 2 ≤ N →
      ∀ (f : Fin N → ℂ),
        avgProjHighFreqL2Sq N M f ≤
          C * ((N : ℝ) / ((M : ℝ) ^ 2)) *
            ∑ n : Fin N, ‖highFreqPart N f n‖ ^ 2 := by
  obtain ⟨C_linnik, hC_pos, h_linnik⟩ := linnik_large_sieve
  obtain ⟨c, M₀, hc_pos, hM₀_ge2, h_card⟩ := primesInRange_card_lower_bound
  refine ⟨C_linnik / c, div_pos hC_pos hc_pos, M₀, ?_⟩
  intro N M hN hM₀ hM2N f
  have hM_pos : (0 : ℕ) < M := by omega
  have h_card_bound : c * (M : ℝ) ≤ ((primesInRange M).card : ℝ) := h_card M hM₀
  have hcM_pos : (0 : ℝ) < c * (M : ℝ) := by positivity
  have h_card_pos : (0 : ℝ) < ((primesInRange M).card : ℝ) := by linarith
  have h_linnik_bound := h_linnik N M hN hM_pos hM2N f
  unfold avgProjHighFreqL2Sq
  have hM_ne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos


  calc (1 / ((primesInRange M).card : ℝ)) * linnikLHS N M f
      ≤ (1 / ((primesInRange M).card : ℝ)) *
          (C_linnik * (↑N / ↑M) * ∑ n : Fin N, ‖highFreqPart N f n‖ ^ 2) := by
        gcongr
      _ ≤ (1 / (c * ↑M)) *
          (C_linnik * (↑N / ↑M) * ∑ n : Fin N, ‖highFreqPart N f n‖ ^ 2) := by
        gcongr
      _ = C_linnik / c * (↑N / (↑M ^ 2)) *
          ∑ n : Fin N, ‖highFreqPart N f n‖ ^ 2 := by
        field_simp

end LinnikLargeSieve

end
