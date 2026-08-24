/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.RamseyLocalLemma

set_option maxHeartbeats 1600000

namespace RamseyLocalLemma

open Finset Fintype

/-- Algebraic reshuffling: the hypothesis
$(\binom{k}{2}\binom{n}{k-2} + 1) \cdot 2^{1 - \binom{k}{2}} < 1/e$ is equivalent to the
form $e \cdot 2^{1 - \binom{k}{2}} \cdot (\binom{k}{2}\binom{n}{k-2} + 1) < 1$
required by the LLL. -/
lemma lll_hyp_convert (k n : ℕ)
    (h : ((Nat.choose k 2 * Nat.choose n (k - 2) + 1 : ℕ) : ℝ) *
      (2 : ℝ) ^ ((1 : ℝ) - (Nat.choose k 2 : ℝ)) < 1 / Real.exp 1) :
    Real.exp 1 * (2 : ℝ) ^ ((1 : ℝ) - (Nat.choose k 2 : ℝ)) *
      ((Nat.choose k 2 : ℝ) * (Nat.choose n (k - 2) : ℝ) + 1) < 1 := by
  have hexp : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h1 : (↑(k.choose 2 * n.choose (k - 2) + 1) : ℝ) *
      (2 : ℝ) ^ ((1 : ℝ) - ↑(k.choose 2)) * Real.exp 1 < 1 := by
    rwa [lt_div_iff₀ hexp] at h
  linarith [show Real.exp 1 * (2 : ℝ) ^ ((1 : ℝ) - ↑(k.choose 2)) *
      (↑(k.choose 2) * ↑(n.choose (k - 2)) + 1) =
    (↑(k.choose 2 * n.choose (k - 2) + 1) : ℝ) *
      (2 : ℝ) ^ ((1 : ℝ) - ↑(k.choose 2)) * Real.exp 1 from by push_cast; ring]

/-- (Theorem 1.1.9, Spencer 1977 — Ramsey lower bound via LLL) If
$(\binom{k}{2}\binom{n}{k-2} + 1) \cdot 2^{1 - \binom{k}{2}} < 1/e$, then there
exists a graph on $n$ vertices with no $k$-clique in $G$ or $G^c$, witnessing
$R(k, k) > n$. -/
theorem spencer_ramsey_lll (k n : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n)
    (h : ((Nat.choose k 2 * Nat.choose n (k - 2) + 1 : ℕ) : ℝ) *
      (2 : ℝ) ^ ((1 : ℝ) - (Nat.choose k 2 : ℝ)) < 1 / Real.exp 1) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k :=
  spencer_ramsey_lower_bound n k hk hkn (lll_hyp_convert k n h)

end RamseyLocalLemma
