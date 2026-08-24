/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.LLLRandomVariableModel
import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter1.RamseyLowerBound

set_option maxHeartbeats 1600000

namespace RamseyLocalLemma

open Finset Fintype RamseyLowerBound MeasureTheory ProbabilityTheory LovaszLocalLemma

/-- Application of the random-variable Lovász Local Lemma to the symmetric Ramsey
problem: if $e \cdot 2^{1 - \binom{k}{2}} \cdot (\binom{k}{2}\binom{n}{k-2} + 1) \le 1$,
there exists a graph on $n$ vertices with no $k$-clique in $G$ or $G^c$. -/
theorem lovasz_local_lemma_rv_ramsey
    (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n)
    (h : Real.exp 1 * (2 : ℝ) ^ ((1 : ℝ) - (k.choose 2 : ℝ)) *
      ((k.choose 2 : ℝ) * (n.choose (k - 2) : ℝ) + 1) ≤ 1) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k := by sorry

/-- Strict-inequality form of Spencer's LLL-based Ramsey lower bound: under
$e \cdot 2^{1 - \binom{k}{2}} \cdot (\binom{k}{2}\binom{n}{k-2} + 1) < 1$, there is
a graph on $n$ vertices with no $k$-clique in $G$ or $G^c$. -/
theorem spencer_ramsey_lower_bound (n k : ℕ) (hk : 2 ≤ k) (hkn : k ≤ n)
    (h : Real.exp 1 * (2 : ℝ) ^ ((1 : ℝ) - (k.choose 2 : ℝ)) *
      ((k.choose 2 : ℝ) * (n.choose (k - 2) : ℝ) + 1) < 1) :
    ∃ G : SimpleGraph (Fin n), G.CliqueFree k ∧ Gᶜ.CliqueFree k :=
  lovasz_local_lemma_rv_ramsey n k hk hkn (le_of_lt h)

end RamseyLocalLemma
