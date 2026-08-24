/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Atlas.ProbabilisticMethodsInCombinatorics.code.ChromaticNumber

set_option maxHeartbeats 400000

namespace ChromaticRandom

open SimpleGraph Finset

/-- Property $\star$ for $G(n, 1/2)$ holds with high probability: for every $\varepsilon > 0$
and all large $n$, the probability that $G(n,1/2)$ contains a subset $S$ of size
$\geq n / (\log_2 n)^2$ none of whose $(k_0 - 3)$-subsets is independent is at most
$\exp(-n^{1-\varepsilon})$. -/
theorem property_star_whp :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in Filter.atTop,
      ChromaticNumber.probGnHalf n (fun G =>
        ∃ (S : Finset (Fin n)), S.card ≥ n / (Nat.log 2 n) ^ 2 ∧
          ∀ (I : Finset (Fin n)), I ⊆ S → I.card ≥ ChromaticNumber.k₀ n - 3 →
            ¬ G.IsIndepSet (↑I : Set (Fin n))) ≤
        Real.exp (-(↑n : ℝ) ^ (1 - ε)) := by sorry

/-- **Bollobás's theorem** (Theorem 8.3.2, Bollobás 1988). With high probability,
$\chi(G(n, 1/2)) \sim n / (2 \log_2 n)$. Concretely, for every $\varepsilon > 0$ and all
large $n$, $G(n, 1/2)$ is colorable with $n/(k_0 - 3) + n/(\log_2 n)^2$ colors with
probability at least $1 - \exp(-n^{1-\varepsilon})$. -/
theorem bollobas_chromatic_number :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ (n : ℕ) in Filter.atTop,
      ChromaticNumber.probGnHalf n (fun G =>
        G.Colorable (n / (ChromaticNumber.k₀ n - 3) + n / (Nat.log 2 n) ^ 2)) ≥
        1 - Real.exp (-(↑n : ℝ) ^ (1 - ε)) := by sorry

end ChromaticRandom
