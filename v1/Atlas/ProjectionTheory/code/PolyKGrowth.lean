/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProjectionTheory.code.PolyK
import Atlas.ProjectionTheory.code.PlunneckeLemma

open scoped Pointwise

namespace PlunneckeInequality

/-- **Polynomial growth corollary.** If `0 < s < t < 1`, then there exists `K = K(s,t)`
such that for every prime `p` and every `A ⊆ 𝔽_p` with `|A| = p^s` we have
`|poly_K(A)| ≥ p^t`. -/
theorem poly_k_growth (s t : ℝ) (hs : 0 < s) (hst : s < t) (ht : t < 1) :
    ∃ K : ℕ,
      ∀ (p : ℕ) [Fact (Nat.Prime p)] (A : Finset (ZMod p)),
        (A.card : ℝ) = (p : ℝ) ^ s →
        ((poly_k K A).card : ℝ) ≥ (p : ℝ) ^ t := by


  sorry

end PlunneckeInequality
