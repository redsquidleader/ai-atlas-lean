/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Pointwise Finset

namespace PlunneckeInequality

/-- **Plünnecke cube-difference expansion lemma.** If $A \subset \mathbb{F}_p$ with
$|A| = p^s$ for $0 < s < 1$, then there exists some $\varepsilon = \varepsilon(s) > 0$
such that $|A^3 - A^3| \ge p^{s + \varepsilon}$, witnessing genuine expansion under the
combined operations of (multiplicative) cubing and (additive) differencing. -/
theorem cube_diff_expansion (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ (ε : ℝ), 0 < ε ∧
      ∀ (p : ℕ) [Fact (Nat.Prime p)] (A : Finset (ZMod p)),
        (A.card : ℝ) = (p : ℝ) ^ s →
        ((A * A * A - A * A * A).card : ℝ) ≥ (p : ℝ) ^ (s + ε) := by

  refine ⟨s * (1 - s) / 8, by have h1 := sub_pos.mpr hs1; positivity, ?_⟩

  intro p hp A hA


  sorry

end PlunneckeInequality
