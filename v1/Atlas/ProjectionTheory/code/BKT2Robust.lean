/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace BourgainKatzTaoRobust

/-- **Bourgain–Katz–Tao 2 (robust version).** With the same setup as BKT (`X ⊂ 𝔽_p²`
of size `p^{s_X}`, `D ⊂ 𝔽_p` of size `p^{s_D}` with `0 < s_X < 2`, `0 < s_D`), there
exists `ε = ε(s_X, s_D) > 0` and a direction `t ∈ D` such that the projection
`π_t : (x₁, x₂) ↦ x₁ + t·x₂` is robust: for every `Y ⊆ X` with `|Y| ≥ p^{-ε} |X|`,
`|π_t(Y)| ≥ p^ε |X|^{1/2}`. -/
theorem bkt2_robust_projection_bound
    (s_X s_D : ℝ) (hs_X : 0 < s_X) (hs_X' : s_X < 2) (hs_D : 0 < s_D) :
    ∃ ε : ℝ, ε > 0 ∧
      ∀ (p : ℕ) [Fact (Nat.Prime p)]
        (X : Finset (ZMod p × ZMod p)) (D : Finset (ZMod p)),
        X.card = ⌊(p : ℝ) ^ s_X⌋₊ →
        D.card = ⌊(p : ℝ) ^ s_D⌋₊ →
        ∃ t ∈ D, ∀ Y : Finset (ZMod p × ZMod p), Y ⊆ X →
          (Y.card : ℝ) ≥ (p : ℝ) ^ (-ε) * (X.card : ℝ) →
            ((Finset.image (fun x => x.1 + t * x.2) Y).card : ℝ) ≥
              (p : ℝ) ^ ε * (X.card : ℝ) ^ ((1 : ℝ) / 2) := by sorry

end BourgainKatzTaoRobust
