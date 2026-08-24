/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Pointwise

namespace BourgainKatzTao

/-- **Bourgain–Katz–Tao sum-product theorem** (finite field case): for any prime $p$ and any
$A \subseteq \mathbb{Z}/p\mathbb{Z}$ with $1 < |A| < p$, there exists $\varepsilon > 0$ such that
$$\max(|A+A|,\ |A\cdot A|) \geq |A|^{1+\varepsilon}.$$ -/
theorem bourgain_katz_tao_sumproduct
    (p : ℕ) [hp : Fact (Nat.Prime p)] (A : Finset (ZMod p))
    (hA_lower : 1 < A.card) (hA_upper : A.card < p) :
    ∃ ε : ℝ, 0 < ε ∧
      (↑(max (A * A).card (A + A).card) : ℝ) ≥ (↑A.card : ℝ) ^ (1 + ε) := by sorry


end BourgainKatzTao
