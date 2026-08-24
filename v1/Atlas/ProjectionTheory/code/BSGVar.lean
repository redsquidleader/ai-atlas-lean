/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Finset Pointwise

namespace BSGVar


/--
Balog–Szemerédi–Gowers variant (energy form). Let `A`, `B` be subsets of an
abelian group with `|A| = |B| = N` and additive energy
`E(A, B) ≥ K⁻¹ N³`. Then there exist `A' ⊆ A`, `B' ⊆ B` with
`|A'|, |B'| ≥ K^{-C} N` and `|A' + B'| ≤ K^{C} N` for some constant `C > 0`.
-/
theorem bsg_var
  {G : Type*} [DecidableEq G] [AddCommGroup G]
  (A B : Finset G) (N : ℕ) (K : ℝ)
  (hK : K ≥ 1)
  (hA : A.card = N) (hB : B.card = N)
  (hE : (A.addEnergy B : ℝ) ≥ K⁻¹ * (N : ℝ) ^ 3) :
  ∃ C : ℝ, C > 0 ∧
    ∃ A' B' : Finset G,
      A' ⊆ A ∧ B' ⊆ B ∧
      ((A'.card : ℝ) ≥ K ^ (-C) * N) ∧
      ((B'.card : ℝ) ≥ K ^ (-C) * N) ∧
      (((A' + B').card : ℝ) ≤ K ^ C * N) := by sorry

end BSGVar
