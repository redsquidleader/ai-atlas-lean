/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.HilbertFormulaOdd
import Atlas.ArithmeticGeometry.code.HilbertSymbol2Adic

noncomputable section

open scoped Classical

variable {p : ℕ} [hp : Fact (Nat.Prime p)]


/-- The Legendre symbol on the natural-number value of `a : ZMod p` agrees with the
quadratic character of `ZMod p`. -/
lemma legendreSym_val (a : ZMod p) :
    legendreSym p (ZMod.val a : ℤ) = (quadraticChar (ZMod p)) a := by
  unfold legendreSym
  congr 1
  simp [ZMod.natCast_val]


/-- Bilinearity of the $p$-adic Hilbert symbol in the left argument:
$(ab, c)_p = (a, c)_p \cdot (b, c)_p$ (part of Corollary 10.10). -/
theorem padic_hilbert_mul_left (p : ℕ) [Fact (Nat.Prime p)]
    (a b c : ℚ_[p]ˣ) :
    padicHilbertSymbol p (a * b) c =
    padicHilbertSymbol p a c * padicHilbertSymbol p b c := by
  simp only [padicHilbertSymbol]
  exact hilbertSymbol.mul_left a b c


end
