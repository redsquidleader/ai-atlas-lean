/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.Uniformization
import Mathlib.NumberTheory.ArithmeticFunction.Misc

noncomputable section

open Complex ArithmeticFunction

namespace ComplexLattice

variable (τ : UpperHalfPlane)

/-- The *nome* `q = e^{2πiτ}` associated to `τ ∈ ℍ`. -/
def nome (τ : UpperHalfPlane) : ℂ :=
  Complex.exp (2 * ↑Real.pi * I * (τ : ℂ))

/-- **Lemma 19.5** (q-expansion of `g₂`). For the lattice associated to
`τ ∈ ℍ`, the Eisenstein-like coefficient `g₂` of its Weierstrass form admits the
q-expansion
`g₂(τ) = (4π⁴/3)·(1 + 240 ∑_{n≥1} σ₃(n) qⁿ)`,
where `σ₃(n)` is the divisor sum `∑_{d|n} d³`. -/
theorem g₂_qexpansion :
    (ofUpperHalfPlane τ).g₂ =
      (4 * (↑Real.pi : ℂ) ^ 4 / 3) *
        (1 + 240 * ∑' (n : ℕ), (↑(sigma 3 (n + 1)) : ℂ) * nome τ ^ (n + 1)) := by sorry

/-- **Lemma 19.5** (q-expansion of `g₃`). For the lattice associated to
`τ ∈ ℍ`, the coefficient `g₃` admits the q-expansion
`g₃(τ) = (8π⁶/27)·(1 - 504 ∑_{n≥1} σ₅(n) qⁿ)`,
where `σ₅(n) = ∑_{d|n} d⁵`. -/
theorem g₃_qexpansion :
    (ofUpperHalfPlane τ).g₃ =
      (8 * (↑Real.pi : ℂ) ^ 6 / 27) *
        (1 - 504 * ∑' (n : ℕ), (↑(sigma 5 (n + 1)) : ℂ) * nome τ ^ (n + 1)) := by sorry

/-- **Lemma 19.5** (product formula for the modular discriminant). The
discriminant `Δ(τ) = g₂(τ)³ - 27 g₃(τ)²` has the infinite-product q-expansion
`Δ(τ) = (2π)¹² · q · ∏_{n≥1} (1 - qⁿ)²⁴`. -/
theorem discriminant_product_formula :
    (ofUpperHalfPlane τ).discriminantLattice =
      (2 * (↑Real.pi : ℂ)) ^ 12 * nome τ *
        ∏' (n : ℕ), (1 - nome τ ^ (n + 1)) ^ 24 := by sorry

end ComplexLattice
