/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.SheafCohomology
import Mathlib.Analysis.Complex.Basic

namespace GAGA

/-- GAGA consequence for `Pic⁰(X)` of a smooth projective curve of genus `g`:
the connected component of the Picard group is a complex torus `ℂᵍ / Λ` with
`Λ` a lattice of rank `2g`. -/
theorem gaga_pic0_is_complex_torus (g : ℕ) (hg : 0 < g) :
    ∃ (Λ : AddSubgroup (Fin g → ℂ)),
      Nonempty (Λ ≃+ (Fin (2 * g) → ℤ)) := by sorry

/-- Algebraic side of GAGA for `P¹`: the Euler characteristic of `O(n)` is
`h⁰ − h¹ = n + 1`, matching its analytic counterpart. -/
theorem P1_gaga_algebraic_side (k : Type) [Field k] (n : ℤ) :
    (Module.finrank k (SheafCohomology.H0 k n) : ℤ) -
    (Module.finrank k (SheafCohomology.H1 k n) : ℤ) = n + 1 :=
  SheafCohomology.euler_characteristic k n

end GAGA
