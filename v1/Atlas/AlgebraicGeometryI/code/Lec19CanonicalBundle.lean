/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Atlas.AlgebraicGeometryI.code.PicardProjective

noncomputable section

open KaehlerDifferential Module PicardProjective

universe u


/-- Definition 37 (Lecture 19). The canonical module `ω = ∧^{d+1} Ω` of the polynomial ring
`k[x_0,…,x_d]`, the algebraic model of the canonical bundle on affine `(d+1)`-space. -/
def canonicalModule (k : Type u) [Field k] (d : ℕ) :
    Submodule (MvPolynomial (Fin (d + 1)) k)
      (ExteriorAlgebra (MvPolynomial (Fin (d + 1)) k) (Ω[MvPolynomial (Fin (d + 1)) k⁄k])) :=
  ⋀[MvPolynomial (Fin (d + 1)) k]^(d + 1) (Ω[MvPolynomial (Fin (d + 1)) k⁄k])

/-- The canonical module on affine `(d+1)`-space is free of rank one (the top exterior power
of a rank `d+1` module). -/
theorem canonicalModule_rank_one (k : Type u) [Field k] (d : ℕ) :
    Module.finrank (MvPolynomial (Fin (d + 1)) k) (canonicalModule k d) = 1 := by
  unfold canonicalModule
  rw [exteriorPower.finrank_eq,
    Module.finrank_eq_card_basis (mvPolynomialBasis k (Fin (d + 1))),
    Fintype.card_fin, Nat.choose_self]

/-- The canonical module on affine `(d+1)`-space is a free module. -/
theorem canonicalModule_free (k : Type u) [Field k] (d : ℕ) :
    Module.Free (MvPolynomial (Fin (d + 1)) k) (canonicalModule k d) := by
  unfold canonicalModule; exact inferInstance


/-- The canonical sheaf `ω_{ℙⁿ}` viewed as an element of the graded Picard group of `ℙⁿ`. -/
noncomputable def canonicalSheafInPicard (n : ℕ) (k : Type*) [Field k] :
    GradedPicardGroup (Fin (n + 1)) k := by sorry


/-- The canonical bundle on `ℙⁿ` has degree `-(n+1)` in `Pic(ℙⁿ) ≃ ℤ`; this is the
consequence of the Euler sequence taken with top exterior powers. -/
theorem euler_sequence_canonical_degree {k : Type*} [Field k] (n : ℕ) :
    (PicardProjective.gradedPicardGroup_equiv_int k n)
      (canonicalSheafInPicard n k) = -(↑n + 1 : ℤ) := by sorry

/-- The canonical sheaf on `ℙⁿ` is isomorphic to the twist `O(-(n+1))`. -/
theorem canonical_projective_space_eq {k : Type*} [Field k] (n : ℕ) :
    canonicalSheafInPicard n k =
      PicardProjective.twistingSheafPow n k (-(↑n + 1)) := by
  apply (PicardProjective.gradedPicardGroup_equiv_int k n).injective
  rw [euler_sequence_canonical_degree, PicardProjective.degree_twistingSheafPow]

/-- Restated degree formula: the image of `K_{ℙⁿ}` in `Pic(ℙⁿ) ≃ ℤ` is `-(n+1)`. -/
theorem canonical_projective_space_degree {k : Type*} [Field k] (n : ℕ) :
    (PicardProjective.gradedPicardGroup_equiv_int k n)
      (canonicalSheafInPicard n k) = -(↑n + 1 : ℤ) :=
  euler_sequence_canonical_degree n

end
