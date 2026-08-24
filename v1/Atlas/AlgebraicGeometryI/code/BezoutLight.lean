/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Atlas.AlgebraicGeometryI.code.BezoutTheorem

set_option maxHeartbeats 400000

open MvPolynomial

/-- The degree-`n` piece of the homogeneous quotient ring `k[x₀, x₁, x₂] / I`, presented as the
quotient of the space of degree-`n` homogeneous polynomials by the corresponding piece of `I`. -/
noncomputable abbrev homogQuotPiece (k : Type*) [Field k]
    (I : Ideal (MvPolynomial (Fin 3) k)) (n : ℕ) :=
  (homogeneousSubmodule (Fin 3) k n) ⧸
    Submodule.comap (homogeneousSubmodule (Fin 3) k n).subtype (I.restrictScalars k)

/-- Predicate stating that the bivariate polynomial `f ∈ k[X][Y]` has total degree at most `n`,
i.e. for each coefficient `f.coeff i ∈ k[X]` the sum of its `X`-degree and `Y`-index `i` is `≤ n`. -/
def hasTotalDegreeAtMost {k : Type*} [CommSemiring k]
    (f : Polynomial (Polynomial k)) (n : ℕ) : Prop :=
  ∀ i, (f.coeff i).natDegree + i ≤ n

/-- Resultant degree formula: when `g` and `f` have total degrees at most `e` and `d`
respectively, the norm of `AdjoinRoot.mk g f` has degree `d * e`. -/
theorem resultant_degree_formula
    (k : Type*) [Field k]
    (g : Polynomial (Polynomial k)) (hg : g.Monic) (hirr : Irreducible g)
    (f : Polynomial (Polynomial k)) (hf : AdjoinRoot.mk g f ≠ 0)
    (d e : ℕ)
    (hg_deg : hasTotalDegreeAtMost g e)
    (hf_deg : hasTotalDegreeAtMost f d) :
    (Algebra.norm (Polynomial k) (AdjoinRoot.mk g f)).natDegree = d * e := by
  sorry

/-- Graded-affine stabilization: for large enough `n ≥ d + e - 2`, the degree-`n` piece of the
homogeneous coordinate ring of `V(f) ∩ V(g) ⊂ P²` is `k`-linearly equivalent to an affine
quotient `k[X][Y] / ⟨g', f'⟩` for suitable bivariate polynomials `g'`, `f'`. -/
theorem graded_affine_stabilization
    (k : Type*) [Field k]
    (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (f g : MvPolynomial (Fin 3) k)
    (hf_homog : f.IsHomogeneous d)
    (hg_homog : g.IsHomogeneous e)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hcoprime : IsCoprime f g) :
    ∃ (g' f' : Polynomial (Polynomial k)),
      g'.Monic ∧ Irreducible g' ∧
      AdjoinRoot.mk g' f' ≠ 0 ∧
      hasTotalDegreeAtMost g' e ∧ hasTotalDegreeAtMost f' d ∧
      ∀ n, d + e - 2 ≤ n →
        Module.finrank k (homogQuotPiece k (Ideal.span {f} ⊔ Ideal.span {g}) n) =
        Module.finrank k (Polynomial (Polynomial k) ⧸ Ideal.span {g', f'}) := by
  sorry

/-- Bezout's theorem (Thm 5.2, Thm 16.1): for coprime homogeneous polynomials `f, g` of degrees
`d`, `e` defining curves in `P²`, the Hilbert function of the quotient stabilises at `d * e`
once the degree `n` is at least `d + e - 2`. -/
theorem bezout_theorem
    (k : Type*) [Field k]
    (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (f g : MvPolynomial (Fin 3) k)
    (hf_homog : f.IsHomogeneous d)
    (hg_homog : g.IsHomogeneous e)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hcoprime : IsCoprime f g) :
    ∀ n, d + e - 2 ≤ n →
      Module.finrank k (homogQuotPiece k (Ideal.span {f} ⊔ Ideal.span {g}) n) = d * e := by

  obtain ⟨g', f', hg'_monic, hg'_irr, hf'_ne, hg'_deg, hf'_deg, hstab⟩ :=
    graded_affine_stabilization k d e hd he f g hf_homog hg_homog hf_ne hg_ne hcoprime
  intro n hn

  rw [hstab n hn]

  rw [bezout_bivariate_norm_irreducible k g' hg'_monic hg'_irr f' hf'_ne]

  rw [resultant_degree_formula k g' hg'_monic hg'_irr f' hf'_ne d e hg'_deg hf'_deg,
      Nat.mul_comm]
