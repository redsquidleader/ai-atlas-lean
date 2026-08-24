/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.Lec5BezoutPascal

noncomputable section

open MvPolynomial Classical Module

namespace Lec5BezoutPascal

variable (k : Type*) [Field k]

/-- Dehomogenization with respect to the 0th coordinate: substitutes `x₀ = 1` in a
homogeneous polynomial in three variables to land in the affine chart `k[x₁, x₂]`. -/
def dehomogenize₀ : MvPolynomial (Fin 3) k →ₐ[k] MvPolynomial (Fin 2) k :=
  MvPolynomial.aeval (fun i : Fin 3 =>
    if h : i = 0 then C 1
    else X (⟨i.val - 1, by omega⟩ : Fin 2))

/-- The affine coordinates of a projective point `p` in the 0th affine chart `x₀ ≠ 0`,
obtained by dividing by the 0th homogeneous coordinate. -/
def affinePoint₀ (p : P2 k) (h₀ : Projectivization.rep p 0 ≠ 0) : Fin 2 → k :=
  fun i => Projectivization.rep p (⟨i.val + 1, by omega⟩ : Fin 3) / Projectivization.rep p 0

/-- A plane curve `X` is singular at a projective point `p` (with `p` in the chart
`x₀ ≠ 0`) if the multiplicity of its dehomogenization at the corresponding affine point
is at least two. -/
def PlaneCurve.IsSingularAt (X : PlaneCurve k) (p : P2 k)
    (h₀ : Projectivization.rep p 0 ≠ 0)
    (hf : dehomogenize₀ k X.poly ≠ 0) : Prop :=
  hypersurfaceMultiplicity k (dehomogenize₀ k X.poly) (affinePoint₀ k p h₀) hf ≥ 2

/-- Projective intersection multiplicity of two plane curves at a point `p` (in the
`x₀ ≠ 0` chart), defined as the affine intersection multiplicity of their
dehomogenizations. -/
def projIntersectionMultiplicity (X Y : PlaneCurve k) (p : P2 k)
    (h₀ : Projectivization.rep p 0 ≠ 0)
    [Module.Finite k (CurveQuotient k (dehomogenize₀ k X.poly) (dehomogenize₀ k Y.poly))] :
    ℕ :=
  intersectionMultiplicity k
    (dehomogenize₀ k X.poly) (dehomogenize₀ k Y.poly) (affinePoint₀ k p h₀)

/-- If `f` has multiplicity ≥ 2 at the common zero `p`, then the intersection
multiplicity of `f` and `g` at `p` is at least two. -/
theorem intersectionMultiplicity_ge_two_of_mult_ge_two
    (k : Type*) [Field k] [IsAlgClosed k]
    (f g : MvPolynomial (Fin 2) k) (p : Fin 2 → k)
    [Module.Finite k (CurveQuotient k f g)]
    (hf : f ≠ 0)
    (hfp : MvPolynomial.eval p f = 0)
    (hgp : MvPolynomial.eval p g = 0)
    (hmult : hypersurfaceMultiplicity k f p hf ≥ 2) :
    intersectionMultiplicity k f g p ≥ 2 := by sorry

/-- Symmetric version: if `g` has multiplicity ≥ 2 at the common zero `p`, then the
intersection multiplicity of `f` and `g` at `p` is at least two. -/
theorem intersectionMultiplicity_ge_two_of_mult_ge_two_right
    (k : Type*) [Field k] [IsAlgClosed k]
    (f g : MvPolynomial (Fin 2) k) (p : Fin 2 → k)
    [Module.Finite k (CurveQuotient k f g)]
    (hg : g ≠ 0)
    (hfp : MvPolynomial.eval p f = 0)
    (hgp : MvPolynomial.eval p g = 0)
    (hmult : hypersurfaceMultiplicity k g p hg ≥ 2) :
    intersectionMultiplicity k f g p ≥ 2 := by sorry

/-- Projective version: if `X` is singular at the common point `p`, the intersection
multiplicity of `X` and `Y` at `p` exceeds one. -/
theorem projIntersectionMultiplicity_gt_one_of_singular_X
    [IsAlgClosed k]
    (X Y : PlaneCurve k) (p : P2 k)
    (h₀ : Projectivization.rep p 0 ≠ 0)
    (hf : dehomogenize₀ k X.poly ≠ 0) (hg : dehomogenize₀ k Y.poly ≠ 0)
    [Module.Finite k (CurveQuotient k (dehomogenize₀ k X.poly) (dehomogenize₀ k Y.poly))]
    (hp_on_X : MvPolynomial.eval (affinePoint₀ k p h₀) (dehomogenize₀ k X.poly) = 0)
    (hp_on_Y : MvPolynomial.eval (affinePoint₀ k p h₀) (dehomogenize₀ k Y.poly) = 0)
    (hsing : X.IsSingularAt k p h₀ hf) :
    projIntersectionMultiplicity k X Y p h₀ > 1 := by
  unfold projIntersectionMultiplicity
  have h := intersectionMultiplicity_ge_two_of_mult_ge_two k
    (dehomogenize₀ k X.poly) (dehomogenize₀ k Y.poly) (affinePoint₀ k p h₀)
    hf hp_on_X hp_on_Y hsing
  omega

/-- Projective version: if `Y` is singular at the common point `p`, the intersection
multiplicity of `X` and `Y` at `p` exceeds one. -/
theorem projIntersectionMultiplicity_gt_one_of_singular_Y
    [IsAlgClosed k]
    (X Y : PlaneCurve k) (p : P2 k)
    (h₀ : Projectivization.rep p 0 ≠ 0)
    (hf : dehomogenize₀ k X.poly ≠ 0) (hg : dehomogenize₀ k Y.poly ≠ 0)
    [Module.Finite k (CurveQuotient k (dehomogenize₀ k X.poly) (dehomogenize₀ k Y.poly))]
    (hp_on_X : MvPolynomial.eval (affinePoint₀ k p h₀) (dehomogenize₀ k X.poly) = 0)
    (hp_on_Y : MvPolynomial.eval (affinePoint₀ k p h₀) (dehomogenize₀ k Y.poly) = 0)
    (hsing : Y.IsSingularAt k p h₀ hg) :
    projIntersectionMultiplicity k X Y p h₀ > 1 := by
  unfold projIntersectionMultiplicity
  have h := intersectionMultiplicity_ge_two_of_mult_ge_two_right k
    (dehomogenize₀ k X.poly) (dehomogenize₀ k Y.poly) (affinePoint₀ k p h₀)
    hg hp_on_X hp_on_Y hsing
  omega

/-- Corollary 20 (Lec 5): for two plane curves through a common point `p`, the
intersection multiplicity at `p` exceeds one iff at least one curve is singular there. -/
theorem corollary20_intersection_mult_gt_one_of_singular
    [IsAlgClosed k]
    (X Y : PlaneCurve k) (p : P2 k)
    (h₀ : Projectivization.rep p 0 ≠ 0)
    (hf : dehomogenize₀ k X.poly ≠ 0) (hg : dehomogenize₀ k Y.poly ≠ 0)
    [Module.Finite k (CurveQuotient k (dehomogenize₀ k X.poly) (dehomogenize₀ k Y.poly))]
    (hp_on_X : MvPolynomial.eval (affinePoint₀ k p h₀) (dehomogenize₀ k X.poly) = 0)
    (hp_on_Y : MvPolynomial.eval (affinePoint₀ k p h₀) (dehomogenize₀ k Y.poly) = 0)
    (hsing : X.IsSingularAt k p h₀ hf ∨ Y.IsSingularAt k p h₀ hg) :
    projIntersectionMultiplicity k X Y p h₀ > 1 := by
  rcases hsing with hX_sing | hY_sing
  · exact projIntersectionMultiplicity_gt_one_of_singular_X k X Y p h₀ hf hg
      hp_on_X hp_on_Y hX_sing
  · exact projIntersectionMultiplicity_gt_one_of_singular_Y k X Y p h₀ hf hg
      hp_on_X hp_on_Y hY_sing

end Lec5BezoutPascal

end
