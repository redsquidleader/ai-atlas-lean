/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.Divisors

noncomputable section

open CurveDivisor

structure EllipticCurveP2Data (C : Type*) (F : Type*) [Field F] where
  curveInst : FunctionFieldCurve C F
  Line : Type*
  lineIntersectionDivisor : Line → CurveDivisor C
  linearFormRatio : Line → Line → Fˣ
  restrictLinearForm : Line → Fˣ
  ratio_eq_mul_inv : ∀ (L₁ L₂ : Line),
    linearFormRatio L₁ L₂ = restrictLinearForm L₁ * (restrictLinearForm L₂)⁻¹

namespace EllipticCurveP2Data

variable {C : Type*} {F : Type*} [Field F]

noncomputable def pdiv (E : EllipticCurveP2Data C F) (f : Fˣ) : CurveDivisor C :=
  @CurveWithOrd.principalDivisor C F _ E.curveInst f

end EllipticCurveP2Data

theorem EllipticCurveP2Data.bezout_degree {C : Type*} {F : Type*} [Field F]
    (E : EllipticCurveP2Data C F) (L : E.Line) :
    degree C (E.lineIntersectionDivisor L) = 3 := by sorry

theorem EllipticCurveP2Data.bezout_divisor {C : Type*} {F : Type*} [Field F]
    (E : EllipticCurveP2Data C F) (L : E.Line) :
    E.pdiv (E.restrictLinearForm L) = E.lineIntersectionDivisor L := by sorry

namespace EllipticCurveP2Data

variable {C : Type*} {F : Type*} [Field F] (E : EllipticCurveP2Data C F)

theorem lineIntersectionDivisor_degree (L : E.Line) :
    degree C (E.lineIntersectionDivisor L) = 3 :=
  E.bezout_degree L

theorem div_restrictLinearForm (L : E.Line) :
    E.pdiv (E.restrictLinearForm L) = E.lineIntersectionDivisor L :=
  E.bezout_divisor L


theorem pdiv_mul (f g : Fˣ) :
    E.pdiv (f * g) = E.pdiv f + E.pdiv g := by
  simp only [pdiv]
  exact @CurveWithOrd.principalDivisor_mul C F _ E.curveInst f g

theorem pdiv_inv (f : Fˣ) :
    E.pdiv f⁻¹ = -E.pdiv f := by
  simp only [pdiv]
  exact @CurveWithOrd.principalDivisor_inv C F _ E.curveInst f

theorem lemma_23_17 (L₁ L₂ : E.Line) :
    E.pdiv (E.linearFormRatio L₁ L₂) =
      E.lineIntersectionDivisor L₁ - E.lineIntersectionDivisor L₂ := by
  rw [E.ratio_eq_mul_inv, E.pdiv_mul, E.pdiv_inv,
    E.div_restrictLinearForm, E.div_restrictLinearForm, sub_eq_add_neg]


end EllipticCurveP2Data

end
