/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ArithmeticGeometry.code.TateShafarevich

namespace EllipticCurveOver

noncomputable def LFunction (E : EllipticCurveOver ℚ) : ℂ → ℂ := by sorry

noncomputable def mordellWeilRank (E : EllipticCurveOver ℚ) : ℕ :=
  haveI : E.curve.IsElliptic := E.isElliptic
  Module.finrank ℤ (E.curve.toAffine.Point ⧸ AddCommGroup.torsion E.curve.toAffine.Point)

theorem LFunction_analyticAt (E : EllipticCurveOver ℚ) :
    AnalyticAt ℂ E.LFunction 1 := by sorry

end EllipticCurveOver

theorem birch_swinnerton_dyer_conjecture (E : EllipticCurveOver ℚ) :
    analyticOrderAt E.LFunction 1 = E.mordellWeilRank := by sorry
