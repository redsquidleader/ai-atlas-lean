/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.RiemannRoch


open RiemannRochSpace


namespace Lemma2112

variable {C : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] [RiemannRochData C F k]

open CurveWithOrd CurveDivisor


/-- (Lemma 21.12) A divisor $D$ of degree $0$ has $\ell(D) = 1$ iff $D$ is principal. -/
theorem ell_eq_one_iff_principal (D : CurveDivisor C)
    (hdeg : degree C D = 0) :
    divisorDim (F := F) (k := k) D = 1 ↔ IsPrincipal (F := F) D :=
  divisorDim_degree_zero_iff (F := F) (k := k) D hdeg

end Lemma2112
