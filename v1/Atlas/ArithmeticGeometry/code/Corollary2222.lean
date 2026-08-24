/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.RiemannRoch

namespace Corollary2222

open RiemannRochSpace CurveDivisor CurveWithOrd

theorem ell_eq_genus {C F k : Type*} [Field k] [Field F] [Algebra k F]
    [RiemannRochData C F k]
    (W : CurveDivisor C) (hW : IsCanonicalDivisor W) :
    (divisorDim (F := F) (k := k) W : ℤ) = (genus (C := C) (F := F) (k := k) : ℤ) :=
  canonical_divisorDim_eq_genus W hW


end Corollary2222
