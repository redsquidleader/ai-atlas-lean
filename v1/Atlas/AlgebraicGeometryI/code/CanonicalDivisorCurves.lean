/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves
import Atlas.AlgebraicGeometryI.code.DedekindCurve

open CanonicalSheafCurves

noncomputable section

namespace CanonicalDivisorCurves


/-- Canonical divisor class of a Dedekind curve `C`: the class of its canonical sheaf in the
Picard-group representation `ℤ × ℤ` (rank, degree). -/
def canonicalDivisorClass_dedekind {k : Type*} [Field k]
    (C : DedekindCurve k) : ℤ × ℤ :=
  canonicalSheafClass C.toSmoothCompleteCurve

/-- For a Dedekind curve `C`, the canonical degree equals `2g - 2`. -/
theorem canonical_degree_eq_2g_minus_2_dedekind {k : Type*} [Field k]
    (C : DedekindCurve k) :
    C.toSmoothCompleteCurve.degK = 2 * C.toSmoothCompleteCurve.g - 2 :=
  deg_canonical_eq_2g_sub_2 C.toSmoothCompleteCurve


/-- Serre duality consequence: `χ(K) = g - 1` for a Dedekind curve. -/
theorem canonical_chi_eq_g_minus_1_dedekind {k : Type*} [Field k]
    (C : DedekindCurve k) :
    C.toSmoothCompleteCurve.χ (1, C.toSmoothCompleteCurve.degK) =
    C.toSmoothCompleteCurve.g - 1 :=
  C.toSmoothCompleteCurve.hχ_canonical

/-- The Euler characteristic of the structure sheaf of a Dedekind curve is `1 - g`. -/
theorem structure_chi_eq_1_minus_g_dedekind {k : Type*} [Field k]
    (C : DedekindCurve k) :
    C.toSmoothCompleteCurve.χ (1, 0) = 1 - C.toSmoothCompleteCurve.g :=
  C.toSmoothCompleteCurve.hχ_struct

/-- Serre duality in characteristic form: `χ(O) + χ(K) = 0`. -/
theorem serre_duality_chi_dedekind {k : Type*} [Field k]
    (C : DedekindCurve k) :
    C.toSmoothCompleteCurve.χ (1, 0) +
    C.toSmoothCompleteCurve.χ (1, C.toSmoothCompleteCurve.degK) = 0 :=
  serre_duality_chi C.toSmoothCompleteCurve


/-- Riemann-Roch formula for a Dedekind curve: `χ(r, d) = d - r(g - 1)`. -/
theorem rr_formula_dedekind {k : Type*} [Field k]
    (C : DedekindCurve k) (r d : ℤ) :
    C.toSmoothCompleteCurve.χ (r, d) = d - r * (C.toSmoothCompleteCurve.g - 1) :=
  chi_eq_rr C.toSmoothCompleteCurve r d

/-- The canonical degree from the underlying `SmoothCompleteCurve` agrees with the Dedekind
canonical degree. -/
theorem toSCC_degK_eq_dedekind_degK {k : Type*} [Field k]
    (C : DedekindCurve k) :
    C.toSmoothCompleteCurve.degK = C.degK := rfl

/-- The genus from the underlying `SmoothCompleteCurve` agrees with the Dedekind genus. -/
theorem toSCC_g_eq_ddGenus {k : Type*} [Field k]
    (C : DedekindCurve k) :
    C.toSmoothCompleteCurve.g = (C.ddGenus : ℤ) := rfl

end CanonicalDivisorCurves

end
