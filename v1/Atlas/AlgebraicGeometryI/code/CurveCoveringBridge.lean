/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.CanonicalDivisorDecomposition
import Atlas.AlgebraicGeometryI.code.RiemannHurwitzDegree

noncomputable section

open RiemannHurwitzFormula CanonicalSheafCurves RiemannHurwitzDegree

/-- Convert a `CurveCovering` into the abstract `CurveMorphismData` used by the
Riemann–Hurwitz formula, by packaging degree, canonical degrees, and ramification. -/
def CurveCovering.toCurveMorphismData (C : CurveCovering) : CurveMorphismData where
  degree := C.n
  deg_KX := C.X.degK
  deg_KY := C.Y.degK
  deg_R := C.deg_R
  h_deg_R_nonneg := C.deg_R_nonneg
  h_deg_pos := C.h_n_pos

/-- The packaged `CurveMorphismData` of a `CurveCovering` satisfies the Riemann–Hurwitz identity
`deg K_X = n · deg K_Y + deg R`. -/
theorem CurveCovering.toCurveMorphismData_satisfies_RH (C : CurveCovering) :
    C.toCurveMorphismData.deg_KX =
      C.toCurveMorphismData.degree * C.toCurveMorphismData.deg_KY +
      C.toCurveMorphismData.deg_R := by
  show C.X.degK = C.n * C.Y.degK + C.deg_R
  exact C.degK_eq

/-- For the elliptic identity covering, the morphism data has degree `1` and ramification
divisor of degree `0`. -/
theorem CurveCovering.ellipticIdentity_morphismData :
    CurveCovering.ellipticIdentity.toCurveMorphismData.degree = 1 ∧
    CurveCovering.ellipticIdentity.toCurveMorphismData.deg_R = 0 := by
  exact ⟨rfl, CurveCovering.ellipticIdentity_deg_R⟩

/-- The Riemann–Hurwitz identity instantiated on the elliptic identity covering. -/
theorem CurveCovering.ellipticIdentity_toCurveMorphismData_RH :
    CurveCovering.ellipticIdentity.toCurveMorphismData.deg_KX =
      CurveCovering.ellipticIdentity.toCurveMorphismData.degree *
        CurveCovering.ellipticIdentity.toCurveMorphismData.deg_KY +
      CurveCovering.ellipticIdentity.toCurveMorphismData.deg_R :=
  CurveCovering.ellipticIdentity.toCurveMorphismData_satisfies_RH

/-- Package a `CurveCovering` as `CurveCoverData`, combining the morphism data with the
source and target curves. -/
def CurveCovering.toCurveCoverData (C : CurveCovering) : CurveCoverData where
  morphism := C.toCurveMorphismData
  source := C.X
  target := C.Y
  h_degK_X := rfl
  h_degK_Y := rfl

/-- The cover data of a `CurveCovering` satisfies the canonical-divisor decomposition
underlying the Riemann–Hurwitz formula. -/
theorem CurveCovering.toCurveCoverData_satisfies_decomp (C : CurveCovering) :
    C.toCurveCoverData.morphism.deg_KX =
      C.toCurveCoverData.morphism.degree * C.toCurveCoverData.morphism.deg_KY +
      C.toCurveCoverData.morphism.deg_R :=
  C.toCurveMorphismData_satisfies_RH

/-- Riemann–Hurwitz genus form derived via the cover-data bridge:
`2g_X - 2 = n · (2g_Y - 2) + deg R`. -/
theorem CurveCovering.genus_form_via_bridge (C : CurveCovering) :
    2 * C.X.g - 2 = C.n * (2 * C.Y.g - 2) + C.deg_R := by
  have h := riemann_hurwitz_genus_form C.toCurveCoverData C.toCurveCoverData_satisfies_decomp
  exact h

/-- Lower bound on the genus arising from a covering, obtained from the bridge:
`2g_X - 2 ≥ n · (2g_Y - 2)` (since `deg R ≥ 0`). -/
theorem CurveCovering.genus_lower_bound_via_bridge (C : CurveCovering) :
    2 * C.X.g - 2 ≥ C.n * (2 * C.Y.g - 2) := by
  have h := riemann_hurwitz_genus_lower_bound_cover C.toCurveCoverData
    C.toCurveCoverData_satisfies_decomp
  exact h

/-- The genus formula proved via the bridge agrees with the direct Riemann–Hurwitz formula. -/
theorem CurveCovering.bridge_agrees_with_direct (C : CurveCovering) :
    C.genus_form_via_bridge = C.riemann_hurwitz_genus := rfl

end
