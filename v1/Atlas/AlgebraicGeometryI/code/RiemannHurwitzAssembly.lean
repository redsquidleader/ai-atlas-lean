/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.RiemannHurwitz
import Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves

noncomputable section

open CanonicalSheafCurves

namespace RiemannHurwitzAssembly

/-- A finite morphism of smooth complete curves: source `X`, target `Y`,
degree `n > 0`, and a ramification divisor of nonnegative degree `deg_R`,
together with the canonical-divisor identity `K_X = n · K_Y + R`. -/
structure CurveCovering where
  X : SmoothCompleteCurve
  Y : SmoothCompleteCurve
  n : ℤ
  hn : 0 < n
  deg_R : ℤ
  deg_R_nonneg : 0 ≤ deg_R
  degK_eq : X.degK = n * Y.degK + deg_R

namespace CurveCovering

/-- Riemann–Hurwitz theorem: for a finite morphism of smooth complete curves,
`2 g_X − 2 = n(2 g_Y − 2) + deg R`, obtained from `K_X = n K_Y + R`. -/
theorem riemann_hurwitz_genus (f : CurveCovering) :
    2 * f.X.g - 2 = f.n * (2 * f.Y.g - 2) + f.deg_R := by
  have h_deg := f.degK_eq
  have h_X := deg_canonical_eq_2g_sub_2 f.X
  have h_Y := deg_canonical_eq_2g_sub_2 f.Y
  rw [h_X, h_Y] at h_deg
  linarith

/-- Explicit (step-by-step) version of the Riemann–Hurwitz formula. -/
theorem riemann_hurwitz_genus_explicit (f : CurveCovering) :
    2 * f.X.g - 2 = f.n * (2 * f.Y.g - 2) + f.deg_R := by

  have h_deg : f.X.degK = f.n * f.Y.degK + f.deg_R := f.degK_eq

  have h_degK_X : f.X.degK = 2 * f.X.g - 2 := deg_canonical_eq_2g_sub_2 f.X

  have h_degK_Y : f.Y.degK = 2 * f.Y.g - 2 := deg_canonical_eq_2g_sub_2 f.Y

  rw [h_degK_X, h_degK_Y] at h_deg
  linarith

/-- The defining canonical-divisor identity `K_X = n K_Y + R`, repackaged. -/
theorem degree_form (f : CurveCovering) :
    f.X.degK = f.n * f.Y.degK + f.deg_R :=
  f.degK_eq

/-- Genus lower bound from Riemann–Hurwitz: `g_X ≥ n · g_Y − n + 1`. -/
theorem genus_lower_bound (f : CurveCovering) :
    f.X.g ≥ f.n * f.Y.g - f.n + 1 := by
  have hRH := f.riemann_hurwitz_genus
  have hR := f.deg_R_nonneg
  nlinarith

/-- The ramification-divisor degree expressed via the source and target genera. -/
theorem deg_R_from_genera (f : CurveCovering) :
    f.deg_R = 2 * f.X.g - 2 - f.n * (2 * f.Y.g - 2) := by
  have hRH := f.riemann_hurwitz_genus
  linarith

/-- For an étale cover (no ramification), the Riemann–Hurwitz formula
reduces to the exact relation `2 g_X − 2 = n(2 g_Y − 2)`. -/
theorem etale_genus (f : CurveCovering) (h : f.deg_R = 0) :
    2 * f.X.g - 2 = f.n * (2 * f.Y.g - 2) := by
  have hRH := f.riemann_hurwitz_genus
  linarith

/-- Hyperelliptic curve example: a double cover of `ℙ¹` has ramification
divisor of degree `2 g_X + 2` (the number of Weierstrass points). -/
theorem hyperelliptic_ramification (f : CurveCovering) (hn : f.n = 2) (hg : f.Y.g = 0) :
    f.deg_R = 2 * f.X.g + 2 := by
  have hRH := f.riemann_hurwitz_genus
  nlinarith

end CurveCovering

/-- The Riemann–Hurwitz theorem (Thm 21.1) packaged as a standalone statement
about `CurveCovering`. -/
theorem riemann_hurwitz_theorem (f : CurveCovering) :
    2 * f.X.g - 2 = f.n * (2 * f.Y.g - 2) + f.deg_R :=
  f.riemann_hurwitz_genus

/-- Restating: the canonical divisor of a smooth complete curve has
degree `2g − 2`. -/
theorem canonical_degree_eq_2g_sub_2 (C : SmoothCompleteCurve) :
    C.degK = 2 * C.g - 2 :=
  deg_canonical_eq_2g_sub_2 C

/-- Alternative derivation of Riemann–Hurwitz via the abstract numerical
lemma `riemann_hurwitz_formula` applied to canonical degrees. -/
theorem riemann_hurwitz_from_A1 (f : CurveCovering) :
    2 * f.X.g - 2 = f.n * (2 * f.Y.g - 2) + f.deg_R :=
  riemann_hurwitz_formula f.n f.X.g f.Y.g f.deg_R f.X.degK f.Y.degK
    (f.n * f.Y.degK)
    (deg_canonical_eq_2g_sub_2 f.X)
    (deg_canonical_eq_2g_sub_2 f.Y)
    rfl
    f.degK_eq

example : (2 : ℤ) * 1 - 2 = 2 * (2 * 0 - 2) + 4 := by norm_num

example : (2 : ℤ) * 2 - 2 = 2 * (2 * 0 - 2) + 6 := by norm_num

example : (2 : ℤ) * 3 - 2 = 2 * (2 * 2 - 2) + 0 := by norm_num

example : (2 : ℤ) * 1 - 2 = 3 * (2 * 0 - 2) + 6 := by norm_num

end RiemannHurwitzAssembly

end
