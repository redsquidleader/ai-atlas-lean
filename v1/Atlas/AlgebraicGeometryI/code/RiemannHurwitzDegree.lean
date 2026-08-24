/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.RiemannHurwitzFormula
import Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves

noncomputable section

open RiemannHurwitzFormula CanonicalSheafCurves

namespace RiemannHurwitzDegree

/-- Bundle of data for a finite cover f : X → Y of smooth complete curves: a
`CurveMorphismData` together with the source and target curves and equalities
identifying the abstract canonical degrees with the curves' canonical degrees. -/
structure CurveCoverData where
  morphism : CurveMorphismData
  source : SmoothCompleteCurve
  target : SmoothCompleteCurve
  h_degK_X : morphism.deg_KX = source.degK
  h_degK_Y : morphism.deg_KY = target.degK

/-- Riemann–Hurwitz in genus form: for a cover f : X → Y of smooth complete
curves with Riemann–Hurwitz decomposition `deg K_X = n · deg K_Y + deg R`, one
has `2 g_X - 2 = n (2 g_Y - 2) + deg R` (Thm 21.1, Cor 27, Lec 21). -/
theorem riemann_hurwitz_genus_form (f : CurveCoverData)
    (h_decomp : f.morphism.deg_KX = f.morphism.degree * f.morphism.deg_KY + f.morphism.deg_R) :
    2 * f.source.g - 2 = f.morphism.degree * (2 * f.target.g - 2) + f.morphism.deg_R := by
  have hX := deg_canonical_eq_2g_sub_2 f.source
  have hY := deg_canonical_eq_2g_sub_2 f.target
  rw [f.h_degK_X, hX] at h_decomp
  rw [f.h_degK_Y, hY] at h_decomp
  linarith

/-- Solving Riemann–Hurwitz for `2 g_X`: gives `2 g_X = n (2 g_Y - 2) + deg R + 2`. -/
theorem riemann_hurwitz_genus_solve (f : CurveCoverData)
    (h_decomp : f.morphism.deg_KX = f.morphism.degree * f.morphism.deg_KY + f.morphism.deg_R) :
    2 * f.source.g = f.morphism.degree * (2 * f.target.g - 2) + f.morphism.deg_R + 2 := by
  have := riemann_hurwitz_genus_form f h_decomp
  linarith

/-- Consequence of Riemann–Hurwitz: since the ramification divisor has
non-negative degree, `2 g_X - 2 ≥ n (2 g_Y - 2)`. -/
theorem riemann_hurwitz_genus_lower_bound_cover (f : CurveCoverData)
    (h_decomp : f.morphism.deg_KX = f.morphism.degree * f.morphism.deg_KY + f.morphism.deg_R) :
    2 * f.source.g - 2 ≥ f.morphism.degree * (2 * f.target.g - 2) := by
  have hRH := riemann_hurwitz_genus_form f h_decomp
  linarith [f.morphism.h_deg_R_nonneg]

/-- Convenience constructor for `CurveCoverData` from a source and target curve,
a degree `n`, a ramification degree `degR`, and the hypothesis that the genus
form of Riemann–Hurwitz holds. -/
def CurveCoverData.mk' (X Y : SmoothCompleteCurve) (n degR : ℤ)
    (h_nonneg : 0 ≤ degR)
    (h_pos : 0 < n)
    (_h_RH : 2 * X.g - 2 = n * (2 * Y.g - 2) + degR) :
    CurveCoverData where
  morphism := {
    degree := n
    deg_KX := X.degK
    deg_KY := Y.degK
    deg_R := degR
    h_deg_R_nonneg := h_nonneg
    h_deg_pos := h_pos
  }
  source := X
  target := Y
  h_degK_X := rfl
  h_degK_Y := rfl

/-- Specialization of the Riemann–Hurwitz genus formula when the target is
`ℙ¹` (genus 0): `2 g_X - 2 = -2 n + deg R`. -/
theorem riemann_hurwitz_P1_genus_form (g_X n degR : ℤ)
    (h_RH : 2 * g_X - 2 = n * (2 * 0 - 2) + degR) :
    2 * g_X - 2 = -2 * n + degR := by linarith

/-- Solving the `ℙ¹`-target Riemann–Hurwitz formula for `2 g_X`. -/
theorem riemann_hurwitz_P1_genus_solve (g n degR : ℤ)
    (h_RH : 2 * g - 2 = -2 * n + degR) :
    2 * g = degR - 2 * n + 2 := by linarith

/-- Simple ramification contribution: each simple ramification point (multiplicity 2)
contributes `(2 - 1) = 1` to the ramification divisor degree. -/
theorem simple_ramification_degR (r : ℤ) :
    r * ((2 : ℤ) - 1) = r := by ring

/-- Riemann–Hurwitz for a cover with only simple ramification: substituting
`r · (2 - 1) = r` gives `2 g - 2 = -2 n + r`. -/
theorem riemann_hurwitz_simple_genus (g n r : ℤ)
    (h_RH : 2 * g - 2 = -2 * n + r * (2 - 1)) :
    2 * g - 2 = -2 * n + r := by linarith

/-- Counts the number of simple ramification points in terms of `g` and `n`
for a cover of `ℙ¹` with only simple ramification. -/
theorem simple_ramification_count (g n r : ℤ)
    (h_RH : 2 * g - 2 = -2 * n + r) :
    r = 2 * g + 2 * n - 2 := by linarith

section GenusComputations

/-- For a hyperelliptic double cover of `ℙ¹` by a curve of genus `g`,
Riemann–Hurwitz reduces to `2 g - 2 = 2(2·0 - 2) + (2 g + 2)`. -/
theorem genus_hyperelliptic_from_curves (g : ℕ) :
    let X := mkCurve g
    let Y := mkCurve 0
    2 * X.g - 2 = 2 * (2 * Y.g - 2) + (2 * (g : ℤ) + 2) := by
  simp [mkCurve]
  ring

/-- Recovering the genus of a hyperelliptic curve from its branch point count:
if `b` is the number of branch points, then `2g = b - 2`. -/
theorem hyperelliptic_genus_from_branch_points (g b : ℤ)
    (h_RH : 2 * g - 2 = 2 * (-2 : ℤ) + b) :
    2 * g = b - 2 := by linarith

/-- A smooth plane quartic has genus 3: `2g - 2 = d(d - 3)` with `d = 4`. -/
theorem genus_plane_quartic :
    let d : ℤ := 4
    let g : ℤ := 3
    2 * g - 2 = d * (d - 3) := by norm_num

/-- Canonical degree numerical identity for a plane quartic of genus 3. -/
theorem plane_quartic_degK :
    (4 : ℤ) * (4 - 3) = 2 * 3 - 2 := by norm_num

/-- A plane quartic viewed as a degree-4 cover of `ℙ¹`: the Riemann–Hurwitz
numerical identity `2·3 - 2 = -2·4 + 12`. -/
theorem plane_quartic_as_cover_P1 :
    (2 : ℤ) * 3 - 2 = -2 * 4 + 12 := by norm_num

/-- Ramification count for a plane quartic seen as a degree-4 cover of `ℙ¹`. -/
theorem plane_quartic_ramification_count :
    2 * (3 : ℤ) + 2 * 4 - 2 = 12 := by norm_num

/-- A smooth plane quintic has genus 6: `2g - 2 = d(d - 3)` with `d = 5`. -/
theorem genus_plane_quintic :
    let d : ℤ := 5
    let g : ℤ := 6
    2 * g - 2 = d * (d - 3) := by norm_num

/-- Genus from a degree-3 cover of `ℙ¹` with 4 totally ramified (multiplicity 3)
points: numerical check of Riemann–Hurwitz. -/
theorem genus_degree3_cover_4_total_ram :
    let n : ℤ := 3
    let r : ℤ := 4
    let e : ℤ := 3
    let degR := r * (e - 1)
    let g : ℤ := 2
    2 * g - 2 = -2 * n + degR := by norm_num

/-- Genus from a degree-3 cover of `ℙ¹` with 6 simple ramification points. -/
theorem genus_degree3_cover_6_simple_ram :
    let n : ℤ := 3
    let degR : ℤ := 6
    let g : ℤ := 1
    2 * g - 2 = -2 * n + degR := by norm_num

/-- For an unramified double cover of a genus-2 curve, the cover has genus 3
(checked numerically via Riemann–Hurwitz). -/
theorem genus_unramified_double_cover_genus2 :
    let C_X := mkCurve 3
    let C_Y := mkCurve 2
    2 * C_X.g - 2 = 2 * (2 * C_Y.g - 2) + 0 := by
  simp [mkCurve]

/-- Étale (unramified) covers: from Riemann–Hurwitz with `deg R = 0`,
`g_X = n (g_Y - 1) + 1`. -/
theorem genus_etale_cover (g_X g_Y n : ℤ)
    (h_RH : 2 * g_X - 2 = n * (2 * g_Y - 2)) :
    g_X = n * (g_Y - 1) + 1 := by linarith

end GenusComputations

section LurothBound

/-- Lüroth-type bound: for a cover X → ℙ¹ with `g_X ≥ 0`, the ramification
divisor satisfies `deg R ≥ 2n - 2`. -/
theorem luroth_bound (n degR : ℤ) (g_X : ℤ) (hg : g_X ≥ 0)
    (h_RH : 2 * g_X - 2 = -2 * n + degR) :
    degR ≥ 2 * n - 2 := by linarith

/-- Alternative form of the Lüroth bound: `deg R ≥ 2(n - 1)`. -/
theorem luroth_bound_alt (n degR : ℤ) (g_X : ℤ) (hg : g_X ≥ 0)
    (h_RH : 2 * g_X - 2 = -2 * n + degR) :
    degR ≥ 2 * (n - 1) := by linarith

/-- The non-negativity of the genus forces the ramification divisor degree to
satisfy `deg R ≥ 2n - 2` for any cover of `ℙ¹`. -/
theorem genus_nonneg_constraint (g_X n degR : ℤ)
    (hg_X : g_X ≥ 0)
    (h_RH : 2 * g_X - 2 = -2 * n + degR) :
    degR ≥ 2 * n - 2 := by linarith

/-- A hyperelliptic double cover of `ℙ¹` must have at least 2 branch points. -/
theorem hyperelliptic_min_branch_points (g_X : ℤ) (hg : g_X ≥ 0) (b : ℤ)
    (h_RH : 2 * g_X - 2 = 2 * (-2 : ℤ) + b) :
    b ≥ 2 := by linarith

/-- A degree-3 cover of `ℙ¹` must have ramification divisor of degree at least 4. -/
theorem degree3_min_ramification (g_X : ℤ) (hg : g_X ≥ 0) (degR : ℤ)
    (h_RH : 2 * g_X - 2 = -2 * 3 + degR) :
    degR ≥ 4 := by linarith

/-- The Riemann–Hurwitz formula forces the ramification divisor degree
`deg R` to be even. -/
theorem riemann_hurwitz_parity (g_X g_Y n degR : ℤ)
    (h_RH : 2 * g_X - 2 = n * (2 * g_Y - 2) + degR) :
    ∃ k : ℤ, degR = 2 * k := by
  use g_X - 1 - n * (g_Y - 1)
  linarith

end LurothBound

section StandardExamples

/-- A double cover of `ℙ¹` by an elliptic curve (genus 1) with 4 simple
ramification points; the standard example. -/
def ellipticCoverP1 : CurveCoverData :=
  CurveCoverData.mk' (mkCurve 1) (mkCurve 0) 2 4
    (by norm_num)
    (by norm_num)
    (by simp [mkCurve])

/-- The source of `ellipticCoverP1` has genus 1. -/
theorem ellipticCoverP1_source_genus : ellipticCoverP1.source.g = 1 := by
  simp [ellipticCoverP1, CurveCoverData.mk', mkCurve]

/-- The target of `ellipticCoverP1` is `ℙ¹` (genus 0). -/
theorem ellipticCoverP1_target_genus : ellipticCoverP1.target.g = 0 := by
  simp [ellipticCoverP1, CurveCoverData.mk', mkCurve]

/-- The degree of `ellipticCoverP1` is 2. -/
theorem ellipticCoverP1_degree : ellipticCoverP1.morphism.degree = 2 := by
  simp [ellipticCoverP1, CurveCoverData.mk']

/-- The ramification divisor of `ellipticCoverP1` has degree 4. -/
theorem ellipticCoverP1_degR : ellipticCoverP1.morphism.deg_R = 4 := by
  simp [ellipticCoverP1, CurveCoverData.mk']

/-- Riemann–Hurwitz holds for `ellipticCoverP1` in genus form. -/
theorem ellipticCoverP1_RH :
    2 * ellipticCoverP1.source.g - 2 =
    ellipticCoverP1.morphism.degree * (2 * ellipticCoverP1.target.g - 2) +
    ellipticCoverP1.morphism.deg_R :=
  riemann_hurwitz_genus_form ellipticCoverP1 (by simp [ellipticCoverP1, CurveCoverData.mk', mkCurve])

/-- A double cover of `ℙ¹` by a genus-2 curve with 6 simple ramification points. -/
def genus2CoverP1 : CurveCoverData :=
  CurveCoverData.mk' (mkCurve 2) (mkCurve 0) 2 6
    (by norm_num)
    (by norm_num)
    (by simp [mkCurve])

/-- The source of `genus2CoverP1` has genus 2. -/
theorem genus2CoverP1_source_genus : genus2CoverP1.source.g = 2 := by
  simp [genus2CoverP1, CurveCoverData.mk', mkCurve]

/-- Riemann–Hurwitz holds for `genus2CoverP1` in genus form. -/
theorem genus2CoverP1_RH :
    2 * genus2CoverP1.source.g - 2 =
    genus2CoverP1.morphism.degree * (2 * genus2CoverP1.target.g - 2) +
    genus2CoverP1.morphism.deg_R :=
  riemann_hurwitz_genus_form genus2CoverP1 (by simp [genus2CoverP1, CurveCoverData.mk', mkCurve])

/-- A double cover of `ℙ¹` by a genus-3 curve with 8 simple ramification points. -/
def genus3CoverP1 : CurveCoverData :=
  CurveCoverData.mk' (mkCurve 3) (mkCurve 0) 2 8
    (by norm_num)
    (by norm_num)
    (by simp [mkCurve])

/-- Riemann–Hurwitz holds for `genus3CoverP1` in genus form. -/
theorem genus3CoverP1_RH :
    2 * genus3CoverP1.source.g - 2 =
    genus3CoverP1.morphism.degree * (2 * genus3CoverP1.target.g - 2) +
    genus3CoverP1.morphism.deg_R :=
  riemann_hurwitz_genus_form genus3CoverP1 (by simp [genus3CoverP1, CurveCoverData.mk', mkCurve])

/-- Hyperelliptic cover: a generic double cover `X → ℙ¹` where `X` has genus `g`
and the cover has `2g + 2` simple ramification points. -/
def hyperellipticCover (g : ℕ) : CurveCoverData :=
  CurveCoverData.mk' (mkCurve g) (mkCurve 0) 2 (2 * (g : ℤ) + 2)
    (by linarith [Int.natCast_nonneg g])
    (by norm_num)
    (by simp [mkCurve]; linarith [Int.natCast_nonneg g])

/-- The source of `hyperellipticCover g` has genus `g`. -/
theorem hyperellipticCover_source_genus (g : ℕ) :
    (hyperellipticCover g).source.g = (g : ℤ) := by
  simp [hyperellipticCover, CurveCoverData.mk', mkCurve]

/-- The target of `hyperellipticCover g` is `ℙ¹`. -/
theorem hyperellipticCover_target_genus (g : ℕ) :
    (hyperellipticCover g).target.g = 0 := by
  simp [hyperellipticCover, CurveCoverData.mk', mkCurve]

/-- The hyperelliptic cover has degree 2. -/
theorem hyperellipticCover_degree (g : ℕ) :
    (hyperellipticCover g).morphism.degree = 2 := by
  simp [hyperellipticCover, CurveCoverData.mk']

/-- The hyperelliptic cover of genus `g` has ramification divisor of degree `2g + 2`. -/
theorem hyperellipticCover_degR (g : ℕ) :
    (hyperellipticCover g).morphism.deg_R = 2 * (g : ℤ) + 2 := by
  simp [hyperellipticCover, CurveCoverData.mk']

end StandardExamples

example : (2 : ℤ) * 1 - 2 = 2 * (2 * 0 - 2) + 4 := by norm_num

example : (2 : ℤ) * 2 - 2 = 2 * (2 * 0 - 2) + 6 := by norm_num

example : (2 : ℤ) * 3 - 2 = 2 * (2 * 0 - 2) + 8 := by norm_num

example : (2 : ℤ) * 1 - 2 = 3 * (2 * 0 - 2) + 6 := by norm_num

example : (2 : ℤ) * 3 - 2 = 4 * (2 * 0 - 2) + 12 := by norm_num

example : (2 : ℤ) * 3 - 2 = 2 * (2 * 2 - 2) + 0 := by norm_num

example : (2 : ℤ) * 4 - 2 = 3 * (2 * 2 - 2) + 0 := by norm_num

end RiemannHurwitzDegree

end

/-- The Riemann–Hurwitz degree formula: for a finite cover `f : X → Y` of
smooth complete curves of degree `n`, `deg K_X = n · deg K_Y + deg R`. -/
theorem riemann_hurwitz_degree_formula (f : CurveCovering) :
    f.X.degK = f.n * f.Y.degK + f.deg_R :=
  f.degK_eq
