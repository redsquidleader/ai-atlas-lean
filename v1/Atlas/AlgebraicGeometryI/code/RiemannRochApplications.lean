/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.RiemannRochEulerCurves
import Atlas.AlgebraicGeometryI.code.SheafCohCurvesFiniteness
import Atlas.AlgebraicGeometryI.code.RiemannRochRiemannForm
import Atlas.AlgebraicGeometryI.code.DedekindCurve

open CanonicalSheafCurves RiemannRochEulerCurves RiemannRochRiemannForm
open SheafCohCurvesFiniteness

noncomputable section

namespace RiemannRochApplications

/-- Serre duality package for the structure sheaf `𝒪_C` of a smooth complete
curve `C`: `h^0(𝒪) = 1`, `h^1(𝒪) = g`. -/
def structureSheafSD (C : SmoothCompleteCurve) (hg : C.g ≥ 0) :
    SerreDualityCurve C 1 0 where
  h0 := 1
  h1 := C.g
  h0_dual := C.χ (1, C.degK) + 1
  chi_decomp := by
    rw [chi_structure_sheaf_curve]
  serre_dual := by


    have := euler_char_canonical C
    linarith
  h0_nonneg := by norm_num
  h1_nonneg := hg

/-- Serre duality package for the canonical sheaf `ω_C`: `h^0(ω) = g`,
`h^1(ω) = 1`. -/
def canonicalSheafSD (C : SmoothCompleteCurve) (hg : C.g ≥ 0) :
    SerreDualityCurve C 1 C.degK where
  h0 := C.g
  h1 := 1
  h0_dual := C.χ (1, 0) + C.g
  chi_decomp := by
    rw [euler_char_canonical]
  serre_dual := by


    have := chi_structure_sheaf_curve C
    linarith
  h0_nonneg := hg
  h1_nonneg := by norm_num

/-- Serre duality for the structure sheaf: `h^0(𝒪_C) = 1` and `h^1(𝒪_C) = h^0(ω_C) = g`. -/
theorem corollary_29_serre_duality (C : SmoothCompleteCurve) (_hg : C.g ≥ 0)
    (h0_O h1_O h0_K : ℤ)
    (_hchi_O : C.χ (1, 0) = h0_O - h1_O)
    (hSD_O : h1_O = h0_K)
    (_hh0_O : h0_O = 1) (hh1_O : h1_O = C.g) :
    h0_K = C.g := by
  linarith

/-- Corollary 29 (Lec 25): `h^0(ω_C) = g`, the dimension of global sections
of the canonical sheaf equals the geometric genus. -/
theorem corollary_29 (C : SmoothCompleteCurve) (_hg : C.g ≥ 0)
    (h0_K h1_K : ℤ)
    (hchi_K : C.χ (1, C.degK) = h0_K - h1_K)
    (hSD_K : h1_K = 1) :
    h0_K = C.g := by
  have := euler_char_canonical C
  linarith

/-- The genus can be computed from `h^0(K)` and `h^1(K)`: under
Serre duality `h^1(K) = 1`, so `h^0(K) = g`. -/
theorem genus_from_canonical_sections (C : SmoothCompleteCurve) (_hg : C.g ≥ 0)
    (h0_K h1_K : ℤ)
    (hchi_K : C.χ (1, C.degK) = h0_K - h1_K)
    (hSD_K : h1_K = 1) (_hh0_K : h0_K ≥ 0) :
    h0_K = C.g := by
  have hRR := euler_char_canonical C
  linarith

/-- Numerical Corollary 29: `χ(𝒪) = 1 - g`, `χ(ω) = g - 1`, and
`χ(𝒪) + χ(ω) = 0` (Serre duality for `𝒪`). -/
theorem corollary_29_numerical (C : SmoothCompleteCurve) :
    C.χ (1, 0) = 1 - C.g ∧
    C.χ (1, C.degK) = C.g - 1 ∧
    C.χ (1, 0) + C.χ (1, C.degK) = 0 :=
  ⟨chi_structure_sheaf_curve C,
   euler_char_canonical C,
   serre_duality_chi C⟩

/-- The degree of the Serre dual of `L` (of degree `d`) is `2g - 2 - d`,
using `deg K = 2g - 2`. -/
theorem serre_dual_degree (C : SmoothCompleteCurve) (d : ℤ) :
    C.degK - d = (2 * C.g - 2) - d := by
  rw [deg_canonical_eq_2g_sub_2 C]

/-- For a line bundle of degree `d > 2g - 2`, the Serre dual has negative degree. -/
theorem high_degree_serre_dual_negative (C : SmoothCompleteCurve) (d : ℤ)
    (hd : d > 2 * C.g - 2) :
    C.degK - d < 0 := by
  have := deg_canonical_eq_2g_sub_2 C
  linarith

/-- For `d > 2g - 2`, the Euler characteristic of the Serre dual of a line
bundle is non-positive. -/
theorem high_degree_euler_char_dual_nonpos (C : SmoothCompleteCurve) (d : ℤ)
    (hd : d > 2 * C.g - 2) (hg : C.g ≥ 0) :
    C.χ (1, C.degK - d) ≤ 0 := by
  rw [euler_char_line_bundle]
  have := deg_canonical_eq_2g_sub_2 C
  linarith

/-- In the high-degree case where `h^1 = 0`, Riemann–Roch is exact:
`h^0(L) = d + 1 - g`. -/
theorem high_degree_exact_rr (C : SmoothCompleteCurve) (d : ℤ)
    (SD : SerreDualityCurve C 1 d) (h1_zero : SD.h1 = 0) :
    SD.h0 = d + 1 - C.g := by
  have := riemann_roch_exact_when_h1_zero C 1 d SD h1_zero
  linarith

/-- For `d ≥ 2g - 1` (and `h^1 = 0`), `h^0(L) ≥ g`. -/
theorem high_degree_has_sections (C : SmoothCompleteCurve) (d : ℤ)
    (hd : d ≥ 2 * C.g - 1) (_hg : C.g ≥ 0)
    (SD : SerreDualityCurve C 1 d) (h1_zero : SD.h1 = 0) :
    SD.h0 ≥ C.g := by
  have := high_degree_exact_rr C d SD h1_zero
  linarith

/-- For `d ≥ 2g`, `h^0(L) ≥ g + 1`. -/
theorem very_high_degree_sections (C : SmoothCompleteCurve) (d : ℤ)
    (hd : d ≥ 2 * C.g)
    (SD : SerreDualityCurve C 1 d) (h1_zero : SD.h1 = 0) :
    SD.h0 ≥ C.g + 1 := by
  have := high_degree_exact_rr C d SD h1_zero
  linarith

/-- For a genus-0 curve (i.e., `ℙ¹`), `χ(𝒪) = 1`. -/
theorem genus_zero_chi_O (C : SmoothCompleteCurve) (hg : C.g = 0) :
    C.χ (1, 0) = 1 := by
  rw [chi_structure_sheaf_curve]; linarith

/-- For a genus-0 curve, `deg K = -2`. -/
theorem genus_zero_deg_K (C : SmoothCompleteCurve) (hg : C.g = 0) :
    C.degK = -2 := by
  have := deg_canonical_eq_2g_sub_2 C; linarith

/-- For a genus-0 curve, the Euler characteristic of `𝒪(1)` is 2. -/
theorem genus_zero_point_chi (C : SmoothCompleteCurve) (hg : C.g = 0) :
    C.χ (1, 1) = 2 := by
  rw [euler_char_line_bundle]; linarith

/-- On a genus-0 curve, `h^0(𝒪(1)) = 2` (the two sections defining the
projective embedding). -/
theorem genus_zero_point_sections (C : SmoothCompleteCurve) (hg : C.g = 0)
    (SD : SerreDualityCurve C 1 1) (h1_zero : SD.h1 = 0) :
    SD.h0 = 2 := by
  have := riemann_roch_exact_when_h1_zero C 1 1 SD h1_zero
  linarith [hg]

/-- For a genus-0 curve, the degree-1 line bundle provides a map to `ℙ¹`,
realised by `χ(𝒪(1)) = 2` together with vanishing of the Serre dual. -/
theorem genus_zero_gives_map_to_P1 (C : SmoothCompleteCurve) (hg : C.g = 0) :
    C.χ (1, 1) = 2 ∧ C.degK - 1 < 0 := by
  constructor
  · exact genus_zero_point_chi C hg
  · have := genus_zero_deg_K C hg
    linarith

/-- For a genus-0 curve and any `d`, when `h^1 = 0`, `h^0(L(d)) = d + 1`. -/
theorem genus_zero_sections (C : SmoothCompleteCurve) (hg : C.g = 0) (d : ℤ)
    (SD : SerreDualityCurve C 1 d) (h1_zero : SD.h1 = 0) :
    SD.h0 = d + 1 := by
  have := riemann_roch_exact_when_h1_zero C 1 d SD h1_zero
  linarith [hg]

/-- For an elliptic curve (genus 1), `χ(𝒪) = 0`. -/
theorem elliptic_chi_O (C : SmoothCompleteCurve) (hg : C.g = 1) :
    C.χ (1, 0) = 0 := by
  rw [chi_structure_sheaf_curve]; linarith

/-- For an elliptic curve, `deg K = 0` (the canonical bundle is trivial). -/
theorem elliptic_K_trivial (C : SmoothCompleteCurve) (hg : C.g = 1) :
    C.degK = 0 := by
  have := deg_canonical_eq_2g_sub_2 C; linarith

/-- For an elliptic curve, the Euler characteristic of a line bundle of
degree `d` is `d`. -/
theorem elliptic_chi (C : SmoothCompleteCurve) (hg : C.g = 1) (d : ℤ) :
    C.χ (1, d) = d := by
  rw [euler_char_line_bundle]; linarith

/-- For an elliptic curve with `h^1 = 0`, `h^0(L) = d`. -/
theorem elliptic_sections (C : SmoothCompleteCurve) (hg : C.g = 1) (d : ℤ)
    (SD : SerreDualityCurve C 1 d) (h1_zero : SD.h1 = 0) :
    SD.h0 = d := by
  have := riemann_roch_exact_when_h1_zero C 1 d SD h1_zero
  linarith [hg]

/-- An elliptic curve embeds as a smooth cubic in `ℙ²` via a degree-3 line
bundle: `h^0(𝒪(3)) = 3`. -/
theorem elliptic_cubic_embedding (C : SmoothCompleteCurve) (hg : C.g = 1)
    (SD : SerreDualityCurve C 1 3) (h1_zero : SD.h1 = 0) :
    SD.h0 = 3 :=
  elliptic_sections C hg 3 SD h1_zero

/-- For a genus-2 curve, `deg K = 2`. -/
theorem genus2_deg_K (C : SmoothCompleteCurve) (hg : C.g = 2) :
    C.degK = 2 := by
  have := deg_canonical_eq_2g_sub_2 C; linarith

/-- For a genus-2 curve, `h^0(K_C) = 2`. -/
theorem genus2_canonical_sections (C : SmoothCompleteCurve) (hg : C.g = 2)
    (SD : SerreDualityCurve C 1 C.degK) (hSD_h1 : SD.h1 = 1) :
    SD.h0 = 2 := by
  have hchi := euler_char_canonical C
  have := SD.chi_decomp
  linarith

/-- For a genus-2 curve and high degree (so `h^1 = 0`), `h^0(L) = d - 1`. -/
theorem genus2_high_degree (C : SmoothCompleteCurve) (hg : C.g = 2) (d : ℤ)
    (SD : SerreDualityCurve C 1 d) (h1_zero : SD.h1 = 0) :
    SD.h0 = d - 1 := by
  have := riemann_roch_exact_when_h1_zero C 1 d SD h1_zero
  linarith [hg]

/-- Verification: on `ℙ¹`, `dim H^0(𝒪) = 1`. -/
theorem P1_verify_H0_structure (k : Type) [Field k] :
    Module.finrank k (SheafCohomology.H0 k 0) = 1 := by
  exact SheafCohomology.finrank_H0_of_nonneg k 0 le_rfl

/-- Verification: on `ℙ¹`, `dim H^1(𝒪) = 0`. -/
theorem P1_verify_H1_structure (k : Type) [Field k] :
    Module.finrank k (SheafCohomology.H1 k 0) = 0 := by
  exact SheafCohomology.finrank_H1_of_nonneg k 0 le_rfl

/-- Verification: on `ℙ¹`, `χ(𝒪) = 1`. -/
theorem P1_verify_euler_char_O (k : Type) [Field k] :
    (Module.finrank k (SheafCohomology.H0 k 0) : ℤ) -
    (Module.finrank k (SheafCohomology.H1 k 0) : ℤ) = 1 := by
  rw [P1_verify_H0_structure, P1_verify_H1_structure]
  norm_num

/-- Serre duality on `ℙ¹`: `dim H^1(𝒪(n)) = dim H^0(𝒪(-2 - n))`. -/
theorem P1_verify_serre_duality (k : Type) [Field k] (n : ℤ) :
    Module.finrank k (SheafCohomology.H1 k n) =
    Module.finrank k (SheafCohomology.H0 k (-2 - n)) := by
  by_cases hn : 0 ≤ n
  · exact SheafCohomology.serre_duality_nonneg k n hn
  · exact SheafCohomology.serre_duality_neg k n (not_le.mp hn)

/-- On `ℙ¹`, `dim H^0(𝒪(1)) = 2`. -/
theorem P1_verify_H0_degree1 (k : Type) [Field k] :
    Module.finrank k (SheafCohomology.H0 k 1) = 2 := by
  rw [SheafCohomology.finrank_H0_of_nonneg k 1 (by norm_num)]
  simp

/-- On `ℙ¹`, `dim H^1(𝒪(1)) = 0`. -/
theorem P1_verify_H1_degree1 (k : Type) [Field k] :
    Module.finrank k (SheafCohomology.H1 k 1) = 0 := by
  exact SheafCohomology.finrank_H1_of_nonneg k 1 (by norm_num)

/-- On `ℙ¹`, for `n ≥ 0`, `dim H^0(𝒪(n)) = n + 1`. -/
theorem P1_verify_H0_nonneg (k : Type) [Field k] (n : ℤ) (hn : 0 ≤ n) :
    (Module.finrank k (SheafCohomology.H0 k n) : ℤ) = n + 1 := by
  rw [SheafCohomology.finrank_H0_of_nonneg k n hn]
  omega

/-- On `ℙ¹`, for `n ≥ 0`, `dim H^1(𝒪(n)) = 0`. -/
theorem P1_verify_H1_nonneg (k : Type) [Field k] (n : ℤ) (hn : 0 ≤ n) :
    Module.finrank k (SheafCohomology.H1 k n) = 0 := by
  exact SheafCohomology.finrank_H1_of_nonneg k n hn

/-- On `ℙ¹`, `dim H^0(𝒪(-1)) = 0`. -/
theorem P1_verify_H0_neg1 (k : Type) [Field k] :
    Module.finrank k (SheafCohomology.H0 k (-1)) = 0 := by
  exact SheafCohomology.finrank_H0_of_neg k (-1) (by norm_num)

/-- On `ℙ¹`, `dim H^1(𝒪(-2)) = 1` (corresponding to the canonical bundle). -/
theorem P1_verify_H1_neg2 (k : Type) [Field k] :
    Module.finrank k (SheafCohomology.H1 k (-2)) = 1 := by
  rw [SheafCohomology.finrank_H1_of_neg k (-2) (by norm_num)]
  norm_num

/-- Consistency: for `mkCurve 0 = ℙ¹`, the abstract Euler characteristic
matches the Čech computation. -/
theorem P1_abstract_cech_consistency (k : Type) [Field k] (n : ℤ) :
    (mkCurve 0).χ (1, n) =
    (Module.finrank k (SheafCohomology.H0 k n) : ℤ) -
    (Module.finrank k (SheafCohomology.H1 k n) : ℤ) := by
  rw [euler_char_P1 (mkCurve 0) (mkCurve_genus 0) n]
  exact (SheafCohomology.euler_characteristic k n).symm

/-- Consistency: the genus of `mkCurve 0 = ℙ¹` equals `dim H^1(𝒪)`. -/
theorem P1_genus_consistency (k : Type) [Field k] :
    (mkCurve 0).g = (Module.finrank k (SheafCohomology.H1 k 0) : ℤ) := by
  rw [mkCurve_genus, P1_verify_H1_structure]

/-- The genus can be recovered from the structure sheaf's Euler characteristic:
`g = 1 - χ(𝒪)`. -/
theorem genus_from_euler_char (C : SmoothCompleteCurve) :
    C.g = 1 - C.χ (1, 0) := by
  rw [chi_structure_sheaf_curve]; ring

/-- Consequence of Cor 31 (Lec 25): `deg K + 2 = 2g`. -/
theorem degree_genus_formula (C : SmoothCompleteCurve) :
    C.degK + 2 = 2 * C.g := by
  have := deg_canonical_eq_2g_sub_2 C; linarith

/-- The Riemann inequality from the Serre duality data: `d + 1 - g ≤ h^0(L)`. -/
theorem riemann_inequality_from_SD (C : SmoothCompleteCurve) (d : ℤ)
    (SD : SerreDualityCurve C 1 d) :
    d + 1 - C.g ≤ SD.h0 := by
  exact riemann_inequality_line_bundle C d SD

/-- Serre duality for the Euler characteristic: `χ(L) + χ(K ⊗ L*) = 0`. -/
theorem serre_duality_euler_char (C : SmoothCompleteCurve) (d : ℤ) :
    C.χ (1, d) + C.χ (1, C.degK - d) = 0 :=
  euler_char_dual_line_bundle C d

/-- For the self-dual class `L = K^{1/2}` (degree `g - 1`), the Euler
characteristic is zero. -/
theorem self_dual_chi_zero (C : SmoothCompleteCurve) :
    C.χ (1, C.g - 1) = 0 := by
  rw [euler_char_line_bundle]; ring

/-- Serre duality package for `𝒪` derived from a Dedekind curve `C` with
`ddGenus` providing `h^1(𝒪)`. -/
def serreDualityO_fromDedekind {k : Type*} [Field k] (C : DedekindCurve k) :
    SerreDualityCurve C.toSmoothCompleteCurve 1 0 where
  h0 := 1
  h1 := C.ddGenus
  h0_dual := C.ddGenus
  chi_decomp := by
    rw [chi_structure_sheaf_curve]

    rfl
  serre_dual := rfl
  h0_nonneg := by norm_num
  h1_nonneg := Nat.cast_nonneg _

/-- Serre duality package for `ω_C` derived from a Dedekind curve `C`. -/
def serreDualityK_fromDedekind {k : Type*} [Field k] (C : DedekindCurve k) :
    SerreDualityCurve C.toSmoothCompleteCurve 1 C.toSmoothCompleteCurve.degK where
  h0 := C.ddGenus
  h1 := 1
  h0_dual := 1
  chi_decomp := by
    rw [euler_char_canonical]

    rfl
  serre_dual := rfl
  h0_nonneg := Nat.cast_nonneg _
  h1_nonneg := by norm_num

end RiemannRochApplications

end
