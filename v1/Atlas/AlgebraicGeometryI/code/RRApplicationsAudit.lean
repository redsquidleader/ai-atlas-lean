/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.RiemannRochApplications

set_option maxHeartbeats 800000

open CanonicalSheafCurves RiemannRochEulerCurves RiemannRochRiemannForm
open RiemannRochApplications SheafCohCurvesFiniteness

noncomputable section

namespace RRApplicationsAudit

/-- Audit: derivation of `deg K = 2g − 2` (Cor 31, Lec 24). -/
theorem audit_degK_derivation (C : SmoothCompleteCurve) :
    C.degK = 2 * C.g - 2 :=
  deg_canonical_eq_2g_sub_2 C

/-- Audit: Riemann inequality `h^0(L) ≥ d + 1 − g` for line bundles. -/
theorem audit_riemann_inequality (C : SmoothCompleteCurve) (d : ℤ)
    (SD : SerreDualityCurve C 1 d) :
    SD.h0 ≥ d + 1 - C.g :=
  riemann_inequality_line_bundle C d SD

/-- Audit of Cor 29 (Lec 24): `h^0(K) = g`. -/
theorem audit_corollary_29 (C : SmoothCompleteCurve) (_hg : C.g ≥ 0)
    (h0_K h1_K : ℤ)
    (hchi_K : C.χ (1, C.degK) = h0_K - h1_K)
    (hSD_K : h1_K = 1) :
    h0_K = C.g := by
  have := euler_char_canonical C
  linarith

/-- Audit: vanishing of `h^1` makes Riemann–Roch exact. -/
theorem audit_high_degree_exact (C : SmoothCompleteCurve) (d : ℤ)
    (SD : SerreDualityCurve C 1 d) (h1_zero : SD.h1 = 0) :
    SD.h0 = d + 1 - C.g :=
  high_degree_exact_rr C d SD h1_zero

/-- Audit: degree-1 line bundles on `ℙ¹` have two global sections. -/
theorem audit_genus_zero_sections (C : SmoothCompleteCurve) (hg : C.g = 0)
    (SD : SerreDualityCurve C 1 1) (h1_zero : SD.h1 = 0) :
    SD.h0 = 2 :=
  genus_zero_point_sections C hg SD h1_zero

/-- Audit: Euler-characteristic form of Serre duality. -/
theorem audit_serre_duality_chi (C : SmoothCompleteCurve) (d : ℤ) :
    C.χ (1, d) + C.χ (1, C.degK - d) = 0 :=
  euler_char_dual_line_bundle C d

/-- Audit: consistency between the abstract Euler characteristic on
`mkCurve 0` and the concrete Čech computation on `ℙ¹`. -/
theorem audit_P1_consistency (k : Type) [Field k] (n : ℤ) :
    (mkCurve 0).χ (1, n) =
    (Module.finrank k (SheafCohomology.H0 k n) : ℤ) -
    (Module.finrank k (SheafCohomology.H1 k n) : ℤ) :=
  P1_abstract_cech_consistency k n

/-- Audit: the genus of the smooth curve associated to a Dedekind curve `C`
matches the Dedekind-theoretic genus `C.ddGenus`. -/
theorem audit_dedekind_grounding {k : Type*} [Field k] (C : DedekindCurve k) :
    C.toSmoothCompleteCurve.g = (C.ddGenus : ℤ) := by
  rfl

/-- Audit: the Serre-duality bundle for the structure sheaf of a Dedekind
curve has `h^0 = 1` and `h^1 = g`. -/
theorem audit_dedekind_SD_O {k : Type*} [Field k] (C : DedekindCurve k) :
    (serreDualityO_fromDedekind C).h0 = 1 ∧
    (serreDualityO_fromDedekind C).h1 = (C.ddGenus : ℤ) := by
  exact ⟨rfl, rfl⟩

/-- Audit: full Riemann–Roch pipeline for genus 0 collects the three key
facts (`h^0 = 2` for `𝒪(1)`, `deg K = −2`, `χ(𝒪) = 1`). -/
theorem audit_full_pipeline_genus0 (C : SmoothCompleteCurve) (hg : C.g = 0)
    (SD : SerreDualityCurve C 1 1) (h1_zero : SD.h1 = 0) :
    SD.h0 = 2 ∧ C.degK = -2 ∧ C.χ (1, 0) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · exact genus_zero_point_sections C hg SD h1_zero
  · exact genus_zero_deg_K C hg
  · exact genus_zero_chi_O C hg

/-- Audit: full Riemann–Roch pipeline in general (Riemann inequality,
Euler-characteristic Serre duality, `deg K = 2g − 2`). -/
theorem audit_full_pipeline_general (C : SmoothCompleteCurve) (d : ℤ)
    (SD : SerreDualityCurve C 1 d) :
    SD.h0 ≥ d + 1 - C.g ∧
    C.χ (1, d) + C.χ (1, C.degK - d) = 0 ∧
    C.degK = 2 * C.g - 2 := by
  refine ⟨?_, ?_, ?_⟩
  · exact riemann_inequality_line_bundle C d SD
  · exact euler_char_dual_line_bundle C d
  · exact deg_canonical_eq_2g_sub_2 C

/-- Audit: elliptic pipeline (`χ(𝒪) = 0`, `K` trivial, `h^0(𝒪(3p)) = 3`). -/
theorem audit_elliptic_pipeline (C : SmoothCompleteCurve) (hg : C.g = 1)
    (SD3 : SerreDualityCurve C 1 3) (h1_zero : SD3.h1 = 0) :
    C.χ (1, 0) = 0 ∧ C.degK = 0 ∧ SD3.h0 = 3 := by
  refine ⟨?_, ?_, ?_⟩
  · exact elliptic_chi_O C hg
  · exact elliptic_K_trivial C hg
  · exact elliptic_cubic_embedding C hg SD3 h1_zero

end RRApplicationsAudit

end
