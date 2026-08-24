/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.TateCechInfra

noncomputable section

universe v

namespace CechCohomologyIdentification

variable {k : Type*} [Field k]


/-- From the packaged Čech sheaf data on a curve, both forms of Serre duality
`h⁰(E ⊗ K) = h¹(E)` and `h⁰(E) = h¹(E ⊗ K)` hold. -/
theorem serre_duality_from_cech_sheaf_data
    (D : TateCechInfra.CechSheafData k) :
    D.h0_EK = D.h1_E ∧ D.h0_E = D.h1_EK :=
  SerreDualityTate.serre_duality_from_tate_both D.setup D.curve D.deg
    D.h0_E D.h1_E D.h0_EK D.h1_EK
    D.hRR_E D.hRR_EK rfl rfl

/-- One half of Serre duality from Čech sheaf data: `h⁰(E ⊗ K) = h¹(E)`. -/
theorem serre_duality_h0_from_cech_sheaf_data
    (D : TateCechInfra.CechSheafData k) :
    D.h0_EK = D.h1_E :=
  (serre_duality_from_cech_sheaf_data D).1

/-- The dual half of Serre duality from Čech sheaf data: `h⁰(E) = h¹(E ⊗ K)`. -/
theorem serre_duality_h1_from_cech_sheaf_data
    (D : TateCechInfra.CechSheafData k) :
    D.h0_E = D.h1_EK :=
  (serre_duality_from_cech_sheaf_data D).2


/-- Unconditional Serre duality assembled from a Tate duality setup, a smooth complete curve, and
Riemann–Roch identities for `E` and `E ⊗ K`. -/
theorem serre_duality_unconditional_from_setup
    (S : SerreDualityTate.TateDualitySetup k) [FiniteDimensional k S.V]
    (C : CanonicalSheafCurves.SmoothCompleteCurve) (d : ℤ)
    (h0_E h1_EK : ℤ)
    (hRR_E : h0_E - ↑(Module.finrank k S.cechH1) = C.χ (1, d))
    (hRR_EK : ↑(Module.finrank k ↥S.dual.cechH0) - h1_EK =
              C.χ (1, C.degK - d)) :
    ↑(Module.finrank k ↥S.dual.cechH0) = ↑(Module.finrank k S.cechH1) ∧
    h0_E = h1_EK := by
  constructor
  · exact_mod_cast SerreDualityTate.tate_duality_core S
  · have h_tate := SerreDualityTate.tate_duality_core S
    have h_chi := SerreDualityCurves.serre_duality_chi_rank1 C d
    have h_cast : (Module.finrank k ↥S.dual.cechH0 : ℤ) =
                  (Module.finrank k S.cechH1 : ℤ) := by exact_mod_cast h_tate
    linarith


/-- For a smooth complete curve, `χ(L) + χ(K ⊗ L⁻¹) = 0` (Serre duality on Euler
characteristics). -/
theorem serre_duality_unconditional_chi
    (C : CanonicalSheafCurves.SmoothCompleteCurve) (d : ℤ) :
    C.χ (1, d) + C.χ (1, C.degK - d) = 0 :=
  SerreDualityCurves.serre_duality_chi_rank1 C d

/-- Given Riemann–Roch for `E` and `E ⊗ K` and one half of Serre duality `h⁰(E) = h¹(E ⊗ K)`,
deduce the other half `h¹(E) = h⁰(E ⊗ K)`. -/
theorem serre_duality_other_direction
    (C : CanonicalSheafCurves.SmoothCompleteCurve) (d : ℤ)
    (h0_E h1_E h0_EK h1_EK : ℤ)
    (hRR_E : h0_E - h1_E = C.χ (1, d))
    (hRR_EK : h0_EK - h1_EK = C.χ (1, C.degK - d))
    (hSD_one : h0_E = h1_EK) :
    h1_E = h0_EK := by
  have hchi := SerreDualityCurves.serre_duality_chi_rank1 C d
  linarith

/-- The reverse direction: from `h¹(E) = h⁰(E ⊗ K)` and Riemann–Roch we recover
`h⁰(E) = h¹(E ⊗ K)`. -/
theorem serre_duality_other_direction_reverse
    (C : CanonicalSheafCurves.SmoothCompleteCurve) (d : ℤ)
    (h0_E h1_E h0_EK h1_EK : ℤ)
    (hRR_E : h0_E - h1_E = C.χ (1, d))
    (hRR_EK : h0_EK - h1_EK = C.χ (1, C.degK - d))
    (hSD_one : h1_E = h0_EK) :
    h0_E = h1_EK := by
  have hchi := SerreDualityCurves.serre_duality_chi_rank1 C d
  linarith


/-- Symmetric form for the trivial and canonical bundles: from Riemann–Roch for `O` and `K`
plus Serre duality `h⁰(O) = h¹(K)`, one concludes `h¹(O) = h⁰(K)`, giving the genus equality. -/
theorem genus_equality_from_tate
    (C : CanonicalSheafCurves.SmoothCompleteCurve)
    (h0_O h1_O h0_K h1_K : ℤ)
    (hRR_O : h0_O - h1_O = C.χ (1, 0))
    (hRR_K : h0_K - h1_K = C.χ (1, C.degK))
    (hSD : h0_O = h1_K) :
    h1_O = h0_K := by
  have hchi := SerreDualityCurves.serre_duality_chi_rank1 C 0
  simp only [sub_zero] at hchi
  linarith

/-- The degree of the canonical bundle of a smooth complete curve is `2g - 2`. -/
theorem deg_canonical_from_tate
    (C : CanonicalSheafCurves.SmoothCompleteCurve) :
    C.degK = 2 * C.g - 2 :=
  SerreDualityCurves.deg_K_from_serre_duality C


/-- Full chain of Serre duality consequences from a Čech sheaf datum: both duality identities,
the Euler-characteristic identity, and the Riemann–Roch formula. -/
theorem serre_duality_complete_chain
    (D : TateCechInfra.CechSheafData k) :
    D.h0_EK = D.h1_E ∧ D.h0_E = D.h1_EK ∧
    D.curve.χ (1, D.deg) + D.curve.χ (1, D.curve.degK - D.deg) = 0 ∧
    D.curve.χ (1, D.deg) = D.deg + 1 - D.curve.g := by
  refine ⟨TateCechInfra.serre_duality_unconditional D,
    TateCechInfra.serre_duality_h0_eq_h1 D,
    SerreDualityCurves.serre_duality_chi_rank1 D.curve D.deg, ?_⟩
  rw [CanonicalSheafCurves.chi_eq_rr D.curve 1 D.deg]; ring

/-- The integer-valued cohomology dimensions stored in `CechSheafData` agree definitionally with
the actual Čech cohomology of the Tate duality setup. -/
theorem serre_duality_identification_is_rfl
    (D : TateCechInfra.CechSheafData k) :

    D.h0_EK = ↑(Module.finrank k ↥D.setup.dual.cechH0) ∧

    D.h1_E = ↑(Module.finrank k D.setup.cechH1) :=
  ⟨rfl, rfl⟩

end CechCohomologyIdentification

end
