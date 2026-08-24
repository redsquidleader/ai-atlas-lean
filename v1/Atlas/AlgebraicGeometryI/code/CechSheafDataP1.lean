/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.CechCohomologyIdentification
import Atlas.AlgebraicGeometryI.code.GenusConstruction

noncomputable section

universe v

namespace CechSheafDataP1

open SerreDualityTate CanonicalSheafCurves GenusConstruction
open TateCechInfra

variable (k : Type) [Field k]


/-- The Tate duality setup for `P¹` with its standard two-open cover: the ambient `k`-vector
space is `k` itself with both subspaces equal to the top subspace. -/
def tateSetupP1 : TateDualitySetup k where
  V := k
  V₁ := ⊤
  V₂ := ⊤

instance : FiniteDimensional k (tateSetupP1 k).V :=
  inferInstanceAs (FiniteDimensional k k)


/-- For the standard two-open cover of `P¹`, the first Čech cohomology of the structure sheaf
vanishes. -/
lemma finrank_cechH1_eq_zero :
    Module.finrank k (tateSetupP1 k).cechH1 = 0 := by

  show Module.finrank k ((tateSetupP1 k).V ⧸ ((tateSetupP1 k).V₁ ⊔ (tateSetupP1 k).V₂)) = 0
  have h_top : (tateSetupP1 k).V₁ ⊔ (tateSetupP1 k).V₂ = ⊤ := by
    show (⊤ : Submodule k k) ⊔ ⊤ = ⊤
    exact sup_idem _
  rw [h_top]

  show Module.finrank k (k ⧸ (⊤ : Submodule k k)) = 0
  have h := Submodule.finrank_quotient_add_finrank (⊤ : Submodule k k)
  rw [finrank_top k k] at h
  omega

/-- For the standard cover of `P¹`, the 0-th Čech cohomology of the dual setup also vanishes. -/
lemma finrank_dual_cechH0_eq_zero :
    Module.finrank k ↥(tateSetupP1 k).dual.cechH0 = 0 := by

  unfold tateSetupP1 TateDualitySetup.dual TateDualitySetup.cechH0
  simp only

  have h_top_ann : (⊤ : Submodule k k).dualAnnihilator = ⊥ :=
    Submodule.dualAnnihilator_top
  rw [h_top_ann]
  simp


/-- The smooth complete curve `P¹` constructed from the Čech data. -/
def P1 : SmoothCompleteCurve := P1CurveFromCech k

/-- The genus of `P¹` is `0`. -/
lemma P1_genus : (P1 k).g = 0 := P1CurveFromCech_genus k
/-- The degree of the canonical bundle of `P¹` is `-2`. -/
lemma P1_degK : (P1 k).degK = -2 := P1CurveFromCech_degK k

/-- The Euler characteristic of the structure sheaf of `P¹` is `1`. -/
lemma P1_chi_O : (P1 k).χ (1, 0) = 1 := by
  exact (P1 k).hχ_struct

/-- The Euler characteristic of the canonical bundle of `P¹` is `-1`. -/
lemma P1_chi_K : (P1 k).χ (1, -2) = -1 := by
  exact (P1 k).hχ_canonical


/-- The packaged `CechSheafData` instance for `P¹` with line bundle of degree `0`, the structure
sheaf, exhibiting Riemann–Roch for both `O` and `K`. -/
def cechSheafDataP1 : CechSheafData k where
  setup := tateSetupP1 k
  curve := P1 k
  deg := 0
  h0_E := 1
  h1_EK := 1
  hRR_E := by

    rw [finrank_cechH1_eq_zero]
    simp
    exact (P1_chi_O k).symm
  hRR_EK := by

    rw [finrank_dual_cechH0_eq_zero]
    simp
    rw [P1_degK]
    exact P1_chi_K k


/-- Both forms of Serre duality hold on `P¹` via the assembled Čech sheaf data. -/
theorem serre_duality_P1_from_cech_data :
    (cechSheafDataP1 k).h0_EK = (cechSheafDataP1 k).h1_E ∧
    (cechSheafDataP1 k).h0_E = (cechSheafDataP1 k).h1_EK :=
  serre_duality_both (cechSheafDataP1 k)

/-- One half of Serre duality for `P¹`: `h⁰(K) = h¹(O)`. -/
theorem serre_duality_P1_h0K_eq_h1O :
    (cechSheafDataP1 k).h0_EK = (cechSheafDataP1 k).h1_E :=
  serre_duality_unconditional (cechSheafDataP1 k)

/-- The dual half of Serre duality for `P¹`: `h⁰(O) = h¹(K)`. -/
theorem serre_duality_P1_h0O_eq_h1K :
    (cechSheafDataP1 k).h0_E = (cechSheafDataP1 k).h1_EK :=
  serre_duality_h0_eq_h1 (cechSheafDataP1 k)

/-- Full chain of Serre duality consequences for `P¹`: both duality identities and the Euler
characteristic identity. -/
theorem serre_duality_P1_full_chain :
    (cechSheafDataP1 k).h0_EK = (cechSheafDataP1 k).h1_E ∧
    (cechSheafDataP1 k).h0_E = (cechSheafDataP1 k).h1_EK ∧
    (P1 k).χ (1, 0) + (P1 k).χ (1, (P1 k).degK - 0) = 0 :=
  serre_duality_full_chain (cechSheafDataP1 k)


/-- The type `CechSheafData k` is nonempty, witnessed by the `P¹` instance. -/
theorem cechSheafDataP1_nonvacuity :
    Nonempty (CechSheafData.{0} k) :=
  ⟨cechSheafDataP1 k⟩

/-- Concrete numerical values for the `P¹` Čech sheaf data: `h⁰(O) = 1`, `h¹(K) = 1`,
`deg = 0`, `g = 0`, `degK = -2`. -/
theorem cechSheafDataP1_values :
    (cechSheafDataP1 k).h0_E = 1 ∧
    (cechSheafDataP1 k).h1_EK = 1 ∧
    (cechSheafDataP1 k).deg = 0 ∧
    (cechSheafDataP1 k).curve.g = 0 ∧
    (cechSheafDataP1 k).curve.degK = -2 :=
  ⟨rfl, rfl, rfl, P1_genus k, P1_degK k⟩

/-- Both the first Čech cohomology and the dual zeroth Čech cohomology vanish for `P¹`. -/
theorem cechSheafDataP1_cech_dimensions :
    Module.finrank k (cechSheafDataP1 k).setup.cechH1 = 0 ∧
    Module.finrank k ↥(cechSheafDataP1 k).setup.dual.cechH0 = 0 :=
  ⟨finrank_cechH1_eq_zero k, finrank_dual_cechH0_eq_zero k⟩

/-- Concrete values for the Serre duality identification on `P¹`: `h⁰(K) = 0` and `h¹(O) = 0`. -/
theorem serre_duality_P1_concrete_values :
    (cechSheafDataP1 k).h0_EK = 0 ∧ (cechSheafDataP1 k).h1_E = 0 := by
  constructor
  ·
    show (Module.finrank k ↥(tateSetupP1 k).dual.cechH0 : ℤ) = 0
    rw [finrank_dual_cechH0_eq_zero]
    simp
  ·
    show (Module.finrank k (tateSetupP1 k).cechH1 : ℤ) = 0
    rw [finrank_cechH1_eq_zero]
    simp

end CechSheafDataP1

end
