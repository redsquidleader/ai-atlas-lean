/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.SerreDualityTate
import Atlas.AlgebraicGeometryI.code.SerreDualityAnnihilator


section TateVectorSpaceDef

variable {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V]

/-- Two subspaces `W₁`, `W₂` of `V` are commensurable iff their quotients by
their intersection are both finite-dimensional. -/
def IsCommensurable (W₁ W₂ : Submodule k V) : Prop :=
  Module.Finite k (W₁ ⧸ Submodule.comap W₁.subtype (W₁ ⊓ W₂)) ∧
  Module.Finite k (W₂ ⧸ Submodule.comap W₂.subtype (W₁ ⊓ W₂))

/-- Commensurability is reflexive: every subspace is commensurable with itself. -/
theorem IsCommensurable.refl (W : Submodule k V) : IsCommensurable W W := by
  have h : Submodule.comap W.subtype (W ⊓ W) = ⊤ := by ext x; simp
  constructor <;> { rw [h]; infer_instance }

/-- Commensurability is symmetric in its two arguments. -/
theorem IsCommensurable.symm {W₁ W₂ : Submodule k V}
    (h : IsCommensurable W₁ W₂) : IsCommensurable W₂ W₁ := by
  constructor
  · rw [inf_comm]; exact h.2
  · rw [inf_comm]; exact h.1

/-- A Tate vector space over `k` (Def 46, Lec 25): a topological `k`-vector
space whose neighborhood basis of zero consists of pairwise commensurable
linear subspaces. -/
class IsTateVectorSpace (k : Type*) [Field k] (V : Type*) [AddCommGroup V] [Module k V]
    [TopologicalSpace V] : Prop where
  exists_nhds_basis : ∃ (ι : Type*) (W : ι → Submodule k V),
    (nhds (0 : V)).HasBasis (fun _ : ι => True) (fun i => ↑(W i)) ∧
    ∀ i j, IsCommensurable (W i) (W j)

end TateVectorSpaceDef

noncomputable section

universe v

namespace TateCechInfra

open SerreDualityTate SerreDualityCurves
open CanonicalSheafCurves RiemannRochCurves SerreDualityP1
open SheafCohCurvesFiniteness CohomologyP1 SheafCohomology
open SerreDualityAnnihilator

variable (k : Type*) [Field k]

/-- Packaging the data needed to apply Tate self-duality machinery to a Čech
cohomology setup on a smooth complete curve, recording the Riemann–Roch
identities for both `E` and the dualized line bundle `K - E`. -/
structure CechSheafData where
  setup : TateDualitySetup.{_, v} k
  [instFD : FiniteDimensional k setup.V]
  curve : SmoothCompleteCurve
  deg : ℤ
  h0_E : ℤ
  h1_EK : ℤ
  hRR_E : h0_E - ↑(Module.finrank k setup.cechH1) = curve.χ (1, deg)
  hRR_EK : ↑(Module.finrank k ↥setup.dual.cechH0) - h1_EK =
            curve.χ (1, curve.degK - deg)

attribute [instance] CechSheafData.instFD

variable {k}

/-- The dimension of `H¹(E)` as an integer, extracted from the Čech data. -/
def CechSheafData.h1_E (D : CechSheafData k) : ℤ :=
  ↑(Module.finrank k D.setup.cechH1)

/-- The dimension of `H⁰(K - E)` as an integer, extracted from the Čech data. -/
def CechSheafData.h0_EK (D : CechSheafData k) : ℤ :=
  ↑(Module.finrank k ↥D.setup.dual.cechH0)

/-- Unconditional Serre duality from Tate self-duality: `h⁰(K - E) = h¹(E)`. -/
theorem serre_duality_unconditional (D : CechSheafData k) :
    D.h0_EK = D.h1_E := by
  unfold CechSheafData.h0_EK CechSheafData.h1_E
  exact_mod_cast tate_duality_core D.setup

/-- Combining Tate duality with Riemann–Roch gives `h⁰(E) = h¹(K - E)`. -/
theorem serre_duality_h0_eq_h1 (D : CechSheafData k) :
    D.h0_E = D.h1_EK := by
  have h_tate := tate_duality_core D.setup
  have h_chi := serre_duality_chi_rank1 D.curve D.deg
  have hRR_E := D.hRR_E
  have hRR_EK := D.hRR_EK
  have h_cast : (Module.finrank k ↥D.setup.dual.cechH0 : ℤ) =
                (Module.finrank k D.setup.cechH1 : ℤ) := by exact_mod_cast h_tate
  linarith

/-- Both halves of Serre duality packaged together. -/
theorem serre_duality_both (D : CechSheafData k) :
    D.h0_EK = D.h1_E ∧ D.h0_E = D.h1_EK :=
  ⟨serre_duality_unconditional D, serre_duality_h0_eq_h1 D⟩

/-- Adapter feeding the Čech data into the generic Tate-duality result. -/
theorem cech_data_feeds_tate (D : CechSheafData k) :
    D.h0_EK = D.h1_E ∧ D.h0_E = D.h1_EK :=
  serre_duality_from_tate_both D.setup D.curve D.deg
    D.h0_E D.h1_E D.h0_EK D.h1_EK
    D.hRR_E D.hRR_EK rfl rfl

/-- Full chain: Tate self-duality combined with the Euler characteristic
identity yields both Serre duality isomorphisms together with the genus
constraint `χ(E) + χ(K - E) = 0`. -/
theorem serre_duality_full_chain (D : CechSheafData k) :
    D.h0_EK = D.h1_E ∧ D.h0_E = D.h1_EK ∧
    D.curve.χ (1, D.deg) + D.curve.χ (1, D.curve.degK - D.deg) = 0 := by
  exact ⟨serre_duality_unconditional D, serre_duality_h0_eq_h1 D,
         serre_duality_chi_rank1 D.curve D.deg⟩

/-- If the residue pairing vanishes on `S.V₁ × V₁'`, then `V₁'` is contained
in the annihilator of `S.V₁`. -/
theorem residue_pairing_gives_annihilator_inclusion
    (S : TateDualitySetup k) (V₁' : Submodule k (Module.Dual k S.V))
    (h_residue : ∀ f ∈ S.V₁, ∀ φ ∈ V₁', φ f = 0) :
    V₁' ≤ S.V₁.dualAnnihilator :=
  residue_implies_annihilator_inclusion k S V₁' h_residue

/-- If both `Vᵢ'` equal the annihilators of `S.Vᵢ`, then their intersection
equals the annihilator of `S.V₁ ⊔ S.V₂`. -/
theorem annihilator_equalities_give_duality
    (S : TateDualitySetup k)
    (V₁' V₂' : Submodule k (Module.Dual k S.V))
    (h_eq₁ : V₁' = S.V₁.dualAnnihilator)
    (h_eq₂ : V₂' = S.V₂.dualAnnihilator) :
    V₁' ⊓ V₂' = (S.V₁ ⊔ S.V₂).dualAnnihilator :=
  annihilator_equality_gives_duality k S V₁' h_eq₁ V₂' h_eq₂

/-- Core Tate dimension identity: the dual cohomology has the same dimension
as the original Čech `H¹`. -/
theorem tate_dimension_identity
    (S : TateDualitySetup.{_, v} k) [FiniteDimensional k S.V] :
    Module.finrank k ↥S.dual.cechH0 = Module.finrank k S.cechH1 :=
  tate_duality_core S

/-- In a finite-dimensional space, the annihilator of a sum has the same
dimension as the quotient by that sum. -/
theorem annihilator_quotient_dimension
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (W₁ W₂ : Submodule k V) :
    Module.finrank k ↥(W₁ ⊔ W₂).dualAnnihilator =
    Module.finrank k (V ⧸ (W₁ ⊔ W₂)) := by
  have h_ann := Subspace.finrank_add_finrank_dualAnnihilator_eq (W₁ ⊔ W₂)
  have h_quot := Submodule.finrank_quotient_add_finrank (W₁ ⊔ W₂)
  omega

/-- Tate duality via a self-pairing isomorphism `V ≃ V*`: the dimension of
the intersection of annihilators pulled back through `B` matches the quotient
dimension. -/
theorem self_pairing_tate_duality
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (B : V ≃ₗ[k] Module.Dual k V)
    (W₁ W₂ : Submodule k V) :
    Module.finrank k ↥(W₁.dualAnnihilator.comap B.toLinearMap ⊓
                         W₂.dualAnnihilator.comap B.toLinearMap) =
    Module.finrank k (V ⧸ (W₁ ⊔ W₂)) :=
  tate_duality_via_pairing B W₁ W₂

/-- Genus equality `χ(O) + χ(K) = 0` deduced from Serre duality on a smooth
complete curve. -/
theorem genus_equality_from_serre (C : SmoothCompleteCurve) :
    C.χ (1, 0) + C.χ (1, C.degK) = 0 :=
  genus_equality C

/-- The canonical divisor has degree `2g - 2`, computed from Serre duality. -/
theorem canonical_degree (C : SmoothCompleteCurve) :
    C.degK = 2 * C.g - 2 :=
  deg_K_from_serre_duality C

/-- Transfer one direction of Serre duality to the other via the Euler
characteristic identity. -/
theorem serre_duality_direction_transfer
    (C : SmoothCompleteCurve) (d : ℤ)
    (h0_E h1_E h0_EK h1_EK : ℤ)
    (hRR_E : h0_E - h1_E = C.χ (1, d))
    (hRR_EK : h0_EK - h1_EK = C.χ (1, C.degK - d))
    (hSD_one : h0_E = h1_EK) :
    h1_E = h0_EK := by
  have hchi := serre_duality_chi_rank1 C d
  linarith

end TateCechInfra

end
