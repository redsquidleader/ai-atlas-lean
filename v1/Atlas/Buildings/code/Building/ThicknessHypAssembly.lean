/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.ThicknessFoldings

open ChamberComplex

variable {V : Type} [DecidableEq V]

namespace AptIsCoxeterProof

/-- Assembled discharge of the hypothesis `ThicknessImpliesAptStructureHyp`,
asserting that thickness of a chamber complex induces sufficient apartment
structure (via foldings). -/
theorem thickness_hyp : ThicknessImpliesAptStructureHyp V :=
  ThicknessFoldings.thickness_implies_apt_structure_hyp

/-- Each apartment of a thick chamber complex, equipped with sufficient
foldings, carries a Coxeter complex structure with an injective surjective
labeling map $\varphi$ to a Coxeter group preserving adjacency. -/
theorem apt_is_coxeter_from_foldings'
    (K : ChamberComplex V) (hThick : K.IsThick)
    (pre : PreApartmentData K)
    (tits_thm : TitsTheoremHyp V)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments) :
    ∃ (B_idx : Type) (M : CoxeterMatrix B_idx) (cc : ChamberComplex V),
      cc.toSimplicialComplex = A ∧
      ∃ (φ : Finset V → M.Group),
        (∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D) ∧
        (∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w) ∧
        (∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C')) ∧
        cc.IsThin :=
  apt_is_coxeter_from_foldings K hThick pre tits_thm thickness_hyp A hA

/-- Promote `PreApartmentData` to a full `ApartmentSystem`, given thickness
and the Tits theorem hypothesis. -/
def PreApartmentData.toApartmentSystem' {K : ChamberComplex V}
    (pre : PreApartmentData K) (hThick : K.IsThick)
    (tits_thm : TitsTheoremHyp V) :
    ApartmentSystem K :=
  pre.toApartmentSystem hThick tits_thm thickness_hyp

/-- The apartments of `pre.toApartmentSystem'` are exactly `pre.apartments`. -/
theorem PreApartmentData.toApartmentSystem_apartments' {K : ChamberComplex V}
    (pre : PreApartmentData K) (hThick : K.IsThick)
    (tits_thm : TitsTheoremHyp V) :
    (pre.toApartmentSystem' hThick tits_thm).apartments = pre.apartments :=
  rfl

end AptIsCoxeterProof
