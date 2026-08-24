/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.AptIsCoxeterUnconditional

open ChamberComplex

variable {V : Type} [DecidableEq V]

namespace AptIsCoxeterProof

/-- Apartments in a thick chamber complex carry a thin chamber-complex structure with sufficient
foldings — restatement of the thickness hypothesis specialized to apartments. -/
theorem apt_sufficient_foldings
    (K : ChamberComplex V) (hThick : K.IsThick)
    (pre : PreApartmentData K)
    (A : SimplicialComplex V) (hA : A ∈ pre.apartments) :
    ∃ (cc : ChamberComplex V),
      cc.toSimplicialComplex = A ∧
      cc.IsThin ∧
      HasSufficientFoldings cc :=
  thickness_hyp K hThick pre A hA

end AptIsCoxeterProof
