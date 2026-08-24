/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.Theorem22_11

open scoped RestrictedProduct
open FunctionFieldAdeleRing DiscreteValuationFamily

section Lemma22_13
set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] {P : Type*} [DecidableEq P]
  {O : P → ValuationSubring F}
  (k : Type*) [Field k] [Algebra k F]
  [ConstantField k (F := F) (P := P) (O := O)]
  [FunctionFieldProperty F P O]
  [DiscreteValuationFamily P F k]
  [HasResidueFieldSurjection P F k O]

/-- **Lemma 22.13.** The $k$-dimension of the Weil differentials regular at the
divisor $D$ equals the index of speciality: $\dim_k \Omega(D) = i(D)$. -/
theorem weilDifferentials_dim_eq_indexOfSpeciality (D : P →₀ ℤ) :
    (Module.finrank k ↥(weilDifferentials (F := F) (O := O) k (D : P → ℤ)) : ℤ) =
      adeleIndexOfSpeciality (F := F) (O := O) k D := by

  have h_duality := weilDifferentials_finrank_eq (F := F) (O := O) k (D : P → ℤ)

  obtain ⟨_, h_dim⟩ := speciality_eq_adele_quotient_dim (F := F) (O := O) k D

  have h1 : (Module.finrank k ↥(weilDifferentials (F := F) (O := O) k (↑D : P → ℤ)) : ℤ) =
    (Module.finrank k (FunctionFieldAdeleRing F P O ⧸
        (adeleSpace (F := F) (O := O) k (↑D : P → ℤ) ⊔
          principalAdeles (F := F) (O := O) k)) : ℤ) := by
    exact_mod_cast h_duality
  exact h1.trans h_dim

end Lemma22_13
