/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.QuasiBialgebra
import Atlas.TensorCategories.code.QuasiTensorFunctor

set_option maxHeartbeats 800000

open scoped TensorProduct
open CategoryTheory

universe u v

namespace TensorCategories

/-- Proposition 1.34.4: In a quasi-bialgebra `H`, the comultiplication, counit and
associator `Φ` satisfy the standard quasi-bialgebra identities (quasi-coassociativity,
pentagon, and counit identities). -/
theorem prop_1_34_4
    (R : Type u) [CommSemiring R]
    (H : Type v) [Semiring H] [Algebra R H] [hQB : QuasiBialgebra R H] :

    (∀ a : H,
      QuasiBialgebra.idTensorComul R H hQB.comul a * (hQB.Φ : H ⊗[R] (H ⊗[R] H)) =
      (hQB.Φ : H ⊗[R] (H ⊗[R] H)) * QuasiBialgebra.comulTensorId R H hQB.comul a) ∧

    ((1 : H) ⊗ₜ[R] (hQB.Φ : H ⊗[R] (H ⊗[R] H)) *
        QuasiBialgebra.idComulId R H hQB.comul (hQB.Φ : H ⊗[R] (H ⊗[R] H)) *
        QuasiBialgebra.embedPhiRight R H (hQB.Φ : H ⊗[R] (H ⊗[R] H)) =
      QuasiBialgebra.idIdComul R H hQB.comul (hQB.Φ : H ⊗[R] (H ⊗[R] H)) *
        QuasiBialgebra.comulIdId R H hQB.comul (hQB.Φ : H ⊗[R] (H ⊗[R] H))) ∧

    ((Algebra.TensorProduct.lid R H).toAlgHom.comp
      ((Algebra.TensorProduct.map hQB.counit (AlgHom.id R H)).comp hQB.comul) =
      AlgHom.id R H) ∧

    ((Algebra.TensorProduct.rid R R H).toAlgHom.comp
      ((Algebra.TensorProduct.map (AlgHom.id R H) hQB.counit).comp hQB.comul) =
      AlgHom.id R H) ∧

    (QuasiBialgebra.idCounitId R H hQB.counit (hQB.Φ : H ⊗[R] (H ⊗[R] H)) = 1) :=
  ⟨hQB.quasi_coassoc, hQB.pentagon, hQB.left_counit, hQB.right_counit, hQB.Φ_counit⟩

/-- Proposition 1.35.1: In a quasi-Hopf algebra, the antipode `S`, the elements `α`, `β`
and the associator `Φ` satisfy the two identities
`Σ Φ_i^1 β S(Φ_i^2) α Φ_i^3 = 1` and `Σ S(Φ̄_i^1) α Φ̄_i^2 β S(Φ̄_i^3) = 1`. -/
theorem prop_1_35_1
    (R : Type u) [CommSemiring R]
    (H : Type v) [Semiring H] [Algebra R H] [hQH : QuasiHopfAlgebra R H] :

    QuasiBialgebra.phiBetaSAlphaMap R H hQH.S.toLinearMap hQH.α_elem hQH.β_elem
      (hQH.Φ : H ⊗[R] (H ⊗[R] H)) = 1 ∧

    QuasiBialgebra.phiInvSAlphaBetaSMap R H hQH.S.toLinearMap hQH.α_elem hQH.β_elem
      (↑hQH.Φ⁻¹ : H ⊗[R] (H ⊗[R] H)) = 1 :=
  ⟨hQH.phi_beta_S_alpha, hQH.phiInv_S_alpha_beta_S⟩

/-- Proposition 1.35.1 (named restatement): The quasi-Hopf identities of `prop_1_35_1`
packaged under the textbook name. -/
theorem Proposition_1_35_1
    (R : Type u) [CommSemiring R]
    (H : Type v) [Semiring H] [Algebra R H] [hQH : QuasiHopfAlgebra R H] :
    QuasiBialgebra.phiBetaSAlphaMap R H hQH.S.toLinearMap hQH.α_elem hQH.β_elem
      (hQH.Φ : H ⊗[R] (H ⊗[R] H)) = 1 ∧
    QuasiBialgebra.phiInvSAlphaBetaSMap R H hQH.S.toLinearMap hQH.α_elem hQH.β_elem
      (↑hQH.Φ⁻¹ : H ⊗[R] (H ⊗[R] H)) = 1 :=
  prop_1_35_1 R H

end TensorCategories
