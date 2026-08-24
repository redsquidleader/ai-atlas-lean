/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.CombinatorialGeometry.ThreeChamber

open scoped Classical

variable {V : Type*} [DecidableEq V]

namespace CombinatorialGeometry

/-- Existence of an auxiliary retraction $\rho$ onto an apartment $A$ centered at $C$ that
preserves the Weyl-valued distance $\delta_W(C, \cdot)$ and sends adjacent chambers to equal or
adjacent images. -/
theorem auxiliary_retraction_exists {b : Building V}
    (δW : Building.WValuedDist b)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC : A.IsMaximal C) :
    ∃ (ρ : Finset V → Finset V),

      (∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D →
        ρ D ∈ A.faces ∧ A.IsMaximal (ρ D)) ∧

      (∀ D, D ∈ A.faces → A.IsMaximal D → ρ D = D) ∧

      (∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D →
        δW.delta C (ρ D) = δW.delta C D) ∧

      (∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D →
        δW.delta (ρ D) C = δW.delta D C) ∧

      (∀ D₁ D₂, b.toChamberComplex.toSimplicialComplex.Adjacent D₁ D₂ →
        ρ D₁ = ρ D₂ ∨ A.Adjacent (ρ D₁) (ρ D₂)) :=
  δW.delta_retraction_preserves A hA C hC

/-- The Weyl-distance preserving retraction agrees with any other $\delta_W$-isometry $f$ on the
domain $Y$ where $f$ takes values in $A$. -/
theorem strong_isometry_determined_by_retraction {b : Building V}
    (δW : Building.WValuedDist b)
    (A : SimplicialComplex V) (hA : A ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC : A.IsMaximal C)
    (ρ : Finset V → Finset V)

    (hρ_max : ∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D →
      ρ D ∈ A.faces ∧ A.IsMaximal (ρ D))
    (hρ_fix : ∀ D, D ∈ A.faces → A.IsMaximal D → ρ D = D)
    (hρ_delta : ∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D →
      δW.delta C (ρ D) = δW.delta C D)

    (Y : Set (Finset V)) (f : Finset V → Finset V)
    (hY : ∀ y ∈ Y, b.toChamberComplex.toSimplicialComplex.IsMaximal y)
    (hf_img : ∀ y ∈ Y, f y ∈ A.faces)
    (hf_delta : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, δW.delta (f y₁) (f y₂) = δW.delta y₁ y₂) :

    ∀ y ∈ Y, ρ y = f y :=
  δW.delta_retraction_agrees_with_iso A hA C hC ρ hρ_max hρ_fix hρ_delta Y f hY hf_img hf_delta

end CombinatorialGeometry
