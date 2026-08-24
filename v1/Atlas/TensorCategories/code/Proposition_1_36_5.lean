/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.Twists

open CategoryTheory TensorCategories

universe u

section Prop_1_36_5

variable (k : Type u) [Field k] (G : Type u) [Group G]

/-- Map from `H^2(G, k×)` to isomorphism classes of monoidal fiber functors on `Vec_G`,
sending a cohomology class `[J]` to the isomorphism class of the fiber functor twisted by
the cocycle `J`. -/
noncomputable def cocycleH2ToFiberFunctorClass :
    CocycleH2 G kˣ → MonoidalFiberFunctorIsoClasses k (VecG k G) :=
  Quotient.lift
    (fun J => @Quotient.mk _ (monoidalFiberFunctorSetoid k (VecG k G))
      (cocycleToFiberFunctor k G J))
    (fun J₁ J₂ h => Quotient.sound
      ((cocycleToFiberFunctor_iso_iff_cohomologous k G J₁ J₂).mpr h))

/-- Computation rule: on the cohomology class of a representative cocycle `J`, the map
`cocycleH2ToFiberFunctorClass` returns the isomorphism class of the corresponding fiber
functor. -/
theorem cocycleH2ToFiberFunctorClass_mk (J : Cocycle2 G kˣ) :
    cocycleH2ToFiberFunctorClass k G
      (@Quotient.mk _ (cocycleCohomologousSetoid G kˣ) J) =
    @Quotient.mk _ (monoidalFiberFunctorSetoid k (VecG k G))
      (cocycleToFiberFunctor k G J) :=
  rfl

/-- Injectivity of the map from `H^2(G, k×)` to isomorphism classes of monoidal fiber
functors on `Vec_G`. -/
theorem cocycleH2ToFiberFunctorClass_injective :
    Function.Injective (cocycleH2ToFiberFunctorClass k G) := by
  intro q₁ q₂ h
  obtain ⟨J₁, rfl⟩ := Quotient.exists_rep q₁
  obtain ⟨J₂, rfl⟩ := Quotient.exists_rep q₂
  apply Quotient.sound
  rw [cocycleH2ToFiberFunctorClass_mk, cocycleH2ToFiberFunctorClass_mk] at h
  exact (cocycleToFiberFunctor_iso_iff_cohomologous k G J₁ J₂).mp (Quotient.exact h)

/-- Surjectivity of the map from `H^2(G, k×)` to isomorphism classes of monoidal fiber
functors on `Vec_G`. -/
theorem cocycleH2ToFiberFunctorClass_surjective :
    Function.Surjective (cocycleH2ToFiberFunctorClass k G) := by
  intro q
  obtain ⟨FF, rfl⟩ := Quotient.exists_rep q
  obtain ⟨J, hJ⟩ := cocycleToFiberFunctor_surj k G FF
  exact ⟨@Quotient.mk _ (cocycleCohomologousSetoid G kˣ) J,
    by rw [cocycleH2ToFiberFunctorClass_mk]
       exact Quotient.sound ((monoidalFiberFunctorSetoid k (VecG k G)).iseqv.symm hJ)⟩

/-- Bijectivity of the map from `H^2(G, k×)` to isomorphism classes of monoidal fiber
functors on `Vec_G`. -/
theorem cocycleH2ToFiberFunctorClass_bijective :
    Function.Bijective (cocycleH2ToFiberFunctorClass k G) :=
  ⟨cocycleH2ToFiberFunctorClass_injective k G,
   cocycleH2ToFiberFunctorClass_surjective k G⟩

/-- Proposition 1.36.5: Fiber functors on `Vec_G` up to isomorphism bijectively correspond
to `H^2(G, k×)`. -/
theorem Proposition_1_36_5 :
    Nonempty (MonoidalFiberFunctorIsoClasses k (VecG k G) ≃ CocycleH2 G kˣ) :=
  ⟨(Equiv.ofBijective _ (cocycleH2ToFiberFunctorClass_bijective k G)).symm⟩

end Prop_1_36_5
