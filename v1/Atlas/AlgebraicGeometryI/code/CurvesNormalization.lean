/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.FractionRing

open Algebra

section FiniteBirationalNormal

/-- If `B` is an integrally closed domain with fraction field `K` and `A` is the integral
closure of `B` in `K`, then `A` is algebra-isomorphic to `B` (so a finite birational map
over a normal base is an isomorphism). -/
noncomputable def finite_birational_normal_algEquiv
    (B A K : Type*) [CommRing B] [IsDomain B] [CommRing A]
    [Field K]
    [Algebra B K] [IsFractionRing B K]
    [Algebra A K] [Algebra B A]
    [IsScalarTower B A K]
    [IsIntegrallyClosed B]
    [IsIntegralClosure A B K] :
    A ≃ₐ[B] B :=
  haveI : IsIntegralClosure B B K := (isIntegrallyClosed_iff_isIntegralClosure K).mp inferInstance
  IsIntegralClosure.equiv B A K B

/-- Under the same hypotheses as `finite_birational_normal_algEquiv`, the structure map
`B → A` is bijective. -/
theorem finite_birational_normal_algebraMap_bijective
    (B A K : Type*) [CommRing B] [IsDomain B] [CommRing A]
    [Field K]
    [Algebra B K] [IsFractionRing B K]
    [Algebra A K] [Algebra B A]
    [IsScalarTower B A K]
    [IsIntegrallyClosed B]
    [IsIntegralClosure A B K] :
    Function.Bijective (algebraMap B A) := by
  have : IsIntegralClosure B B K := (isIntegrallyClosed_iff_isIntegralClosure K).mp inferInstance
  let e := IsIntegralClosure.equiv B A K B
  have key : (e.symm : B → A) = algebraMap B A := by
    ext b
    have h1 : e.symm b = e.symm (algebraMap B B b) := by simp
    exact h1.trans (e.symm.commutes b)
  rw [← key]
  exact e.symm.bijective

end FiniteBirationalNormal

section Normalization

set_option backward.isDefEq.respectTransparency false in
/-- The normalization of an integrally closed domain `A` (its integral closure in its
fraction field) is `A` itself. -/
noncomputable def normalization_of_normal_is_self
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] :
    integralClosure A (FractionRing A) ≃ₐ[A] A := by
  haveI : IsIntegralClosure A A (FractionRing A) :=
    (isIntegrallyClosed_iff_isIntegralClosure (FractionRing A)).mp inferInstance
  letI : Algebra (integralClosure A (FractionRing A)) (FractionRing A) :=
    (integralClosure A (FractionRing A)).val.toRingHom.toAlgebra
  haveI : IsScalarTower A (integralClosure A (FractionRing A)) (FractionRing A) := by
    constructor
    intro x y z
    simp [Algebra.smul_def, mul_assoc]
  exact IsIntegralClosure.equiv A (integralClosure A (FractionRing A)) (FractionRing A) A

end Normalization

section Proposition28

/-- Proposition 28 (finiteness part): For a finitely generated `k`-algebra domain `A` with
fraction field `K` and a finite field extension `L/K`, the integral closure of `A` in `L`
is finite over `A`. -/
theorem normalization_is_finite_general
    (k A : Type*) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L] :
    Module.Finite A (integralClosure A L) := by
  sorry

/-- Proposition 28 (finite-type part): The integral closure of `A` in `L` remains of finite
type over the base field `k`. -/
theorem normalization_finiteType_general
    (k A : Type*) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Algebra k K] [IsScalarTower k A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L]
    [Algebra k L] [IsScalarTower k A L] :
    Algebra.FiniteType k (integralClosure A L) := by
  haveI : Module.Finite A (integralClosure A L) :=
    normalization_is_finite_general k A K L
  exact Algebra.FiniteType.trans (‹Algebra.FiniteType k A›)
    (Module.Finite.finiteType (integralClosure A L))

/-- Proposition 28 (normality part): The integral closure of `A` in a finite extension `L`
is itself integrally closed. -/
theorem normalization_is_normal_general
    (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra A L] [IsScalarTower A K L] :
    IsIntegrallyClosed (integralClosure A L) :=
  integralClosure.isIntegrallyClosedOfFiniteExtension K

/-- The structure map `A → integralClosure A L` is injective, so normalization does not
collapse the base. -/
theorem normalization_map_injective_general
    (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type*) [Field L] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] :
    Function.Injective (algebraMap A (integralClosure A L)) := by
  haveI : IsScalarTower A (integralClosure A L) L :=
    IsScalarTower.subalgebra' A L L (integralClosure A L)
  exact algebraMap_injective_of_field_isFractionRing A (↥(integralClosure A L)) K L

end Proposition28
