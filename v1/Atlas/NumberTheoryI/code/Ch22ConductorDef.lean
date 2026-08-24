/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.Cor227

noncomputable section

open scoped NumberField

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

noncomputable def conductorModulus (p : CongruenceSubgroupPair K) : Modulus K :=
  (corollary_22_7_existence p).choose.modulus

lemma conductorModulus_witness_spec (p : CongruenceSubgroupPair K) :
    p.IsEquiv (corollary_22_7_existence p).choose ∧
    ∀ q : CongruenceSubgroupPair K, p.IsEquiv q →
      (conductorModulus p).dvd q.modulus :=
  (corollary_22_7_existence p).choose_spec

theorem conductorModulus_dvd (p : CongruenceSubgroupPair K) :
    (conductorModulus p).dvd p.modulus :=
  (conductorModulus_witness_spec p).2 p (CongruenceSubgroupPair.isEquiv_refl p)

theorem conductorModulus_dvd_of_equiv (p p' : CongruenceSubgroupPair K)
    (h : p.IsEquiv p') : (conductorModulus p).dvd p'.modulus :=
  (conductorModulus_witness_spec p).2 p' h

theorem conductorModulus_eq_of_equiv (p₁ p₂ : CongruenceSubgroupPair K)
    (h : p₁.IsEquiv p₂) : conductorModulus p₁ = conductorModulus p₂ := by

  have h₁₂ : (conductorModulus p₁).dvd (conductorModulus p₂) := by
    have hp₂₀ := (conductorModulus_witness_spec p₂).1
    have hp₁_witness₂ : p₁.IsEquiv (corollary_22_7_existence p₂).choose :=
      h.trans' hp₂₀
    exact (conductorModulus_witness_spec p₁).2 _ hp₁_witness₂

  have h₂₁ : (conductorModulus p₂).dvd (conductorModulus p₁) := by
    have hp₁₀ := (conductorModulus_witness_spec p₁).1
    have hp₂_witness₁ : p₂.IsEquiv (corollary_22_7_existence p₁).choose :=
      h.symm'.trans' hp₁₀
    exact (conductorModulus_witness_spec p₂).2 _ hp₂_witness₁
  exact Modulus.dvd_antisymm' h₁₂ h₂₁

theorem conductorModulus_exists_equiv (p : CongruenceSubgroupPair K) :
    ∃ p' : CongruenceSubgroupPair K,
      p'.modulus = conductorModulus p ∧ p.IsEquiv p' :=
  ⟨(corollary_22_7_existence p).choose, rfl, (conductorModulus_witness_spec p).1⟩

def CongruenceSubgroupPair.conductor (p : CongruenceSubgroupPair K) : Modulus K :=
  conductorModulus p

def CongruenceSubgroupPair.IsPrimitive (p : CongruenceSubgroupPair K) : Prop :=
  p.modulus = p.conductor

theorem CongruenceSubgroupPair.conductor_dvd (p : CongruenceSubgroupPair K) :
    p.conductor.dvd p.modulus :=
  conductorModulus_dvd p

theorem CongruenceSubgroupPair.conductor_dvd_of_equiv
    (p p' : CongruenceSubgroupPair K) (h : p.IsEquiv p') :
    p.conductor.dvd p'.modulus :=
  conductorModulus_dvd_of_equiv p p' h

theorem CongruenceSubgroupPair.conductor_eq_of_equiv
    (p₁ p₂ : CongruenceSubgroupPair K) (h : p₁.IsEquiv p₂) :
    p₁.conductor = p₂.conductor :=
  conductorModulus_eq_of_equiv p₁ p₂ h

end RayClassField
