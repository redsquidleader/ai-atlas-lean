/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.Ch22ConductorDef
import Atlas.NumberTheoryI.code.Lem225

noncomputable section

open scoped NumberField

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

theorem Modulus.ext_iff (𝔪 𝔫 : Modulus K) : 𝔪 = 𝔫 ↔ ∀ v, 𝔪 v = 𝔫 v := by
  constructor
  · rintro rfl; intro; rfl
  · intro h
    cases 𝔪; cases 𝔫
    congr 1
    funext v
    exact h v

theorem Modulus.dvd_antisymm (𝔪 𝔫 : Modulus K) (h₁ : 𝔪.dvd 𝔫) (h₂ : 𝔫.dvd 𝔪) :
    𝔪 = 𝔫 := by
  rw [Modulus.ext_iff]
  intro v
  exact le_antisymm (h₁ v) (h₂ v)

theorem proposition_22_9
    (p : CongruenceSubgroupPair K)
    (p₀ : CongruenceSubgroupPair K)
    (hmod : p₀.modulus = p.modulus)
    (hprim : p.IsPrimitive)
    (hle : p₀.toAmbientSubgroup ≤ p.toAmbientSubgroup) :
    p₀.conductor = p.modulus := by

  set 𝔠 := p₀.conductor with h𝔠_def

  have h𝔠_dvd_𝔪 : 𝔠.dvd p.modulus := by
    rw [← hmod]
    exact p₀.conductor_dvd

  obtain ⟨p₀', hp₀'_mod, hp₀'_equiv⟩ := conductorModulus_exists_equiv p₀

  have hp₀'_dvd : p₀'.modulus.dvd p₀.modulus := by
    rw [hp₀'_mod]
    exact p₀.conductor_dvd
  have hlem225_p₀ : FracIdealsCoprime_subgroup K p₀.modulus ⊓
      RayGroup.toAmbientSubgroup K p₀'.modulus ≤ p₀.toAmbientSubgroup :=
    lemma_22_5_necessity p₀ p₀' hp₀'_dvd hp₀'_equiv


  have hlem225_p : FracIdealsCoprime_subgroup K p.modulus ⊓
      RayGroup.toAmbientSubgroup K 𝔠 ≤ p.toAmbientSubgroup := by
    intro x hx
    apply hle
    have : x ∈ FracIdealsCoprime_subgroup K p₀.modulus ⊓
        RayGroup.toAmbientSubgroup K p₀'.modulus := by
      constructor
      · rw [hmod]; exact hx.1
      · rw [hp₀'_mod]; exact hx.2
    exact hlem225_p₀ this


  have hexists_equiv_𝔠 : ∃ p' : CongruenceSubgroupPair K,
      p'.modulus = 𝔠 ∧ p.IsEquiv p' := by
    rw [lemma_22_5 p 𝔠 h𝔠_dvd_𝔪]
    exact hlem225_p


  have h𝔪_dvd_𝔠 : p.modulus.dvd 𝔠 := by
    obtain ⟨p', hp'_mod, hp'_equiv⟩ := hexists_equiv_𝔠
    have : p.conductor.dvd p'.modulus :=
      p.conductor_dvd_of_equiv p' hp'_equiv
    rw [hp'_mod] at this
    rwa [← hprim] at this

  exact Modulus.dvd_antisymm 𝔠 p.modulus h𝔠_dvd_𝔪 h𝔪_dvd_𝔠

end RayClassField
