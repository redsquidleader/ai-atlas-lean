/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.SL2Representations

noncomputable section

open Complex

structure PrincipalSeriesBridge
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    (ν : ℂ) (ε : ZMod 2)
    (R : SL2IrredGKModule.Realization (.principalSeries ν ε) 𝔤 K 𝔨 Ad) where
  toModel : R.W ≃ₗ[ℂ] (ℤ → ℂ)
  compat_H : ∀ w : R.W,
    toModel (⁅sl2_canonical_H 𝔤, w⁆) = principalSeries_ρH ν ε (toModel w)
  compat_E : ∀ w : R.W,
    toModel (⁅sl2_canonical_E 𝔤, w⁆) = principalSeries_ρE ν ε (toModel w)
  compat_F : ∀ w : R.W,
    toModel (⁅sl2_canonical_F 𝔤, w⁆) = principalSeries_ρF ν ε (toModel w)

namespace PrincipalSeriesBridge

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
variable {K : Type*} [Group K]
variable {𝔨 : LieSubalgebra ℂ 𝔤}
variable {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}

def neg_intertwining_linearMap
    {s : ℂ} {ε : ZMod 2}
    {R₁ : SL2IrredGKModule.Realization (.principalSeries s ε) 𝔤 K 𝔨 Ad}
    {R₂ : SL2IrredGKModule.Realization (.principalSeries (-s) ε) 𝔤 K 𝔨 Ad}
    (b₁ : PrincipalSeriesBridge s ε R₁)
    (b₂ : PrincipalSeriesBridge (-s) ε R₂)
    (c : ℤ → ℂ) : R₁.W →ₗ[ℂ] R₂.W :=
  b₂.toModel.symm.toLinearMap ∘ₗ (principalSeries_neg_map c) ∘ₗ b₁.toModel.toLinearMap

lemma neg_intertwining_bijective
    {s : ℂ} {ε : ZMod 2}
    {R₁ : SL2IrredGKModule.Realization (.principalSeries s ε) 𝔤 K 𝔨 Ad}
    {R₂ : SL2IrredGKModule.Realization (.principalSeries (-s) ε) 𝔤 K 𝔨 Ad}
    (b₁ : PrincipalSeriesBridge s ε R₁)
    (b₂ : PrincipalSeriesBridge (-s) ε R₂)
    (c : ℤ → ℂ) (hc : ∀ m : ℤ, c m ≠ 0) :
    Function.Bijective (neg_intertwining_linearMap b₁ b₂ c) := by


  have h_neg_bij : Function.Bijective (principalSeries_neg_map c) := by
    constructor
    · intro f g hfg
      ext m
      have hm : (principalSeries_neg_map c) f m = (principalSeries_neg_map c) g m := by
        rw [hfg]
      simp only [principalSeries_neg_map, LinearMap.coe_mk, AddHom.coe_mk] at hm
      exact mul_left_cancel₀ (hc m) hm
    · intro f
      exact ⟨fun m => (c m)⁻¹ * f m, by
        ext m
        simp only [principalSeries_neg_map, LinearMap.coe_mk, AddHom.coe_mk]
        rw [← mul_assoc, mul_inv_cancel₀ (hc m), one_mul]⟩

  have hb₁ := b₁.toModel.bijective
  have hb₂ := b₂.toModel.symm.bijective
  exact hb₂.comp (h_neg_bij.comp hb₁)

end PrincipalSeriesBridge

end
