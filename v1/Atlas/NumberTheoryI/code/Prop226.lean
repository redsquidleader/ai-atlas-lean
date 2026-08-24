/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.Lem225

noncomputable section

open scoped NumberField

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

lemma Modulus.gcd_dvd_left (𝔪₁ 𝔪₂ : Modulus K) : (𝔪₁.gcd 𝔪₂).dvd 𝔪₁ :=
  fun _ => min_le_left _ _

lemma Modulus.gcd_dvd_right (𝔪₁ 𝔪₂ : Modulus K) : (𝔪₁.gcd 𝔪₂).dvd 𝔪₂ :=
  fun _ => min_le_right _ _

lemma Modulus.dvd_lcm_left (𝔪₁ 𝔪₂ : Modulus K) : 𝔪₁.dvd (𝔪₁.lcm 𝔪₂) :=
  fun _ => le_max_left _ _

lemma Modulus.dvd_lcm_right (𝔪₁ 𝔪₂ : Modulus K) : 𝔪₂.dvd (𝔪₁.lcm 𝔪₂) :=
  fun _ => le_max_right _ _

theorem weak_approx_ray_gen_aux' {K : Type u} [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (α : Kˣ)
    (hα_cop : ∀ v : FinitePlace K, (𝔪₁.gcd 𝔪₂) (Place.finite v) ≠ 0 →
      v.valuation K (α : K) = 1)
    (hα_val : ∀ v : FinitePlace K, (𝔪₁.gcd 𝔪₂) (Place.finite v) ≠ 0 →
      v.valuation K ((α : K) - 1) ≤
        ↑(Multiplicative.ofAdd (-((𝔪₁.gcd 𝔪₂) (Place.finite v) : ℤ))))
    (hα_sign : ∀ w : NumberField.InfinitePlace K,
      (𝔪₁.gcd 𝔪₂) (Place.infinite w) ≠ 0 →
      0 < (w.embedding (α : K)).re) :
    ∃ (β : Kˣ),

      (∀ v : FinitePlace K, 𝔪₁ (Place.finite v) ≠ 0 → v.valuation K ((α * β : Kˣ) : K) = 1) ∧

      (∀ v : FinitePlace K, 𝔪₁ (Place.finite v) ≠ 0 →
        v.valuation K (((α * β : Kˣ) : K) - 1) ≤
          ↑(Multiplicative.ofAdd (-(𝔪₁ (Place.finite v) : ℤ)))) ∧

      (∀ w : NumberField.InfinitePlace K, 𝔪₁ (Place.infinite w) ≠ 0 →
        0 < (w.embedding ((α * β : Kˣ) : K)).re) ∧

      (∀ v : FinitePlace K, 𝔪₂ (Place.finite v) ≠ 0 → v.valuation K ((β⁻¹ : Kˣ) : K) = 1) ∧

      (∀ v : FinitePlace K, 𝔪₂ (Place.finite v) ≠ 0 →
        v.valuation K (((β⁻¹ : Kˣ) : K) - 1) ≤
          ↑(Multiplicative.ofAdd (-(𝔪₂ (Place.finite v) : ℤ)))) ∧

      (∀ w : NumberField.InfinitePlace K, 𝔪₂ (Place.infinite w) ≠ 0 →
        0 < (w.embedding ((β⁻¹ : Kˣ) : K)).re) := by

  sorry

theorem weak_approx_coprime_CRT_aux {K : Type u} [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (J : (FracIdeal K)ˣ)
    (hJ : J ∈ FracIdealsCoprime_subgroup K 𝔪₁) :
    ∃ (a b : (FracIdeal K)ˣ),
      a ∈ FracIdealsCoprime_subgroup K 𝔪₂ ∧
      b ∈ FracIdealsCoprime_subgroup K 𝔪₁ ∧
      b ∈ RayGroup.toAmbientSubgroup K (𝔪₁.gcd 𝔪₂) ∧
      J = a * b := by

  sorry

theorem theorem_8_5_ray_gen_decomp {K : Type u} [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (I : FracIdealsCoprime K (𝔪₁.gcd 𝔪₂))
    (hI : IsRayGenerator (𝔪₁.gcd 𝔪₂) I) :
    ∃ (I₁ : FracIdealsCoprime K 𝔪₁) (I₂ : FracIdealsCoprime K 𝔪₂),
      IsRayGenerator 𝔪₁ I₁ ∧
      IsRayGenerator 𝔪₂ I₂ ∧
      (FracIdealsCoprime_subgroup K (𝔪₁.gcd 𝔪₂)).subtype I =
        (FracIdealsCoprime_subgroup K 𝔪₁).subtype I₁ *
        (FracIdealsCoprime_subgroup K 𝔪₂).subtype I₂ := by
  classical
  obtain ⟨α, hα_eq, hα_val, hα_sign⟩ := hI

  have hα_cop : ∀ v : FinitePlace K, (𝔪₁.gcd 𝔪₂) (Place.finite v) ≠ 0 →
      v.valuation K (α : K) = 1 := by
    intro v hv
    have hI_cop := I.property v hv

    have hI_val_eq : I.val = toPrincipalIdeal (𝓞 K) K α := by
      apply Units.val_injective
      rw [coe_toPrincipalIdeal]
      exact hα_eq

    rw [hI_val_eq] at hI_cop

    obtain ⟨x, hx_mem, hx_val⟩ := hI_cop.1
    simp only [coe_toPrincipalIdeal] at hx_mem
    have h_inv : HasTrivialValuation ((toPrincipalIdeal (𝓞 K) K α)⁻¹) v := hI_cop.2
    rw [← MonoidHom.map_inv] at h_inv
    obtain ⟨y, hy_mem, hy_val⟩ := h_inv
    simp only [coe_toPrincipalIdeal] at hy_mem
    rw [FractionalIdeal.mem_spanSingleton] at hx_mem hy_mem
    obtain ⟨r, hr⟩ := hx_mem
    obtain ⟨s, hs⟩ := hy_mem
    subst hr; subst hs
    simp only [Algebra.smul_def] at hx_val hy_val
    rw [map_mul] at hx_val hy_val
    have hr_le : v.valuation K (algebraMap _ K r) ≤ 1 := v.valuation_le_one r
    have hs_le : v.valuation K (algebraMap _ K s) ≤ 1 := v.valuation_le_one s
    have hαα : v.valuation K (α : K) * v.valuation K ((α⁻¹ : Kˣ) : K) = 1 := by
      rw [← map_mul, show (α : K) * ((α⁻¹ : Kˣ) : K) = 1 from by simp, map_one]
    apply le_antisymm
    · calc v.valuation K (α : K)
          = v.valuation K (α : K) * 1 := (mul_one _).symm
        _ = v.valuation K (α : K) * (v.valuation K (algebraMap _ K s) *
            v.valuation K ((α⁻¹ : Kˣ) : K)) := by rw [hy_val]
        _ = (v.valuation K (α : K) * v.valuation K ((α⁻¹ : Kˣ) : K)) *
            v.valuation K (algebraMap _ K s) := by
              rw [mul_assoc, mul_comm (v.valuation K (algebraMap _ K s))]
        _ = 1 * v.valuation K (algebraMap _ K s) := by rw [hαα]
        _ = v.valuation K (algebraMap _ K s) := one_mul _
        _ ≤ 1 := hs_le
    · calc (1 : WithZero (Multiplicative ℤ))
          = v.valuation K (algebraMap _ K r) * v.valuation K (α : K) := hx_val.symm
        _ ≤ 1 * v.valuation K (α : K) := by gcongr
        _ = v.valuation K (α : K) := one_mul _

  obtain ⟨β, hαβ_cop, hαβ_val, hαβ_sign, hβinv_cop, hβinv_val, hβinv_sign⟩ :=
    weak_approx_ray_gen_aux' 𝔪₁ 𝔪₂ α hα_cop hα_val hα_sign

  have hαβ_in_coprime : (α * β) ∈ UnitsCoprime_subgroup' K 𝔪₁ := hαβ_cop

  have hβinv_in_coprime : β⁻¹ ∈ UnitsCoprime_subgroup' K 𝔪₂ := hβinv_cop

  let I₁ : FracIdealsCoprime K 𝔪₁ :=
    ⟨toPrincipalIdeal (𝓞 K) K (α * β),
     toPrincipalIdeal_mem_FracIdealsCoprime 𝔪₁ (α * β) hαβ_in_coprime⟩
  let I₂ : FracIdealsCoprime K 𝔪₂ :=
    ⟨toPrincipalIdeal (𝓞 K) K β⁻¹,
     toPrincipalIdeal_mem_FracIdealsCoprime 𝔪₂ β⁻¹ hβinv_in_coprime⟩
  refine ⟨I₁, I₂, ?_, ?_, ?_⟩
  ·
    exact ⟨α * β, coe_toPrincipalIdeal (α * β), hαβ_val, hαβ_sign⟩
  ·
    exact ⟨β⁻¹, coe_toPrincipalIdeal β⁻¹, hβinv_val, hβinv_sign⟩
  ·


    apply Units.ext

    simp only [Subgroup.coe_subtype, Units.val_mul]


    have hI_val_eq : I.val = toPrincipalIdeal (𝓞 K) K α := by
      apply Units.val_injective
      rw [coe_toPrincipalIdeal]
      exact hα_eq

    simp only [hI_val_eq]


    have hI1_coe : (I₁.val.val : FracIdeal K) = (toPrincipalIdeal (𝓞 K) K (α * β)).val := rfl
    have hI2_coe : (I₂.val.val : FracIdeal K) = (toPrincipalIdeal (𝓞 K) K β⁻¹).val := rfl
    rw [hI1_coe, hI2_coe]
    simp only [coe_toPrincipalIdeal]
    rw [show ((α * β : Kˣ) : K) = (α : K) * (β : K) from Units.val_mul α β,
        show ((β⁻¹ : Kˣ) : K) = (β : K)⁻¹ from Units.val_inv_eq_inv_val β,
        FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    field_simp

theorem ray_generator_gcd_decomp_aux {K : Type u} [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (I : FracIdealsCoprime K (𝔪₁.gcd 𝔪₂))
    (hI : IsRayGenerator (𝔪₁.gcd 𝔪₂) I) :
    ∃ (I₁ : FracIdealsCoprime K 𝔪₁) (I₂ : FracIdealsCoprime K 𝔪₂),
      IsRayGenerator 𝔪₁ I₁ ∧
      IsRayGenerator 𝔪₂ I₂ ∧
      (FracIdealsCoprime_subgroup K (𝔪₁.gcd 𝔪₂)).subtype I =
        (FracIdealsCoprime_subgroup K 𝔪₁).subtype I₁ *
        (FracIdealsCoprime_subgroup K 𝔪₂).subtype I₂ :=
  theorem_8_5_ray_gen_decomp 𝔪₁ 𝔪₂ I hI

theorem ray_generator_gcd_decomp {K : Type u} [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (I : FracIdealsCoprime K (𝔪₁.gcd 𝔪₂))
    (hI : IsRayGenerator (𝔪₁.gcd 𝔪₂) I) :
    ∃ (J₁ : (FracIdeal K)ˣ) (J₂ : (FracIdeal K)ˣ),
      J₁ ∈ RayGroup.toAmbientSubgroup K 𝔪₁ ∧
      J₂ ∈ RayGroup.toAmbientSubgroup K 𝔪₂ ∧
      (FracIdealsCoprime_subgroup K (𝔪₁.gcd 𝔪₂)).subtype I = J₁ * J₂ := by
  obtain ⟨I₁, I₂, hI₁, hI₂, hprod⟩ := ray_generator_gcd_decomp_aux 𝔪₁ 𝔪₂ I hI
  refine ⟨(FracIdealsCoprime_subgroup K 𝔪₁).subtype I₁,
          (FracIdealsCoprime_subgroup K 𝔪₂).subtype I₂, ?_, ?_, hprod⟩
  ·
    rw [RayGroup.toAmbientSubgroup]
    exact Subgroup.mem_map.mpr ⟨I₁, Subgroup.subset_closure hI₁, rfl⟩
  ·
    rw [RayGroup.toAmbientSubgroup]
    exact Subgroup.mem_map.mpr ⟨I₂, Subgroup.subset_closure hI₂, rfl⟩

theorem ray_generator_gcd_mem_sup {K : Type u} [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (I : FracIdealsCoprime K (𝔪₁.gcd 𝔪₂))
    (hI : IsRayGenerator (𝔪₁.gcd 𝔪₂) I) :
    (FracIdealsCoprime_subgroup K (𝔪₁.gcd 𝔪₂)).subtype I ∈
      RayGroup.toAmbientSubgroup K 𝔪₁ ⊔ RayGroup.toAmbientSubgroup K 𝔪₂ := by
  obtain ⟨J₁, J₂, hJ₁, hJ₂, hprod⟩ := ray_generator_gcd_decomp 𝔪₁ 𝔪₂ I hI
  rw [hprod]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hJ₁) (Subgroup.mem_sup_right hJ₂)

theorem theorem_8_5_ray_group_gcd (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K) :
    RayGroup.toAmbientSubgroup K (𝔪₁.gcd 𝔪₂) ≤
    RayGroup.toAmbientSubgroup K 𝔪₁ ⊔ RayGroup.toAmbientSubgroup K 𝔪₂ := by
  intro x hx
  rw [RayGroup.toAmbientSubgroup, Subgroup.mem_map] at hx
  obtain ⟨y, hy_mem, rfl⟩ := hx
  suffices h : RayGroup K (𝔪₁.gcd 𝔪₂) ≤
      (RayGroup.toAmbientSubgroup K 𝔪₁ ⊔ RayGroup.toAmbientSubgroup K 𝔪₂).comap
        (FracIdealsCoprime_subgroup K (𝔪₁.gcd 𝔪₂)).subtype by
    exact (h hy_mem)
  rw [RayGroup, Subgroup.closure_le]
  intro I hI
  show (FracIdealsCoprime_subgroup K (𝔪₁.gcd 𝔪₂)).subtype I ∈
    RayGroup.toAmbientSubgroup K 𝔪₁ ⊔ RayGroup.toAmbientSubgroup K 𝔪₂
  exact ray_generator_gcd_mem_sup 𝔪₁ 𝔪₂ I hI

theorem theorem_8_5_coprime_CRT_bridge (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K) :
    FracIdealsCoprime_subgroup K 𝔪₁ ≤
    FracIdealsCoprime_subgroup K 𝔪₂ ⊔
    (FracIdealsCoprime_subgroup K 𝔪₁ ⊓ RayGroup.toAmbientSubgroup K (𝔪₁.gcd 𝔪₂)) := by
  intro J hJ
  obtain ⟨a, b, ha_cop, hb_cop, hb_ray, hab⟩ := weak_approx_coprime_CRT_aux 𝔪₁ 𝔪₂ J hJ
  rw [Subgroup.mem_sup]
  exact ⟨a, ha_cop, b, ⟨hb_cop, hb_ray⟩, hab.symm⟩

theorem theorem_8_5_coprime_CRT_core (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K) :
    FracIdealsCoprime_subgroup K 𝔪₁ ≤
    FracIdealsCoprime_subgroup K 𝔪₂ ⊔
    (FracIdealsCoprime_subgroup K 𝔪₁ ⊓ RayGroup.toAmbientSubgroup K (𝔪₁.gcd 𝔪₂)) :=
  theorem_8_5_coprime_CRT_bridge K 𝔪₁ 𝔪₂

theorem theorem_8_5_coprime_decomp (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K) :
    FracIdealsCoprime_subgroup K 𝔪₁ ≤
    (FracIdealsCoprime_subgroup K 𝔪₁ ⊓ FracIdealsCoprime_subgroup K 𝔪₂) ⊔
    (FracIdealsCoprime_subgroup K 𝔪₁ ⊓ RayGroup.toAmbientSubgroup K (𝔪₁.gcd 𝔪₂)) := by


  intro x hx
  have hx' := theorem_8_5_coprime_CRT_core K 𝔪₁ 𝔪₂ hx

  have hmem : x ∈ (FracIdealsCoprime_subgroup K 𝔪₂ ⊔
      (FracIdealsCoprime_subgroup K 𝔪₁ ⊓
        RayGroup.toAmbientSubgroup K (𝔪₁.gcd 𝔪₂))) ⊓
      FracIdealsCoprime_subgroup K 𝔪₁ := ⟨hx', hx⟩

  rw [sup_comm] at hmem

  rw [sup_inf_assoc_of_le _ (inf_le_left (a := FracIdealsCoprime_subgroup K 𝔪₁))] at hmem

  rw [sup_comm, inf_comm (a := FracIdealsCoprime_subgroup K 𝔪₂)] at hmem
  exact hmem

lemma equiv_gcd_ray_le_left
    (p₁ p₂ : CongruenceSubgroupPair K)
    (hequiv : p₁.IsEquiv p₂) :
    FracIdealsCoprime_subgroup K p₁.modulus ⊓
      RayGroup.toAmbientSubgroup K (p₁.modulus.gcd p₂.modulus) ≤
    p₁.toAmbientSubgroup := by
  set 𝔪₁ := p₁.modulus
  set 𝔪₂ := p₂.modulus
  have hR₁_le_C₁ : RayGroup.toAmbientSubgroup K 𝔪₁ ≤ p₁.toAmbientSubgroup := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨y, p₁.ray_le hy, rfl⟩
  have hR₂_le_C₂ : RayGroup.toAmbientSubgroup K 𝔪₂ ≤ p₂.toAmbientSubgroup := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨y, p₂.ray_le hy, rfl⟩
  have hR₁_le_I₁ : RayGroup.toAmbientSubgroup K 𝔪₁ ≤
      FracIdealsCoprime_subgroup K 𝔪₁ :=
    RayGroup.toAmbientSubgroup_le 𝔪₁
  have hI₁_cap_R₂_le_C₁ : FracIdealsCoprime_subgroup K 𝔪₁ ⊓
      RayGroup.toAmbientSubgroup K 𝔪₂ ≤ p₁.toAmbientSubgroup := by
    intro y ⟨hy_I₁, hy_R₂⟩
    have : y ∈ FracIdealsCoprime_subgroup K 𝔪₁ ⊓ p₂.toAmbientSubgroup :=
      ⟨hy_I₁, hR₂_le_C₂ hy_R₂⟩
    rw [hequiv] at this
    exact this.2
  intro x ⟨hx_I₁, hx_R_n⟩
  have hx_sup := theorem_8_5_ray_group_gcd K 𝔪₁ 𝔪₂ hx_R_n
  have hx_inter : x ∈ FracIdealsCoprime_subgroup K 𝔪₁ ⊓
      (RayGroup.toAmbientSubgroup K 𝔪₁ ⊔ RayGroup.toAmbientSubgroup K 𝔪₂) :=
    ⟨hx_I₁, hx_sup⟩
  rw [inf_comm, sup_inf_assoc_of_le _ hR₁_le_I₁, inf_comm] at hx_inter
  exact sup_le hR₁_le_C₁ hI₁_cap_R₂_le_C₁ hx_inter

lemma equiv_gcd_ray_le_right
    (p₁ p₂ : CongruenceSubgroupPair K)
    (hequiv : p₁.IsEquiv p₂) :
    FracIdealsCoprime_subgroup K p₂.modulus ⊓
      RayGroup.toAmbientSubgroup K (p₁.modulus.gcd p₂.modulus) ≤
    p₂.toAmbientSubgroup := by
  set 𝔪₁ := p₁.modulus
  set 𝔪₂ := p₂.modulus
  have hR₁_le_C₁ : RayGroup.toAmbientSubgroup K 𝔪₁ ≤ p₁.toAmbientSubgroup := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨y, p₁.ray_le hy, rfl⟩
  have hR₂_le_C₂ : RayGroup.toAmbientSubgroup K 𝔪₂ ≤ p₂.toAmbientSubgroup := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨y, p₂.ray_le hy, rfl⟩
  have hR₂_le_I₂ : RayGroup.toAmbientSubgroup K 𝔪₂ ≤
      FracIdealsCoprime_subgroup K 𝔪₂ :=
    RayGroup.toAmbientSubgroup_le 𝔪₂
  have hI₂_cap_R₁_le_C₂ : FracIdealsCoprime_subgroup K 𝔪₂ ⊓
      RayGroup.toAmbientSubgroup K 𝔪₁ ≤ p₂.toAmbientSubgroup := by
    intro y ⟨hy_I₂, hy_R₁⟩
    have : y ∈ FracIdealsCoprime_subgroup K 𝔪₂ ⊓ p₁.toAmbientSubgroup :=
      ⟨hy_I₂, hR₁_le_C₁ hy_R₁⟩
    rw [← hequiv] at this
    exact this.2
  intro x ⟨hx_I₂, hx_R_n⟩
  have hx_sup := theorem_8_5_ray_group_gcd K 𝔪₁ 𝔪₂ hx_R_n
  have hx_inter : x ∈ FracIdealsCoprime_subgroup K 𝔪₂ ⊓
      (RayGroup.toAmbientSubgroup K 𝔪₁ ⊔ RayGroup.toAmbientSubgroup K 𝔪₂) :=
    ⟨hx_I₂, hx_sup⟩
  rw [inf_comm, sup_comm, sup_inf_assoc_of_le _ hR₂_le_I₂, inf_comm] at hx_inter
  exact sup_le hR₂_le_C₂ hI₂_cap_R₁_le_C₂ hx_inter

theorem equiv_sup_ray_gcd_eq
    (p₁ p₂ : CongruenceSubgroupPair K)
    (hequiv : p₁.IsEquiv p₂) :
    p₁.toAmbientSubgroup ⊔ RayGroup.toAmbientSubgroup K (p₁.modulus.gcd p₂.modulus) =
    p₂.toAmbientSubgroup ⊔ RayGroup.toAmbientSubgroup K (p₁.modulus.gcd p₂.modulus) := by
  set 𝔪₁ := p₁.modulus
  set 𝔪₂ := p₂.modulus
  set 𝔫 := 𝔪₁.gcd 𝔪₂
  have hI₁_R_n_le_C₁ := equiv_gcd_ray_le_left p₁ p₂ hequiv
  have hI₂_R_n_le_C₂ := equiv_gcd_ray_le_right p₁ p₂ hequiv
  have hC₁_le_I₁ := p₁.toAmbientSubgroup_le
  have hC₂_le_I₂ := p₂.toAmbientSubgroup_le
  apply le_antisymm
  · apply sup_le _ le_sup_right
    intro x hx_C₁
    have hx_I₁ : x ∈ FracIdealsCoprime_subgroup K 𝔪₁ := hC₁_le_I₁ hx_C₁
    have hx_decomp := theorem_8_5_coprime_decomp K 𝔪₁ 𝔪₂ hx_I₁
    rw [Subgroup.mem_sup] at hx_decomp
    obtain ⟨a, ha, b, hb, hab⟩ := hx_decomp
    have hb_C₁ : b ∈ p₁.toAmbientSubgroup := hI₁_R_n_le_C₁ hb
    have ha_C₁ : a ∈ p₁.toAmbientSubgroup := by
      have : a = x * b⁻¹ := by rw [← hab]; group
      rw [this]
      exact p₁.toAmbientSubgroup.mul_mem hx_C₁ (p₁.toAmbientSubgroup.inv_mem hb_C₁)
    have ha_I₂ : a ∈ FracIdealsCoprime_subgroup K 𝔪₂ := ha.2
    have ha_mem : a ∈ FracIdealsCoprime_subgroup K 𝔪₂ ⊓ p₁.toAmbientSubgroup :=
      ⟨ha_I₂, ha_C₁⟩
    rw [← hequiv] at ha_mem
    have ha_C₂ : a ∈ p₂.toAmbientSubgroup := ha_mem.2
    have hb_R_n : b ∈ RayGroup.toAmbientSubgroup K 𝔫 := hb.2
    rw [← hab]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left ha_C₂) (Subgroup.mem_sup_right hb_R_n)
  · apply sup_le _ le_sup_right
    intro x hx_C₂
    have hx_I₂ : x ∈ FracIdealsCoprime_subgroup K 𝔪₂ := hC₂_le_I₂ hx_C₂
    have hx_decomp := theorem_8_5_coprime_decomp K 𝔪₂ 𝔪₁ hx_I₂
    rw [Subgroup.mem_sup] at hx_decomp
    obtain ⟨a, ha, b, hb, hab⟩ := hx_decomp
    have hgcd_comm : 𝔪₂.gcd 𝔪₁ = 𝔫 := by
      show Modulus.gcd 𝔪₂ 𝔪₁ = Modulus.gcd 𝔪₁ 𝔪₂
      simp only [Modulus.gcd]
      congr 1
      funext v
      exact min_comm _ _
    have hb' : b ∈ FracIdealsCoprime_subgroup K 𝔪₂ ⊓ RayGroup.toAmbientSubgroup K 𝔫 := by
      constructor
      · exact hb.1
      · rw [← hgcd_comm]; exact hb.2
    have hb_C₂ : b ∈ p₂.toAmbientSubgroup := hI₂_R_n_le_C₂ hb'
    have ha_C₂ : a ∈ p₂.toAmbientSubgroup := by
      have : a = x * b⁻¹ := by rw [← hab]; group
      rw [this]
      exact p₂.toAmbientSubgroup.mul_mem hx_C₂ (p₂.toAmbientSubgroup.inv_mem hb_C₂)
    have ha_I₁ : a ∈ FracIdealsCoprime_subgroup K 𝔪₁ := ha.2
    have ha_mem : a ∈ FracIdealsCoprime_subgroup K 𝔪₁ ⊓ p₂.toAmbientSubgroup :=
      ⟨ha_I₁, ha_C₂⟩
    rw [hequiv] at ha_mem
    have ha_C₁ : a ∈ p₁.toAmbientSubgroup := ha_mem.2
    have hb_R_n : b ∈ RayGroup.toAmbientSubgroup K 𝔫 := hb'.2
    rw [← hab]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left ha_C₁) (Subgroup.mem_sup_right hb_R_n)

theorem proposition_22_6
    (p₁ p₂ : CongruenceSubgroupPair K)
    (hequiv : p₁.IsEquiv p₂) :
    ∃ p : CongruenceSubgroupPair K,
      p.modulus = p₁.modulus.gcd p₂.modulus ∧
      p₁.IsEquiv p ∧ p₂.IsEquiv p := by
  set 𝔪₁ := p₁.modulus
  set 𝔪₂ := p₂.modulus
  set 𝔫 := 𝔪₁.gcd 𝔪₂
  have hcond_p₁ := equiv_gcd_ray_le_left p₁ p₂ hequiv
  obtain ⟨r, hr_mod, hr_equiv₁, hr_amb⟩ :=
    lemma_22_5_sufficiency p₁ 𝔫 (Modulus.gcd_dvd_left 𝔪₁ 𝔪₂) hcond_p₁
  have hp₂_equiv_r : p₂.IsEquiv r := by
    show FracIdealsCoprime_subgroup K p₂.modulus ⊓ r.toAmbientSubgroup =
         FracIdealsCoprime_subgroup K r.modulus ⊓ p₂.toAmbientSubgroup
    rw [hr_mod, hr_amb]
    rw [equiv_sup_ray_gcd_eq p₁ p₂ hequiv]
    have hC₂_le_I₂ : p₂.toAmbientSubgroup ≤ FracIdealsCoprime_subgroup K 𝔪₂ :=
      p₂.toAmbientSubgroup_le
    have hC₂_le_I_n : p₂.toAmbientSubgroup ≤ FracIdealsCoprime_subgroup K 𝔫 :=
      le_trans hC₂_le_I₂ (FracIdealsCoprime_subgroup_mono (Modulus.gcd_dvd_right 𝔪₁ 𝔪₂))
    rw [inf_eq_right.mpr hC₂_le_I_n]
    rw [inf_comm, sup_inf_assoc_of_le _ hC₂_le_I₂, inf_comm]
    rw [sup_eq_left.mpr]
    exact equiv_gcd_ray_le_right p₁ p₂ hequiv
  exact ⟨r, hr_mod, hr_equiv₁, hp₂_equiv_r⟩

end RayClassField
