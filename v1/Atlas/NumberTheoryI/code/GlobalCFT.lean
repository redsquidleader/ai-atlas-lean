/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.RayClassFields
import Atlas.NumberTheoryI.code.Ideles
import Atlas.NumberTheoryI.code.IdeleNorm
import Atlas.NumberTheoryI.code.KroneckerWeber
import Atlas.NumberTheoryI.code.Cor227
import Atlas.NumberTheoryI.code.Chapter3.FiniteApproximation
import Atlas.NumberTheoryI.code.Ch22NormGroup
import Atlas.NumberTheoryI.code.Prop2219
noncomputable section

open NumberField RayClassField Pointwise KroneckerWeber

section ArtinSymbol

universe v

variable (K : Type v) (L : Type v) [Field K] [Field L]
  [NumberField K] [NumberField L]
  [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

def ArtinSymbol
    (𝔔 : Ideal (RingOfIntegers L))
    [𝔔.IsPrime] [Finite (RingOfIntegers L ⧸ 𝔔)] :
    (L ≃ₐ[K] L) :=
  arithFrobAt (RingOfIntegers K) (L ≃ₐ[K] L) 𝔔

theorem ArtinSymbol.isArithFrob
    (𝔔 : Ideal (RingOfIntegers L))
    [𝔔.IsPrime] [Finite (RingOfIntegers L ⧸ 𝔔)] :
    IsArithFrobAt (RingOfIntegers K) (ArtinSymbol K L 𝔔) 𝔔 :=
  IsArithFrobAt.arithFrobAt (RingOfIntegers K) (L ≃ₐ[K] L) 𝔔

end ArtinSymbol

namespace GlobalCFT

universe u

structure IsCongruenceSubgroup (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪)) : Prop where
  contains_ray : RayGroup K 𝔪 ≤ 𝒞


lemma FracIdealsCoprime_subgroup_le (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫) :
    FracIdealsCoprime_subgroup K 𝔫 ≤ FracIdealsCoprime_subgroup K 𝔪 := by
  intro I hI v hv
  apply hI v
  intro h0
  exact absurd (Nat.le_zero.mp (h0 ▸ h (Place.finite v))) hv

noncomputable def FracIdealsCoprime.inclusion (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫) :
    FracIdealsCoprime K 𝔫 →* FracIdealsCoprime K 𝔪 :=
  Subgroup.inclusion (FracIdealsCoprime_subgroup_le K 𝔪 𝔫 h)

lemma IsRayGenerator_inclusion (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫)
    (I : FracIdealsCoprime K 𝔫) (hI : IsRayGenerator 𝔫 I) :
    IsRayGenerator 𝔪 (Subgroup.inclusion (FracIdealsCoprime_subgroup_le K 𝔪 𝔫 h) I) := by
  obtain ⟨α, hprinc, hcong, hsign⟩ := hI
  refine ⟨α, ?_, ?_, ?_⟩
  ·
    simp only [Subgroup.coe_inclusion]
    exact hprinc
  ·
    intro v hv
    have hv_n : 𝔫 (Place.finite v) ≠ 0 := by
      intro h0; exact hv (Nat.eq_zero_of_le_zero (h0 ▸ h (Place.finite v)))
    have hle : (𝔪 (Place.finite v) : ℤ) ≤ (𝔫 (Place.finite v) : ℤ) :=
      Int.ofNat_le.mpr (h (Place.finite v))
    calc v.valuation K ((α : K) - 1)
        ≤ ↑(Multiplicative.ofAdd (-(𝔫 (Place.finite v) : ℤ))) := hcong v hv_n
      _ ≤ ↑(Multiplicative.ofAdd (-(𝔪 (Place.finite v) : ℤ))) := by
          simp only [WithZero.coe_le_coe, Multiplicative.ofAdd_le]
          linarith
  ·
    intro w hw
    exact hsign w (fun h0 => hw (Nat.eq_zero_of_le_zero (h0 ▸ h (Place.infinite w))))

theorem RayGroup.inclusion_le (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫) :
    ∀ x : FracIdealsCoprime K 𝔫,
      x ∈ RayGroup K 𝔫 → (FracIdealsCoprime.inclusion K 𝔪 𝔫 h) x ∈ RayGroup K 𝔪 := by

  intro x hx
  let f := FracIdealsCoprime.inclusion K 𝔪 𝔫 h

  have hmem : f x ∈ Subgroup.map f (RayGroup K 𝔫) := ⟨x, hx, rfl⟩

  rw [show RayGroup K 𝔫 = Subgroup.closure {I | IsRayGenerator 𝔫 I} from rfl,
      MonoidHom.map_closure] at hmem

  have himg_sub : f '' {I | IsRayGenerator 𝔫 I} ⊆ {I | IsRayGenerator 𝔪 I} := by
    rintro _ ⟨I, hI, rfl⟩
    exact IsRayGenerator_inclusion K 𝔪 𝔫 h I hI
  exact Subgroup.closure_mono himg_sub hmem

def CongruenceSubgroupEquiv (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁))
    (𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂)) : Prop :=
  ∃ (𝔫 : Modulus K) (h₁ : Modulus.dvd 𝔪₁ 𝔫) (h₂ : Modulus.dvd 𝔪₂ 𝔫),
    Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₁ 𝔫 h₁) 𝒞₁ =
    Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫 h₂) 𝒞₂

theorem congruenceSubgroupEquiv_refl (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪)) :
    CongruenceSubgroupEquiv K 𝔪 𝔪 𝒞 𝒞 := by
  refine ⟨𝔪, fun v => le_refl _, fun v => le_refl _, rfl⟩

theorem congruenceSubgroupEquiv_symm (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁))
    (𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂))
    (h : CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂) :
    CongruenceSubgroupEquiv K 𝔪₂ 𝔪₁ 𝒞₂ 𝒞₁ := by
  obtain ⟨𝔫, h₁, h₂, heq⟩ := h
  exact ⟨𝔫, h₂, h₁, heq.symm⟩

theorem FracIdealsCoprime.inclusion_comp (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 𝔭 : Modulus K) (h₁ : Modulus.dvd 𝔪 𝔫) (h₂ : Modulus.dvd 𝔫 𝔭)
    (h₃ : Modulus.dvd 𝔪 𝔭) :
    ∀ x : FracIdealsCoprime K 𝔭,
      (FracIdealsCoprime.inclusion K 𝔪 𝔫 h₁)
        ((FracIdealsCoprime.inclusion K 𝔫 𝔭 h₂) x) =
      (FracIdealsCoprime.inclusion K 𝔪 𝔭 h₃) x := by
  intro x
  simp only [FracIdealsCoprime.inclusion, Subgroup.inclusion]
  rfl


theorem FracIdealsCoprime.exists_ray_mul_coprime (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫)
    (x : FracIdealsCoprime K 𝔪) :
    ∃ (r : FracIdealsCoprime K 𝔪),
      r ∈ RayGroup K 𝔪 ∧
      (x * r⁻¹).val ∈ FracIdealsCoprime_subgroup K 𝔫 := by

  have hgcd : 𝔪.gcd 𝔫 = 𝔪 := by
    have hfun : (𝔪.gcd 𝔫).toFun = 𝔪.toFun := by
      funext v; exact Nat.min_eq_left (h v)
    rcases 𝔪 with ⟨f, hf1, hf2, hf3⟩
    rcases 𝔫 with ⟨g, hg1, hg2, hg3⟩
    simp only [Modulus.gcd, Modulus.mk.injEq] at hfun ⊢
    exact hfun

  have hcrt := theorem_8_5_coprime_CRT_core K 𝔪 𝔫
  rw [hgcd] at hcrt


  have hx_mem : x.val ∈ FracIdealsCoprime_subgroup K 𝔪 := x.prop
  have hx_sup := hcrt hx_mem
  rw [Subgroup.mem_sup] at hx_sup
  obtain ⟨y, hy, z, hz, hxyz⟩ := hx_sup
  have hz_ray : z ∈ RayGroup.toAmbientSubgroup K 𝔪 := (Subgroup.mem_inf.mp hz).2
  have hz_cop : z ∈ FracIdealsCoprime_subgroup K 𝔪 := (Subgroup.mem_inf.mp hz).1

  rw [RayGroup.toAmbientSubgroup] at hz_ray
  obtain ⟨r₀, hr₀_ray, hr₀_eq⟩ := Subgroup.mem_map.mp hz_ray


  let r : FracIdealsCoprime K 𝔪 := r₀
  refine ⟨r, hr₀_ray, ?_⟩


  suffices h : (x * r⁻¹).val = y by rw [h]; exact hy
  change x.val * r.val⁻¹ = y
  have : r.val = z := hr₀_eq
  rw [this]

  rw [← hxyz, mul_inv_cancel_right]

theorem FracIdealsCoprime.approx_theorem (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫)
    (x : FracIdealsCoprime K 𝔪) :
    ∃ (y : FracIdealsCoprime K 𝔫) (r : FracIdealsCoprime K 𝔪),
      r ∈ RayGroup K 𝔪 ∧
      x = (FracIdealsCoprime.inclusion K 𝔪 𝔫 h) y * r := by

  obtain ⟨r, hr_ray, hr_coprime⟩ := FracIdealsCoprime.exists_ray_mul_coprime K 𝔪 𝔫 h x

  refine ⟨⟨(x * r⁻¹).val, hr_coprime⟩, r, hr_ray, ?_⟩


  have incl_eq : (FracIdealsCoprime.inclusion K 𝔪 𝔫 h) ⟨(x * r⁻¹).val, hr_coprime⟩ = x * r⁻¹ := by
    apply Subtype.ext
    simp only [FracIdealsCoprime.inclusion]
    rfl
  rw [incl_eq]
  group

theorem FracIdealsCoprime.inclusion_mk_surjective (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫)
    (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    [𝒞.Normal]
    (hCong : IsCongruenceSubgroup K 𝔪 𝒞) :
    Function.Surjective ((QuotientGroup.mk' 𝒞).comp (FracIdealsCoprime.inclusion K 𝔪 𝔫 h)) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective 𝒞 q

  obtain ⟨y, r, hr_ray, hx_eq⟩ := FracIdealsCoprime.approx_theorem K 𝔪 𝔫 h x
  refine ⟨y, ?_⟩
  simp only [MonoidHom.comp_apply]


  rw [hx_eq, map_mul]
  have hr_mem : r ∈ 𝒞 := hCong.contains_ray hr_ray
  have : (QuotientGroup.mk' 𝒞) r = 1 :=
    (QuotientGroup.eq_one_iff r).mpr hr_mem
  rw [this, mul_one]

theorem congruenceSubgroupEquiv_trans (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ 𝔪₃ : Modulus K)
    (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁))
    (𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂))
    (𝒞₃ : Subgroup (FracIdealsCoprime K 𝔪₃))
    (h₁₂ : CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂)
    (h₂₃ : CongruenceSubgroupEquiv K 𝔪₂ 𝔪₃ 𝒞₂ 𝒞₃) :
    CongruenceSubgroupEquiv K 𝔪₁ 𝔪₃ 𝒞₁ 𝒞₃ := by
  obtain ⟨𝔫₁₂, h₁_12, h₂_12, heq₁₂⟩ := h₁₂
  obtain ⟨𝔫₂₃, h₂_23, h₃_23, heq₂₃⟩ := h₂₃

  let 𝔫 := Modulus.lcm 𝔫₁₂ 𝔫₂₃
  have hd₁₂_n : Modulus.dvd 𝔫₁₂ 𝔫 := fun v => le_max_left _ _
  have hd₂₃_n : Modulus.dvd 𝔫₂₃ 𝔫 := fun v => le_max_right _ _
  have hd₁_n : Modulus.dvd 𝔪₁ 𝔫 := fun v => le_trans (h₁_12 v) (hd₁₂_n v)
  have hd₂_n₁ : Modulus.dvd 𝔪₂ 𝔫 := fun v => le_trans (h₂_12 v) (hd₁₂_n v)
  have hd₂_n₂ : Modulus.dvd 𝔪₂ 𝔫 := fun v => le_trans (h₂_23 v) (hd₂₃_n v)
  have hd₃_n : Modulus.dvd 𝔪₃ 𝔫 := fun v => le_trans (h₃_23 v) (hd₂₃_n v)
  refine ⟨𝔫, hd₁_n, hd₃_n, ?_⟩


  ext x
  simp only [Subgroup.mem_comap]
  constructor
  · intro hx₁


    have step1 : (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫₁₂ h₂_12)
        ((FracIdealsCoprime.inclusion K 𝔫₁₂ 𝔫 hd₁₂_n) x) ∈ 𝒞₂ := by
      rw [← Subgroup.mem_comap, ← heq₁₂, Subgroup.mem_comap]
      rw [FracIdealsCoprime.inclusion_comp K 𝔪₁ 𝔫₁₂ 𝔫 h₁_12 hd₁₂_n hd₁_n]
      exact hx₁


    have step1' : (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫 hd₂_n₁) x ∈ 𝒞₂ := by
      rw [← FracIdealsCoprime.inclusion_comp K 𝔪₂ 𝔫₁₂ 𝔫 h₂_12 hd₁₂_n hd₂_n₁]
      exact step1

    have step2 : (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫₂₃ h₂_23)
        ((FracIdealsCoprime.inclusion K 𝔫₂₃ 𝔫 hd₂₃_n) x) ∈ 𝒞₂ := by
      rw [FracIdealsCoprime.inclusion_comp K 𝔪₂ 𝔫₂₃ 𝔫 h₂_23 hd₂₃_n hd₂_n₂]
      exact step1'

    have step3 : (FracIdealsCoprime.inclusion K 𝔪₃ 𝔫₂₃ h₃_23)
        ((FracIdealsCoprime.inclusion K 𝔫₂₃ 𝔫 hd₂₃_n) x) ∈ 𝒞₃ := by
      have : (FracIdealsCoprime.inclusion K 𝔫₂₃ 𝔫 hd₂₃_n) x ∈
          Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫₂₃ h₂_23) 𝒞₂ := by
        rw [Subgroup.mem_comap]; exact step2
      rw [heq₂₃] at this
      exact this

    rw [← FracIdealsCoprime.inclusion_comp K 𝔪₃ 𝔫₂₃ 𝔫 h₃_23 hd₂₃_n hd₃_n]
    exact step3

  · intro hx₃

    have step1 : (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫₂₃ h₂_23)
        ((FracIdealsCoprime.inclusion K 𝔫₂₃ 𝔫 hd₂₃_n) x) ∈ 𝒞₂ := by
      rw [← Subgroup.mem_comap, heq₂₃, Subgroup.mem_comap]
      rw [FracIdealsCoprime.inclusion_comp K 𝔪₃ 𝔫₂₃ 𝔫 h₃_23 hd₂₃_n hd₃_n]
      exact hx₃
    have step1' : (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫 hd₂_n₂) x ∈ 𝒞₂ := by
      rw [← FracIdealsCoprime.inclusion_comp K 𝔪₂ 𝔫₂₃ 𝔫 h₂_23 hd₂₃_n hd₂_n₂]
      exact step1
    have step2 : (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫₁₂ h₂_12)
        ((FracIdealsCoprime.inclusion K 𝔫₁₂ 𝔫 hd₁₂_n) x) ∈ 𝒞₂ := by
      rw [FracIdealsCoprime.inclusion_comp K 𝔪₂ 𝔫₁₂ 𝔫 h₂_12 hd₁₂_n hd₂_n₁]
      exact step1'
    have step3 : (FracIdealsCoprime.inclusion K 𝔪₁ 𝔫₁₂ h₁_12)
        ((FracIdealsCoprime.inclusion K 𝔫₁₂ 𝔫 hd₁₂_n) x) ∈ 𝒞₁ := by
      have : (FracIdealsCoprime.inclusion K 𝔫₁₂ 𝔫 hd₁₂_n) x ∈
          Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫₁₂ h₂_12) 𝒞₂ := by
        rw [Subgroup.mem_comap]; exact step2
      rw [← heq₁₂] at this
      exact this

    rw [← FracIdealsCoprime.inclusion_comp K 𝔪₁ 𝔫₁₂ 𝔫 h₁_12 hd₁₂_n hd₁_n]
    exact step3

noncomputable def proposition_22_4_iso_aux (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁))
    (𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂))
    (hCong₁ : IsCongruenceSubgroup K 𝔪₁ 𝒞₁)
    (hCong₂ : IsCongruenceSubgroup K 𝔪₂ 𝒞₂)
    (𝔫 : Modulus K) (h𝔪₁ : Modulus.dvd 𝔪₁ 𝔫) (h𝔪₂ : Modulus.dvd 𝔪₂ 𝔫)
    (heq : Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₁ 𝔫 h𝔪₁) 𝒞₁ =
           Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫 h𝔪₂) 𝒞₂) :
    FracIdealsCoprime K 𝔪₁ ⧸ 𝒞₁ ≃* FracIdealsCoprime K 𝔪₂ ⧸ 𝒞₂ := by

  let ι₁ := FracIdealsCoprime.inclusion K 𝔪₁ 𝔫 h𝔪₁
  let ι₂ := FracIdealsCoprime.inclusion K 𝔪₂ 𝔫 h𝔪₂

  haveI normal₁ : (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁)).Normal :=
    Subgroup.normal_of_comm 𝒞₁
  haveI normal₂ : (𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂)).Normal :=
    Subgroup.normal_of_comm 𝒞₂

  let f₁ := (QuotientGroup.mk' 𝒞₁).comp ι₁
  let f₂ := (QuotientGroup.mk' 𝒞₂).comp ι₂

  have surj₁ : Function.Surjective f₁ :=
    FracIdealsCoprime.inclusion_mk_surjective K 𝔪₁ 𝔫 h𝔪₁ 𝒞₁ hCong₁
  have surj₂ : Function.Surjective f₂ :=
    FracIdealsCoprime.inclusion_mk_surjective K 𝔪₂ 𝔫 h𝔪₂ 𝒞₂ hCong₂


  have ker_eq₁ : f₁.ker = Subgroup.comap ι₁ 𝒞₁ := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_comap, f₁, MonoidHom.comp_apply]
    exact QuotientGroup.eq_one_iff (ι₁ x)
  have ker_eq₂ : f₂.ker = Subgroup.comap ι₂ 𝒞₂ := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_comap, f₂, MonoidHom.comp_apply]
    exact QuotientGroup.eq_one_iff (ι₂ x)

  have heq_ker : f₁.ker = f₂.ker := by rw [ker_eq₁, ker_eq₂, heq]

  exact (QuotientGroup.quotientKerEquivOfSurjective f₁ surj₁).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq heq_ker).trans
      (QuotientGroup.quotientKerEquivOfSurjective f₂ surj₂))

noncomputable def proposition_22_4_iso (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁))
    (𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂))
    (hCong₁ : IsCongruenceSubgroup K 𝔪₁ 𝒞₁)
    (hCong₂ : IsCongruenceSubgroup K 𝔪₂ 𝒞₂)
    (h : CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂) :
    FracIdealsCoprime K 𝔪₁ ⧸ 𝒞₁ ≃* FracIdealsCoprime K 𝔪₂ ⧸ 𝒞₂ := by
  choose 𝔫 h𝔪₁ h𝔪₂ heq using h
  exact proposition_22_4_iso_aux K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂ hCong₁ hCong₂ 𝔫 h𝔪₁ h𝔪₂ heq

theorem lemma_22_5 (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K) (h_dvd : Modulus.dvd 𝔪₂ 𝔪₁)
    (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁))
    (h_cong : IsCongruenceSubgroup K 𝔪₁ 𝒞₁) :
    (∃ 𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂),
      IsCongruenceSubgroup K 𝔪₂ 𝒞₂ ∧ CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂) ↔


    (∀ x : FracIdealsCoprime K 𝔪₁,
      (FracIdealsCoprime.inclusion K 𝔪₂ 𝔪₁ h_dvd) x ∈ RayGroup K 𝔪₂ →
      x ∈ 𝒞₁) := by
  constructor
  ·
    rintro ⟨𝒞₂, h_cong₂, 𝔫, h_dvd₁, h_dvd₂, h_eq⟩
    intro x hx

    obtain ⟨r, hr_ray, hr_cop⟩ := FracIdealsCoprime.exists_ray_mul_coprime K 𝔪₁ 𝔫 h_dvd₁ x
    set y : FracIdealsCoprime K 𝔪₁ := x * r⁻¹ with hy_def

    set y' : FracIdealsCoprime K 𝔫 := ⟨y.val, hr_cop⟩ with hy'_def
    have hy'_eq : FracIdealsCoprime.inclusion K 𝔪₁ 𝔫 h_dvd₁ y' = y := by
      simp only [FracIdealsCoprime.inclusion, Subgroup.inclusion]; rfl

    have hy'_in₂ : y' ∈ Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫 h_dvd₂) 𝒞₂ := by
      rw [Subgroup.mem_comap]
      have hcomp : FracIdealsCoprime.inclusion K 𝔪₂ 𝔫 h_dvd₂ y' =
          FracIdealsCoprime.inclusion K 𝔪₂ 𝔪₁ h_dvd
            (FracIdealsCoprime.inclusion K 𝔪₁ 𝔫 h_dvd₁ y') := by
        rw [FracIdealsCoprime.inclusion_comp K 𝔪₂ 𝔪₁ 𝔫 h_dvd h_dvd₁ h_dvd₂]
      rw [hcomp, hy'_eq, hy_def, map_mul, map_inv]
      exact 𝒞₂.mul_mem (h_cong₂.contains_ray hx)
        (𝒞₂.inv_mem (h_cong₂.contains_ray (RayGroup.inclusion_le K 𝔪₂ 𝔪₁ h_dvd r hr_ray)))

    have hy'_in₁ : y' ∈ Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₁ 𝔫 h_dvd₁) 𝒞₁ :=
      h_eq ▸ hy'_in₂
    rw [Subgroup.mem_comap] at hy'_in₁
    rw [hy'_eq] at hy'_in₁

    have : x = y * r := by rw [hy_def]; group
    rw [this]
    exact 𝒞₁.mul_mem hy'_in₁ (h_cong.contains_ray hr_ray)
  ·
    intro h_back
    set incl₂₁ := FracIdealsCoprime.inclusion K 𝔪₂ 𝔪₁ h_dvd
    set 𝒞₂ := Subgroup.map incl₂₁ 𝒞₁ ⊔ RayGroup K 𝔪₂ with h𝒞₂_def
    refine ⟨𝒞₂, ⟨le_sup_right⟩, ?_⟩

    refine ⟨𝔪₁, Modulus.dvd_refl 𝔪₁, h_dvd, ?_⟩
    ext x
    simp only [Subgroup.mem_comap]
    have hincl_id : FracIdealsCoprime.inclusion K 𝔪₁ 𝔪₁ (Modulus.dvd_refl 𝔪₁) x = x := by
      simp only [FracIdealsCoprime.inclusion, Subgroup.inclusion]; rfl
    constructor
    ·
      intro hx_in
      rw [hincl_id] at hx_in
      exact (le_sup_left : Subgroup.map incl₂₁ 𝒞₁ ≤ 𝒞₂) (Subgroup.mem_map_of_mem _ hx_in)
    ·
      intro hx_in
      rw [hincl_id]
      rw [h𝒞₂_def] at hx_in
      rw [Subgroup.mem_sup] at hx_in
      obtain ⟨a, ha, b, hb, hab⟩ := hx_in
      obtain ⟨y, hy_in, hy_eq⟩ := Subgroup.mem_map.mp ha


      have hxy_ray : incl₂₁ (x * y⁻¹) ∈ RayGroup K 𝔪₂ := by
        rw [map_mul, map_inv, hy_eq]
        have hab' : incl₂₁ x = a * b := hab.symm
        rw [hab', mul_comm a b, mul_assoc, mul_inv_cancel, mul_one]
        exact hb

      have hxy_in : x * y⁻¹ ∈ 𝒞₁ := h_back _ hxy_ray
      have : x = (x * y⁻¹) * y := by group
      rw [this]
      exact 𝒞₁.mul_mem hxy_in hy_in

lemma FracIdealsCoprime.subtype_inclusion (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫)
    (x : FracIdealsCoprime K 𝔫) :
    (FracIdealsCoprime_subgroup K 𝔪).subtype
      (FracIdealsCoprime.inclusion K 𝔪 𝔫 h x) =
    (FracIdealsCoprime_subgroup K 𝔫).subtype x := by
  simp only [FracIdealsCoprime.inclusion, Subgroup.inclusion]
  rfl

lemma mem_comap_inclusion_iff_mem_toAmbientSubgroup (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (h : Modulus.dvd 𝔪 𝔫)
    (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (x : FracIdealsCoprime K 𝔫) :
    x ∈ Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪 𝔫 h) 𝒞 ↔
    (FracIdealsCoprime_subgroup K 𝔫).subtype x ∈
      𝒞.map (FracIdealsCoprime_subgroup K 𝔪).subtype := by
  rw [Subgroup.mem_comap]
  constructor
  · intro hx
    exact ⟨FracIdealsCoprime.inclusion K 𝔪 𝔫 h x, hx,
      FracIdealsCoprime.subtype_inclusion K 𝔪 𝔫 h x⟩
  · rintro ⟨y, hy, heq⟩
    have hval : FracIdealsCoprime.inclusion K 𝔪 𝔫 h x = y := by
      apply Subtype.ext
      have h1 := FracIdealsCoprime.subtype_inclusion K 𝔪 𝔫 h x
      simp only [Subgroup.coe_subtype] at h1 heq
      exact h1.trans heq.symm
    rw [hval]
    exact hy

theorem isEquiv_to_congruenceSubgroupEquiv (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁))
    (𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂))
    (h₁ : IsCongruenceSubgroup K 𝔪₁ 𝒞₁)
    (h₂ : IsCongruenceSubgroup K 𝔪₂ 𝒞₂)
    (h_isEquiv : (⟨𝔪₁, 𝒞₁, h₁.contains_ray⟩ : CongruenceSubgroupPair K).IsEquiv
                  ⟨𝔪₂, 𝒞₂, h₂.contains_ray⟩) :
    CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂ := by
  set p₁ : CongruenceSubgroupPair K := ⟨𝔪₁, 𝒞₁, h₁.contains_ray⟩
  set p₂ : CongruenceSubgroupPair K := ⟨𝔪₂, 𝒞₂, h₂.contains_ray⟩
  set 𝔫 := Modulus.lcm 𝔪₁ 𝔪₂
  have hdvd₁ : Modulus.dvd 𝔪₁ 𝔫 := RayClassField.Modulus.dvd_lcm_left 𝔪₁ 𝔪₂
  have hdvd₂ : Modulus.dvd 𝔪₂ 𝔫 := RayClassField.Modulus.dvd_lcm_right 𝔪₁ 𝔪₂
  refine ⟨𝔫, hdvd₁, hdvd₂, ?_⟩
  ext x
  rw [mem_comap_inclusion_iff_mem_toAmbientSubgroup K 𝔪₁ 𝔫 hdvd₁ 𝒞₁ x]
  rw [mem_comap_inclusion_iff_mem_toAmbientSubgroup K 𝔪₂ 𝔫 hdvd₂ 𝒞₂ x]
  have hx_in_I₁ : (FracIdealsCoprime_subgroup K 𝔫).subtype x ∈
      FracIdealsCoprime_subgroup K 𝔪₁ :=
    FracIdealsCoprime_subgroup_le K 𝔪₁ 𝔫 hdvd₁ x.2
  have hx_in_I₂ : (FracIdealsCoprime_subgroup K 𝔫).subtype x ∈
      FracIdealsCoprime_subgroup K 𝔪₂ :=
    FracIdealsCoprime_subgroup_le K 𝔪₂ 𝔫 hdvd₂ x.2
  constructor
  · intro hx_amb₁
    have : (FracIdealsCoprime_subgroup K 𝔫).subtype x ∈
        FracIdealsCoprime_subgroup K 𝔪₂ ⊓ p₁.toAmbientSubgroup :=
      ⟨hx_in_I₂, hx_amb₁⟩
    rw [← h_isEquiv] at this
    exact this.2
  · intro hx_amb₂
    have : (FracIdealsCoprime_subgroup K 𝔫).subtype x ∈
        FracIdealsCoprime_subgroup K 𝔪₁ ⊓ p₂.toAmbientSubgroup :=
      ⟨hx_in_I₁, hx_amb₂⟩
    rw [h_isEquiv] at this
    exact this.2

theorem isEquiv_of_dvd_comap (K : Type u) [Field K] [NumberField K]
    (𝔪 𝔫 : Modulus K) (hdvd : Modulus.dvd 𝔪 𝔫)
    (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (𝒞_𝔫 : Subgroup (FracIdealsCoprime K 𝔫))
    (h_cong_𝔫 : IsCongruenceSubgroup K 𝔫 𝒞_𝔫)
    (h_eq : 𝒞_𝔫 = Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪 𝔫 hdvd) 𝒞) :
    (⟨𝔪, 𝒞, h_cong.contains_ray⟩ : CongruenceSubgroupPair K).IsEquiv
      ⟨𝔫, 𝒞_𝔫, h_cong_𝔫.contains_ray⟩ := by


  show FracIdealsCoprime_subgroup K 𝔪 ⊓
      (𝒞_𝔫.map (FracIdealsCoprime_subgroup K 𝔫).subtype) =
    FracIdealsCoprime_subgroup K 𝔫 ⊓
      (𝒞.map (FracIdealsCoprime_subgroup K 𝔪).subtype)
  ext a
  simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.coe_subtype]
  constructor
  ·
    rintro ⟨ha_cop_m, z, hz_in, hz_eq⟩
    constructor
    · rw [← hz_eq]; exact z.2
    ·
      have hz_comap : FracIdealsCoprime.inclusion K 𝔪 𝔫 hdvd z ∈ 𝒞 := by
        have : z ∈ Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪 𝔫 hdvd) 𝒞 :=
          h_eq ▸ hz_in
        exact Subgroup.mem_comap.mp this
      exact ⟨FracIdealsCoprime.inclusion K 𝔪 𝔫 hdvd z, hz_comap, by
        have := FracIdealsCoprime.subtype_inclusion K 𝔪 𝔫 hdvd z
        simp only [Subgroup.coe_subtype] at this hz_eq ⊢
        exact this.symm.trans hz_eq⟩
  ·
    rintro ⟨ha_cop_n, c, hc_in, hc_eq⟩
    refine ⟨?_, ?_⟩
    ·
      rw [← hc_eq]; exact c.2
    ·
      refine ⟨⟨a, ha_cop_n⟩, ?_, rfl⟩

      rw [h_eq]

      have hval : FracIdealsCoprime.inclusion K 𝔪 𝔫 hdvd ⟨a, ha_cop_n⟩ = c := by
        apply Subtype.ext
        have h1 := FracIdealsCoprime.subtype_inclusion K 𝔪 𝔫 hdvd (⟨a, ha_cop_n⟩ : FracIdealsCoprime K 𝔫)
        simp only [Subgroup.coe_subtype] at h1 hc_eq
        exact h1.trans hc_eq.symm
      exact Subgroup.mem_comap.mpr (hval ▸ hc_in)

theorem congruenceSubgroupEquiv_to_isEquiv (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁))
    (𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂))
    (h₁ : IsCongruenceSubgroup K 𝔪₁ 𝒞₁)
    (h₂ : IsCongruenceSubgroup K 𝔪₂ 𝒞₂)
    (h_equiv : CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂) :
    (⟨𝔪₁, 𝒞₁, h₁.contains_ray⟩ : CongruenceSubgroupPair K).IsEquiv
      ⟨𝔪₂, 𝒞₂, h₂.contains_ray⟩ := by
  obtain ⟨𝔫, hdvd₁, hdvd₂, h_comap_eq⟩ := h_equiv
  set p₁ : CongruenceSubgroupPair K := ⟨𝔪₁, 𝒞₁, h₁.contains_ray⟩
  set p₂ : CongruenceSubgroupPair K := ⟨𝔪₂, 𝒞₂, h₂.contains_ray⟩

  set 𝒞_𝔫 := Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₁ 𝔫 hdvd₁) 𝒞₁

  have h_cong_𝔫 : IsCongruenceSubgroup K 𝔫 𝒞_𝔫 := by
    constructor
    intro z hz
    rw [Subgroup.mem_comap]
    exact h₁.contains_ray (RayGroup.inclusion_le K 𝔪₁ 𝔫 hdvd₁ z hz)
  set p_𝔫 : CongruenceSubgroupPair K := ⟨𝔫, 𝒞_𝔫, h_cong_𝔫.contains_ray⟩

  have h_equiv₁ : p₁.IsEquiv p_𝔫 :=
    isEquiv_of_dvd_comap K 𝔪₁ 𝔫 hdvd₁ 𝒞₁ h₁ 𝒞_𝔫 h_cong_𝔫 rfl

  have h_eq₂ : 𝒞_𝔫 = Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪₂ 𝔫 hdvd₂) 𝒞₂ :=
    h_comap_eq

  have h_equiv₂ : p₂.IsEquiv p_𝔫 :=
    isEquiv_of_dvd_comap K 𝔪₂ 𝔫 hdvd₂ 𝒞₂ h₂ 𝒞_𝔫 h_cong_𝔫 h_eq₂


  exact h_equiv₁.trans' h_equiv₂.symm'

theorem proposition_22_6 (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K)
    (𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁))
    (𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂))
    (h₁ : IsCongruenceSubgroup K 𝔪₁ 𝒞₁)
    (h₂ : IsCongruenceSubgroup K 𝔪₂ 𝒞₂)
    (h_equiv : CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂) :
    ∃ 𝒞 : Subgroup (FracIdealsCoprime K (Modulus.gcd 𝔪₁ 𝔪₂)),
      IsCongruenceSubgroup K (Modulus.gcd 𝔪₁ 𝔪₂) 𝒞 ∧
      CongruenceSubgroupEquiv K 𝔪₁ (Modulus.gcd 𝔪₁ 𝔪₂) 𝒞₁ 𝒞 ∧
      CongruenceSubgroupEquiv K 𝔪₂ (Modulus.gcd 𝔪₁ 𝔪₂) 𝒞₂ 𝒞 := by

  set p₁ : CongruenceSubgroupPair K := ⟨𝔪₁, 𝒞₁, h₁.contains_ray⟩
  set p₂ : CongruenceSubgroupPair K := ⟨𝔪₂, 𝒞₂, h₂.contains_ray⟩
  have h_isEquiv : p₁.IsEquiv p₂ :=
    congruenceSubgroupEquiv_to_isEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂ h₁ h₂ h_equiv

  obtain ⟨⟨p_mod, p_sub, p_ray⟩, hp_mod, hp_equiv₁, hp_equiv₂⟩ :=
    RayClassField.proposition_22_6 p₁ p₂ h_isEquiv

  simp only [CongruenceSubgroupPair.modulus] at hp_mod
  subst hp_mod

  have h_cong : IsCongruenceSubgroup K (Modulus.gcd 𝔪₁ 𝔪₂) p_sub := by
    constructor; exact p_ray
  refine ⟨p_sub, h_cong, ?_, ?_⟩
  · exact isEquiv_to_congruenceSubgroupEquiv K 𝔪₁ (Modulus.gcd 𝔪₁ 𝔪₂) 𝒞₁ p_sub h₁ h_cong
      hp_equiv₁
  · exact isEquiv_to_congruenceSubgroupEquiv K 𝔪₂ (Modulus.gcd 𝔪₁ 𝔪₂) 𝒞₂ p_sub h₂ h_cong
      hp_equiv₂

theorem equiv_moduli_closed_under_gcd (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (𝔪₁ 𝔪₂ : Modulus K)
    (h₁ : ∃ 𝒞₁ : Subgroup (FracIdealsCoprime K 𝔪₁),
      IsCongruenceSubgroup K 𝔪₁ 𝒞₁ ∧ CongruenceSubgroupEquiv K 𝔪 𝔪₁ 𝒞 𝒞₁)
    (h₂ : ∃ 𝒞₂ : Subgroup (FracIdealsCoprime K 𝔪₂),
      IsCongruenceSubgroup K 𝔪₂ 𝒞₂ ∧ CongruenceSubgroupEquiv K 𝔪 𝔪₂ 𝒞 𝒞₂) :
    ∃ 𝒞g : Subgroup (FracIdealsCoprime K (Modulus.gcd 𝔪₁ 𝔪₂)),
      IsCongruenceSubgroup K (Modulus.gcd 𝔪₁ 𝔪₂) 𝒞g ∧
      CongruenceSubgroupEquiv K 𝔪 (Modulus.gcd 𝔪₁ 𝔪₂) 𝒞 𝒞g := by
  obtain ⟨𝒞₁, hc₁, he₁⟩ := h₁
  obtain ⟨𝒞₂, hc₂, he₂⟩ := h₂

  have h_equiv₁₂ : CongruenceSubgroupEquiv K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂ :=
    congruenceSubgroupEquiv_trans K 𝔪₁ 𝔪 𝔪₂ 𝒞₁ 𝒞 𝒞₂
      (congruenceSubgroupEquiv_symm K 𝔪 𝔪₁ 𝒞 𝒞₁ he₁) he₂
  obtain ⟨𝒞g, hcg, heg₁, heg₂⟩ := proposition_22_6 K 𝔪₁ 𝔪₂ 𝒞₁ 𝒞₂ hc₁ hc₂ h_equiv₁₂
  exact ⟨𝒞g, hcg, congruenceSubgroupEquiv_trans K 𝔪 𝔪₁ (Modulus.gcd 𝔪₁ 𝔪₂) 𝒞 𝒞₁ 𝒞g he₁ heg₁⟩

lemma gcd_weight_lt_of_not_dvd {K : Type u} [Field K] [NumberField K]
    {𝔪₁ 𝔪₂ : Modulus K} (h : ¬ 𝔪₁.dvd 𝔪₂) :
    (𝔪₁.gcd 𝔪₂).weight < 𝔪₁.weight := by
  simp only [Modulus.dvd, not_forall, not_le] at h
  obtain ⟨v₀, hv₀⟩ := h
  have hgcd_v₀ : (𝔪₁.gcd 𝔪₂).toFun v₀ < 𝔪₁.toFun v₀ := by
    simp only [Modulus.gcd]
    exact lt_of_le_of_lt (min_le_right _ _) hv₀
  have hgcd_le : ∀ v, (𝔪₁.gcd 𝔪₂).toFun v ≤ 𝔪₁.toFun v := fun v => by
    simp only [Modulus.gcd]; exact min_le_left _ _
  have hv₀_supp : v₀ ∈ 𝔪₁.finite_support.toFinset := by
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    omega
  have hsub : (𝔪₁.gcd 𝔪₂).finite_support.toFinset ⊆ 𝔪₁.finite_support.toFinset := by
    intro v hv
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hv ⊢
    intro heq
    exact hv (by simp only [Modulus.gcd]; omega)
  unfold Modulus.weight
  calc (𝔪₁.gcd 𝔪₂).finite_support.toFinset.sum (𝔪₁.gcd 𝔪₂).toFun
      ≤ 𝔪₁.finite_support.toFinset.sum (𝔪₁.gcd 𝔪₂).toFun := by
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
    _ < 𝔪₁.finite_support.toFinset.sum 𝔪₁.toFun := by
        exact Finset.sum_lt_sum (fun v _ => hgcd_le v) ⟨v₀, hv₀_supp, hgcd_v₀⟩

theorem exists_minimal_equiv_modulus (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞) :
    ∃ (𝔠 : Modulus K),
      (∃ 𝒞₀ : Subgroup (FracIdealsCoprime K 𝔠),
        IsCongruenceSubgroup K 𝔠 𝒞₀ ∧ CongruenceSubgroupEquiv K 𝔪 𝔠 𝒞 𝒞₀) ∧
      ∀ (𝔫 : Modulus K),
        (∃ 𝒟 : Subgroup (FracIdealsCoprime K 𝔫),
          IsCongruenceSubgroup K 𝔫 𝒟 ∧ CongruenceSubgroupEquiv K 𝔪 𝔫 𝒞 𝒟) →
        Modulus.dvd 𝔠 𝔫 := by


  suffices h : ∀ (n : ℕ) (𝔪' : Modulus K) (𝒞' : Subgroup (FracIdealsCoprime K 𝔪')),
      IsCongruenceSubgroup K 𝔪' 𝒞' →
      CongruenceSubgroupEquiv K 𝔪 𝔪' 𝒞 𝒞' →
      𝔪'.weight = n →
      ∃ (𝔠 : Modulus K),
        (∃ 𝒞₀ : Subgroup (FracIdealsCoprime K 𝔠),
          IsCongruenceSubgroup K 𝔠 𝒞₀ ∧ CongruenceSubgroupEquiv K 𝔪 𝔠 𝒞 𝒞₀) ∧
        ∀ (𝔫 : Modulus K),
          (∃ 𝒟 : Subgroup (FracIdealsCoprime K 𝔫),
            IsCongruenceSubgroup K 𝔫 𝒟 ∧ CongruenceSubgroupEquiv K 𝔪 𝔫 𝒞 𝒟) →
          Modulus.dvd 𝔠 𝔫 from
    h 𝔪.weight 𝔪 𝒞 h_cong (congruenceSubgroupEquiv_refl K 𝔪 𝒞) rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro 𝔪' 𝒞' h_cong' h_equiv' h_wt

  by_cases hmin : ∀ (𝔫 : Modulus K),
      (∃ 𝒟 : Subgroup (FracIdealsCoprime K 𝔫),
        IsCongruenceSubgroup K 𝔫 𝒟 ∧ CongruenceSubgroupEquiv K 𝔪 𝔫 𝒞 𝒟) →
      Modulus.dvd 𝔪' 𝔫
  ·
    exact ⟨𝔪', ⟨⟨𝒞', h_cong', h_equiv'⟩, hmin⟩⟩
  ·
    push Not at hmin

    obtain ⟨𝔫, ⟨𝒟, h_congD, h_equivD⟩, hndvd⟩ := hmin

    obtain ⟨𝒞g, h_congG, h_equivG⟩ :=
      equiv_moduli_closed_under_gcd K 𝔪 𝒞 𝔪' 𝔫
        ⟨𝒞', h_cong', h_equiv'⟩ ⟨𝒟, h_congD, h_equivD⟩

    have h_wt_lt : (Modulus.gcd 𝔪' 𝔫).weight < n := by
      rw [← h_wt]
      exact gcd_weight_lt_of_not_dvd hndvd

    exact ih (Modulus.gcd 𝔪' 𝔫).weight h_wt_lt
      (Modulus.gcd 𝔪' 𝔫) 𝒞g h_congG h_equivG rfl

theorem corollary_22_7 (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞) :
    ∃! (𝔠 : Modulus K),
      (∃ 𝒞₀ : Subgroup (FracIdealsCoprime K 𝔠),
        IsCongruenceSubgroup K 𝔠 𝒞₀ ∧ CongruenceSubgroupEquiv K 𝔪 𝔠 𝒞 𝒞₀) ∧
      ∀ (𝔫 : Modulus K),
        (∃ 𝒟 : Subgroup (FracIdealsCoprime K 𝔫),
          IsCongruenceSubgroup K 𝔫 𝒟 ∧ CongruenceSubgroupEquiv K 𝔪 𝔫 𝒞 𝒟) →
        Modulus.dvd 𝔠 𝔫 := by

  obtain ⟨𝔠, ⟨h_exist, h_dvd⟩⟩ := exists_minimal_equiv_modulus K 𝔪 𝒞 h_cong
  refine ⟨𝔠, ⟨h_exist, h_dvd⟩, ?_⟩

  intro 𝔠' ⟨h_exist', h_dvd'⟩

  have h1 : Modulus.dvd 𝔠 𝔠' := h_dvd 𝔠' h_exist'
  have h2 : Modulus.dvd 𝔠' 𝔠 := h_dvd' 𝔠 h_exist
  have htf : 𝔠'.toFun = 𝔠.toFun := funext (fun v => le_antisymm (h2 v) (h1 v))
  rcases 𝔠 with ⟨f₁, hs₁, hi₁, hc₁⟩
  rcases 𝔠' with ⟨f₂, hs₂, hi₂, hc₂⟩
  congr 1

noncomputable def conductorOfCongruenceSubgroup (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞) : Modulus K :=
  (corollary_22_7 K 𝔪 𝒞 h_cong).choose

def IsPrimitive (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞) : Prop :=
  conductorOfCongruenceSubgroup K 𝔪 𝒞 h_cong = 𝔪

abbrev RayClassCharacter (K : Type u) [Field K] [NumberField K] (𝔪 : Modulus K) : Type u :=
  RayClassGroup K 𝔪 →* ℂˣ

def RayClassGroup.mapOfDvd {K : Type u} [Field K] [NumberField K]
    {𝔪₁ 𝔪₂ : Modulus K} (h : Modulus.dvd 𝔪₁ 𝔪₂) :
    RayClassGroup K 𝔪₂ →* RayClassGroup K 𝔪₁ :=
  QuotientGroup.map (RayGroup K 𝔪₂) (RayGroup K 𝔪₁)
    (FracIdealsCoprime.inclusion K 𝔪₁ 𝔪₂ h)
    (fun x hx => RayGroup.inclusion_le K 𝔪₁ 𝔪₂ h x hx)

def IsInducedBy (K : Type u) [Field K] [NumberField K]
    (𝔪₁ 𝔪₂ : Modulus K) (h : Modulus.dvd 𝔪₁ 𝔪₂)
    (χ₁ : RayClassCharacter K 𝔪₁) (χ₂ : RayClassCharacter K 𝔪₂) : Prop :=
  χ₂ = χ₁.comp (RayClassGroup.mapOfDvd h)

def kernelCongruenceSubgroup (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (χ : RayClassCharacter K 𝔪) : Subgroup (FracIdealsCoprime K 𝔪) :=
  Subgroup.comap (QuotientGroup.mk' (RayGroup K 𝔪)) (MonoidHom.ker χ)

theorem kernelCongruenceSubgroup_isCong (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (χ : RayClassCharacter K 𝔪) :
    IsCongruenceSubgroup K 𝔪 (kernelCongruenceSubgroup K 𝔪 χ) := by
  refine ⟨fun x hx => ?_⟩
  show x ∈ kernelCongruenceSubgroup K 𝔪 χ
  unfold kernelCongruenceSubgroup
  simp only [Subgroup.mem_comap]
  have hq : (QuotientGroup.mk' (RayGroup K 𝔪)) x = 1 :=
    (QuotientGroup.eq_one_iff x).mpr hx
  rw [hq]
  exact (MonoidHom.ker χ).one_mem

noncomputable def conductorOfRayClassCharacter (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (χ : RayClassCharacter K 𝔪) : Modulus K :=
  conductorOfCongruenceSubgroup K 𝔪 (kernelCongruenceSubgroup K 𝔪 χ)
    (kernelCongruenceSubgroup_isCong K 𝔪 χ)

theorem conductorOfRayClassCharacter_dvd (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (χ : RayClassCharacter K 𝔪) :
    Modulus.dvd (conductorOfRayClassCharacter K 𝔪 χ) 𝔪 := by
  unfold conductorOfRayClassCharacter conductorOfCongruenceSubgroup
  have h := (corollary_22_7 K 𝔪 (kernelCongruenceSubgroup K 𝔪 χ)
    (kernelCongruenceSubgroup_isCong K 𝔪 χ)).choose_spec.1.2
  exact h 𝔪 ⟨kernelCongruenceSubgroup K 𝔪 χ, kernelCongruenceSubgroup_isCong K 𝔪 χ,
    congruenceSubgroupEquiv_refl K 𝔪 _⟩

def IsRayClassCharacterPrincipal (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (χ : RayClassCharacter K 𝔪) : Prop :=
  χ = 1

noncomputable def WeberLFunction (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (χ : RayClassCharacter K 𝔪) : ℂ → ℂ :=
  RayClassField.WeberLFunction_ext χ

noncomputable def rayClassHolomorphicPart (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (γ : RayClassGroup K 𝔪) : ℂ → ℂ :=
  RayClassField.rayClassPartialZeta_regularPart γ

noncomputable def PrimeToFracIdealsCoprime (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝔭 : Prime' K) (h_coprime : 𝔪 (Place.finite 𝔭) = 0) :
    FracIdealsCoprime K 𝔪 := primeCoprime K 𝔪 𝔭 h_coprime

def primesInCongruenceSubgroup (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪)) :
    Set (Prime' K) :=
  {𝔭 : Prime' K | ∃ (h : 𝔪 (Place.finite 𝔭) = 0),
    PrimeToFracIdealsCoprime K 𝔪 𝔭 h ∈ 𝒞}

noncomputable def PrimitiveCharsContaining (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪)) : Type u :=
  (FracIdealsCoprime K 𝔪 ⧸ 𝒞) →* ℂˣ

lemma IsCongruenceSubgroup.finiteIndex {K : Type u} [Field K] [NumberField K]
    {𝔪 : Modulus K} {𝒞 : Subgroup (FracIdealsCoprime K 𝔪)}
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞) : 𝒞.FiniteIndex := by
  haveI : Finite (FracIdealsCoprime K 𝔪 ⧸ RayGroup K 𝔪) :=
    inferInstanceAs (Finite (RayClassGroup K 𝔪))
  haveI : (RayGroup K 𝔪).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.finiteIndex_of_le h_cong.contains_ray

noncomputable instance instFintypePrimitiveCharsContaining (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    [𝒞.FiniteIndex] :
    Fintype (PrimitiveCharsContaining K 𝔪 𝒞) := by
  unfold PrimitiveCharsContaining
  haveI : Finite (FracIdealsCoprime K 𝔪 ⧸ 𝒞) := Subgroup.finite_quotient_of_finiteIndex

  exact Fintype.ofFinite _

noncomputable def toRayClassCharOfPrimitive (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (χ : PrimitiveCharsContaining K 𝔪 𝒞) : RayClassCharacter K 𝔪 := by
  classical


  by_cases h : RayGroup K 𝔪 ≤ 𝒞
  · exact χ.comp (QuotientGroup.map (RayGroup K 𝔪) 𝒞 (MonoidHom.id _) (fun _ hx => h hx))
  · exact 1

opaque orderOfVanishingPrimitive (_K : Type u) [Field _K] [NumberField _K]
    (_𝔪 : Modulus _K) (_𝒞 : Subgroup (FracIdealsCoprime _K _𝔪))
    (_χ : PrimitiveCharsContaining _K _𝔪 _𝒞) : ℕ

def isPrincipalPrimitive (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (χ : PrimitiveCharsContaining K 𝔪 𝒞) : Prop :=
  IsRayClassCharacterPrincipal K 𝔪 (toRayClassCharOfPrimitive K 𝔪 𝒞 χ)

instance instDecidableIsPrincipalPrimitive (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (χ : PrimitiveCharsContaining K 𝔪 𝒞) :
    Decidable (isPrincipalPrimitive K 𝔪 𝒞 χ) := by
  unfold isPrincipalPrimitive IsRayClassCharacterPrincipal
  exact Classical.dec _

def AllLValuesNonzero (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪)) : Prop :=
  ∀ χ : PrimitiveCharsContaining K 𝔪 𝒞,
    ¬isPrincipalPrimitive K 𝔪 𝒞 χ → orderOfVanishingPrimitive K 𝔪 𝒞 χ = 0

noncomputable def dirichletDensityCongruence (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (_h_cong : IsCongruenceSubgroup K 𝔪 𝒞) : ℚ :=
  haveI := _h_cong.finiteIndex

  (1 - (↑(∑ χ : PrimitiveCharsContaining K 𝔪 𝒞,
    if isPrincipalPrimitive K 𝔪 𝒞 χ then 0
    else orderOfVanishingPrimitive K 𝔪 𝒞 χ) : ℚ)) / (𝒞.index : ℚ)

noncomputable def dirichletDensityCoset (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (I : FracIdealsCoprime K 𝔪) : ℚ :=
  (DirichletDensity K {𝔭 : Prime' K | ∃ (h : 𝔪 (Place.finite 𝔭) = 0),
    (QuotientGroup.mk (s := 𝒞) (PrimeToFracIdealsCoprime K 𝔪 𝔭 h) :
      FracIdealsCoprime K 𝔪 ⧸ 𝒞) = QuotientGroup.mk I}).getD 0

theorem congruenceSubgroup_index_pos (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞) :
    0 < 𝒞.index := by
  haveI : Finite (FracIdealsCoprime K 𝔪 ⧸ RayGroup K 𝔪) :=
    inferInstanceAs (Finite (RayClassGroup K 𝔪))
  haveI : (RayGroup K 𝔪).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  haveI : 𝒞.FiniteIndex := Subgroup.finiteIndex_of_le h_cong.contains_ray
  exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero

theorem coset_nthPower_meromorphicOrder_eq (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (I : FracIdealsCoprime K 𝔪) [𝒞.FiniteIndex] :
    let S := {𝔭 : Prime' K | ∃ (h : 𝔪 (Place.finite 𝔭) = 0),
      (QuotientGroup.mk (s := 𝒞) (PrimeToFracIdealsCoprime K 𝔪 𝔭 h) :
        FracIdealsCoprime K 𝔪 ⧸ 𝒞) = QuotientGroup.mk I}
    let E := ∑ χ : PrimitiveCharsContaining K 𝔪 𝒞,
      if isPrincipalPrimitive K 𝔪 𝒞 χ then 0
      else orderOfVanishingPrimitive K 𝔪 𝒞 χ
    meromorphicOrderAt (partialDedekindZeta K S ^ 𝒞.index) 1 =
      ↑(-(1 - ↑E : ℤ)) := by sorry

theorem coset_nthPower_poleOrder (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (I : FracIdealsCoprime K 𝔪) [𝒞.FiniteIndex] :

    let S := {𝔭 : Prime' K | ∃ (h : 𝔪 (Place.finite 𝔭) = 0),

      (QuotientGroup.mk (s := 𝒞) (PrimeToFracIdealsCoprime K 𝔪 𝔭 h) :
        FracIdealsCoprime K 𝔪 ⧸ 𝒞) = QuotientGroup.mk I}
    let E := ∑ χ : PrimitiveCharsContaining K 𝔪 𝒞,
      if isPrincipalPrimitive K 𝔪 𝒞 χ then 0
      else orderOfVanishingPrimitive K 𝔪 𝒞 χ
    HasMeromorphicContinuationWithPoleOrder
      (partialDedekindZeta K S ^ 𝒞.index)
      ((1 : ℤ) - ↑E) := by
  intro S E
  exact ⟨(partialDedekindZeta_meromorphicAt S).pow _,
    coset_nthPower_meromorphicOrder_eq K 𝔪 𝒞 h_cong I⟩

lemma hasPolarDensity_coset (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (I : FracIdealsCoprime K 𝔪) :
    HasPolarDensity K {𝔭 : Prime' K | ∃ (h : 𝔪 (Place.finite 𝔭) = 0),
      (QuotientGroup.mk (s := 𝒞) (PrimeToFracIdealsCoprime K 𝔪 𝔭 h) :
        FracIdealsCoprime K 𝔪 ⧸ 𝒞) = QuotientGroup.mk I}
      (dirichletDensityCongruence K 𝔪 𝒞 h_cong) := by
  haveI := h_cong.finiteIndex


  have h_pos := congruenceSubgroup_index_pos K 𝔪 𝒞 h_cong

  have h_mer := coset_nthPower_poleOrder K 𝔪 𝒞 h_cong I

  set E := ∑ χ : PrimitiveCharsContaining K 𝔪 𝒞,
    if isPrincipalPrimitive K 𝔪 𝒞 χ then 0
    else orderOfVanishingPrimitive K 𝔪 𝒞 χ
  set m : ℤ := (1 : ℤ) - ↑E
  refine ⟨⟨𝒞.index, h_pos⟩, m, h_mer, ?_⟩

  show dirichletDensityCongruence K 𝔪 𝒞 h_cong = (↑m : ℚ) / (↑(↑(⟨𝒞.index, h_pos⟩ : ℕ+) : ℕ) : ℚ)
  have hpn : (↑(↑(⟨𝒞.index, h_pos⟩ : ℕ+) : ℕ) : ℚ) = (↑𝒞.index : ℚ) := by simp
  rw [hpn]
  unfold dirichletDensityCongruence
  congr 1
  simp only [m, E]
  push_cast
  ring

theorem dirichletDensityCongruence_nonneg (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞) :
    0 ≤ dirichletDensityCongruence K 𝔪 𝒞 h_cong :=
  polar_density_nonneg _ _ (polarDensity_eq_some_iff.mpr (hasPolarDensity_coset K 𝔪 𝒞 h_cong 1))

theorem theorem_22_20 (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (n : ℕ) (hn : 𝒞.index = n) (hn_pos : 0 < n) :
    (AllLValuesNonzero K 𝔪 𝒞 →
      dirichletDensityCongruence K 𝔪 𝒞 h_cong = 1 / (n : ℚ)) ∧
    (¬ AllLValuesNonzero K 𝔪 𝒞 →
      dirichletDensityCongruence K 𝔪 𝒞 h_cong = 0) := by
  haveI := h_cong.finiteIndex

  set E := ∑ χ : PrimitiveCharsContaining K 𝔪 𝒞,
    if isPrincipalPrimitive K 𝔪 𝒞 χ then 0
    else orderOfVanishingPrimitive K 𝔪 𝒞 χ with hE_def

  have h_formula : dirichletDensityCongruence K 𝔪 𝒞 h_cong =
      (1 - (↑E : ℚ)) / (n : ℚ) := by
    unfold dirichletDensityCongruence
    rw [hn]

  have h_equiv : AllLValuesNonzero K 𝔪 𝒞 ↔ E = 0 := by
    unfold AllLValuesNonzero
    constructor
    · intro h
      apply Finset.sum_eq_zero
      intro χ _
      split_ifs with hp
      · rfl
      · exact h χ hp
    · intro h χ hχ
      rw [hE_def] at h
      have h_all_zero := Finset.sum_eq_zero_iff.mp h χ (Finset.mem_univ χ)
      simp only [hχ, ↓reduceIte] at h_all_zero
      exact h_all_zero

  have h_nonneg := dirichletDensityCongruence_nonneg K 𝔪 𝒞 h_cong
  rw [h_formula] at h_nonneg
  have hn_pos_rat : (0 : ℚ) < (n : ℚ) := Nat.cast_pos.mpr hn_pos
  have h_num_nonneg : 0 ≤ 1 - (↑E : ℚ) := by
    rwa [le_div_iff₀ hn_pos_rat, zero_mul] at h_nonneg
  have hE_le : E ≤ 1 := by
    have : (↑E : ℚ) ≤ 1 := by linarith
    exact_mod_cast this

  constructor
  ·
    intro h_all
    rw [h_equiv] at h_all

    rw [h_formula, h_all]
    simp
  ·
    intro h_not_all
    rw [h_equiv] at h_not_all

    have hE_eq : E = 1 := by omega
    rw [h_formula, hE_eq]
    simp

lemma hasDirichletDensity_coset (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (I : FracIdealsCoprime K 𝔪) :
    HasDirichletDensity K {𝔭 : Prime' K | ∃ (h : 𝔪 (Place.finite 𝔭) = 0),
      (QuotientGroup.mk (s := 𝒞) (PrimeToFracIdealsCoprime K 𝔪 𝔭 h) :
        FracIdealsCoprime K 𝔪 ⧸ 𝒞) = QuotientGroup.mk I}
      (dirichletDensityCongruence K 𝔪 𝒞 h_cong) :=
  polar_implies_dirichlet (hasPolarDensity_coset K 𝔪 𝒞 h_cong I)

lemma dirichletDensity_coset_eq_some (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (I : FracIdealsCoprime K 𝔪) :
    DirichletDensity K {𝔭 : Prime' K | ∃ (h : 𝔪 (Place.finite 𝔭) = 0),
      (QuotientGroup.mk (s := 𝒞) (PrimeToFracIdealsCoprime K 𝔪 𝔭 h) :
        FracIdealsCoprime K 𝔪 ⧸ 𝒞) = QuotientGroup.mk I} =
      some (dirichletDensityCongruence K 𝔪 𝒞 h_cong) :=
  dirichletDensity_eq_some_iff.mpr (hasDirichletDensity_coset K 𝔪 𝒞 h_cong I)

theorem characterOrthogonality_coset_density (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (I : FracIdealsCoprime K 𝔪) :
    dirichletDensityCoset K 𝔪 𝒞 h_cong I =
      dirichletDensityCongruence K 𝔪 𝒞 h_cong := by
  unfold dirichletDensityCoset
  rw [dirichletDensity_coset_eq_some K 𝔪 𝒞 h_cong I]
  simp [Option.getD]

lemma dirichletDensityCoset_eq_congruence (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (I : FracIdealsCoprime K 𝔪) :
    dirichletDensityCoset K 𝔪 𝒞 h_cong I =
      dirichletDensityCongruence K 𝔪 𝒞 h_cong :=
  characterOrthogonality_coset_density K 𝔪 𝒞 h_cong I

theorem proposition_22_21 (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (n : ℕ) (hn : 𝒞.index = n) (hn_pos : 0 < n)
    (I : FracIdealsCoprime K 𝔪) :
    (AllLValuesNonzero K 𝔪 𝒞 →
      dirichletDensityCoset K 𝔪 𝒞 h_cong I = 1 / (n : ℚ)) ∧
    (¬ AllLValuesNonzero K 𝔪 𝒞 →
      dirichletDensityCoset K 𝔪 𝒞 h_cong I = 0) := by

  have h_eq := dirichletDensityCoset_eq_congruence K 𝔪 𝒞 h_cong I

  have h_thm := theorem_22_20 K 𝔪 𝒞 h_cong n hn hn_pos
  constructor
  · intro hL
    rw [h_eq]
    exact h_thm.1 hL
  · intro hL
    rw [h_eq]
    exact h_thm.2 hL

theorem dirichletDensity_coprime_primes_eq_one (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (_h_cong : IsCongruenceSubgroup K 𝔪 𝒞) :
    DirichletDensity K {𝔭 : Prime' K | ∃ (_ : 𝔪 (Place.finite 𝔭) = 0), True} = some 1 := by


  have h_cofin : (Set.univ \ {𝔭 : Prime' K | ∃ (_ : 𝔪 (Place.finite 𝔭) = 0), True}).Finite := by
    apply Set.Finite.subset (modulus_support_finite K 𝔪)
    intro 𝔭 h𝔭
    simp only [Set.mem_diff, Set.mem_univ, Set.mem_setOf_eq, true_and] at h𝔭
    simp only [Set.mem_setOf_eq]
    intro h_eq
    exact h𝔭 ⟨h_eq, trivial⟩

  have h_polar := proposition_21_14a_cofinite
    {𝔭 : Prime' K | ∃ (_ : 𝔪 (Place.finite 𝔭) = 0), True} h_cofin

  have h_has_polar := polarDensity_eq_some_iff.mp h_polar
  have h_has_dirichlet := polar_implies_dirichlet h_has_polar
  exact dirichletDensity_eq_some_iff.mpr h_has_dirichlet

theorem summable_rpow_inv_absNorm_prime {K : Type*} [Field K] [NumberField K]
    (S : Set (Prime' K)) (s : ℝ) (hs : 1 < s) :
    Summable (fun (𝔭 : S) => ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) :=
  partialDedekindZeta_dirichletSeries_summable S s hs

set_option maxHeartbeats 400000 in
theorem dirichletDensity_nfold_coset_additivity (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (n : ℕ) (hn : 𝒞.index = n) (hn_pos : 0 < n)
    (reps : Fin n → FracIdealsCoprime K 𝔪)
    (h_reps : Function.Injective (fun i => QuotientGroup.mk (s := 𝒞) (reps i)))
    (ρ : ℚ)
    (h_density : DirichletDensity K {𝔭 : Prime' K | ∃ (_ : 𝔪 (Place.finite 𝔭) = 0), True} = some ρ) :
    ρ = ∑ i : Fin n, dirichletDensityCoset K 𝔪 𝒞 h_cong (reps i) := by

  have h_one := dirichletDensity_coprime_primes_eq_one K 𝔪 𝒞 h_cong
  have hρ : ρ = 1 := Option.some.inj (h_density.symm.trans h_one)

  have h_each : ∀ i : Fin n, dirichletDensityCoset K 𝔪 𝒞 h_cong (reps i) =
      dirichletDensityCongruence K 𝔪 𝒞 h_cong :=
    fun i => dirichletDensityCoset_eq_congruence K 𝔪 𝒞 h_cong (reps i)

  simp_rw [h_each]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

  subst hρ


  have h_coprime_dir := dirichletDensity_eq_some_iff.mp h_one

  have h_coset_dir : ∀ i : Fin n, HasDirichletDensity K
      {(𝔭 : Prime' K) | ∃ (h : 𝔪 (Place.finite 𝔭) = 0),
        (QuotientGroup.mk (s := 𝒞) (PrimeToFracIdealsCoprime K 𝔪 𝔭 h) :
          FracIdealsCoprime K 𝔪 ⧸ 𝒞) = QuotientGroup.mk (reps i)}
      (dirichletDensityCongruence K 𝔪 𝒞 h_cong) := by
    intro i
    exact dirichletDensity_eq_some_iff.mp (dirichletDensity_coset_eq_some K 𝔪 𝒞 h_cong (reps i))

  have h_sum_dir : HasDirichletDensity K
      {(𝔭 : Prime' K) | ∃ (_ : 𝔪 (Place.finite 𝔭) = 0), True}
      (↑n * dirichletDensityCongruence K 𝔪 𝒞 h_cong) := by

    let Si : Fin n → Set (Prime' K) := fun i =>
      {𝔭 | ∃ (h : 𝔪 (Place.finite 𝔭) = 0),
        (QuotientGroup.mk (s := 𝒞) (PrimeToFracIdealsCoprime K 𝔪 𝔭 h) :
          FracIdealsCoprime K 𝔪 ⧸ 𝒞) = QuotientGroup.mk (reps i)}

    have h_disj : Set.PairwiseDisjoint (Finset.univ : Finset (Fin n)) Si := by
      intro i _ j _ hij
      simp only [Function.onFun, Set.disjoint_iff]
      intro 𝔭 ⟨hi, hj⟩
      obtain ⟨h_cop_i, h_qi⟩ := hi
      obtain ⟨h_cop_j, h_qj⟩ := hj
      apply hij
      apply h_reps
      show (QuotientGroup.mk (s := 𝒞) (reps i) : FracIdealsCoprime K 𝔪 ⧸ 𝒞) =
           QuotientGroup.mk (reps j)
      rw [← h_qi, ← h_qj]


    have h_surj : Function.Surjective (fun i : Fin n => QuotientGroup.mk (s := 𝒞) (reps i)) := by
      haveI : Fintype (FracIdealsCoprime K 𝔪 ⧸ 𝒞) :=
        Subgroup.fintypeOfIndexNeZero (by rw [hn]; omega)
      have h_card : Fintype.card (FracIdealsCoprime K 𝔪 ⧸ 𝒞) = n := by
        rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card 𝒞, hn]
      exact ((Fintype.bijective_iff_injective_and_card _).mpr
        ⟨h_reps, by rw [Fintype.card_fin, h_card]⟩).2

    have h_eq_union : {𝔭 : Prime' K | ∃ (_ : 𝔪 (Place.finite 𝔭) = 0), True} =
        ⋃ i : Fin n, Si i := by
      ext 𝔭
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Si]
      constructor
      · rintro ⟨h_cop, _⟩
        obtain ⟨i, hi⟩ := h_surj (QuotientGroup.mk (s := 𝒞) (PrimeToFracIdealsCoprime K 𝔪 𝔭 h_cop))
        exact ⟨i, h_cop, hi.symm⟩
      · rintro ⟨i, h_cop, _⟩
        exact ⟨h_cop, trivial⟩

    unfold HasDirichletDensity
    rw [h_eq_union]

    have h_ind_tendsto : ∀ i : Fin n, Filter.Tendsto
        (fun s : ℝ => (∑' (𝔭 : ↥(Si i)),
          ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) /
          Real.log (1 / (s - 1)))
        (nhdsWithin 1 (Set.Ioi 1))
        (nhds ((dirichletDensityCongruence K 𝔪 𝒞 h_cong : ℝ))) :=
      fun i => h_coset_dir i
    have h_sum_tendsto := tendsto_finset_sum Finset.univ
      (fun i _ => h_ind_tendsto i)
    have h_sum_val : ∑ i : Fin n, (dirichletDensityCongruence K 𝔪 𝒞 h_cong : ℝ) =
        ↑n * (dirichletDensityCongruence K 𝔪 𝒞 h_cong : ℝ) := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show ((↑n * dirichletDensityCongruence K 𝔪 𝒞 h_cong : ℚ) : ℝ) =
      ↑n * (dirichletDensityCongruence K 𝔪 𝒞 h_cong : ℝ) from by push_cast; ring]
    rw [← h_sum_val]
    apply Filter.Tendsto.congr' _ h_sum_tendsto
    apply Filter.eventually_of_mem self_mem_nhdsWithin
    intro s (hs : 1 < s)
    dsimp only
    rw [← Finset.sum_div]
    congr 1


    rw [show (⋃ i : Fin n, Si i) = ⋃ i ∈ (Finset.univ : Finset (Fin n)), Si i from by
      simp only [Finset.mem_univ, Set.iUnion_true]]
    exact (Summable.tsum_finset_bUnion_disjoint
      (f := fun 𝔭 : Prime' K => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s))
      (fun i hi j hj hij => h_disj hi hj hij)
      (fun i _ => summable_rpow_inv_absNorm_prime (Si i) s hs)).symm


  have h_eq := hasDirichletDensity_unique h_coprime_dir h_sum_dir
  rw [nsmul_eq_mul]
  exact_mod_cast h_eq

theorem dirichletDensity_coset_partition_sum (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (n : ℕ) (hn : 𝒞.index = n) (hn_pos : 0 < n)
    (reps : Fin n → FracIdealsCoprime K 𝔪)
    (h_reps : Function.Injective (fun i => QuotientGroup.mk (s := 𝒞) (reps i))) :
    (DirichletDensity K {𝔭 : Prime' K | ∃ (_ : 𝔪 (Place.finite 𝔭) = 0), True}).getD 0 =
      ∑ i : Fin n, dirichletDensityCoset K 𝔪 𝒞 h_cong (reps i) := by

  have h_one := dirichletDensity_coprime_primes_eq_one K 𝔪 𝒞 h_cong

  rw [h_one]
  simp only [Option.getD]

  exact dirichletDensity_nfold_coset_additivity K 𝔪 𝒞 h_cong n hn hn_pos reps h_reps 1 h_one

theorem density_cosets_sum_one (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (n : ℕ) (hn : 𝒞.index = n) (hn_pos : 0 < n)
    (reps : Fin n → FracIdealsCoprime K 𝔪)
    (h_reps : Function.Injective (fun i => QuotientGroup.mk (s := 𝒞) (reps i))) :
    ∑ i : Fin n, dirichletDensityCoset K 𝔪 𝒞 h_cong (reps i) = 1 := by

  have h_sum := dirichletDensity_coset_partition_sum K 𝔪 𝒞 h_cong n hn hn_pos reps h_reps

  have h_one := dirichletDensity_coprime_primes_eq_one K 𝔪 𝒞 h_cong

  rw [h_one] at h_sum
  simp [Option.getD] at h_sum
  linarith

theorem corollary_22_22 (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (n : ℕ) (hn : 𝒞.index = n) (hn_pos : 0 < n)
    (reps : Fin n → FracIdealsCoprime K 𝔪)
    (h_reps : Function.Injective (fun i => QuotientGroup.mk (s := 𝒞) (reps i))) :
    AllLValuesNonzero K 𝔪 𝒞 ∧
    ∀ (I : FracIdealsCoprime K 𝔪),
      dirichletDensityCoset K 𝔪 𝒞 h_cong I = 1 / (n : ℚ) := by
  have h_sum := density_cosets_sum_one K 𝔪 𝒞 h_cong n hn hn_pos reps h_reps
  have h_each : ∀ i : Fin n,
      (AllLValuesNonzero K 𝔪 𝒞 →
        dirichletDensityCoset K 𝔪 𝒞 h_cong (reps i) = 1 / (n : ℚ)) ∧
      (¬ AllLValuesNonzero K 𝔪 𝒞 →
        dirichletDensityCoset K 𝔪 𝒞 h_cong (reps i) = 0) :=
    fun i => proposition_22_21 K 𝔪 𝒞 h_cong n hn hn_pos (reps i)

  have hL : AllLValuesNonzero K 𝔪 𝒞 := by
    by_contra hL
    have h_zero : ∀ i : Fin n,
        dirichletDensityCoset K 𝔪 𝒞 h_cong (reps i) = 0 :=
      fun i => (h_each i).2 hL
    simp only [h_zero, Finset.sum_const_zero] at h_sum
    exact one_ne_zero h_sum.symm
  exact ⟨hL, fun I => (proposition_22_21 K 𝔪 𝒞 h_cong n hn hn_pos I).1 hL⟩

theorem ps9_dirichletDensity_mono {K : Type*} [Field K] [NumberField K]
    {S T : Set (Prime' K)} {ρS ρT : ℚ}
    (hST : S ⊆ T)
    (hS : HasDirichletDensity K S ρS)
    (hT : HasDirichletDensity K T ρT) :
    ρS ≤ ρT := by

  suffices h : (ρS : ℝ) ≤ (ρT : ℝ) from mod_cast h

  apply le_of_tendsto_of_tendsto hS hT


  have hIoo : Set.Ioo (1 : ℝ) 2 ∈ nhdsWithin 1 (Set.Ioi 1) :=
    Ioo_mem_nhdsGT (by norm_num : (1 : ℝ) < 2)
  filter_upwards [hIoo] with s hs
  have hs_gt : 1 < s := hs.1
  have hs_lt : s < 2 := hs.2

  have hlog_pos : 0 < Real.log (1 / (s - 1)) := by
    apply Real.log_pos
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < s - 1)]
    linarith

  apply div_le_div_of_nonneg_right _ hlog_pos.le
  exact Summable.tsum_le_tsum_of_inj (Set.inclusion hST)
    (Set.inclusion_injective hST)
    (fun c _ => by positivity)
    (fun i => le_refl _)
    (summable_rpow_inv_absNorm_prime S s hs_gt)
    (summable_rpow_inv_absNorm_prime T s hs_gt)

theorem dirichletDensity_le_of_PrimeSetLe {K : Type u} [Field K] [NumberField K]
    {S T : Set (Prime' K)} {ρS ρT : ℚ}
    (hle : PrimeSetLe S T)
    (hS_polar : PolarDensity K S = some ρS)
    (hT_dir : HasDirichletDensity K T ρT) :
    ρS ≤ ρT := by


  have hST_fin : Set.Finite (S \ T) := hle

  have h_symm : Set.Finite (symmDiff S (S ∩ T)) := by
    have : symmDiff S (S ∩ T) = S \ T := by
      ext x
      simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_diff]
      tauto
    rw [this]
    exact hST_fin


  have h_union_eq : (S ∩ T) ∪ (S \ T) = S := by
    ext x; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]; tauto
  have h_inter_fin : ((S ∩ T) ∩ (S \ T)).Finite := by
    convert Set.finite_empty
    ext x; simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_empty_iff_false]; tauto
  have h_sdiff_polar : PolarDensity K (S \ T) = some 0 :=
    proposition_21_14a_finite _ hST_fin
  have h_inter_polar : PolarDensity K (S ∩ T) = some (ρS - 0) := by
    have hU : PolarDensity K ((S ∩ T) ∪ (S \ T)) = some ρS := by
      rw [h_union_eq]; exact hS_polar
    exact proposition_21_14c_additive_case3 (S ∩ T) (S \ T) h_inter_fin
      0 ρS h_sdiff_polar hU
  rw [sub_zero] at h_inter_polar

  have h_inter_dir : HasDirichletDensity K (S ∩ T) ρS := by
    have := (polarDensity_eq_some_iff (K := K)).mp h_inter_polar
    exact polar_implies_dirichlet this

  exact ps9_dirichletDensity_mono Set.inter_subset_right h_inter_dir hT_dir

theorem corollary_22_23 (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (h_spl : PrimeSetLe (Spl K L) (primesInCongruenceSubgroup K 𝔪 𝒞)) :
    𝒞.index ≤ Module.finrank K L := by

  by_cases hind : 𝒞.index = 0
  · simp [hind]

  have hind_pos : 0 < 𝒞.index := Nat.pos_of_ne_zero hind
  have hfr_pos : 0 < Module.finrank K L := Module.finrank_pos

  have h_spl_polar := theorem_21_15 K L (Module.finrank K L) rfl hfr_pos

  have h_spl_dir : HasDirichletDensity K (Spl K L) (1 / (Module.finrank K L : ℚ)) := by
    have := (polarDensity_eq_some_iff (K := K)).mp h_spl_polar
    exact polar_implies_dirichlet this


  have h_cong_dir : HasDirichletDensity K
      (primesInCongruenceSubgroup K 𝔪 𝒞) (1 / (𝒞.index : ℚ)) := by

    haveI : Fintype (FracIdealsCoprime K 𝔪 ⧸ 𝒞) :=
      Subgroup.fintypeOfIndexNeZero hind
    have h_card : Fintype.card (FracIdealsCoprime K 𝔪 ⧸ 𝒞) = 𝒞.index := by
      rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    set e : (FracIdealsCoprime K 𝔪 ⧸ 𝒞) ≃ Fin 𝒞.index :=
      (Fintype.equivFin _).trans (finCongr h_card) with e_def
    set reps : Fin 𝒞.index → FracIdealsCoprime K 𝔪 :=
      fun i => Quotient.out (e.symm i) with reps_def
    have h_reps : Function.Injective
        (fun i => QuotientGroup.mk (s := 𝒞) (reps i)) := by
      intro i j hij
      have mk_out : ∀ q : FracIdealsCoprime K 𝔪 ⧸ 𝒞,
          QuotientGroup.mk (s := 𝒞) (Quotient.out q) = q :=
        fun q => Quotient.out_eq' q
      simp only [reps_def, mk_out] at hij
      exact e.symm.injective hij

    have h_cor := (corollary_22_22 K 𝔪 𝒞 h_cong 𝒞.index rfl hind_pos reps h_reps).2
        (1 : FracIdealsCoprime K 𝔪)


    have h_ne : (1 : ℚ) / (𝒞.index : ℚ) ≠ 0 :=
      div_ne_zero one_ne_zero (Nat.cast_ne_zero.mpr hind)
    unfold dirichletDensityCoset at h_cor

    set S := {𝔭 : Prime' K | ∃ (h : 𝔪 (Place.finite 𝔭) = 0),
      (QuotientGroup.mk (s := 𝒞) (PrimeToFracIdealsCoprime K 𝔪 𝔭 h) :
        FracIdealsCoprime K 𝔪 ⧸ 𝒞) = QuotientGroup.mk 1} with S_def
    have h_some : DirichletDensity K S = some (1 / (𝒞.index : ℚ)) := by
      cases hD : DirichletDensity K S with
      | none =>
        rw [hD] at h_cor
        simp only [Option.getD] at h_cor
        exact absurd h_cor.symm h_ne
      | some v =>
        rw [hD] at h_cor
        simp only [Option.getD] at h_cor
        rw [h_cor]
    have h_dir : HasDirichletDensity K S (1 / (𝒞.index : ℚ)) :=
      dirichletDensity_eq_some_iff.mp h_some

    have h_eq : primesInCongruenceSubgroup K 𝔪 𝒞 = S := by
      ext 𝔭
      simp only [primesInCongruenceSubgroup, Set.mem_setOf_eq, S_def]
      constructor
      · rintro ⟨h, hm⟩
        exact ⟨h, by rw [QuotientGroup.eq]; simpa using hm⟩
      · rintro ⟨h, hm⟩
        exact ⟨h, by rw [QuotientGroup.eq] at hm; simpa using hm⟩
    rwa [← h_eq] at h_dir


  have h_dle : (1 / (Module.finrank K L : ℚ)) ≤ (1 / (𝒞.index : ℚ)) :=
    dirichletDensity_le_of_PrimeSetLe h_spl h_spl_polar h_cong_dir


  have hm' : (0 : ℚ) < 𝒞.index := Nat.cast_pos.mpr hind_pos
  have hn' : (0 : ℚ) < Module.finrank K L := Nat.cast_pos.mpr hfr_pos
  rw [div_le_div_iff_of_pos_left one_pos hn' hm'] at h_dle
  exact_mod_cast h_dle

noncomputable def extensionAdmissibleModulus (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Modulus K where
  toFun _ := 0
  finite_support := by simp [Set.finite_empty]
  inf_le_one := fun _ => Nat.zero_le 1
  complex_zero := fun _ _ => rfl

noncomputable def extensionNormSubgroup (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Subgroup (FracIdealsCoprime K (extensionAdmissibleModulus K L)) :=
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq (fun _ => by simp)
  haveI : FiniteDimensional ℚ L := Module.Finite.trans K L
  haveI : NumberField L := NumberField.mk
  NormGroup K L (extensionAdmissibleModulus K L)

theorem extensionNormSubgroup_isCong (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    IsCongruenceSubgroup K (extensionAdmissibleModulus K L)
      (extensionNormSubgroup K L) := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  haveI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq (fun _ => by simp)
  haveI : FiniteDimensional ℚ L := Module.Finite.trans K L
  haveI : NumberField L := NumberField.mk
  exact ⟨rayGroup_le_normGroup K L (extensionAdmissibleModulus K L)⟩

noncomputable def extensionConductor (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] : Modulus K :=
  conductorOfCongruenceSubgroup K
    (extensionAdmissibleModulus K L)
    (extensionNormSubgroup K L)
    (extensionNormSubgroup_isCong K L)

def IsUnramifiedIn (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  ∀ (𝔔 : Ideal (NumberField.RingOfIntegers L)) [𝔔.IsPrime],
    𝔔.LiesOver 𝔭.asIdeal →
    Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) 𝔔

def IsTamelyRamifiedIn (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  ∀ (𝔔 : Ideal (NumberField.RingOfIntegers L)) [𝔔.IsPrime],
    𝔔.LiesOver 𝔭.asIdeal →
      ¬ (ringChar (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) ∣
          Ideal.ramificationIdx 𝔭.asIdeal 𝔔)

def IsWildlyRamifiedIn (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  ∃ (𝔔 : Ideal (NumberField.RingOfIntegers L)) (_ : 𝔔.IsPrime),
    𝔔.LiesOver 𝔭.asIdeal ∧
      ringChar (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal) ∣
        Ideal.ramificationIdx 𝔭.asIdeal 𝔔

def IsTotallyRamifiedIn (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  ∀ (𝔔 : Ideal (NumberField.RingOfIntegers L)) [𝔔.IsPrime],
    𝔔.LiesOver 𝔭.asIdeal →
      Ideal.inertiaDeg 𝔭.asIdeal 𝔔 = 1

def IsTotallyTamelyRamified (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  IsTotallyRamifiedIn K L 𝔭 ∧ IsTamelyRamifiedIn K L 𝔭

def IsTotallyWildlyRamified (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prop :=
  IsTotallyRamifiedIn K L 𝔭 ∧
    ∀ (𝔔 : Ideal (NumberField.RingOfIntegers L)) [𝔔.IsPrime],
      𝔔.LiesOver 𝔭.asIdeal →
        ∃ k : ℕ, Ideal.ramificationIdx 𝔭.asIdeal 𝔔 =
          (ringChar (NumberField.RingOfIntegers K ⧸ 𝔭.asIdeal)) ^ k

theorem extensionConductor_eq_zero_of_unramified (K : Type u) (L : Type u)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔭 : Prime' K) (_h : IsUnramifiedIn K L 𝔭) :
    (extensionConductor K L) (Place.finite 𝔭) = 0 := by


  unfold extensionConductor conductorOfCongruenceSubgroup
  have h_spec := (corollary_22_7 K (extensionAdmissibleModulus K L)
    (extensionNormSubgroup K L) (extensionNormSubgroup_isCong K L)).choose_spec
  have h_dvd : Modulus.dvd
      (corollary_22_7 K (extensionAdmissibleModulus K L)
        (extensionNormSubgroup K L) (extensionNormSubgroup_isCong K L)).choose
      (extensionAdmissibleModulus K L) := by
    exact h_spec.1.2 (extensionAdmissibleModulus K L)
      ⟨extensionNormSubgroup K L, extensionNormSubgroup_isCong K L,
       congruenceSubgroupEquiv_refl K (extensionAdmissibleModulus K L)
         (extensionNormSubgroup K L)⟩
  have h_le := h_dvd (Place.finite 𝔭)
  have h_zero : (extensionAdmissibleModulus K L) (Place.finite 𝔭) = 0 := rfl
  omega

theorem IsUnramifiedIn_of_extensionConductor_eq_zero (K : Type u) (L : Type u)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔭 : Prime' K) (h : (extensionConductor K L) (Place.finite 𝔭) = 0) :
    IsUnramifiedIn K L 𝔭 := by
  sorry

theorem proposition_22_25_unramified (K : Type u) (L : Type u)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔭 : Prime' K) :
    (extensionConductor K L) (Place.finite 𝔭) = 0 ↔ IsUnramifiedIn K L 𝔭 :=
  ⟨IsUnramifiedIn_of_extensionConductor_eq_zero K L 𝔭,
   extensionConductor_eq_zero_of_unramified K L 𝔭⟩

theorem proposition_22_25_tame (K : Type u) (L : Type u)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔭 : Prime' K) :
    (extensionConductor K L) (Place.finite 𝔭) = 1 ↔
      (IsTamelyRamifiedIn K L 𝔭 ∧ ¬ IsUnramifiedIn K L 𝔭) := by
  sorry

theorem proposition_22_25_wild (K : Type u) (L : Type u)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔭 : Prime' K) :
    2 ≤ (extensionConductor K L) (Place.finite 𝔭) ↔ IsWildlyRamifiedIn K L 𝔭 := by
  have h_unram := proposition_22_25_unramified K L 𝔭
  have h_tame := proposition_22_25_tame K L 𝔭
  have h_tame_iff_not_wild : IsTamelyRamifiedIn K L 𝔭 ↔ ¬ IsWildlyRamifiedIn K L 𝔭 := by
    constructor
    · intro h_t ⟨𝔔, h𝔔p, h_lies, h_div⟩
      exact @h_t 𝔔 h𝔔p h_lies h_div
    · intro h_nw 𝔔 h𝔔p h_lies h_div
      exact h_nw ⟨𝔔, h𝔔p, h_lies, h_div⟩


  have h_unram_imp_tame : IsUnramifiedIn K L 𝔭 → IsTamelyRamifiedIn K L 𝔭 := by
    intro h_u 𝔔 h𝔔p h_lies h_div
    haveI : 𝔔.IsPrime := h𝔔p
    haveI : Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) 𝔔 := h_u 𝔔 h_lies
    haveI : 𝔔.LiesOver 𝔭.asIdeal := h_lies
    have h𝔔_ne : 𝔔 ≠ ⊥ := by
      intro h
      have h1 := Ideal.over_def 𝔔 𝔭.asIdeal
      rw [h] at h1
      have h2 : Ideal.under (NumberField.RingOfIntegers K)
          (⊥ : Ideal (NumberField.RingOfIntegers L)) = ⊥ := by
        simp [Ideal.under,
          Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)]
      rw [h2] at h1
      exact 𝔭.ne_bot h1
    have h_ram_one : 𝔭.asIdeal.ramificationIdx 𝔔 = 1 := by
      have h1 : (Ideal.under (NumberField.RingOfIntegers K) 𝔔).ramificationIdx 𝔔 = 1 :=
        Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
          (R := NumberField.RingOfIntegers K) h𝔔_ne
      rwa [← Ideal.over_def 𝔔 𝔭.asIdeal] at h1
    rw [h_ram_one] at h_div
    exact CharP.ringChar_ne_one (Nat.eq_one_of_dvd_one h_div)
  set n := (extensionConductor K L) (Place.finite 𝔭)
  constructor
  ·
    intro hn2
    rw [← not_not (a := IsWildlyRamifiedIn K L 𝔭)]
    intro h_not_wild
    have h_tame_ram := h_tame_iff_not_wild.mpr h_not_wild
    have h_not_unram : ¬ IsUnramifiedIn K L 𝔭 := by
      intro h_u; have := h_unram.mpr h_u; omega
    have := h_tame.mpr ⟨h_tame_ram, h_not_unram⟩
    omega
  ·
    intro h_wild
    have h_not_tame : ¬ IsTamelyRamifiedIn K L 𝔭 :=
      fun h_t => (h_tame_iff_not_wild.mp h_t) h_wild
    have h_ne_one : n ≠ 1 := by
      intro heq; exact h_not_tame (h_tame.mp heq).1
    have h_ne_zero : n ≠ 0 := by
      intro heq
      have h_u := h_unram.mp heq
      exact h_not_tame (h_unram_imp_tame h_u)
    omega

lemma extensionNormSubgroup_equiv_at_modulus (K : Type u) (L : Type u)
    [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔫 : Modulus K) :
    ∃ 𝒟 : Subgroup (FracIdealsCoprime K 𝔫),
      IsCongruenceSubgroup K 𝔫 𝒟 ∧
      CongruenceSubgroupEquiv K (extensionAdmissibleModulus K L) 𝔫
        (extensionNormSubgroup K L) 𝒟 := by


  set 𝔪 := extensionAdmissibleModulus K L
  have h_dvd_m_n : Modulus.dvd 𝔪 𝔫 := fun v => Nat.zero_le _

  set 𝒟 := Subgroup.comap (FracIdealsCoprime.inclusion K 𝔪 𝔫 h_dvd_m_n)
    (extensionNormSubgroup K L)
  refine ⟨𝒟, ?_, ?_⟩


  · constructor
    intro x hx
    show (FracIdealsCoprime.inclusion K 𝔪 𝔫 h_dvd_m_n) x ∈ extensionNormSubgroup K L


    exact (extensionNormSubgroup_isCong K L).contains_ray
      (RayGroup.inclusion_le K 𝔪 𝔫 h_dvd_m_n x hx)


  · refine ⟨𝔫, h_dvd_m_n, fun v => le_refl _, ?_⟩


    show 𝒟 = Subgroup.comap (FracIdealsCoprime.inclusion K 𝔫 𝔫 _) 𝒟
    ext x
    simp only [Subgroup.mem_comap]
    constructor
    · intro hx; convert hx using 1
    · intro hx; convert hx using 1

theorem extensionConductor_infinite_zero (K : Type u) (L : Type u)
    [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (w : NumberField.InfinitePlace K) :
    NumberField.InfinitePlace.IsUnramifiedIn L w →
    (extensionConductor K L) (Place.infinite w) = 0 := by
  intro _


  unfold extensionConductor conductorOfCongruenceSubgroup
  have h_spec := (corollary_22_7 K
    (extensionAdmissibleModulus K L)
    (extensionNormSubgroup K L)
    (extensionNormSubgroup_isCong K L)).choose_spec
  have h_dvd : Modulus.dvd
    (corollary_22_7 K
      (extensionAdmissibleModulus K L)
      (extensionNormSubgroup K L)
      (extensionNormSubgroup_isCong K L)).choose
    (extensionAdmissibleModulus K L) := by
    exact h_spec.1.2 (extensionAdmissibleModulus K L)
      ⟨extensionNormSubgroup K L, extensionNormSubgroup_isCong K L,
       congruenceSubgroupEquiv_refl K (extensionAdmissibleModulus K L)
         (extensionNormSubgroup K L)⟩
  have h_le := h_dvd (Place.infinite w)
  simp only [extensionAdmissibleModulus] at h_le
  exact Nat.le_zero.mp h_le

theorem extensionConductor_infinite_one (K : Type u) (L : Type u)
    [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (w : NumberField.InfinitePlace K) :
    ¬ NumberField.InfinitePlace.IsUnramifiedIn L w →
    (extensionConductor K L) (Place.infinite w) = 1 := by
  sorry

noncomputable def NormGroup (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔪 : Modulus K) : Subgroup (FracIdealsCoprime K 𝔪) :=
  letI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  letI : FiniteDimensional ℚ L := FiniteDimensional.trans ℚ K L
  letI : NumberField L := NumberField.mk

  RayClassField.NormGroup K L 𝔪

theorem normGroup_isCongruenceSubgroup (K : Type u) (L : Type u)
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔪 : Modulus K)
    (h_cond : Modulus.dvd (extensionConductor K L) 𝔪) :
    IsCongruenceSubgroup K 𝔪 (NormGroup K L 𝔪) :=
  ⟨le_sup_left⟩

noncomputable def choosePrimeOverHOS (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) : Prime' L :=
  ⟨choosePrimeOver K L 𝔭, choosePrimeOver_isPrime K L 𝔭, choosePrimeOver_ne_bot K L 𝔭⟩

lemma choosePrimeOverHOS_lyingUnder (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (𝔭 : Prime' K) :
    lyingUnder K L (choosePrimeOverHOS K L 𝔭) = 𝔭 := by
  ext
  simp only [lyingUnder, IsDedekindDomain.HeightOneSpectrum.under_asIdeal,
    choosePrimeOverHOS, choosePrimeOver_over]

theorem theorem_6_10_norm_prime
    (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔮 : Prime' L) :
    fracIdealNorm K L (primeAsUnitFracIdeal L 𝔮) =
      (primeAsUnitFracIdeal K (lyingUnder K L 𝔮)) ^ (inertiaDegree' K L 𝔮) := by
  exact fracIdealNorm_prime_eq K L 𝔮

lemma primeAbove_coprime_extendModulus
    (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    (𝔪 : Modulus K) (𝔭 : Prime' K) (𝔮 : Prime' L)
    (h_over : lyingUnder K L 𝔮 = 𝔭)
    (h_coprime : 𝔪 (Place.finite 𝔭) = 0) :
    (extendModulus K L 𝔪) (Place.finite 𝔮) = 0 := by
  simp only [extendModulus]
  rw [h_over]
  simp only [Nat.mul_eq_zero]
  exact Or.inr h_coprime

theorem splitsCompletely_inertiaDeg_eq_one
    (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (𝔭 : Prime' K) (𝔮 : Prime' L)
    (h_split : SplitsCompletely K L 𝔭)
    (h_over : lyingUnder K L 𝔮 = 𝔭) :
    inertiaDegree' K L 𝔮 = 1 := by


  have h_frob_eq_one : FrobeniusAutomorphism K L 𝔭 = 1 := h_split

  let Q₀ := choosePrimeOver K L 𝔭
  have h_isArith : IsArithFrobAt (NumberField.RingOfIntegers K)
      (arithFrobAt (NumberField.RingOfIntegers K) (L ≃ₐ[K] L) Q₀) Q₀ :=
    IsArithFrobAt.arithFrobAt (NumberField.RingOfIntegers K) (L ≃ₐ[K] L) Q₀

  rw [FrobeniusAutomorphism] at h_frob_eq_one
  rw [h_frob_eq_one] at h_isArith


  have h_pow : ∀ x : NumberField.RingOfIntegers L ⧸ Q₀,
      x ^ Nat.card (NumberField.RingOfIntegers K ⧸ Ideal.under (NumberField.RingOfIntegers K) Q₀) = x := by
    intro x
    have := h_isArith.restrict_apply x


    have hrestr_id : ∀ y : NumberField.RingOfIntegers L ⧸ Q₀, h_isArith.restrict y = y := by
      intro y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      show Ideal.Quotient.mk Q₀ ((MulSemiringAction.toAlgHom (NumberField.RingOfIntegers K)
        (NumberField.RingOfIntegers L) (1 : L ≃ₐ[K] L)) y) = Ideal.Quotient.mk Q₀ y
      congr 1
    rw [← this, hrestr_id]


  haveI hQ₀_prime : Q₀.IsPrime := choosePrimeOver_isPrime K L 𝔭
  haveI hQ₀_finite : Finite (NumberField.RingOfIntegers L ⧸ Q₀) :=
    choosePrimeOver_finite K L 𝔭
  haveI : Fintype (NumberField.RingOfIntegers L ⧸ Q₀) := Fintype.ofFinite _
  let P₀ := Ideal.under (NumberField.RingOfIntegers K) Q₀
  haveI : Finite (NumberField.RingOfIntegers K ⧸ P₀) :=
    Finite.of_injective _ Ideal.algebraMap_quotient_injective
  haveI : Fintype (NumberField.RingOfIntegers K ⧸ P₀) := Fintype.ofFinite _
  have h_pow_card : ∀ x : NumberField.RingOfIntegers L ⧸ Q₀,
      x ^ Fintype.card (NumberField.RingOfIntegers K ⧸ P₀) = x := by
    intro x
    rw [← Nat.card_eq_fintype_card]
    exact h_pow x

  have hP₀_eq : P₀ = 𝔭.asIdeal := choosePrimeOver_over K L 𝔭

  haveI hQ₀_max : Q₀.IsMaximal :=
    hQ₀_prime.isMaximal (choosePrimeOver_ne_bot K L 𝔭)

  haveI hP₀_max : P₀.IsMaximal := hP₀_eq ▸ (𝔭.isPrime.isMaximal 𝔭.ne_bot)

  letI : Field (NumberField.RingOfIntegers K ⧸ P₀) := Ideal.Quotient.field P₀
  letI : Field (NumberField.RingOfIntegers L ⧸ Q₀) := Ideal.Quotient.field Q₀

  letI : Algebra (NumberField.RingOfIntegers K ⧸ P₀)
      (NumberField.RingOfIntegers L ⧸ Q₀) :=
    Ideal.Quotient.algebraQuotientOfLEComap (le_of_eq rfl)
  have h_finrank_one : Module.finrank (NumberField.RingOfIntegers K ⧸ P₀)
      (NumberField.RingOfIntegers L ⧸ Q₀) = 1 := by
    have hfrob_eq : FiniteField.frobeniusAlgHom (NumberField.RingOfIntegers K ⧸ P₀)
        (NumberField.RingOfIntegers L ⧸ Q₀) = 1 := by
      apply AlgHom.ext
      intro x
      show x ^ Fintype.card (NumberField.RingOfIntegers K ⧸ P₀) = x
      exact h_pow_card x
    rw [← FiniteField.orderOf_frobeniusAlgHom, hfrob_eq, orderOf_one]

  have h_comap : Ideal.comap (algebraMap (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L)) Q₀ = P₀ := rfl
  have h_inertiaDeg_Q₀ : Ideal.inertiaDeg P₀ Q₀ = 1 := by
    unfold Ideal.inertiaDeg
    simp only [h_comap]
    convert h_finrank_one

  unfold inertiaDegree'
  rw [h_over]


  rw [hP₀_eq] at h_inertiaDeg_Q₀
  haveI : 𝔮.asIdeal.IsPrime := 𝔮.isPrime
  haveI : Finite (NumberField.RingOfIntegers L ⧸ 𝔮.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ 𝔮.ne_bot

  haveI : Q₀.LiesOver 𝔭.asIdeal := Ideal.LiesOver.mk hP₀_eq.symm
  have h𝔮_over_asIdeal : 𝔭.asIdeal = Ideal.under (NumberField.RingOfIntegers K) 𝔮.asIdeal := by
    have := IsDedekindDomain.HeightOneSpectrum.under_asIdeal (NumberField.RingOfIntegers K) 𝔮
    rw [← this]
    exact congrArg IsDedekindDomain.HeightOneSpectrum.asIdeal h_over.symm
  haveI : 𝔮.asIdeal.LiesOver 𝔭.asIdeal := Ideal.LiesOver.mk h𝔮_over_asIdeal
  rw [← h_inertiaDeg_Q₀]
  exact (Ideal.inertiaDeg_eq_of_isGaloisGroup 𝔭.asIdeal Q₀ 𝔮.asIdeal (L ≃ₐ[K] L)).symm

theorem splitsCompletely_coprime_mem_normGroup
    (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔪 : Modulus K)
    (h_cond : Modulus.dvd (extensionConductor K L) 𝔪)
    (𝔭 : Prime' K)
    (h_split : SplitsCompletely K L 𝔭)
    (h_coprime : 𝔪 (Place.finite 𝔭) = 0) :
    PrimeToFracIdealsCoprime K 𝔪 𝔭 h_coprime ∈ NormGroup K L 𝔪 := by

  let 𝔮 := choosePrimeOverHOS K L 𝔭
  have h_over : lyingUnder K L 𝔮 = 𝔭 := choosePrimeOverHOS_lyingUnder K L 𝔭

  have h_ext_coprime : (extendModulus K L 𝔪) (Place.finite 𝔮) = 0 :=
    primeAbove_coprime_extendModulus K L 𝔪 𝔭 𝔮 h_over h_coprime

  let 𝔮_coprime : FracIdealsCoprime L (extendModulus K L 𝔪) :=
    primeCoprime L (extendModulus K L 𝔪) 𝔮 h_ext_coprime

  have h_f_eq_one : inertiaDegree' K L 𝔮 = 1 :=
    splitsCompletely_inertiaDeg_eq_one K L 𝔭 𝔮 h_split h_over
  have h_norm_eq : fracIdealNorm K L (primeAsUnitFracIdeal L 𝔮) =
      primeAsUnitFracIdeal K 𝔭 := by
    rw [theorem_6_10_norm_prime K L 𝔮, h_over, h_f_eq_one, pow_one]

  have h_in_range : PrimeToFracIdealsCoprime K 𝔪 𝔭 h_coprime ∈
      (idealNormMap K L 𝔪).range := by
    refine ⟨𝔮_coprime, ?_⟩
    apply Subtype.ext


    simp only [idealNormMap, MonoidHom.coe_mk, OneHom.coe_mk]
    exact h_norm_eq

  exact idealNormMap_range_le_normGroup K L 𝔪 h_in_range

theorem proposition_22_28 (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔪 : Modulus K)
    (h_cond : Modulus.dvd (extensionConductor K L) 𝔪) :
    PrimeSetLe (Spl K L) (primesInCongruenceSubgroup K 𝔪 (NormGroup K L 𝔪)) := by


  apply Set.Finite.subset (modulus_support_finite K 𝔪)
  intro 𝔭 h𝔭
  simp only [Set.mem_diff, Spl, Set.mem_setOf_eq, primesInCongruenceSubgroup] at h𝔭
  obtain ⟨h_split, h_not_in⟩ := h𝔭

  simp only [Set.mem_setOf_eq]


  intro h_coprime
  apply h_not_in
  exact ⟨h_coprime,
    splitsCompletely_coprime_mem_normGroup K L 𝔪 h_cond 𝔭 h_split h_coprime⟩

theorem theorem_22_29_norm_index_inequality
    (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔪 : Modulus K)
    (h_cond : Modulus.dvd (extensionConductor K L) 𝔪) :
    (NormGroup K L 𝔪).index ≤ Module.finrank K L := by
  exact corollary_22_23 K L 𝔪 (NormGroup K L 𝔪)
    (normGroup_isCongruenceSubgroup K L 𝔪 h_cond)
    (proposition_22_28 K L 𝔪 h_cond)

theorem completeness_theorem (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔪 : Modulus K) :
    Modulus.dvd (extensionConductor K L) 𝔪 ↔
    ∃ (M : Type u) (_ : Field M) (_ : NumberField M) (_ : Algebra K M)
      (_ : FiniteDimensional K M) (_ : KroneckerWeber.IsAbelianExtension K M),
    @IsRayClassField K M _ _ _ _ _ _ 𝔪 ∧ Nonempty (L →ₐ[K] M) := by sorry

structure IsHilbertClassField (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsAbelianExtension K L] : Prop where
  finiteDimensional : FiniteDimensional K L
  everywhere_unramified : ∀ 𝔭 : Prime' K, IsUnramifiedIn K L 𝔭
  maximal :
    ∀ (M : Type u) [Field M] [NumberField M] [Algebra K M] [IsAbelianExtension K M]
      [FiniteDimensional K M],
      (∀ 𝔭 : Prime' K, IsUnramifiedIn K M 𝔭) → Nonempty (M →ₐ[K] L)

lemma hilbertClassField_ker_eq_rayGroup
    (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [KroneckerWeber.IsAbelianExtension K L]
    (hunram : ∀ 𝔭 : Prime' K, IsUnramifiedIn K L 𝔭)
    (hmax : ∀ (M : Type u) [Field M] [NumberField M] [Algebra K M] [IsAbelianExtension K M]
      [FiniteDimensional K M],
      (∀ 𝔭 : Prime' K, IsUnramifiedIn K M 𝔭) → Nonempty (M →ₐ[K] L)) :
    (ArtinMap K L Modulus.trivial).ker = RayGroup K Modulus.trivial := by


  sorry

lemma hilbertClassField_maximal
    (K : Type u) (L : Type u) (M : Type u) [Field K] [Field L] [Field M]
    [NumberField K] [NumberField L] [NumberField M]
    [Algebra K L] [Algebra K M]
    [KroneckerWeber.IsAbelianExtension K L] [KroneckerWeber.IsAbelianExtension K M]
    (hL : IsRayClassField K L Modulus.trivial)
    (hunramM : ∀ 𝔭 : Prime' K, IsUnramifiedIn K M 𝔭) :
    Nonempty (M →ₐ[K] L) := by

  have h_cond : Modulus.dvd (extensionConductor K M) Modulus.trivial := by
    intro v; simp only [Modulus.trivial]


    sorry

  have h_compl := (completeness_theorem K M Modulus.trivial).mp h_cond
  obtain ⟨N, hFN, hNN, hAN, hFDN, hGN, hRN, ⟨f⟩⟩ := h_compl


  haveI := hGN
  have h_unique := rayClassField_unique K L N Modulus.trivial hL hRN
  obtain ⟨φ⟩ := h_unique

  exact ⟨φ.symm.toAlgHom.comp f⟩

end GlobalCFT

open Ideles

structure GlobalArtinMap (K : Type*) [Field K] [NumberField K] where
  I : Type*
  [instPreorder : Preorder I]
  GalLK : I → Type*
  [instFintype : ∀ i, Fintype (GalLK i)]
  [instCommGroup : ∀ i, CommGroup (GalLK i)]
  restrictMap : ∀ {i j : I}, i ≤ j → GalLK j →* GalLK i
  artinMap : ∀ i, IdeleGroup K →* GalLK i
  artinMap_compat : ∀ {i j : I} (h : i ≤ j) (a : IdeleGroup K),
    restrictMap h (artinMap j a) = artinMap i a
  GalAb : Type*
  [galAb_group : CommGroup GalAb]
  [galAb_topologicalSpace : TopologicalSpace GalAb]
  [galAb_topologicalGroup : IsTopologicalGroup GalAb]
  [galAb_compactSpace : CompactSpace GalAb]
  artinHom : IdeleGroup K →* GalAb
  artinHom_continuous : Continuous artinHom
  proj : ∀ i, GalAb →* GalLK i
  artinMap_eq_proj : ∀ i (a : IdeleGroup K), artinMap i a = proj i (artinHom a)
  artinMap_surjective : ∀ i, Function.Surjective (artinMap i)
  proj_jointly_injective : ∀ g : GalAb, (∀ i, proj i g = 1) → g = 1
  proj_compat : ∀ {i j : I} (h : i ≤ j) (g : GalAb),
    restrictMap h (proj j g) = proj i g
  principalInKer : principalIdeles K ≤ MonoidHom.ker artinHom
  normSubgroup : ∀ i, Subgroup (IdeleClassGroup K)
  normSubgroup_normal : ∀ i, (normSubgroup i).Normal
  artinMapCK_surjective : ∀ i, Function.Surjective
    ((proj i).comp (QuotientGroup.lift (principalIdeles K) artinHom principalInKer))
  ker_eq_normSubgroup : ∀ i, MonoidHom.ker
    ((proj i).comp (QuotientGroup.lift (principalIdeles K) artinHom principalInKer)) =
    normSubgroup i
attribute [instance] GlobalArtinMap.instPreorder
  GlobalArtinMap.instFintype
  GlobalArtinMap.instCommGroup
  GlobalArtinMap.galAb_group
  GlobalArtinMap.galAb_topologicalSpace
  GlobalArtinMap.galAb_topologicalGroup
  GlobalArtinMap.galAb_compactSpace

namespace GlobalArtinMap
theorem normSubgroup_existence {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K)
    (H : Subgroup (IdeleClassGroup K))
    (hopen : IsOpen (H : Set (IdeleClassGroup K)))
    (hfin : H.FiniteIndex) :
    ∃! i : θ.I, θ.normSubgroup i = H := by sorry
end GlobalArtinMap

theorem proposition_28_3 {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K)
    (θ' : IdeleGroup K →* θ.GalAb)
    (hcompat : ∀ (i : θ.I) (a : IdeleGroup K), θ.proj i (θ' a) = θ.artinMap i a) :
    ∀ (a : IdeleGroup K), θ' a = θ.artinHom a := by
  intro a
  have h : ∀ i : θ.I, θ.proj i (θ' a * (θ.artinHom a)⁻¹) = 1 := by
    intro i
    rw [map_mul, map_inv]
    rw [hcompat i a, θ.artinMap_eq_proj i a]
    exact mul_inv_cancel _
  have := θ.proj_jointly_injective (θ' a * (θ.artinHom a)⁻¹) h
  rwa [mul_inv_eq_one] at this

theorem theorem_28_4_principal_in_ker {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K) :
    principalIdeles K ≤ MonoidHom.ker θ.artinHom :=
  θ.principalInKer

noncomputable def GlobalArtinMap.artinHomCK {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K) :
    IdeleClassGroup K →* θ.GalAb :=
  QuotientGroup.lift (principalIdeles K) θ.artinHom (theorem_28_4_principal_in_ker θ)

theorem GlobalArtinMap.artinHomCK_comp {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K) (a : IdeleGroup K) :
    θ.artinHomCK (QuotientGroup.mk a) = θ.artinHom a := by
  simp only [artinHomCK, QuotientGroup.lift_mk']

noncomputable def GlobalArtinMap.normSubgroupCK {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K) (i : θ.I) :
    Subgroup (IdeleClassGroup K) :=
  θ.normSubgroup i

theorem GlobalArtinMap.normSubgroupCK_normal {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K) (i : θ.I) :
    (θ.normSubgroupCK i).Normal :=
  θ.normSubgroup_normal i

attribute [instance] GlobalArtinMap.normSubgroupCK_normal

noncomputable def GlobalArtinMap.artinMapCK {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K) (i : θ.I) :
    IdeleClassGroup K →* θ.GalLK i :=
  (θ.proj i).comp θ.artinHomCK

theorem theorem_28_4_ker_eq_norm {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K) (i : θ.I) :
    MonoidHom.ker (θ.artinMapCK i) = θ.normSubgroupCK i :=
  θ.ker_eq_normSubgroup i

theorem theorem_28_4_iso {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K) (i : θ.I) :
    Nonempty (IdeleClassGroup K ⧸ θ.normSubgroupCK i ≃* θ.GalLK i) :=
  ⟨QuotientGroup.liftEquiv (θ.normSubgroupCK i)
    (θ.artinMapCK_surjective i) (θ.ker_eq_normSubgroup i).symm⟩

theorem theorem_28_6_global_existence {K : Type*} [Field K] [NumberField K]
    (θ : GlobalArtinMap K)
    (H : Subgroup (IdeleClassGroup K))
    (hopen : IsOpen (H : Set (IdeleClassGroup K)))
    (hfin : H.FiniteIndex) :
    ∃! i : θ.I, θ.normSubgroupCK i = H :=
  θ.normSubgroup_existence H hopen hfin

section Chebotarev

universe w

open NumberField RayClassField GlobalCFT

def IsConjugationStable {G : Type*} [Group G] (C : Set G) : Prop :=
  ∀ g : G, ∀ c ∈ C, g * c * g⁻¹ ∈ C

noncomputable def FrobeniusConjClass (K : Type w) (L : Type w)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (𝔭 : Prime' K) : Set (L ≃ₐ[K] L) :=
  {σ : L ≃ₐ[K] L | ∃ (𝔔 : Ideal (RingOfIntegers L)),
    𝔔.IsPrime ∧ 𝔔.LiesOver 𝔭.asIdeal ∧
    IsArithFrobAt (RingOfIntegers K) σ 𝔔}

theorem FrobeniusConjClass.nonempty (K : Type w) (L : Type w)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (𝔭 : Prime' K) (_h_unram : GlobalCFT.IsUnramifiedIn K L 𝔭) :
    (FrobeniusConjClass K L 𝔭).Nonempty := by
  have h𝔭 := 𝔭.isPrime
  have h_inj := RingOfIntegers.algebraMap.injective K L
  obtain ⟨𝔔, _, h𝔔_prime, h𝔔_comap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (S := RingOfIntegers L) 𝔭.asIdeal ⊥
      (by rw [Ideal.comap_bot_of_injective _ h_inj]; exact bot_le)
  have h𝔔_ne_bot : 𝔔 ≠ ⊥ := by
    intro h
    rw [h, Ideal.comap_bot_of_injective _ h_inj] at h𝔔_comap
    exact 𝔭.ne_bot h𝔔_comap.symm
  haveI : 𝔔.IsMaximal := Ideal.IsPrime.isMaximal h𝔔_prime h𝔔_ne_bot
  haveI : 𝔔.IsPrime := h𝔔_prime
  haveI : Finite (RingOfIntegers L ⧸ 𝔔) := inferInstance
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (RingOfIntegers K) (L ≃ₐ[K] L) 𝔔
  exact ⟨σ, 𝔔, h𝔔_prime, ⟨h𝔔_comap.symm⟩, hσ⟩

def primesWithFrobInSet (K : Type w) (L : Type w)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (C : Set (L ≃ₐ[K] L)) : Set (Prime' K) :=
  {𝔭 : Prime' K | GlobalCFT.IsUnramifiedIn K L 𝔭 ∧ FrobeniusConjClass K L 𝔭 ⊆ C}

theorem rayGroup_isCongruenceSubgroup (K : Type w) [Field K] [NumberField K]
    (𝔪 : Modulus K) :
    IsCongruenceSubgroup K 𝔪 (RayGroup K 𝔪) :=
  ⟨le_refl _⟩

theorem rayGroup_index_eq_natCard (K : Type w) [Field K] [NumberField K]
    (𝔪 : Modulus K) :
    (RayGroup K 𝔪).index = Nat.card (RayClassGroup K 𝔪) := by
  rw [Subgroup.index_eq_card]
  rfl

theorem corollary_22_22_hasDirichletDensity
    {K : Type*} [Field K] [NumberField K]
    (𝔪 : Modulus K) (𝒞 : Subgroup (FracIdealsCoprime K 𝔪))
    (h_cong : IsCongruenceSubgroup K 𝔪 𝒞)
    (n : ℕ) (hn : 𝒞.index = n) (hn_pos : 0 < n)
    (I : FracIdealsCoprime K 𝔪) :
    HasDirichletDensity K
      {𝔭 : Prime' K | ∃ (h : 𝔪 (Place.finite 𝔭) = 0),
        (QuotientGroup.mk (s := 𝒞) (PrimeToFracIdealsCoprime K 𝔪 𝔭 h) :
          FracIdealsCoprime K 𝔪 ⧸ 𝒞) = QuotientGroup.mk I}
      (1 / (n : ℚ)) := by

  haveI : Fintype (FracIdealsCoprime K 𝔪 ⧸ 𝒞) :=
    Subgroup.fintypeOfIndexNeZero (hn ▸ hn_pos.ne')
  have h_card : Fintype.card (FracIdealsCoprime K 𝔪 ⧸ 𝒞) = n := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]
    exact hn
  set e : (FracIdealsCoprime K 𝔪 ⧸ 𝒞) ≃ Fin n := (Fintype.equivFin _).trans (finCongr h_card)
  set reps : Fin n → FracIdealsCoprime K 𝔪 := fun i => Quotient.out (e.symm i) with reps_def
  have h_reps : Function.Injective (fun i => QuotientGroup.mk (s := 𝒞) (reps i)) := by
    intro i j hij
    have mk_out : ∀ q : FracIdealsCoprime K 𝔪 ⧸ 𝒞,
        QuotientGroup.mk (s := 𝒞) (Quotient.out q) = q :=
      fun q => Quotient.out_eq' q
    simp only [reps_def, mk_out] at hij
    exact e.symm.injective hij

  have h_cor := (corollary_22_22 K 𝔪 𝒞 h_cong n hn hn_pos reps h_reps).2 I


  have h_ne : (1 : ℚ) / (n : ℚ) ≠ 0 :=
    div_ne_zero one_ne_zero (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn_pos))
  have h_some : DirichletDensity K {𝔭 : Prime' K | ∃ (h : 𝔪 (Place.finite 𝔭) = 0),
      (QuotientGroup.mk (s := 𝒞) (PrimeToFracIdealsCoprime K 𝔪 𝔭 h) :
        FracIdealsCoprime K 𝔪 ⧸ 𝒞) = QuotientGroup.mk I} = some (1 / (n : ℚ)) := by
    have h_getD := h_cor
    unfold dirichletDensityCoset at h_getD
    cases hD : DirichletDensity K {𝔭 : Prime' K | ∃ (h : 𝔪 (Place.finite 𝔭) = 0),
        (QuotientGroup.mk (s := 𝒞) (PrimeToFracIdealsCoprime K 𝔪 𝔭 h) :
          FracIdealsCoprime K 𝔪 ⧸ 𝒞) = QuotientGroup.mk I} with
    | none =>
      rw [hD] at h_getD
      simp only [Option.getD] at h_getD
      exact absurd h_getD.symm h_ne
    | some v =>
      rw [hD] at h_getD
      simp only [Option.getD] at h_getD
      rw [h_getD]
  exact dirichletDensity_eq_some_iff.mp h_some

theorem proposition_28_10 (K : Type w) [Field K] [NumberField K]
    (𝔪 : Modulus K)
    (c : RayClassGroup K 𝔪) :
    DirichletDensity K {𝔭 : Prime' K | ∃ (h : 𝔪 (Place.finite 𝔭) = 0),
      QuotientGroup.mk (PrimeToFracIdealsCoprime K 𝔪 𝔭 h) = c} =
    some (1 / (Nat.card (RayClassGroup K 𝔪) : ℚ)) := by


  have h_cong : IsCongruenceSubgroup K 𝔪 (RayGroup K 𝔪) :=
    rayGroup_isCongruenceSubgroup K 𝔪

  set n := Nat.card (RayClassGroup K 𝔪) with hn_def
  have h_index : (RayGroup K 𝔪).index = n := rayGroup_index_eq_natCard K 𝔪

  have hn_pos : 0 < n := Nat.card_pos (α := RayClassGroup K 𝔪)

  obtain ⟨I, hI⟩ := Quotient.exists_rep c

  have h_has := corollary_22_22_hasDirichletDensity 𝔪 (RayGroup K 𝔪) h_cong n h_index hn_pos I

  have h_eq : {𝔭 : Prime' K | ∃ (h : 𝔪 (Place.finite 𝔭) = 0),
      QuotientGroup.mk (PrimeToFracIdealsCoprime K 𝔪 𝔭 h) = c} =
    {𝔭 : Prime' K | ∃ (h : 𝔪 (Place.finite 𝔭) = 0),
      (QuotientGroup.mk (s := RayGroup K 𝔪)
        (PrimeToFracIdealsCoprime K 𝔪 𝔭 h) :
        FracIdealsCoprime K 𝔪 ⧸ RayGroup K 𝔪) =
      QuotientGroup.mk I} := by
    ext 𝔭
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨h_cop, h_class⟩
      exact ⟨h_cop, by rw [h_class, ← hI]⟩
    · rintro ⟨h_cop, h_class⟩
      exact ⟨h_cop, by rw [← hI]; exact h_class⟩

  rw [h_eq]
  exact dirichletDensity_eq_some_iff.mpr h_has

noncomputable def liftToGalLE {K L : Type*} [Field K] [Field L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) :
    L ≃ₐ[IntermediateField.fixedField (Subgroup.zpowers σ)] L :=
  IntermediateField.fixingSubgroupEquiv
    (IntermediateField.fixedField (Subgroup.zpowers σ))
    ⟨σ, by rw [IntermediateField.fixingSubgroup_fixedField]; exact Subgroup.mem_zpowers σ⟩

lemma abelianFrobenius_rayClass_density_bridge
    (E : Type w) (L : Type w)
    [Field E] [Field L] [NumberField E] [NumberField L]
    [Algebra E L] [IsGalois E L] [FiniteDimensional E L]
    (σ : L ≃ₐ[E] L) :
    HasDirichletDensity E
      (primesWithFrobInSet E L {σ})
      (1 / (Fintype.card (L ≃ₐ[E] L) : ℚ)) := by

  set 𝔪 := extensionConductor E L with h𝔪_def


  have h_bridge : HasDirichletDensity E
      (primesWithFrobInSet E L {σ})
      (1 / (Nat.card (RayClassGroup E 𝔪) : ℚ)) := by


    sorry

  have h_card_eq : (Nat.card (RayClassGroup E 𝔪) : ℚ) =
      (Fintype.card (L ≃ₐ[E] L) : ℚ) := by


    sorry
  rwa [h_card_eq] at h_bridge

lemma abelianDensity_fixedField (K : Type w) (L : Type w)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) :
    let E := IntermediateField.fixedField (Subgroup.zpowers σ)
    haveI : NumberField E := NumberField.of_intermediateField E
    HasDirichletDensity E
      (primesWithFrobInSet E L {liftToGalLE σ})
      (1 / (orderOf σ : ℚ)) := by

  intro E
  haveI : NumberField E := NumberField.of_intermediateField E


  have h_bridge := abelianFrobenius_rayClass_density_bridge E L (liftToGalLE σ)


  suffices h_card : (Fintype.card (L ≃ₐ[E] L) : ℚ) = (orderOf σ : ℚ) by
    rwa [h_card] at h_bridge

  have h_eq : Fintype.card (L ≃ₐ[E] L) = orderOf σ := by
    rw [show E = IntermediateField.fixedField (Subgroup.zpowers σ) from rfl]
    rw [Fintype.card_eq_nat_card, ← Nat.card_zpowers (a := σ)]
    have h := @IntermediateField.fixingSubgroup_fixedField K _ L _ _ (Subgroup.zpowers σ) ‹_›
    have h1 : Nat.card (L ≃ₐ[↥(IntermediateField.fixedField (Subgroup.zpowers σ))] L) =
      Nat.card ((IntermediateField.fixedField (Subgroup.zpowers σ)).fixingSubgroup) :=
      (Nat.card_congr (IntermediateField.fixingSubgroupEquiv _).toEquiv).symm
    rw [h1, h]
  exact_mod_cast h_eq

theorem dirichletSeries_conjClass_comparison (K : Type w) (L : Type w)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) :
    let E := IntermediateField.fixedField (Subgroup.zpowers σ)
    haveI : NumberField E := NumberField.of_intermediateField E
    HasDirichletDensity E (primesWithFrobInSet E L {liftToGalLE σ}) (1 / (orderOf σ : ℚ)) →
    HasDirichletDensity K
      (primesWithFrobInSet K L (ConjClasses.mk σ).carrier)
      ((Set.toFinite (ConjClasses.mk σ).carrier).toFinset.card /
        ((Subgroup.zpowers σ).index * orderOf σ : ℚ)) := by sorry

theorem conjClass_density_intermediate (K : Type w) (L : Type w)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) :
    HasDirichletDensity K
      (primesWithFrobInSet K L (ConjClasses.mk σ).carrier)
      ((Set.toFinite (ConjClasses.mk σ).carrier).toFinset.card /
        ((Subgroup.zpowers σ).index * orderOf σ : ℚ)) := by

  let E := IntermediateField.fixedField (Subgroup.zpowers σ)
  haveI : NumberField E := NumberField.of_intermediateField E

  have h_abelian := abelianDensity_fixedField K L σ

  exact dirichletSeries_conjClass_comparison K L σ h_abelian

theorem conjClass_hasDirichletDensity (K : Type w) (L : Type w)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (σ : L ≃ₐ[K] L) :
    HasDirichletDensity K
      (primesWithFrobInSet K L (ConjClasses.mk σ).carrier)
      ((Set.toFinite (ConjClasses.mk σ).carrier).toFinset.card /
        (Fintype.card (L ≃ₐ[K] L) : ℚ)) := by


  have h_intermediate := conjClass_density_intermediate K L σ

  set G_card := Fintype.card (L ≃ₐ[K] L) with hG_card_def
  set Hσ := Subgroup.zpowers σ with hHσ_def
  have h_lagrange : (Hσ.index : ℚ) * (orderOf σ : ℚ) = (G_card : ℚ) := by
    have : Hσ.index * orderOf σ = G_card := by
      rw [← Nat.card_zpowers σ]
      rw [Subgroup.index_mul_card Hσ]
      exact @Nat.card_eq_fintype_card (L ≃ₐ[K] L) _
    exact_mod_cast this

  suffices h_eq : (↑(Set.toFinite (ConjClasses.mk σ).carrier).toFinset.card : ℚ) /
      (↑G_card : ℚ) =
    (↑(Set.toFinite (ConjClasses.mk σ).carrier).toFinset.card : ℚ) /
      ((Hσ.index : ℚ) * (orderOf σ : ℚ)) by
    rw [h_eq]
    exact h_intermediate
  congr 1
  exact h_lagrange.symm

set_option maxHeartbeats 800000 in
theorem dirichletDensity_disjoint_union (K : Type w) (L : Type w)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (A B : Set (L ≃ₐ[K] L))
    (hA : IsConjugationStable A) (hB : IsConjugationStable B)
    (h_disj : Disjoint A B)
    (dA dB : ℚ)
    (hdA : HasDirichletDensity K (primesWithFrobInSet K L A) dA)
    (hdB : HasDirichletDensity K (primesWithFrobInSet K L B) dB) :
    HasDirichletDensity K (primesWithFrobInSet K L (A ∪ B)) (dA + dB) := by


  have h_set : primesWithFrobInSet K L (A ∪ B) =
      primesWithFrobInSet K L A ∪ primesWithFrobInSet K L B := by
    ext 𝔭
    simp only [primesWithFrobInSet, Set.mem_setOf_eq, Set.mem_union]
    constructor
    · rintro ⟨h_unram, h_sub⟩
      obtain ⟨σ, hσ⟩ := FrobeniusConjClass.nonempty K L 𝔭 h_unram

      have frob_conj : ∀ τ, τ ∈ FrobeniusConjClass K L 𝔭 →
          ∃ g : L ≃ₐ[K] L, τ = g * σ * g⁻¹ := by
        intro τ hτ
        obtain ⟨𝔔₁, h𝔔₁_prime, h𝔔₁_over, h𝔔₁_frob⟩ := hσ
        obtain ⟨𝔔₂, h𝔔₂_prime, h𝔔₂_over, h𝔔₂_frob⟩ := hτ
        haveI : 𝔔₁.IsPrime := h𝔔₁_prime
        haveI : 𝔔₂.IsPrime := h𝔔₂_prime

        have h_under_eq : 𝔔₁.under (RingOfIntegers K) = 𝔔₂.under (RingOfIntegers K) := by
          rw [← h𝔔₁_over.over, ← h𝔔₂_over.over]

        obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq
          (RingOfIntegers K) (RingOfIntegers L) (L ≃ₐ[K] L) 𝔔₁ 𝔔₂ h_under_eq

        have h_conj_frob : IsArithFrobAt (RingOfIntegers K) (g * σ * g⁻¹) 𝔔₂ :=
          hg ▸ h𝔔₁_frob.conj g

        haveI : Algebra.IsUnramifiedAt (RingOfIntegers K) 𝔔₂ := h_unram 𝔔₂ h𝔔₂_over
        have hQ : 𝔔₂.primeCompl ≤ nonZeroDivisors (RingOfIntegers L) :=
          Ideal.primeCompl_le_nonZeroDivisors 𝔔₂
        have h_alg_eq := h𝔔₂_frob.eq_of_isUnramifiedAt h_conj_frob hQ
        haveI : FaithfulSMul (L ≃ₐ[K] L) (RingOfIntegers L) := by
          constructor
          intro σ' τ' h'
          have hL : ∀ (a : RingOfIntegers L), σ' (a : L) = τ' (a : L) :=
            fun a => congr_arg Subtype.val (h' a)
          have h_ring : σ'.toRingHom.comp (algebraMap (RingOfIntegers L) L) =
              τ'.toRingHom.comp (algebraMap (RingOfIntegers L) L) :=
            RingHom.ext fun a => hL a
          exact AlgEquiv.ext fun x => RingHom.congr_fun
            (IsLocalization.ringHom_ext (nonZeroDivisors (RingOfIntegers L)) h_ring) x
        exact ⟨g, MulSemiringAction.toAlgHom_injective
          (RingOfIntegers K) (RingOfIntegers L) h_alg_eq⟩
      cases h_sub hσ with
      | inl hσ_A =>
        left; exact ⟨h_unram, fun τ hτ => by
          obtain ⟨g, hg⟩ := frob_conj τ hτ; rw [hg]; exact hA g σ hσ_A⟩
      | inr hσ_B =>
        right; exact ⟨h_unram, fun τ hτ => by
          obtain ⟨g, hg⟩ := frob_conj τ hτ; rw [hg]; exact hB g σ hσ_B⟩
    · rintro (⟨h_unram, h_sub_A⟩ | ⟨h_unram, h_sub_B⟩)
      · exact ⟨h_unram, h_sub_A.trans Set.subset_union_left⟩
      · exact ⟨h_unram, h_sub_B.trans Set.subset_union_right⟩

  have h_disj_primes : Disjoint (primesWithFrobInSet K L A) (primesWithFrobInSet K L B) := by
    rw [Set.disjoint_iff]
    intro 𝔭 ⟨h𝔭_A, h𝔭_B⟩
    obtain ⟨h_unram, h_sub_A⟩ := h𝔭_A
    obtain ⟨_, h_sub_B⟩ := h𝔭_B
    obtain ⟨σ, hσ⟩ := FrobeniusConjClass.nonempty K L 𝔭 h_unram
    exact Set.disjoint_iff.mp h_disj ⟨h_sub_A hσ, h_sub_B hσ⟩

  rw [h_set]
  show HasDirichletDensity K
    (primesWithFrobInSet K L A ∪ primesWithFrobInSet K L B) (dA + dB)
  unfold HasDirichletDensity
  rw [show ((dA + dB : ℚ) : ℝ) = (↑dA : ℝ) + (↑dB : ℝ) from by push_cast; ring]


  have h_ev_eq : ∀ᶠ s in nhdsWithin 1 (Set.Ioi 1),
      (fun s => (∑' (𝔭 : ↑(primesWithFrobInSet K L A)),
          ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) /
          Real.log (1 / (s - 1)) +
        (∑' (𝔭 : ↑(primesWithFrobInSet K L B)),
          ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) /
          Real.log (1 / (s - 1))) s =
      (fun s => (∑' (𝔭 : ↑(primesWithFrobInSet K L A ∪ primesWithFrobInSet K L B)),
          ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s))) /
          Real.log (1 / (s - 1))) s := by
    apply Filter.eventually_of_mem self_mem_nhdsWithin
    intro s (hs : 1 < s)
    dsimp only
    rw [← add_div]
    congr 1
    let f : Prime' K → ℝ := fun 𝔭 => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)
    have hsumA : Summable (f ∘ Subtype.val (p := (· ∈ primesWithFrobInSet K L A))) :=
      summable_rpow_inv_absNorm_prime (primesWithFrobInSet K L A) s hs
    have hsumB : Summable (f ∘ Subtype.val (p := (· ∈ primesWithFrobInSet K L B))) :=
      summable_rpow_inv_absNorm_prime (primesWithFrobInSet K L B) s hs
    exact (Summable.tsum_union_disjoint h_disj_primes hsumA hsumB).symm
  exact (Filter.Tendsto.add hdA hdB).congr' h_ev_eq
theorem primesWithFrobInSet_empty_hasDensity_zero (K : Type w) (L : Type w)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    HasDirichletDensity K (primesWithFrobInSet K L ∅) 0 := by

  have h_empty : primesWithFrobInSet K L ∅ = ∅ := by
    ext 𝔭
    simp only [primesWithFrobInSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro h_unram h_sub
    exact (FrobeniusConjClass.nonempty K L 𝔭 h_unram).ne_empty (Set.subset_empty_iff.mp h_sub)

  unfold HasDirichletDensity

  have h_tsum : ∀ s : ℝ, ∑' (𝔭 : ↥(primesWithFrobInSet K L ∅)),
      ((Ideal.absNorm (𝔭 : Prime' K).asIdeal : ℝ) ^ (-s)) = 0 := by
    intro s
    rw [h_empty]
    exact tsum_empty
  simp_rw [h_tsum, zero_div]
  simp only [Rat.cast_zero]
  exact tendsto_const_nhds

lemma conjClass_subset_of_mem_conjStable {G : Type*} [Group G]
    (C : Set G) (hC : IsConjugationStable C) (σ : G) (hσ : σ ∈ C) :
    (ConjClasses.mk σ).carrier ⊆ C := by
  intro τ hτ
  rw [ConjClasses.mem_carrier_iff_mk_eq] at hτ
  have hconj : IsConj τ σ := ConjClasses.mk_eq_mk_iff_isConj.mp hτ
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj

  have h1 : τ = g⁻¹ * σ * (g⁻¹)⁻¹ := by
    calc τ = g⁻¹ * (g * τ * g⁻¹) * (g⁻¹)⁻¹ := by group
    _ = g⁻¹ * σ * (g⁻¹)⁻¹ := by rw [hg]
  rw [h1]
  exact hC g⁻¹ σ hσ

lemma conjStable_sdiff {G : Type*} [Group G]
    (C : Set G) (hC : IsConjugationStable C) (σ : G) :
    IsConjugationStable (C \ (ConjClasses.mk σ).carrier) := by
  intro g c ⟨hcC, hcCC⟩
  refine ⟨hC g c hcC, ?_⟩
  intro hmem
  apply hcCC
  rw [ConjClasses.mem_carrier_iff_mk_eq] at hmem ⊢
  rw [← hmem]
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g, rfl⟩)

theorem theorem_28_9_chebotarev (K : Type w) (L : Type w)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (C : Set (L ≃ₐ[K] L))
    (hC : IsConjugationStable C)
    (hC_finite : Set.Finite C) :
    DirichletDensity K (primesWithFrobInSet K L C) =
    some (hC_finite.toFinset.card / (Fintype.card (L ≃ₐ[K] L) : ℚ)) := by
  classical

  rw [dirichletDensity_eq_some_iff]

  have : ∀ (n : ℕ) (C : Set (L ≃ₐ[K] L)) (hC : IsConjugationStable C)
      (hC_finite : Set.Finite C), hC_finite.toFinset.card = n →
      HasDirichletDensity K (primesWithFrobInSet K L C)
        (hC_finite.toFinset.card / (Fintype.card (L ≃ₐ[K] L) : ℚ)) := by
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
    intro C hC hC_finite h_card
    by_cases h_empty : C = ∅
    ·
      subst h_empty
      convert primesWithFrobInSet_empty_hasDensity_zero K L using 1
      simp only [Set.Finite.toFinset_empty, Finset.card_empty, Nat.cast_zero, zero_div]

    ·
      obtain ⟨σ, hσ⟩ := Set.nonempty_iff_ne_empty.mpr h_empty

      set CC := (ConjClasses.mk σ).carrier with hCC_def

      set C' := C \ CC with hC'_def

      have hCC_sub : CC ⊆ C := conjClass_subset_of_mem_conjStable C hC σ hσ
      have hC'_stable : IsConjugationStable C' := conjStable_sdiff C hC σ
      have hCC_stable : IsConjugationStable CC := by
        intro g c hcCC
        rw [ConjClasses.mem_carrier_iff_mk_eq] at hcCC ⊢
        rw [← hcCC]
        exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g⁻¹, by group⟩)
      have h_disj : Disjoint CC C' := by
        rw [Set.disjoint_iff]
        intro x ⟨hx1, hx2⟩
        exact hx2.2 hx1
      have h_union : C = CC ∪ C' := by
        ext x
        simp only [Set.mem_union, Set.mem_diff, hC'_def]
        constructor
        · intro hx
          by_cases hxCC : x ∈ CC
          · left; exact hxCC
          · right; exact ⟨hx, hxCC⟩
        · rintro (hx | ⟨hx, -⟩)
          · exact hCC_sub hx
          · exact hx

      have hCC_finite : Set.Finite CC := Set.toFinite CC
      have hC'_finite : Set.Finite C' := hC_finite.subset Set.diff_subset

      have hσ_mem_CC : σ ∈ CC := ConjClasses.mem_carrier_mk
      have hCC_nonempty : CC.Nonempty := ⟨σ, hσ_mem_CC⟩
      have hCC_card_pos : 0 < hCC_finite.toFinset.card := by
        rw [Finset.card_pos]
        exact ⟨σ, hCC_finite.mem_toFinset.mpr hσ_mem_CC⟩

      have h_card_sum : hC_finite.toFinset.card =
          hCC_finite.toFinset.card + hC'_finite.toFinset.card := by
        have h1 : hC_finite.toFinset = hCC_finite.toFinset ∪ hC'_finite.toFinset := by
          ext x
          simp only [Set.Finite.mem_toFinset, Finset.mem_union]
          constructor
          · intro hx
            by_cases hxCC : x ∈ CC
            · left; exact hxCC
            · right; exact ⟨hx, hxCC⟩
          · rintro (hx | ⟨hx, -⟩)
            · exact hCC_sub hx
            · exact hx
        have h2 : Disjoint hCC_finite.toFinset hC'_finite.toFinset := by
          rw [Finset.disjoint_iff_ne]
          intro a ha b hb hab
          subst hab
          have : a ∈ CC := hCC_finite.mem_toFinset.mp ha
          have : a ∈ C' := hC'_finite.mem_toFinset.mp hb
          exact this.2 ‹a ∈ CC›
        rw [h1, Finset.card_union_of_disjoint h2]
      have h_card_C' : hC'_finite.toFinset.card < n := by
        omega

      have ih_C' := ih hC'_finite.toFinset.card h_card_C' C' hC'_stable hC'_finite rfl

      have h_CC_dens := conjClass_hasDirichletDensity K L σ

      have hCC_finset_eq : hCC_finite.toFinset.card =
          (Set.toFinite (ConjClasses.mk σ).carrier).toFinset.card := by
        congr 1

      have h_combined := dirichletDensity_disjoint_union K L CC C'
        hCC_stable hC'_stable h_disj _ _ h_CC_dens ih_C'


      have h_val : (hC_finite.toFinset.card : ℚ) / (Fintype.card (L ≃ₐ[K] L) : ℚ) =
          (Set.toFinite (ConjClasses.mk σ).carrier).toFinset.card /
            (Fintype.card (L ≃ₐ[K] L) : ℚ) +
          hC'_finite.toFinset.card / (Fintype.card (L ≃ₐ[K] L) : ℚ) := by
        rw [← add_div]
        congr 1
        rw [← hCC_finset_eq]; exact_mod_cast h_card_sum
      rw [h_val, h_union]
      exact h_combined

  exact this _ C hC hC_finite rfl

theorem corollary_28_11 (K : Type w) (L : Type w)
    [Field K] [Field L] [NumberField K] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    (hcomm : ∀ a b : L ≃ₐ[K] L, a * b = b * a)
    (σ : L ≃ₐ[K] L) :
    DirichletDensity K (primesWithFrobInSet K L {σ}) =
    some (1 / (Fintype.card (L ≃ₐ[K] L) : ℚ)) := by

  have hC : IsConjugationStable ({σ} : Set (L ≃ₐ[K] L)) := by
    intro g c hc
    simp only [Set.mem_singleton_iff] at hc ⊢
    rw [hc]
    calc g * σ * g⁻¹ = σ * g * g⁻¹ := by rw [hcomm g σ]
      _ = σ * (g * g⁻¹) := by rw [mul_assoc]
      _ = σ * 1 := by rw [mul_inv_cancel]
      _ = σ := by rw [mul_one]

  have hC_finite : Set.Finite ({σ} : Set (L ≃ₐ[K] L)) := Set.finite_singleton σ

  have h := theorem_28_9_chebotarev K L {σ} hC hC_finite

  have hcard : hC_finite.toFinset.card = 1 := by
    rw [Set.Finite.toFinset_singleton]
    exact Finset.card_singleton σ
  rw [h, hcard]
  norm_cast

end Chebotarev

section Functoriality

variable {K : Type*} [Field K] [NumberField K]
  {L : Type*} [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

open Ideles

structure GlobalArtinFunctoriality
    (θK : GlobalArtinMap K) (θL : GlobalArtinMap L) where
  transfer : θL.GalAb →* θK.GalAb
  transfer_continuous : Continuous transfer
  artinMap_comm : ∀ (a : IdeleGroup L),
    θK.artinHom (ideleNorm K L a) = transfer (θL.artinHom a)

def theorem_28_8_functoriality
    (θK : GlobalArtinMap K) (θL : GlobalArtinMap L) :
    GlobalArtinFunctoriality θK θL := sorry

def GlobalArtinMap.transferMap
    (θK : GlobalArtinMap K) (θL : GlobalArtinMap L) :
    θL.GalAb →* θK.GalAb :=
  (theorem_28_8_functoriality θK θL).transfer

theorem theorem_28_8_comm
    (θK : GlobalArtinMap K) (θL : GlobalArtinMap L)
    (a : IdeleGroup L) :
    θK.artinHom (ideleNorm K L a) = (θK.transferMap θL) (θL.artinHom a) :=
  (theorem_28_8_functoriality θK θL).artinMap_comm a

theorem theorem_28_8_comm_classGroup
    (θK : GlobalArtinMap K) (θL : GlobalArtinMap L)
    (a : IdeleClassGroup L) :
    θK.artinHomCK (ideleNormCK K L a) =
      (θK.transferMap θL) (θL.artinHomCK a) := by

  obtain ⟨a₀, rfl⟩ := QuotientGroup.mk_surjective a
  rw [ideleNormCK_compat K L a₀]
  rw [GlobalArtinMap.artinHomCK_comp θK]
  rw [GlobalArtinMap.artinHomCK_comp θL]
  exact theorem_28_8_comm θK θL a₀

end Functoriality

section ArtinMapGaloisCorrespondence

open Ideles

variable {K : Type*} [Field K] [NumberField K]

theorem normSubgroup_finiteIndex (θ : GlobalArtinMap K) (i : θ.I) :
    (θ.normSubgroupCK i).FiniteIndex := by

  have hker : MonoidHom.ker (θ.artinMapCK i) = θ.normSubgroupCK i :=
    theorem_28_4_ker_eq_norm θ i
  rw [← hker]

  exact Subgroup.finiteIndex_ker (θ.artinMapCK i)

theorem normSubgroup_surjective (θ : GlobalArtinMap K)
    (H : Subgroup (IdeleClassGroup K))
    (hopen : IsOpen (H : Set (IdeleClassGroup K)))
    (hfin : H.FiniteIndex) :
    ∃ i : θ.I, θ.normSubgroupCK i = H :=
  let ⟨i, hi, _⟩ := theorem_28_6_global_existence θ H hopen hfin
  ⟨i, hi⟩

theorem artinMap_quotient_iso (θ : GlobalArtinMap K) (i : θ.I) :
    Nonempty (IdeleClassGroup K ⧸ θ.normSubgroupCK i ≃* θ.GalLK i) :=
  theorem_28_4_iso θ i

theorem globalCFT_main_theorem (θ : GlobalArtinMap K) :

    (∀ i : θ.I, (θ.normSubgroupCK i).FiniteIndex) ∧

    (∀ H : Subgroup (IdeleClassGroup K),
      IsOpen (H : Set (IdeleClassGroup K)) → H.FiniteIndex →
        ∃ i : θ.I, θ.normSubgroupCK i = H) ∧

    (∀ i : θ.I,
      Nonempty (IdeleClassGroup K ⧸ θ.normSubgroupCK i ≃* θ.GalLK i)) :=
  ⟨normSubgroup_finiteIndex θ,
   normSubgroup_surjective θ,
   artinMap_quotient_iso θ⟩

end ArtinMapGaloisCorrespondence

end
