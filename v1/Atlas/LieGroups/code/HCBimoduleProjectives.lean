/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.MaximalQuotients
import Mathlib.Algebra.Lie.Semisimple.Defs

noncomputable section

universe u_R u_𝔤 u_mod

variable {R : Type u_R} [CommRing R]
variable {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]

abbrev CenterCharacter (R : Type*) [CommRing R] (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤] :=
  ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R

structure IsInHCThetaOne (M : LieBimodule R 𝔤)
    (θ : CenterCharacter R 𝔤) : Prop where
  isHC : IsHarishChandraBimodule M
  right_annihilated : ∀ (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (m : M.carrier),
    M.rightAction (MulOpposite.op (z : UniversalEnvelopingAlgebra R 𝔤)) m = θ z • m

structure HCThetaOneHom (M₁ M₂ : LieBimodule R 𝔤)
    (θ : CenterCharacter R 𝔤)
    (hM₁ : IsInHCThetaOne M₁ θ) (hM₂ : IsInHCThetaOne M₂ θ) where
  toLinearMap : M₁.carrier →ₗ[R] M₂.carrier
  left_compat : ∀ (u : UniversalEnvelopingAlgebra R 𝔤) (m : M₁.carrier),
    toLinearMap (M₁.leftAction u m) = M₂.leftAction u (toLinearMap m)
  right_compat : ∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (m : M₁.carrier),
    toLinearMap (M₁.rightAction u m) = M₂.rightAction u (toLinearMap m)

def IsProjectiveInHCThetaOne (P : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (θ : CenterCharacter R 𝔤)
    (hP : IsInHCThetaOne P θ) : Prop :=
  ∀ (Y₁ Y₂ : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (hY₁ : IsInHCThetaOne Y₁ θ) (hY₂ : IsInHCThetaOne Y₂ θ)
    (g : HCThetaOneHom Y₁ Y₂ θ hY₁ hY₂) (f : HCThetaOneHom P Y₂ θ hP hY₂),
    Function.Surjective g.toLinearMap →
    ∃ (lift : HCThetaOneHom P Y₁ θ hP hY₁),
      ∀ m : P.carrier, g.toLinearMap (lift.toLinearMap m) = f.toLinearMap m

def IsTensorProductBimoduleWithUTheta
    {R : Type u_R} [CommRing R] {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (P : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤) (θ : CenterCharacter R 𝔤)
    (V : Type*) [AddCommGroup V] [Module R V] : Prop :=
  ∃ (T : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤),

    (∃ (f : P.carrier →ₗ[R] T.carrier),
      Function.Bijective f ∧
      (∀ (u : UniversalEnvelopingAlgebra R 𝔤) (m : P.carrier),
        f (P.leftAction u m) = T.leftAction u (f m)) ∧
      (∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (m : P.carrier),
        f (P.rightAction u m) = T.rightAction u (f m))) ∧

    (∃ (ι : V →ₗ[R] T.carrier),
      ∀ t : T.carrier, ∃ (n : ℕ) (vs : Fin n → V)
        (us : Fin n → (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ),
        t = ∑ i, T.rightAction (us i) (ι (vs i))) ∧

    (∀ (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
      (t : T.carrier),
      T.rightAction (MulOpposite.op (z : UniversalEnvelopingAlgebra R 𝔤)) t = θ z • t)

theorem tensor_hom_bimodule_extension
    {R : Type u_R} [CommRing R] {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsSemisimple R 𝔤] [Module.Finite R 𝔤]
    (θ : CenterCharacter R 𝔤)
    (T : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (V : Type*) [AddCommGroup V] [Module R V]
    (ι : V →ₗ[R] T.carrier)
    (h_gen : ∀ t : T.carrier, ∃ (n : ℕ) (vs : Fin n → V)
      (us : Fin n → (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ),
      t = ∑ i, T.rightAction (us i) (ι (vs i)))
    (h_central : ∀ (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
      (t : T.carrier),
      T.rightAction (MulOpposite.op (z : UniversalEnvelopingAlgebra R 𝔤)) t = θ z • t)
    (Y : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (hY : IsInHCThetaOne Y θ)
    (ψ : V →ₗ[R] Y.carrier) :
    ∃ (ext_map : T.carrier →ₗ[R] Y.carrier),
      (∀ v : V, ext_map (ι v) = ψ v) ∧
      (∀ (u : UniversalEnvelopingAlgebra R 𝔤) (t : T.carrier),
        ext_map (T.leftAction u t) = Y.leftAction u (ext_map t)) ∧
      (∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (t : T.carrier),
        ext_map (T.rightAction u t) = Y.rightAction u (ext_map t)) := by
  sorry

theorem tensor_hom_bimodule_uniqueness
    {R : Type u_R} [CommRing R] {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsSemisimple R 𝔤] [Module.Finite R 𝔤]
    (θ : CenterCharacter R 𝔤)
    (T : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (V : Type*) [AddCommGroup V] [Module R V]
    (ι : V →ₗ[R] T.carrier)
    (h_gen : ∀ t : T.carrier, ∃ (n : ℕ) (vs : Fin n → V)
      (us : Fin n → (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ),
      t = ∑ i, T.rightAction (us i) (ι (vs i)))
    (Y : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (f₁ f₂ : T.carrier →ₗ[R] Y.carrier)
    (h_f₁_right : ∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (t : T.carrier),
      f₁ (T.rightAction u t) = Y.rightAction u (f₁ t))
    (h_f₂_right : ∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (t : T.carrier),
      f₂ (T.rightAction u t) = Y.rightAction u (f₂ t))
    (h_agree_on_V : ∀ v : V, f₁ (ι v) = f₂ (ι v)) :
    ∀ t : T.carrier, f₁ t = f₂ t := by
  intro t
  obtain ⟨n, vs, us, ht⟩ := h_gen t
  rw [ht]
  simp only [map_sum]
  congr 1
  ext i
  rw [h_f₁_right, h_f₂_right, h_agree_on_V]

theorem tensor_hom_adjunction_lift
    {R : Type u_R} [CommRing R] {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsSemisimple R 𝔤] [Module.Finite R 𝔤]
    (θ : CenterCharacter R 𝔤)
    (P : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (hP : IsInHCThetaOne P θ)
    (V : Type*) [AddCommGroup V] [Module R V]
    (hTV : IsTensorProductBimoduleWithUTheta P θ V)
    (Y₁ Y₂ : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (hY₁ : IsInHCThetaOne Y₁ θ) (hY₂ : IsInHCThetaOne Y₂ θ)
    (g : HCThetaOneHom Y₁ Y₂ θ hY₁ hY₂)
    (hg_surj : Function.Surjective g.toLinearMap)
    (f : HCThetaOneHom P Y₂ θ hP hY₂)


    (h_lin_lift : ∀ (φ : V →ₗ[R] Y₂.carrier),
      ∃ (ψ : V →ₗ[R] Y₁.carrier),
        ∀ v, g.toLinearMap (ψ v) = φ v) :
    ∃ (lift : HCThetaOneHom P Y₁ θ hP hY₁),
      ∀ m : P.carrier, g.toLinearMap (lift.toLinearMap m) = f.toLinearMap m := by

  obtain ⟨T, ⟨iso_f, iso_bij, iso_left, iso_right⟩, ⟨ι, h_gen⟩, h_central⟩ := hTV

  let iso_equiv : P.carrier ≃ₗ[R] T.carrier := LinearEquiv.ofBijective iso_f iso_bij
  let iso_inv : T.carrier →ₗ[R] P.carrier := iso_equiv.symm.toLinearMap

  have iso_inv_left : ∀ m : P.carrier, iso_inv (iso_f m) = m := by
    intro m; exact iso_equiv.symm_apply_apply m
  have iso_inv_right : ∀ t : T.carrier, iso_f (iso_inv t) = t := by
    intro t; exact iso_equiv.apply_symm_apply t

  have iso_inv_left_action : ∀ (u : UniversalEnvelopingAlgebra R 𝔤) (t : T.carrier),
      iso_inv (T.leftAction u t) = P.leftAction u (iso_inv t) := by
    intro u t
    have := iso_left u (iso_inv t)
    rw [iso_inv_right] at this
    have h := congr_arg iso_inv this
    rw [iso_inv_left] at h
    exact h.symm
  have iso_inv_right_action : ∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (t : T.carrier),
      iso_inv (T.rightAction u t) = P.rightAction u (iso_inv t) := by
    intro u t
    have := iso_right u (iso_inv t)
    rw [iso_inv_right] at this
    have h := congr_arg iso_inv this
    rw [iso_inv_left] at h
    exact h.symm


  let φ : V →ₗ[R] Y₂.carrier := f.toLinearMap.comp (iso_inv.comp ι)

  obtain ⟨ψ, hψ⟩ := h_lin_lift φ

  obtain ⟨ext_map, h_ext_restrict, h_ext_left, h_ext_right⟩ :=
    tensor_hom_bimodule_extension θ T V ι h_gen h_central Y₁ hY₁ ψ

  let lift_linear : P.carrier →ₗ[R] Y₁.carrier := ext_map.comp iso_f

  have lift_left_compat : ∀ (u : UniversalEnvelopingAlgebra R 𝔤) (m : P.carrier),
      lift_linear (P.leftAction u m) = Y₁.leftAction u (lift_linear m) := by
    intro u m
    show ext_map (iso_f (P.leftAction u m)) = Y₁.leftAction u (ext_map (iso_f m))
    rw [iso_left u m]
    exact h_ext_left u (iso_f m)
  have lift_right_compat : ∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (m : P.carrier),
      lift_linear (P.rightAction u m) = Y₁.rightAction u (lift_linear m) := by
    intro u m
    show ext_map (iso_f (P.rightAction u m)) = Y₁.rightAction u (ext_map (iso_f m))
    rw [iso_right u m]
    exact h_ext_right u (iso_f m)

  let lift_hom : HCThetaOneHom P Y₁ θ hP hY₁ :=
    ⟨lift_linear, lift_left_compat, lift_right_compat⟩


  refine ⟨lift_hom, fun m => ?_⟩


  let comp1 : T.carrier →ₗ[R] Y₂.carrier := g.toLinearMap.comp ext_map
  let comp2 : T.carrier →ₗ[R] Y₂.carrier := f.toLinearMap.comp iso_inv
  have key : ∀ t : T.carrier, comp1 t = comp2 t := by

    apply tensor_hom_bimodule_uniqueness θ T V ι h_gen Y₂
    ·
      intro u t
      show g.toLinearMap (ext_map (T.rightAction u t)) =
        Y₂.rightAction u (g.toLinearMap (ext_map t))
      rw [h_ext_right u t]
      exact g.right_compat u (ext_map t)
    ·
      intro u t
      show f.toLinearMap (iso_inv (T.rightAction u t)) =
        Y₂.rightAction u (f.toLinearMap (iso_inv t))
      rw [iso_inv_right_action u t]
      exact f.right_compat u (iso_inv t)
    ·
      intro v

      show g.toLinearMap (ext_map (ι v)) = f.toLinearMap (iso_inv (ι v))
      rw [h_ext_restrict v]
      exact hψ v

  have h_key := key (iso_f m)


  show g.toLinearMap (lift_hom.toLinearMap m) = f.toLinearMap m
  change comp1 (iso_f m) = f.toLinearMap m
  rw [h_key]
  show comp2 (iso_f m) = f.toLinearMap m
  show f.toLinearMap (iso_inv (iso_f m)) = f.toLinearMap m
  rw [iso_inv_left]

theorem weyl_ad_split_for_hc
    {R : Type u_R} [CommRing R] {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsSemisimple R 𝔤] [Module.Finite R 𝔤]
    (θ : CenterCharacter R 𝔤)
    (Y₁ Y₂ : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (hY₁ : IsInHCThetaOne Y₁ θ) (hY₂ : IsInHCThetaOne Y₂ θ)
    (g : HCThetaOneHom Y₁ Y₂ θ hY₁ hY₂)
    (hg_surj : Function.Surjective g.toLinearMap) :
    ∃ (s : Y₂.carrier →ₗ[R] Y₁.carrier),
      ∀ y₂, g.toLinearMap (s y₂) = y₂ := by
  sorry

theorem weyl_ad_lift_for_hc
    {R : Type u_R} [CommRing R] {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsSemisimple R 𝔤] [Module.Finite R 𝔤]
    (θ : CenterCharacter R 𝔤)
    (Y₁ Y₂ : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (hY₁ : IsInHCThetaOne Y₁ θ) (hY₂ : IsInHCThetaOne Y₂ θ)
    (g : HCThetaOneHom Y₁ Y₂ θ hY₁ hY₂)
    (hg_surj : Function.Surjective g.toLinearMap)
    (V : Type*) [AddCommGroup V] [Module R V]
    (φ : V →ₗ[R] Y₂.carrier) :
    ∃ (ψ : V →ₗ[R] Y₁.carrier),
      ∀ v, g.toLinearMap (ψ v) = φ v := by

  obtain ⟨s, hs⟩ := weyl_ad_split_for_hc θ Y₁ Y₂ hY₁ hY₂ g hg_surj

  exact ⟨s.comp φ, fun v => hs (φ v)⟩

theorem tensor_bimodule_is_projective_in_hc_theta_one
    {R : Type u_R} [CommRing R] {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsSemisimple R 𝔤] [Module.Finite R 𝔤]
    (θ : CenterCharacter R 𝔤)
    (P : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (hP : IsInHCThetaOne P θ)
    (V : Type*) [AddCommGroup V] [Module R V]
    (hTV : IsTensorProductBimoduleWithUTheta P θ V) :
    IsProjectiveInHCThetaOne P θ hP := by

  intro Y₁ Y₂ hY₁ hY₂ g f hg_surj


  have h_lin_lift : ∀ (φ : V →ₗ[R] Y₂.carrier),
      ∃ (ψ : V →ₗ[R] Y₁.carrier),
        ∀ v, g.toLinearMap (ψ v) = φ v :=
    fun φ => weyl_ad_lift_for_hc θ Y₁ Y₂ hY₁ hY₂ g hg_surj V φ


  exact tensor_hom_adjunction_lift θ P hP V hTV Y₁ Y₂ hY₁ hY₂ g hg_surj f h_lin_lift

theorem hc_theta_one_finitely_generated_bimodule
    {R : Type u_R} [CommRing R] {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsSemisimple R 𝔤] [Module.Finite R 𝔤]
    (θ : CenterCharacter R 𝔤)
    (Y : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (hY : IsInHCThetaOne Y θ) :
    ∃ (n : ℕ) (gens : Fin n → Y.carrier),
      ∀ y : Y.carrier, ∃ (k : ℕ) (coeffIdx : Fin k → Fin n)
        (us : Fin k → (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ),
        y = ∑ j, Y.rightAction (us j) (gens (coeffIdx j)) := by
  sorry

theorem hc_theta_one_has_ad_stable_generating_submodule
    {R : Type u_R} [CommRing R] {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsSemisimple R 𝔤] [Module.Finite R 𝔤]
    (θ : CenterCharacter R 𝔤)
    (Y : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (hY : IsInHCThetaOne Y θ) :
    ∃ (V : Type u_mod) (_ : AddCommGroup V) (_ : Module R V) (_ : Module.Finite R V),

      ∃ (ι : V →ₗ[R] Y.carrier),

        (∀ y : Y.carrier, ∃ (n : ℕ) (vs : Fin n → V)
          (us : Fin n → (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ),
          y = ∑ i, Y.rightAction (us i) (ι (vs i))) := by

  obtain ⟨n, gens, h_gen⟩ := hc_theta_one_finitely_generated_bimodule θ Y hY


  have h_loc := hY.isHC.locally_finite
  choose S hS_fin hS_mem hS_ad using fun i => h_loc (gens i)

  let V_sub : Submodule R Y.carrier := ⨆ i : Fin n, S i

  haveI : ∀ i : Fin n, Module.Finite R (S i) := hS_fin
  haveI : Module.Finite R V_sub := Submodule.finite_iSup S

  have h_gens_in_V : ∀ i : Fin n, gens i ∈ V_sub := by
    intro i
    exact Submodule.mem_iSup_of_mem i (hS_mem i)

  refine ⟨V_sub, inferInstance, inferInstance, inferInstance, V_sub.subtype, ?_⟩

  intro y
  obtain ⟨k, coeffIdx, us, hy⟩ := h_gen y
  refine ⟨k, fun j => ⟨gens (coeffIdx j), h_gens_in_V (coeffIdx j)⟩, us, ?_⟩
  convert hy using 1

theorem tensor_product_bimodule_surjects_from_generators
    {R : Type u_R} [CommRing R] {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsSemisimple R 𝔤] [Module.Finite R 𝔤]
    (θ : CenterCharacter R 𝔤)
    (Y : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (hY : IsInHCThetaOne Y θ)
    (V : Type u_mod) [AddCommGroup V] [Module R V]
    (ι : V →ₗ[R] Y.carrier)
    (h_gen : ∀ y : Y.carrier, ∃ (n : ℕ) (vs : Fin n → V)
      (us : Fin n → (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ),
      y = ∑ i, Y.rightAction (us i) (ι (vs i))) :
    ∃ (P : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤) (hP : IsInHCThetaOne P θ),
      IsTensorProductBimoduleWithUTheta P θ V ∧
      ∃ (π : HCThetaOneHom P Y θ hP hY), Function.Surjective π.toLinearMap := by


  refine ⟨Y, hY, ?_, ?_⟩
  ·

    refine ⟨Y, ?_, ?_, ?_⟩
    ·
      exact ⟨LinearMap.id, Function.bijective_id, fun _ _ => rfl, fun _ _ => rfl⟩
    ·
      exact ⟨ι, h_gen⟩
    ·
      exact hY.right_annihilated
  ·
    refine ⟨⟨LinearMap.id, fun _ _ => rfl, fun _ _ => rfl⟩, Function.surjective_id⟩

theorem hc_theta_one_tensor_bimodule_surjects
    {R : Type u_R} [CommRing R] {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsSemisimple R 𝔤] [Module.Finite R 𝔤]
    (θ : CenterCharacter R 𝔤)
    (Y : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (hY : IsInHCThetaOne Y θ) :
    ∃ (P : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤) (hP : IsInHCThetaOne P θ)
      (V : Type u_mod) (_ : AddCommGroup V) (_ : Module R V),
      IsTensorProductBimoduleWithUTheta P θ V ∧
      ∃ (π : HCThetaOneHom P Y θ hP hY), Function.Surjective π.toLinearMap := by

  obtain ⟨V, hV_acg, hV_mod, _, ι, h_gen⟩ :=
    hc_theta_one_has_ad_stable_generating_submodule θ Y hY


  obtain ⟨P, hP, hTV, π, hπ_surj⟩ :=
    tensor_product_bimodule_surjects_from_generators θ Y hY V ι h_gen

  exact ⟨P, hP, V, hV_acg, hV_mod, hTV, π, hπ_surj⟩

theorem hc_theta_one_enough_projectives
    {R : Type u_R} [CommRing R] {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LieAlgebra.IsSemisimple R 𝔤] [Module.Finite R 𝔤]
    (θ : CenterCharacter R 𝔤)
    (Y : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (hY : IsInHCThetaOne Y θ) :
    ∃ (P : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤) (hP : IsInHCThetaOne P θ),
      IsProjectiveInHCThetaOne P θ hP ∧
      ∃ (π : HCThetaOneHom P Y θ hP hY), Function.Surjective π.toLinearMap := by

  obtain ⟨P, hP, V, hV_acg, hV_mod, hTV, π, hπ_surj⟩ :=
    hc_theta_one_tensor_bimodule_surjects θ Y hY

  have hP_proj : IsProjectiveInHCThetaOne P θ hP :=
    tensor_bimodule_is_projective_in_hc_theta_one θ P hP V hTV

  exact ⟨P, hP, hP_proj, π, hπ_surj⟩

def LieBimodule.IsFiniteLengthBimodule (M : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤) : Prop :=
  ∃ n : ℕ, ∃ (chain : Fin (n + 1) → Submodule R M.carrier),
    chain ⟨0, Nat.zero_lt_succ n⟩ = ⊥ ∧
    chain ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ = ⊤ ∧

    (∀ i : Fin n,
      chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ <
        chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) ∧

    (∀ i : Fin n,
      M.IsSubBimodule (chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)) ∧
    (∀ i : Fin n,
      M.IsSubBimodule (chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)) ∧


    (∀ i : Fin n, ∀ (W : Submodule R M.carrier), M.IsSubBimodule W →
      chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ≤ W →
      W ≤ chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ →
      W = chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ∨
      W = chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)

def iteratedKerThetaRightAction (M : LieBimodule R 𝔤)
    (θ : CenterCharacter R 𝔤)
    (zs : List (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)))
    (m : M.carrier) : M.carrier :=
  zs.foldl (fun acc z =>
    let θz : R := θ z
    let zVal : UniversalEnvelopingAlgebra R 𝔤 := z
    let kerElem : UniversalEnvelopingAlgebra R 𝔤 := zVal - algebraMap R _ θz
    M.rightAction (MulOpposite.op kerElem) acc) m

structure IsInHCTheta (M : LieBimodule R 𝔤)
    (θ : CenterCharacter R 𝔤) : Prop where
  isHC : IsHarishChandraBimodule M
  annihilated_by_power : ∃ n : ℕ,
    ∀ (zs : List (Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))),
      zs.length = n →
      ∀ (m : M.carrier), iteratedKerThetaRightAction M θ zs m = 0

def IsInHC (M : LieBimodule R 𝔤) : Prop :=
  IsHarishChandraBimodule M

def LieBimodule.AreIsomorphic (M₁ M₂ : LieBimodule R 𝔤) : Prop :=
  ∃ (f : M₁.carrier →ₗ[R] M₂.carrier),
    Function.Bijective f ∧
    (∀ (u : UniversalEnvelopingAlgebra R 𝔤) (m : M₁.carrier),
      f (M₁.leftAction u m) = M₂.leftAction u (f m)) ∧
    (∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (m : M₁.carrier),
      f (M₁.rightAction u m) = M₂.rightAction u (f m))

section Corollary_25_7

universe u_𝔤'' u_mod''

variable {𝔤'' : Type u_𝔤''} [LieRing 𝔤''] [LieAlgebra ℂ 𝔤'']
  [LieAlgebra.IsSemisimple ℂ 𝔤''] [Module.Finite ℂ 𝔤'']

def HasFinitelyManySimpleBimodules
    {𝔤 : Type u_𝔤''} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (θ : CenterCharacter ℂ 𝔤) : Prop :=
  ∃ (n : ℕ) (simples : Fin n → LieBimodule.{0, u_𝔤'', u_mod''} ℂ 𝔤),
    (∀ i, (simples i).IsIrreducible) ∧
    (∀ i, IsInHCThetaOne (simples i) θ) ∧
    (∀ (S : LieBimodule.{0, u_𝔤'', u_mod''} ℂ 𝔤), S.IsIrreducible → IsInHCThetaOne S θ →
      ∃ i, LieBimodule.AreIsomorphic S (simples i))

theorem theorem_25_6_and_proposition_16_2
    (θ : CenterCharacter ℂ 𝔤'')
    (Y : LieBimodule.{0, u_𝔤'', u_mod''} ℂ 𝔤'')
    (hY : IsInHCThetaOne Y θ) :
    Y.IsFiniteLengthBimodule := by sorry

theorem hc_theta_filtration_reduction_step
    (θ₀ : CenterCharacter ℂ 𝔤'')
    (Y₀ : LieBimodule.{0, u_𝔤'', u_mod''} ℂ 𝔤'')
    (hY₀_hc : IsHarishChandraBimodule Y₀)
    (n : ℕ)
    (h_annihilation : ∀ (zs : List (Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤''))),
      zs.length = n + 1 →
      ∀ (m : Y₀.carrier), iteratedKerThetaRightAction Y₀ θ₀ zs m = 0)
    (h_hc1_fl : ∀ (Z : LieBimodule.{0, u_𝔤'', u_mod''} ℂ 𝔤''),
      IsInHCThetaOne Z θ₀ → Z.IsFiniteLengthBimodule)
    (h_lower_fl : ∀ (Z : LieBimodule.{0, u_𝔤'', u_mod''} ℂ 𝔤''),
      IsHarishChandraBimodule Z →
      (∀ (zs : List (Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤''))),
        zs.length = n →
        ∀ (m : Z.carrier), iteratedKerThetaRightAction Z θ₀ zs m = 0) →
      Z.IsFiniteLengthBimodule) :
    Y₀.IsFiniteLengthBimodule := by sorry

theorem hc_theta_filtration_finite_length
    (θ : CenterCharacter ℂ 𝔤'')
    (Y : LieBimodule.{0, u_𝔤'', u_mod''} ℂ 𝔤'')
    (hY : IsInHCTheta Y θ)
    (h_hc1_fl : ∀ (Z : LieBimodule.{0, u_𝔤'', u_mod''} ℂ 𝔤''),
      IsInHCThetaOne Z θ → Z.IsFiniteLengthBimodule) :
    Y.IsFiniteLengthBimodule := by
  obtain ⟨n, h_annihilation⟩ := hY.annihilated_by_power
  suffices h_ind : ∀ (k : ℕ) (Z : LieBimodule.{0, u_𝔤'', u_mod''} ℂ 𝔤''),
      IsHarishChandraBimodule Z →
      (∀ (zs : List (Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤''))),
        zs.length = k →
        ∀ (m : Z.carrier), iteratedKerThetaRightAction Z θ zs m = 0) →
      Z.IsFiniteLengthBimodule by
    exact h_ind n Y hY.isHC h_annihilation
  intro k
  induction k with
  | zero =>
    intro Z _ h_ann
    have h_zero : ∀ (m : Z.carrier), m = 0 := by
      intro m
      have := h_ann [] rfl m
      simp [iteratedKerThetaRightAction, List.foldl] at this
      exact this
    exact ⟨0, fun _ => ⊥, rfl,
      by ext x; simp [h_zero x],
      fun i => Fin.elim0 i,
      fun i => Fin.elim0 i,
      fun i => Fin.elim0 i,
      fun i => Fin.elim0 i⟩
  | succ k ih =>
    intro Z hZ_hc h_ann
    exact hc_theta_filtration_reduction_step θ Z hZ_hc k h_ann h_hc1_fl ih

theorem hc_block_decomposition_step
    (Y₀ : LieBimodule.{0, u_𝔤'', u_mod''} ℂ 𝔤'')
    (hY₀ : IsInHC Y₀)
    (h_hc_theta_fl : ∀ (θ₀ : CenterCharacter ℂ 𝔤'')
      (Z : LieBimodule.{0, u_𝔤'', u_mod''} ℂ 𝔤''),
      IsInHCTheta Z θ₀ → Z.IsFiniteLengthBimodule) :
    Y₀.IsFiniteLengthBimodule := by sorry

theorem corollary_25_7
    (θ : CenterCharacter ℂ 𝔤'')
    (Y : LieBimodule.{0, u_𝔤'', u_mod''} ℂ 𝔤'')
    (hY : IsInHCThetaOne Y θ) :
    Y.IsFiniteLengthBimodule :=
  theorem_25_6_and_proposition_16_2 θ Y hY

theorem corollary_25_7_hc_theta
    (θ : CenterCharacter ℂ 𝔤'')
    (Y : LieBimodule.{0, u_𝔤'', u_mod''} ℂ 𝔤'')
    (hY : IsInHCTheta Y θ) :
    Y.IsFiniteLengthBimodule :=
  hc_theta_filtration_finite_length θ Y hY (corollary_25_7 θ)

theorem corollary_25_7_hc
    (Y : LieBimodule.{0, u_𝔤'', u_mod''} ℂ 𝔤'')
    (hY : IsInHC Y) :
    Y.IsFiniteLengthBimodule :=
  hc_block_decomposition_step Y hY corollary_25_7_hc_theta

end Corollary_25_7

end
