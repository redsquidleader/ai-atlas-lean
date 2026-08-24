/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.HCBimoduleProjectives
import Atlas.LieGroups.code.GrothendieckGroupO
import Atlas.LieGroups.code.BernsteinGelfandEquivalence

noncomputable section

open ProjectiveFunctors

section Definitions

universe u_R u_𝔤 u_mod

variable {R : Type u_R} [CommRing R]
variable {𝔤 : Type u_𝔤} [LieRing 𝔤] [LieAlgebra R 𝔤]

def IsSimpleInHCThetaOne (L : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (θ : CenterCharacter R 𝔤) (_hL : IsInHCThetaOne L θ) : Prop :=
  L.IsIrreducible

def IsIndecomposableInHCThetaOne (P : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (θ : CenterCharacter R 𝔤) (_hP : IsInHCThetaOne P θ) : Prop :=
  (∃ m : P.carrier, m ≠ 0) ∧
  ∀ (S₁ S₂ : Submodule R P.carrier),
    P.IsSubBimodule S₁ → P.IsSubBimodule S₂ →
    S₁ ⊔ S₂ = ⊤ → S₁ ⊓ S₂ = ⊥ →
    S₁ = ⊥ ∨ S₂ = ⊥

def IsProjectiveCoverInHCThetaOne (P L : LieBimodule.{u_R, u_𝔤, u_mod} R 𝔤)
    (θ : CenterCharacter R 𝔤)
    (hP : IsInHCThetaOne P θ) (hL : IsInHCThetaOne L θ) : Prop :=
  IsIndecomposableInHCThetaOne P θ hP ∧
  IsProjectiveInHCThetaOne P θ hP ∧
  ∃ (π : HCThetaOneHom P L θ hP hL), Function.Surjective π.toLinearMap

def IsIndecomposableInO
    {Δ : TriangularDecomposition R 𝔤}
    (_rd : PositiveRootData Δ)
    (P : Type u_mod) [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (_hP : IsCategoryO Δ _rd P) : Prop :=
  (∃ m : P, m ≠ 0) ∧
  ∀ (S₁ S₂ : LieSubmodule R 𝔤 P),
    S₁ ⊔ S₂ = ⊤ → S₁ ⊓ S₂ = ⊥ →
    S₁ = ⊥ ∨ S₂ = ⊥

end Definitions

section Theorem25_6

universe u

variable {R : Type u} [CommRing R]
variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
variable [LieAlgebra.IsSemisimple R 𝔤] [Module.Finite R 𝔤]
variable {D : TriangularDecomposition R 𝔤}
variable {rd : PositiveRootData D}

def quotientLieBimodule (M : LieBimodule.{u, u, u} R 𝔤) (J : Submodule R M.carrier)
    (hJ : M.IsSubBimodule J) : LieBimodule.{u, u, u} R 𝔤 where
  carrier := M.carrier ⧸ J
  leftAction := {
    toFun := fun u => J.mapQ J (M.leftAction u) (fun _ hm => hJ.1 u _ hm)
    map_one' := by
      apply LinearMap.ext; intro x; obtain ⟨m, rfl⟩ := J.mkQ_surjective x
      simp only [Submodule.mapQ_apply, Submodule.mkQ_apply]
      congr 1; exact LinearMap.congr_fun (map_one M.leftAction) m
    map_mul' := fun u v => by
      apply LinearMap.ext; intro x; obtain ⟨m, rfl⟩ := J.mkQ_surjective x
      simp only [Submodule.mapQ_apply, Submodule.mkQ_apply]
      congr 1; exact LinearMap.congr_fun (map_mul M.leftAction u v) m
    map_zero' := by
      apply LinearMap.ext; intro x; obtain ⟨m, rfl⟩ := J.mkQ_surjective x
      simp only [Submodule.mapQ_apply, Submodule.mkQ_apply, LinearMap.zero_apply]
      rw [show M.leftAction 0 = 0 from map_zero M.leftAction, LinearMap.zero_apply]
      exact J.mkQ.map_zero
    map_add' := fun u v => by
      apply LinearMap.ext; intro x; obtain ⟨m, rfl⟩ := J.mkQ_surjective x
      simp only [Submodule.mapQ_apply, Submodule.mkQ_apply, LinearMap.add_apply]
      rw [show M.leftAction (u + v) = M.leftAction u + M.leftAction v from
        map_add M.leftAction u v, LinearMap.add_apply]
      exact J.mkQ.map_add _ _
    commutes' := fun r => by
      apply LinearMap.ext; intro x; obtain ⟨m, rfl⟩ := J.mkQ_surjective x
      simp only [Submodule.mapQ_apply, Submodule.mkQ_apply,
        Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply]
      rw [show M.leftAction (r • 1) = r • M.leftAction 1 from map_smul M.leftAction r 1,
        show M.leftAction 1 = 1 from map_one M.leftAction, LinearMap.smul_apply]; rfl }
  rightAction := {
    toFun := fun u => J.mapQ J (M.rightAction u) (fun _ hm => hJ.2 u _ hm)
    map_one' := by
      apply LinearMap.ext; intro x; obtain ⟨m, rfl⟩ := J.mkQ_surjective x
      simp only [Submodule.mapQ_apply, Submodule.mkQ_apply]
      congr 1; exact LinearMap.congr_fun (map_one M.rightAction) m
    map_mul' := fun u v => by
      apply LinearMap.ext; intro x; obtain ⟨m, rfl⟩ := J.mkQ_surjective x
      simp only [Submodule.mapQ_apply, Submodule.mkQ_apply]
      congr 1; exact LinearMap.congr_fun (map_mul M.rightAction u v) m
    map_zero' := by
      apply LinearMap.ext; intro x; obtain ⟨m, rfl⟩ := J.mkQ_surjective x
      simp only [Submodule.mapQ_apply, Submodule.mkQ_apply, LinearMap.zero_apply]
      rw [show M.rightAction 0 = 0 from map_zero M.rightAction, LinearMap.zero_apply]
      exact J.mkQ.map_zero
    map_add' := fun u v => by
      apply LinearMap.ext; intro x; obtain ⟨m, rfl⟩ := J.mkQ_surjective x
      simp only [Submodule.mapQ_apply, Submodule.mkQ_apply, LinearMap.add_apply]
      rw [show M.rightAction (u + v) = M.rightAction u + M.rightAction v from
        map_add M.rightAction u v, LinearMap.add_apply]
      exact J.mkQ.map_add _ _
    commutes' := fun r => by
      apply LinearMap.ext; intro x; obtain ⟨m, rfl⟩ := J.mkQ_surjective x
      simp only [Submodule.mapQ_apply, Submodule.mkQ_apply,
        Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply]
      rw [show M.rightAction (r • 1) = r • M.rightAction 1 from
        map_smul M.rightAction r 1,
        show M.rightAction 1 = 1 from map_one M.rightAction,
        LinearMap.smul_apply]; rfl }
  actions_commute := fun u v m => by
    obtain ⟨m₀, rfl⟩ := J.mkQ_surjective m
    show (J.mapQ J (M.leftAction u) (fun _ hm => hJ.1 u _ hm))
      ((J.mapQ J (M.rightAction v) (fun _ hm => hJ.2 v _ hm)) (J.mkQ m₀)) =
      (J.mapQ J (M.rightAction v) (fun _ hm => hJ.2 v _ hm))
      ((J.mapQ J (M.leftAction u) (fun _ hm => hJ.1 u _ hm)) (J.mkQ m₀))
    simp only [Submodule.mapQ_apply, Submodule.mkQ_apply]
    congr 1; exact M.actions_commute u v m₀

theorem theorem_25_6
    (wg : WeylGroupData D)
    (theta : CenterCharacter R 𝔤)
    (Tl : TlambdaData.{u, u, u} theta) :

    (∀ (mu lam : D.𝔥 →ₗ[R] R),
      IsProperRep rd wg mu lam →
      ∃ (L_xi P_xi : LieBimodule.{u, u, u} R 𝔤)
        (hL : IsInHCThetaOne L_xi theta)
        (hP : IsInHCThetaOne P_xi theta),
        IsSimpleInHCThetaOne L_xi theta hL ∧
        IsProjectiveCoverInHCThetaOne P_xi L_xi theta hP hL ∧
        (∃ (Q : LieModuleObj.{u, u, u} R 𝔤),
          Nonempty (IsHighestWeightModule D Q.carrier (mu - wg.ρ)) ∧
          Nonempty (IsCategoryO D rd Q.carrier) ∧
          (∀ hQO, IsProjectiveInO rd Q.carrier hQO) ∧
          (∀ hQO, IsIndecomposableInO rd Q.carrier hQO) ∧
          Nonempty (LieModuleIso R 𝔤 (Tl.applyObj P_xi hP) Q))) ∧

    (∀ (L : LieBimodule.{u, u, u} R 𝔤) (hL : IsInHCThetaOne L theta),
      IsSimpleInHCThetaOne L theta hL →
      ∃ (mu' lam' : D.𝔥 →ₗ[R] R), IsProperRep rd wg mu' lam' ∧
        (∃ (L' : LieBimodule.{u, u, u} R 𝔤) (_ : IsInHCThetaOne L' theta),
          LieBimodule.AreIsomorphic L L')) ∧

    (∀ (P : LieBimodule.{u, u, u} R 𝔤) (hP : IsInHCThetaOne P theta),
      IsIndecomposableInHCThetaOne P theta hP →
      IsProjectiveInHCThetaOne P theta hP →
      ∃ (mu' lam' : D.𝔥 →ₗ[R] R), IsProperRep rd wg mu' lam' ∧
        (∃ (P' : LieBimodule.{u, u, u} R 𝔤) (_ : IsInHCThetaOne P' theta),
          LieBimodule.AreIsomorphic P P')) := by
  refine ⟨?_, ?_, ?_⟩


  · intro mu lam hproper
    sorry

  · intro L hL hL_simple

    sorry

  · intro P hP hIndec hProj

    sorry

end Theorem25_6

end
