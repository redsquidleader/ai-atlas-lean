/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.MaximalQuotients
import Atlas.LieGroups.code.KostantTheorem

universe u_hc_bim

noncomputable section

def kostant_base_change_iso_local
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [LieAlgebra.IsSemisimple ℂ 𝔤]
    (Δ : TriangularDecomposition ℂ 𝔤)
    (χ : ↥(Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤)) →ₐ[ℂ] ℂ)
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    [Module.Finite ℂ V]
    (hirr : LieModule.IsIrreducible ℂ 𝔤 V) :
    (HomAdEquivariant V (MaximalQuotient.bimodule χ)) ≃ₗ[ℂ] (WeightSpace Δ V 0) := by


  exact sorry

theorem corollary_14_3_dim_eq
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [LieAlgebra.IsSemisimple ℂ 𝔤]
    (Δ : TriangularDecomposition ℂ 𝔤)
    (χ : ↥(Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤)) →ₐ[ℂ] ℂ)
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    [Module.Finite ℂ V]
    (hirr : LieModule.IsIrreducible ℂ 𝔤 V) :
    Module.finrank ℂ (HomAdEquivariant V (MaximalQuotient.bimodule χ)) =
    Module.finrank ℂ (WeightSpace Δ V 0) := by


  have e : (HomAdEquivariant V (MaximalQuotient.bimodule χ)) ≃ₗ[ℂ] (WeightSpace Δ V 0) :=
    kostant_base_change_iso_local Δ χ V hirr

  exact LinearEquiv.finrank_eq e

def HomAdEquivariant.postcomp
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {V : Type*} [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    {N M : LieBimodule R 𝔤}
    (π : N.carrier →ₗ[R] M.carrier)
    (hπ_left : ∀ (u : UniversalEnvelopingAlgebra R 𝔤) (n : N.carrier),
      π (N.leftAction u n) = M.leftAction u (π n))
    (hπ_right : ∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (n : N.carrier),
      π (N.rightAction u n) = M.rightAction u (π n)) :
    HomAdEquivariant V N →ₗ[R] HomAdEquivariant V M where
  toFun f := ⟨π.comp f.val, by
    intro x v
    simp only [LinearMap.comp_apply]
    rw [f.property x v]
    show π (N.adjointAction x (f.val v)) = M.adjointAction x (π (f.val v))
    simp only [LieBimodule.adjointAction, LinearMap.sub_apply]
    rw [← hπ_left, ← hπ_right, map_sub]⟩
  map_add' f g := by
    ext v
    simp [LinearMap.comp_apply, LinearMap.add_apply]
  map_smul' c f := by
    ext v
    simp [LinearMap.comp_apply, LinearMap.smul_apply]

theorem corollary_14_5
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [LieAlgebra.IsSemisimple ℂ 𝔤] [Module.Finite ℂ 𝔤]
    (Δ : TriangularDecomposition ℂ 𝔤)
    (M : LieBimodule.{_, _, u_hc_bim} ℂ 𝔤)
    (hirr : M.IsIrreducible)
    (hlocfin : IsHarishChandraBimodule M) :

    (∃ (χ : ↥(Subalgebra.center ℂ (UniversalEnvelopingAlgebra ℂ 𝔤)) →ₐ[ℂ] ℂ)
       (V : Type u_hc_bim) (_ : AddCommGroup V) (_ : Module ℂ V)
       (_ : LieRingModule 𝔤 V) (_ : LieModule ℂ 𝔤 V)
       (_ : Module.Finite ℂ V)
       (_ : LieModule.IsIrreducible ℂ 𝔤 V),
       ∃ (surj : TensorProduct ℂ V (MaximalQuotient χ) →ₗ[ℂ] M.carrier),
         Function.Surjective surj ∧
         (∀ (x : 𝔤) (t : TensorProduct ℂ V (MaximalQuotient χ)),
           surj ((tensorBimodule (LieBimodule.trivial V) χ).adjointAction x t) =
           M.adjointAction x (surj t)))
    ∧

    (∀ (W : Type 0) [AddCommGroup W] [Module ℂ W] [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W]
       [Module.Finite ℂ W] (_ : LieModule.IsIrreducible ℂ 𝔤 W),
       Module.Finite ℂ (HomAdEquivariant W M)) := by
  have part_i := corollary_14_5_i M hirr hlocfin
  refine ⟨part_i, ?_⟩
  obtain ⟨χ, V₀, instACG, instMod, instLRM, instLM, instFin, hirr_V₀, surj, hsurj, hequivar⟩ := part_i
  have hAdm : IsAdmissibleBimodule (tensorBimodule (LieBimodule.trivial V₀) χ) :=
    corollary_14_4 Δ (LieBimodule.trivial V₀) χ
  exact hc_quotient_admissible (tensorBimodule (LieBimodule.trivial V₀) χ) M hAdm surj hsurj hequivar

end
