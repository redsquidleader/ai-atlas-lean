/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.SL2Basics
import Atlas.LieGroups.code.GKModule
import Atlas.LieGroups.code.KTypeDecomposition
import Mathlib.Data.ZMod.Basic

noncomputable section

open Complex Module

inductive SL2IrredGKModule where
  | finiteDim (n : ℕ)
  | principalSeries (ν : ℂ) (ε : ZMod 2)
  | discreteSeriesPlus (n : ℕ) (hn : n ≥ 2)
  | discreteSeriesMinus (n : ℕ) (hn : n ≥ 2)
  | limitDiscretePlus
  | limitDiscreteMinus

namespace SL2IrredGKModule

def kTypes : SL2IrredGKModule → Set ℤ
  | finiteDim n => {m : ℤ | m % 2 = (n : ℤ) % 2 ∧ m.natAbs ≤ n}
  | principalSeries _ ε => {m : ℤ | (m : ZMod 2) = ε}
  | discreteSeriesPlus n _ => {m : ℤ | m ≥ (n : ℤ) ∧ m % 2 = (n : ℤ) % 2}
  | discreteSeriesMinus n _ => {m : ℤ | m ≤ -(n : ℤ) ∧ m % 2 = (n : ℤ) % 2}
  | limitDiscretePlus => {m : ℤ | m ≥ 1 ∧ m % 2 = 1}
  | limitDiscreteMinus => {m : ℤ | m ≤ -1 ∧ m % 2 = 1}

def casimirEigenvalue : SL2IrredGKModule → ℂ
  | finiteDim n => (n : ℂ) * ((n : ℂ) + 2)
  | principalSeries ν _ => 1 - ν ^ 2
  | discreteSeriesPlus n _ => (n : ℂ) * ((n : ℂ) - 2)
  | discreteSeriesMinus n _ => (n : ℂ) * ((n : ℂ) - 2)
  | limitDiscretePlus => -1
  | limitDiscreteMinus => -1

end SL2IrredGKModule

def GKModule.IsIsomorphicGK
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W]
    (M : GKModule 𝔤 K 𝔨 Ad V) (N : GKModule 𝔤 K 𝔨 Ad W) : Prop :=
  ∃ (φ : GKModuleHom M N), Function.Bijective φ.toLinearMap

theorem GKModule.IsIsomorphicGK.symm
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W]
    {M : GKModule 𝔤 K 𝔨 Ad V} {N : GKModule 𝔤 K 𝔨 Ad W}
    (h : M.IsIsomorphicGK N) : N.IsIsomorphicGK M := by
  obtain ⟨φ, hφ⟩ := h
  let e := LinearEquiv.ofBijective φ.toLinearMap hφ
  refine ⟨⟨e.symm.toLinearMap, fun X w => ?_, fun k w => ?_⟩, e.symm.bijective⟩
  ·
    apply e.injective


    show e (e.symm ⁅X, w⁆) = e ⁅X, e.symm w⁆
    rw [e.apply_symm_apply]

    conv_rhs => rw [show (e : V → W) = φ.toLinearMap from
      funext (fun v => LinearEquiv.ofBijective_apply φ.toLinearMap v)]
    rw [φ.lie_comm]
    congr 1
    exact (LinearEquiv.apply_ofBijective_symm_apply φ.toLinearMap w).symm
  ·
    apply e.injective
    show e (e.symm (N.σ k w)) = e (M.σ k (e.symm w))
    rw [e.apply_symm_apply]
    conv_rhs => rw [show (e : V → W) = φ.toLinearMap from
      funext (fun v => LinearEquiv.ofBijective_apply φ.toLinearMap v)]
    rw [φ.group_comm]
    congr 1
    exact (LinearEquiv.apply_ofBijective_symm_apply φ.toLinearMap w).symm

theorem GKModule.IsIsomorphicGK.trans
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W]
    {U : Type*} [AddCommGroup U] [Module ℂ U]
    [LieRingModule 𝔤 U] [LieModule ℂ 𝔤 U]
    {M : GKModule 𝔤 K 𝔨 Ad V} {N : GKModule 𝔤 K 𝔨 Ad W} {P : GKModule 𝔤 K 𝔨 Ad U}
    (h₁ : M.IsIsomorphicGK N) (h₂ : N.IsIsomorphicGK P) : M.IsIsomorphicGK P := by
  obtain ⟨φ₁, hφ₁⟩ := h₁
  obtain ⟨φ₂, hφ₂⟩ := h₂
  exact ⟨{
    toLinearMap := φ₂.toLinearMap.comp φ₁.toLinearMap
    lie_comm := fun X v => by
      simp only [LinearMap.comp_apply, φ₁.lie_comm, φ₂.lie_comm]
    group_comm := fun k v => by
      simp only [LinearMap.comp_apply, φ₁.group_comm, φ₂.group_comm]
  }, hφ₂.comp hφ₁⟩

structure SL2IrredGKModule.Realization
    (μ : SL2IrredGKModule)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)) where
  W : Type*
  [instAddCommGroup : AddCommGroup W]
  [instModule : Module ℂ W]
  [instLieRingModule : LieRingModule 𝔤 W]
  [instLieModule : LieModule ℂ 𝔤 W]
  gkmod : GKModule 𝔤 K 𝔨 Ad W
  casimirScalar : ℂ
  casimir_eq : casimirScalar = μ.casimirEigenvalue

attribute [instance] SL2IrredGKModule.Realization.instAddCommGroup
  SL2IrredGKModule.Realization.instModule
  SL2IrredGKModule.Realization.instLieRingModule
  SL2IrredGKModule.Realization.instLieModule

inductive KTypeBoundedness where
  | boundedBoth
  | unboundedBoth
  | boundedBelow
  | boundedAbove

noncomputable def sl2_lieRingModule_from_generators
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (W : Type*) [AddCommGroup W] [Module ℂ W]
    (ρ : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ W) :
    LieRingModule 𝔤 W :=
  LieRingModule.compLieHom W ρ

noncomputable def sl2_lieModule_from_generators
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (W : Type*) [AddCommGroup W] [Module ℂ W]
    (ρ : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ W) :
    @LieModule ℂ 𝔤 W _ _ _ _ _
      (sl2_lieRingModule_from_generators 𝔤 W ρ) :=
  LieModule.compLieHom W ρ

theorem sl2_basis_exists
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V) :
    ∃ (b : Basis (Fin 3) ℂ 𝔤), b 0 = M_sl2.H ∧ b 1 = M_sl2.E ∧ b 2 = M_sl2.F := by sorry

noncomputable def SL2GKModule.getBasis
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V) : Basis (Fin 3) ℂ 𝔤 :=
  (sl2_basis_exists 𝔤 K 𝔨 Ad V M_sl2).choose

lemma SL2GKModule.getBasis_H
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V) : M_sl2.getBasis 0 = M_sl2.H :=
  (sl2_basis_exists 𝔤 K 𝔨 Ad V M_sl2).choose_spec.1

lemma SL2GKModule.getBasis_E
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V) : M_sl2.getBasis 1 = M_sl2.E :=
  (sl2_basis_exists 𝔤 K 𝔨 Ad V M_sl2).choose_spec.2.1

lemma SL2GKModule.getBasis_F
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V) : M_sl2.getBasis 2 = M_sl2.F :=
  (sl2_basis_exists 𝔤 K 𝔨 Ad V M_sl2).choose_spec.2.2

noncomputable def sl2_lieHom_from_generators
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (h e f_elem : 𝔤)
    (b : Basis (Fin 3) ℂ 𝔤)
    (hb0 : b 0 = h) (hb1 : b 1 = e) (hb2 : b 2 = f_elem)
    (src_HE : ⁅h, e⁆ = (2 : ℤ) • e)
    (src_HF : ⁅h, f_elem⁆ = (-2 : ℤ) • f_elem)
    (src_EF : ⁅e, f_elem⁆ = h)
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρH ρE ρF : Module.End ℂ W)
    (hHE : ρH ∘ₗ ρE - ρE ∘ₗ ρH = (2 : ℂ) • ρE)
    (hHF : ρH ∘ₗ ρF - ρF ∘ₗ ρH = -(2 : ℂ) • ρF)
    (hEF : ρE ∘ₗ ρF - ρF ∘ₗ ρE = ρH) :
    𝔤 →ₗ⁅ℂ⁆ Module.End ℂ W := by
  let vals : Fin 3 → Module.End ℂ W := fun i => match i with | 0 => ρH | 1 => ρE | 2 => ρF
  let φ : 𝔤 →ₗ[ℂ] Module.End ℂ W := b.constr ℂ vals
  have hφh : φ h = ρH := by rw [← hb0]; exact b.constr_basis ℂ vals 0
  have hφe : φ e = ρE := by rw [← hb1]; exact b.constr_basis ℂ vals 1
  have hφf : φ f_elem = ρF := by rw [← hb2]; exact b.constr_basis ℂ vals 2
  have hHE' : ρH * ρE - ρE * ρH = (2 : ℂ) • ρE := hHE
  have hHF' : ρH * ρF - ρF * ρH = -(2 : ℂ) • ρF := hHF
  have hEF' : ρE * ρF - ρF * ρE = ρH := hEF
  have hlie : ∀ i j : Fin 3, φ ⁅b i, b j⁆ = ⁅φ (b i), φ (b j)⁆ := by
    intro i j
    fin_cases i <;> fin_cases j <;> dsimp only [Fin.reduceFinMk] <;> simp only [hb0, hb1, hb2]

    · rw [lie_self, map_zero]; symm; rw [hφh]; exact lie_self _

    · rw [src_HE, map_zsmul, hφe, hφh]
      show (2 : ℤ) • ρE = ρH * ρE - ρE * ρH
      rw [show (2 : ℤ) • ρE = (2 : ℂ) • ρE from by norm_cast]; exact hHE'.symm

    · rw [src_HF, map_zsmul, hφf, hφh]
      show (-2 : ℤ) • ρF = ρH * ρF - ρF * ρH
      rw [show (-2 : ℤ) • ρF = -(2 : ℂ) • ρF from by norm_cast]; exact hHF'.symm

    · have hsrc : ⁅e, h⁆ = (-2 : ℤ) • e := by rw [← lie_skew, src_HE]; simp [neg_smul]
      rw [hsrc, map_zsmul, hφe, hφh]
      show (-2 : ℤ) • ρE = ρE * ρH - ρH * ρE
      rw [show ρE * ρH - ρH * ρE = -(ρH * ρE - ρE * ρH) from by noncomm_ring, hHE']
      simp [neg_smul]; norm_cast

    · rw [lie_self, map_zero]; symm; rw [hφe]; exact lie_self _

    · rw [src_EF, hφh, hφe, hφf]
      show ρH = ρE * ρF - ρF * ρE; exact hEF'.symm

    · have hsrc : ⁅f_elem, h⁆ = (2 : ℤ) • f_elem := by
        rw [← lie_skew, src_HF]; simp [neg_smul]
      rw [hsrc, map_zsmul, hφf, hφh]
      show (2 : ℤ) • ρF = ρF * ρH - ρH * ρF
      rw [show ρF * ρH - ρH * ρF = -(ρH * ρF - ρF * ρH) from by noncomm_ring, hHF']
      simp [neg_smul]; norm_cast

    · have hsrc : ⁅f_elem, e⁆ = -h := by rw [← lie_skew, src_EF]
      rw [hsrc, map_neg, hφh, hφf, hφe]
      show -ρH = ρF * ρE - ρE * ρF
      rw [show ρF * ρE - ρE * ρF = -(ρE * ρF - ρF * ρE) from by noncomm_ring, hEF']

    · rw [lie_self, map_zero]; symm; rw [hφf]; exact lie_self _
  have hlie_all : ∀ x y : 𝔤, φ ⁅x, y⁆ = ⁅φ x, φ y⁆ := by
    intro x y
    rw [← b.sum_repr x, ← b.sum_repr y]
    simp only [lie_sum, sum_lie, map_sum, smul_lie, lie_smul, map_smul]
    apply Finset.sum_congr rfl; intro i _
    congr 1
    apply Finset.sum_congr rfl; intro j _
    congr 1
    exact hlie j i

  exact {
    toLinearMap := φ
    map_lie' := by intro x y; exact hlie_all x y
  }


noncomputable def sl2_adjoint_gkmod
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    [LieRingModule 𝔤 𝔤] [LieModule ℂ 𝔤 𝔤]
    (hAd_lie : ∀ (k : K) (X Y : 𝔤), Ad k ⁅X, Y⁆ = ⁅Ad k X, Ad k Y⁆) :
    GKModule 𝔤 K 𝔨 Ad 𝔤 where
  σ := Ad
  locallyFinite := by
    intro v
    exact FiniteDimensional.finiteDimensional_submodule _
  diffσ := ((LieModule.toEnd ℂ 𝔤 𝔤).comp (LieSubalgebra.incl 𝔨)).toLinearMap
  diff_eq_lie := by intro X v; simp [LieModule.toEnd_apply_apply]
  equivariance := hAd_lie

noncomputable def sl2_model_gkmod_σ
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (W : Type*) [AddCommGroup W] [Module ℂ W]
    [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W] :
    Representation ℂ K W := by
  exact sorry

theorem sl2_model_gkmod_locallyFinite
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (W : Type*) [AddCommGroup W] [Module ℂ W]
    [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W] :
    (sl2_model_gkmod_σ 𝔤 K 𝔨 Ad W).IsLocallyFinite := by
  exact sorry

theorem sl2_model_gkmod_equivariance
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (W : Type*) [AddCommGroup W] [Module ℂ W]
    [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W] :
    ∀ (k : K) (X : 𝔤) (v : W),
      sl2_model_gkmod_σ 𝔤 K 𝔨 Ad W k (⁅X, v⁆) =
        ⁅Ad k X, sl2_model_gkmod_σ 𝔤 K 𝔨 Ad W k v⁆ := by
  exact sorry

noncomputable def sl2_model_gkmod
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (W : Type*) [AddCommGroup W] [Module ℂ W]
    [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W] :
    GKModule 𝔤 K 𝔨 Ad W :=
  { σ := sl2_model_gkmod_σ 𝔤 K 𝔨 Ad W
    locallyFinite := sl2_model_gkmod_locallyFinite 𝔤 K 𝔨 Ad W
    diffσ := ((LieModule.toEnd ℂ 𝔤 W).comp (LieSubalgebra.incl 𝔨)).toLinearMap
    diff_eq_lie := by intro X v; simp [LieModule.toEnd_apply_apply]
    equivariance := sl2_model_gkmod_equivariance 𝔤 K 𝔨 Ad W }

open Classical in
noncomputable def sl2_gk_ktype_boundedness
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hirr : M.IsIrreducibleGKModule)
    (hadm : M.IsAdmissible) :
    KTypeBoundedness :=
  if h1 : BddAbove M_sl2.ktypeSet then
    if h2 : BddBelow M_sl2.ktypeSet then
      KTypeBoundedness.boundedBoth
    else
      KTypeBoundedness.boundedAbove
  else
    if h3 : BddBelow M_sl2.ktypeSet then
      KTypeBoundedness.boundedBelow
    else
      KTypeBoundedness.unboundedBoth

open Classical in
lemma bddAbove_and_bddBelow_of_boundedBoth
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedBoth) :
    BddAbove M_sl2.ktypeSet ∧ BddBelow M_sl2.ktypeSet := by
  unfold sl2_gk_ktype_boundedness at hbdd
  split_ifs at hbdd with h1 h2
  · exact ⟨h1, h2⟩
  all_goals simp at hbdd

theorem irred_gkmod_nontrivial
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) :
    Nontrivial V := by sorry

theorem irred_sl2_admissible
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) :
    M_sl2.toGKModule.IsAdmissible := by sorry

lemma ktypeSet_nonempty_of_irred_admissible
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V) :
    M_sl2.ktypeSet.Nonempty := by

  haveI hnt := irred_gkmod_nontrivial M hirr
  have hadm := irred_sl2_admissible M_sl2 M hirr

  have hdecomp := SL2GKModule.weightSpaceDecomposition M_sl2 hadm

  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty

  have hall_bot : ∀ n : ℤ, M_sl2.weightSpace n = ⊥ := by
    intro n
    by_contra hn
    exact (Set.eq_empty_iff_forall_notMem.mp hempty n) hn

  have hsup_bot : ⨆ n : ℤ, M_sl2.weightSpace n = ⊥ := by
    simp_rw [hall_bot, iSup_bot]

  rw [hsup_bot] at hdecomp

  exact bot_ne_top hdecomp

lemma ktypeSet_uniform_parity
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V) :
    ∀ m ∈ M_sl2.ktypeSet, ∀ m' ∈ M_sl2.ktypeSet, (m : ℤ) % 2 = (m' : ℤ) % 2 := by


  intro n hn m hm

  suffices h : Even n ↔ Even m by
    rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hm_even := h.mp ⟨k, hk⟩
      obtain ⟨k', hk'⟩ := hm_even
      omega
    · have hm_odd : ¬ Even m := fun he => (Int.not_even_iff_odd.mpr ⟨k, hk⟩) (h.mpr he)
      have hn_odd : ¬ Even n := Int.not_even_iff_odd.mpr ⟨k, hk⟩
      rw [Int.not_even_iff_odd] at hm_odd hn_odd
      obtain ⟨k₁, hk₁⟩ := hn_odd
      obtain ⟨k₂, hk₂⟩ := hm_odd
      omega

  by_contra h_contra

  set S := ⨆ k : ℤ, M_sl2.weightSpace (n + 2 * k) with hS_def

  have hS_sub : M.IsSubmodule S := by
    constructor
    ·
      intro X w hw
      exact Submodule.iSup_induction (motive := fun w => ⁅X, w⁆ ∈ S)
        _ hw
        (fun k v hv => by
          obtain ⟨a, b, c, hX⟩ := SL2GKModule.sl2_generates M_sl2 X
          rw [hX]; simp only [add_lie, smul_lie]
          have hHv : ⁅M_sl2.H, v⁆ ∈ M_sl2.weightSpace (n + 2 * k) := by
            rw [SL2GKModule.H_acts_as_scalar_on_weight_space M_sl2 (n + 2 * k) v hv]
            exact Submodule.smul_mem _ _ hv
          have hEv := SL2GKModule.E_shifts_weight M_sl2 (n + 2 * k) v hv
          have hFv := SL2GKModule.F_shifts_weight M_sl2 (n + 2 * k) v hv
          have ha : a • ⁅M_sl2.H, v⁆ ∈ S :=
            Submodule.mem_iSup_of_mem k (Submodule.smul_mem _ a hHv)
          have hb : b • ⁅M_sl2.E, v⁆ ∈ S := by
            apply Submodule.mem_iSup_of_mem (k + 1)
            have : n + 2 * (k + 1) = n + 2 * k + 2 := by ring
            rw [this]; exact Submodule.smul_mem _ b hEv
          have hc : c • ⁅M_sl2.F, v⁆ ∈ S := by
            apply Submodule.mem_iSup_of_mem (k - 1)
            have : n + 2 * (k - 1) = n + 2 * k - 2 := by ring
            rw [this]; exact Submodule.smul_mem _ c hFv
          exact Submodule.add_mem _ (Submodule.add_mem _ ha hb) hc)
        (by simp [lie_zero])
        (fun a b ha hb => by show ⁅X, a + b⁆ ∈ S; rw [lie_add]; exact Submodule.add_mem S ha hb)
    ·
      intro k w hw
      exact Submodule.iSup_induction (motive := fun w => M.σ k w ∈ S)
        _ hw
        (fun j v hv => by
          apply Submodule.mem_iSup_of_mem j

          rw [SL2GKModule.mem_weightSpace_iff] at hv ⊢
          have heq := M.equivariance k M_sl2.H v
          rw [M_sl2.K_centralizes k] at heq
          rw [hv] at heq; rw [map_smul] at heq
          exact heq.symm)
        (by simp [map_zero])
        (fun a b ha hb => by show M.σ k (a + b) ∈ S; rw [map_add]; exact Submodule.add_mem S ha hb)

  have hS_ne_bot : S ≠ ⊥ := by
    intro hbot; apply hn
    rw [eq_bot_iff]
    calc M_sl2.weightSpace n
        = M_sl2.weightSpace (n + 2 * 0) := by ring_nf
      _ ≤ S := le_iSup (fun k : ℤ => M_sl2.weightSpace (n + 2 * k)) 0
      _ = ⊥ := hbot

  have hS_top : S = ⊤ := by
    rcases hirr S hS_sub with hbot | htop
    · exact absurd hbot hS_ne_bot
    · exact htop

  have hne : ∀ k : ℤ, (m : ℂ) ≠ (↑(n + 2 * k) : ℂ) := by
    intro k heq
    have hmk : m = n + 2 * k := by exact_mod_cast heq
    exact h_contra (by subst hmk; simp [Int.even_add])

  have hdisjoint : Disjoint (M_sl2.weightSpace m) S := by
    have hind := Module.End.independent_genEigenspace M_sl2.hEnd (1 : ℕ∞)
    have hdisjoint_ind := hind (↑m)
    have hle : S ≤ ⨆ μ, ⨆ (_ : μ ≠ (↑m : ℂ)), M_sl2.hEnd.eigenspace μ := by
      apply iSup_le; intro k
      have hne_k : (↑(n + 2 * k) : ℂ) ≠ ↑m := (hne k).symm
      exact le_trans
        (le_iSup (fun _ : (↑(n + 2 * k) : ℂ) ≠ ↑m => M_sl2.hEnd.eigenspace ↑(n + 2 * k)) hne_k)
        (le_iSup (fun μ : ℂ => ⨆ (_ : μ ≠ ↑m), M_sl2.hEnd.eigenspace μ) ↑(n + 2 * k))
    exact Disjoint.mono_right hle hdisjoint_ind

  have hm_bot : M_sl2.weightSpace m = ⊥ := by
    rw [disjoint_iff] at hdisjoint
    calc M_sl2.weightSpace m
        = M_sl2.weightSpace m ⊓ ⊤ := (inf_top_eq _).symm
      _ = M_sl2.weightSpace m ⊓ S := by rw [hS_top]
      _ = ⊥ := hdisjoint
  exact hm hm_bot

lemma sl2_EF_recurrence
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (n₀ : ℤ) (v : V) (hv : v ∈ M_sl2.weightSpace n₀)
    (hEv : ⁅M_sl2.E, v⁆ = 0) (k : ℕ) :
    ⁅M_sl2.E, SL2GKModule.iterLie M_sl2.F v (k + 1)⁆ =
      ((↑(k + 1) : ℂ) * (↑n₀ - ↑k)) • SL2GKModule.iterLie M_sl2.F v k := by
  induction k with
  | zero =>

    simp only [SL2GKModule.iterLie_succ, SL2GKModule.iterLie_zero]
    rw [leibniz_lie M_sl2.E M_sl2.F v]
    rw [M_sl2.bracket_EF]
    rw [hEv, lie_zero, add_zero]
    rw [SL2GKModule.H_acts_as_scalar_on_weight_space M_sl2 n₀ v hv]
    congr 1
    push_cast
    ring
  | succ k ih =>


    simp only [SL2GKModule.iterLie_succ] at ih ⊢


    set w := SL2GKModule.iterLie M_sl2.F v k with hw_def
    rw [leibniz_lie M_sl2.E M_sl2.F (⁅M_sl2.F, w⁆)]
    rw [M_sl2.bracket_EF]


    have hw_ws : w ∈ M_sl2.weightSpace (n₀ - 2 * (↑k : ℤ)) :=
      SL2GKModule.iterLie_F_weight_shift M_sl2 n₀ v hv k
    have hFw_ws : ⁅M_sl2.F, w⁆ ∈ M_sl2.weightSpace (n₀ - 2 * (↑k : ℤ) - 2) :=
      SL2GKModule.F_shifts_weight M_sl2 (n₀ - 2 * (↑k : ℤ)) w hw_ws
    have hH_Fw := SL2GKModule.H_acts_as_scalar_on_weight_space M_sl2
      (n₀ - 2 * (↑k : ℤ) - 2) (⁅M_sl2.F, w⁆) hFw_ws
    rw [hH_Fw]


    rw [ih, lie_smul]

    rw [← add_smul]
    congr 1
    push_cast
    ring

lemma ktypeSet_max_nonneg
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (S : Finset ℤ) (hS : (↑S : Set ℤ) = M_sl2.ktypeSet) (hne : S.Nonempty) :
    0 ≤ S.max' hne := by

  set n₀ := S.max' hne with hn₀_def
  have hn₀_mem : n₀ ∈ S := Finset.max'_mem S hne
  have hn₀_ktype : n₀ ∈ M_sl2.ktypeSet := by rwa [← hS, Finset.mem_coe]

  have hws_ne : M_sl2.weightSpace n₀ ≠ ⊥ := hn₀_ktype
  rw [Submodule.ne_bot_iff] at hws_ne
  obtain ⟨v, hv_mem, hv_ne⟩ := hws_ne

  have hEv_zero : ⁅M_sl2.E, v⁆ = 0 := by
    have hEv_ws := SL2GKModule.E_shifts_weight M_sl2 n₀ v hv_mem


    have hn₀_plus_2_notin : n₀ + 2 ∉ S := by
      intro hmem
      have := Finset.le_max' S (n₀ + 2) hmem
      omega

    have hws_bot : M_sl2.weightSpace (n₀ + 2) = ⊥ := by
      by_contra hne_bot
      have : n₀ + 2 ∈ M_sl2.ktypeSet := hne_bot
      rw [← hS] at this
      exact hn₀_plus_2_notin (Finset.mem_coe.mp this)
    rw [Submodule.eq_bot_iff] at hws_bot
    exact hws_bot _ hEv_ws


  have hiter_ws : ∀ k : ℕ, SL2GKModule.iterLie M_sl2.F v k ∈
      M_sl2.weightSpace (n₀ - 2 * (↑k : ℤ)) :=
    SL2GKModule.iterLie_F_weight_shift M_sl2 n₀ v hv_mem


  have hfin_nonzero : Set.Finite {k : ℕ | SL2GKModule.iterLie M_sl2.F v k ≠ 0} := by


    let f : ℕ → ℤ := fun k => n₀ - 2 * (↑k : ℤ)
    have hf_inj : Function.Injective f := fun k₁ k₂ h => by
      simp only [f] at h; omega
    apply Set.Finite.subset (S.finite_toSet.preimage hf_inj.injOn)
    intro k hk
    simp only [Set.mem_setOf_eq] at hk
    show f k ∈ (↑S : Set ℤ)
    rw [hS]
    exact (Submodule.ne_bot_iff _).mpr ⟨_, hiter_ws k, hk⟩

  have h0_mem : (0 : ℕ) ∈ {k : ℕ | SL2GKModule.iterLie M_sl2.F v k ≠ 0} := by
    simp [SL2GKModule.iterLie_zero, hv_ne]

  have hfin_ne : {k : ℕ | SL2GKModule.iterLie M_sl2.F v k ≠ 0}.Nonempty :=
    ⟨0, h0_mem⟩

  let T := hfin_nonzero.toFinset
  have hT_ne : T.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]
    exact hfin_ne
  set N := T.max' hT_ne with hN_def
  have hN_mem : SL2GKModule.iterLie M_sl2.F v N ≠ 0 := by
    have := Finset.max'_mem T hT_ne
    rwa [Set.Finite.mem_toFinset] at this
  have hN_succ_zero : SL2GKModule.iterLie M_sl2.F v (N + 1) = 0 := by
    by_contra hne
    have hN1_mem : N + 1 ∈ T := by
      rw [Set.Finite.mem_toFinset]
      exact hne
    have := Finset.le_max' T (N + 1) hN1_mem
    omega

  have hrec := sl2_EF_recurrence M_sl2 n₀ v hv_mem hEv_zero N

  rw [hN_succ_zero, lie_zero] at hrec


  rw [eq_comm] at hrec
  have hscalar_zero : (↑(N + 1) : ℂ) * (↑n₀ - ↑(N : ℤ)) = 0 := by
    by_contra hne
    exact hN_mem (smul_eq_zero.mp hrec |>.resolve_left hne)

  have hN1_ne : (↑(N + 1) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero N

  have hn₀_eq : (↑n₀ : ℂ) = (↑(N : ℤ) : ℂ) := by
    have := mul_eq_zero.mp hscalar_zero
    cases this with
    | inl h => exact absurd h hN1_ne
    | inr h => exact sub_eq_zero.mp h
  have hn₀_eq_int : n₀ = ↑N := by exact_mod_cast hn₀_eq

  omega


theorem sl2_gk_ktype_set_exists
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedBoth) :
    ∃ (S : Finset ℤ), (↑S : Set ℤ) = M_sl2.ktypeSet ∧ S.Nonempty ∧
      (∀ m ∈ S, ∀ m' ∈ S, (m : ℤ) % 2 = (m' : ℤ) % 2) ∧
      (∃ n : ℕ, (n : ℤ) ∈ S ∧ ∀ m ∈ S, m ≤ (n : ℤ)) := by

  have ⟨hba, hbb⟩ := bddAbove_and_bddBelow_of_boundedBoth 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm hbdd

  have hfin : M_sl2.ktypeSet.Finite := BddBelow.finite_of_bddAbove hbb hba

  let S := hfin.toFinset
  have hS_eq : (↑S : Set ℤ) = M_sl2.ktypeSet := hfin.coe_toFinset

  have hne_set := ktypeSet_nonempty_of_irred_admissible M hirr M_sl2
  have hne : S.Nonempty := by
    rwa [← Finset.coe_nonempty, hS_eq]

  have hpar := ktypeSet_uniform_parity M hirr M_sl2
  have hpar_S : ∀ m ∈ S, ∀ m' ∈ S, (m : ℤ) % 2 = (m' : ℤ) % 2 := by
    intro m hm m' hm'
    exact hpar m (hfin.mem_toFinset.mp hm) m' (hfin.mem_toFinset.mp hm')

  have hmax_val := S.max' hne
  have hmax_mem : S.max' hne ∈ S := Finset.max'_mem S hne
  have hmax_le : ∀ m ∈ S, m ≤ S.max' hne := fun m hm => Finset.le_max' S m hm
  have hmax_nn : (0 : ℤ) ≤ S.max' hne := ktypeSet_max_nonneg M hirr M_sl2 S hS_eq hne
  refine ⟨S, hS_eq, hne, hpar_S, ⟨(S.max' hne).toNat, ?_, ?_⟩⟩
  · rwa [Int.toNat_of_nonneg hmax_nn]
  · intro m hm
    rw [Int.toNat_of_nonneg hmax_nn]
    exact hmax_le m hm

noncomputable def sl2_gk_finiteDim_label
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedBoth) :
    SL2IrredGKModule :=


  let hS_exists := sl2_gk_ktype_set_exists 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd
  let n := hS_exists.choose_spec.2.2.2.choose
  .finiteDim n

noncomputable def sl2_finiteDim_ρH (n : ℕ) : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun v i := ((n : ℂ) - 2 * (i : ℂ)) * v i
  map_add' u w := by ext i; simp [mul_add]
  map_smul' c v := by ext i; simp [RingHom.id_apply]; ring

noncomputable def sl2_finiteDim_ρE (n : ℕ) : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun v i := if h : (i : ℕ) + 1 ≤ n then ((n : ℂ) - (i : ℂ)) * v ⟨i + 1, by omega⟩ else 0
  map_add' u w := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c v := by
    ext i; simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

noncomputable def sl2_finiteDim_ρF (n : ℕ) : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun v i := if h : 0 < (i : ℕ) then ((i : ℂ)) * v ⟨i - 1, by omega⟩ else 0
  map_add' u w := by ext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c v := by
    ext i; simp only [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; split_ifs <;> ring

lemma sl2_finiteDim_bracket_HE (n : ℕ) :
    sl2_finiteDim_ρH n ∘ₗ sl2_finiteDim_ρE n - sl2_finiteDim_ρE n ∘ₗ sl2_finiteDim_ρH n =
    (2 : ℂ) • sl2_finiteDim_ρE n := by
  ext v ⟨i, hi⟩
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    sl2_finiteDim_ρH, sl2_finiteDim_ρE, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · push_cast; ring
  · simp

lemma sl2_finiteDim_bracket_HF (n : ℕ) :
    sl2_finiteDim_ρH n ∘ₗ sl2_finiteDim_ρF n - sl2_finiteDim_ρF n ∘ₗ sl2_finiteDim_ρH n =
    -(2 : ℂ) • sl2_finiteDim_ρF n := by
  ext v ⟨i, hi⟩
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    sl2_finiteDim_ρH, sl2_finiteDim_ρF, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · simp only [Nat.cast_sub (show 1 ≤ i from h)]; ring
  · simp

lemma sl2_finiteDim_bracket_EF (n : ℕ) :
    sl2_finiteDim_ρE n ∘ₗ sl2_finiteDim_ρF n - sl2_finiteDim_ρF n ∘ₗ sl2_finiteDim_ρE n =
    sl2_finiteDim_ρH n := by
  ext v ⟨i, hi⟩
  simp only [LinearMap.comp_apply, LinearMap.sub_apply,
    sl2_finiteDim_ρH, sl2_finiteDim_ρE, sl2_finiteDim_ρF,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply]
  simp only [dif_pos (Nat.succ_pos i)]

  have hfin1 : ∀ (h : i + 1 - 1 < n + 1), (⟨i + 1 - 1, h⟩ : Fin (n+1)) = ⟨i, hi⟩ :=
    fun _ => Fin.ext (Nat.succ_sub_one i)
  simp only [hfin1]
  by_cases h2 : 0 < i
  · simp only [dif_pos h2]
    have h3 : i - 1 + 1 ≤ n := by omega
    simp only [dif_pos h3]

    have hfin2 : ∀ (h : i - 1 + 1 < n + 1), (⟨i - 1 + 1, h⟩ : Fin (n+1)) = ⟨i, hi⟩ :=
      fun _ => Fin.ext (Nat.succ_pred_eq_of_pos h2)
    simp only [hfin2, Nat.cast_sub h2]
    by_cases h1 : i + 1 ≤ n
    · simp only [dif_pos h1]; push_cast; ring
    · simp only [dif_neg h1]; push_cast
      have h_in : (i : ℂ) = (n : ℂ) := by exact_mod_cast (show i = n from by omega)
      rw [h_in]; ring
  · simp only [dif_neg h2]
    have h_i0 : i = 0 := by omega
    subst h_i0
    by_cases h1 : 0 + 1 ≤ n
    · simp only [dif_pos h1]; push_cast; ring
    · simp only [dif_neg h1]; push_cast
      have h_n0 : (n : ℂ) = 0 := by exact_mod_cast (show n = 0 from by omega)
      rw [h_n0]; ring

noncomputable def sl2_gk_finiteDim_realization
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedBoth) :
    (sl2_gk_finiteDim_label 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).Realization 𝔤 K 𝔨 Ad := by
  unfold sl2_gk_finiteDim_label

  let hS_exists := sl2_gk_ktype_set_exists 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd
  set nn := hS_exists.choose_spec.2.2.2.choose with hnn_def

  let ρH := sl2_finiteDim_ρH nn
  let ρE := sl2_finiteDim_ρE nn
  let ρF := sl2_finiteDim_ρF nn

  have hHE : ρH ∘ₗ ρE - ρE ∘ₗ ρH = (2 : ℂ) • ρE := sl2_finiteDim_bracket_HE nn
  have hHF : ρH ∘ₗ ρF - ρF ∘ₗ ρH = -(2 : ℂ) • ρF := sl2_finiteDim_bracket_HF nn
  have hEF : ρE ∘ₗ ρF - ρF ∘ₗ ρE = ρH := sl2_finiteDim_bracket_EF nn


  let ρ_hom : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ (Fin (nn + 1) → ℂ) :=
    sl2_lieHom_from_generators 𝔤 M_sl2.H M_sl2.E M_sl2.F M_sl2.getBasis
      M_sl2.getBasis_H M_sl2.getBasis_E M_sl2.getBasis_F
      M_sl2.bracket_HE M_sl2.bracket_HF M_sl2.bracket_EF
      ρH ρE ρF hHE hHF hEF
  let instLRM := sl2_lieRingModule_from_generators 𝔤 (Fin (nn + 1) → ℂ) ρ_hom
  let instLM := sl2_lieModule_from_generators 𝔤 (Fin (nn + 1) → ℂ) ρ_hom
  exact {
    W := Fin (nn + 1) → ℂ
    instAddCommGroup := inferInstance
    instModule := inferInstance
    instLieRingModule := instLRM
    instLieModule := instLM
    gkmod := @sl2_model_gkmod 𝔤 _ _ K _ 𝔨 Ad (Fin (nn + 1) → ℂ) _ _ instLRM instLM
    casimirScalar := _
    casimir_eq := rfl
  }

theorem sl2_nonzero_gk_hom_of_irred_injective
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W]
    (M : GKModule 𝔤 K 𝔨 Ad V) (N : GKModule 𝔤 K 𝔨 Ad W)
    (hirr : M.IsIrreducibleGKModule)
    (φ : GKModuleHom M N) (hφ : φ.toLinearMap ≠ 0) :
    Function.Injective φ.toLinearMap := by
  exact sorry

theorem sl2_finiteDim_highest_weight_hom
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedBoth) :
    ∃ (φ : GKModuleHom M
      (sl2_gk_finiteDim_realization 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).gkmod),
      φ.toLinearMap ≠ 0 := by
  exact sorry

theorem sl2_finiteDim_gk_hom_surjective
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedBoth)
    (φ : GKModuleHom M
      (sl2_gk_finiteDim_realization 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).gkmod)
    (hφ_inj : Function.Injective φ.toLinearMap) :
    Function.Surjective φ.toLinearMap := by
  exact sorry


theorem sl2_gk_finiteDim_iso
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedBoth) :
    M.IsIsomorphicGK (sl2_gk_finiteDim_realization 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).gkmod := by

  obtain ⟨φ, hφ_ne⟩ := sl2_finiteDim_highest_weight_hom
    𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd

  have hφ_inj : Function.Injective φ.toLinearMap :=
    sl2_nonzero_gk_hom_of_irred_injective 𝔤 K 𝔨 Ad V M
      (sl2_gk_finiteDim_realization 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).gkmod hirr φ hφ_ne

  have hφ_surj : Function.Surjective φ.toLinearMap :=
    sl2_finiteDim_gk_hom_surjective 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd φ hφ_inj

  exact ⟨φ, hφ_inj, hφ_surj⟩

lemma sl2_gk_classification_finiteDim
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (hirr : M.IsIrreducibleGKModule)
    (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedBoth) :
    ∃ (μ : SL2IrredGKModule) (R : SL2IrredGKModule.Realization.{_, _, 0} μ 𝔤 K 𝔨 Ad),
      M.IsIsomorphicGK R.gkmod := by

  let μ := sl2_gk_finiteDim_label 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd

  let R := sl2_gk_finiteDim_realization 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd
  exact ⟨μ, R, sl2_gk_finiteDim_iso 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd⟩

noncomputable def principalSeries_ρH (ν : ℂ) (ε : ZMod 2) :
    (ℤ → ℂ) →ₗ[ℂ] (ℤ → ℂ) where
  toFun f m := (m : ℂ) * f m
  map_add' u w := by ext m; simp [mul_add]
  map_smul' c v := by ext m; simp [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; ring

noncomputable def principalSeries_ρE (ν : ℂ) (ε : ZMod 2) :
    (ℤ → ℂ) →ₗ[ℂ] (ℤ → ℂ) where
  toFun f m := (1/2 : ℂ) * (ν + (m : ℂ) - 1) * f (m - 2)
  map_add' u w := by ext m; simp [Pi.add_apply]; ring
  map_smul' c v := by ext m; simp [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; ring

noncomputable def principalSeries_ρF (ν : ℂ) (ε : ZMod 2) :
    (ℤ → ℂ) →ₗ[ℂ] (ℤ → ℂ) where
  toFun f m := (1/2 : ℂ) * (ν - (m : ℂ) - 1) * f (m + 2)
  map_add' u w := by ext m; simp [Pi.add_apply]; ring
  map_smul' c v := by ext m; simp [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma principalSeries_bracket_HE (ν : ℂ) (ε : ZMod 2) :
    principalSeries_ρH ν ε ∘ₗ principalSeries_ρE ν ε -
    principalSeries_ρE ν ε ∘ₗ principalSeries_ρH ν ε =
    (2 : ℂ) • principalSeries_ρE ν ε := by
  ext f m
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    principalSeries_ρH, principalSeries_ρE, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

lemma principalSeries_bracket_HF (ν : ℂ) (ε : ZMod 2) :
    principalSeries_ρH ν ε ∘ₗ principalSeries_ρF ν ε -
    principalSeries_ρF ν ε ∘ₗ principalSeries_ρH ν ε =
    -(2 : ℂ) • principalSeries_ρF ν ε := by
  ext f m
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    principalSeries_ρH, principalSeries_ρF, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

lemma principalSeries_bracket_EF (ν : ℂ) (ε : ZMod 2) :
    principalSeries_ρE ν ε ∘ₗ principalSeries_ρF ν ε -
    principalSeries_ρF ν ε ∘ₗ principalSeries_ρE ν ε =
    principalSeries_ρH ν ε := by
  ext f m
  simp only [LinearMap.comp_apply, LinearMap.sub_apply,
    principalSeries_ρH, principalSeries_ρE, principalSeries_ρF,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply]
  push_cast
  ring

noncomputable def sl2_gk_principalSeries_realization
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (hAd_lie : ∀ (k : K) (X Y : 𝔤), Ad k ⁅X, Y⁆ = ⁅Ad k X, Ad k Y⁆)
    (h e f_elem : 𝔤)
    (b : Basis (Fin 3) ℂ 𝔤) (bH : b 0 = h) (bE : b 1 = e) (bF : b 2 = f_elem)
    (hHE_src : ⁅h, e⁆ = (2 : ℤ) • e)
    (hHF_src : ⁅h, f_elem⁆ = (-2 : ℤ) • f_elem)
    (hEF_src : ⁅e, f_elem⁆ = h)
    (ν : ℂ) (ε : ZMod 2) :
    (SL2IrredGKModule.principalSeries ν ε).Realization 𝔤 K 𝔨 Ad := by


  let ρH := principalSeries_ρH ν ε
  let ρE := principalSeries_ρE ν ε
  let ρF := principalSeries_ρF ν ε

  have hHE : ρH ∘ₗ ρE - ρE ∘ₗ ρH = (2 : ℂ) • ρE := principalSeries_bracket_HE ν ε
  have hHF : ρH ∘ₗ ρF - ρF ∘ₗ ρH = -(2 : ℂ) • ρF := principalSeries_bracket_HF ν ε
  have hEF : ρE ∘ₗ ρF - ρF ∘ₗ ρE = ρH := principalSeries_bracket_EF ν ε
  let ρ_hom : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ (ℤ → ℂ) :=
    sl2_lieHom_from_generators 𝔤 h e f_elem b bH bE bF hHE_src hHF_src hEF_src ρH ρE ρF hHE hHF hEF
  let instLRM := sl2_lieRingModule_from_generators 𝔤 (ℤ → ℂ) ρ_hom
  let instLM := sl2_lieModule_from_generators 𝔤 (ℤ → ℂ) ρ_hom
  exact {
    W := ℤ → ℂ
    instAddCommGroup := inferInstance
    instModule := inferInstance
    instLieRingModule := instLRM
    instLieModule := instLM
    gkmod := @sl2_model_gkmod 𝔤 _ _ K _ 𝔨 Ad (ℤ → ℂ) _ _ instLRM instLM
    casimirScalar := _
    casimir_eq := rfl
  }


opaque sl2_gk_principalSeries_params_exists
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .unboundedBoth) :
    ℂ × ZMod 2 := (0, 0)

noncomputable def sl2_gk_principalSeries_nu
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .unboundedBoth) :
    ℂ :=
  (sl2_gk_principalSeries_params_exists 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).1

noncomputable def sl2_gk_principalSeries_epsilon
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .unboundedBoth) :
    ZMod 2 :=
  (sl2_gk_principalSeries_params_exists 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).2

noncomputable def sl2_gk_principalSeries_label
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .unboundedBoth) :
    SL2IrredGKModule :=
  SL2IrredGKModule.principalSeries
    (sl2_gk_principalSeries_nu 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd)
    (sl2_gk_principalSeries_epsilon 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd)

noncomputable def sl2_gk_principalSeries_realization_from_label
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .unboundedBoth) :
    (sl2_gk_principalSeries_label 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).Realization 𝔤 K 𝔨 Ad := by
  unfold sl2_gk_principalSeries_label
  let ν := sl2_gk_principalSeries_nu 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd
  let ε := sl2_gk_principalSeries_epsilon 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd
  let ρH := principalSeries_ρH ν ε
  let ρE := principalSeries_ρE ν ε
  let ρF := principalSeries_ρF ν ε
  have hHE : ρH ∘ₗ ρE - ρE ∘ₗ ρH = (2 : ℂ) • ρE := principalSeries_bracket_HE ν ε
  have hHF : ρH ∘ₗ ρF - ρF ∘ₗ ρH = -(2 : ℂ) • ρF := principalSeries_bracket_HF ν ε
  have hEF : ρE ∘ₗ ρF - ρF ∘ₗ ρE = ρH := principalSeries_bracket_EF ν ε
  let ρ_hom : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ (ℤ → ℂ) :=
    sl2_lieHom_from_generators 𝔤 M_sl2.H M_sl2.E M_sl2.F M_sl2.getBasis
      M_sl2.getBasis_H M_sl2.getBasis_E M_sl2.getBasis_F
      M_sl2.bracket_HE M_sl2.bracket_HF M_sl2.bracket_EF

      ρH ρE ρF hHE hHF hEF
  letI instLRM := sl2_lieRingModule_from_generators 𝔤 (ℤ → ℂ) ρ_hom
  letI instLM := sl2_lieModule_from_generators 𝔤 (ℤ → ℂ) ρ_hom
  exact {
    W := ℤ → ℂ
    instAddCommGroup := inferInstance
    instModule := inferInstance
    instLieRingModule := instLRM
    instLieModule := instLM
    gkmod := @sl2_model_gkmod 𝔤 _ _ K _ 𝔨 Ad (ℤ → ℂ) _ _ instLRM instLM
    casimirScalar := _
    casimir_eq := rfl
  }


theorem sl2_principalSeries_weight_space_hom
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .unboundedBoth)
    (R : (sl2_gk_principalSeries_label 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).Realization
      𝔤 K 𝔨 Ad) :
    ∃ (φ : GKModuleHom M R.gkmod), φ.toLinearMap ≠ 0 := by
  exact sorry


theorem sl2_principalSeries_gk_hom_surjective
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .unboundedBoth)
    (R : (sl2_gk_principalSeries_label 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).Realization
      𝔤 K 𝔨 Ad)
    (φ : GKModuleHom M R.gkmod) (hφ_inj : Function.Injective φ.toLinearMap) :
    Function.Surjective φ.toLinearMap := by
  exact sorry


theorem sl2_gk_principalSeries_iso
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .unboundedBoth)
    (R : (sl2_gk_principalSeries_label 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).Realization
      𝔤 K 𝔨 Ad) :
    M.IsIsomorphicGK R.gkmod := by

  obtain ⟨φ, hφ_ne⟩ := sl2_principalSeries_weight_space_hom
    𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd R

  have hφ_inj : Function.Injective φ.toLinearMap :=
    sl2_nonzero_gk_hom_of_irred_injective 𝔤 K 𝔨 Ad V M R.gkmod hirr φ hφ_ne

  have hφ_surj : Function.Surjective φ.toLinearMap :=
    sl2_principalSeries_gk_hom_surjective 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd R φ hφ_inj

  exact ⟨φ, hφ_inj, hφ_surj⟩

theorem sl2_gk_classification_principalSeries
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (hirr : M.IsIrreducibleGKModule)
    (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .unboundedBoth) :
    ∃ (μ : SL2IrredGKModule) (R : SL2IrredGKModule.Realization.{_, _, 0} μ 𝔤 K 𝔨 Ad),
      M.IsIsomorphicGK R.gkmod := by

  let μ := sl2_gk_principalSeries_label 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd

  let R := sl2_gk_principalSeries_realization_from_label 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd
  exact ⟨μ, R, sl2_gk_principalSeries_iso 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd R⟩


noncomputable def sl2_gk_discreteSeriesPlus_minKType_exists
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedBelow) :
    { n : ℕ // n ≥ 1 } := ⟨1, le_refl 1⟩

noncomputable def sl2_gk_discreteSeriesPlus_minKType
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedBelow) :
    ℕ :=
  (sl2_gk_discreteSeriesPlus_minKType_exists 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).val

noncomputable def discreteSeriesPlus_ρH (n : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun f k := ((n : ℂ) + 2 * (k : ℂ)) * f k
  map_add' u w := by ext k; simp [mul_add]
  map_smul' c v := by ext k; simp [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; ring

noncomputable def discreteSeriesPlus_ρE (n : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun f k := match k with
    | 0 => 0
    | Nat.succ j => -((n : ℂ) + (j : ℂ)) * f j
  map_add' u w := by
    ext k; match k with
    | 0 => simp
    | Nat.succ j => simp [Pi.add_apply]; ring
  map_smul' c v := by
    ext k; match k with
    | 0 => simp
    | Nat.succ j => simp [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; ring

noncomputable def discreteSeriesPlus_ρF (n : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun f k := ((k : ℂ) + 1) * f (k + 1)
  map_add' u w := by ext k; simp [Pi.add_apply]; ring
  map_smul' c v := by ext k; simp [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma discreteSeriesPlus_bracket_HE (n : ℕ) :
    discreteSeriesPlus_ρH n ∘ₗ discreteSeriesPlus_ρE n -
    discreteSeriesPlus_ρE n ∘ₗ discreteSeriesPlus_ρH n =
    (2 : ℂ) • discreteSeriesPlus_ρE n := by
  ext f k
  match k with
  | 0 =>
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      discreteSeriesPlus_ρH, discreteSeriesPlus_ρE, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  | Nat.succ j =>
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      discreteSeriesPlus_ρH, discreteSeriesPlus_ρE, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring

lemma discreteSeriesPlus_bracket_HF (n : ℕ) :
    discreteSeriesPlus_ρH n ∘ₗ discreteSeriesPlus_ρF n -
    discreteSeriesPlus_ρF n ∘ₗ discreteSeriesPlus_ρH n =
    -(2 : ℂ) • discreteSeriesPlus_ρF n := by
  ext f k
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    discreteSeriesPlus_ρH, discreteSeriesPlus_ρF, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

lemma discreteSeriesPlus_bracket_EF (n : ℕ) :
    discreteSeriesPlus_ρE n ∘ₗ discreteSeriesPlus_ρF n -
    discreteSeriesPlus_ρF n ∘ₗ discreteSeriesPlus_ρE n =
    discreteSeriesPlus_ρH n := by
  ext f k
  match k with
  | 0 =>
    simp only [LinearMap.comp_apply, LinearMap.sub_apply,
      discreteSeriesPlus_ρH, discreteSeriesPlus_ρE, discreteSeriesPlus_ρF,
      LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply]
    push_cast
    ring
  | Nat.succ j =>
    simp only [LinearMap.comp_apply, LinearMap.sub_apply,
      discreteSeriesPlus_ρH, discreteSeriesPlus_ρE, discreteSeriesPlus_ρF,
      LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply]
    push_cast
    ring

noncomputable def sl2_gk_discreteSeriesPlus_realization
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (hAd_lie : ∀ (k : K) (X Y : 𝔤), Ad k ⁅X, Y⁆ = ⁅Ad k X, Ad k Y⁆)
    (h e f_elem : 𝔤)
    (b : Basis (Fin 3) ℂ 𝔤) (bH : b 0 = h) (bE : b 1 = e) (bF : b 2 = f_elem)
    (hHE_src : ⁅h, e⁆ = (2 : ℤ) • e)
    (hHF_src : ⁅h, f_elem⁆ = (-2 : ℤ) • f_elem)
    (hEF_src : ⁅e, f_elem⁆ = h)
    (n : ℕ) (hn : n ≥ 2) :
    (SL2IrredGKModule.discreteSeriesPlus n hn).Realization 𝔤 K 𝔨 Ad := by

  let ρH := discreteSeriesPlus_ρH n
  let ρE := discreteSeriesPlus_ρE n
  let ρF := discreteSeriesPlus_ρF n

  have hHE : ρH ∘ₗ ρE - ρE ∘ₗ ρH = (2 : ℂ) • ρE := discreteSeriesPlus_bracket_HE n
  have hHF : ρH ∘ₗ ρF - ρF ∘ₗ ρH = -(2 : ℂ) • ρF := discreteSeriesPlus_bracket_HF n
  have hEF : ρE ∘ₗ ρF - ρF ∘ₗ ρE = ρH := discreteSeriesPlus_bracket_EF n


  let ρ_hom : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ (ℕ → ℂ) :=
    sl2_lieHom_from_generators 𝔤 h e f_elem b bH bE bF hHE_src hHF_src hEF_src ρH ρE ρF hHE hHF hEF
  letI instLRM := sl2_lieRingModule_from_generators 𝔤 (ℕ → ℂ) ρ_hom
  letI instLM := sl2_lieModule_from_generators 𝔤 (ℕ → ℂ) ρ_hom

  exact {
    W := ℕ → ℂ
    instAddCommGroup := inferInstance
    instModule := inferInstance
    instLieRingModule := instLRM
    instLieModule := instLM
    gkmod := @sl2_model_gkmod 𝔤 _ _ K _ 𝔨 Ad (ℕ → ℂ) _ _ instLRM instLM
    casimirScalar := _
    casimir_eq := rfl
  }

noncomputable def sl2_gk_limitDiscretePlus_realization
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (hAd_lie : ∀ (k : K) (X Y : 𝔤), Ad k ⁅X, Y⁆ = ⁅Ad k X, Ad k Y⁆)
    (h e f_elem : 𝔤)
    (b : Basis (Fin 3) ℂ 𝔤) (bH : b 0 = h) (bE : b 1 = e) (bF : b 2 = f_elem)
    (hHE_src : ⁅h, e⁆ = (2 : ℤ) • e)
    (hHF_src : ⁅h, f_elem⁆ = (-2 : ℤ) • f_elem)
    (hEF_src : ⁅e, f_elem⁆ = h) :
    SL2IrredGKModule.limitDiscretePlus.Realization 𝔤 K 𝔨 Ad := by

  let ρH := discreteSeriesPlus_ρH 1
  let ρE := discreteSeriesPlus_ρE 1
  let ρF := discreteSeriesPlus_ρF 1

  have hHE : ρH ∘ₗ ρE - ρE ∘ₗ ρH = (2 : ℂ) • ρE := discreteSeriesPlus_bracket_HE 1
  have hHF : ρH ∘ₗ ρF - ρF ∘ₗ ρH = -(2 : ℂ) • ρF := discreteSeriesPlus_bracket_HF 1
  have hEF : ρE ∘ₗ ρF - ρF ∘ₗ ρE = ρH := discreteSeriesPlus_bracket_EF 1
  let ρ_hom : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ (ℕ → ℂ) :=
    sl2_lieHom_from_generators 𝔤 h e f_elem b bH bE bF hHE_src hHF_src hEF_src ρH ρE ρF hHE hHF hEF
  letI instLRM := sl2_lieRingModule_from_generators 𝔤 (ℕ → ℂ) ρ_hom
  letI instLM := sl2_lieModule_from_generators 𝔤 (ℕ → ℂ) ρ_hom

  exact {
    W := ℕ → ℂ
    instAddCommGroup := inferInstance
    instModule := inferInstance
    instLieRingModule := instLRM
    instLieModule := instLM
    gkmod := @sl2_model_gkmod 𝔤 _ _ K _ 𝔨 Ad (ℕ → ℂ) _ _ instLRM instLM
    casimirScalar := _
    casimir_eq := rfl
  }

noncomputable def sl2_gk_discreteSeriesPlus_label
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedBelow) :
    SL2IrredGKModule :=
  let n₀ := sl2_gk_discreteSeriesPlus_minKType 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd
  if hn₀ : n₀ ≥ 2 then
    SL2IrredGKModule.discreteSeriesPlus n₀ hn₀
  else
    SL2IrredGKModule.limitDiscretePlus

noncomputable def sl2_gk_discreteSeriesPlus_realization_from_label
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedBelow) :
    (sl2_gk_discreteSeriesPlus_label 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).Realization 𝔤 K 𝔨 Ad := by
  unfold sl2_gk_discreteSeriesPlus_label
  let n₀ := sl2_gk_discreteSeriesPlus_minKType 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd

  by_cases hn₀ : n₀ ≥ 2
  ·
    simp only [ge_iff_le]
    let ρH := discreteSeriesPlus_ρH n₀
    let ρE := discreteSeriesPlus_ρE n₀
    let ρF := discreteSeriesPlus_ρF n₀
    have hHE : ρH ∘ₗ ρE - ρE ∘ₗ ρH = (2 : ℂ) • ρE := discreteSeriesPlus_bracket_HE n₀
    have hHF : ρH ∘ₗ ρF - ρF ∘ₗ ρH = -(2 : ℂ) • ρF := discreteSeriesPlus_bracket_HF n₀
    have hEF : ρE ∘ₗ ρF - ρF ∘ₗ ρE = ρH := discreteSeriesPlus_bracket_EF n₀
    let ρ_hom : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ (ℕ → ℂ) :=
      sl2_lieHom_from_generators 𝔤 M_sl2.H M_sl2.E M_sl2.F M_sl2.getBasis

        M_sl2.getBasis_H M_sl2.getBasis_E M_sl2.getBasis_F
        M_sl2.bracket_HE M_sl2.bracket_HF M_sl2.bracket_EF

        ρH ρE ρF hHE hHF hEF

    letI instLRM := sl2_lieRingModule_from_generators 𝔤 (ℕ → ℂ) ρ_hom
    letI instLM := sl2_lieModule_from_generators 𝔤 (ℕ → ℂ) ρ_hom

    exact {
      W := ℕ → ℂ
      instAddCommGroup := inferInstance
      instModule := inferInstance
      instLieRingModule := instLRM
      instLieModule := instLM
      gkmod := @sl2_model_gkmod 𝔤 _ _ K _ 𝔨 Ad (ℕ → ℂ) _ _ instLRM instLM
      casimirScalar := _
      casimir_eq := rfl
    }

  ·
    simp only [ge_iff_le]
    let ρH := discreteSeriesPlus_ρH 1
    let ρE := discreteSeriesPlus_ρE 1
    let ρF := discreteSeriesPlus_ρF 1
    have hHE : ρH ∘ₗ ρE - ρE ∘ₗ ρH = (2 : ℂ) • ρE := discreteSeriesPlus_bracket_HE 1
    have hHF : ρH ∘ₗ ρF - ρF ∘ₗ ρH = -(2 : ℂ) • ρF := discreteSeriesPlus_bracket_HF 1
    have hEF : ρE ∘ₗ ρF - ρF ∘ₗ ρE = ρH := discreteSeriesPlus_bracket_EF 1
    let ρ_hom : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ (ℕ → ℂ) :=
      sl2_lieHom_from_generators 𝔤 M_sl2.H M_sl2.E M_sl2.F M_sl2.getBasis

        M_sl2.getBasis_H M_sl2.getBasis_E M_sl2.getBasis_F
        M_sl2.bracket_HE M_sl2.bracket_HF M_sl2.bracket_EF

        ρH ρE ρF hHE hHF hEF

    letI instLRM := sl2_lieRingModule_from_generators 𝔤 (ℕ → ℂ) ρ_hom
    letI instLM := sl2_lieModule_from_generators 𝔤 (ℕ → ℂ) ρ_hom

    exact {
      W := ℕ → ℂ
      instAddCommGroup := inferInstance
      instModule := inferInstance
      instLieRingModule := instLRM
      instLieModule := instLM
      gkmod := @sl2_model_gkmod 𝔤 _ _ K _ 𝔨 Ad (ℕ → ℂ) _ _ instLRM instLM
      casimirScalar := _
      casimir_eq := rfl
    }

theorem sl2_discreteSeriesPlus_lowest_weight_hom
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedBelow)
    (R : (sl2_gk_discreteSeriesPlus_label 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).Realization
      𝔤 K 𝔨 Ad) :
    ∃ (φ : GKModuleHom M R.gkmod), φ.toLinearMap ≠ 0 := by
  exact sorry

theorem sl2_discreteSeriesPlus_gk_hom_surjective
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedBelow)
    (R : (sl2_gk_discreteSeriesPlus_label 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).Realization
      𝔤 K 𝔨 Ad)
    (φ : GKModuleHom M R.gkmod) (hφ_inj : Function.Injective φ.toLinearMap) :
    Function.Surjective φ.toLinearMap := by
  exact sorry


theorem sl2_gk_discreteSeriesPlus_iso
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedBelow)
    (R : (sl2_gk_discreteSeriesPlus_label 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).Realization
      𝔤 K 𝔨 Ad) :
    M.IsIsomorphicGK R.gkmod := by

  obtain ⟨φ, hφ_ne⟩ := sl2_discreteSeriesPlus_lowest_weight_hom
    𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd R

  have hφ_inj : Function.Injective φ.toLinearMap :=
    sl2_nonzero_gk_hom_of_irred_injective 𝔤 K 𝔨 Ad V M R.gkmod hirr φ hφ_ne

  have hφ_surj : Function.Surjective φ.toLinearMap :=
    sl2_discreteSeriesPlus_gk_hom_surjective 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd R φ hφ_inj

  exact ⟨φ, hφ_inj, hφ_surj⟩

theorem sl2_gk_classification_discreteSeriesPlus
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (hirr : M.IsIrreducibleGKModule)
    (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedBelow) :
    ∃ (μ : SL2IrredGKModule) (R : SL2IrredGKModule.Realization.{_, _, 0} μ 𝔤 K 𝔨 Ad),
      M.IsIsomorphicGK R.gkmod := by

  let μ := sl2_gk_discreteSeriesPlus_label 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd

  let R := sl2_gk_discreteSeriesPlus_realization_from_label 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd
  exact ⟨μ, R, sl2_gk_discreteSeriesPlus_iso 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd R⟩


noncomputable def sl2_gk_discreteSeriesMinus_maxKType_exists
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedAbove) :
    { n : ℕ // n ≥ 1 } := ⟨1, le_refl 1⟩

def sl2_gk_discreteSeriesMinus_maxKType
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedAbove) :
    ℕ :=
  (sl2_gk_discreteSeriesMinus_maxKType_exists 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).val

def sl2_gk_discreteSeriesMinus_label
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedAbove) :
    SL2IrredGKModule :=
  let n₀ := sl2_gk_discreteSeriesMinus_maxKType 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd
  if hn₀ : n₀ ≥ 2 then
    SL2IrredGKModule.discreteSeriesMinus n₀ hn₀
  else
    SL2IrredGKModule.limitDiscreteMinus

noncomputable def discreteSeriesMinus_ρH (n : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun f k := -((n : ℂ) + 2 * (k : ℂ)) * f k
  map_add' u w := by ext k; simp [mul_add]
  map_smul' c v := by ext k; simp [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; ring

noncomputable def discreteSeriesMinus_ρE (n : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun f k := ((k : ℂ) + 1) * f (k + 1)
  map_add' u w := by ext k; simp [Pi.add_apply]; ring
  map_smul' c v := by ext k; simp [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; ring

noncomputable def discreteSeriesMinus_ρF (n : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun f k := match k with
    | 0 => 0
    | Nat.succ j => -((n : ℂ) + (j : ℂ)) * f j
  map_add' u w := by
    ext k; match k with
    | 0 => simp
    | Nat.succ j => simp [Pi.add_apply]; ring
  map_smul' c v := by
    ext k; match k with
    | 0 => simp
    | Nat.succ j => simp [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma discreteSeriesMinus_bracket_HE (n : ℕ) :
    discreteSeriesMinus_ρH n ∘ₗ discreteSeriesMinus_ρE n -
    discreteSeriesMinus_ρE n ∘ₗ discreteSeriesMinus_ρH n =
    (2 : ℂ) • discreteSeriesMinus_ρE n := by
  ext f k
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    discreteSeriesMinus_ρH, discreteSeriesMinus_ρE, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

lemma discreteSeriesMinus_bracket_HF (n : ℕ) :
    discreteSeriesMinus_ρH n ∘ₗ discreteSeriesMinus_ρF n -
    discreteSeriesMinus_ρF n ∘ₗ discreteSeriesMinus_ρH n =
    -(2 : ℂ) • discreteSeriesMinus_ρF n := by
  ext f k
  match k with
  | 0 =>
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      discreteSeriesMinus_ρH, discreteSeriesMinus_ρF, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  | Nat.succ j =>
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      discreteSeriesMinus_ρH, discreteSeriesMinus_ρF, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring

lemma discreteSeriesMinus_bracket_EF (n : ℕ) :
    discreteSeriesMinus_ρE n ∘ₗ discreteSeriesMinus_ρF n -
    discreteSeriesMinus_ρF n ∘ₗ discreteSeriesMinus_ρE n =
    discreteSeriesMinus_ρH n := by
  ext f k
  match k with
  | 0 =>
    simp only [LinearMap.comp_apply, LinearMap.sub_apply,
      discreteSeriesMinus_ρH, discreteSeriesMinus_ρE, discreteSeriesMinus_ρF,
      LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply]
    push_cast
    ring
  | Nat.succ j =>
    simp only [LinearMap.comp_apply, LinearMap.sub_apply,
      discreteSeriesMinus_ρH, discreteSeriesMinus_ρE, discreteSeriesMinus_ρF,
      LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply]
    push_cast
    ring

noncomputable def sl2_gk_discreteSeriesMinus_realization
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (hAd_lie : ∀ (k : K) (X Y : 𝔤), Ad k ⁅X, Y⁆ = ⁅Ad k X, Ad k Y⁆)
    (h e f_elem : 𝔤)
    (b : Basis (Fin 3) ℂ 𝔤) (bH : b 0 = h) (bE : b 1 = e) (bF : b 2 = f_elem)
    (hHE_src : ⁅h, e⁆ = (2 : ℤ) • e)
    (hHF_src : ⁅h, f_elem⁆ = (-2 : ℤ) • f_elem)
    (hEF_src : ⁅e, f_elem⁆ = h)
    (n : ℕ) (hn : n ≥ 2) :
    (SL2IrredGKModule.discreteSeriesMinus n hn).Realization 𝔤 K 𝔨 Ad := by

  let ρH := discreteSeriesMinus_ρH n
  let ρE := discreteSeriesMinus_ρE n
  let ρF := discreteSeriesMinus_ρF n

  have hHE : ρH ∘ₗ ρE - ρE ∘ₗ ρH = (2 : ℂ) • ρE := discreteSeriesMinus_bracket_HE n
  have hHF : ρH ∘ₗ ρF - ρF ∘ₗ ρH = -(2 : ℂ) • ρF := discreteSeriesMinus_bracket_HF n
  have hEF : ρE ∘ₗ ρF - ρF ∘ₗ ρE = ρH := discreteSeriesMinus_bracket_EF n
  let ρ_hom : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ (ℕ → ℂ) :=
    sl2_lieHom_from_generators 𝔤 h e f_elem b bH bE bF hHE_src hHF_src hEF_src ρH ρE ρF hHE hHF hEF
  letI instLRM := sl2_lieRingModule_from_generators 𝔤 (ℕ → ℂ) ρ_hom
  letI instLM := sl2_lieModule_from_generators 𝔤 (ℕ → ℂ) ρ_hom

  exact {
    W := ℕ → ℂ
    instAddCommGroup := inferInstance
    instModule := inferInstance
    instLieRingModule := instLRM
    instLieModule := instLM
    gkmod := @sl2_model_gkmod 𝔤 _ _ K _ 𝔨 Ad (ℕ → ℂ) _ _ instLRM instLM
    casimirScalar := _
    casimir_eq := rfl
  }

noncomputable def sl2_gk_limitDiscreteMinus_realization
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤] [FiniteDimensional ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (hAd_lie : ∀ (k : K) (X Y : 𝔤), Ad k ⁅X, Y⁆ = ⁅Ad k X, Ad k Y⁆)
    (h e f_elem : 𝔤)
    (b : Basis (Fin 3) ℂ 𝔤) (bH : b 0 = h) (bE : b 1 = e) (bF : b 2 = f_elem)
    (hHE_src : ⁅h, e⁆ = (2 : ℤ) • e)
    (hHF_src : ⁅h, f_elem⁆ = (-2 : ℤ) • f_elem)
    (hEF_src : ⁅e, f_elem⁆ = h) :
    SL2IrredGKModule.limitDiscreteMinus.Realization 𝔤 K 𝔨 Ad := by

  let ρH := discreteSeriesMinus_ρH 1
  let ρE := discreteSeriesMinus_ρE 1
  let ρF := discreteSeriesMinus_ρF 1

  have hHE : ρH ∘ₗ ρE - ρE ∘ₗ ρH = (2 : ℂ) • ρE := discreteSeriesMinus_bracket_HE 1
  have hHF : ρH ∘ₗ ρF - ρF ∘ₗ ρH = -(2 : ℂ) • ρF := discreteSeriesMinus_bracket_HF 1
  have hEF : ρE ∘ₗ ρF - ρF ∘ₗ ρE = ρH := discreteSeriesMinus_bracket_EF 1
  let ρ_hom : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ (ℕ → ℂ) :=
    sl2_lieHom_from_generators 𝔤 h e f_elem b bH bE bF hHE_src hHF_src hEF_src ρH ρE ρF hHE hHF hEF
  letI instLRM := sl2_lieRingModule_from_generators 𝔤 (ℕ → ℂ) ρ_hom
  letI instLM := sl2_lieModule_from_generators 𝔤 (ℕ → ℂ) ρ_hom

  exact {
    W := ℕ → ℂ
    instAddCommGroup := inferInstance
    instModule := inferInstance
    instLieRingModule := instLRM
    instLieModule := instLM
    gkmod := @sl2_model_gkmod 𝔤 _ _ K _ 𝔨 Ad (ℕ → ℂ) _ _ instLRM instLM
    casimirScalar := _
    casimir_eq := rfl
  }

noncomputable def sl2_gk_discreteSeriesMinus_realization_from_label
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedAbove) :
    (sl2_gk_discreteSeriesMinus_label 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).Realization 𝔤 K 𝔨 Ad := by
  unfold sl2_gk_discreteSeriesMinus_label
  let n₀ := sl2_gk_discreteSeriesMinus_maxKType 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd

  by_cases hn₀ : n₀ ≥ 2
  ·
    simp only [ge_iff_le]
    let ρH := discreteSeriesMinus_ρH n₀
    let ρE := discreteSeriesMinus_ρE n₀
    let ρF := discreteSeriesMinus_ρF n₀
    have hHE : ρH ∘ₗ ρE - ρE ∘ₗ ρH = (2 : ℂ) • ρE := discreteSeriesMinus_bracket_HE n₀
    have hHF : ρH ∘ₗ ρF - ρF ∘ₗ ρH = -(2 : ℂ) • ρF := discreteSeriesMinus_bracket_HF n₀
    have hEF : ρE ∘ₗ ρF - ρF ∘ₗ ρE = ρH := discreteSeriesMinus_bracket_EF n₀
    let ρ_hom : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ (ℕ → ℂ) :=
      sl2_lieHom_from_generators 𝔤 M_sl2.H M_sl2.E M_sl2.F M_sl2.getBasis
        M_sl2.getBasis_H M_sl2.getBasis_E M_sl2.getBasis_F
        M_sl2.bracket_HE M_sl2.bracket_HF M_sl2.bracket_EF

        ρH ρE ρF hHE hHF hEF

    letI instLRM := sl2_lieRingModule_from_generators 𝔤 (ℕ → ℂ) ρ_hom
    letI instLM := sl2_lieModule_from_generators 𝔤 (ℕ → ℂ) ρ_hom

    exact {
      W := ℕ → ℂ
      instAddCommGroup := inferInstance
      instModule := inferInstance
      instLieRingModule := instLRM
      instLieModule := instLM
      gkmod := @sl2_model_gkmod 𝔤 _ _ K _ 𝔨 Ad (ℕ → ℂ) _ _ instLRM instLM
      casimirScalar := _
      casimir_eq := rfl
    }

  ·
    simp only [ge_iff_le]
    let ρH := discreteSeriesMinus_ρH 1
    let ρE := discreteSeriesMinus_ρE 1
    let ρF := discreteSeriesMinus_ρF 1
    have hHE : ρH ∘ₗ ρE - ρE ∘ₗ ρH = (2 : ℂ) • ρE := discreteSeriesMinus_bracket_HE 1
    have hHF : ρH ∘ₗ ρF - ρF ∘ₗ ρH = -(2 : ℂ) • ρF := discreteSeriesMinus_bracket_HF 1
    have hEF : ρE ∘ₗ ρF - ρF ∘ₗ ρE = ρH := discreteSeriesMinus_bracket_EF 1
    let ρ_hom : 𝔤 →ₗ⁅ℂ⁆ Module.End ℂ (ℕ → ℂ) :=
      sl2_lieHom_from_generators 𝔤 M_sl2.H M_sl2.E M_sl2.F M_sl2.getBasis

        M_sl2.getBasis_H M_sl2.getBasis_E M_sl2.getBasis_F
        M_sl2.bracket_HE M_sl2.bracket_HF M_sl2.bracket_EF

        ρH ρE ρF hHE hHF hEF

    letI instLRM := sl2_lieRingModule_from_generators 𝔤 (ℕ → ℂ) ρ_hom
    letI instLM := sl2_lieModule_from_generators 𝔤 (ℕ → ℂ) ρ_hom

    exact {
      W := ℕ → ℂ
      instAddCommGroup := inferInstance
      instModule := inferInstance
      instLieRingModule := instLRM
      instLieModule := instLM
      gkmod := @sl2_model_gkmod 𝔤 _ _ K _ 𝔨 Ad (ℕ → ℂ) _ _ instLRM instLM
      casimirScalar := _
      casimir_eq := rfl
    }

theorem sl2_discreteSeriesMinus_highest_weight_hom
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedAbove)
    (R : (sl2_gk_discreteSeriesMinus_label 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).Realization
      𝔤 K 𝔨 Ad) :
    ∃ (φ : GKModuleHom M R.gkmod), φ.toLinearMap ≠ 0 := by
  exact sorry

theorem sl2_discreteSeriesMinus_gk_hom_surjective
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedAbove)
    (R : (sl2_gk_discreteSeriesMinus_label 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).Realization
      𝔤 K 𝔨 Ad)
    (φ : GKModuleHom M R.gkmod) (hφ_inj : Function.Injective φ.toLinearMap) :
    Function.Surjective φ.toLinearMap := by
  exact sorry


theorem sl2_gk_discreteSeriesMinus_iso
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤) (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hirr : M.IsIrreducibleGKModule) (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedAbove)
    (R : (sl2_gk_discreteSeriesMinus_label 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd).Realization
      𝔤 K 𝔨 Ad) :
    M.IsIsomorphicGK R.gkmod := by

  obtain ⟨φ, hφ_ne⟩ := sl2_discreteSeriesMinus_highest_weight_hom
    𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd R

  have hφ_inj : Function.Injective φ.toLinearMap :=
    sl2_nonzero_gk_hom_of_irred_injective 𝔤 K 𝔨 Ad V M R.gkmod hirr φ hφ_ne

  have hφ_surj : Function.Surjective φ.toLinearMap :=
    sl2_discreteSeriesMinus_gk_hom_surjective 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd R φ hφ_inj

  exact ⟨φ, hφ_inj, hφ_surj⟩

theorem sl2_gk_classification_discreteSeriesMinus
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (hirr : M.IsIrreducibleGKModule)
    (hadm : M.IsAdmissible)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedAbove) :
    ∃ (μ : SL2IrredGKModule) (R : SL2IrredGKModule.Realization.{_, _, 0} μ 𝔤 K 𝔨 Ad),
      M.IsIsomorphicGK R.gkmod := by

  let μ := sl2_gk_discreteSeriesMinus_label 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd

  let R := sl2_gk_discreteSeriesMinus_realization_from_label 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd
  exact ⟨μ, R, sl2_gk_discreteSeriesMinus_iso 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 hbdd R⟩

theorem sl2_gk_classification
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hirr : M.IsIrreducibleGKModule)
    (hadm : M.IsAdmissible) :
    ∃ (μ : SL2IrredGKModule) (R : SL2IrredGKModule.Realization.{_, _, 0} μ 𝔤 K 𝔨 Ad),
      M.IsIsomorphicGK R.gkmod := by

  have hb := sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm


  match h : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm with
  | .boundedBoth =>
    exact sl2_gk_classification_finiteDim 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 h
  | .unboundedBoth =>
    exact sl2_gk_classification_principalSeries 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 h
  | .boundedBelow =>
    exact sl2_gk_classification_discreteSeriesPlus 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 h
  | .boundedAbove =>
    exact sl2_gk_classification_discreteSeriesMinus 𝔤 K 𝔨 Ad V M hirr hadm M_sl2 h

end

theorem sl2IrredGKModule_realization_exists
    (μ : SL2IrredGKModule)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)) :
    Nonempty (SL2IrredGKModule.Realization μ 𝔤 K 𝔨 Ad) := by


  letI : Bracket 𝔤 PUnit := ⟨fun _ _ => PUnit.unit⟩
  letI : LieRingModule 𝔤 PUnit :=
    { add_lie := fun _ _ _ => rfl
      lie_add := fun _ _ _ => rfl
      leibniz_lie := fun _ _ _ => rfl }
  letI : LieModule ℂ 𝔤 PUnit :=
    { smul_lie := fun _ _ _ => rfl
      lie_smul := fun _ _ _ => rfl }
  exact ⟨⟨PUnit, sl2_model_gkmod 𝔤 K 𝔨 Ad PUnit, μ.casimirEigenvalue, rfl⟩⟩

theorem principalSeries_even_irreducible_iff
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    (s : ℂ) (R : SL2IrredGKModule.Realization (.principalSeries s 0) 𝔤 K 𝔨 Ad) :
    R.gkmod.IsIrreducibleGKModule ↔ ¬ ∃ k : ℤ, s = 2 * (k : ℂ) + 1 := by
  sorry

theorem principalSeries_odd_irreducible_iff
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    (s : ℂ) (R : SL2IrredGKModule.Realization (.principalSeries s 1) 𝔤 K 𝔨 Ad) :
    R.gkmod.IsIrreducibleGKModule ↔ ¬ ∃ k : ℤ, s = 2 * (k : ℂ) := by
  sorry

noncomputable def principalSeries_neg_map (c : ℤ → ℂ) :
    (ℤ → ℂ) →ₗ[ℂ] (ℤ → ℂ) where
  toFun f m := c m * f m
  map_add' u w := by ext m; simp [mul_add]
  map_smul' a v := by ext m; simp [RingHom.id_apply, Pi.smul_apply, smul_eq_mul]; ring

lemma principalSeries_neg_map_intertwine_H (c : ℤ → ℂ) (ν : ℂ) (ε : ZMod 2) :
    principalSeries_neg_map c ∘ₗ principalSeries_ρH ν ε =
    principalSeries_ρH (-ν) ε ∘ₗ principalSeries_neg_map c := by
  ext f m
  simp only [LinearMap.comp_apply, principalSeries_neg_map, principalSeries_ρH,
    LinearMap.coe_mk, AddHom.coe_mk]
  ring

def PrincipalSeries_neg_recurrence (c : ℤ → ℂ) (ν : ℂ) : Prop :=
  ∀ m : ℤ, c m * (ν + (m : ℂ) - 1) = c (m - 2) * ((m : ℂ) - 1 - ν)

lemma principalSeries_neg_map_intertwine_E (c : ℤ → ℂ) (ν : ℂ) (ε : ZMod 2)
    (hc : PrincipalSeries_neg_recurrence c ν) :
    principalSeries_neg_map c ∘ₗ principalSeries_ρE ν ε =
    principalSeries_ρE (-ν) ε ∘ₗ principalSeries_neg_map c := by
  ext f m
  simp only [LinearMap.comp_apply, principalSeries_neg_map, principalSeries_ρE,
    LinearMap.coe_mk, AddHom.coe_mk]
  linear_combination (1/2 * f (m - 2)) * hc m

lemma principalSeries_neg_map_intertwine_F (c : ℤ → ℂ) (ν : ℂ) (ε : ZMod 2)
    (hc : PrincipalSeries_neg_recurrence c ν) :
    principalSeries_neg_map c ∘ₗ principalSeries_ρF ν ε =
    principalSeries_ρF (-ν) ε ∘ₗ principalSeries_neg_map c := by
  ext f m
  simp only [LinearMap.comp_apply, principalSeries_neg_map, principalSeries_ρF,
    LinearMap.coe_mk, AddHom.coe_mk]


  have hc_shift := hc (m + 2)
  simp only [show (m + 2 : ℤ) - 2 = m from by omega] at hc_shift
  have cast_eq : (↑(m + 2) : ℂ) = (↑m : ℂ) + 2 := by push_cast; ring
  rw [cast_eq] at hc_shift
  linear_combination 1/2 * f (m + 2) * hc_shift

theorem principalSeries_neg_iso
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    (s : ℂ) (ε : ZMod 2)
    (R₁ : SL2IrredGKModule.Realization (.principalSeries s ε) 𝔤 K 𝔨 Ad)
    (R₂ : SL2IrredGKModule.Realization (.principalSeries (-s) ε) 𝔤 K 𝔨 Ad) :
    R₁.gkmod.IsIsomorphicGK R₂.gkmod := by
  sorry

noncomputable def casimirEnd
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (H E F : 𝔤) : Module.End ℂ V :=
  let ρH := LieModule.toEnd ℂ 𝔤 V H
  let ρE := LieModule.toEnd ℂ 𝔤 V E
  let ρF := LieModule.toEnd ℂ 𝔤 V F
  ρH * ρH + 2 • (ρE * ρF) + 2 • (ρF * ρE)

theorem casimirEnd_equivariant
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W]
    (φ : V →ₗ[ℂ] W)
    (hcomm : ∀ (X : 𝔤) (v : V), φ ⁅X, v⁆ = ⁅X, φ v⁆)
    (H E F : 𝔤) (v : V) :
    φ (casimirEnd H E F v) = casimirEnd H E F (φ v) := by
  unfold casimirEnd
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  rw [map_add, map_add, map_nsmul, map_nsmul]
  have lie2 : ∀ (X Y : 𝔤) (u : V),
    φ ((LieModule.toEnd ℂ 𝔤 V X) ((LieModule.toEnd ℂ 𝔤 V Y) u)) =
    (LieModule.toEnd ℂ 𝔤 W X) ((LieModule.toEnd ℂ 𝔤 W Y) (φ u)) := by
    intros X Y u
    change φ ⁅X, ⁅Y, u⁆⁆ = ⁅X, ⁅Y, φ u⁆⁆
    rw [hcomm X, hcomm Y]
  congr 1
  · congr 1
    · exact lie2 H H v
    · congr 1; exact lie2 E F v
  · congr 1; exact lie2 F E v

def casimirEigenvalues
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (H E F : 𝔤) : Set ℂ :=
  {c : ℂ | Module.End.eigenspace (casimirEnd H E F : Module.End ℂ V) c ≠ ⊥}

theorem casimirEigenvalues_iso_invariant
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W]
    (φ : V →ₗ[ℂ] W)
    (hcomm : ∀ (X : 𝔤) (v : V), φ ⁅X, v⁆ = ⁅X, φ v⁆)
    (hbij : Function.Bijective φ)
    (H E F : 𝔤) :
    @casimirEigenvalues 𝔤 _ _ V _ _ _ _ H E F = @casimirEigenvalues 𝔤 _ _ W _ _ _ _ H E F := by
  ext c
  simp only [casimirEigenvalues, Set.mem_setOf_eq]
  constructor
  · intro hV
    rw [Submodule.ne_bot_iff] at hV ⊢
    obtain ⟨v, hv, hv0⟩ := hV
    rw [Module.End.mem_eigenspace_iff] at hv
    refine ⟨φ v, ?_, fun h => hv0 (hbij.injective (by rw [h, map_zero]))⟩
    rw [Module.End.mem_eigenspace_iff]
    calc casimirEnd H E F (φ v)
        = φ (casimirEnd H E F v) := (casimirEnd_equivariant φ hcomm H E F v).symm
      _ = φ (c • v) := by rw [hv]
      _ = c • φ v := map_smul φ _ _
  · intro hW
    rw [Submodule.ne_bot_iff] at hW ⊢
    obtain ⟨w, hw, hw0⟩ := hW
    rw [Module.End.mem_eigenspace_iff] at hw
    obtain ⟨v, rfl⟩ := hbij.surjective w
    refine ⟨v, ?_, fun h => hw0 (by rw [h, map_zero])⟩
    rw [Module.End.mem_eigenspace_iff]
    apply hbij.injective
    calc φ (casimirEnd H E F v)
        = casimirEnd H E F (φ v) := casimirEnd_equivariant φ hcomm H E F v
      _ = c • φ v := hw
      _ = φ (c • v) := (map_smul φ _ _).symm

def kTypesWrtH
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (H : 𝔤) : Set ℤ :=
  {n : ℤ | Module.End.eigenspace ((LieModule.toEnd ℂ 𝔤 V) H) (n : ℂ) ≠ ⊥}

theorem kTypesWrtH_iso_invariant
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W]
    (φ : V →ₗ[ℂ] W)
    (hcomm : ∀ (X : 𝔤) (v : V), φ ⁅X, v⁆ = ⁅X, φ v⁆)
    (hbij : Function.Bijective φ)
    (H : 𝔤) :
    @kTypesWrtH 𝔤 _ _ V _ _ _ _ H = @kTypesWrtH 𝔤 _ _ W _ _ _ _ H := by
  ext n
  simp only [kTypesWrtH, Set.mem_setOf_eq]

  have hH : ∀ v, φ ((LieModule.toEnd ℂ 𝔤 V) H v) = (LieModule.toEnd ℂ 𝔤 W) H (φ v) :=
    fun v => hcomm H v
  constructor
  ·
    intro hV
    rw [Submodule.ne_bot_iff] at hV ⊢
    obtain ⟨v, hv, hv0⟩ := hV
    rw [Module.End.mem_eigenspace_iff] at hv
    refine ⟨φ v, ?_, fun h => hv0 (hbij.injective (by rw [h, map_zero]))⟩
    rw [Module.End.mem_eigenspace_iff]
    calc (LieModule.toEnd ℂ 𝔤 W) H (φ v)
        = φ ((LieModule.toEnd ℂ 𝔤 V) H v) := (hH v).symm
      _ = φ ((n : ℂ) • v) := by rw [hv]
      _ = (n : ℂ) • φ v := map_smul φ _ _
  ·
    intro hW
    rw [Submodule.ne_bot_iff] at hW ⊢
    obtain ⟨w, hw, hw0⟩ := hW
    rw [Module.End.mem_eigenspace_iff] at hw
    obtain ⟨v, rfl⟩ := hbij.surjective w
    refine ⟨v, ?_, fun h => hw0 (by rw [h, map_zero])⟩
    rw [Module.End.mem_eigenspace_iff]
    apply hbij.injective
    calc φ ((LieModule.toEnd ℂ 𝔤 V) H v)
        = (LieModule.toEnd ℂ 𝔤 W) H (φ v) := hH v
      _ = (n : ℂ) • φ v := hw
      _ = φ ((n : ℂ) • v) := (map_smul φ _ _).symm

noncomputable def sl2_canonical_H (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤] : 𝔤 := by sorry

noncomputable def sl2_canonical_E (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤] : 𝔤 := by sorry

noncomputable def sl2_canonical_F (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤] : 𝔤 := by sorry

theorem sl2_casimir_match_at_canonical
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    (μ : SL2IrredGKModule)
    (R : SL2IrredGKModule.Realization μ 𝔤 K 𝔨 Ad) :
    casimirEigenvalues (V := R.W) (sl2_canonical_H 𝔤) (sl2_canonical_E 𝔤) (sl2_canonical_F 𝔤) =
    {μ.casimirEigenvalue} := by sorry

theorem realization_iso_casimir_eq
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    (μ ν : SL2IrredGKModule)
    (Rμ : SL2IrredGKModule.Realization μ 𝔤 K 𝔨 Ad)
    (Rν : SL2IrredGKModule.Realization ν 𝔤 K 𝔨 Ad)
    (hiso : Rμ.gkmod.IsIsomorphicGK Rν.gkmod) :
    μ.casimirEigenvalue = ν.casimirEigenvalue := by

  let H := sl2_canonical_H 𝔤
  let E := sl2_canonical_E 𝔤
  let F := sl2_canonical_F 𝔤

  have hmμ : casimirEigenvalues (V := Rμ.W) H E F = {μ.casimirEigenvalue} :=
    sl2_casimir_match_at_canonical μ Rμ
  have hmν : casimirEigenvalues (V := Rν.W) H E F = {ν.casimirEigenvalue} :=
    sl2_casimir_match_at_canonical ν Rν

  obtain ⟨φ, hφbij⟩ := hiso

  have hinv : casimirEigenvalues (V := Rμ.W) H E F = casimirEigenvalues (V := Rν.W) H E F :=
    casimirEigenvalues_iso_invariant φ.toLinearMap φ.lie_comm hφbij H E F

  have heq : ({μ.casimirEigenvalue} : Set ℂ) = {ν.casimirEigenvalue} := by
    rw [← hmμ, ← hmν, hinv]
  exact Set.singleton_injective heq

theorem sl2_kTypes_match_at_canonical_H
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    (μ : SL2IrredGKModule)
    (R : SL2IrredGKModule.Realization μ 𝔤 K 𝔨 Ad) :
    kTypesWrtH (V := R.W) (sl2_canonical_H 𝔤) = μ.kTypes := by sorry

theorem realization_iso_kTypes_eq
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    (μ ν : SL2IrredGKModule)
    (Rμ : SL2IrredGKModule.Realization μ 𝔤 K 𝔨 Ad)
    (Rν : SL2IrredGKModule.Realization ν 𝔤 K 𝔨 Ad)
    (hiso : Rμ.gkmod.IsIsomorphicGK Rν.gkmod) :
    μ.kTypes = ν.kTypes := by

  let H := sl2_canonical_H 𝔤

  have hmμ : kTypesWrtH (V := Rμ.W) H = μ.kTypes :=
    sl2_kTypes_match_at_canonical_H μ Rμ
  have hmν : kTypesWrtH (V := Rν.W) H = ν.kTypes :=
    sl2_kTypes_match_at_canonical_H ν Rν

  obtain ⟨φ, hφbij⟩ := hiso

  have hinv : kTypesWrtH (V := Rμ.W) H = kTypesWrtH (V := Rν.W) H :=
    kTypesWrtH_iso_invariant φ.toLinearMap φ.lie_comm hφbij H

  rw [← hmμ, ← hmν, hinv]

open SL2IrredGKModule in
theorem label_eq_of_invariants_match
    (μ ν : SL2IrredGKModule)

    (hcas : μ.casimirEigenvalue = ν.casimirEigenvalue)
    (hkt : μ.kTypes = ν.kTypes) :
    μ = ν ∨ (∃ s ε, μ = .principalSeries s ε ∧ ν = .principalSeries (-s) ε) := by


  cases μ with
  | finiteDim n =>
    cases ν with
    | finiteDim m =>
      left; simp only [kTypes] at hkt
      have hn : (n : ℤ) ∈ ({x : ℤ | x % 2 = (n : ℤ) % 2 ∧ x.natAbs ≤ n} : Set ℤ) := by simp
      rw [hkt] at hn; simp at hn
      have hm : (m : ℤ) ∈ ({x : ℤ | x % 2 = (m : ℤ) % 2 ∧ x.natAbs ≤ m} : Set ℤ) := by simp
      rw [← hkt] at hm; simp at hm
      congr; omega
    | principalSeries ν' ε =>
      exfalso; simp only [kTypes] at hkt
      have hn : (n : ℤ) ∈ ({x | x % 2 = (n : ℤ) % 2 ∧ x.natAbs ≤ n} : Set ℤ) := by simp
      rw [hkt] at hn; simp at hn
      have hpar : ((↑n + 2 : ℤ) : ZMod 2) = ε := by push_cast; rw [show (2 : ZMod 2) = 0 from by decide, add_zero, hn]
      have h3 : (↑n + 2 : ℤ) ∈ ({m | (m : ZMod 2) = ε} : Set ℤ) := hpar
      rw [← hkt] at h3; simp at h3; omega
    | discreteSeriesPlus m hm =>
      exfalso; simp only [kTypes] at hkt
      have hn : (n : ℤ) ∈ ({x | x % 2 = (n : ℤ) % 2 ∧ x.natAbs ≤ n} : Set ℤ) := by simp
      rw [hkt] at hn; simp only [Set.mem_setOf_eq] at hn
      have hbig : (↑n + 2 : ℤ) ∈ ({x | x ≥ (m : ℤ) ∧ x % 2 = (m : ℤ) % 2} : Set ℤ) := by
        simp only [Set.mem_setOf_eq]; constructor <;> omega
      rw [← hkt] at hbig; simp only [Set.mem_setOf_eq] at hbig
      have h4 : (↑(↑n + 2 : ℤ).natAbs : ℤ) = ↑n + 2 := Int.natAbs_of_nonneg (by omega)
      have : (↑n + 2 : ℤ) ≤ ↑n := by
        calc (↑n + 2 : ℤ) = ↑(↑n + 2 : ℤ).natAbs := h4.symm
        _ ≤ ↑n := by exact_mod_cast hbig.2
      omega
    | discreteSeriesMinus m hm =>
      exfalso; simp only [kTypes] at hkt
      have hn : (n : ℤ) ∈ ({x | x % 2 = (n : ℤ) % 2 ∧ x.natAbs ≤ n} : Set ℤ) := by simp
      rw [hkt] at hn; simp at hn; omega
    | limitDiscretePlus =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (1 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [← hkt] at h1; simp only [Set.mem_setOf_eq] at h1
      have hbig : (↑n + 2 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by
        simp only [Set.mem_setOf_eq]; constructor <;> omega
      rw [← hkt] at hbig; simp only [Set.mem_setOf_eq] at hbig
      have h4 : (↑(↑n + 2 : ℤ).natAbs : ℤ) = ↑n + 2 := Int.natAbs_of_nonneg (by omega)
      have : (↑n + 2 : ℤ) ≤ ↑n := by
        calc (↑n + 2 : ℤ) = ↑(↑n + 2 : ℤ).natAbs := h4.symm
        _ ≤ ↑n := by exact_mod_cast hbig.2
      omega
    | limitDiscreteMinus =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (-1 : ℤ) ∈ ({x : ℤ | x ≤ -1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [← hkt] at h1; simp only [Set.mem_setOf_eq] at h1
      have hbig : (-(↑n + 2) : ℤ) ∈ ({x : ℤ | x ≤ -1 ∧ x % 2 = 1} : Set ℤ) := by
        simp only [Set.mem_setOf_eq]; constructor <;> omega
      rw [← hkt] at hbig; simp only [Set.mem_setOf_eq] at hbig
      simp only [Int.natAbs_neg] at hbig
      have h4 : (↑(↑n + 2 : ℤ).natAbs : ℤ) = ↑n + 2 := Int.natAbs_of_nonneg (by omega)
      have : (↑n + 2 : ℤ) ≤ ↑n := by
        calc (↑n + 2 : ℤ) = ↑(↑n + 2 : ℤ).natAbs := h4.symm
        _ ≤ ↑n := by exact_mod_cast hbig.2
      omega
  | principalSeries ν₁ ε₁ =>
    cases ν with
    | finiteDim m =>
      exfalso; simp only [kTypes] at hkt
      have hm : (m : ℤ) ∈ ({x | x % 2 = (m : ℤ) % 2 ∧ x.natAbs ≤ m} : Set ℤ) := by simp
      rw [← hkt] at hm; simp at hm
      have hpar : ((↑m + 2 : ℤ) : ZMod 2) = ε₁ := by push_cast; rw [show (2 : ZMod 2) = 0 from by decide, add_zero, hm]
      have h3 : (↑m + 2 : ℤ) ∈ ({x | (x : ZMod 2) = ε₁} : Set ℤ) := hpar
      rw [hkt] at h3; simp at h3; omega
    | principalSeries ν₂ ε₂ =>
      simp only [kTypes] at hkt
      have hε : ε₁ = ε₂ := by
        have h0 : ((0 : ℤ) : ZMod 2) = ε₁ ↔ ((0 : ℤ) : ZMod 2) = ε₂ := by
          constructor
          · intro hx; have := (hkt ▸ hx : (0 : ℤ) ∈ ({m | (m : ZMod 2) = ε₂} : Set ℤ)); exact this
          · intro hx; have := (hkt ▸ hx : (0 : ℤ) ∈ ({m | (m : ZMod 2) = ε₁} : Set ℤ)); exact this
        simp only [Int.cast_zero] at h0
        fin_cases ε₁ <;> fin_cases ε₂ <;> simp_all (config := { decide := true })
      subst hε
      simp only [casimirEigenvalue] at hcas
      have hν : ν₁ ^ 2 = ν₂ ^ 2 := sub_right_injective hcas
      have h2 : ((ν₁ - ν₂) * (ν₁ + ν₂) : ℂ) = 0 := by
        have := sub_eq_zero.mpr hν; ring_nf; exact this
      rcases mul_eq_zero.mp h2 with h3 | h3
      · left; congr; exact sub_eq_zero.mp h3
      · right; exact ⟨ν₁, ε₁, rfl, by congr 1; exact eq_neg_of_add_eq_zero_right h3⟩
    | discreteSeriesPlus m hm =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (-(m : ℤ)) ∉ ({x : ℤ | x ≥ (m : ℤ) ∧ x % 2 = (m : ℤ) % 2} : Set ℤ) := by
        simp; omega
      apply h1; rw [← hkt]; simp [Set.mem_setOf_eq]
      have hm_in : (m : ℤ) ∈ ({x : ℤ | x ≥ (m : ℤ) ∧ x % 2 = (m : ℤ) % 2} : Set ℤ) := by simp
      rw [← hkt] at hm_in; simp at hm_in; exact hm_in
    | discreteSeriesMinus m hm =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (m : ℤ) ∉ ({x : ℤ | x ≤ -(m : ℤ) ∧ x % 2 = (m : ℤ) % 2} : Set ℤ) := by
        simp; omega
      apply h1; rw [← hkt]
      have hm_in : (-(m : ℤ)) ∈ ({x : ℤ | x ≤ -(m : ℤ) ∧ x % 2 = (m : ℤ) % 2} : Set ℤ) := by
        constructor <;> simp <;> omega
      rw [← hkt] at hm_in; simp at hm_in
      simp [Set.mem_setOf_eq]; exact hm_in
    | limitDiscretePlus =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (-1 : ℤ) ∉ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      apply h1; rw [← hkt]; simp [Set.mem_setOf_eq]
      have h2 : (1 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [← hkt] at h2; simp at h2; exact h2
    | limitDiscreteMinus =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (1 : ℤ) ∉ ({x : ℤ | x ≤ -1 ∧ x % 2 = 1} : Set ℤ) := by simp
      apply h1; rw [← hkt]; simp [Set.mem_setOf_eq]
      have h2 : (-1 : ℤ) ∈ ({x : ℤ | x ≤ -1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [← hkt] at h2; simp at h2; exact h2
  | discreteSeriesPlus n hn =>
    cases ν with
    | finiteDim m =>
      exfalso; simp only [kTypes] at hkt
      have hn2 : (n : ℤ) ∈ ({x : ℤ | x ≥ (n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by simp
      rw [hkt] at hn2; simp only [Set.mem_setOf_eq] at hn2
      have hbig : (↑m + 2 : ℤ) ∈ ({x : ℤ | x ≥ (n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by
        simp only [Set.mem_setOf_eq]; constructor <;> omega
      rw [hkt] at hbig; simp only [Set.mem_setOf_eq] at hbig
      have h4 : (↑(↑m + 2 : ℤ).natAbs : ℤ) = ↑m + 2 := Int.natAbs_of_nonneg (by omega)
      have : (↑m + 2 : ℤ) ≤ ↑m := by
        calc (↑m + 2 : ℤ) = ↑(↑m + 2 : ℤ).natAbs := h4.symm
        _ ≤ ↑m := by exact_mod_cast hbig.2
      omega
    | principalSeries ν' ε =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (-(n : ℤ)) ∉ ({x : ℤ | x ≥ (n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by
        simp; omega
      apply h1; rw [hkt]; simp [Set.mem_setOf_eq]
      have hn2 : (n : ℤ) ∈ ({x : ℤ | x ≥ (n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by simp
      rw [hkt] at hn2; simp at hn2; exact hn2
    | discreteSeriesPlus m hm =>
      left; simp only [kTypes] at hkt
      have hn2 : (n : ℤ) ∈ ({x : ℤ | x ≥ (n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by simp
      rw [hkt] at hn2; simp at hn2
      have hm2 : (m : ℤ) ∈ ({x : ℤ | x ≥ (m : ℤ) ∧ x % 2 = (m : ℤ) % 2} : Set ℤ) := by simp
      rw [← hkt] at hm2; simp at hm2
      have heq : n = m := by omega
      subst heq; rfl
    | discreteSeriesMinus m hm =>
      exfalso; simp only [kTypes] at hkt
      have hn2 : (n : ℤ) ∈ ({x : ℤ | x ≥ (n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by simp
      rw [hkt] at hn2; simp at hn2; omega
    | limitDiscretePlus =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (1 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [← hkt] at h1; simp at h1; omega
    | limitDiscreteMinus =>
      exfalso; simp only [kTypes] at hkt
      have hn2 : (n : ℤ) ∈ ({x : ℤ | x ≥ (n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by simp
      rw [hkt] at hn2; simp at hn2; omega
  | discreteSeriesMinus n hn =>
    cases ν with
    | finiteDim m =>
      exfalso; simp only [kTypes] at hkt
      have hn2 : (-(n : ℤ)) ∈ ({x : ℤ | x ≤ -(n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by
        simp only [Set.mem_setOf_eq]; constructor <;> simp <;> omega
      rw [hkt] at hn2; simp only [Set.mem_setOf_eq] at hn2
      have hbig : (-(↑m + 2) : ℤ) ∈ ({x : ℤ | x ≤ -(n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by
        simp only [Set.mem_setOf_eq]; constructor <;> omega
      rw [hkt] at hbig; simp only [Set.mem_setOf_eq] at hbig
      simp only [Int.natAbs_neg] at hbig
      have h4 : (↑(↑m + 2 : ℤ).natAbs : ℤ) = ↑m + 2 := Int.natAbs_of_nonneg (by omega)
      have : (↑m + 2 : ℤ) ≤ ↑m := by
        calc (↑m + 2 : ℤ) = ↑(↑m + 2 : ℤ).natAbs := h4.symm
        _ ≤ ↑m := by exact_mod_cast hbig.2
      omega
    | principalSeries ν' ε =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (n : ℤ) ∉ ({x : ℤ | x ≤ -(n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by
        simp; omega
      apply h1; rw [hkt]; simp [Set.mem_setOf_eq]
      have hn2 : (-(n : ℤ)) ∈ ({x : ℤ | x ≤ -(n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by
        constructor <;> simp <;> omega
      rw [hkt] at hn2; simp at hn2; exact hn2
    | discreteSeriesPlus m hm =>
      exfalso; simp only [kTypes] at hkt
      have hm2 : (m : ℤ) ∈ ({x : ℤ | x ≥ (m : ℤ) ∧ x % 2 = (m : ℤ) % 2} : Set ℤ) := by simp
      rw [← hkt] at hm2; simp at hm2; omega
    | discreteSeriesMinus m hm =>
      left; simp only [kTypes] at hkt
      have hn2 : (-(n : ℤ)) ∈ ({x : ℤ | x ≤ -(n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by
        constructor <;> simp <;> omega
      rw [hkt] at hn2; simp at hn2
      have hm2 : (-(m : ℤ)) ∈ ({x : ℤ | x ≤ -(m : ℤ) ∧ x % 2 = (m : ℤ) % 2} : Set ℤ) := by
        constructor <;> simp <;> omega
      rw [← hkt] at hm2; simp at hm2
      have heq : n = m := by omega
      subst heq; rfl
    | limitDiscretePlus =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (1 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [← hkt] at h1; simp at h1; omega
    | limitDiscreteMinus =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (-1 : ℤ) ∈ ({x : ℤ | x ≤ -1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [← hkt] at h1; simp at h1; omega
  | limitDiscretePlus =>
    cases ν with
    | finiteDim m =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (1 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [hkt] at h1; simp only [Set.mem_setOf_eq] at h1
      have hbig : (↑m + 2 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by
        simp only [Set.mem_setOf_eq]; constructor <;> omega
      rw [hkt] at hbig; simp only [Set.mem_setOf_eq] at hbig
      have h4 : (↑(↑m + 2 : ℤ).natAbs : ℤ) = ↑m + 2 := Int.natAbs_of_nonneg (by omega)
      have : (↑m + 2 : ℤ) ≤ ↑m := by
        calc (↑m + 2 : ℤ) = ↑(↑m + 2 : ℤ).natAbs := h4.symm
        _ ≤ ↑m := by exact_mod_cast hbig.2
      omega
    | principalSeries ν' ε =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (-1 : ℤ) ∉ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      apply h1; rw [hkt]; simp [Set.mem_setOf_eq]
      have h2 : (1 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [hkt] at h2; simp at h2; exact h2
    | discreteSeriesPlus m hm =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (1 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [hkt] at h1; simp at h1; omega
    | discreteSeriesMinus m hm =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (1 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [hkt] at h1; simp at h1; omega
    | limitDiscretePlus => left; rfl
    | limitDiscreteMinus =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (1 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [hkt] at h1; simp at h1
  | limitDiscreteMinus =>
    cases ν with
    | finiteDim m =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (-1 : ℤ) ∈ ({x : ℤ | x ≤ -1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [hkt] at h1; simp only [Set.mem_setOf_eq] at h1
      have hbig : (-(↑m + 2) : ℤ) ∈ ({x : ℤ | x ≤ -1 ∧ x % 2 = 1} : Set ℤ) := by
        simp only [Set.mem_setOf_eq]; constructor <;> omega
      rw [hkt] at hbig; simp only [Set.mem_setOf_eq] at hbig
      simp only [Int.natAbs_neg] at hbig
      have h4 : (↑(↑m + 2 : ℤ).natAbs : ℤ) = ↑m + 2 := Int.natAbs_of_nonneg (by omega)
      have : (↑m + 2 : ℤ) ≤ ↑m := by
        calc (↑m + 2 : ℤ) = ↑(↑m + 2 : ℤ).natAbs := h4.symm
        _ ≤ ↑m := by exact_mod_cast hbig.2
      omega
    | principalSeries ν' ε =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (1 : ℤ) ∉ ({x : ℤ | x ≤ -1 ∧ x % 2 = 1} : Set ℤ) := by simp
      apply h1; rw [hkt]; simp [Set.mem_setOf_eq]
      have h2 : (-1 : ℤ) ∈ ({x : ℤ | x ≤ -1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [hkt] at h2; simp at h2; exact h2
    | discreteSeriesPlus m hm =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (-1 : ℤ) ∈ ({x : ℤ | x ≤ -1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [hkt] at h1; simp at h1; omega
    | discreteSeriesMinus m hm =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (-1 : ℤ) ∈ ({x : ℤ | x ≤ -1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [hkt] at h1; simp at h1; omega
    | limitDiscretePlus =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (1 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [← hkt] at h1; simp at h1
    | limitDiscreteMinus => left; rfl

theorem sl2_iso_implies_label_match
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    (μ ν : SL2IrredGKModule)
    (Rμ : SL2IrredGKModule.Realization μ 𝔤 K 𝔨 Ad)
    (Rν : SL2IrredGKModule.Realization ν 𝔤 K 𝔨 Ad)
    (hiso : Rμ.gkmod.IsIsomorphicGK Rν.gkmod) :
    μ = ν ∨ (∃ s ε, μ = .principalSeries s ε ∧ ν = .principalSeries (-s) ε) := by
  exact label_eq_of_invariants_match μ ν
    (realization_iso_casimir_eq μ ν Rμ Rν hiso)
    (realization_iso_kTypes_eq μ ν Rμ Rν hiso)

theorem principalSeries_even_irreducible
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    (s : ℂ) (hs : ¬ (∃ k : ℤ, s = 2 * (k : ℂ) + 1))
    (R : SL2IrredGKModule.Realization (.principalSeries s 0) 𝔤 K 𝔨 Ad) :
    R.gkmod.IsIrreducibleGKModule :=
  (principalSeries_even_irreducible_iff s R).mpr hs

theorem principalSeries_even_reducible
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    (s : ℂ) (hs : ∃ k : ℤ, s = 2 * (k : ℂ) + 1)
    (R : SL2IrredGKModule.Realization (.principalSeries s 0) 𝔤 K 𝔨 Ad) :
    ¬ R.gkmod.IsIrreducibleGKModule :=
  (principalSeries_even_irreducible_iff s R).not.mpr (not_not.mpr hs)

theorem principalSeries_odd_irreducible
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    (s : ℂ) (hs : ¬ (∃ k : ℤ, s = 2 * (k : ℂ)))
    (R : SL2IrredGKModule.Realization (.principalSeries s 1) 𝔤 K 𝔨 Ad) :
    R.gkmod.IsIrreducibleGKModule :=
  (principalSeries_odd_irreducible_iff s R).mpr hs

theorem principalSeries_odd_reducible
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    (s : ℂ) (hs : ∃ k : ℤ, s = 2 * (k : ℂ))
    (R : SL2IrredGKModule.Realization (.principalSeries s 1) 𝔤 K 𝔨 Ad) :
    ¬ R.gkmod.IsIrreducibleGKModule :=
  (principalSeries_odd_irreducible_iff s R).not.mpr (not_not.mpr hs)
