/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.DualityFunctorDefs
import Atlas.LieGroups.code.BGGReciprocity

noncomputable section

universe uCatO

def IsInjectiveInO
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (I : Type uCatO) [AddCommGroup I] [Module R I]
    [LieRingModule 𝔤 I] [LieModule R 𝔤 I]
    (_hI : IsCategoryO Δ rd I) : Prop :=
  ∀ (X : Type uCatO) [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (_ : IsCategoryO Δ rd X),
  ∀ (Y : Type uCatO) [AddCommGroup Y] [Module R Y]
    [LieRingModule 𝔤 Y] [LieModule R 𝔤 Y]
    (_ : IsCategoryO Δ rd Y),
  ∀ (i : X →ₗ⁅R, 𝔤⁆ Y) (_ : Function.Injective i)
    (f : X →ₗ⁅R, 𝔤⁆ I),
    ∃ (g : Y →ₗ⁅R, 𝔤⁆ I), ∀ x, g (i x) = f x

theorem duality_projective_to_injective
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (cτ : CartanInvolution rd)
    {P : Type uCatO} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (hPO : IsCategoryO Δ rd P)
    (hPproj : IsProjectiveInO rd P hPO)
    (dP : DualInO cτ P hPO) :
    IsInjectiveInO rd dP.Xdual dP.isCategoryO := by
  sorry

theorem injective_hull_simple_is_dual_projective
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {_wg : WeylGroupData Δ}
    (cτ : CartanInvolution rd)
    (lam : Δ.𝔥 →ₗ[R] R)
    {Llam : Type uCatO} [AddCommGroup Llam] [Module R Llam]
    [LieRingModule 𝔤 Llam] [LieModule R 𝔤 Llam]
    (hLO : IsCategoryO Δ rd Llam)
    (hLirr : LieModule.IsIrreducible R 𝔤 Llam)
    (hLhw : IsHighestWeightModule Δ Llam lam)
    {Plam : Type uCatO} [AddCommGroup Plam] [Module R Plam]
    [LieRingModule 𝔤 Plam] [LieModule R 𝔤 Plam]
    (hPO : IsCategoryO Δ rd Plam)
    (hPproj : IsProjectiveInO rd Plam hPO)
    (hPsurj : ∃ (π : Plam →ₗ⁅R, 𝔤⁆ Llam), Function.Surjective π)
    (dP : DualInO cτ Plam hPO) :
    IsInjectiveInO rd dP.Xdual dP.isCategoryO ∧
    (∃ (ι : Llam →ₗ⁅R, 𝔤⁆ dP.Xdual), Function.Injective ι ∧
      ∀ (N : LieSubmodule R 𝔤 dP.Xdual), N ≠ ⊥ →
        ∃ (v : Llam), v ≠ 0 ∧ ι v ∈ N) := by
  obtain ⟨π, hπ_surj⟩ := hPsurj
  have dL : DualInO cτ Llam hLO := dualInO cτ hLO
  obtain ⟨πdual, hπdual_surj_to_inj, _⟩ :=
    duality_functor_contravariant cτ hPO hLO π dP dL
  have hπdual_inj : Function.Injective πdual := hπdual_surj_to_inj hπ_surj
  obtain ⟨_, _, iso_L, hiso_L_bij⟩ := simple_module_self_dual cτ lam hLO hLirr hLhw dL
  let ι : Llam →ₗ⁅R, 𝔤⁆ dP.Xdual := LieModuleHom.comp πdual iso_L
  have hι_inj : Function.Injective ι := hπdual_inj.comp hiso_L_bij.1
  have hPdualInj : IsInjectiveInO rd dP.Xdual dP.isCategoryO :=
    duality_projective_to_injective cτ hPO hPproj dP
  have hEss : ∀ (N : LieSubmodule R 𝔤 dP.Xdual), N ≠ ⊥ →
      ∃ (v : Llam), v ≠ 0 ∧ ι v ∈ N := by
    sorry
  exact ⟨hPdualInj, ι, hι_inj, hEss⟩

end
