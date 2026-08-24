/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.CompositionSeries

noncomputable section

universe uCatO

structure CartanInvolution
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (_rd : PositiveRootData Δ) where
  τ : 𝔤 →ₗ[R] 𝔤
  involution : τ ∘ₗ τ = LinearMap.id
  negate_cartan : ∀ h : Δ.𝔥, τ (h : 𝔤) = -(h : 𝔤)
  anti_hom : ∀ (X Y : 𝔤), τ ⁅X, Y⁆ = ⁅τ Y, τ X⁆

structure DualInO
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (cτ : CartanInvolution rd)
    (X : Type uCatO) [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hX : IsCategoryO Δ rd X) where
  Xdual : Type uCatO
  [instAddCommGroup : AddCommGroup Xdual]
  [instModule : Module R Xdual]
  [instLieRingModule : LieRingModule 𝔤 Xdual]
  [instLieModule : LieModule R 𝔤 Xdual]
  isCategoryO : IsCategoryO Δ rd Xdual

attribute [instance] DualInO.instAddCommGroup DualInO.instModule
  DualInO.instLieRingModule DualInO.instLieModule

def dualInO
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (cτ : CartanInvolution rd)
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hX : IsCategoryO Δ rd X) :
    DualInO cτ X hX := by
  sorry

theorem prop_20_9_ii_simple_self_dual
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (cτ : CartanInvolution rd)
    {Llam : Type uCatO} [AddCommGroup Llam] [Module R Llam]
    [LieRingModule 𝔤 Llam] [LieModule R 𝔤 Llam]
    (lam : Δ.𝔥 →ₗ[R] R)
    (hLO : IsCategoryO Δ rd Llam)
    (hLirr : LieModule.IsIrreducible R 𝔤 Llam)
    (hLhw : IsHighestWeightModule Δ Llam lam)
    (d : DualInO cτ Llam hLO) :
    LieModule.IsIrreducible R 𝔤 d.Xdual ∧
    Nonempty (IsHighestWeightModule Δ d.Xdual lam) ∧
    ∃ (iso : Llam →ₗ⁅R, 𝔤⁆ d.Xdual), Function.Bijective iso := by
  sorry

def IsContragredientVerma
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (M : Type uCatO) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (lam : Δ.𝔥 →ₗ[R] R)
    (_hM : IsCategoryO Δ rd M) : Prop :=
  ∃ (Mlam : Type uCatO) (_ : AddCommGroup Mlam) (_ : Module R Mlam)
    (_ : LieRingModule 𝔤 Mlam) (_ : LieModule R 𝔤 Mlam),
    Nonempty (IsVermaModule Δ Mlam lam) ∧ IsCategoryO Δ rd Mlam ∧
    (∃ (β : M →ₗ[R] Mlam →ₗ[R] R),
      (∀ (x : 𝔤) (m : M) (m' : Mlam), β (⁅x, m⁆) m' + β m ⁅x, m'⁆ = 0) ∧
      (∀ m : M, (∀ m' : Mlam, β m m' = 0) → m = 0) ∧
      (∀ m' : Mlam, (∀ m : M, β m m' = 0) → m' = 0))

theorem prop_20_9_ii_verma_dual_contragredient
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (cτ : CartanInvolution rd)
    {Mlam : Type uCatO} [AddCommGroup Mlam] [Module R Mlam]
    [LieRingModule 𝔤 Mlam] [LieModule R 𝔤 Mlam]
    (lam : Δ.𝔥 →ₗ[R] R)
    (hMlam : IsVermaModule Δ Mlam lam)
    (hMlamO : IsCategoryO Δ rd Mlam)
    (d : DualInO cτ Mlam hMlamO) :
    IsContragredientVerma rd d.Xdual lam d.isCategoryO := by
  sorry

theorem prop_20_9_iii_contravariant
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (cτ : CartanInvolution rd)
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hX : IsCategoryO Δ rd X)
    {Y : Type uCatO} [AddCommGroup Y] [Module R Y]
    [LieRingModule 𝔤 Y] [LieModule R 𝔤 Y]
    (hY : IsCategoryO Δ rd Y)
    (f : X →ₗ⁅R, 𝔤⁆ Y)
    (dX : DualInO cτ X hX)
    (dY : DualInO cτ Y hY) :
    ∃ (fdual : dY.Xdual →ₗ⁅R, 𝔤⁆ dX.Xdual),
      (Function.Surjective f → Function.Injective fdual) ∧
      (Function.Injective f → Function.Surjective fdual) := by
  sorry

theorem prop_20_9_iii_involutive
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (cτ : CartanInvolution rd)
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hX : IsCategoryO Δ rd X)
    (dX : DualInO cτ X hX)
    (dXdd : DualInO cτ dX.Xdual dX.isCategoryO) :
    ∃ (iso : X →ₗ⁅R, 𝔤⁆ dXdd.Xdual), Function.Bijective iso := by
  sorry

theorem prop_20_9_iii_preserves_blocks
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (cτ : CartanInvolution rd)
    (wg : WeylGroupData Δ)
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hX : IsCategoryO Δ rd X)
    (lam : Δ.𝔥 →ₗ[R] R)
    (hBlock : IsInBlockO Δ rd wg X lam)
    (d : DualInO cτ X hX) :
    IsInBlockO Δ rd wg d.Xdual lam := by
  sorry

theorem simple_module_self_dual
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (cτ : CartanInvolution rd)
    {Llam : Type uCatO} [AddCommGroup Llam] [Module R Llam]
    [LieRingModule 𝔤 Llam] [LieModule R 𝔤 Llam]
    (lam : Δ.𝔥 →ₗ[R] R)
    (hLO : IsCategoryO Δ rd Llam)
    (hLirr : LieModule.IsIrreducible R 𝔤 Llam)
    (hLhw : IsHighestWeightModule Δ Llam lam)
    (d : DualInO cτ Llam hLO) :
    LieModule.IsIrreducible R 𝔤 d.Xdual ∧
    Nonempty (IsHighestWeightModule Δ d.Xdual lam) ∧
    ∃ (iso : Llam →ₗ⁅R, 𝔤⁆ d.Xdual), Function.Bijective iso :=
  prop_20_9_ii_simple_self_dual cτ lam hLO hLirr hLhw d

theorem verma_dual_is_contragredient
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (cτ : CartanInvolution rd)
    {Mlam : Type uCatO} [AddCommGroup Mlam] [Module R Mlam]
    [LieRingModule 𝔤 Mlam] [LieModule R 𝔤 Mlam]
    (lam : Δ.𝔥 →ₗ[R] R)
    (hMlam : IsVermaModule Δ Mlam lam)
    (hMlamO : IsCategoryO Δ rd Mlam)
    (d : DualInO cτ Mlam hMlamO) :
    IsContragredientVerma rd d.Xdual lam d.isCategoryO :=
  prop_20_9_ii_verma_dual_contragredient cτ lam hMlam hMlamO d

theorem duality_functor_contravariant
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (cτ : CartanInvolution rd)
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hX : IsCategoryO Δ rd X)
    {Y : Type uCatO} [AddCommGroup Y] [Module R Y]
    [LieRingModule 𝔤 Y] [LieModule R 𝔤 Y]
    (hY : IsCategoryO Δ rd Y)
    (f : X →ₗ⁅R, 𝔤⁆ Y)
    (dX : DualInO cτ X hX)
    (dY : DualInO cτ Y hY) :
    ∃ (fdual : dY.Xdual →ₗ⁅R, 𝔤⁆ dX.Xdual),
      (Function.Surjective f → Function.Injective fdual) ∧
      (Function.Injective f → Function.Surjective fdual) :=
  prop_20_9_iii_contravariant cτ hX hY f dX dY

theorem duality_functor_involutive
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (cτ : CartanInvolution rd)
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hX : IsCategoryO Δ rd X)
    (dX : DualInO cτ X hX)
    (dXdd : DualInO cτ dX.Xdual dX.isCategoryO) :
    ∃ (iso : X →ₗ⁅R, 𝔤⁆ dXdd.Xdual), Function.Bijective iso :=
  prop_20_9_iii_involutive cτ hX dX dXdd

end
