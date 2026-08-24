/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.DualityFunctor

noncomputable section

universe uCatO

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {R 𝔤}

def ExtVanishes_CategoryO
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) :
    ℕ →
    (X : Type uCatO) → [AddCommGroup X] → [Module R X] →
    [LieRingModule 𝔤 X] → [LieModule R 𝔤 X] →
    IsCategoryO Δ rd X →
    (Y : Type uCatO) → [AddCommGroup Y] → [Module R Y] →
    [LieRingModule 𝔤 Y] → [LieModule R 𝔤 Y] →
    IsCategoryO Δ rd Y → Prop
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => True
  | 1, X, _, _, _, _, _hXO, Y, _, _, _, _, _hYO =>
    ∀ (E : Type uCatO) [AddCommGroup E] [Module R E]
      [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
      (_hEO : IsCategoryO Δ rd E)
      (ι : Y →ₗ⁅R, 𝔤⁆ E) (_hι : Function.Injective ι)
      (p : E →ₗ⁅R, 𝔤⁆ X) (_hp : Function.Surjective p)
      (_hexact : ∀ e : E, p e = 0 ↔ ∃ m : Y, ι m = e),
      ∃ (s : X →ₗ⁅R, 𝔤⁆ E), ∀ x, p (s x) = x
  | n + 2, X, _, _, _, _, hXO, Y, _, _, _, _, _hYO =>
    ∀ (I : Type uCatO) [AddCommGroup I] [Module R I]
      [LieRingModule 𝔤 I] [LieModule R 𝔤 I]
      (_hIO : IsCategoryO Δ rd I)
      (Q : Type uCatO) [AddCommGroup Q] [Module R Q]
      [LieRingModule 𝔤 Q] [LieModule R 𝔤 Q]
      (hQO : IsCategoryO Δ rd Q)
      (ι : Y →ₗ⁅R, 𝔤⁆ I) (_hι : Function.Injective ι)
      (p : I →ₗ⁅R, 𝔤⁆ Q) (_hp : Function.Surjective p),
      ExtVanishes_CategoryO rd (n + 1) X hXO Q hQO

theorem free_over_nminus_is_projective_in_O
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hXfree : letI := instModuleUEASubalg Δ.𝔫_neg X;
              Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) X) :
    IsProjectiveInO rd X hXO := by


  sorry

theorem projective_implies_ext1_vanishes
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hXproj : IsProjectiveInO rd X hXO)
    {Y : Type uCatO} [AddCommGroup Y] [Module R Y]
    [LieRingModule 𝔤 Y] [LieModule R 𝔤 Y]
    (hYO : IsCategoryO Δ rd Y) :
    ExtVanishes_CategoryO rd 1 X hXO Y hYO := by
  intro E _ _ _ _ hEO ι _hι p hp _hexact
  exact hXproj E hEO X hXO p hp (LieModuleHom.id : X →ₗ⁅R, 𝔤⁆ X)

theorem ext1_vanishing_free_nminus_all_Y
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hXfree : letI := instModuleUEASubalg Δ.𝔫_neg X;
              Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) X)
    {Y : Type uCatO} [AddCommGroup Y] [Module R Y]
    [LieRingModule 𝔤 Y] [LieModule R 𝔤 Y]
    (hYO : IsCategoryO Δ rd Y) :
    ExtVanishes_CategoryO rd 1 X hXO Y hYO :=
  projective_implies_ext1_vanishes hXO (free_over_nminus_is_projective_in_O hXO hXfree) hYO

theorem ext_higher_vanishing_of_free_nminus_general
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hXfree : letI := instModuleUEASubalg Δ.𝔫_neg X;
              Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) X)
    (m : ℕ)
    {Y : Type uCatO} [AddCommGroup Y] [Module R Y]
    [LieRingModule 𝔤 Y] [LieModule R 𝔤 Y]
    (hYO : IsCategoryO Δ rd Y) :
    ExtVanishes_CategoryO rd (m + 1 + 1) X hXO Y hYO := by
  revert Y
  induction m with
  | zero =>
    intro Y _ _ _ _ hYO
    intro I _ _ _ _ _hIO Q _ _ _ _ hQO ι _hι p _hp
    exact ext1_vanishing_free_nminus_all_Y hXO hXfree hQO
  | succ n ih =>
    intro Y _ _ _ _ hYO
    intro I _ _ _ _ _hIO Q _ _ _ _ hQO ι _hι p _hp
    exact ih hQO

theorem ext_higher_vanishing_of_free_nminus
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hXfree : letI := instModuleUEASubalg Δ.𝔫_neg X;
              Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) X)
    (mu : Δ.𝔥 →ₗ[R] R)
    {MmuDual : Type uCatO} [AddCommGroup MmuDual] [Module R MmuDual]
    [LieRingModule 𝔤 MmuDual] [LieModule R 𝔤 MmuDual]
    (hMmuDualO : IsCategoryO Δ rd MmuDual)
    (_hMmuDual : IsContragredientVerma rd MmuDual mu hMmuDualO)
    (m : ℕ) :
    ExtVanishes_CategoryO rd (m + 1 + 1) X hXO MmuDual hMmuDualO :=
  ext_higher_vanishing_of_free_nminus_general hXO hXfree m hMmuDualO

theorem ext_vanishing_higher_of_standard_filtration
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hXsf : HasStandardFiltration rd X hXO)
    (mu : Δ.𝔥 →ₗ[R] R)
    {MmuDual : Type uCatO} [AddCommGroup MmuDual] [Module R MmuDual]
    [LieRingModule 𝔤 MmuDual] [LieModule R 𝔤 MmuDual]
    (hMmuDualO : IsCategoryO Δ rd MmuDual)
    (hMmuDual : IsContragredientVerma rd MmuDual mu hMmuDualO)
    (m : ℕ) :
    ExtVanishes_CategoryO rd (m + 1 + 1) X hXO MmuDual hMmuDualO := by
  have hXfree := standard_filtration_free_nminus_helper hXO hXsf
  exact ext_higher_vanishing_of_free_nminus hXO hXfree mu hMmuDualO hMmuDual m

end
