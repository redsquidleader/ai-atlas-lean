/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.BGGReciprocity
import Atlas.LieGroups.code.HeckeKL

noncomputable section

universe uCatO

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {R 𝔤}

def ExtOVanishes
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ} :
    ℕ →
    (X : Type uCatO) → [AddCommGroup X] → [Module R X] →
    [LieRingModule 𝔤 X] → [LieModule R 𝔤 X] →
    (IsCategoryO Δ rd X) →
    (Y : Type uCatO) → [AddCommGroup Y] → [Module R Y] →
    [LieRingModule 𝔤 Y] → [LieModule R 𝔤 Y] →
    (IsCategoryO Δ rd Y) →
    Prop
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => True
  | 1, X, _, _, _, _, _, Y, _, _, _, _, _ =>
    ∀ (E : Type uCatO) [AddCommGroup E] [Module R E]
      [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
      (_ : IsCategoryO Δ rd E)
      (ι : Y →ₗ⁅R, 𝔤⁆ E) (_ : Function.Injective ι)
      (p : E →ₗ⁅R, 𝔤⁆ X) (_ : Function.Surjective p)
      (_ : ∀ e : E, p e = 0 ↔ ∃ m : Y, ι m = e),
      ∃ (s : X →ₗ⁅R, 𝔤⁆ E), ∀ x, p (s x) = x
  | (n + 2), X, _, _, _, _, _, Y, _, _, _, _, hYO =>
    ∀ (K : Type uCatO) [AddCommGroup K] [Module R K]
      [LieRingModule 𝔤 K] [LieModule R 𝔤 K]
      (hKO : IsCategoryO Δ rd K)
      (P : Type uCatO) [AddCommGroup P] [Module R P]
      [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
      (hPO : IsCategoryO Δ rd P)
      (_ : IsProjectiveInO rd P hPO)
      (ι : K →ₗ⁅R, 𝔤⁆ P) (_ : Function.Injective ι)
      (p : P →ₗ⁅R, 𝔤⁆ X) (_ : Function.Surjective p)
      (_ : ∀ q, p q = 0 ↔ ∃ k, ι k = q),
      ExtOVanishes (n + 1) K hKO Y hYO

theorem projective_in_O_is_nminus_retract_of_free
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {P : Type uCatO} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (_hPO : IsCategoryO Δ rd P)
    (_hPproj : IsProjectiveInO rd P _hPO) :
    letI _instP := instModuleUEASubalg Δ.𝔫_neg P
    ∃ (Q : Type uCatO) (_ : AddCommGroup Q) (_ : Module R Q)
      (_ : LieRingModule 𝔤 Q) (_ : LieModule R 𝔤 Q),
      letI _instQ := instModuleUEASubalg Δ.𝔫_neg Q
      Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) Q ∧
      ∃ (ι : P →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] Q)
        (s : Q →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] P),
        s.comp ι = LinearMap.id := by


  letI : Module (UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) P := instModuleUEASubalg Δ.𝔫_neg P
  haveI hFree : Module.Free (UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) P :=
    projective_in_O_is_free_U_nminus (wg := wg) _hPO _hPproj
  exact ⟨P, inferInstance, inferInstance, inferInstance, inferInstance,
    hFree, LinearMap.id, LinearMap.id, LinearMap.id_comp _⟩

theorem quillen_suslin_UEA_nminus
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {P : Type uCatO} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    [Module (UniversalEnvelopingAlgebra R Δ.𝔫_neg) P] :
    Module.Projective (UniversalEnvelopingAlgebra R Δ.𝔫_neg) P →
    Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) P := by sorry

theorem nminus_projective_is_free
    {Δ : TriangularDecomposition R 𝔤}
    {P : Type uCatO} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P] :
    letI := instModuleUEASubalg Δ.𝔫_neg P
    Module.Projective (UniversalEnvelopingAlgebra R Δ.𝔫_neg) P →
    Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) P := by
  letI := instModuleUEASubalg Δ.𝔫_neg P
  exact quillen_suslin_UEA_nminus

theorem projective_in_O_is_free_nminus
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {P : Type uCatO} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (hPO : IsCategoryO Δ rd P)
    (_hPproj : IsProjectiveInO rd P hPO) :
    IsFreeOverNMinus (Δ := Δ) P := by

  unfold IsFreeOverNMinus
  letI := instModuleUEASubalg Δ.𝔫_neg P
  exact projective_in_O_is_free_U_nminus (wg := wg) hPO _hPproj


lemma UEA_induction_on
    {L : Type*} [LieRing L] [LieAlgebra R L]
    {C : UniversalEnvelopingAlgebra R L → Prop}
    (u : UniversalEnvelopingAlgebra R L)
    (h_alg : ∀ r : R, C (algebraMap R _ r))
    (h_ι : ∀ x : L, C (UniversalEnvelopingAlgebra.ι R x))
    (h_mul : ∀ a b, C a → C b → C (a * b))
    (h_add : ∀ a b, C a → C b → C (a + b)) :
    C u := by
  obtain ⟨t, rfl⟩ := RingQuot.mkAlgHom_surjective R
    (UniversalEnvelopingAlgebra.Rel R L) u
  change C ((UniversalEnvelopingAlgebra.mkAlgHom R L) t)
  induction t using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact h_alg r
  | ι x => exact h_ι x
  | mul a b ha hb => rw [map_mul]; exact h_mul _ _ ha hb
  | add a b ha hb => rw [map_add]; exact h_add _ _ ha hb


lemma lieModuleHom_ueaSubalg_compat
    {Δ : TriangularDecomposition R 𝔤}
    {M N : Type*} [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (f : M →ₗ⁅R, 𝔤⁆ N)
    (u : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) (m : M) :
    f ((ueaSubalgAction Δ.𝔫_neg M u) m) = (ueaSubalgAction Δ.𝔫_neg N u) (f m) := by
  suffices h : ∀ m, f ((ueaSubalgAction Δ.𝔫_neg M u) m) =
      (ueaSubalgAction Δ.𝔫_neg N u) (f m) from h m
  induction u using UEA_induction_on with
  | h_alg r =>
    intro m
    simp only [ueaSubalgAction, Algebra.algebraMap_eq_smul_one]
    simp [LinearMap.smul_apply, map_smul]
  | h_ι x =>
    intro m
    simp only [ueaSubalgAction, UniversalEnvelopingAlgebra.lift_ι_apply,
      LieModule.toEnd_apply_apply]
    exact f.map_lie x m
  | h_mul a b ha hb =>
    intro m
    simp only [map_mul]
    change f ((ueaSubalgAction Δ.𝔫_neg M a).comp (ueaSubalgAction Δ.𝔫_neg M b) m) =
           (ueaSubalgAction Δ.𝔫_neg N a).comp (ueaSubalgAction Δ.𝔫_neg N b) (f m)
    simp only [LinearMap.comp_apply]
    rw [ha ((ueaSubalgAction Δ.𝔫_neg M b) m)]
    congr 1
    exact hb m
  | h_add a b ha hb =>
    intro m
    simp only [map_add, LinearMap.add_apply, map_add]
    rw [ha m, hb m]


noncomputable def lieModuleHomToUEALinearMap
    {Δ : TriangularDecomposition R 𝔤}
    {M N : Type uCatO} [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (f : M →ₗ⁅R, 𝔤⁆ N) :
    letI := instModuleUEASubalg Δ.𝔫_neg M
    letI := instModuleUEASubalg Δ.𝔫_neg N
    M →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] N := by
  letI := instModuleUEASubalg Δ.𝔫_neg M
  letI := instModuleUEASubalg Δ.𝔫_neg N
  exact {
    toFun := f
    map_add' := f.toLinearMap.map_add
    map_smul' := fun r m => lieModuleHom_ueaSubalg_compat f r m
  }

theorem direct_summand_of_free_nminus_is_free
    {Δ : TriangularDecomposition R 𝔤}
    {P : Type uCatO} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (_hPfree : IsFreeOverNMinus (Δ := Δ) P)
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (_hXfree : IsFreeOverNMinus (Δ := Δ) X)
    {K : Type uCatO} [AddCommGroup K] [Module R K]
    [LieRingModule 𝔤 K] [LieModule R 𝔤 K]
    (_ι : K →ₗ⁅R, 𝔤⁆ P) (_hι : Function.Injective _ι)
    (_p : P →ₗ⁅R, 𝔤⁆ X) (_hp : Function.Surjective _p)
    (_hexact : ∀ q, _p q = 0 ↔ ∃ k, _ι k = q) :
    IsFreeOverNMinus (Δ := Δ) K := by

  letI instK := instModuleUEASubalg Δ.𝔫_neg K
  letI instP := instModuleUEASubalg Δ.𝔫_neg P
  letI instX := instModuleUEASubalg Δ.𝔫_neg X

  let ι_U : K →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] P :=
    lieModuleHomToUEALinearMap _ι
  let p_U : P →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] X :=
    lieModuleHomToUEALinearMap _p

  haveI : Module.Free (UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) X := _hXfree
  haveI : Module.Projective (UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) X :=
    Module.Projective.of_free

  have hp_surj : Function.Surjective p_U := _hp
  obtain ⟨σ_U, hσ⟩ := Module.projective_lifting_property p_U LinearMap.id hp_surj


  have hι_inj : Function.Injective ι_U := _hι
  have hker : ∀ q, p_U (q - σ_U (p_U q)) = 0 := by
    intro q
    simp only [map_sub]
    have : p_U (σ_U (p_U q)) = p_U q := by
      have h := LinearMap.ext_iff.mp hσ (p_U q)
      simp [LinearMap.comp_apply] at h
      exact h
    rw [this, sub_self]

  have hpre : ∀ q, ∃ k, ι_U k = q - σ_U (p_U q) := by
    intro q
    exact (_hexact (q - σ_U (p_U q))).mp (hker q)
  let ret_fun : P → K := fun q => Classical.choose (hpre q)
  have hret_spec : ∀ q, ι_U (ret_fun q) = q - σ_U (p_U q) :=
    fun q => Classical.choose_spec (hpre q)

  have hret_add : ∀ x y, ret_fun (x + y) = ret_fun x + ret_fun y := by
    intro x y
    apply hι_inj
    simp only [map_add, hret_spec]
    abel
  have hret_smul : ∀ (r : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) x,
      ret_fun (r • x) = r • ret_fun x := by
    intro r x
    apply hι_inj
    simp only [map_smul, hret_spec, smul_sub]

  let ret_U : P →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] K := {
    toFun := ret_fun
    map_add' := hret_add
    map_smul' := hret_smul
  }

  have hret_ι : ∀ k, ret_U (ι_U k) = k := by
    intro k
    apply hι_inj
    show ι_U (ret_fun (ι_U k)) = ι_U k
    rw [hret_spec (ι_U k)]


    have : p_U (ι_U k) = 0 := by
      change _p (_ι k) = 0
      exact (_hexact (_ι k)).mpr ⟨k, rfl⟩
    rw [this, map_zero, sub_zero]

  haveI : Module.Free (UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) P := _hPfree
  haveI : Module.Projective (UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) P :=
    Module.Projective.of_free

  haveI : Module.Projective (UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) K :=
    Module.Projective.of_split ι_U ret_U (LinearMap.ext hret_ι)

  unfold IsFreeOverNMinus
  exact nminus_projective_is_free (by assumption)

theorem kernel_of_projective_over_free_nminus_is_free
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (_hXO : IsCategoryO Δ rd X)
    (hXfree : IsFreeOverNMinus (Δ := Δ) X)
    {K : Type uCatO} [AddCommGroup K] [Module R K]
    [LieRingModule 𝔤 K] [LieModule R 𝔤 K]
    (_hKO : IsCategoryO Δ rd K)
    {P : Type uCatO} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (_hPO : IsCategoryO Δ rd P)
    (_hPproj : IsProjectiveInO rd P _hPO)
    (ι : K →ₗ⁅R, 𝔤⁆ P) (_hι : Function.Injective ι)
    (p : P →ₗ⁅R, 𝔤⁆ X) (_hp : Function.Surjective p)
    (hexact : ∀ q, p q = 0 ↔ ∃ k, ι k = q) :
    IsFreeOverNMinus (Δ := Δ) K := by

  have hPfree : IsFreeOverNMinus (Δ := Δ) P :=
    projective_in_O_is_free_nminus (wg := wg) _hPO _hPproj


  exact direct_summand_of_free_nminus_is_free hPfree hXfree ι _hι p _hp hexact

theorem ext_vanishing_free_nminus
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hXfree : IsFreeOverNMinus (Δ := Δ) X)
    (mu : Δ.𝔥 →ₗ[R] R)
    (MmuDual : Type uCatO) [AddCommGroup MmuDual] [Module R MmuDual]
    [LieRingModule 𝔤 MmuDual] [LieModule R 𝔤 MmuDual]
    (hMmuDualO : IsCategoryO Δ rd MmuDual)
    (hMmuDual : IsContragredientVerma rd MmuDual mu hMmuDualO)
    (i : ℕ) (hi : i > 0) :
    ExtOVanishes (Δ := Δ) (rd := rd) i X hXO MmuDual hMmuDualO := by


  revert X
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro X _ _ _ _ hXO hXfree
    match i, hi with
    | 0, hi => omega
    | 1, _ =>

      intro E _ _ _ _ hEO ι hι p hp hexact
      have hExt1 : Ext1VanishingForContragredientVerma rd X hXO :=
        ext_vanishing_of_standard_filtration hXO
          (free_nminus_has_standard_filtration (wg := wg) hXO hXfree)

      exact hExt1 mu MmuDual hMmuDualO hMmuDual E hEO ι hι p hp hexact
    | m + 2, _ =>

      intro K _ _ _ _ hKO P _ _ _ _ hPO hPproj ι hι p hp hexact
      have hKfree : IsFreeOverNMinus (Δ := Δ) K :=
        kernel_of_projective_over_free_nminus_is_free
          (wg := wg) hXO hXfree hKO hPO hPproj ι hι p hp hexact
      exact ih (m + 1) (by omega) (Nat.succ_pos m) hKO hKfree

theorem standardly_filtered_higher_ext_vanishing
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hSF : HasStandardFiltration rd X hXO)
    (mu : Δ.𝔥 →ₗ[R] R)
    (MmuDual : Type uCatO) [AddCommGroup MmuDual] [Module R MmuDual]
    [LieRingModule 𝔤 MmuDual] [LieModule R 𝔤 MmuDual]
    (hMmuDualO : IsCategoryO Δ rd MmuDual)
    (hMmuDual : IsContragredientVerma rd MmuDual mu hMmuDualO)
    (i : ℕ) (hi : i > 0) :
    ExtOVanishes (Δ := Δ) (rd := rd) i X hXO MmuDual hMmuDualO := by

  have hXfree : IsFreeOverNMinus (Δ := Δ) X :=
    standard_filtration_free_nminus_helper hXO hSF

  exact ext_vanishing_free_nminus (wg := wg) hXO hXfree mu MmuDual hMmuDualO hMmuDual i hi

theorem nonsplit_verma_ext_implies_comp_mult
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    {Mlam : Type uCatO} [AddCommGroup Mlam] [Module R Mlam]
    [LieRingModule 𝔤 Mlam] [LieModule R 𝔤 Mlam]
    (hMlam : IsVermaModule Δ Mlam lam)
    (hMlamO : IsCategoryO Δ rd Mlam)
    {Mmu : Type uCatO} [AddCommGroup Mmu] [Module R Mmu]
    [LieRingModule 𝔤 Mmu] [LieModule R 𝔤 Mmu]
    (hMmu : IsVermaModule Δ Mmu mu)
    (hMmuO : IsCategoryO Δ rd Mmu)
    (E : Type uCatO) [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    (hEO : IsCategoryO Δ rd E)
    (i : Mlam →ₗ⁅R, 𝔤⁆ E) (hi : Function.Injective i)
    (p : E →ₗ⁅R, 𝔤⁆ Mmu) (hp : Function.Surjective p)
    (hns : ¬ ∃ (s : Mmu →ₗ⁅R, 𝔤⁆ E), ∀ x, p (s x) = x) :
    compositionMultiplicity rd wg mu lam ≠ 0 ∧ lam ≠ mu := by sorry

end
