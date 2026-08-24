/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.CategoryOII
import Atlas.LieGroups.code.DufloJoseph
import Atlas.LieGroups.code.BGGReciprocity
import Atlas.LieGroups.code.TensorO
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.Algebra.Lie.Semisimple.Basic

noncomputable section

open scoped TensorProduct

universe uM

variable {R : Type*} [CommRing R]
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
variable (Δ : TriangularDecomposition R 𝔤)
variable (rd : PositiveRootData Δ)
variable (wg : WeylGroupData Δ)

local notation "𝔥*" => (Δ.𝔥 →ₗ[R] R)

structure TranslationFunctorData where
  lam : 𝔥*
  mu : 𝔥*
  V : Type*
  [V_addCommGroup : AddCommGroup V]
  [V_module : Module R V]
  [V_lieRingModule : LieRingModule 𝔤 V]
  [V_lieModule : LieModule R 𝔤 V]
  [V_finiteDim : Module.Finite R V]
  [V_irreducible : IsSimpleModule R V]
  lam_dominant : IsDominantWeightLE rd wg lam
  mu_dominant : IsDominantWeightLE rd wg mu
  extremal_weight : mu - lam ∈ weights Δ V

attribute [instance] TranslationFunctorData.V_addCommGroup
  TranslationFunctorData.V_module TranslationFunctorData.V_lieRingModule
  TranslationFunctorData.V_lieModule TranslationFunctorData.V_finiteDim
  TranslationFunctorData.V_irreducible

structure TranslationFunctorData.ApplyResult
    (F : TranslationFunctorData Δ rd wg)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] where
  carrier : Type*
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module R carrier]
  [instLieRingModule : LieRingModule 𝔤 carrier]
  [instLieModule : LieModule R 𝔤 carrier]
  hasInfChar : HasInfinitesimalCharacter (R := R) (𝔤 := 𝔤) carrier (evalHC Δ wg F.mu)

attribute [instance] TranslationFunctorData.ApplyResult.instAddCommGroup
  TranslationFunctorData.ApplyResult.instModule
  TranslationFunctorData.ApplyResult.instLieRingModule
  TranslationFunctorData.ApplyResult.instLieModule

section CharEigenspace

variable {R : Type*} [CommRing R]
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
variable (act : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
variable (χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R)

def charEigenspace : Submodule R M where
  carrier := {m : M | ∀ z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)),
    act (z : UniversalEnvelopingAlgebra R 𝔤) m = χ z • m}
  zero_mem' z := by simp [map_zero, smul_zero]
  add_mem' {a b} ha hb z := by simp [map_add, ha z, hb z, smul_add]
  smul_mem' r m hm z := by
    show act (↑z) (r • m) = χ z • (r • m)
    rw [(act (↑z)).map_smul, hm z, smul_comm]

set_option linter.unusedSectionVars false in
theorem charEigenspace_closed_uea (u : UniversalEnvelopingAlgebra R 𝔤) {m : M}
    (hm : m ∈ charEigenspace act χ) :
    act u m ∈ charEigenspace act χ := by
  intro z

  have h1 : (act (↑z)) ((act u) m) =
      (act ((↑z : UniversalEnvelopingAlgebra R 𝔤) * u)) m := by
    rw [map_mul]; rfl

  have hc : (z : UniversalEnvelopingAlgebra R 𝔤) * u =
      u * (z : UniversalEnvelopingAlgebra R 𝔤) :=
    ((Subalgebra.mem_center_iff.mp z.property) u).symm

  have h2 : (act (u * (↑z : UniversalEnvelopingAlgebra R 𝔤))) m =
      (act u) ((act (↑z)) m) := by
    rw [map_mul]; rfl
  rw [h1, hc, h2, hm z, (act u).map_smul]

def charEigenspaceLie
    (hcompat : ∀ (x : 𝔤) (m : M),
      act (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆) :
    LieSubmodule R 𝔤 M where
  __ := charEigenspace act χ
  lie_mem {x m} hm := by
    show ⁅x, m⁆ ∈ charEigenspace act χ
    rw [← hcompat x m]
    exact charEigenspace_closed_uea act χ (UniversalEnvelopingAlgebra.ι R x) hm

noncomputable def restrictedUEAAction
    (hcompat : ∀ (x : 𝔤) (m : M),
      act (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆) :
    UniversalEnvelopingAlgebra R 𝔤 →ₐ[R]
      Module.End R ↥(charEigenspaceLie act χ hcompat) where
  toFun u :=
    { toFun := fun ⟨m, hm⟩ =>
        ⟨act u m, charEigenspace_closed_uea act χ u hm⟩
      map_add' := fun ⟨a, _⟩ ⟨b, _⟩ => by simp [Subtype.ext_iff, map_add]
      map_smul' := fun r ⟨m, _⟩ => by simp [Subtype.ext_iff, (act u).map_smul] }
  map_one' := by ext ⟨m, _⟩; simp [map_one]
  map_mul' a b := by
    ext ⟨m, _⟩
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply]
    show (act (a * b) m : M) = act a (act b m)
    rw [map_mul]; rfl
  map_zero' := by ext ⟨m, _⟩; simp [map_zero]
  map_add' a b := by
    ext ⟨m, _⟩; simp [map_add, LinearMap.add_apply]
  commutes' r := by
    ext ⟨m, _⟩
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    show (act (algebraMap R _ r) m : M) = r • m
    rw [AlgHom.commutes]; rfl

theorem restrictedUEAAction_compat
    (hcompat : ∀ (x : 𝔤) (m : M),
      act (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (x : 𝔤) (m : ↥(charEigenspaceLie act χ hcompat)) :
    restrictedUEAAction act χ hcompat (UniversalEnvelopingAlgebra.ι R x) m =
      ⁅x, m⁆ := by
  ext; simp [restrictedUEAAction]; exact hcompat x ↑m

theorem restrictedUEA_center_acts
    (hcompat : ∀ (x : 𝔤) (m : M),
      act (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)))
    (m : ↥(charEigenspaceLie act χ hcompat)) :
    restrictedUEAAction act χ hcompat
      (z : UniversalEnvelopingAlgebra R 𝔤) m = χ z • m := by
  ext; simp [restrictedUEAAction]; exact m.property z

end CharEigenspace

theorem translation_center_acts_by_scalar_ax

    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (F : TranslationFunctorData Δ rd wg)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)))
    (m : F.V ⊗[R] M) :
    ueaActionFromLieModule (F.V ⊗[R] M) (z : UniversalEnvelopingAlgebra R 𝔤) m =
      evalHC Δ wg F.mu z • m := by sorry

noncomputable def TranslationFunctorData.applyToModule
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (F : TranslationFunctorData Δ rd wg)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    F.ApplyResult Δ rd wg M :=
  let act := ueaActionFromLieModule (R := R) (𝔤 := 𝔤) (F.V ⊗[R] M)
  let hcompat := ueaActionFromLieModule_compat (R := R) (𝔤 := 𝔤) (F.V ⊗[R] M)
  let χ := evalHC Δ wg F.mu
  let S := charEigenspaceLie act χ hcompat
  { carrier := ↥S
    instAddCommGroup := inferInstance
    instModule := inferInstance
    instLieRingModule := inferInstance
    instLieModule := inferInstance
    hasInfChar :=
      { ueaAction := restrictedUEAAction act χ hcompat
        compat := restrictedUEAAction_compat act χ hcompat
        center_acts_by_scalar := restrictedUEA_center_acts act χ hcompat } }

theorem lemma_23_4_shifted_stabilizer
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)

    (lam mu : Δ.𝔥 →ₗ[R] R)
    (hlam : IsDominantWeightLE rd wg lam)
    (hmu : IsDominantWeightLE rd wg mu)

    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V] [IsSimpleModule R V]
    (hext : mu - lam ∈ weights Δ V)

    (w : wg.W)
    (hw_weight : wg.shiftedAction w mu - lam ∈ weights Δ V) :

    wg.shiftedAction w mu = mu := by sorry

theorem norm_inequality_forces_extremal_weight
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (F : TranslationFunctorData Δ rd wg)
    (M_lam : Type*) [AddCommGroup M_lam] [Module R M_lam]
    [LieRingModule 𝔤 M_lam] [LieModule R 𝔤 M_lam]
    (_hM : IsVermaModule Δ M_lam (F.lam - wg.ρ))
    (_hW : WeylStabilizerModQ rd wg F.lam ⊆ WeylStabilizerModQ rd wg F.mu)

    (β : Δ.𝔥 →ₗ[R] R)
    (_hβ_weight : β ∈ weights Δ F.V)

    (_hβ_survives : evalHC Δ wg (F.lam + β) = evalHC Δ wg F.mu) :

    β = F.mu - F.lam := by

  have hdef : ∀ (wt : Δ.𝔥 →ₗ[R] R)
    (z : ↑(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))),
    evalHC Δ wg wt z = evalWeight Δ (wt + wg.ρ)
      ((chevalley_restriction_hc_iso Δ wg z : wg.invariantSubalgebra) :
        UniversalEnvelopingAlgebra R Δ.𝔥) := by
    intro wt z; rfl

  have hrev : evalHC Δ wg F.mu = evalHC Δ wg (F.lam + β) := _hβ_survives.symm
  rw [infinitesimalCharacter_eq_iff_shiftedWeylOrbit Δ wg (evalHC Δ wg) hdef
    F.mu (F.lam + β)] at hrev
  obtain ⟨w', hw'⟩ := hrev


  have hw'_weight : wg.shiftedAction w' F.mu - F.lam ∈ weights Δ F.V := by
    have : wg.shiftedAction w' F.mu - F.lam = β := by
      rw [← hw']; simp [add_sub_cancel_left]
    rw [this]; exact _hβ_weight
  have hstab := lemma_23_4_shifted_stabilizer Δ rd wg F.lam F.mu
    F.lam_dominant F.mu_dominant F.V F.extremal_weight w' hw'_weight


  have key : F.lam + β = F.mu := by rw [hw', hstab]
  exact eq_sub_of_add_eq' key

theorem block_projection_single_verma_factor
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (F : TranslationFunctorData Δ rd wg)
    (M_lam : Type*) [AddCommGroup M_lam] [Module R M_lam]
    [LieRingModule 𝔤 M_lam] [LieModule R 𝔤 M_lam]
    (_hM : IsVermaModule Δ M_lam (F.lam - wg.ρ))
    (_hW : WeylStabilizerModQ rd wg F.lam ⊆ WeylStabilizerModQ rd wg F.mu)

    (_h_unique : ∀ (β : Δ.𝔥 →ₗ[R] R),
      β ∈ weights Δ F.V →
      evalHC Δ wg (F.lam + β) = evalHC Δ wg F.mu →
      β = F.mu - F.lam) :

    Nonempty (IsVermaModule Δ (F.applyToModule Δ rd wg M_lam).carrier (F.mu - wg.ρ)) := by sorry

theorem translation_functor_verma_output
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (F : TranslationFunctorData Δ rd wg)
    (M_lam : Type*) [AddCommGroup M_lam] [Module R M_lam]
    [LieRingModule 𝔤 M_lam] [LieModule R 𝔤 M_lam]
    (hM : IsVermaModule Δ M_lam (F.lam - wg.ρ))
    (hW : WeylStabilizerModQ rd wg F.lam ⊆ WeylStabilizerModQ rd wg F.mu) :
    Nonempty (IsVermaModule Δ (F.applyToModule Δ rd wg M_lam).carrier (F.mu - wg.ρ)) := by

  have h_unique : ∀ (β : Δ.𝔥 →ₗ[R] R),
      β ∈ weights Δ F.V →
      evalHC Δ wg (F.lam + β) = evalHC Δ wg F.mu →
      β = F.mu - F.lam :=
    fun β hβ_wt hβ_surv =>
      norm_inequality_forces_extremal_weight Δ rd wg F M_lam hM hW β hβ_wt hβ_surv

  exact block_projection_single_verma_factor Δ rd wg F M_lam hM hW h_unique

theorem TranslationFunctor.verma_maps_to_verma
    (F : TranslationFunctorData Δ rd wg)
    (M_lam : Type*) [AddCommGroup M_lam] [Module R M_lam]
    [LieRingModule 𝔤 M_lam] [LieModule R 𝔤 M_lam]
    (hM : IsVermaModule Δ M_lam (F.lam - wg.ρ))
    (hW : WeylStabilizerModQ rd wg F.lam ⊆ WeylStabilizerModQ rd wg F.mu) :

    let result := F.applyToModule Δ rd wg M_lam
    Nonempty (IsVermaModule Δ result.carrier (F.mu - wg.ρ)) := by


  exact translation_functor_verma_output Δ rd wg F M_lam hM hW

structure IsContragredientLieModule
    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (W : Type*) [AddCommGroup W] [Module R W]
    [LieRingModule 𝔤 W] [LieModule R 𝔤 W] where
  pairing : V →ₗ[R] W →ₗ[R] R
  nondegenerate_left : ∀ v : V, (∀ w : W, pairing v w = 0) → v = 0
  nondegenerate_right : ∀ w : W, (∀ v : V, pairing v w = 0) → w = 0
  equivariant : ∀ (x : 𝔤) (v : V) (w : W),
    pairing (⁅x, v⁆) w + pairing v (⁅x, w⁆) = 0

def IsContragredientLieModule.symm
    {V : Type*} [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    {W : Type*} [AddCommGroup W] [Module R W] [LieRingModule 𝔤 W] [LieModule R 𝔤 W]
    (h : IsContragredientLieModule (R := R) (𝔤 := 𝔤) V W) :
    IsContragredientLieModule (R := R) (𝔤 := 𝔤) W V where
  pairing :=
    { toFun := fun w =>
        { toFun := fun v => h.pairing v w
          map_add' := fun v₁ v₂ => by simp [map_add]
          map_smul' := fun r v => by simp [map_smul] }
      map_add' := fun w₁ w₂ => by
        ext v; simp [map_add]
      map_smul' := fun r w => by
        ext v; simp [map_smul] }
  nondegenerate_left := fun w hw => h.nondegenerate_right w (fun v => hw v)
  nondegenerate_right := fun v hv => h.nondegenerate_left v (fun w => hv w)
  equivariant := fun x w v => by
    have h_eq := h.equivariant x v w


    rw [add_comm]
    exact h_eq

theorem exists_verma_module
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (wt : Δ.𝔥 →ₗ[R] R) :
    ∃ (M_lam : Type*) (_ : AddCommGroup M_lam) (_ : Module R M_lam)
      (_ : LieRingModule 𝔤 M_lam) (_ : LieModule R 𝔤 M_lam),
      Nonempty (IsVermaModule Δ M_lam wt) := by sorry

theorem verma_module_iso_of_same_weight
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (M₁ : Type*) [AddCommGroup M₁] [Module R M₁] [LieRingModule 𝔤 M₁] [LieModule R 𝔤 M₁]
    (M₂ : Type*) [AddCommGroup M₂] [Module R M₂] [LieRingModule 𝔤 M₂] [LieModule R 𝔤 M₂]
    (wt : Δ.𝔥 →ₗ[R] R)
    (h₁ : IsVermaModule Δ M₁ wt) (h₂ : IsVermaModule Δ M₂ wt) :
    Nonempty (M₁ ≃ₗ⁅R, 𝔤⁆ M₂) := by sorry

theorem projective_functor_determination_on_block
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (F G : TranslationFunctorData Δ rd wg)
    (hG_lam : G.lam = F.mu) (hG_mu : G.mu = F.lam)
    (hG_V_dual : IsContragredientLieModule (R := R) (𝔤 := 𝔤) F.V G.V)
    (hW : WeylStabilizerModQ rd wg F.lam = WeylStabilizerModQ rd wg F.mu)

    (M_lam : Type*) [AddCommGroup M_lam] [Module R M_lam]
    [LieRingModule 𝔤 M_lam] [LieModule R 𝔤 M_lam]
    (hVerma : IsVermaModule Δ M_lam (F.lam - wg.ρ))

    (hVerma_fixed : Nonempty ((G.applyToModule Δ rd wg
      (F.applyToModule Δ rd wg M_lam).carrier).carrier ≃ₗ⁅R, 𝔤⁆ M_lam))


    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM_ic : HasInfinitesimalCharacter (R := R) (𝔤 := 𝔤) M (evalHC Δ wg F.lam)) :
    let FM := F.applyToModule Δ rd wg M
    let GFM := G.applyToModule Δ rd wg FM.carrier
    Nonempty (GFM.carrier ≃ₗ⁅R, 𝔤⁆ M) := by sorry

theorem composition_fixes_verma
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (F G : TranslationFunctorData Δ rd wg)
    (hG_lam : G.lam = F.mu) (hG_mu : G.mu = F.lam)
    (hW : WeylStabilizerModQ rd wg F.lam = WeylStabilizerModQ rd wg F.mu)
    (M_lam : Type*) [AddCommGroup M_lam] [Module R M_lam]
    [LieRingModule 𝔤 M_lam] [LieModule R 𝔤 M_lam]
    (hVerma : IsVermaModule Δ M_lam (F.lam - wg.ρ)) :
    Nonempty ((G.applyToModule Δ rd wg
      (F.applyToModule Δ rd wg M_lam).carrier).carrier ≃ₗ⁅R, 𝔤⁆ M_lam) := by

  have hFV := translation_functor_verma_output Δ rd wg F M_lam hVerma
    (hW ▸ le_refl _)

  have hGFV : Nonempty (IsVermaModule Δ
      (G.applyToModule Δ rd wg
        (F.applyToModule Δ rd wg M_lam).carrier).carrier
      (G.mu - wg.ρ)) := by
    obtain ⟨hFV_inst⟩ := hFV
    have hW' : WeylStabilizerModQ rd wg G.lam ⊆ WeylStabilizerModQ rd wg G.mu := by
      rw [hG_lam, hG_mu]; exact hW ▸ le_refl _
    have hFV_inst' : IsVermaModule Δ
        (F.applyToModule Δ rd wg M_lam).carrier (G.lam - wg.ρ) := by
      rw [hG_lam]; exact hFV_inst
    exact translation_functor_verma_output Δ rd wg G _ hFV_inst' hW'

  obtain ⟨hGFV_inst⟩ := hGFV
  have hGFV_inst' : IsVermaModule Δ
      (G.applyToModule Δ rd wg
        (F.applyToModule Δ rd wg M_lam).carrier).carrier
      (F.lam - wg.ρ) := by
    rw [← hG_mu]; exact hGFV_inst
  exact verma_module_iso_of_same_weight Δ _ _ _ hGFV_inst' hVerma

theorem translation_functor_composition_iso_id
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (F G : TranslationFunctorData Δ rd wg)
    (hG_lam : G.lam = F.mu) (hG_mu : G.mu = F.lam)
    (hG_V_dual : IsContragredientLieModule (R := R) (𝔤 := 𝔤) F.V G.V)
    (hW : WeylStabilizerModQ rd wg F.lam = WeylStabilizerModQ rd wg F.mu)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM_ic : HasInfinitesimalCharacter (R := R) (𝔤 := 𝔤) M (evalHC Δ wg F.lam)) :
    let FM := F.applyToModule Δ rd wg M
    let GFM := G.applyToModule Δ rd wg FM.carrier
    Nonempty (GFM.carrier ≃ₗ⁅R, 𝔤⁆ M) := by
  intro FM GFM


  obtain ⟨M_lam, instACG, instMod, instLRM, instLM, ⟨hVerma_data⟩⟩ :=
    @exists_verma_module.{_, _, 0} R _ 𝔤 _ _ Δ (F.lam - wg.ρ)


  exact projective_functor_determination_on_block Δ rd wg F G
    hG_lam hG_mu hG_V_dual hW M_lam hVerma_data
    (composition_fixes_verma Δ rd wg F G hG_lam hG_mu hW M_lam hVerma_data) M hM_ic

theorem TranslationFunctor.equivalence
    (F : TranslationFunctorData Δ rd wg)
    (hW : WeylStabilizerModQ rd wg F.lam = WeylStabilizerModQ rd wg F.mu)

    (G : TranslationFunctorData Δ rd wg)
    (hG_lam : G.lam = F.mu) (hG_mu : G.mu = F.lam)

    (hG_V_dual : IsContragredientLieModule (R := R) (𝔤 := 𝔤) F.V G.V) :

    (∀ (M_lam : Type*) [AddCommGroup M_lam] [Module R M_lam]
       [LieRingModule 𝔤 M_lam] [LieModule R 𝔤 M_lam],
       IsVermaModule Δ M_lam (F.lam - wg.ρ) →
       Nonempty (IsVermaModule Δ (F.applyToModule Δ rd wg M_lam).carrier (F.mu - wg.ρ)))
    ∧

    (∀ (M_mu : Type*) [AddCommGroup M_mu] [Module R M_mu]
       [LieRingModule 𝔤 M_mu] [LieModule R 𝔤 M_mu],
       IsVermaModule Δ M_mu (F.mu - wg.ρ) →
       Nonempty (IsVermaModule Δ (G.applyToModule Δ rd wg M_mu).carrier (F.lam - wg.ρ)))
    ∧


    (∀ (M : Type*) [AddCommGroup M] [Module R M]
       [LieRingModule 𝔤 M] [LieModule R 𝔤 M],
       HasInfinitesimalCharacter (R := R) (𝔤 := 𝔤) M (evalHC Δ wg F.lam) →
       let FM := F.applyToModule Δ rd wg M
       let GFM := G.applyToModule Δ rd wg FM.carrier
       Nonempty (GFM.carrier ≃ₗ⁅R, 𝔤⁆ M))
    ∧


    (∀ (N : Type*) [AddCommGroup N] [Module R N]
       [LieRingModule 𝔤 N] [LieModule R 𝔤 N],
       HasInfinitesimalCharacter (R := R) (𝔤 := 𝔤) N (evalHC Δ wg F.mu) →
       let GN := G.applyToModule Δ rd wg N
       let FGN := F.applyToModule Δ rd wg GN.carrier
       Nonempty (FGN.carrier ≃ₗ⁅R, 𝔤⁆ N)) := by
  refine ⟨fun M_lam _ _ _ _ hM => ?_, fun M_mu _ _ _ _ hM => ?_,
          fun M _ _ _ _ hM_ic => ?_, fun N _ _ _ _ hN_ic => ?_⟩

  · exact TranslationFunctor.verma_maps_to_verma Δ rd wg F M_lam hM hW.le

  · have hW' : WeylStabilizerModQ rd wg G.lam ⊆ WeylStabilizerModQ rd wg G.mu := by
      rw [hG_lam, hG_mu]
      exact hW.symm.le
    rw [← hG_mu]
    exact TranslationFunctor.verma_maps_to_verma Δ rd wg G M_mu
      (by rw [hG_lam]; exact hM) hW'


  · exact translation_functor_composition_iso_id Δ rd wg F G hG_lam hG_mu
      hG_V_dual hW M hM_ic


  · have hW_sym : WeylStabilizerModQ rd wg G.lam = WeylStabilizerModQ rd wg G.mu := by
      rw [hG_lam, hG_mu]
      exact hW.symm
    have hN_ic : HasInfinitesimalCharacter (R := R) (𝔤 := 𝔤) N (evalHC Δ wg G.lam) := by
      rw [hG_lam]
      exact hN_ic
    exact translation_functor_composition_iso_id Δ rd wg G F hG_mu.symm hG_lam.symm
      (IsContragredientLieModule.symm hG_V_dual) hW_sym N hN_ic

theorem charEigenspace_isCategoryO_ax

    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M)
    (act : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R)
    (hcompat : ∀ (x : 𝔤) (m : M),
      act (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆) :
    IsCategoryO Δ rd ↥(charEigenspaceLie act χ hcompat) := by sorry

theorem TranslationFunctor.preserves_categoryO
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (F : TranslationFunctorData Δ rd wg)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M) :

    let result := F.applyToModule Δ rd wg M
    IsCategoryO Δ rd result.carrier := by

  have hVM : IsCategoryO Δ rd (F.V ⊗[R] M) := tensorProduct_isCategoryO_aux hM

  exact charEigenspace_isCategoryO_ax hVM _ _ _

theorem tensor_finiteDim_free_nminus
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {V : Type*} [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V]
    {X : Type*} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXfree : IsFreeOverNMinus (Δ := Δ) X) :
    IsFreeOverNMinus (Δ := Δ) (V ⊗[R] X) := by sorry

theorem translation_functor_standard_filtration

    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (F : TranslationFunctorData Δ rd wg)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M)
    (hFM : IsCategoryO Δ rd (F.applyToModule Δ rd wg M).carrier) :
    HasStandardFiltration rd (F.applyToModule Δ rd wg M).carrier hFM := by sorry

def TwoSidedIdeal.toSubmoduleR {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (J : TwoSidedIdeal A) : Submodule R A where
  carrier := (J : Set A)
  add_mem' ha hb := J.add_mem ha hb
  zero_mem' := J.zero_mem
  smul_mem' r a ha := by rw [Algebra.smul_def]; exact J.mul_mem_left _ _ ha

noncomputable def idealToSubmoduleEvalAtV {R A M : Type*} [CommRing R] [Ring A] [Algebra R A]
    [AddCommGroup M] [Module R M] (act : A →ₐ[R] Module.End R M) (v : M) : A →ₗ[R] M where
  toFun u := act u v
  map_add' x y := by simp [map_add, LinearMap.add_apply]
  map_smul' r x := by
    simp only [RingHom.id_apply]
    show act (r • x) v = r • (act x v)
    rw [Algebra.smul_def, map_mul]
    simp [AlgHom.commutes]

theorem idealToSubmoduleMap_order_reflecting
    {R : Type*} [CommRing R]
    {A : Type*} [Ring A] [Algebra R A]
    (M : Type*) [AddCommGroup M] [Module R M]
    (act : A →ₐ[R] Module.End R M)
    (v : M)
    (I J : TwoSidedIdeal A)
    (hinj : Function.Injective (fun u => act u v))
    (hsurj : Function.Surjective (fun u => act u v))
    (hle : Submodule.span R {m : M | ∃ j ∈ I, ∃ x : M, m = act j x} ≤
           Submodule.span R {m : M | ∃ j ∈ J, ∃ x : M, m = act j x}) :
    I ≤ J := by
  intro a ha

  have key : act a v ∈ Submodule.span R {m : M | ∃ j ∈ J, ∃ x : M, m = act j x} :=
    hle (Submodule.subset_span ⟨a, ha, v, rfl⟩)

  let ev := idealToSubmoduleEvalAtV act v
  have gen_sub : {m : M | ∃ j ∈ J, ∃ x : M, m = act j x} ⊆
      ↑(Submodule.map ev J.toSubmoduleR) := by
    intro m ⟨j', hj', x, hx⟩
    obtain ⟨u, hu⟩ := hsurj x
    show m ∈ Submodule.map ev J.toSubmoduleR
    rw [Submodule.mem_map]
    refine ⟨j' * u, J.mul_mem_right j' u hj', ?_⟩

    change act (j' * u) v = m
    rw [hx, ← hu, map_mul]
    rfl

  have key2 : act a v ∈ Submodule.map ev J.toSubmoduleR :=
    Submodule.span_le.mpr gen_sub key
  rw [Submodule.mem_map] at key2
  obtain ⟨b, hbJ, hbv⟩ := key2

  have hbv' : act b v = act a v := by exact_mod_cast hbv
  have : a = b := hinj hbv'.symm
  rw [this]; exact hbJ

theorem pbw_verma_hwv_annihilator_in_central_ideal_aux
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hM : IsVermaModule Δ M wt)
    (u : UniversalEnvelopingAlgebra R 𝔤)
    (hu : (ueaActionFromLieModule M) u hM.highestWeightVec = 0) :
    MaximalQuotient.proj (evalHC Δ wg (wt + wg.ρ)) u = 0 := by sorry

theorem smul_left_injective_of_pbw_verma
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hM : IsVermaModule Δ M wt)
    (r₁ r₂ : R)
    (h : r₁ • hM.highestWeightVec = r₂ • hM.highestWeightVec) :
    r₁ = r₂ := by sorry

theorem verma_hwv_annihilator_in_central_ideal
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hM : IsVermaModule Δ M wt)
    (χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R)
    (hic : HasInfinitesimalCharacter M χ)
    (u : UniversalEnvelopingAlgebra R 𝔤)
    (hu : hic.ueaAction u hM.highestWeightVec = 0) :
    MaximalQuotient.proj χ u = 0 := by

  have hact_eq : ∀ (v : UniversalEnvelopingAlgebra R 𝔤) (m : M),
      hic.ueaAction v m = (ueaActionFromLieModule M) v m := by
    have heq : hic.ueaAction = ueaActionFromLieModule M := by
      apply UniversalEnvelopingAlgebra.hom_ext R
      ext x

      simp only [AlgHom.toLieHom_apply, LieHom.comp_apply]
      rw [hic.compat x, ueaActionFromLieModule_compat M x]
    intro v m; rw [heq]


  have hu' : (ueaActionFromLieModule M) u hM.highestWeightVec = 0 := by
    rw [← hact_eq]; exact hu

  let χ_verma := evalHC Δ wg (wt + wg.ρ)
  let hic_verma := vermaHasInfinitesimalCharacter Δ wg M wt hM

  have h_proj_verma : MaximalQuotient.proj χ_verma u = 0 :=
    pbw_verma_hwv_annihilator_in_central_ideal_aux Δ wg M wt hM u hu'

  have hχ_eq : ∀ z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤),
      χ z = χ_verma z := by
    intro z
    have h1 : hic.ueaAction (z : UniversalEnvelopingAlgebra R 𝔤) hM.highestWeightVec =
        χ z • hM.highestWeightVec :=
      hic.center_acts_by_scalar z hM.highestWeightVec
    have h2 : (ueaActionFromLieModule M) (z : UniversalEnvelopingAlgebra R 𝔤) hM.highestWeightVec =
        χ_verma z • hM.highestWeightVec :=
      hic_verma.center_acts_by_scalar z hM.highestWeightVec
    rw [hact_eq] at h1
    have h3 : χ z • hM.highestWeightVec = χ_verma z • hM.highestWeightVec := by
      rw [← h1, ← h2]
    exact smul_left_injective_of_pbw_verma Δ M wt hM (χ z) (χ_verma z) h3

  have hI_eq : maximalQuotientIdeal χ = maximalQuotientIdeal χ_verma := by
    unfold maximalQuotientIdeal
    congr 1
    ext x; constructor
    · rintro ⟨z, rfl⟩; exact ⟨z, by rw [hχ_eq z]⟩
    · rintro ⟨z, rfl⟩; exact ⟨z, by rw [hχ_eq z]⟩


  show (maximalQuotientIdeal χ).ringCon.mk' u = 0
  rw [hI_eq]
  exact h_proj_verma


theorem verma_eval_injective
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hM : IsVermaModule Δ M wt)
    (χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R)
    (hic : HasInfinitesimalCharacter M χ)
    (act : MaximalQuotient χ →ₐ[R] Module.End R M)
    (hcompat : ∀ (u : UniversalEnvelopingAlgebra R 𝔤) (m : M),
      hic.ueaAction u m = act (MaximalQuotient.proj χ u) m) :
    Function.Injective (fun u => act u hM.highestWeightVec) := by

  intro q₁ q₂ heq

  have hsurj : Function.Surjective (MaximalQuotient.proj χ) :=
    RingCon.mk'_surjective _
  obtain ⟨u₁, hu₁⟩ := hsurj q₁
  obtain ⟨u₂, hu₂⟩ := hsurj q₂

  have h1 : hic.ueaAction u₁ hM.highestWeightVec = (act q₁) hM.highestWeightVec := by
    rw [hcompat u₁ hM.highestWeightVec, hu₁]
  have h2 : hic.ueaAction u₂ hM.highestWeightVec = (act q₂) hM.highestWeightVec := by
    rw [hcompat u₂ hM.highestWeightVec, hu₂]

  have heq' : (act q₁) hM.highestWeightVec = (act q₂) hM.highestWeightVec := heq
  have hdiff : hic.ueaAction (u₁ - u₂) hM.highestWeightVec = 0 := by
    simp only [map_sub, LinearMap.sub_apply]
    rw [h1, h2, heq', sub_self]

  have hproj := verma_hwv_annihilator_in_central_ideal Δ wg wt hM χ hic (u₁ - u₂) hdiff

  rw [map_sub] at hproj
  rw [← hu₁, ← hu₂]
  exact sub_eq_zero.mp hproj


theorem verma_eval_surjective
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hM : IsVermaModule Δ M wt)
    (χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R)
    (hic : HasInfinitesimalCharacter M χ)
    (act : MaximalQuotient χ →ₐ[R] Module.End R M)
    (hcompat : ∀ (u : UniversalEnvelopingAlgebra R 𝔤) (m : M),
      hic.ueaAction u m = act (MaximalQuotient.proj χ u) m) :
    Function.Surjective (fun u => act u hM.highestWeightVec) := by

  intro m

  set S : Set M := {m : M | ∃ q : MaximalQuotient χ,
    (act q) hM.highestWeightVec = m} with hS_def

  have hS_add : ∀ a b : M, a ∈ S → b ∈ S → a + b ∈ S := by
    rintro a b ⟨q₁, rfl⟩ ⟨q₂, rfl⟩
    exact ⟨q₁ + q₂, by simp [map_add, LinearMap.add_apply]⟩

  have hS_zero : (0 : M) ∈ S := ⟨0, by simp [map_zero, LinearMap.zero_apply]⟩

  have hS_smul : ∀ (r : R) (a : M), a ∈ S → r • a ∈ S := by
    rintro r _ ⟨q, rfl⟩
    exact ⟨r • q, by simp [map_smul, LinearMap.smul_apply]⟩

  have hS_lie : ∀ (x : 𝔤) (a : M), a ∈ S → ⁅x, a⁆ ∈ S := by
    rintro x _ ⟨q, rfl⟩

    rw [← hic.compat x ((act q) hM.highestWeightVec)]

    rw [hcompat (UniversalEnvelopingAlgebra.ι R x) ((act q) hM.highestWeightVec)]

    have : (act (MaximalQuotient.proj χ (UniversalEnvelopingAlgebra.ι R x)))
        ((act q) hM.highestWeightVec) =
      (act (MaximalQuotient.proj χ (UniversalEnvelopingAlgebra.ι R x) * q))
        hM.highestWeightVec := by
      rw [map_mul]; rfl
    rw [this]
    exact ⟨MaximalQuotient.proj χ (UniversalEnvelopingAlgebra.ι R x) * q, rfl⟩

  set N : LieSubmodule R 𝔤 M := {
    carrier := S
    add_mem' := fun ha hb => hS_add _ _ ha hb
    zero_mem' := hS_zero
    smul_mem' := fun r _ hx => hS_smul r _ hx
    lie_mem := fun {x a} ha => hS_lie x a ha
  } with hN_def

  have hvlam : hM.highestWeightVec ∈ N :=
    ⟨1, by simp [map_one]⟩

  have htop : N = ⊤ := by
    rw [eq_top_iff, ← hM.generates]
    exact LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr hvlam)

  have hm : m ∈ N := htop ▸ trivial
  exact hm

theorem idealToSubmoduleMap_order_properties
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (hlam : IsDominantWeightLE rd wg lam)
    (hmu : evalHC Δ wg mu = evalHC Δ wg lam)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsVermaModule Δ M (mu - wg.ρ)) :
    ∃ (ν : TwoSidedIdeal (MaximalQuotient (evalHC Δ wg lam)) →o Submodule R M),
      ν ⊥ = ⊥ ∧ ν ⊤ = ⊤ ∧
      (∀ I J, ν I ≤ ν J → I ≤ J) := by


  have hic_mu := vermaHasInfinitesimalCharacter Δ wg M (mu - wg.ρ) hM

  have hic : HasInfinitesimalCharacter (R := R) (𝔤 := 𝔤) M (evalHC Δ wg lam) := by
    have key : mu - wg.ρ + wg.ρ = mu := sub_add_cancel mu wg.ρ
    rw [key] at hic_mu
    exact hmu ▸ hic_mu

  obtain ⟨act, hact⟩ := MaximalQuotient.factors_through (evalHC Δ wg lam) M hic


  let ν_fun : TwoSidedIdeal (MaximalQuotient (evalHC Δ wg lam)) → Submodule R M :=
    fun J => Submodule.span R {m : M | ∃ j ∈ J, ∃ x : M, m = act j x}

  have ν_mono : Monotone ν_fun := by
    intro I J hIJ
    apply Submodule.span_mono
    intro m ⟨j, hj, x, hx⟩
    exact ⟨j, hIJ hj, x, hx⟩
  let ν : TwoSidedIdeal (MaximalQuotient (evalHC Δ wg lam)) →o Submodule R M :=
    ⟨ν_fun, ν_mono⟩
  refine ⟨ν, ?_, ?_, ?_⟩
  ·
    apply le_antisymm
    · apply Submodule.span_le.mpr
      intro m ⟨j, hj, x, hx⟩
      have hj0 : j = 0 := (TwoSidedIdeal.mem_bot _).mp hj
      simp only [SetLike.mem_coe, Submodule.mem_bot]
      rw [hx, hj0, map_zero, LinearMap.zero_apply]
    · exact bot_le
  ·
    apply le_antisymm le_top
    intro m _
    apply Submodule.subset_span
    exact ⟨1, TwoSidedIdeal.mem_top (R := MaximalQuotient (evalHC Δ wg lam)),
           m, by simp [map_one]⟩
  ·

    intro I J hle
    have hinj := verma_eval_injective Δ wg (mu - wg.ρ) hM
        (evalHC Δ wg lam) hic act hact
    have hsurj := verma_eval_surjective Δ wg (mu - wg.ρ) hM
        (evalHC Δ wg lam) hic act hact
    exact idealToSubmoduleMap_order_reflecting M act hM.highestWeightVec I J hinj hsurj hle

theorem idealToSubmoduleMap_reflects_order_general
    (lam mu : 𝔥*)
    (hlam : IsDominantWeightLE rd wg lam)
    (hmu : evalHC Δ wg mu = evalHC Δ wg lam)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsVermaModule Δ M (mu - wg.ρ)) :
    ∃ (ν : TwoSidedIdeal (MaximalQuotient (evalHC Δ wg lam)) →o Submodule R M),
      ν ⊥ = ⊥ ∧ ν ⊤ = ⊤ ∧
      (∀ I J, ν I ≤ ν J → I ≤ J) :=
  idealToSubmoduleMap_order_properties Δ rd wg lam mu hlam hmu M hM

def idealToSubmoduleMap
    (lam : 𝔥*)
    (hlam : IsDominantWeightLE rd wg lam)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsVermaModule Δ M (lam - wg.ρ)) :
    TwoSidedIdeal (MaximalQuotient (evalHC Δ wg lam)) →o Submodule R M :=
  (idealToSubmoduleMap_reflects_order_general Δ rd wg lam lam hlam rfl M hM).choose

lemma idealToSubmoduleMap_properties
    (lam : 𝔥*)
    (hlam : IsDominantWeightLE rd wg lam)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsVermaModule Δ M (lam - wg.ρ)) :
    let ν := idealToSubmoduleMap Δ rd wg lam hlam M hM
    ν ⊥ = ⊥ ∧ ν ⊤ = ⊤ ∧
    (∀ I J, ν I ≤ ν J → I ≤ J) :=
  (idealToSubmoduleMap_reflects_order_general Δ rd wg lam lam hlam rfl M hM).choose_spec

theorem ideals_submodules_image_characterization_forward

    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (hlam : IsDominantWeightLE rd wg lam)
    (M : Type uM) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsVermaModule Δ M (lam - wg.ρ)) :
    let ν := idealToSubmoduleMap Δ rd wg lam hlam M hM
    (∀ (J : TwoSidedIdeal (MaximalQuotient (evalHC Δ wg lam))),
      ∃ (I : Type uM) (mu : I → Δ.𝔥 →ₗ[R] R),
        (∀ i, evalHC Δ wg (mu i) = evalHC Δ wg lam) ∧
        (∀ i, BruhatLE rd (mu i) lam) ∧
        (∀ i, ∀ w : wg.W, wg.dualAction w lam = lam →
          BruhatLE rd (mu i) (wg.dualAction w (mu i))) ∧
        ∃ (P : Type uM) (_ : AddCommGroup P) (_ : Module R P)
          (_ : LieRingModule 𝔤 P) (_ : LieModule R 𝔤 P),
          ∃ (hPO : IsCategoryO Δ rd P), IsProjectiveInO rd P hPO ∧
          Nonempty (P →ₗ⁅R, 𝔤⁆ M)) := by sorry

theorem projective_image_in_nu_range

    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (hlam : IsDominantWeightLE rd wg lam)
    (M : Type uM) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsVermaModule Δ M (lam - wg.ρ))
    (N : Submodule R M)
    (hN : ∃ (I : Type uM) (mu : I → Δ.𝔥 →ₗ[R] R),
      (∀ i, evalHC Δ wg (mu i) = evalHC Δ wg lam) ∧
      (∀ i, BruhatLE rd (mu i) lam) ∧
      (∀ i, ∀ w : wg.W, wg.dualAction w lam = lam →
        BruhatLE rd (mu i) (wg.dualAction w (mu i))) ∧
      ∃ (P : Type uM) (_ : AddCommGroup P) (_ : Module R P)
        (_ : LieRingModule 𝔤 P) (_ : LieModule R 𝔤 P),
        ∃ (hPO : IsCategoryO Δ rd P), IsProjectiveInO rd P hPO ∧
        Nonempty (P →ₗ⁅R, 𝔤⁆ M)) :
    ∃ (J : TwoSidedIdeal (MaximalQuotient (evalHC Δ wg lam))),
      idealToSubmoduleMap Δ rd wg lam hlam M hM J = N := by sorry

theorem ideals_submodules_image_backward_ax
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (hlam : IsDominantWeightLE rd wg lam)
    (M : Type uM) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsVermaModule Δ M (lam - wg.ρ)) :
    let ν := idealToSubmoduleMap Δ rd wg lam hlam M hM
    (∀ (N : Submodule R M),
      (∃ (I : Type uM) (mu : I → Δ.𝔥 →ₗ[R] R),
        (∀ i, evalHC Δ wg (mu i) = evalHC Δ wg lam) ∧
        (∀ i, BruhatLE rd (mu i) lam) ∧
        (∀ i, ∀ w : wg.W, wg.dualAction w lam = lam →
          BruhatLE rd (mu i) (wg.dualAction w (mu i))) ∧
        ∃ (P : Type uM) (_ : AddCommGroup P) (_ : Module R P)
          (_ : LieRingModule 𝔤 P) (_ : LieModule R 𝔤 P),
          ∃ (hPO : IsCategoryO Δ rd P), IsProjectiveInO rd P hPO ∧
          Nonempty (P →ₗ⁅R, 𝔤⁆ M)) →
      ∃ (J : TwoSidedIdeal (MaximalQuotient (evalHC Δ wg lam))),
        ν J = N) := by
  intro ν N hN
  exact projective_image_in_nu_range Δ rd wg lam hlam M hM N hN

theorem ideals_submodules_lattice_iso
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (hlam : IsDominantWeightLE rd wg lam)
    (hregular : ∀ w : wg.W, wg.dualAction w lam = lam → w = 1)
    (M : Type uM) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsVermaModule Δ M (lam - wg.ρ)) :


    Nonempty (TwoSidedIdeal (MaximalQuotient (evalHC Δ wg lam)) ≃o LieSubmodule R 𝔤 M) := by sorry

theorem idealToSubmoduleMap_image_isLieSubmodule
    (lam : 𝔥*)
    (hlam : IsDominantWeightLE rd wg lam)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsVermaModule Δ M (lam - wg.ρ))
    (ν : TwoSidedIdeal (MaximalQuotient (evalHC Δ wg lam)) →o Submodule R M)
    (hνbot : ν ⊥ = ⊥) (hνtop : ν ⊤ = ⊤)
    (hνrefl : ∀ I J, ν I ≤ ν J → I ≤ J)
    (hνlie : ∀ I : TwoSidedIdeal (MaximalQuotient (evalHC Δ wg lam)),
      ∀ (x : 𝔤) (m : M), m ∈ ν I → ⁅x, m⁆ ∈ ν I)
    (I : TwoSidedIdeal (MaximalQuotient (evalHC Δ wg lam))) :
    ∃ (N : LieSubmodule R 𝔤 M), (N : Submodule R M) = ν I :=
  ⟨{ toSubmodule := ν I, lie_mem := fun {x m} hm => hνlie I x m hm }, rfl⟩

theorem lie_closure_of_ideal_action
    (lam : 𝔥*)
    (hlam : IsDominantWeightLE rd wg lam)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsVermaModule Δ M (lam - wg.ρ))
    (ν : TwoSidedIdeal (MaximalQuotient (evalHC Δ wg lam)) →o Submodule R M)
    (hνbot : ν ⊥ = ⊥) (hνtop : ν ⊤ = ⊤)
    (hνrefl : ∀ I J, ν I ≤ ν J → I ≤ J) :
    ∀ I : TwoSidedIdeal (MaximalQuotient (evalHC Δ wg lam)),
      ∀ (x : 𝔤) (m : M), m ∈ ν I → ⁅x, m⁆ ∈ ν I := by
  sorry


theorem dufloJoseph_proper_ideal_contradicts_simple
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (hlam : IsDominantWeightLE rd wg lam)
    (hmu : evalHC Δ wg mu = evalHC Δ wg lam)
    (hSimple : IsSimpleRing (MaximalQuotient (evalHC Δ wg lam)))
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hVM : IsVermaModule Δ M (mu - wg.ρ))
    (h_not_irr : ¬ LieModule.IsIrreducible R 𝔤 M) :
    False := by
  sorry


theorem simple_algebra_if_irreducible_verma
    (lam : 𝔥*)
    (hlam : IsDominantWeightLE rd wg lam)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsVermaModule Δ M (lam - wg.ρ))
    (hirr : LieModule.IsIrreducible R 𝔤 M) :

    IsSimpleRing (MaximalQuotient (evalHC Δ wg lam)) := by

  haveI := hirr

  obtain ⟨ν, hνbot, hνtop, hνrefl⟩ :=
    idealToSubmoduleMap_reflects_order_general Δ rd wg lam lam hlam rfl M hM

  haveI hnt : Nontrivial M := LieModule.nontrivial_of_isIrreducible R 𝔤 M
  have hne_ideal : (⊥ : TwoSidedIdeal (MaximalQuotient (evalHC Δ wg lam))) ≠ ⊤ := by
    intro h
    have hsub : (⊥ : Submodule R M) = ⊤ := by
      rw [← hνbot, ← hνtop]
      exact congrArg ν h
    exact not_subsingleton M ((Submodule.subsingleton_iff R).mp
      (subsingleton_of_bot_eq_top hsub))
  haveI : Nontrivial (MaximalQuotient (evalHC Δ wg lam)) := by
    by_contra h'
    rw [not_nontrivial_iff_subsingleton] at h'
    apply hne_ideal
    haveI := h'
    ext x
    constructor
    · intro _; trivial
    · intro _
      have : x = 0 := Subsingleton.elim x 0
      rw [this]; exact TwoSidedIdeal.zero_mem _

  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro I

  have hνlie : ∀ J : TwoSidedIdeal (MaximalQuotient (evalHC Δ wg lam)),
      ∀ (x : 𝔤) (m : M), m ∈ ν J → ⁅x, m⁆ ∈ ν J :=
    lie_closure_of_ideal_action Δ rd wg lam hlam M hM ν hνbot hνtop hνrefl
  obtain ⟨N, hN⟩ := idealToSubmoduleMap_image_isLieSubmodule Δ rd wg lam hlam M hM
    ν hνbot hνtop hνrefl hνlie I


  rcases hirr.eq_bot_or_eq_top N with hbot | htop

  · left
    apply le_antisymm
    · apply hνrefl

      have hNbot : (N : Submodule R M) = ⊥ := by
        simp only [hbot, LieSubmodule.bot_toSubmodule]
      exact (hN.symm.trans (hNbot.trans hνbot.symm)).le
    · exact bot_le

  · right
    apply le_antisymm
    · exact le_top
    · apply hνrefl

      have hNtop : (N : Submodule R M) = ⊤ := by
        simp only [htop, LieSubmodule.top_toSubmodule]
      exact (hνtop.trans (hNtop.symm.trans hN)).le

end
