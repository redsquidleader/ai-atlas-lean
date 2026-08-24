/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Irreducible

noncomputable section

structure SmoothVarietyWithGroupAction where
  X : Type*
  K : Type*
  [grpK : Group K]
  [topK : TopologicalSpace K]
  [connK : ConnectedSpace K]
  [actKX : MulAction K X]
  DX : Type*
  [ringDX : Ring DX]
  [algebraDX : Algebra ℂ DX]
  [actKDX : MulAction K DX]
  orbits : Set (Set X)
  orbit_is_orbit : ∀ O ∈ orbits, O.Nonempty ∧ (∀ x ∈ O, ∀ k : K, k • x ∈ O)
  orbits_cover : ∀ x : X, ∃ O ∈ orbits, x ∈ O
  orbits_disjoint : ∀ O₁ ∈ orbits, ∀ O₂ ∈ orbits, O₁ ≠ O₂ → Disjoint O₁ O₂
  orbits_finite : orbits.Finite

attribute [instance] SmoothVarietyWithGroupAction.grpK
attribute [instance] SmoothVarietyWithGroupAction.topK
attribute [instance] SmoothVarietyWithGroupAction.connK
attribute [instance] SmoothVarietyWithGroupAction.actKX
attribute [instance] SmoothVarietyWithGroupAction.ringDX
attribute [instance] SmoothVarietyWithGroupAction.algebraDX
attribute [instance] SmoothVarietyWithGroupAction.actKDX

def SmoothVarietyWithGroupAction.stabilizer (S : SmoothVarietyWithGroupAction)
    (x : S.X) : Subgroup S.K :=
  MulAction.stabilizer S.K x

structure OrbitRepPair (S : SmoothVarietyWithGroupAction) where
  orbit : Set S.X
  orbit_mem : orbit ∈ S.orbits
  basepoint : S.X
  basepoint_mem : basepoint ∈ orbit
  ComponentGroup : Type*
  [compGrpGroup : Group ComponentGroup]
  quotientMap : (MulAction.stabilizer S.K basepoint) →* ComponentGroup
  quotientMap_surjective : Function.Surjective quotientMap
  V : Type*
  [addCommGroupV : AddCommGroup V]
  [moduleV : Module ℂ V]
  compGroupRep : Representation ℂ ComponentGroup V
  V_irreducible : compGroupRep.IsIrreducible

attribute [instance] OrbitRepPair.addCommGroupV
attribute [instance] OrbitRepPair.moduleV
attribute [instance] OrbitRepPair.compGrpGroup

structure IrredKEquivDModule (S : SmoothVarietyWithGroupAction) where
  carrier : Type*
  [addCommGroup : AddCommGroup carrier]
  [moduleC : Module ℂ carrier]
  [moduleDX : Module S.DX carrier]
  [mulActionK : MulAction S.K carrier]
  equivariance : ∀ (k : S.K) (d : S.DX) (m : carrier),
    k • (d • m) = (k • d) • (k • m)
  isIrreducible : IsSimpleModule S.DX carrier

attribute [instance] IrredKEquivDModule.addCommGroup
attribute [instance] IrredKEquivDModule.moduleC
attribute [instance] IrredKEquivDModule.moduleDX
attribute [instance] IrredKEquivDModule.mulActionK

def IrredKEquivDModule.IsIsomorphic (S : SmoothVarietyWithGroupAction)
    (M N : IrredKEquivDModule S) : Prop :=
  Nonempty (M.carrier ≃ₗ[S.DX] N.carrier)

theorem kashiwarasTheorem (S : SmoothVarietyWithGroupAction)
    (M : IrredKEquivDModule S) (O : Set S.X) (hO : O ∈ S.orbits) :
    ∃ (restrict : IrredKEquivDModule S → IrredKEquivDModule S)
      (extend : IrredKEquivDModule S → IrredKEquivDModule S),
      (∀ N : IrredKEquivDModule S,
        IrredKEquivDModule.IsIsomorphic S (extend (restrict N)) N) ∧
      (∀ L : IrredKEquivDModule S,
        IrredKEquivDModule.IsIsomorphic S (restrict (extend L)) L) := by sorry

noncomputable def associatedBundleDModule (S : SmoothVarietyWithGroupAction)
    (O : Set S.X) (hO : O ∈ S.orbits) (x : S.X) (hx : x ∈ O)
    (ComponentGroup : Type*) [Group ComponentGroup]
    (quotientMap : (MulAction.stabilizer S.K x) →* ComponentGroup)
    (hSurj : Function.Surjective quotientMap)
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    (compGroupRep : Representation ℂ ComponentGroup V)
    (hIrred : compGroupRep.IsIrreducible) :
    IrredKEquivDModule S := by sorry

abbrev associated_bundle_dmodule := @associatedBundleDModule

abbrev kashiwaras_theorem := @kashiwarasTheorem

theorem associatedBundleDModule_support_orbit (S : SmoothVarietyWithGroupAction)
    (p : OrbitRepPair S) :
    ∀ (inSupport : Set S.X → Prop),
      inSupport p.orbit →
      (∀ O ∈ S.orbits, inSupport O → O = p.orbit) := by sorry

theorem associatedBundleDModule_injective (S : SmoothVarietyWithGroupAction)
    (p₁ p₂ : OrbitRepPair S)
    (h : associatedBundleDModule S p₁.orbit p₁.orbit_mem p₁.basepoint p₁.basepoint_mem
        p₁.ComponentGroup p₁.quotientMap p₁.quotientMap_surjective
        p₁.V p₁.compGroupRep p₁.V_irreducible =
      associatedBundleDModule S p₂.orbit p₂.orbit_mem p₂.basepoint p₂.basepoint_mem
        p₂.ComponentGroup p₂.quotientMap p₂.quotientMap_surjective
        p₂.V p₂.compGroupRep p₂.V_irreducible) :
    p₁ = p₂ := by sorry

theorem associatedBundleDModule_surjective (S : SmoothVarietyWithGroupAction)
    (M : IrredKEquivDModule S) :
    ∃ p : OrbitRepPair S, IrredKEquivDModule.IsIsomorphic S M
      (associatedBundleDModule S p.orbit p.orbit_mem p.basepoint p.basepoint_mem
        p.ComponentGroup p.quotientMap p.quotientMap_surjective
        p.V p.compGroupRep p.V_irreducible) := by sorry

theorem theorem_31_1 (S : SmoothVarietyWithGroupAction) :
    ∃ (param : OrbitRepPair S → IrredKEquivDModule S),
      Function.Injective param ∧
      (∀ M : IrredKEquivDModule S,
        ∃ p : OrbitRepPair S, IrredKEquivDModule.IsIsomorphic S M (param p)) := by
  refine ⟨fun p => associatedBundleDModule S p.orbit p.orbit_mem p.basepoint
    p.basepoint_mem p.ComponentGroup p.quotientMap p.quotientMap_surjective
    p.V p.compGroupRep p.V_irreducible, ?_, ?_⟩
  · intro p₁ p₂ h
    exact associatedBundleDModule_injective S p₁ p₂ h

  · exact associatedBundleDModule_surjective S

structure HarishChandraData where
  G : Type*
  [grpG : Group G]
  K : Type*
  [grpK : Group K]
  𝔤 : Type*
  [lieRing𝔤 : LieRing 𝔤]
  [lieAlgebra𝔤 : LieAlgebra ℂ 𝔤]
  𝓕 : Type*
  [actK𝓕 : MulAction K 𝓕]
  W : Type*
  [grpW : Group W]
  [fintypeW : Fintype W]
  Z_Ug : Type*
  [commRingZ : CommRing Z_Ug]
  [algebraZ : Algebra ℂ Z_Ug]
  [dotActionW : MulAction W (Z_Ug →ₐ[ℂ] ℂ)]
  antidominance_pred : (Z_Ug →ₐ[ℂ] ℂ) → Prop

attribute [instance] HarishChandraData.grpG
attribute [instance] HarishChandraData.grpK
attribute [instance] HarishChandraData.lieRing𝔤
attribute [instance] HarishChandraData.lieAlgebra𝔤
attribute [instance] HarishChandraData.actK𝓕
attribute [instance] HarishChandraData.grpW
attribute [instance] HarishChandraData.fintypeW
attribute [instance] HarishChandraData.commRingZ
attribute [instance] HarishChandraData.algebraZ
attribute [instance] HarishChandraData.dotActionW

def HarishChandraData.IsRegularChar (D : HarishChandraData) (χ : D.Z_Ug →ₐ[ℂ] ℂ) : Prop :=
  ∀ w : D.W, w • χ = χ → w = 1

class HarishChandraData.IsAntidominantChar (D : HarishChandraData)
    (χ : D.Z_Ug →ₐ[ℂ] ℂ) : Prop where
  antidominant_rep_exists : D.antidominance_pred χ

theorem prop_31_3 (D : HarishChandraData) :
    Finite (MulAction.orbitRel.Quotient D.K D.𝓕) := by sorry

structure HCGKModule (D : HarishChandraData) where
  carrier : Type*
  [addCommGroup : AddCommGroup carrier]
  [module : Module ℂ carrier]
  [lieRingModule : LieRingModule D.𝔤 carrier]
  [lieModule : LieModule ℂ D.𝔤 carrier]
  [mulAction : MulAction D.K carrier]
  χ : D.Z_Ug →ₐ[ℂ] ℂ

attribute [instance] HCGKModule.addCommGroup
attribute [instance] HCGKModule.module
attribute [instance] HCGKModule.lieRingModule
attribute [instance] HCGKModule.lieModule
attribute [instance] HCGKModule.mulAction

def HCGKModule.IsGKSubmodule {D : HarishChandraData} (M : HCGKModule D)
    (W : Submodule ℂ M.carrier) : Prop :=
  (∀ (X : D.𝔤) (m : M.carrier), m ∈ W → ⁅X, m⁆ ∈ W) ∧
  (∀ (k : D.K) (m : M.carrier), m ∈ W → k • m ∈ W)

def HCGKModule.IsIrreducible {D : HarishChandraData} (M : HCGKModule D) : Prop :=
  Nontrivial M.carrier ∧
  ∀ W : Submodule ℂ M.carrier, M.IsGKSubmodule W → W = ⊥ ∨ W = ⊤

structure HCClassifyingDatum (D : HarishChandraData) where
  basepoint : D.𝓕
  orbit : Set D.𝓕
  orbit_eq : orbit = MulAction.orbit D.K basepoint
  K_x : Subgroup D.K
  K_x_eq : K_x = MulAction.stabilizer D.K basepoint
  V : Type*
  [addCommGroupV : AddCommGroup V]
  [moduleV : Module ℂ V]
  stabRep : Representation ℂ K_x V
  V_irreducible : stabRep.IsIrreducible
  lieKx : LieSubalgebra ℂ D.𝔤
  char_lieKx : D.𝔤 →ₗ[ℂ] ℂ
  lieKx_action : lieKx →ₗ[ℂ] (V →ₗ[ℂ] V)
  char_lieKx_acts : ∀ (X : lieKx) (v : V), lieKx_action X v = char_lieKx (X : D.𝔤) • v

attribute [instance] HCClassifyingDatum.addCommGroupV
attribute [instance] HCClassifyingDatum.moduleV

theorem twistedDModuleClassification (D : HarishChandraData)
    (S : SmoothVarietyWithGroupAction)
    (hFlagVar : S.X = D.𝓕)
    (hGroupActs : S.K = D.K) :
    ∃ (M_assign : HCClassifyingDatum D → IrredKEquivDModule S),
      (∀ d₁ d₂ : HCClassifyingDatum D,
        IrredKEquivDModule.IsIsomorphic S (M_assign d₁) (M_assign d₂) → d₁ = d₂) ∧
      (∀ M : IrredKEquivDModule S,
        ∃ d, IrredKEquivDModule.IsIsomorphic S M (M_assign d)) := by sorry

theorem bbGlobalSectionsEquiv (D : HarishChandraData)
    (χ : D.Z_Ug →ₐ[ℂ] ℂ) (hχ : D.IsAntidominantChar χ)
    (S : SmoothVarietyWithGroupAction)
    (hFlagVar : S.X = D.𝓕) (hGroupActs : S.K = D.K) :
    ∃ (Γ_fun : IrredKEquivDModule S → HCGKModule D)
      (Loc_fun : HCGKModule D → IrredKEquivDModule S),

      (∀ M, (Γ_fun M).χ = χ) ∧

      (∀ M, (Γ_fun M).IsIrreducible) ∧

      (∀ V : HCGKModule D, V.χ = χ →
        Nonempty (V.carrier ≃ₗ[ℂ] (Γ_fun (Loc_fun V)).carrier)) ∧

      (∀ M : IrredKEquivDModule S,
        IrredKEquivDModule.IsIsomorphic S (Loc_fun (Γ_fun M)) M) ∧

      (∀ M₁ M₂ : IrredKEquivDModule S, Γ_fun M₁ = Γ_fun M₂ →
        IrredKEquivDModule.IsIsomorphic S M₁ M₂) ∧

      (∀ V : HCGKModule D, V.IsIrreducible → V.χ = χ →
        ∃ M : IrredKEquivDModule S, Nonempty (V.carrier ≃ₗ[ℂ] (Γ_fun M).carrier)) ∧

      (∀ M₁ M₂ : IrredKEquivDModule S,
        IrredKEquivDModule.IsIsomorphic S M₁ M₂ →
        Nonempty ((Γ_fun M₁).carrier ≃ₗ[ℂ] (Γ_fun M₂).carrier)) ∧

      (∀ M, Nonempty (M.carrier ≃ₗ[ℂ] (Γ_fun M).carrier)) := by sorry

theorem bbEquivWithDModuleRealization (D : HarishChandraData)
    (χ : D.Z_Ug →ₐ[ℂ] ℂ)
    (_hχ_reg : D.IsRegularChar χ)
    [hχ_ad : D.IsAntidominantChar χ]
    (S : SmoothVarietyWithGroupAction)
    (hFlagVar : S.X = D.𝓕)
    (hGroupActs : S.K = D.K) :
    ∃ (M_assign : HCClassifyingDatum D → IrredKEquivDModule S)
      (Γ_fun : IrredKEquivDModule S → HCGKModule D),

      (∀ d₁ d₂ : HCClassifyingDatum D,
        IrredKEquivDModule.IsIsomorphic S (M_assign d₁) (M_assign d₂) → d₁ = d₂) ∧
      (∀ M : IrredKEquivDModule S,
        ∃ d, IrredKEquivDModule.IsIsomorphic S M (M_assign d)) ∧
      (∀ M, (Γ_fun M).IsIrreducible ∧ (Γ_fun M).χ = χ) ∧
      (∀ M₁ M₂ : IrredKEquivDModule S, Γ_fun M₁ = Γ_fun M₂ →
        IrredKEquivDModule.IsIsomorphic S M₁ M₂) ∧
      (∀ V : HCGKModule D, V.IsIrreducible → V.χ = χ →
        ∃ M : IrredKEquivDModule S, Nonempty (V.carrier ≃ₗ[ℂ] (Γ_fun M).carrier)) ∧

      (∀ M₁ M₂ : IrredKEquivDModule S,
        IrredKEquivDModule.IsIsomorphic S M₁ M₂ →
        Nonempty ((Γ_fun M₁).carrier ≃ₗ[ℂ] (Γ_fun M₂).carrier)) ∧
      (∀ M, Nonempty (M.carrier ≃ₗ[ℂ] (Γ_fun M).carrier)) := by
  obtain ⟨M_assign, hM_inj, hM_surj⟩ := twistedDModuleClassification D S hFlagVar hGroupActs
  obtain ⟨Γ_fun, _, hΓ_char, hΓ_irred, _, _, hΓ_inj, hΓ_surj, hΓ_func, hΓ_carrier⟩ :=
    bbGlobalSectionsEquiv D χ hχ_ad S hFlagVar hGroupActs
  refine ⟨M_assign, Γ_fun, hM_inj, hM_surj, ?_, hΓ_inj, hΓ_surj, ?_, ?_⟩
  · intro M; exact ⟨hΓ_irred M, hΓ_char M⟩
  · exact hΓ_func
  · exact hΓ_carrier

theorem thm_31_4 (D : HarishChandraData)
    (χ : D.Z_Ug →ₐ[ℂ] ℂ)
    (hχ_reg : D.IsRegularChar χ)
    [hχ_ad : D.IsAntidominantChar χ]
    (S : SmoothVarietyWithGroupAction)
    (hFlagVar : S.X = D.𝓕)
    (hGroupActs : S.K = D.K) :


    ∃ (M_DModule : HCClassifyingDatum D → IrredKEquivDModule S)
      (π : HCClassifyingDatum D → HCGKModule D),


      (∀ d, (π d).IsIrreducible ∧ (π d).χ = χ) ∧

      Function.Injective π ∧

      (∀ M : HCGKModule D, M.IsIrreducible → M.χ = χ →

        ∃ d, Nonempty (M.carrier ≃ₗ[ℂ] (π d).carrier)) ∧

      (∀ d₁ d₂ : HCClassifyingDatum D,
        IrredKEquivDModule.IsIsomorphic S (M_DModule d₁) (M_DModule d₂) → d₁ = d₂) ∧

      (∀ d, Nonempty ((M_DModule d).carrier ≃ₗ[ℂ] (π d).carrier)) := by

  obtain ⟨M_assign, Γ_fun, hM_inj, hM_surj, hΓ_irred, hΓ_inj, hΓ_surj, hΓ_func,
    hΓ_carrier⟩ := bbEquivWithDModuleRealization D χ hχ_reg S hFlagVar hGroupActs


  refine ⟨M_assign, fun d => Γ_fun (M_assign d), ?_, ?_, ?_, ?_, ?_⟩

  · intro d; exact hΓ_irred (M_assign d)

  · intro d₁ d₂ h
    exact hM_inj d₁ d₂ (hΓ_inj (M_assign d₁) (M_assign d₂) h)

  · intro V hV_irred hV_χ
    obtain ⟨M, hM⟩ := hΓ_surj V hV_irred hV_χ
    obtain ⟨d, hd⟩ := hM_surj M
    have hfunc : Nonempty ((Γ_fun M).carrier ≃ₗ[ℂ] (Γ_fun (M_assign d)).carrier) :=
      hΓ_func M (M_assign d) hd
    exact ⟨d, hM.elim fun e => hfunc.elim fun f => ⟨e.trans f⟩⟩

  · exact hM_inj

  · intro d
    exact hΓ_carrier (M_assign d)

end
