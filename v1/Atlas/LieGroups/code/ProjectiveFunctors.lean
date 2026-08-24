/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.CategoryOII
import Atlas.LieGroups.code.DufloJoseph
import Atlas.LieGroups.code.TensorO

noncomputable section

open scoped TensorProduct

universe u

namespace ProjectiveFunctors

variable {R : Type u} [CommRing R]
variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

structure RepGfObj (R : Type u) [CommRing R] (𝔤 : Type u) [LieRing 𝔤]
    [LieAlgebra R 𝔤] where
  carrier : Type u
  inst_addCommGroup : AddCommGroup carrier
  inst_module : Module R carrier
  inst_lieRingModule : LieRingModule 𝔤 carrier
  inst_lieModule : LieModule R 𝔤 carrier

attribute [instance] RepGfObj.inst_addCommGroup RepGfObj.inst_module
  RepGfObj.inst_lieRingModule RepGfObj.inst_lieModule

opaque IsLocallyFiniteCenterAction {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (_M : RepGfObj R 𝔤) : Prop

structure RepGfHom (M N : RepGfObj R 𝔤) where
  toFun : M.carrier →ₗ⁅R, 𝔤⁆ N.carrier

def RepGfHom.comp {M N P : RepGfObj R 𝔤} (g : RepGfHom N P) (f : RepGfHom M N) :
    RepGfHom M P where
  toFun := g.toFun.comp f.toFun

def RepGfHom.id (M : RepGfObj R 𝔤) : RepGfHom M M where
  toFun := LieModuleHom.id

def RepGfHom.EqAsMap {M N : RepGfObj R 𝔤} (f g : RepGfHom M N) : Prop :=
  ∀ x : M.carrier, f.toFun x = g.toFun x

opaque centerActsNilpotentlyShifted_of_order {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (M : RepGfObj R 𝔤) (theta : Δ.𝔥 →ₗ[R] R) (n : ℕ) : Prop

theorem centerActsNilpotentlyShifted_of_order_mono
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (M : RepGfObj R 𝔤) (theta : Δ.𝔥 →ₗ[R] R) (n : ℕ) :
    centerActsNilpotentlyShifted_of_order Δ M theta n →
    centerActsNilpotentlyShifted_of_order Δ M theta (n + 1) := by sorry

theorem filtration_one_step
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R}
    (M : RepGfObj R 𝔤) (n : ℕ)
    (_hn : centerActsNilpotentlyShifted_of_order Δ M theta (n + 2)) :
    ∃ (Q : RepGfObj R 𝔤) (_ : centerActsNilpotentlyShifted_of_order Δ Q theta 1)
      (K : RepGfObj R 𝔤) (_ : centerActsNilpotentlyShifted_of_order Δ K theta (n + 1))
      (fQ : RepGfHom Q M) (fK : RepGfHom K M),
      ∀ m : M.carrier, ∃ (q : Q.carrier) (k : K.carrier),
        (fQ.toFun q : M.carrier) + (fK.toFun k : M.carrier) = m := by sorry

theorem repGfObj_directSum_data
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R}
    (N₁ N₂ : RepGfObj R 𝔤)
    (hN₁ : centerActsNilpotentlyShifted_of_order Δ N₁ theta 1)
    (hN₂ : centerActsNilpotentlyShifted_of_order Δ N₂ theta 1)
    (M : RepGfObj R 𝔤)
    (f₁ : RepGfHom N₁ M) (f₂ : RepGfHom N₂ M) :
    ∃ (N : RepGfObj R 𝔤) (_ : centerActsNilpotentlyShifted_of_order Δ N theta 1)
      (f : RepGfHom N M),
      (∀ m : M.carrier,
        (∃ (x₁ : N₁.carrier) (x₂ : N₂.carrier),
          (f₁.toFun x₁ : M.carrier) + (f₂.toFun x₂ : M.carrier) = m) →
        ∃ y : N.carrier, f.toFun y = m) := by sorry

theorem filtration_surjection_from_nilpotent_order
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R}
    (M : RepGfObj R 𝔤) (n : ℕ)
    (_hn : centerActsNilpotentlyShifted_of_order Δ M theta n) :
    ∃ (N : RepGfObj R 𝔤) (_ : centerActsNilpotentlyShifted_of_order Δ N theta 1)
      (f : RepGfHom N M), Function.Surjective f.toFun := by

  suffices h : ∀ (k : ℕ) (M' : RepGfObj R 𝔤),
      centerActsNilpotentlyShifted_of_order Δ M' theta k →
      ∃ (N : RepGfObj R 𝔤) (_ : centerActsNilpotentlyShifted_of_order Δ N theta 1)
        (f : RepGfHom N M'), Function.Surjective f.toFun from h n M _hn
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro M' hk
  match k with
  | 0 =>

    have h1 := centerActsNilpotentlyShifted_of_order_mono Δ M' theta 0 hk
    exact ⟨M', h1, RepGfHom.id M', fun x => ⟨x, LieModuleHom.id_apply x⟩⟩
  | 1 =>

    exact ⟨M', hk, RepGfHom.id M', fun x => ⟨x, LieModuleHom.id_apply x⟩⟩
  | n + 2 =>

    obtain ⟨Q, hQ, K, hK, fQ, fK, hcover⟩ := filtration_one_step M' n hk

    obtain ⟨N', hN', g, hg_surj⟩ := ih (n + 1) (by omega) K hK

    let fK_g : RepGfHom N' M' := fK.comp g

    obtain ⟨N, hN, f, hf⟩ := repGfObj_directSum_data N' Q hN' hQ M' fK_g fQ
    refine ⟨N, hN, f, fun m => ?_⟩

    obtain ⟨q, k', hqk⟩ := hcover m

    obtain ⟨y, hy⟩ := hg_surj k'

    have hfkg : fK_g.toFun y = fK.toFun k' := by
      show (fK.toFun.comp g.toFun) y = fK.toFun k'
      simp [hy]

    have hcover_y : (fK_g.toFun y : M'.carrier) + (fQ.toFun q : M'.carrier) = m := by
      rw [hfkg, add_comm]; exact hqk

    exact hf m ⟨y, q, hcover_y⟩

def centerActsByScalar_prop {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (M : RepGfObj R 𝔤) (theta : Δ.𝔥 →ₗ[R] R) : Prop :=
  centerActsNilpotentlyShifted_of_order Δ M theta 1

def centerActsNilpotentlyShifted_prop {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (M : RepGfObj R 𝔤) (theta : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∃ n, centerActsNilpotentlyShifted_of_order Δ M theta n

theorem centerActsByScalar_implies_nilpotentlyShifted {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (M : RepGfObj R 𝔤) (theta : Δ.𝔥 →ₗ[R] R) :
    centerActsByScalar_prop Δ M theta → centerActsNilpotentlyShifted_prop Δ M theta := by
  intro h
  exact ⟨1, h⟩

structure HasInfChar {Δ : TriangularDecomposition R 𝔤}
    (M : RepGfObj R 𝔤) (theta : Δ.𝔥 →ₗ[R] R) : Prop where
  center_acts_by_scalar : centerActsByScalar_prop Δ M theta

structure HasGenInfChar {Δ : TriangularDecomposition R 𝔤}
    (M : RepGfObj R 𝔤) (theta : Δ.𝔥 →ₗ[R] R) : Prop where
  center_acts_nilpotently_shifted : centerActsNilpotentlyShifted_prop Δ M theta

theorem hasInfChar_implies_hasGenInfChar {Δ : TriangularDecomposition R 𝔤}
    (M : RepGfObj R 𝔤) (theta : Δ.𝔥 →ₗ[R] R)
    (h : HasInfChar M theta) : HasGenInfChar M theta :=
  ⟨centerActsByScalar_implies_nilpotentlyShifted Δ M theta h.center_acts_by_scalar⟩

structure EndoFunctorData (R : Type u) [CommRing R] (𝔤 : Type u) [LieRing 𝔤]
    [LieAlgebra R 𝔤] where
  obj : RepGfObj R 𝔤 → RepGfObj R 𝔤
  mapHom : ∀ {M N : RepGfObj R 𝔤}, RepGfHom M N → RepGfHom (obj M) (obj N)
  map_id : ∀ (M : RepGfObj R 𝔤), (mapHom (RepGfHom.id M)).EqAsMap (RepGfHom.id (obj M))
  map_comp : ∀ {M N P : RepGfObj R 𝔤} (f : RepGfHom M N) (g : RepGfHom N P),
    (mapHom (g.comp f)).EqAsMap ((mapHom g).comp (mapHom f))

structure NatTransData (F G : EndoFunctorData R 𝔤) where
  app : ∀ (M : RepGfObj R 𝔤), RepGfHom (F.obj M) (G.obj M)
  naturality : ∀ {M₁ M₂ : RepGfObj R 𝔤} (f : RepGfHom M₁ M₂),
    ((app M₂).comp (F.mapHom f)).EqAsMap ((G.mapHom f).comp (app M₁))

def NatTransData.comp {F G H : EndoFunctorData R 𝔤}
    (β : NatTransData G H) (α : NatTransData F G) : NatTransData F H where
  app M := (β.app M).comp (α.app M)
  naturality f x := by


    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply]
    have hα := α.naturality f x
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hα
    rw [hα]
    have hβ := β.naturality f ((α.app _).toFun x)
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hβ
    exact hβ

def NatTransData.id (F : EndoFunctorData R 𝔤) : NatTransData F F where
  app _ := RepGfHom.id _
  naturality f x := by

    simp [RepGfHom.comp, RepGfHom.id]

def NatTransData.EqPointwise {F G : EndoFunctorData R 𝔤}
    (α β : NatTransData F G) : Prop :=
  ∀ M : RepGfObj R 𝔤, (α.app M).EqAsMap (β.app M)

def AreNatIso (F G : EndoFunctorData R 𝔤) : Prop :=
  ∃ (α : NatTransData F G) (β : NatTransData G F),
    (β.comp α).EqPointwise (NatTransData.id F) ∧
    (α.comp β).EqPointwise (NatTransData.id G)

def IsDirectSummand (F G : EndoFunctorData R 𝔤) : Prop :=
  ∃ (i : NatTransData F G) (p : NatTransData G F),
    (p.comp i).EqPointwise (NatTransData.id F)

lemma isDirectSummand_refl (F : EndoFunctorData R 𝔤) : IsDirectSummand F F :=
  ⟨NatTransData.id F, NatTransData.id F,
    fun M x => by simp [NatTransData.comp, NatTransData.id, RepGfHom.comp, RepGfHom.id]⟩

def IsExactSequence {M₁ M₂ M₃ : RepGfObj R 𝔤}
    (f : RepGfHom M₁ M₂) (g : RepGfHom M₂ M₃) : Prop :=
  ∀ (m : M₂.carrier), g.toFun m = 0 ↔ ∃ (x : M₁.carrier), f.toFun x = m

def IsProjectiveModule (M : RepGfObj R 𝔤) : Prop :=
  ∀ {N : RepGfObj R 𝔤} (p : RepGfHom N M),
    (Function.Surjective p.toFun) →
    ∃ (s : RepGfHom M N), (p.comp s).EqAsMap (RepGfHom.id M)

structure TensorFunctorData (R : Type u) [CommRing R] (𝔤 : Type u) [LieRing 𝔤]
    [LieAlgebra R 𝔤] where
  V : Type u
  inst_addCommGroupV : AddCommGroup V
  inst_moduleV : Module R V
  inst_lieRingModuleV : LieRingModule 𝔤 V
  inst_lieModuleV : LieModule R 𝔤 V
  inst_finiteDimV : Module.Finite R V
  inst_freeV : Module.Free R V
  functor : EndoFunctorData R 𝔤
  tensor_obj_spec : ∀ (M : RepGfObj R 𝔤),
    Nonempty ((functor.obj M).carrier ≃ₗ⁅R, 𝔤⁆ (TensorProduct R V M.carrier))
  block_factoring : ∀ (Δ : TriangularDecomposition R 𝔤)
    (theta : Δ.𝔥 →ₗ[R] R) (M : RepGfObj R 𝔤),
    ¬ HasGenInfChar M theta → ∀ (x : (functor.obj M).carrier), x = 0
  is_exact : ∀ {M₁ M₂ M₃ : RepGfObj R 𝔤}
    (f : RepGfHom M₁ M₂) (g : RepGfHom M₂ M₃)
    (_hex : IsExactSequence f g),
    IsExactSequence (functor.mapHom f) (functor.mapHom g)
  sends_projectives_to_projectives : ∀ (M : RepGfObj R 𝔤),
    IsProjectiveModule M → IsProjectiveModule (functor.obj M)

structure IsProjectiveFunctor (F : EndoFunctorData R 𝔤) : Prop where
  exists_tensor_summand :
    ∃ (FV : TensorFunctorData R 𝔤), IsDirectSummand F FV.functor

lemma tensor_functor_is_projective (FV : TensorFunctorData R 𝔤) :
    IsProjectiveFunctor FV.functor where
  exists_tensor_summand := ⟨FV, isDirectSummand_refl FV.functor⟩

theorem IsProjectiveFunctor.is_exact {F : EndoFunctorData R 𝔤}
    (hF : IsProjectiveFunctor F)
    {M₁ M₂ M₃ : RepGfObj R 𝔤}
    (f : RepGfHom M₁ M₂) (g : RepGfHom M₂ M₃)
    (_hex : IsExactSequence f g) :
    IsExactSequence (F.mapHom f) (F.mapHom g) := by
  obtain ⟨FV, inc, ret, hRI⟩ := hF.exists_tensor_summand

  have hFVex := FV.is_exact f g _hex

  have inc_nat : ∀ {A B : RepGfObj R 𝔤} (h : RepGfHom A B) (x : (F.obj A).carrier),
      (inc.app B).toFun ((F.mapHom h).toFun x) =
      (FV.functor.mapHom h).toFun ((inc.app A).toFun x) := by
    intro A B h x; exact inc.naturality h x
  have ret_nat : ∀ {A B : RepGfObj R 𝔤} (h : RepGfHom A B) (x : (FV.functor.obj A).carrier),
      (ret.app B).toFun ((FV.functor.mapHom h).toFun x) =
      (F.mapHom h).toFun ((ret.app A).toFun x) := by
    intro A B h x; exact ret.naturality h x
  have hRI' : ∀ M (x : (F.obj M).carrier),
      (ret.app M).toFun ((inc.app M).toFun x) = x := fun M x => hRI M x
  intro m
  constructor
  ·
    intro hgm
    have h1 : (FV.functor.mapHom g).toFun ((inc.app M₂).toFun m) = 0 := by
      rw [← inc_nat g m, hgm, map_zero]
    obtain ⟨y, hy⟩ := (hFVex ((inc.app M₂).toFun m)).mp h1
    refine ⟨(ret.app M₁).toFun y, ?_⟩
    rw [← ret_nat f y, hy, hRI']
  ·
    intro ⟨x, hfx⟩
    have h1 : (inc.app M₃).toFun ((F.mapHom g).toFun m) = 0 := by
      rw [inc_nat g m, ← hfx, inc_nat f x]
      have := ((hFVex ((FV.functor.mapHom f).toFun ((inc.app M₁).toFun x))).mpr
        ⟨(inc.app M₁).toFun x, rfl⟩)
      exact this
    have h2 : (F.mapHom g).toFun m =
        (ret.app M₃).toFun ((inc.app M₃).toFun ((F.mapHom g).toFun m)) :=
      (hRI' M₃ ((F.mapHom g).toFun m)).symm
    rw [h2, h1, map_zero]

theorem IsProjectiveFunctor.sends_projectives_to_projectives {F : EndoFunctorData R 𝔤}
    (hF : IsProjectiveFunctor F)
    (M : RepGfObj R 𝔤)
    (hM : IsProjectiveModule M) : IsProjectiveModule (F.obj M) := by
  obtain ⟨FV, inc, ret, hRI⟩ := hF.exists_tensor_summand

  have hFVM : IsProjectiveModule (FV.functor.obj M) :=
    FV.sends_projectives_to_projectives M hM
  have hRI' : ∀ (x : (F.obj M).carrier),
      (ret.app M).toFun ((inc.app M).toFun x) = x := fun x => hRI M x

  intro N q hq_surj

  letI prodLRM : LieRingModule 𝔤 (N.carrier × (FV.functor.obj M).carrier) :=
    { bracket := fun x mn => (⁅x, mn.1⁆, ⁅x, mn.2⁆)
      add_lie := fun x y mn => by ext <;> exact add_lie x y _
      lie_add := fun x mn₁ mn₂ => by ext <;> exact lie_add x _ _
      leibniz_lie := fun x y mn => by ext <;> exact leibniz_lie x y _ }
  letI prodLM : LieModule R 𝔤 (N.carrier × (FV.functor.obj M).carrier) :=
    { smul_lie := fun r x mn => by ext <;> exact smul_lie r x _
      lie_smul := fun r x mn => by ext <;> exact lie_smul r x _ }
  let pullbackSub : LieSubmodule R 𝔤 (N.carrier × (FV.functor.obj M).carrier) :=
    { carrier := {p | q.toFun p.1 = (ret.app M).toFun p.2}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, map_add] at *
        rw [ha, hb]
      zero_mem' := by simp
      smul_mem' := by
        intro r p hp
        simp only [Set.mem_setOf_eq, Prod.smul_fst, Prod.smul_snd, map_smul] at *
        rw [hp]
      lie_mem := by
        intro x p hp
        simp only [Set.mem_setOf_eq] at *
        show q.toFun (⁅x, p⁆ : N.carrier × (FV.functor.obj M).carrier).1 = (ret.app M).toFun (⁅x, p⁆ : N.carrier × (FV.functor.obj M).carrier).2
        dsimp [Bracket.bracket, prodLRM]
        rw [LieModuleHom.map_lie q.toFun x p.1, LieModuleHom.map_lie (ret.app M).toFun x p.2, hp] }
  let P : RepGfObj R 𝔤 := ⟨↥pullbackSub, inferInstance, inferInstance, inferInstance, inferInstance⟩

  let π₂ : RepGfHom P (FV.functor.obj M) :=
    ⟨{ toLinearMap := {
         toFun := fun p => p.val.2
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl }
       map_lie' := fun {x m} => rfl }⟩

  have hπ₂_surj : Function.Surjective π₂.toFun := by
    intro f
    obtain ⟨n, hn⟩ := hq_surj ((ret.app M).toFun f)
    exact ⟨⟨(n, f), hn⟩, rfl⟩

  obtain ⟨σ, hσ⟩ := hFVM π₂ hπ₂_surj

  let π₁ : RepGfHom P N :=
    ⟨{ toLinearMap := {
         toFun := fun p => p.val.1
         map_add' := fun _ _ => rfl
         map_smul' := fun _ _ => rfl }
       map_lie' := fun {x m} => rfl }⟩

  let s : RepGfHom (F.obj M) N := π₁.comp (σ.comp (inc.app M))
  refine ⟨s, fun x => ?_⟩
  show (q.comp s).toFun x = (RepGfHom.id (F.obj M)).toFun x
  simp only [s, RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply,
             RepGfHom.id, LieModuleHom.coe_id, id_eq]
  set y := σ.toFun ((inc.app M).toFun x) with hy_def
  have hπ₁_eq : π₁.toFun y = (↑y : N.carrier × (FV.functor.obj M).carrier).1 := rfl
  rw [hπ₁_eq]
  have hpull : q.toFun (↑y : N.carrier × (FV.functor.obj M).carrier).1 =
      (ret.app M).toFun (↑y : N.carrier × (FV.functor.obj M).carrier).2 := y.prop
  have hsec : (↑y : N.carrier × (FV.functor.obj M).carrier).2 = (inc.app M).toFun x := by
    have := hσ ((inc.app M).toFun x)
    exact this
  rw [hpull, hsec, hRI']

structure ThetaFunctorData (R : Type u) [CommRing R] (𝔤 : Type u) [LieRing 𝔤]
    [LieAlgebra R 𝔤] (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (theta : Δ.𝔥 →ₗ[R] R) where
  baseFunctor : EndoFunctorData R 𝔤
  factors_through_block :
    ∀ (M : RepGfObj R 𝔤), ¬ HasGenInfChar M theta →
    ∀ (x : (baseFunctor.obj M).carrier), x = 0

def AreNatIsoTheta {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F G : ThetaFunctorData R 𝔤 Δ wg theta) : Prop :=
  AreNatIso F.baseFunctor G.baseFunctor

def IsDirectSummandTheta {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F G : ThetaFunctorData R 𝔤 Δ wg theta) : Prop :=
  IsDirectSummand F.baseFunctor G.baseFunctor

def TensorFunctorData.restrictToTheta (FV : TensorFunctorData R 𝔤)
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (theta : Δ.𝔥 →ₗ[R] R) : ThetaFunctorData R 𝔤 Δ wg theta where
  baseFunctor := FV.functor
  factors_through_block := FV.block_factoring Δ theta

structure IsProjectiveThetaFunctor {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ} {theta : Δ.𝔥 →ₗ[R] R}
    (F : ThetaFunctorData R 𝔤 Δ wg theta) : Prop where
  exists_tensor_summand :
    ∃ (FV : TensorFunctorData R 𝔤),
      IsDirectSummandTheta F (FV.restrictToTheta Δ wg theta)

def NatTransThetaSpace {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F₁ F₂ : ThetaFunctorData R 𝔤 Δ wg theta) : Type _ :=
  NatTransData F₁.baseFunctor F₂.baseFunctor

def evalAtVerma {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F₁ F₂ : ThetaFunctorData R 𝔤 Δ wg theta)
    (Mverma : RepGfObj R 𝔤)
    (eta : NatTransThetaSpace F₁ F₂) :
    RepGfHom (F₁.baseFunctor.obj Mverma) (F₂.baseFunctor.obj Mverma) :=
  eta.app Mverma

theorem eilenbergWatts_eval_factorization
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (FV₁ FV₂ : TensorFunctorData R 𝔤)
    (Mverma : RepGfObj R 𝔤)
    (_hMverma : Nonempty (IsVermaModule Δ Mverma.carrier (lam - wg.ρ))) :


    ∃ (X : Type u)
      (ew : NatTransData FV₁.functor FV₂.functor → X)
      (dj : X → RepGfHom (FV₁.functor.obj Mverma) (FV₂.functor.obj Mverma)),
      Function.Bijective ew ∧
      Function.Bijective dj ∧
      (∀ η, (fun η => η.app Mverma) η = dj (ew η)) := by sorry

theorem dufloJoseph_eval_bijective_at_verma
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (FV₁ FV₂ : TensorFunctorData R 𝔤)
    (Mverma : RepGfObj R 𝔤)
    (_hMverma : Nonempty (IsVermaModule Δ Mverma.carrier (lam - wg.ρ))) :
    Function.Bijective (fun (η : NatTransData FV₁.functor FV₂.functor) => η.app Mverma) := by

  obtain ⟨X, ew, dj, hew_bij, hdj_bij, hfactor⟩ :=
    eilenbergWatts_eval_factorization Δ wg lam FV₁ FV₂ Mverma _hMverma

  have heq : (fun η => η.app Mverma) = dj ∘ ew := by
    funext η; exact hfactor η
  rw [heq]

  exact hdj_bij.comp hew_bij

theorem evalAtVerma_bijective_tensor
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (FV₁ FV₂ : TensorFunctorData R 𝔤)
    (Mverma : RepGfObj R 𝔤)
    (_hMverma : Nonempty (IsVermaModule Δ Mverma.carrier (lam - wg.ρ))) :
    Function.Bijective (evalAtVerma
      (FV₁.restrictToTheta Δ wg lam) (FV₂.restrictToTheta Δ wg lam) Mverma) :=


  dufloJoseph_eval_bijective_at_verma Δ wg lam FV₁ FV₂ Mverma _hMverma

theorem evalAtVerma_bijective_of_summand
    {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    {lam : Δ.𝔥 →ₗ[R] R}
    (F₁ F₂ : ThetaFunctorData R 𝔤 Δ wg lam)
    (G₁ G₂ : ThetaFunctorData R 𝔤 Δ wg lam)
    (hSum₁ : IsDirectSummandTheta F₁ G₁)
    (hSum₂ : IsDirectSummandTheta F₂ G₂)
    (Mverma : RepGfObj R 𝔤)
    (hBij : Function.Bijective (evalAtVerma G₁ G₂ Mverma)) :
    Function.Bijective (evalAtVerma F₁ F₂ Mverma) := by
  obtain ⟨i₁, p₁, hp₁⟩ := hSum₁
  obtain ⟨i₂, p₂, hp₂⟩ := hSum₂

  have repGfHom_ext : ∀ {M' N' : RepGfObj R 𝔤} (f g : RepGfHom M' N'),
      (∀ x, f.toFun x = g.toFun x) → f = g := by
    intro M' N' ⟨f⟩ ⟨g⟩ h; congr; exact LieModuleHom.ext h

  have natTransData_ext : ∀ {F' G' : EndoFunctorData R 𝔤}
      (α β : NatTransData F' G'),
      (∀ (M : RepGfObj R 𝔤) (x : (F'.obj M).carrier),
        (α.app M).toFun x = (β.app M).toFun x) → α = β := by
    intro F' G' α β h
    cases α; cases β; congr; funext M
    exact repGfHom_ext _ _ (h M)

  have retract₁ : ∀ (M : RepGfObj R 𝔤) (y : (F₁.baseFunctor.obj M).carrier),
      (p₁.app M).toFun ((i₁.app M).toFun y) = y := by
    intro M y
    have h := hp₁ M y


    simp only [NatTransData.EqPointwise, RepGfHom.EqAsMap] at hp₁
    have := hp₁ M y
    simp [NatTransData.comp, RepGfHom.comp, NatTransData.id, RepGfHom.id] at this
    exact this
  have retract₂ : ∀ (M : RepGfObj R 𝔤) (z : (F₂.baseFunctor.obj M).carrier),
      (p₂.app M).toFun ((i₂.app M).toFun z) = z := by
    intro M z
    simp only [NatTransData.EqPointwise, RepGfHom.EqAsMap] at hp₂
    have := hp₂ M z
    simp [NatTransData.comp, RepGfHom.comp, NatTransData.id, RepGfHom.id] at this
    exact this
  constructor
  ·
    intro η η' heq


    have heval : (i₂.comp (η.comp p₁)).app Mverma = (i₂.comp (η'.comp p₁)).app Mverma := by
      apply repGfHom_ext
      intro x
      show (i₂.app Mverma).toFun ((η.app Mverma).toFun ((p₁.app Mverma).toFun x)) =
           (i₂.app Mverma).toFun ((η'.app Mverma).toFun ((p₁.app Mverma).toFun x))
      rw [show (η.app Mverma) = (η'.app Mverma) from heq]
    have hξeq := hBij.1 heval
    apply natTransData_ext
    intro M x

    have eq₁ : (η.app M).toFun x =
        (p₂.app M).toFun ((i₂.app M).toFun ((η.app M).toFun ((p₁.app M).toFun ((i₁.app M).toFun x)))) := by
      rw [retract₁ M x, retract₂ M]
    have eq₂ : (η'.app M).toFun x =
        (p₂.app M).toFun ((i₂.app M).toFun ((η'.app M).toFun ((p₁.app M).toFun ((i₁.app M).toFun x)))) := by
      rw [retract₁ M x, retract₂ M]
    rw [eq₁, eq₂]
    congr 1

    have hAppEq : (i₂.comp (η.comp p₁)).app M = (i₂.comp (η'.comp p₁)).app M := by rw [hξeq]

    have : ((i₂.comp (η.comp p₁)).app M).toFun ((i₁.app M).toFun x) =
           ((i₂.comp (η'.comp p₁)).app M).toFun ((i₁.app M).toFun x) := by
      rw [hAppEq]
    exact this
  ·
    intro f

    let g : RepGfHom (G₁.baseFunctor.obj Mverma) (G₂.baseFunctor.obj Mverma) :=
      (i₂.app Mverma).comp (f.comp (p₁.app Mverma))
    obtain ⟨Φ, hΦ⟩ := hBij.2 g

    use p₂.comp (Φ.comp i₁)

    apply repGfHom_ext
    intro x
    show (p₂.app Mverma).toFun ((Φ.app Mverma).toFun ((i₁.app Mverma).toFun x)) = f.toFun x

    have hΦM : Φ.app Mverma = g := hΦ
    rw [show (Φ.app Mverma).toFun = g.toFun from congrArg RepGfHom.toFun hΦM]

    show (p₂.app Mverma).toFun
      ((i₂.app Mverma).toFun (f.toFun ((p₁.app Mverma).toFun ((i₁.app Mverma).toFun x)))) = f.toFun x
    rw [retract₁ Mverma x, retract₂ Mverma]

theorem theorem_22_4
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (F₁ F₂ : ThetaFunctorData R 𝔤 Δ wg lam)
    (_hF₁ : IsProjectiveThetaFunctor F₁)
    (_hF₂ : IsProjectiveThetaFunctor F₂)
    (Mverma : RepGfObj R 𝔤)
    (_hMverma : Nonempty (IsVermaModule Δ Mverma.carrier (lam - wg.ρ))) :
    Function.Bijective (evalAtVerma F₁ F₂ Mverma) := by


  obtain ⟨FV₁, hSum₁⟩ := _hF₁.exists_tensor_summand
  obtain ⟨FV₂, hSum₂⟩ := _hF₂.exists_tensor_summand


  have hBij := evalAtVerma_bijective_tensor Δ wg lam FV₁ FV₂ Mverma _hMverma

  exact evalAtVerma_bijective_of_summand F₁ F₂
    (FV₁.restrictToTheta Δ wg lam) (FV₂.restrictToTheta Δ wg lam)
    hSum₁ hSum₂ Mverma hBij

structure NatTransOnInfChar {Δ : TriangularDecomposition R 𝔤}
    (theta : Δ.𝔥 →ₗ[R] R) (F₁ F₂ : EndoFunctorData R 𝔤) where
  app : ∀ (M : RepGfObj R 𝔤), HasInfChar M theta → RepGfHom (F₁.obj M) (F₂.obj M)
  naturality : ∀ {M₁ M₂ : RepGfObj R 𝔤} (hM₁ : HasInfChar M₁ theta)
    (hM₂ : HasInfChar M₂ theta) (f : RepGfHom M₁ M₂),
    ((app M₂ hM₂).comp (F₁.mapHom f)).EqAsMap ((F₂.mapHom f).comp (app M₁ hM₁))

structure NatTransOnGenInfChar {Δ : TriangularDecomposition R 𝔤}
    (theta : Δ.𝔥 →ₗ[R] R) (F₁ F₂ : EndoFunctorData R 𝔤) where
  app : ∀ (M : RepGfObj R 𝔤), HasGenInfChar M theta → RepGfHom (F₁.obj M) (F₂.obj M)
  naturality : ∀ {M₁ M₂ : RepGfObj R 𝔤} (hM₁ : HasGenInfChar M₁ theta)
    (hM₂ : HasGenInfChar M₂ theta) (f : RepGfHom M₁ M₂),
    ((app M₂ hM₂).comp (F₁.mapHom f)).EqAsMap ((F₂.mapHom f).comp (app M₁ hM₁))

def NatTransOnGenInfChar.restrictToInfChar {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R} {F₁ F₂ : EndoFunctorData R 𝔤}
    (η : NatTransOnGenInfChar theta F₁ F₂) : NatTransOnInfChar theta F₁ F₂ where
  app M hM := η.app M (hasInfChar_implies_hasGenInfChar M theta hM)
  naturality hM₁ hM₂ f :=
    η.naturality (hasInfChar_implies_hasGenInfChar _ theta hM₁)
      (hasInfChar_implies_hasGenInfChar _ theta hM₂) f

def NatTransOnInfChar.EqPointwise {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R} {F₁ F₂ : EndoFunctorData R 𝔤}
    (α β : NatTransOnInfChar theta F₁ F₂) : Prop :=
  ∀ (M : RepGfObj R 𝔤) (hM : HasInfChar M theta),
    (α.app M hM).EqAsMap (β.app M hM)

def NatTransOnInfChar.comp {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R} {F G H : EndoFunctorData R 𝔤}
    (β : NatTransOnInfChar theta G H) (α : NatTransOnInfChar theta F G) :
    NatTransOnInfChar theta F H where
  app M hM := (β.app M hM).comp (α.app M hM)
  naturality hM₁ hM₂ f x := by
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply]
    have hα := α.naturality hM₁ hM₂ f x
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hα
    rw [hα]
    have hβ := β.naturality hM₁ hM₂ f ((α.app _ hM₁).toFun x)
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hβ
    exact hβ

def NatTransOnInfChar.id {Δ : TriangularDecomposition R 𝔤}
    (theta : Δ.𝔥 →ₗ[R] R) (F : EndoFunctorData R 𝔤) :
    NatTransOnInfChar theta F F where
  app _ _ := RepGfHom.id _
  naturality _ _ f x := by
    simp [RepGfHom.comp, RepGfHom.id]

def AreNatIsoOnInfChar {Δ : TriangularDecomposition R 𝔤}
    (theta : Δ.𝔥 →ₗ[R] R) (F₁ F₂ : EndoFunctorData R 𝔤) : Prop :=
  ∃ (α : NatTransOnInfChar theta F₁ F₂) (β : NatTransOnInfChar theta F₂ F₁),
    (β.comp α).EqPointwise (NatTransOnInfChar.id theta F₁) ∧
    (α.comp β).EqPointwise (NatTransOnInfChar.id theta F₂)

def NatTransOnGenInfChar.comp {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R} {F G H : EndoFunctorData R 𝔤}
    (β : NatTransOnGenInfChar theta G H) (α : NatTransOnGenInfChar theta F G) :
    NatTransOnGenInfChar theta F H where
  app M hM := (β.app M hM).comp (α.app M hM)
  naturality hM₁ hM₂ f x := by
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply]
    have hα := α.naturality hM₁ hM₂ f x
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hα
    rw [hα]
    have hβ := β.naturality hM₁ hM₂ f ((α.app _ hM₁).toFun x)
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hβ
    exact hβ

def NatTransOnGenInfChar.id {Δ : TriangularDecomposition R 𝔤}
    (theta : Δ.𝔥 →ₗ[R] R) (F : EndoFunctorData R 𝔤) :
    NatTransOnGenInfChar theta F F where
  app _ _ := RepGfHom.id _
  naturality _ _ f x := by
    simp [RepGfHom.comp, RepGfHom.id]

def NatTransOnGenInfChar.EqPointwise {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R} {F₁ F₂ : EndoFunctorData R 𝔤}
    (α β : NatTransOnGenInfChar theta F₁ F₂) : Prop :=
  ∀ (M : RepGfObj R 𝔤) (hM : HasGenInfChar M theta),
    (α.app M hM).EqAsMap (β.app M hM)


theorem genInfChar_admits_infChar_surjection
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R}
    (M : RepGfObj R 𝔤) (_hM : HasGenInfChar M theta) :
    ∃ (N : RepGfObj R 𝔤) (_ : HasInfChar N theta)
      (f : RepGfHom N M), Function.Surjective f.toFun := by

  obtain ⟨n, hn⟩ := _hM.center_acts_nilpotently_shifted

  obtain ⟨N, hN1, f, hf_surj⟩ := filtration_surjection_from_nilpotent_order M n hn

  exact ⟨N, ⟨hN1⟩, f, hf_surj⟩

theorem exact_functor_preserves_surjection
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (F : EndoFunctorData R 𝔤)
    (_hF : IsProjectiveFunctor F)
    {N M : RepGfObj R 𝔤}
    (f : RepGfHom N M)
    (hf : Function.Surjective f.toFun) :
    Function.Surjective (F.mapHom f).toFun := by

  letI lieRingModulePUnit : LieRingModule 𝔤 PUnit.{u+1} :=
    { bracket := fun _ _ => PUnit.unit
      add_lie := fun _ _ _ => rfl
      lie_add := fun _ _ _ => rfl
      leibniz_lie := fun _ _ _ => by simp }
  letI lieModulePUnit : LieModule R 𝔤 PUnit.{u+1} :=
    { smul_lie := fun _ _ _ => rfl
      lie_smul := fun _ _ _ => rfl }
  let Z : RepGfObj R 𝔤 :=
    { carrier := PUnit
      inst_addCommGroup := inferInstance
      inst_module := inferInstance
      inst_lieRingModule := lieRingModulePUnit
      inst_lieModule := lieModulePUnit }

  haveI : AddCommGroup Z.carrier := Z.inst_addCommGroup
  haveI : Module R Z.carrier := Z.inst_module
  haveI : LieRingModule 𝔤 Z.carrier := Z.inst_lieRingModule
  haveI : LieModule R 𝔤 Z.carrier := Z.inst_lieModule
  let g : RepGfHom M Z := ⟨0⟩


  have hex : IsExactSequence f g := by
    intro m
    constructor
    · intro _
      exact hf m
    · intro _
      exact Subsingleton.elim _ _

  have hFex := _hF.is_exact f g hex


  have hZex : IsExactSequence (RepGfHom.id Z) (RepGfHom.id Z) := by
    intro m
    constructor
    · intro _; exact ⟨m, Subsingleton.elim _ _⟩
    · intro _; exact Subsingleton.elim _ _
  have hFZex := _hF.is_exact (RepGfHom.id Z) (RepGfHom.id Z) hZex


  have hFZ_zero : ∀ (y : (F.obj Z).carrier), y = 0 := by
    intro y
    have hmap_id := F.map_id Z


    have h1 : (F.mapHom (RepGfHom.id Z)).toFun y = y := hmap_id y
    have h2 := (hFZex y).mpr ⟨y, h1⟩
    rwa [h1] at h2

  intro y

  have hgy_zero : (F.mapHom g).toFun y = 0 := hFZ_zero _

  exact (hFex y).mp hgy_zero

theorem genInfChar_generated_by_infChar
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F : EndoFunctorData R 𝔤)
    (_hF : IsProjectiveFunctor F)
    (M : RepGfObj R 𝔤) (hM : HasGenInfChar M theta)
    (x : (F.obj M).carrier) :
    ∃ (N : RepGfObj R 𝔤) (_ : HasInfChar N theta)
      (f : RepGfHom N M) (y : (F.obj N).carrier),
      (F.mapHom f).toFun y = x := by

  obtain ⟨N, hN, f, hf_surj⟩ := genInfChar_admits_infChar_surjection M hM

  have hFf_surj := exact_functor_preserves_surjection F _hF f hf_surj

  obtain ⟨y, hy⟩ := hFf_surj x
  exact ⟨N, hN, f, y, hy⟩

theorem eilenbergWatts_component_lift
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F₁ F₂ : EndoFunctorData R 𝔤)
    (_hF₁ : IsProjectiveFunctor F₁)
    (_hF₂ : IsProjectiveFunctor F₂)
    (phi : NatTransOnInfChar theta F₁ F₂)
    (M : RepGfObj R 𝔤) (hM : HasGenInfChar M theta) :
    ∃ (phi_hat_M : RepGfHom (F₁.obj M) (F₂.obj M)),
      ∀ (N : RepGfObj R 𝔤) (hN : HasInfChar N theta)
        (f : RepGfHom N M) (y : (F₁.obj N).carrier),
        phi_hat_M.toFun ((F₁.mapHom f).toFun y) =
          (F₂.mapHom f).toFun ((phi.app N hN).toFun y) := by sorry


theorem eilenbergWatts_homSpace_lift
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F₁ F₂ : EndoFunctorData R 𝔤)
    (_hF₁ : IsProjectiveFunctor F₁)
    (_hF₂ : IsProjectiveFunctor F₂)
    (phi : NatTransOnInfChar theta F₁ F₂) :
    ∃ (phi_hat : NatTransOnGenInfChar theta F₁ F₂),
      phi_hat.restrictToInfChar.EqPointwise phi := by


  have hComponents : ∀ (M : RepGfObj R 𝔤) (hM : HasGenInfChar M theta),
      ∃ (phi_hat_M : RepGfHom (F₁.obj M) (F₂.obj M)),
        ∀ (N : RepGfObj R 𝔤) (hN : HasInfChar N theta)
          (f : RepGfHom N M) (y : (F₁.obj N).carrier),
          phi_hat_M.toFun ((F₁.mapHom f).toFun y) =
            (F₂.mapHom f).toFun ((phi.app N hN).toFun y) :=
    fun M hM => eilenbergWatts_component_lift F₁ F₂ _hF₁ _hF₂ phi M hM


  let phi_hat_app : ∀ (M : RepGfObj R 𝔤), HasGenInfChar M theta →
      RepGfHom (F₁.obj M) (F₂.obj M) :=
    fun M hM => Classical.choose (hComponents M hM)
  have phi_hat_compat : ∀ (M : RepGfObj R 𝔤) (hM : HasGenInfChar M theta)
      (N : RepGfObj R 𝔤) (hN : HasInfChar N theta)
      (f : RepGfHom N M) (y : (F₁.obj N).carrier),
      (phi_hat_app M hM).toFun ((F₁.mapHom f).toFun y) =
        (F₂.mapHom f).toFun ((phi.app N hN).toFun y) :=
    fun M hM => Classical.choose_spec (hComponents M hM)

  refine ⟨⟨phi_hat_app, ?_⟩, ?_⟩
  ·

    intro M₁ M₂ hM₁ hM₂ f x

    obtain ⟨N, hN, g, y, hxy⟩ := genInfChar_generated_by_infChar F₁ _hF₁ M₁ hM₁ x

    rw [← hxy]
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply]


    have hF₁_comp := F₁.map_comp g f y
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hF₁_comp

    rw [← hF₁_comp]


    have hcompat₂ := phi_hat_compat M₂ hM₂ N hN (f.comp g) y
    simp only [RepGfHom.comp] at hcompat₂
    rw [hcompat₂]


    rw [phi_hat_compat M₁ hM₁ N hN g y]


    have hF₂_comp := F₂.map_comp g f ((phi.app N hN).toFun y)
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hF₂_comp
    exact hF₂_comp
  ·


    intro M hM x
    simp only [NatTransOnGenInfChar.restrictToInfChar]

    obtain ⟨N, hN, f, y, hxy⟩ := genInfChar_generated_by_infChar F₁ _hF₁ M
      (hasInfChar_implies_hasGenInfChar M theta hM) x
    rw [← hxy]

    rw [phi_hat_compat M (hasInfChar_implies_hasGenInfChar M theta hM) N hN f y]

    have hnat := phi.naturality hN hM f y
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hnat
    exact hnat.symm

theorem homSpace_restriction_surjective
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F₁ F₂ : EndoFunctorData R 𝔤)
    (_hF₁ : IsProjectiveFunctor F₁)
    (_hF₂ : IsProjectiveFunctor F₂)
    (phi : NatTransOnInfChar theta F₁ F₂) :
    ∃ (phi_hat : NatTransOnGenInfChar theta F₁ F₂),
      ∀ (M : RepGfObj R 𝔤) (hM : HasInfChar M theta) (x : (F₁.obj M).carrier),
        (phi_hat.app M (hasInfChar_implies_hasGenInfChar M theta hM)).toFun x =
          (phi.app M hM).toFun x := by
  obtain ⟨phi_hat, hEq⟩ := eilenbergWatts_homSpace_lift F₁ F₂ _hF₁ _hF₂ phi
  exact ⟨phi_hat, fun M hM x => hEq M hM x⟩

theorem liftInfCharToGenInfChar_exists
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F₁ F₂ : EndoFunctorData R 𝔤)
    (_hF₁ : IsProjectiveFunctor F₁)
    (_hF₂ : IsProjectiveFunctor F₂)
    (phi : NatTransOnInfChar theta F₁ F₂) :
    ∃ (phi_hat : NatTransOnGenInfChar theta F₁ F₂),
      phi_hat.restrictToInfChar.EqPointwise phi := by
  obtain ⟨phi_hat, hRestr⟩ := homSpace_restriction_surjective F₁ F₂ _hF₁ _hF₂ phi
  exact ⟨phi_hat, fun M hM => hRestr M hM⟩

theorem genInfChar_restriction_injective
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F₁ F₂ : EndoFunctorData R 𝔤)
    (_hF₁ : IsProjectiveFunctor F₁)
    (_hF₂ : IsProjectiveFunctor F₂)
    (α β : NatTransOnGenInfChar theta F₁ F₂)
    (hAgree : α.restrictToInfChar.EqPointwise β.restrictToInfChar) :
    α.EqPointwise β := by

  intro M hM x

  obtain ⟨N, hN, f, y, hxy⟩ := genInfChar_generated_by_infChar F₁ _hF₁ M hM x

  rw [← hxy]

  have hα_nat := α.naturality (hasInfChar_implies_hasGenInfChar N theta hN) hM f y
  simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hα_nat

  have hβ_nat := β.naturality (hasInfChar_implies_hasGenInfChar N theta hN) hM f y
  simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hβ_nat

  rw [hα_nat, hβ_nat]


  congr 1

  exact hAgree N hN y

theorem liftInfCharToGenInfChar_idempotent_exists
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F : EndoFunctorData R 𝔤)
    (_hF : IsProjectiveFunctor F)
    (phi : NatTransOnInfChar theta F F)
    (_hIdem : ∀ (M : RepGfObj R 𝔤) (hM : HasInfChar M theta) (x : (F.obj M).carrier),
      (phi.app M hM).toFun ((phi.app M hM).toFun x) = (phi.app M hM).toFun x) :
    ∃ (phi_hat : NatTransOnGenInfChar theta F F),
      phi_hat.restrictToInfChar.EqPointwise phi ∧
      (phi_hat.comp phi_hat).EqPointwise phi_hat := by

  obtain ⟨phi_hat, hRestr⟩ := eilenbergWatts_homSpace_lift F F _hF _hF phi
  refine ⟨phi_hat, hRestr, ?_⟩


  apply genInfChar_restriction_injective F F _hF _hF

  intro M hM x

  have hR : ∀ y, (phi_hat.app M (hasInfChar_implies_hasGenInfChar M theta hM)).toFun y =
                 (phi.app M hM).toFun y := fun y => hRestr M hM y


  simp only [NatTransOnGenInfChar.restrictToInfChar, NatTransOnGenInfChar.comp,
             RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply, hR]
  exact _hIdem M hM x

theorem proposition_22_5_i
    {Δ : TriangularDecomposition R 𝔤} {_wg : WeylGroupData Δ}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F₁ F₂ : EndoFunctorData R 𝔤)
    (_hF₁ : IsProjectiveFunctor F₁)
    (_hF₂ : IsProjectiveFunctor F₂)
    (phi : NatTransOnInfChar theta F₁ F₂) :
    ∃ (phi_hat : NatTransOnGenInfChar theta F₁ F₂),
      phi_hat.restrictToInfChar.EqPointwise phi :=
  liftInfCharToGenInfChar_exists F₁ F₂ _hF₁ _hF₂ phi

lemma filtration_induction_step
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F : EndoFunctorData R 𝔤)
    (_hF : IsProjectiveFunctor F)
    (η : NatTransOnGenInfChar theta F F)
    (hRestr : ∀ (N : RepGfObj R 𝔤) (hN : HasInfChar N theta) (y : (F.obj N).carrier),
      (η.app N (hasInfChar_implies_hasGenInfChar N theta hN)).toFun y = y)
    (M : RepGfObj R 𝔤) (hM : HasGenInfChar M theta)
    (x : (F.obj M).carrier) :
    (η.app M hM).toFun x = x := by

  have hAgree : η.restrictToInfChar.EqPointwise
      (NatTransOnGenInfChar.id theta F).restrictToInfChar := by
    intro N hN y
    simp only [NatTransOnGenInfChar.restrictToInfChar, NatTransOnGenInfChar.id,
               RepGfHom.id, LieModuleHom.id_apply]
    exact hRestr N hN y
  have hEq := genInfChar_restriction_injective F F _hF _hF η
    (NatTransOnGenInfChar.id theta F) hAgree
  have hEqM := hEq M hM x
  simp only [NatTransOnGenInfChar.id, RepGfHom.id, LieModuleHom.id_apply] at hEqM
  exact hEqM

theorem restrictToInfChar_injective
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F : EndoFunctorData R 𝔤)
    (_hF : IsProjectiveFunctor F)
    (η : NatTransOnGenInfChar theta F F)
    (hRestr : η.restrictToInfChar.EqPointwise (NatTransOnInfChar.id theta F)) :
    η.EqPointwise (NatTransOnGenInfChar.id theta F) := by


  have hRestr' : ∀ (N : RepGfObj R 𝔤) (hN : HasInfChar N theta)
      (y : (F.obj N).carrier),
      (η.app N (hasInfChar_implies_hasGenInfChar N theta hN)).toFun y = y := by
    intro N hN y
    have h := hRestr N hN y


    simp only [NatTransOnGenInfChar.restrictToInfChar, NatTransOnInfChar.id,
               RepGfHom.id, LieModuleHom.id_apply] at h
    exact h

  intro M hM x

  simp only [NatTransOnGenInfChar.id, RepGfHom.id, LieModuleHom.id_apply]
  exact filtration_induction_step F _hF η hRestr' M hM x

theorem proposition_22_5_iii
    {Δ : TriangularDecomposition R 𝔤} {_wg : WeylGroupData Δ}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F₁ F₂ : EndoFunctorData R 𝔤)
    (hF₁ : IsProjectiveFunctor F₁)
    (hF₂ : IsProjectiveFunctor F₂)
    (phi : NatTransOnInfChar theta F₁ F₂)
    (psi : NatTransOnInfChar theta F₂ F₁)

    (hInvL : ∀ (M : RepGfObj R 𝔤) (hM : HasInfChar M theta) (x : (F₁.obj M).carrier),
      (psi.app M hM).toFun ((phi.app M hM).toFun x) = x)
    (hInvR : ∀ (M : RepGfObj R 𝔤) (hM : HasInfChar M theta) (x : (F₂.obj M).carrier),
      (phi.app M hM).toFun ((psi.app M hM).toFun x) = x) :
    ∃ (phi_hat : NatTransOnGenInfChar theta F₁ F₂)
      (psi_hat : NatTransOnGenInfChar theta F₂ F₁),
      phi_hat.restrictToInfChar.EqPointwise phi ∧
      psi_hat.restrictToInfChar.EqPointwise psi ∧
      (psi_hat.comp phi_hat).EqPointwise (NatTransOnGenInfChar.id theta F₁) ∧
      (phi_hat.comp psi_hat).EqPointwise (NatTransOnGenInfChar.id theta F₂) := by

  obtain ⟨phi_hat, hphi_hat⟩ := @proposition_22_5_i R _ 𝔤 _ _ Δ _wg theta F₁ F₂ hF₁ hF₂ phi
  obtain ⟨psi_hat, hpsi_hat⟩ := @proposition_22_5_i R _ 𝔤 _ _ Δ _wg theta F₂ F₁ hF₂ hF₁ psi

  refine ⟨phi_hat, psi_hat, hphi_hat, hpsi_hat, ?_, ?_⟩

  · apply restrictToInfChar_injective F₁ hF₁
    intro M hM x
    simp only [NatTransOnGenInfChar.restrictToInfChar, NatTransOnGenInfChar.comp,
               NatTransOnInfChar.id, RepGfHom.id, RepGfHom.comp]
    show (psi_hat.app M (hasInfChar_implies_hasGenInfChar M theta hM)).toFun
         ((phi_hat.app M (hasInfChar_implies_hasGenInfChar M theta hM)).toFun x) = x
    have hφ : ∀ y, (phi_hat.app M (hasInfChar_implies_hasGenInfChar M theta hM)).toFun y
                 = (phi.app M hM).toFun y := fun y => hphi_hat M hM y
    have hψ : ∀ y, (psi_hat.app M (hasInfChar_implies_hasGenInfChar M theta hM)).toFun y
                 = (psi.app M hM).toFun y := fun y => hpsi_hat M hM y
    rw [hφ, hψ]
    exact hInvL M hM x

  · apply restrictToInfChar_injective F₂ hF₂
    intro M hM x
    simp only [NatTransOnGenInfChar.restrictToInfChar, NatTransOnGenInfChar.comp,
               NatTransOnInfChar.id, RepGfHom.id, RepGfHom.comp]
    show (phi_hat.app M (hasInfChar_implies_hasGenInfChar M theta hM)).toFun
         ((psi_hat.app M (hasInfChar_implies_hasGenInfChar M theta hM)).toFun x) = x
    have hφ : ∀ y, (phi_hat.app M (hasInfChar_implies_hasGenInfChar M theta hM)).toFun y
                 = (phi.app M hM).toFun y := fun y => hphi_hat M hM y
    have hψ : ∀ y, (psi_hat.app M (hasInfChar_implies_hasGenInfChar M theta hM)).toFun y
                 = (psi.app M hM).toFun y := fun y => hpsi_hat M hM y
    rw [hψ, hφ]
    exact hInvR M hM x

def AreNatIsoOnGenInfChar {Δ : TriangularDecomposition R 𝔤}
    (theta : Δ.𝔥 →ₗ[R] R) (F₁ F₂ : EndoFunctorData R 𝔤) : Prop :=
  ∃ (α : NatTransOnGenInfChar theta F₁ F₂) (β : NatTransOnGenInfChar theta F₂ F₁),
    (β.comp α).EqPointwise (NatTransOnGenInfChar.id theta F₁) ∧
    (α.comp β).EqPointwise (NatTransOnGenInfChar.id theta F₂)

def IsDirectSumDecompObj {n : ℕ}
    (M : RepGfObj R 𝔤) (summands : Fin n → RepGfObj R 𝔤) : Prop :=
  ∃ (section_i : ∀ i, RepGfHom (summands i) M)
    (retract_i : ∀ i, RepGfHom M (summands i)),

    (∀ i (x : (summands i).carrier),
      (retract_i i).toFun ((section_i i).toFun x) = x) ∧

    (∀ (x : M.carrier),
      x = Finset.univ.sum (fun i =>
        (section_i i).toFun ((retract_i i).toFun x)))

def IsIndecomposableObj (M : RepGfObj R 𝔤) : Prop :=
  ∀ (e : RepGfHom M M),
    (∀ x, e.toFun (e.toFun x) = e.toFun x) →
    (∀ x, e.toFun x = x) ∨ (∀ x, e.toFun x = 0)

def IsIndecomposable (F : EndoFunctorData R 𝔤) : Prop :=
  ∀ (e : NatTransData F F),
    (e.comp e).EqPointwise e →
    e.EqPointwise (NatTransData.id F) ∨
    (∀ (M : RepGfObj R 𝔤) (x : (F.obj M).carrier), (e.app M).toFun x = 0)

def IsDirectSumDecomp (F : EndoFunctorData R 𝔤) {n : ℕ}
    (F_i : Fin n → EndoFunctorData R 𝔤) : Prop :=

  ∃ (section_i : ∀ i, NatTransData (F_i i) F)
    (retract_i : ∀ i, NatTransData F (F_i i)),

    (∀ i, ((retract_i i).comp (section_i i)).EqPointwise (NatTransData.id (F_i i))) ∧


    (∀ (M : RepGfObj R 𝔤) (x : (F.obj M).carrier),
      (RepGfHom.id (F.obj M)).toFun x =
      Finset.univ.sum (fun i =>
        ((section_i i).app M).toFun (((retract_i i).app M).toFun x)))

def IsDirectSumDecompGen (F : EndoFunctorData R 𝔤) {ι : Type u} [Fintype ι]
    (F_i : ι → EndoFunctorData R 𝔤) : Prop :=
  ∃ (section_i : ∀ i, NatTransData (F_i i) F)
    (retract_i : ∀ i, NatTransData F (F_i i)),
    (∀ i, ((retract_i i).comp (section_i i)).EqPointwise (NatTransData.id (F_i i))) ∧
    (∀ (M : RepGfObj R 𝔤) (x : (F.obj M).carrier),
      (RepGfHom.id (F.obj M)).toFun x =
      Finset.univ.sum (fun i =>
        ((section_i i).app M).toFun (((retract_i i).app M).toFun x)))

def FactorsThroughBlock (Δ : TriangularDecomposition R 𝔤)
    (F : EndoFunctorData R 𝔤) (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ (M : RepGfObj R 𝔤),
    ¬ HasGenInfChar M lam →
    ∀ (x : (F.obj M).carrier), x = 0

theorem projective_factors_through_block
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (F : EndoFunctorData R 𝔤) (_hF : IsProjectiveFunctor F) :
    FactorsThroughBlock Δ F lam := by


  intro M hM x

  obtain ⟨FV, i, p, hpi⟩ := _hF.exists_tensor_summand

  have hret : (p.app M).toFun ((i.app M).toFun x) = x := by
    have := hpi M x
    simp only [NatTransData.comp, NatTransData.id, RepGfHom.comp, RepGfHom.id,
               LieModuleHom.coe_comp, Function.comp_apply, LieModuleHom.coe_id, id_eq] at this
    exact this

  have hzero : (i.app M).toFun x = (0 : (FV.functor.obj M).carrier) :=
    FV.block_factoring Δ lam M hM ((i.app M).toFun x)

  rw [← hret, hzero, map_zero]

def IsProjectiveFunctor.toThetaFunctorData
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (F : EndoFunctorData R 𝔤) (hF : IsProjectiveFunctor F) :
    ThetaFunctorData R 𝔤 Δ wg lam where
  baseFunctor := F
  factors_through_block := projective_factors_through_block Δ wg lam F hF

theorem IsProjectiveFunctor.toIsProjectiveThetaFunctor
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (F : EndoFunctorData R 𝔤) (hF : IsProjectiveFunctor F) :
    IsProjectiveThetaFunctor (hF.toThetaFunctorData Δ wg lam) :=
  { exists_tensor_summand := ⟨hF.exists_tensor_summand.choose, hF.exists_tensor_summand.choose_spec⟩ }

theorem corollary_22_6_i
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (F₁ F₂ : EndoFunctorData R 𝔤)
    (_hF₁ : IsProjectiveFunctor F₁)
    (_hF₂ : IsProjectiveFunctor F₂)
    (Mverma : RepGfObj R 𝔤)
    (_hMverma : Nonempty (IsVermaModule Δ Mverma.carrier (lam - wg.ρ)))

    (iso_fwd : RepGfHom (F₁.obj Mverma) (F₂.obj Mverma))
    (iso_bwd : RepGfHom (F₂.obj Mverma) (F₁.obj Mverma))
    (_hiso₁ : (iso_bwd.comp iso_fwd).EqAsMap (RepGfHom.id _))
    (_hiso₂ : (iso_fwd.comp iso_bwd).EqAsMap (RepGfHom.id _)) :

    AreNatIsoOnGenInfChar lam F₁ F₂ := by


  let T₁ := _hF₁.toThetaFunctorData Δ wg lam F₁
  let T₂ := _hF₂.toThetaFunctorData Δ wg lam F₂
  have hPT₁ := _hF₁.toIsProjectiveThetaFunctor Δ wg lam F₁
  have hPT₂ := _hF₂.toIsProjectiveThetaFunctor Δ wg lam F₂
  have hBij₁₂ := theorem_22_4 Δ wg lam T₁ T₂ hPT₁ hPT₂ Mverma _hMverma
  have hBij₂₁ := theorem_22_4 Δ wg lam T₂ T₁ hPT₂ hPT₁ Mverma _hMverma


  obtain ⟨φ_full, hφ⟩ := hBij₁₂.2 iso_fwd
  obtain ⟨ψ_full, hψ⟩ := hBij₂₁.2 iso_bwd


  have h_comp₁_eval : (ψ_full.comp φ_full).app Mverma = (NatTransData.id F₁).app Mverma := by
    apply (fun ⟨f⟩ ⟨g⟩ h => by congr; exact LieModuleHom.ext h :
      ∀ {M' N' : RepGfObj R 𝔤} (f g : RepGfHom M' N'),
        (∀ x, f.toFun x = g.toFun x) → f = g)
    intro x
    show (ψ_full.app Mverma).toFun ((φ_full.app Mverma).toFun x) =
         (RepGfHom.id _).toFun x
    rw [show (φ_full.app Mverma) = iso_fwd from hφ,
        show (ψ_full.app Mverma) = iso_bwd from hψ]
    exact _hiso₁ x
  have h_comp₂_eval : (φ_full.comp ψ_full).app Mverma = (NatTransData.id F₂).app Mverma := by
    apply (fun ⟨f⟩ ⟨g⟩ h => by congr; exact LieModuleHom.ext h :
      ∀ {M' N' : RepGfObj R 𝔤} (f g : RepGfHom M' N'),
        (∀ x, f.toFun x = g.toFun x) → f = g)
    intro x
    show (φ_full.app Mverma).toFun ((ψ_full.app Mverma).toFun x) =
         (RepGfHom.id _).toFun x
    rw [show (φ_full.app Mverma) = iso_fwd from hφ,
        show (ψ_full.app Mverma) = iso_bwd from hψ]
    exact _hiso₂ x
  have hBij₁₁ := theorem_22_4 Δ wg lam T₁ T₁ hPT₁ hPT₁ Mverma _hMverma
  have hBij₂₂ := theorem_22_4 Δ wg lam T₂ T₂ hPT₂ hPT₂ Mverma _hMverma
  have h_comp₁_eq := hBij₁₁.1 h_comp₁_eval
  have h_comp₂_eq := hBij₂₂.1 h_comp₂_eval


  let phi_hat : NatTransOnGenInfChar lam F₁ F₂ :=
    ⟨fun M _ => φ_full.app M, fun _ _ f => φ_full.naturality f⟩
  let psi_hat : NatTransOnGenInfChar lam F₂ F₁ :=
    ⟨fun M _ => ψ_full.app M, fun _ _ f => ψ_full.naturality f⟩

  refine ⟨phi_hat, psi_hat, ?_, ?_⟩
  ·
    intro M _hGM x


    have hApp : (ψ_full.comp φ_full).app M = (NatTransData.id F₁).app M :=
      congrFun (congrArg NatTransData.app h_comp₁_eq) M
    show (ψ_full.app M).toFun ((φ_full.app M).toFun x) = (RepGfHom.id (F₁.obj M)).toFun x
    exact congrFun (congrArg DFunLike.coe (congrArg RepGfHom.toFun hApp)) x
  ·

    intro M _hGM x
    have hApp : (φ_full.comp ψ_full).app M = (NatTransData.id F₂).app M :=
      congrFun (congrArg NatTransData.app h_comp₂_eq) M
    show (φ_full.app M).toFun ((ψ_full.app M).toFun x) = (RepGfHom.id (F₂.obj M)).toFun x
    exact congrFun (congrArg DFunLike.coe (congrArg RepGfHom.toFun hApp)) x

theorem corollary_22_6_i_areNatIso
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (F₁ F₂ : EndoFunctorData R 𝔤)
    (_hF₁ : IsProjectiveFunctor F₁)
    (_hF₂ : IsProjectiveFunctor F₂)
    (Mverma : RepGfObj R 𝔤)
    (_hMverma : Nonempty (IsVermaModule Δ Mverma.carrier (lam - wg.ρ)))
    (iso_fwd : RepGfHom (F₁.obj Mverma) (F₂.obj Mverma))
    (iso_bwd : RepGfHom (F₂.obj Mverma) (F₁.obj Mverma))
    (_hiso₁ : (iso_bwd.comp iso_fwd).EqAsMap (RepGfHom.id _))
    (_hiso₂ : (iso_fwd.comp iso_bwd).EqAsMap (RepGfHom.id _)) :
    AreNatIso F₁ F₂ := by

  let T₁ := _hF₁.toThetaFunctorData Δ wg lam F₁
  let T₂ := _hF₂.toThetaFunctorData Δ wg lam F₂
  have hPT₁ := _hF₁.toIsProjectiveThetaFunctor Δ wg lam F₁
  have hPT₂ := _hF₂.toIsProjectiveThetaFunctor Δ wg lam F₂
  have hBij₁₂ := theorem_22_4 Δ wg lam T₁ T₂ hPT₁ hPT₂ Mverma _hMverma
  have hBij₂₁ := theorem_22_4 Δ wg lam T₂ T₁ hPT₂ hPT₁ Mverma _hMverma
  obtain ⟨φ_full, hφ⟩ := hBij₁₂.2 iso_fwd
  obtain ⟨ψ_full, hψ⟩ := hBij₂₁.2 iso_bwd

  have h_comp₁_eval : (ψ_full.comp φ_full).app Mverma = (NatTransData.id F₁).app Mverma := by
    apply (fun ⟨f⟩ ⟨g⟩ h => by congr; exact LieModuleHom.ext h :
      ∀ {M' N' : RepGfObj R 𝔤} (f g : RepGfHom M' N'),
        (∀ x, f.toFun x = g.toFun x) → f = g)
    intro x
    show (ψ_full.app Mverma).toFun ((φ_full.app Mverma).toFun x) =
         (RepGfHom.id _).toFun x
    rw [show (φ_full.app Mverma) = iso_fwd from hφ,
        show (ψ_full.app Mverma) = iso_bwd from hψ]
    exact _hiso₁ x
  have h_comp₂_eval : (φ_full.comp ψ_full).app Mverma = (NatTransData.id F₂).app Mverma := by
    apply (fun ⟨f⟩ ⟨g⟩ h => by congr; exact LieModuleHom.ext h :
      ∀ {M' N' : RepGfObj R 𝔤} (f g : RepGfHom M' N'),
        (∀ x, f.toFun x = g.toFun x) → f = g)
    intro x
    show (φ_full.app Mverma).toFun ((ψ_full.app Mverma).toFun x) =
         (RepGfHom.id _).toFun x
    rw [show (φ_full.app Mverma) = iso_fwd from hφ,
        show (ψ_full.app Mverma) = iso_bwd from hψ]
    exact _hiso₂ x
  have hBij₁₁ := theorem_22_4 Δ wg lam T₁ T₁ hPT₁ hPT₁ Mverma _hMverma
  have hBij₂₂ := theorem_22_4 Δ wg lam T₂ T₂ hPT₂ hPT₂ Mverma _hMverma

  have h_comp₁_eq := hBij₁₁.1 h_comp₁_eval
  have h_comp₂_eq := hBij₂₂.1 h_comp₂_eval

  refine ⟨φ_full, ψ_full, ?_, ?_⟩
  ·
    intro M x
    have hApp : (ψ_full.comp φ_full).app M = (NatTransData.id F₁).app M :=
      congrFun (congrArg NatTransData.app h_comp₁_eq) M
    exact congrFun (congrArg DFunLike.coe (congrArg RepGfHom.toFun hApp)) x
  ·
    intro M x
    have hApp : (φ_full.comp ψ_full).app M = (NatTransData.id F₂).app M :=
      congrFun (congrArg NatTransData.app h_comp₂_eq) M
    exact congrFun (congrArg DFunLike.coe (congrArg RepGfHom.toFun hApp)) x

theorem idempotent_lift_gives_functor_decomp
    (R : Type u) [CommRing R] (𝔤 : Type u) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (F : EndoFunctorData R 𝔤) {n : ℕ}
    (E_i : Fin n → NatTransData F F)

    (_hIdem : ∀ i, ((E_i i).comp (E_i i)).EqPointwise (E_i i))

    (M₀ : RepGfObj R 𝔤) (summands : Fin n → RepGfObj R 𝔤)
    (_hDecompObj : IsDirectSumDecompObj (F.obj M₀) summands)


    (_hEvalCompat : ∀ i, ∀ x : (F.obj M₀).carrier,
      ((E_i i).app M₀).toFun x =
      (_hDecompObj.choose i).toFun ((_hDecompObj.choose_spec.choose i).toFun x))


    (_hComplete : ∀ (M : RepGfObj R 𝔤) (x : (F.obj M).carrier),
      x = Finset.univ.sum (fun i => ((E_i i).app M).toFun x)) :
    ∃ (F_i : Fin n → EndoFunctorData R 𝔤),
      (∀ i, (F_i i).obj M₀ = summands i) ∧
      IsDirectSumDecomp F F_i := by


  let sec_obj := _hDecompObj.choose
  let ret_obj := _hDecompObj.choose_spec.choose
  have hRS_obj := _hDecompObj.choose_spec.choose_spec.1

  have hIdemElt : ∀ i (M : RepGfObj R 𝔤) (x : (F.obj M).carrier),
      ((E_i i).app M).toFun (((E_i i).app M).toFun x) = ((E_i i).app M).toFun x :=
    fun i M x => _hIdem i M x

  classical

  let rangeObj : (i : Fin n) → (M : RepGfObj R 𝔤) → RepGfObj R 𝔤 := fun i M =>
    ⟨↥(((E_i i).app M).toFun.range), inferInstance, inferInstance, inferInstance, inferInstance⟩

  let Fi_obj : (i : Fin n) → RepGfObj R 𝔤 → RepGfObj R 𝔤 := fun i M =>
    if M = M₀ then summands i else rangeObj i M

  have hFi_M₀ : ∀ i, Fi_obj i M₀ = summands i := fun i => if_pos rfl


  suffices hMain : ∃ (F_i : Fin n → EndoFunctorData R 𝔤),
      (∀ i, (F_i i).obj M₀ = summands i) ∧


      (∀ i, ∃ (incl : NatTransData (F_i i) F) (proj : NatTransData F (F_i i)),
        ((proj.comp incl).EqPointwise (NatTransData.id (F_i i))) ∧
        (∀ M x, (incl.app M).toFun ((proj.app M).toFun x) = ((E_i i).app M).toFun x)) by
    obtain ⟨F_i, hObj, hSplit⟩ := hMain
    refine ⟨F_i, hObj, ?_⟩

    let incl_i : ∀ i, NatTransData (F_i i) F := fun i => (hSplit i).choose
    let proj_i : ∀ i, NatTransData F (F_i i) := fun i => (hSplit i).choose_spec.choose
    have hRetract : ∀ i, ((proj_i i).comp (incl_i i)).EqPointwise (NatTransData.id (F_i i)) :=
      fun i => (hSplit i).choose_spec.choose_spec.1
    have hInclProj : ∀ i (M : RepGfObj R 𝔤) (x : (F.obj M).carrier),
        ((incl_i i).app M).toFun (((proj_i i).app M).toFun x) = ((E_i i).app M).toFun x :=
      fun i => (hSplit i).choose_spec.choose_spec.2
    exact ⟨incl_i, proj_i, hRetract,
      fun M x => by


        simp only [RepGfHom.id, LieModuleHom.coe_id, id_eq]
        conv_rhs => arg 2; ext i; rw [hInclProj i M x]
        exact _hComplete M x⟩


  let eqToRepGfHom : ∀ {A B : RepGfObj R 𝔤}, A = B → RepGfHom A B :=
    fun h => h ▸ RepGfHom.id _
  have eqToRepGfHom_symm : ∀ {A B : RepGfObj R 𝔤} (h : A = B) (x : A.carrier),
      (eqToRepGfHom h.symm).toFun ((eqToRepGfHom h).toFun x) = x := by
    intro A B h; subst h; intro x; rfl
  have eqToRepGfHom_symm' : ∀ {A B : RepGfObj R 𝔤} (h : A = B) (x : B.carrier),
      (eqToRepGfHom h).toFun ((eqToRepGfHom h.symm).toFun x) = x := by
    intro A B h; subst h; intro x; rfl


  let myRangeRestrict' : ∀ (i : Fin n) (M : RepGfObj R 𝔤),
      @LieModuleHom R 𝔤 (F.obj M).carrier ↥(((E_i i).app M).toFun.range)
        _ _ (F.obj M).inst_addCommGroup _ (F.obj M).inst_module _
        (F.obj M).inst_lieRingModule _ := fun i M =>
    { toLinearMap := (((E_i i).app M).toFun : (F.obj M).carrier →ₗ[R] (F.obj M).carrier).rangeRestrict
      map_lie' := fun {x m} => by
        apply Subtype.ext
        simp only [LieSubmodule.coe_bracket]
        change ((E_i i).app M).toFun ⁅x, m⁆ = ⁅x, ((E_i i).app M).toFun m⁆
        exact ((E_i i).app M).toFun.map_lie x m }


  have rangeRestrict_incl : ∀ i M (x : (F.obj M).carrier),
      ((((E_i i).app M).toFun.range).incl (myRangeRestrict' i M x) : (F.obj M).carrier) =
      ((E_i i).app M).toFun x := by intro i M x; rfl


  have rangeRestrict_idem : ∀ i M (y : ↥(((E_i i).app M).toFun.range)),
      myRangeRestrict' i M (((E_i i).app M).toFun.range.incl y) = y := by
    intro i M y
    apply Subtype.ext
    change ((E_i i).app M).toFun ↑y = ↑y
    obtain ⟨z, hz⟩ := y.prop
    rw [← hz, hIdemElt i M z]


  let incl_at : ∀ (i : Fin n) (M : RepGfObj R 𝔤), RepGfHom (Fi_obj i M) (F.obj M) :=
    fun i M => if hM : M = M₀ then by
      subst hM

      exact (sec_obj i).comp (eqToRepGfHom (hFi_M₀ i))
    else by

      have h_ne : Fi_obj i M = rangeObj i M := if_neg hM
      exact ⟨(((E_i i).app M).toFun.range.incl).comp (eqToRepGfHom h_ne).toFun⟩


  let proj_at : ∀ (i : Fin n) (M : RepGfObj R 𝔤), RepGfHom (F.obj M) (Fi_obj i M) :=
    fun i M => if hM : M = M₀ then by
      subst hM
      exact (eqToRepGfHom (hFi_M₀ i).symm).comp (ret_obj i)
    else by
      have h_ne : Fi_obj i M = rangeObj i M := if_neg hM
      exact ⟨((eqToRepGfHom h_ne.symm).toFun).comp (myRangeRestrict' i M)⟩


  have incl_proj_eq : ∀ i M (x : (F.obj M).carrier),
      (incl_at i M).toFun ((proj_at i M).toFun x) = ((E_i i).app M).toFun x := by
    intro i M x
    by_cases hM : M = M₀
    · subst hM
      simp only [incl_at, proj_at, dif_pos rfl]
      simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply]
      rw [eqToRepGfHom_symm' (hFi_M₀ i)]
      exact (_hEvalCompat i x).symm
    · simp only [incl_at, proj_at, dif_neg hM]
      simp only [LieModuleHom.coe_comp, Function.comp_apply]
      rw [eqToRepGfHom_symm' (show Fi_obj i M = rangeObj i M from if_neg hM)]
      rfl


  have proj_incl_id : ∀ i M (x : (Fi_obj i M).carrier),
      (proj_at i M).toFun ((incl_at i M).toFun x) = x := by
    intro i M x
    by_cases hM : M = M₀
    · subst hM
      simp only [incl_at, proj_at, dif_pos rfl]
      simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply]
      rw [show (ret_obj i).toFun ((sec_obj i).toFun ((eqToRepGfHom (hFi_M₀ i)).toFun x)) =
          (eqToRepGfHom (hFi_M₀ i)).toFun x from hRS_obj i _]
      exact eqToRepGfHom_symm (hFi_M₀ i) x
    · simp only [incl_at, proj_at, dif_neg hM]
      simp only [LieModuleHom.coe_comp, Function.comp_apply]
      have h_ne : Fi_obj i M = rangeObj i M := if_neg hM


      conv_rhs => rw [← eqToRepGfHom_symm h_ne x]
      congr 1
      exact rangeRestrict_idem i M ((eqToRepGfHom h_ne).toFun x)


  have E_i_nat : ∀ i {M N : RepGfObj R 𝔤} (f : RepGfHom M N) (x : (F.obj M).carrier),
      ((E_i i).app N).toFun ((F.mapHom f).toFun x) =
      (F.mapHom f).toFun (((E_i i).app M).toFun x) := by
    intro i M N f x
    have := (E_i i).naturality f x
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at this
    exact this


  have E_i_fixes_incl : ∀ i M (x : (Fi_obj i M).carrier),
      ((E_i i).app M).toFun ((incl_at i M).toFun x) = (incl_at i M).toFun x := by
    intro i M x
    rw [← incl_proj_eq i M ((incl_at i M).toFun x), proj_incl_id]


  let mapHom_i : ∀ (i : Fin n) {M N : RepGfObj R 𝔤},
      RepGfHom M N → RepGfHom (Fi_obj i M) (Fi_obj i N) := fun i {M} {N} f =>
    (proj_at i N).comp ((F.mapHom f).comp (incl_at i M))


  refine ⟨fun i => ⟨Fi_obj i, @mapHom_i i, ?_, ?_⟩, hFi_M₀, fun i => ?_⟩


  · intro M x


    simp only [RepGfHom.EqAsMap, mapHom_i, RepGfHom.comp, LieModuleHom.coe_comp,
      Function.comp_apply, RepGfHom.id, LieModuleHom.coe_id, id_eq]
    have hFid := F.map_id M ((incl_at i M).toFun x)
    simp only [RepGfHom.id, LieModuleHom.coe_id, id_eq] at hFid
    rw [hFid]
    exact proj_incl_id i M x


  · intro M N P f g x
    simp only [RepGfHom.EqAsMap, mapHom_i, RepGfHom.comp, LieModuleHom.coe_comp,
      Function.comp_apply]


    have hFcomp := F.map_comp f g ((incl_at i M).toFun x)
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hFcomp
    rw [hFcomp]


    congr 1


    rw [incl_proj_eq]


    symm; rw [E_i_nat]


    congr 2
    exact E_i_fixes_incl i M x


  · refine ⟨⟨incl_at i, ?_⟩, ⟨proj_at i, ?_⟩, ?_, ?_⟩


    · intro M₁ M₂ f x
      simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply, mapHom_i]


      rw [incl_proj_eq]


      rw [E_i_nat]
      congr 1
      exact E_i_fixes_incl i M₁ x


    · intro M₁ M₂ f x
      simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply, mapHom_i]


      rw [show (incl_at i M₁).toFun ((proj_at i M₁).toFun x) =
          ((E_i i).app M₁).toFun x from incl_proj_eq i M₁ x]


      conv_lhs => rw [show (proj_at i M₂).toFun ((F.mapHom f).toFun x) =
          (proj_at i M₂).toFun (((E_i i).app M₂).toFun ((F.mapHom f).toFun x)) from by
        rw [← incl_proj_eq i M₂ ((F.mapHom f).toFun x)]
        rw [proj_incl_id]]

      rw [E_i_nat]


    · intro M x
      simp only [NatTransData.comp, NatTransData.id, RepGfHom.comp, RepGfHom.id, RepGfHom.EqAsMap,
        LieModuleHom.coe_comp, Function.comp_apply, LieModuleHom.coe_id, id_eq]
      exact proj_incl_id i M x


    · intro M x
      simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply]
      exact incl_proj_eq i M x

theorem isDirectSummand_trans
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (A B C : EndoFunctorData R 𝔤)
    (h1 : IsDirectSummand A B) (h2 : IsDirectSummand B C) :
    IsDirectSummand A C := by
  obtain ⟨i₁, p₁, hp₁⟩ := h1
  obtain ⟨i₂, p₂, hp₂⟩ := h2
  exact ⟨i₂.comp i₁, p₁.comp p₂, fun M x => by
    simp only [NatTransData.comp, RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply,
               NatTransData.EqPointwise, RepGfHom.EqAsMap, NatTransData.id, RepGfHom.id] at *
    have h2' := hp₂ M ((i₁.app M).toFun x)
    rw [h2']
    exact hp₁ M x⟩

theorem projective_of_direct_summand
    (R : Type u) [CommRing R] (𝔤 : Type u) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (F : EndoFunctorData R 𝔤) (G : EndoFunctorData R 𝔤)
    (_hF : IsProjectiveFunctor F)
    (_hSummand : IsDirectSummand G F) : IsProjectiveFunctor G where
  exists_tensor_summand := by
    obtain ⟨FV, hFV⟩ := _hF.exists_tensor_summand
    exact ⟨FV, isDirectSummand_trans G F FV.functor _hSummand hFV⟩

theorem isDirectSummand_of_isDirectSumDecomp
    (F : EndoFunctorData R 𝔤) {n : ℕ}
    (F_i : Fin n → EndoFunctorData R 𝔤)
    (h : IsDirectSumDecomp F F_i) (i : Fin n) :
    IsDirectSummand (F_i i) F := by
  obtain ⟨sec, ret, hRS, _⟩ := h
  exact ⟨sec i, ret i, hRS i⟩

theorem corollary_22_6_ii
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (F : EndoFunctorData R 𝔤)
    (_hF : IsProjectiveFunctor F)
    (Mverma : RepGfObj R 𝔤)
    (_hMverma : Nonempty (IsVermaModule Δ Mverma.carrier (lam - wg.ρ)))
    (n : ℕ) (summands : Fin n → RepGfObj R 𝔤)
    (_hDecomp : IsDirectSumDecompObj (F.obj Mverma) summands) :
    ∃ (F_i : Fin n → EndoFunctorData R 𝔤),
      (∀ i, IsProjectiveFunctor (F_i i)) ∧
      (∀ i, (F_i i).obj Mverma = summands i) ∧
      IsDirectSumDecomp F F_i := by

  let T := _hF.toThetaFunctorData Δ wg lam F
  have hPT := _hF.toIsProjectiveThetaFunctor Δ wg lam F
  have hBij := theorem_22_4 Δ wg lam T T hPT hPT Mverma _hMverma

  let sec_obj := _hDecomp.choose
  let ret_obj := _hDecomp.choose_spec.choose
  have hRS_obj := _hDecomp.choose_spec.choose_spec.1

  let e_i : Fin n → RepGfHom (F.obj Mverma) (F.obj Mverma) :=
    fun i => (sec_obj i).comp (ret_obj i)

  let E_i : Fin n → NatTransData F F := fun i => (hBij.2 (e_i i)).choose
  have hE_eval : ∀ i, (E_i i).app Mverma = e_i i :=
    fun i => (hBij.2 (e_i i)).choose_spec

  have RepGfHom_ext : ∀ {M' N' : RepGfObj R 𝔤} (f g : RepGfHom M' N'),
      (∀ x, f.toFun x = g.toFun x) → f = g := by
    intro M' N' ⟨f⟩ ⟨g⟩ h; congr; exact LieModuleHom.ext h


  have hE_idem : ∀ i, ((E_i i).comp (E_i i)).EqPointwise (E_i i) := by
    intro i

    have h_ei_idem : ∀ x, (e_i i).toFun ((e_i i).toFun x) = (e_i i).toFun x := by
      intro x
      show (sec_obj i).toFun ((ret_obj i).toFun ((sec_obj i).toFun ((ret_obj i).toFun x))) =
           (sec_obj i).toFun ((ret_obj i).toFun x)
      rw [hRS_obj i ((ret_obj i).toFun x)]

    have h_comp_eval : ((E_i i).comp (E_i i)).app Mverma = (E_i i).app Mverma := by
      apply RepGfHom_ext; intro x
      show ((E_i i).app Mverma).toFun (((E_i i).app Mverma).toFun x) =
           ((E_i i).app Mverma).toFun x
      rw [hE_eval i]; exact h_ei_idem x

    have h_eq := hBij.1 h_comp_eval

    intro M x
    have hApp : ((E_i i).comp (E_i i)).app M = (E_i i).app M :=
      congrFun (congrArg NatTransData.app h_eq) M
    exact congrFun (congrArg DFunLike.coe (congrArg RepGfHom.toFun hApp)) x

  have hEvalCompat : ∀ i, ∀ x : (F.obj Mverma).carrier,
      ((E_i i).app Mverma).toFun x =
      (_hDecomp.choose i).toFun ((_hDecomp.choose_spec.choose i).toFun x) := by
    intro i x
    have h := congrFun (congrArg DFunLike.coe (congrArg RepGfHom.toFun (hE_eval i))) x
    exact h


  have hCompleteAtVerma : ∀ x : (F.obj Mverma).carrier,
      (RepGfHom.id (F.obj Mverma)).toFun x =
      Finset.univ.sum (fun i => ((E_i i).app Mverma).toFun x) := by
    intro x

    simp only [RepGfHom.id, LieModuleHom.coe_id, id_eq]

    conv_rhs => arg 2; ext i; rw [hEvalCompat i x]

    exact _hDecomp.choose_spec.choose_spec.2 x


  have hComplete_sum_eq_id : ∀ (M : RepGfObj R 𝔤) (x : (F.obj M).carrier),
      x = Finset.univ.sum (fun i => ((E_i i).app M).toFun x) := by


    have lieModHom_sum_apply : ∀ {A B : RepGfObj R 𝔤}
        (fs : Fin n → (A.carrier →ₗ⁅R, 𝔤⁆ B.carrier)) (x : A.carrier),
        (Finset.univ.sum fs) x = Finset.univ.sum (fun i => fs i x) := by
      intro A B fs y
      classical
      induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
      | empty => exact LieModuleHom.zero_apply y
      | insert a s ha ih =>
        rw [Finset.sum_insert ha, LieModuleHom.add_apply, ih, Finset.sum_insert ha]

    let sumE : NatTransData F F := {
      app := fun M => ⟨Finset.univ.sum (fun i => ((E_i i).app M).toFun)⟩
      naturality := fun {M₁ M₂} f x => by

        simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply]
        rw [lieModHom_sum_apply, lieModHom_sum_apply]

        rw [map_sum (F.mapHom f).toFun]

        exact Finset.sum_congr rfl (fun i _ => (E_i i).naturality f x)
    }

    have hSumAtVerma : sumE.app Mverma = (NatTransData.id F).app Mverma := by
      apply RepGfHom_ext; intro x
      show (Finset.univ.sum (fun i => ((E_i i).app Mverma).toFun)) x =
           (RepGfHom.id (F.obj Mverma)).toFun x
      rw [lieModHom_sum_apply]
      exact (hCompleteAtVerma x).symm

    have hSumEq : sumE = NatTransData.id F := hBij.1 hSumAtVerma

    intro M x
    have hApp : sumE.app M = (NatTransData.id F).app M :=
      congrFun (congrArg NatTransData.app hSumEq) M
    have hx := congrFun (congrArg DFunLike.coe (congrArg RepGfHom.toFun hApp)) x

    simp only [NatTransData.id, RepGfHom.id, LieModuleHom.coe_id, id_eq] at hx


    have h_sum_unfold : (sumE.app M).toFun x = ∑ i, ((E_i i).app M).toFun x :=
      lieModHom_sum_apply (fun i => ((E_i i).app M).toFun) x
    exact hx.symm.trans h_sum_unfold

  obtain ⟨F_i, hObj, hDecomp⟩ :=
    idempotent_lift_gives_functor_decomp R 𝔤 F E_i hE_idem Mverma summands _hDecomp hEvalCompat
      hComplete_sum_eq_id

  refine ⟨F_i, fun i => ?_, hObj, hDecomp⟩
  exact projective_of_direct_summand R 𝔤 F (F_i i) _hF
    (isDirectSummand_of_isDirectSumDecomp F F_i hDecomp i)

lemma areNatIso_refl (F : EndoFunctorData R 𝔤) : AreNatIso F F :=
  ⟨NatTransData.id F, NatTransData.id F,
    fun M x => by simp [NatTransData.comp, NatTransData.id, RepGfHom.comp, RepGfHom.id],
    fun M x => by simp [NatTransData.comp, NatTransData.id, RepGfHom.comp, RepGfHom.id]⟩

theorem corollary_22_6_iii
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (theta : Δ.𝔥 →ₗ[R] R)
    (H : ThetaFunctorData R 𝔤 Δ wg theta)
    (_hH : IsProjectiveThetaFunctor H) :
    ∃ (F : EndoFunctorData R 𝔤) (hF : IsProjectiveFunctor F),
      AreNatIsoTheta H (hF.toThetaFunctorData Δ wg theta) := by

  obtain ⟨FV, hDS⟩ := _hH.exists_tensor_summand


  have hF : IsProjectiveFunctor H.baseFunctor :=
    projective_of_direct_summand R 𝔤 FV.functor H.baseFunctor
      (tensor_functor_is_projective FV) hDS
  exact ⟨H.baseFunctor, hF, areNatIso_refl H.baseFunctor⟩

theorem corollary_22_6
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) :

    (∀ (F₁ F₂ : EndoFunctorData R 𝔤)
       (_hF₁ : IsProjectiveFunctor F₁) (_hF₂ : IsProjectiveFunctor F₂)
       (Mverma : RepGfObj R 𝔤)
       (_hMverma : Nonempty (IsVermaModule Δ Mverma.carrier (lam - wg.ρ)))
       (iso_fwd : RepGfHom (F₁.obj Mverma) (F₂.obj Mverma))
       (iso_bwd : RepGfHom (F₂.obj Mverma) (F₁.obj Mverma))
       (_hiso₁ : (iso_bwd.comp iso_fwd).EqAsMap (RepGfHom.id _))
       (_hiso₂ : (iso_fwd.comp iso_bwd).EqAsMap (RepGfHom.id _)),
       AreNatIsoOnGenInfChar lam F₁ F₂)
    ∧

    (∀ (F : EndoFunctorData R 𝔤) (_hF : IsProjectiveFunctor F)
       (Mverma : RepGfObj R 𝔤)
       (_hMverma : Nonempty (IsVermaModule Δ Mverma.carrier (lam - wg.ρ)))
       (n : ℕ) (summands : Fin n → RepGfObj R 𝔤)
       (_hDecomp : IsDirectSumDecompObj (F.obj Mverma) summands),
       ∃ (F_i : Fin n → EndoFunctorData R 𝔤),
         (∀ i, IsProjectiveFunctor (F_i i)) ∧
         (∀ i, (F_i i).obj Mverma = summands i) ∧
         IsDirectSumDecomp F F_i)
    ∧

    (∀ (H : ThetaFunctorData R 𝔤 Δ wg lam) (_hH : IsProjectiveThetaFunctor H),
       ∃ (F : EndoFunctorData R 𝔤) (hF : IsProjectiveFunctor F),
         AreNatIsoTheta H (hF.toThetaFunctorData Δ wg lam)) := by
  exact ⟨
    fun F₁ F₂ hF₁ hF₂ Mv hMv fwd bwd h₁ h₂ =>
      corollary_22_6_i Δ wg lam F₁ F₂ hF₁ hF₂ Mv hMv fwd bwd h₁ h₂,
    fun F hF Mv hMv n sums hD =>
      corollary_22_6_ii Δ wg lam F hF Mv hMv n sums hD,
    fun H hH =>
      corollary_22_6_iii Δ wg lam H hH⟩

theorem krullSchmidt_repgf
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (M : RepGfObj R 𝔤) :
    ∃ (n : ℕ) (summands : Fin n → RepGfObj R 𝔤),
      IsDirectSumDecompObj M summands ∧
      (∀ i, IsIndecomposableObj (summands i)) := by sorry

theorem indecomposable_from_corollary
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (F : EndoFunctorData R 𝔤)
    (_hF : IsProjectiveFunctor F)
    (Mverma : RepGfObj R 𝔤)
    (_hMverma : Nonempty (IsVermaModule Δ Mverma.carrier (lam - wg.ρ)))
    (n : ℕ) (summands : Fin n → RepGfObj R 𝔤)
    (_hDecomp : IsDirectSumDecompObj (F.obj Mverma) summands)
    (_hSummandsIndecomp : ∀ i, IsIndecomposableObj (summands i))
    (F_i : Fin n → EndoFunctorData R 𝔤)
    (_hFi_proj : ∀ i, IsProjectiveFunctor (F_i i))
    (_hFi_eval : ∀ i, (F_i i).obj Mverma = summands i)
    (_hFi_decomp : IsDirectSumDecomp F F_i)
    (i : Fin n) :
    IsIndecomposable (F_i i) := by


  intro e he_idem

  have h_eval_i : (F_i i).obj Mverma = summands i := _hFi_eval i
  have h_indecomp_at_M : IsIndecomposableObj ((F_i i).obj Mverma) :=
    h_eval_i ▸ _hSummandsIndecomp i

  have h_e_idem_at_M : ∀ x, (e.app Mverma).toFun ((e.app Mverma).toFun x) =
      (e.app Mverma).toFun x := by
    intro x
    have := he_idem Mverma x
    simp only [NatTransData.comp,
               RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at this

    exact this

  have h_or := h_indecomp_at_M (e.app Mverma) h_e_idem_at_M

  let Ti := (_hFi_proj i).toThetaFunctorData Δ wg lam (F_i i)
  have hPTi := (_hFi_proj i).toIsProjectiveThetaFunctor Δ wg lam (F_i i)
  have hBij := theorem_22_4 Δ wg lam Ti Ti hPTi hPTi Mverma _hMverma

  cases h_or with
  | inl h_id =>

    left

    have h_eq_at_M : evalAtVerma Ti Ti Mverma e = evalAtVerma Ti Ti Mverma (NatTransData.id (F_i i)) := by

      show e.app Mverma = (NatTransData.id (F_i i)).app Mverma
      have h_toFun_eq : (e.app Mverma).toFun = ((NatTransData.id (F_i i)).app Mverma).toFun := by
        apply LieModuleHom.ext
        intro x
        simp only [NatTransData.id, RepGfHom.id, LieModuleHom.id_apply]
        exact h_id x
      calc e.app Mverma
          = ⟨(e.app Mverma).toFun⟩ := by cases (e.app Mverma) with | mk f => rfl
        _ = ⟨((NatTransData.id (F_i i)).app Mverma).toFun⟩ := by rw [h_toFun_eq]
        _ = (NatTransData.id (F_i i)).app Mverma := by cases ((NatTransData.id (F_i i)).app Mverma) with | mk f => rfl


    have h_eq := hBij.1 h_eq_at_M

    intro M
    simp only [RepGfHom.EqAsMap]
    intro x
    have : e.app M = (NatTransData.id (F_i i)).app M := congrFun (congrArg NatTransData.app h_eq) M
    simp only [this, NatTransData.id, RepGfHom.id, LieModuleHom.id_apply]
  | inr h_zero =>

    right

    let zero_nt : NatTransData (F_i i) (F_i i) :=
      { app := fun M => ⟨0⟩
        naturality := fun f x => by simp [RepGfHom.comp] }
    have h_eq_at_M : evalAtVerma Ti Ti Mverma e = evalAtVerma Ti Ti Mverma zero_nt := by
      show e.app Mverma = zero_nt.app Mverma
      have h_toFun_eq : (e.app Mverma).toFun = (zero_nt.app Mverma).toFun := by
        apply LieModuleHom.ext
        intro x
        simp only [zero_nt, LieModuleHom.zero_apply]
        exact h_zero x
      calc e.app Mverma
          = ⟨(e.app Mverma).toFun⟩ := by cases (e.app Mverma) with | mk f => rfl
        _ = ⟨(zero_nt.app Mverma).toFun⟩ := by rw [h_toFun_eq]
        _ = zero_nt.app Mverma := by cases (zero_nt.app Mverma) with | mk f => rfl

    have h_eq := hBij.1 h_eq_at_M
    intro M x
    have : e.app M = zero_nt.app M := congrFun (congrArg NatTransData.app h_eq) M
    simp only [this, zero_nt, LieModuleHom.zero_apply]

lemma isDirectSumDecomp_to_gen
    (F : EndoFunctorData R 𝔤) {n : ℕ}
    (F_i : Fin n → EndoFunctorData R 𝔤)
    (h : IsDirectSumDecomp F F_i) :
    @IsDirectSumDecompGen R _ 𝔤 _ _ F (ULift.{u, 0} (Fin n)) (ULift.fintype _)
      (fun j => F_i j.down) := by
  obtain ⟨section_i, retract_i, hRetSec, hSum⟩ := h
  refine ⟨fun j => section_i j.down, fun j => retract_i j.down,
          fun j => hRetSec j.down, ?_⟩
  intro M x
  rw [hSum M x]
  symm
  exact Finset.sum_equiv (Equiv.ulift) (by simp) (by intro i _; rfl)

theorem proposition_22_7_i
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (F : EndoFunctorData R 𝔤)
    (_hF : IsProjectiveFunctor F) :
    ∃ (ι : Type u) (_ : Fintype ι) (F_i : ι → EndoFunctorData R 𝔤),
      (∀ i, IsProjectiveFunctor (F_i i)) ∧
      (∀ i, IsIndecomposable (F_i i)) ∧
      IsDirectSumDecompGen F F_i := by


  set lam := wg.ρ with lam_def
  obtain ⟨Mlam, instACG, instMod, instLRM, instLM, ⟨hVM⟩⟩ :=
    verma_module_exists Δ (lam - wg.ρ)
  let Mverma : RepGfObj R 𝔤 := ⟨Mlam, instACG, instMod, instLRM, instLM⟩
  have hMverma : Nonempty (IsVermaModule Δ Mverma.carrier (lam - wg.ρ)) := ⟨hVM⟩


  obtain ⟨N, summands, hKS, hSummandsIndecomp⟩ := krullSchmidt_repgf (F.obj Mverma)


  obtain ⟨F_i, hFi_proj, hFi_eval, hFi_decomp⟩ :=
    corollary_22_6_ii Δ wg lam F _hF Mverma hMverma N summands hKS

  refine ⟨ULift.{u, 0} (Fin N), ULift.fintype _, fun j => F_i j.down, ?_, ?_, ?_⟩

  · intro ⟨i⟩; exact hFi_proj i

  · intro ⟨i⟩
    exact indecomposable_from_corollary Δ wg lam F _hF Mverma hMverma
      N summands hKS hSummandsIndecomp F_i hFi_proj hFi_eval hFi_decomp i

  · exact isDirectSumDecomp_to_gen F F_i hFi_decomp

theorem tensor_finiteDim_categoryO_commring
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {V : Type*} [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V]
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M)
    {VM : Type*} [AddCommGroup VM] [Module R VM]
    [LieRingModule 𝔤 VM] [LieModule R 𝔤 VM]
    (tensor_iso : VM ≃ₗ⁅R, 𝔤⁆ TensorProduct R V M) :
    IsCategoryO Δ rd VM :=
  tensor_finiteDim_categoryO hM tensor_iso

theorem tensor_functor_preserves_categoryO
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (FV : TensorFunctorData R 𝔤)
    (M : RepGfObj R 𝔤)
    (hMO : IsCategoryO Δ rd M.carrier) :
    IsCategoryO Δ rd (FV.functor.obj M).carrier := by
  obtain ⟨iso⟩ := FV.tensor_obj_spec M
  exact @tensor_finiteDim_categoryO_commring R _ 𝔤 _ _ Δ rd
    FV.V FV.inst_addCommGroupV FV.inst_moduleV FV.inst_lieRingModuleV FV.inst_lieModuleV
    FV.inst_finiteDimV
    M.carrier M.inst_addCommGroup M.inst_module M.inst_lieRingModule M.inst_lieModule
    hMO
    (FV.functor.obj M).carrier (FV.functor.obj M).inst_addCommGroup
    (FV.functor.obj M).inst_module (FV.functor.obj M).inst_lieRingModule
    (FV.functor.obj M).inst_lieModule
    iso

theorem tensor_functor_preserves_projectiveInO
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (FV : TensorFunctorData R 𝔤)
    (M : RepGfObj R 𝔤)
    (hMO : IsCategoryO Δ rd M.carrier)
    (hMproj : IsProjectiveInO rd M.carrier hMO)
    (hFMO : IsCategoryO Δ rd (FV.functor.obj M).carrier) :
    IsProjectiveInO rd (FV.functor.obj M).carrier hFMO := by
  obtain ⟨iso⟩ := FV.tensor_obj_spec M
  letI := FV.inst_addCommGroupV
  letI := FV.inst_moduleV
  letI := FV.inst_lieRingModuleV
  letI := FV.inst_lieModuleV
  letI := FV.inst_finiteDimV
  letI := FV.inst_freeV
  exact tensor_projective_in_O (V := FV.V) hMO hMproj hFMO iso

theorem direct_summand_preserves_categoryO
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (F G : EndoFunctorData R 𝔤)
    (_hDS : IsDirectSummand F G)
    (M : RepGfObj R 𝔤)
    (hGMO : IsCategoryO Δ rd (G.obj M).carrier) :
    IsCategoryO Δ rd (F.obj M).carrier := by

  obtain ⟨i_nt, p_nt, hpi⟩ := _hDS

  let sec := (i_nt.app M).toFun
  let ret := (p_nt.app M).toFun
  have hret_sec : ∀ x : (F.obj M).carrier, ret (sec x) = x := hpi M
  exact {
    finitely_generated := by
      obtain ⟨S, hS⟩ := hGMO.finitely_generated
      classical
      refine ⟨S.image ret, ?_⟩
      rw [eq_top_iff]; intro x _
      rw [← hret_sec x]
      have hmem : sec x ∈ LieSubmodule.lieSpan R 𝔤 (↑S : Set (G.obj M).carrier) := by
        rw [hS]; trivial
      apply LieSubmodule.lieSpan_induction R 𝔤 (p := fun y _ =>
          ret y ∈ LieSubmodule.lieSpan R 𝔤 (↑(S.image ret) : Set (F.obj M).carrier))
      · intro m hm
        exact LieSubmodule.subset_lieSpan (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨m, hm, rfl⟩))
      · simp
      · intro a b _ _ ih1 ih2; rw [map_add]; exact add_mem ih1 ih2
      · intro r a _ ih; rw [map_smul]; exact SMulMemClass.smul_mem r ih
      · intro l a _ ih; rw [LieModuleHom.map_lie]; exact LieSubmodule.lie_mem _ ih
      · exact hmem
    weight_decomp := by
      intro m
      obtain ⟨S, v, hv⟩ := hGMO.weight_decomp (sec m)
      refine ⟨S, fun μ => ⟨ret (v μ), fun h => ?_⟩, ?_⟩
      ·
        have hv_wt := (v μ).property h
        rw [← LieModuleHom.map_lie, hv_wt, map_smul]
      ·
        conv_lhs => rw [← hret_sec m, hv]
        rw [map_sum]
    weight_bound := by
      obtain ⟨bds, hbds⟩ := hGMO.weight_bound
      refine ⟨bds, fun μ hμ => ?_⟩
      apply hbds μ


      unfold weights at hμ ⊢
      simp only [Set.mem_setOf_eq] at hμ ⊢
      intro h_contra
      apply hμ
      rw [Submodule.eq_bot_iff]
      intro x hx

      have hsec_x_wt : sec x ∈ WeightSpace Δ (G.obj M).carrier μ := by
        intro h
        rw [← LieModuleHom.map_lie]
        rw [hx h]
        exact map_smul sec (μ h) x

      rw [Submodule.eq_bot_iff] at h_contra
      have hsec_zero : sec x = 0 := h_contra (sec x) hsec_x_wt

      calc x = ret (sec x) := (hret_sec x).symm
        _ = ret 0 := by rw [hsec_zero]
        _ = 0 := map_zero ret
  }

theorem direct_summand_preserves_projectiveInO
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (F G : EndoFunctorData R 𝔤)
    (_hDS : IsDirectSummand F G)
    (M : RepGfObj R 𝔤)
    (hFMO : IsCategoryO Δ rd (F.obj M).carrier)
    (hGMO : IsCategoryO Δ rd (G.obj M).carrier)
    (hGMproj : IsProjectiveInO rd (G.obj M).carrier hGMO) :
    IsProjectiveInO rd (F.obj M).carrier hFMO := by

  obtain ⟨i_nt, p_nt, hpi⟩ := _hDS

  let sec := (i_nt.app M).toFun
  let ret := (p_nt.app M).toFun

  have hret_sec : ∀ x : (F.obj M).carrier, ret (sec x) = x := hpi M

  intro X _ _ _ _ hXO N _ _ _ _ hNO f hf g

  let g' : (G.obj M).carrier →ₗ⁅R, 𝔤⁆ N := g.comp ret

  obtain ⟨h', hh'⟩ := hGMproj X hXO N hNO f hf g'

  exact ⟨h'.comp sec, fun x => by
    rw [LieModuleHom.comp_apply, hh']
    show g (ret (sec x)) = g x
    rw [hret_sec x]⟩

theorem projective_functor_preserves_projective_in_O
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (rd : PositiveRootData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (_hDom : IsDominantWeightLE rd wg lam)
    (F : EndoFunctorData R 𝔤)
    (_hF : IsProjectiveFunctor F)
    (M : RepGfObj R 𝔤)
    (_hMO : IsCategoryO Δ rd M.carrier)
    (_hMproj : IsProjectiveInO rd M.carrier _hMO) :
    ∃ (hFMO : IsCategoryO Δ rd (F.obj M).carrier),
      IsProjectiveInO rd (F.obj M).carrier hFMO := by

  obtain ⟨FV, hDS⟩ := _hF.exists_tensor_summand

  have hFVMO : IsCategoryO Δ rd (FV.functor.obj M).carrier :=
    tensor_functor_preserves_categoryO Δ rd FV M _hMO

  have hFMO : IsCategoryO Δ rd (F.obj M).carrier :=
    direct_summand_preserves_categoryO Δ rd F FV.functor hDS M hFVMO

  have hFVMproj : IsProjectiveInO rd (FV.functor.obj M).carrier hFVMO :=
    tensor_functor_preserves_projectiveInO Δ rd FV M _hMO _hMproj hFVMO

  have hFMproj : IsProjectiveInO rd (F.obj M).carrier hFMO :=
    direct_summand_preserves_projectiveInO Δ rd F FV.functor hDS M hFMO hFVMO hFVMproj
  exact ⟨hFMO, hFMproj⟩

theorem singular_vector_avoids_radical
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    {P : Type u} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (v : P) (lam : Δ.𝔥 →ₗ[R] R)
    (hv_ne : v ≠ 0)
    (hv_weight : ∀ (h : Δ.𝔥), ⁅(↑h : 𝔤), v⁆ = lam h • v)
    (hv_killed : ∀ (e : Δ.𝔫_pos), ⁅(↑e : 𝔤), v⁆ = 0)
    (hPO : IsCategoryO Δ rd P)
    (hPproj : IsProjectiveInO rd P hPO)
    (hPindecomp : ∀ (A B : LieSubmodule R 𝔤 P),
      A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥)
    (J : LieSubmodule R 𝔤 P)
    (hJ_ne_top : J ≠ ⊤)
    (hJ_max : ∀ (N : LieSubmodule R 𝔤 P), N ≠ ⊤ → N ≤ J)
    (hJ_irr : LieModule.IsIrreducible R 𝔤 (P ⧸ J)) :
    v ∉ J := by


  intro hv_in_J
  have hspan_le_J : LieSubmodule.lieSpan R 𝔤 ({v} : Set P) ≤ J :=
    LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr hv_in_J)


  have hv_gen : LieSubmodule.lieSpan R 𝔤 ({v} : Set P) = ⊤ := by


    sorry
  rw [hv_gen] at hspan_le_J
  exact hJ_ne_top (eq_top_iff.mpr hspan_le_J)

theorem singular_vector_lieSpan_eq_top
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    {P : Type u} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (v : P) (lam : Δ.𝔥 →ₗ[R] R)
    (hv_ne : v ≠ 0)
    (hv_weight : ∀ (h : Δ.𝔥), ⁅(↑h : 𝔤), v⁆ = lam h • v)
    (hv_killed : ∀ (e : Δ.𝔫_pos), ⁅(↑e : 𝔤), v⁆ = 0)
    (hPO : IsCategoryO Δ rd P)
    (hPproj : IsProjectiveInO rd P hPO)
    (hPindecomp : ∀ (A B : LieSubmodule R 𝔤 P),
      A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥) :
    LieSubmodule.lieSpan R 𝔤 ({v} : Set P) = ⊤ := by

  obtain ⟨J, hJ_ne_top, hJ_max, hJ_irr⟩ :=
    projective_cover_unique_simple_quotient hPO hPproj hPindecomp

  have hv_not_in_J : v ∉ J :=
    singular_vector_avoids_radical Δ rd v lam hv_ne hv_weight hv_killed
      hPO hPproj hPindecomp J hJ_ne_top hJ_max hJ_irr

  have hspan_not_le_J : ¬ (LieSubmodule.lieSpan R 𝔤 ({v} : Set P) ≤ J) := by
    intro h_le
    exact hv_not_in_J (h_le (LieSubmodule.subset_lieSpan (Set.mem_singleton v)))

  by_contra h_ne_top
  exact hspan_not_le_J (hJ_max (LieSubmodule.lieSpan R 𝔤 {v}) h_ne_top)

theorem singular_vector_generates_catO
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    {P : Type u} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (v : P) (lam : Δ.𝔥 →ₗ[R] R)
    (hv_ne : v ≠ 0)
    (_hv_weight : ∀ (h : Δ.𝔥), ⁅(↑h : 𝔤), v⁆ = lam h • v)
    (_hv_killed : ∀ (e : Δ.𝔫_pos), ⁅(↑e : 𝔤), v⁆ = 0)
    (_hPO : IsCategoryO Δ rd P)
    (_hPproj : IsProjectiveInO rd P _hPO)
    (_hPindecomp : ∀ (A B : LieSubmodule R 𝔤 P),
      A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥) :
    LieSubmodule.lieSpan R 𝔤 ({v} : Set P) = ⊤ :=
  singular_vector_lieSpan_eq_top Δ rd v lam hv_ne _hv_weight _hv_killed
    _hPO _hPproj _hPindecomp

theorem singular_vector_not_in_maximal_submodule
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    {P : Type u} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (v : P) (lam : Δ.𝔥 →ₗ[R] R)
    (hv_ne : v ≠ 0)
    (_hv_weight : ∀ (h : Δ.𝔥), ⁅(↑h : 𝔤), v⁆ = lam h • v)
    (_hv_killed : ∀ (e : Δ.𝔫_pos), ⁅(↑e : 𝔤), v⁆ = 0)
    (_hPO : IsCategoryO Δ rd P)
    (_hPproj : IsProjectiveInO rd P _hPO)
    (_hPindecomp : ∀ (A B : LieSubmodule R 𝔤 P),
      A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥)
    (J : LieSubmodule R 𝔤 P)
    (_hJ_ne_top : J ≠ ⊤)
    (_hJ_max : ∀ (N : LieSubmodule R 𝔤 P), N ≠ ⊤ → N ≤ J)
    (_hPJ_irr : LieModule.IsIrreducible R 𝔤 (P ⧸ J)) :
    v ∉ J := by

  have hgen : LieSubmodule.lieSpan R 𝔤 ({v} : Set P) = ⊤ :=
    singular_vector_generates_catO Δ rd v lam hv_ne _hv_weight _hv_killed _hPO _hPproj _hPindecomp

  intro hv_in_J

  have hspan_le_J : LieSubmodule.lieSpan R 𝔤 ({v} : Set P) ≤ J := by
    rw [LieSubmodule.lieSpan_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hv_in_J

  have hJ_top : J = ⊤ := by
    rw [eq_top_iff]
    exact hgen ▸ hspan_le_J

  exact _hJ_ne_top hJ_top

theorem singular_vector_generates_indecomp_projective
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    {P : Type u} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (v : P) (lam : Δ.𝔥 →ₗ[R] R)
    (_hv_ne : v ≠ 0)
    (_hv_weight : ∀ (h : Δ.𝔥), ⁅(↑h : 𝔤), v⁆ = lam h • v)
    (_hv_killed : ∀ (e : Δ.𝔫_pos), ⁅(↑e : 𝔤), v⁆ = 0)
    (hPO : IsCategoryO Δ rd P)
    (_hPproj : IsProjectiveInO rd P hPO)
    (_hPindecomp : ∀ (A B : LieSubmodule R 𝔤 P),
      A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥)
    (J : LieSubmodule R 𝔤 P)
    (_hJ_ne_top : J ≠ ⊤)
    (_hJ_max : ∀ (N : LieSubmodule R 𝔤 P), N ≠ ⊤ → N ≤ J)
    (_hPJ_irr : LieModule.IsIrreducible R 𝔤 (P ⧸ J)) :
    LieSubmodule.lieSpan R 𝔤 ({v} : Set P) = ⊤ := by

  have hv_not_in_J : v ∉ J :=
    singular_vector_not_in_maximal_submodule Δ rd v lam _hv_ne _hv_weight _hv_killed
      hPO _hPproj _hPindecomp J _hJ_ne_top _hJ_max _hPJ_irr

  by_contra h_ne_top

  have hS_le_J : LieSubmodule.lieSpan R 𝔤 ({v} : Set P) ≤ J :=
    _hJ_max _ h_ne_top

  have hv_in_S : v ∈ LieSubmodule.lieSpan R 𝔤 ({v} : Set P) :=
    LieSubmodule.subset_lieSpan (Set.mem_singleton v)

  exact hv_not_in_J (hS_le_J hv_in_S)

theorem indecomposable_projective_in_O_has_highest_weight
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (rd : PositiveRootData Δ)
    (P : Type u) [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (hPO : IsCategoryO Δ rd P)
    (_hPproj : IsProjectiveInO rd P hPO)

    (_hPindecomp : ∀ (A B : LieSubmodule R 𝔤 P),
      A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥) :
    ∃ (mu : Δ.𝔥 →ₗ[R] R),
      Nonempty (IsHighestWeightModule Δ P (mu - wg.ρ)) := by


  obtain ⟨J, hJ_ne_top, hJ_max, hPJ_irr⟩ :=
    projective_cover_unique_simple_quotient hPO _hPproj _hPindecomp

  haveI : Nontrivial P := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply hJ_ne_top
    ext x
    simp only [LieSubmodule.mem_top, iff_true]
    have : x = 0 := Subsingleton.elim x 0
    rw [this]; exact J.zero_mem

  obtain ⟨v, lam, hv_ne, hv_weight, hv_killed⟩ :=
    CategoryO.exists_singular_vector hPO


  have hgen : LieSubmodule.lieSpan R 𝔤 ({v} : Set P) = ⊤ :=
    singular_vector_generates_indecomp_projective Δ rd v lam hv_ne hv_weight hv_killed
      hPO _hPproj _hPindecomp J hJ_ne_top hJ_max hPJ_irr

  exact ⟨lam + wg.ρ, ⟨{
    highestWeightVec := v
    hwv_ne_zero := hv_ne
    cartan_action := by rwa [add_sub_cancel_right]
    npos_action := hv_killed
    generates := hgen
  }⟩⟩

theorem lieSubmodule_decomp_gives_idempotent
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (F : EndoFunctorData R 𝔤)
    (_hF : IsProjectiveFunctor F)
    (M : RepGfObj R 𝔤)
    (_hMverma : Nonempty (IsVermaModule Δ M.carrier (lam - wg.ρ)))
    (A B : LieSubmodule R 𝔤 (F.obj M).carrier)
    (_hInf : A ⊓ B = ⊥) (_hSup : A ⊔ B = ⊤)
    (hA : A ≠ ⊥) (hB : B ≠ ⊥) :


    ∃ (e : NatTransData F F),
      (e.comp e).EqPointwise e ∧
      ¬ e.EqPointwise (NatTransData.id F) ∧
      ¬ (∀ (N : RepGfObj R 𝔤) (x : (F.obj N).carrier), (e.app N).toFun x = 0) := by


  let rA : RepGfObj R 𝔤 := ⟨↥A, inferInstance, inferInstance, inferInstance, inferInstance⟩
  let rB : RepGfObj R 𝔤 := ⟨↥B, inferInstance, inferInstance, inferInstance, inferInstance⟩
  let summands : Fin 2 → RepGfObj R 𝔤 := ![rA, rB]

  have hc_sub : IsCompl A.toSubmodule B.toSubmodule := by
    constructor
    · rw [disjoint_iff]
      have h := congr_arg LieSubmodule.toSubmodule _hInf
      simp only [LieSubmodule.inf_toSubmodule, LieSubmodule.bot_toSubmodule] at h
      exact h
    · rw [codisjoint_iff]
      have h := congr_arg LieSubmodule.toSubmodule _hSup
      simp only [LieSubmodule.sup_toSubmodule, LieSubmodule.top_toSubmodule] at h
      exact h

  have hDecomp : IsDirectSumDecompObj (F.obj M) summands := by
    let linProjA := Submodule.linearProjOfIsCompl A.toSubmodule B.toSubmodule hc_sub
    let linProjB := Submodule.linearProjOfIsCompl B.toSubmodule A.toSubmodule hc_sub.symm

    have hdecomp_m : ∀ (m : (F.obj M).carrier),
        m = ↑(linProjA m) + ↑(linProjB m) := by
      intro m
      rw [← Submodule.IsCompl.projection_apply hc_sub,
          ← Submodule.IsCompl.projection_apply hc_sub.symm]
      exact (Submodule.IsCompl.projection_add_projection_eq_self hc_sub m).symm

    have proj_lie_A : ∀ (x : 𝔤) (m : (F.obj M).carrier),
        linProjA ⁅x, m⁆ = ⟨⁅x, ↑(linProjA m)⁆, A.lie_mem (linProjA m).prop⟩ := by
      intro x m
      have hbA : ⁅x, (↑(linProjA m) : (F.obj M).carrier)⁆ ∈ A.toSubmodule :=
        A.lie_mem (linProjA m).prop
      have hbB : ⁅x, (↑(linProjB m) : (F.obj M).carrier)⁆ ∈ B.toSubmodule :=
        B.lie_mem (linProjB m).prop
      conv_lhs => rw [hdecomp_m m, lie_add, map_add]
      rw [Submodule.linearProjOfIsCompl_apply_left hc_sub ⟨_, hbA⟩,
          Submodule.linearProjOfIsCompl_apply_right hc_sub ⟨_, hbB⟩]
      simp

    have proj_lie_B : ∀ (x : 𝔤) (m : (F.obj M).carrier),
        linProjB ⁅x, m⁆ = ⟨⁅x, ↑(linProjB m)⁆, B.lie_mem (linProjB m).prop⟩ := by
      intro x m
      have hbA : ⁅x, (↑(linProjA m) : (F.obj M).carrier)⁆ ∈ A.toSubmodule :=
        A.lie_mem (linProjA m).prop
      have hbB : ⁅x, (↑(linProjB m) : (F.obj M).carrier)⁆ ∈ B.toSubmodule :=
        B.lie_mem (linProjB m).prop
      conv_lhs => rw [hdecomp_m m, lie_add, map_add]
      rw [Submodule.linearProjOfIsCompl_apply_right hc_sub.symm ⟨_, hbA⟩,
          Submodule.linearProjOfIsCompl_apply_left hc_sub.symm ⟨_, hbB⟩]
      simp

    let inclA_lie : rA.carrier →ₗ⁅R, 𝔤⁆ (F.obj M).carrier :=
      { toLinearMap := A.toSubmodule.subtype, map_lie' := fun {x m} => rfl }
    let inclB_lie : rB.carrier →ₗ⁅R, 𝔤⁆ (F.obj M).carrier :=
      { toLinearMap := B.toSubmodule.subtype, map_lie' := fun {x m} => rfl }
    let projA_lie : (F.obj M).carrier →ₗ⁅R, 𝔤⁆ rA.carrier :=
      { toLinearMap := linProjA
        map_lie' := fun {x m} => by exact proj_lie_A x m }
    let projB_lie : (F.obj M).carrier →ₗ⁅R, 𝔤⁆ rB.carrier :=
      { toLinearMap := linProjB
        map_lie' := fun {x m} => by exact proj_lie_B x m }

    let sect : ∀ i : Fin 2, RepGfHom (summands i) (F.obj M) := fun i =>
      match i with
      | ⟨0, _⟩ => ⟨inclA_lie⟩
      | ⟨1, _⟩ => ⟨inclB_lie⟩
    let retr : ∀ i : Fin 2, RepGfHom (F.obj M) (summands i) := fun i =>
      match i with
      | ⟨0, _⟩ => ⟨projA_lie⟩
      | ⟨1, _⟩ => ⟨projB_lie⟩
    refine ⟨sect, retr, ?_, ?_⟩
    ·
      intro i x
      fin_cases i
      · exact Submodule.linearProjOfIsCompl_apply_left hc_sub x
      · exact Submodule.linearProjOfIsCompl_apply_left hc_sub.symm x
    ·
      intro x
      simp only [Fin.sum_univ_two]
      change x = (A.toSubmodule.subtype (linProjA x)) + (B.toSubmodule.subtype (linProjB x))
      exact hdecomp_m x


  obtain ⟨F_i, _hFi_proj, hFi_obj, hFi_decomp⟩ :=
    corollary_22_6_ii Δ wg lam F _hF M _hMverma 2 summands hDecomp

  obtain ⟨sec_i, ret_i, hRS, hSum⟩ := hFi_decomp


  have hRS_unfold : ∀ (i : Fin 2) (N : RepGfObj R 𝔤) (z : ((F_i i).obj N).carrier),
      ((ret_i i).app N).toFun (((sec_i i).app N).toFun z) = z := by
    intro i N z
    have h := (hRS i) N z
    simp only [NatTransData.comp, NatTransData.id, RepGfHom.comp, RepGfHom.id,
               LieModuleHom.comp_apply, LieModuleHom.coe_id, id_eq] at h
    exact h


  let e : NatTransData F F := (sec_i 0).comp (ret_i 0)
  refine ⟨e, ?_, ?_, ?_⟩
  ·
    intro N x
    show ((sec_i 0).app N).toFun (((ret_i 0).app N).toFun
      (((sec_i 0).app N).toFun (((ret_i 0).app N).toFun x))) =
      ((sec_i 0).app N).toFun (((ret_i 0).app N).toFun x)
    congr 1


    exact (hRS 0) N (((ret_i 0).app N).toFun x)
  ·
    intro hEqId
    apply hB
    rw [eq_bot_iff]
    intro b hb
    rw [LieSubmodule.mem_bot]

    have h_sr1_zero : ∀ (y : (F.obj M).carrier),
        ((sec_i 1).app M).toFun (((ret_i 1).app M).toFun y) = 0 := by
      intro y
      have hS := hSum M y
      simp only [Fin.sum_univ_two] at hS


      change y = _ + _ at hS

      have hE' : ((sec_i 0).app M).toFun (((ret_i 0).app M).toFun y) = y := hEqId M y
      rw [hE'] at hS
      have : y + ((sec_i 1).app M).toFun (((ret_i 1).app M).toFun y) - y = 0 := by
        rw [← hS]; simp
      simp at this
      exact this


    have h_s1_zero : ∀ (z : ((F_i 1).obj M).carrier),
        ((sec_i 1).app M).toFun z = 0 := by
      intro z
      have h1 := h_sr1_zero (((sec_i 1).app M).toFun z)


      rw [hRS_unfold 1 M z] at h1
      exact h1

    have h_Fi1_triv : ∀ (z : ((F_i 1).obj M).carrier), z = 0 := by
      intro z
      have h1 := h_s1_zero z

      have h2 := hRS_unfold 1 M z

      rw [h1, map_zero] at h2
      exact h2.symm


    have hobj1 := hFi_obj 1
    have h_summands1_eq_rB : summands 1 = rB := by
      simp [summands, Matrix.cons_val_one]
    have h_eq : (F_i 1).obj M = rB := hobj1.trans h_summands1_eq_rB


    have h_rB_triv : ∀ (b' : rB.carrier), b' = 0 := by
      have := h_eq ▸ h_Fi1_triv
      intro b'


      have hz := this b'
      exact_mod_cast hz
    have h_Bval : (⟨b, hb⟩ : (↥B : Type _)) = 0 := h_rB_triv ⟨b, hb⟩
    exact congrArg Subtype.val h_Bval
  ·
    intro hAllZero
    apply hA
    rw [eq_bot_iff]
    intro a ha
    rw [LieSubmodule.mem_bot]

    have h_sr0_zero : ∀ (y : (F.obj M).carrier),
        ((sec_i 0).app M).toFun (((ret_i 0).app M).toFun y) = 0 := by
      intro y
      exact hAllZero M y

    have h_s0_zero : ∀ (z : ((F_i 0).obj M).carrier),
        ((sec_i 0).app M).toFun z = 0 := by
      intro z
      have h1 := h_sr0_zero (((sec_i 0).app M).toFun z)
      rw [hRS_unfold 0 M z] at h1
      exact h1

    have h_Fi0_triv : ∀ (z : ((F_i 0).obj M).carrier), z = 0 := by
      intro z
      have h1 := h_s0_zero z
      have h2 := hRS_unfold 0 M z
      rw [h1, map_zero] at h2
      exact h2.symm

    have hobj0 := hFi_obj 0
    have h_summands0_eq_rA : summands 0 = rA := by
      simp [summands, Matrix.cons_val_zero]
    have h_eq0 : (F_i 0).obj M = rA := hobj0.trans h_summands0_eq_rA

    have h_rA_triv : ∀ (a' : rA.carrier), a' = 0 := by
      have := h_eq0 ▸ h_Fi0_triv
      intro a'
      have hz := this a'
      exact_mod_cast hz
    have h_Aval : (⟨a, ha⟩ : (↥A : Type _)) = 0 := h_rA_triv ⟨a, ha⟩
    exact congrArg Subtype.val h_Aval

theorem functor_indecomp_gives_module_indecomp
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (rd : PositiveRootData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (_hDom : IsDominantWeightLE rd wg lam)
    (F : EndoFunctorData R 𝔤)
    (_hF : IsProjectiveFunctor F)
    (_hIndecomp : IsIndecomposable F)
    (_hBlock : FactorsThroughBlock Δ F lam)
    (M : RepGfObj R 𝔤)
    (_hMverma : Nonempty (IsVermaModule Δ M.carrier (lam - wg.ρ))) :
    ∀ (A B : LieSubmodule R 𝔤 (F.obj M).carrier),
      A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥ := by


  intro A B hInf hSup
  by_contra h
  push Not at h
  obtain ⟨hA, hB⟩ := h


  obtain ⟨e, hIdem, hNotId, hNotZero⟩ :=
    lieSubmodule_decomp_gives_idempotent Δ wg lam F _hF M _hMverma A B hInf hSup hA hB

  have hIndecomp := _hIndecomp e hIdem

  rcases hIndecomp with hId | hZero
  · exact hNotId hId
  · exact hNotZero hZero

theorem verma_isCategoryO
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (_hM : IsVermaModule Δ M wt) :
    IsCategoryO Δ rd M := by
  constructor
  ·
    refine ⟨{_hM.highestWeightVec}, ?_⟩
    simp only [Finset.coe_singleton]
    exact _hM.toIsHighestWeightModule.generates
  ·


    have hwd := _hM.toIsHighestWeightModule.weight_decomposition
    intro m

    have hm : m ∈ (⨆ (μ : Δ.𝔥 →ₗ[R] R), Δ.weightSubspace M μ : Submodule R M) := by
      rw [hwd]; exact Submodule.mem_top

    rw [Submodule.mem_iSup_iff_exists_finset] at hm
    obtain ⟨s, hms⟩ := hm
    rw [Submodule.mem_iSup_finset_iff_exists_sum] at hms
    obtain ⟨v, hv⟩ := hms


    exact ⟨s, fun μ => ⟨(v μ : M), (v μ).prop⟩, hv.symm⟩
  ·
    exact ⟨{wt}, fun μ hμ => ⟨wt, Finset.mem_singleton.mpr rfl,
      _hM.weight_subset_QPlus rd μ hμ⟩⟩

theorem proposition_22_7_ii
    {R : Type u} [Field R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (rd : PositiveRootData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (_hDom : IsDominantWeightLE rd wg lam)
    (F : EndoFunctorData R 𝔤)
    (_hF : IsProjectiveFunctor F)
    (_hIndecomp : IsIndecomposable F)

    (_hBlock : FactorsThroughBlock Δ F lam)
    (Mverma : RepGfObj R 𝔤)
    (_hMverma : Nonempty (IsVermaModule Δ Mverma.carrier (lam - wg.ρ))) :


    ∃ (mu : Δ.𝔥 →ₗ[R] R)
      (hO : IsCategoryO Δ rd (F.obj Mverma).carrier),
      IsProjectiveInO rd (F.obj Mverma).carrier hO ∧
      (∀ (A B : LieSubmodule R 𝔤 (F.obj Mverma).carrier),
        A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥) ∧
      Nonempty (IsHighestWeightModule Δ (F.obj Mverma).carrier (mu - wg.ρ)) := by


  have hMO : IsCategoryO Δ rd Mverma.carrier := by
    obtain ⟨vm⟩ := _hMverma
    exact verma_isCategoryO Δ rd Mverma.carrier (lam - wg.ρ) vm
  have hMproj : IsProjectiveInO rd Mverma.carrier hMO := by
    obtain ⟨vm⟩ := _hMverma
    exact verma_projective_of_dominant lam _hDom vm hMO

  obtain ⟨hFMO, hFMproj⟩ :=
    projective_functor_preserves_projective_in_O Δ wg rd lam _hDom F _hF Mverma hMO hMproj

  have hFM_indecomp : ∀ (A B : LieSubmodule R 𝔤 (F.obj Mverma).carrier),
      A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥ :=
    functor_indecomp_gives_module_indecomp Δ wg rd lam _hDom F _hF _hIndecomp _hBlock Mverma _hMverma

  obtain ⟨mu, hHW⟩ :=
    indecomposable_projective_in_O_has_highest_weight Δ wg rd
      (F.obj Mverma).carrier hFMO hFMproj hFM_indecomp
  exact ⟨mu, hFMO, hFMproj, hFM_indecomp, hHW⟩

end ProjectiveFunctors

end
