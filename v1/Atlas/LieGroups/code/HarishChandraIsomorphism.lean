/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.VermaModules
import Atlas.LieGroups.code.PBW
import Mathlib.Algebra.Algebra.Subalgebra.Basic

noncomputable section

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {R 𝔤}

def Subalgebra.invariants {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]
    (G : Type*) [Group G] (act : G →* A ≃ₐ[R] A) : Subalgebra R A where
  carrier := { a : A | ∀ g : G, (act g) a = a }
  mul_mem' := fun {a b} ha hb g => by simp [map_mul, ha g, hb g]
  one_mem' := fun g => by simp
  add_mem' := fun {a b} ha hb g => by simp [map_add, ha g, hb g]
  zero_mem' := fun g => by simp
  algebraMap_mem' := fun r g => by simp [AlgEquiv.commutes]

theorem cartan_isLieAbelian (Δ : TriangularDecomposition R 𝔤) : IsLieAbelian Δ.𝔥 :=
  Δ.h_abelian

def weightToLieHom
    {L : Type*} [LieRing L] [LieAlgebra R L] [IsLieAbelian L]
    (wt : L →ₗ[R] R) : L →ₗ⁅R⁆ R where
  toLinearMap := wt
  map_lie' {x y} := by
    simp [LieRing.of_associative_ring_bracket, mul_comm]

def evalWeight (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    UniversalEnvelopingAlgebra R Δ.𝔥 →ₐ[R] R :=
  have : IsLieAbelian Δ.𝔥 := cartan_isLieAbelian Δ
  UniversalEnvelopingAlgebra.lift R (weightToLieHom wt)

structure WeylGroupData (Δ : TriangularDecomposition R 𝔤) where
  W : Type*
  [instGroup : Group W]
  [instFintype : Fintype W]
  algAction : W →* (UniversalEnvelopingAlgebra R Δ.𝔥) ≃ₐ[R]
    (UniversalEnvelopingAlgebra R Δ.𝔥)
  ρ : Δ.𝔥 →ₗ[R] R

  dualAction : W → (Δ.𝔥 →ₗ[R] R) → (Δ.𝔥 →ₗ[R] R)
  dualAction_one : ∀ (μ : Δ.𝔥 →ₗ[R] R), dualAction 1 μ = μ
  dualAction_mul : ∀ (w₁ w₂ : W) (μ : Δ.𝔥 →ₗ[R] R),
    dualAction (w₁ * w₂) μ = dualAction w₁ (dualAction w₂ μ)
  dualAction_add : ∀ (w : W) (μ ν : Δ.𝔥 →ₗ[R] R),
    dualAction w (μ + ν) = dualAction w μ + dualAction w ν
  dualAction_smul : ∀ (w : W) (c : R) (μ : Δ.𝔥 →ₗ[R] R),
    dualAction w (c • μ) = c • dualAction w μ
  algDualCompat : ∀ (g : W) (wt : Δ.𝔥 →ₗ[R] R) (p : UniversalEnvelopingAlgebra R Δ.𝔥),
    evalWeight Δ wt ((algAction g) p) = evalWeight Δ (dualAction g⁻¹ wt) p
  orbitSeparation : ∀ (mu nu : Δ.𝔥 →ₗ[R] R),
    (∀ (p : UniversalEnvelopingAlgebra R Δ.𝔥),
      (∀ g : W, (algAction g) p = p) →
      evalWeight Δ mu p = evalWeight Δ nu p) →
    ∃ w : W, nu = dualAction w mu

attribute [instance] WeylGroupData.instGroup WeylGroupData.instFintype

def WeylGroupData.invariantSubalgebra {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ) :
    Subalgebra R (UniversalEnvelopingAlgebra R Δ.𝔥) :=
  Subalgebra.invariants wg.W wg.algAction

def WeylGroupData.shiftedAction {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ) (w : wg.W) (mu : Δ.𝔥 →ₗ[R] R) : Δ.𝔥 →ₗ[R] R :=
  wg.dualAction w (mu + wg.ρ) - wg.ρ

def PositiveRootData.sumPosRoots {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤} (rd : PositiveRootData Δ) : Δ.𝔥 →ₗ[R] R :=
  ∑ α ∈ rd.posRoots, α

def augmentation (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L] :
    UniversalEnvelopingAlgebra R L →ₐ[R] R :=
  UniversalEnvelopingAlgebra.lift R (0 : L →ₗ⁅R⁆ R)

def pbwTriangularIso (Δ : TriangularDecomposition R 𝔤) :
    (TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔫_neg)
      (TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔥)
                       (UniversalEnvelopingAlgebra R Δ.𝔫_pos))) ≃ₗ[R]
    UniversalEnvelopingAlgebra R 𝔤 :=
  pbw_triangular_iso R 𝔤 Δ

set_option maxHeartbeats 400000 in
def betaMap (Δ : TriangularDecomposition R 𝔤) :
    TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔫_neg)
      (TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔥)
                       (UniversalEnvelopingAlgebra R Δ.𝔫_pos)) →ₗ[R]
    UniversalEnvelopingAlgebra R Δ.𝔥 := by
  apply TensorProduct.lift


  let inner : TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔥)
      (UniversalEnvelopingAlgebra R Δ.𝔫_pos) →ₗ[R] UniversalEnvelopingAlgebra R Δ.𝔥 :=
    TensorProduct.lift
      (((LinearMap.lsmul R (UniversalEnvelopingAlgebra R Δ.𝔥)).comp
        (augmentation R Δ.𝔫_pos).toLinearMap).flip)

  exact ((LinearMap.lsmul R _).comp (augmentation R Δ.𝔫_neg).toLinearMap).flip inner

def HarishChandraMap (Δ : TriangularDecomposition R 𝔤) :
    UniversalEnvelopingAlgebra R 𝔤 →ₗ[R] UniversalEnvelopingAlgebra R Δ.𝔥 :=
  (betaMap Δ).comp (pbwTriangularIso Δ).symm.toLinearMap


theorem uea_algHom_separates
    {R : Type*} [CommRing R]
    {L : Type*} [LieRing L] [LieAlgebra R L] [IsLieAbelian L]
    (p q : UniversalEnvelopingAlgebra R L)
    (h : ∀ (f : UniversalEnvelopingAlgebra R L →ₐ[R] R), f p = f q) :
    p = q := by sorry

theorem evalWeight_separates (Δ : TriangularDecomposition R 𝔤)
    (p q : UniversalEnvelopingAlgebra R Δ.𝔥)
    (h : ∀ (wt : Δ.𝔥 →ₗ[R] R), evalWeight Δ wt p = evalWeight Δ wt q) :
    p = q := by


  have hall : ∀ (f : UniversalEnvelopingAlgebra R Δ.𝔥 →ₐ[R] R), f p = f q := by
    intro f
    have habel : IsLieAbelian Δ.𝔥 := cartan_isLieAbelian Δ
    let g : Δ.𝔥 →ₗ⁅R⁆ R := (UniversalEnvelopingAlgebra.lift R (A := R)).symm f
    let wt : Δ.𝔥 →ₗ[R] R := g.toLinearMap
    have hf_eq : f = evalWeight Δ wt := by
      simp only [evalWeight]
      apply (UniversalEnvelopingAlgebra.lift R).symm.injective
      simp only [Equiv.symm_apply_apply]
      ext x; rfl
    rw [hf_eq]; exact h wt


  have : IsLieAbelian Δ.𝔥 := cartan_isLieAbelian Δ
  exact uea_algHom_separates p q hall

lemma LinearMap.exists_factor_of_surjective_ker_le
    {R' : Type*} [CommRing R']
    {A B C : Type*} [AddCommGroup A] [Module R' A]
    [AddCommGroup B] [Module R' B] [AddCommGroup C] [Module R' C]
    (p : A →ₗ[R'] B) (f : A →ₗ[R'] C)
    (hsurj : Function.Surjective p)
    (hker : LinearMap.ker p ≤ LinearMap.ker f) :
    ∃ (ℓ : B →ₗ[R'] C), ∀ a, ℓ (p a) = f a := by
  choose g hg using hsurj
  have well_def : ∀ (u₁ u₂ : A), p u₁ = p u₂ → f u₁ = f u₂ := by
    intro u₁ u₂ h
    have hmem : u₁ - u₂ ∈ LinearMap.ker p :=
      LinearMap.mem_ker.mpr (by rw [map_sub, h, sub_self])
    have := hker hmem
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this; exact this
  exact ⟨{
    toFun := fun b => f (g b)
    map_add' := fun b₁ b₂ => by
      have h := well_def (g (b₁ + b₂)) (g b₁ + g b₂) (by rw [hg, map_add, hg, hg])
      rw [h, map_add]
    map_smul' := fun r b => by
      simp only [RingHom.id_apply]
      have h := well_def (g (r • b)) (r • g b) (by rw [hg, map_smul, hg])
      rw [h, map_smul]
  }, fun a => well_def (g (p a)) a (by rw [hg])⟩


theorem pbw_hc_eval_kernel_vanishing
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R)
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsHighestWeightModule Δ M wt)
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (hcompat : ∀ (x : 𝔤) (m : M), ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (u : UniversalEnvelopingAlgebra R 𝔤)
    (hu : ueaAct u hM.highestWeightVec = 0) :
    evalWeight Δ wt (HarishChandraMap Δ u) = 0 := by
  sorry

theorem pbw_ueaAct_surjective
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R)
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsHighestWeightModule Δ M wt)
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (hcompat : ∀ (x : 𝔤) (m : M), ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆) :
    Function.Surjective (fun u => ueaAct u hM.highestWeightVec) := by
  intro m
  have hm_top : m ∈ (⊤ : LieSubmodule R 𝔤 M) := LieSubmodule.mem_top m
  rw [← hM.generates] at hm_top
  exact LieSubmodule.lieSpan_induction (R := R) (L := 𝔤)
    (p := fun x _ => ∃ a, (ueaAct a) hM.highestWeightVec = x)
    (fun x hx => by
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨1, by simp [map_one, Module.End.one_apply]⟩)
    (⟨0, by simp [map_zero, LinearMap.zero_apply]⟩)
    (fun x y _ _ ⟨a, ha⟩ ⟨b, hb⟩ =>
      ⟨a + b, by simp only [map_add, LinearMap.add_apply, ha, hb]⟩)
    (fun r x _ ⟨a, ha⟩ =>
      ⟨r • a, by rw [map_smul, LinearMap.smul_apply, ha]⟩)
    (fun x y _ ⟨a, ha⟩ =>
      ⟨UniversalEnvelopingAlgebra.ι R x * a, by
        rw [map_mul, Module.End.mul_apply, ha, hcompat]⟩)
    hm_top

theorem pbw_hc_eval_factors_through_action
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R)
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsHighestWeightModule Δ M wt)
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (hcompat : ∀ (x : 𝔤) (m : M), ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆) :
    ∃ (ℓ : M →ₗ[R] R),
      ∀ (u : UniversalEnvelopingAlgebra R 𝔤),
        evalWeight Δ wt (HarishChandraMap Δ u) = ℓ (ueaAct u hM.highestWeightVec) := by

  set actMap : UniversalEnvelopingAlgebra R 𝔤 →ₗ[R] M :=
    (LinearMap.applyₗ (R := R) (M₂ := M) hM.highestWeightVec).comp ueaAct.toLinearMap

  set hcEvalMap : UniversalEnvelopingAlgebra R 𝔤 →ₗ[R] R :=
    (evalWeight Δ wt).toLinearMap.comp (HarishChandraMap Δ)

  have hsurj : Function.Surjective actMap := by
    intro m
    obtain ⟨u, hu⟩ := pbw_ueaAct_surjective Δ wt hM ueaAct hcompat m
    exact ⟨u, hu⟩

  have hker : LinearMap.ker actMap ≤ LinearMap.ker hcEvalMap := by
    intro u hu
    rw [LinearMap.mem_ker] at hu ⊢
    exact pbw_hc_eval_kernel_vanishing Δ wt hM ueaAct hcompat u hu

  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_factor_of_surjective_ker_le actMap hcEvalMap hsurj hker
  exact ⟨ℓ, fun u => (hℓ u).symm⟩

theorem pbw_eval_hc_vanishes_on_annihilator
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R)
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsHighestWeightModule Δ M wt)
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (hcompat : ∀ (x : 𝔤) (m : M), ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (u : UniversalEnvelopingAlgebra R 𝔤)
    (hu : ueaAct u hM.highestWeightVec = 0) :
    evalWeight Δ wt (HarishChandraMap Δ u) = 0 := by
  obtain ⟨ℓ, hℓ⟩ := pbw_hc_eval_factors_through_action Δ wt hM ueaAct hcompat
  rw [hℓ u, hu]
  exact ℓ.map_zero

set_option maxHeartbeats 1600000 in
theorem pbw_hc_map_one
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) :
    HarishChandraMap Δ (1 : UniversalEnvelopingAlgebra R 𝔤) =
      (1 : UniversalEnvelopingAlgebra R Δ.𝔥) := by


  show (betaMap Δ).comp (pbwTriangularIso Δ).symm.toLinearMap 1 = 1
  simp only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]

  have h1 : (pbwTriangularIso Δ).symm (1 : UniversalEnvelopingAlgebra R 𝔤) =
      (1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) ⊗ₜ[R]
        ((1 : UniversalEnvelopingAlgebra R Δ.𝔥) ⊗ₜ[R]
          (1 : UniversalEnvelopingAlgebra R Δ.𝔫_pos)) := by
    apply (pbwTriangularIso Δ).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (pbw_triangular_iso_one Δ).symm
  rw [h1]

  simp only [betaMap, TensorProduct.lift.tmul, LinearMap.flip_apply,
    LinearMap.comp_apply, AlgHom.toLinearMap_apply, augmentation, map_one]
  simp only [LinearMap.lsmul_apply, one_smul]
  simp only [TensorProduct.lift.tmul, LinearMap.flip_apply, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, map_one]
  simp only [LinearMap.lsmul_apply, one_smul]

theorem pbw_verma_eval_any_hwm (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsHighestWeightModule Δ M wt)
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (hcompat : ∀ (x : 𝔤) (m : M), ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆) :
    ∃ (phi : M →ₗ[R] R),
      phi hM.highestWeightVec = 1 ∧
      ∀ (u : UniversalEnvelopingAlgebra R 𝔤),
        phi (ueaAct u hM.highestWeightVec) = evalWeight Δ wt (HarishChandraMap Δ u) := by

  set f : UniversalEnvelopingAlgebra R 𝔤 →ₗ[R] M :=
    ueaAct.toLinearMap.flip hM.highestWeightVec with hf_def
  set g : UniversalEnvelopingAlgebra R 𝔤 →ₗ[R] R :=
    (evalWeight Δ wt).toLinearMap.comp (HarishChandraMap Δ) with hg_def

  have hker : f.ker ≤ g.ker := by
    intro u hu
    rw [LinearMap.mem_ker] at hu ⊢
    exact pbw_eval_hc_vanishes_on_annihilator Δ wt hM ueaAct hcompat u hu

  have hf_surj : Function.Surjective f := by
    intro m

    have hm : m ∈ LieSubmodule.lieSpan R 𝔤 {hM.highestWeightVec} := by
      rw [hM.generates]; exact LieSubmodule.mem_top m

    suffices h : ∀ x, x ∈ LieSubmodule.lieSpan R 𝔤 ({hM.highestWeightVec} : Set M) →
        x ∈ LinearMap.range f from h m hm
    intro x hx
    induction hx using LieSubmodule.lieSpan_induction with
    | mem v hv =>
      rw [Set.mem_singleton_iff] at hv; subst hv
      exact ⟨1, by change ueaAct 1 hM.highestWeightVec = hM.highestWeightVec; simp [map_one]⟩
    | zero => exact ⟨0, by change ueaAct 0 hM.highestWeightVec = 0; simp [map_zero]⟩

    | add a b _ _ ha hb =>
      obtain ⟨ua, hua⟩ := ha; obtain ⟨ub, hub⟩ := hb
      exact ⟨ua + ub, by rw [LinearMap.map_add]; exact congr_arg₂ (· + ·) hua hub⟩
    | smul r a _ ha =>
      obtain ⟨ua, hua⟩ := ha
      exact ⟨r • ua, by rw [LinearMap.map_smul]; exact congr_arg (r • ·) hua⟩
    | lie x y _ hy =>
      obtain ⟨uy, huy⟩ := hy
      refine ⟨UniversalEnvelopingAlgebra.ι R x * uy, ?_⟩

      change ueaAct (UniversalEnvelopingAlgebra.ι R x * uy) hM.highestWeightVec = ⁅x, y⁆
      have : ueaAct (UniversalEnvelopingAlgebra.ι R x * uy) hM.highestWeightVec =
          ueaAct (UniversalEnvelopingAlgebra.ι R x) (ueaAct uy hM.highestWeightVec) := by
        rw [map_mul]; rfl
      rw [this, hcompat]; exact congr_arg (⁅x, ·⁆) huy


  set K := f.ker with hK_def
  have hgK : K ≤ g.ker := hker


  have hfK : K ≤ f.ker := le_refl K


  let f'Q := K.liftQ f hfK
  have hf'Q_inj : Function.Injective f'Q := by
    rw [← LinearMap.ker_eq_bot]
    rw [Submodule.eq_bot_iff]
    intro q hq
    obtain ⟨u, rfl⟩ := K.mkQ_surjective q
    rw [LinearMap.mem_ker] at hq
    change f u = 0 at hq
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_ker.mpr hq
  have hf'Q_surj : Function.Surjective f'Q := by
    intro m
    obtain ⟨u, hu⟩ := hf_surj m
    exact ⟨K.mkQ u, show f u = m from hu⟩
  let e := LinearEquiv.ofBijective f'Q ⟨hf'Q_inj, hf'Q_surj⟩
  let g'Q := K.liftQ g hgK

  refine ⟨g'Q.comp e.symm.toLinearMap, ?_, ?_⟩
  ·


    show g'Q (e.symm hM.highestWeightVec) = 1
    have he1 : e (K.mkQ 1) = hM.highestWeightVec := by
      show f'Q (K.mkQ 1) = hM.highestWeightVec
      change f 1 = hM.highestWeightVec
      simp [hf_def, map_one]
    conv_lhs => rw [show e.symm hM.highestWeightVec = K.mkQ 1 from e.symm_apply_eq.mpr he1.symm]
    change g 1 = 1
    simp [hg_def, LinearMap.comp_apply, pbw_hc_map_one, map_one]
  ·
    intro u

    show g'Q (e.symm (f u)) = g u
    have heu : e (K.mkQ u) = f u := by
      show f'Q (K.mkQ u) = f u
      rfl
    conv_lhs => rw [show e.symm (f u) = K.mkQ u from e.symm_apply_eq.mpr heu.symm]
    rfl

theorem pbw_verma_eval (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M)
      (_ : LieRingModule 𝔤 M) (_ : LieModule R 𝔤 M)
      (hM : IsHighestWeightModule Δ M wt)
      (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
      (_ : ∀ (x : 𝔤) (m : M),
        ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
      (phi : M →ₗ[R] R),
      phi hM.highestWeightVec = 1 ∧
      ∀ (u : UniversalEnvelopingAlgebra R 𝔤),
        phi (ueaAct u hM.highestWeightVec) = evalWeight Δ wt (HarishChandraMap Δ u) := by

  obtain ⟨M, instACG, instMod, instLRM, instLM, ⟨hVM⟩⟩ := verma_module_exists Δ wt

  let ueaAct := UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M)

  have hcompat : ∀ (x : 𝔤) (m : M),
      ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆ := by
    intro x m
    simp [ueaAct, LieModule.toEnd_apply_apply]

  obtain ⟨phi, hphi⟩ := pbw_verma_eval_any_hwm Δ wt M hVM.toIsHighestWeightModule ueaAct hcompat
  exact ⟨M, instACG, instMod, instLRM, instLM, hVM.toIsHighestWeightModule,
    ueaAct, hcompat, phi, hphi⟩


set_option maxHeartbeats 800000 in
theorem hc_eval_mul_central (Δ : TriangularDecomposition R 𝔤)
    (b : UniversalEnvelopingAlgebra R 𝔤)
    (c : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (wt : Δ.𝔥 →ₗ[R] R) :
    evalWeight Δ wt (HarishChandraMap Δ (b * (c : UniversalEnvelopingAlgebra R 𝔤))) =
    evalWeight Δ wt (HarishChandraMap Δ b) *
    evalWeight Δ wt (HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤)) := by

  obtain ⟨M, _, _, _, _, hM, ueaAct, hcompat, phi, hphi1, hphi_hc⟩ := pbw_verma_eval Δ wt

  rw [← hphi_hc (b * (c : UniversalEnvelopingAlgebra R 𝔤)),
      ← hphi_hc b,
      ← hphi_hc (c : UniversalEnvelopingAlgebra R 𝔤)]

  have hbc : (ueaAct (b * (c : UniversalEnvelopingAlgebra R 𝔤))) hM.highestWeightVec =
      (ueaAct b) ((ueaAct (c : UniversalEnvelopingAlgebra R 𝔤)) hM.highestWeightVec) := by
    rw [map_mul]; rfl
  rw [hbc]

  have hzv_wt : ∀ (h : Δ.𝔥),
      ⁅(h : 𝔤), (ueaAct (c : UniversalEnvelopingAlgebra R 𝔤)) hM.highestWeightVec⁆ =
      wt h • (ueaAct (c : UniversalEnvelopingAlgebra R 𝔤)) hM.highestWeightVec := by
    intro h

    rw [← hcompat (h : 𝔤) ((ueaAct (c : UniversalEnvelopingAlgebra R 𝔤)) hM.highestWeightVec)]

    have hmul_ih_c : (ueaAct (UniversalEnvelopingAlgebra.ι R (h : 𝔤) *
        (c : UniversalEnvelopingAlgebra R 𝔤))) hM.highestWeightVec =
        (ueaAct (UniversalEnvelopingAlgebra.ι R (h : 𝔤)))
        ((ueaAct (c : UniversalEnvelopingAlgebra R 𝔤)) hM.highestWeightVec) := by
      rw [map_mul]; rfl
    rw [← hmul_ih_c]

    have hcomm : (c : UniversalEnvelopingAlgebra R 𝔤) *
        UniversalEnvelopingAlgebra.ι R (h : 𝔤) =
        UniversalEnvelopingAlgebra.ι R (h : 𝔤) *
        (c : UniversalEnvelopingAlgebra R 𝔤) :=
      ((Subalgebra.mem_center_iff.mp c.prop) _).symm

    have hmul_c_ih : (ueaAct ((c : UniversalEnvelopingAlgebra R 𝔤) *
        UniversalEnvelopingAlgebra.ι R (h : 𝔤))) hM.highestWeightVec =
        (ueaAct (c : UniversalEnvelopingAlgebra R 𝔤))
        ((ueaAct (UniversalEnvelopingAlgebra.ι R (h : 𝔤))) hM.highestWeightVec) := by
      rw [map_mul]; rfl
    rw [← hcomm, hmul_c_ih]

    rw [hcompat (h : 𝔤) hM.highestWeightVec, hM.cartan_action h, map_smul]

  obtain ⟨chi, hchi⟩ := IsHighestWeightModule.highestWeightSpace_one_dim hM
    ((ueaAct (c : UniversalEnvelopingAlgebra R 𝔤)) hM.highestWeightVec) hzv_wt
  rw [hchi]

  rw [map_smul (ueaAct b)]
  simp only [map_smul phi, hphi1]
  simp only [smul_eq_mul]
  ring

theorem harishChandra_mul_central (Δ : TriangularDecomposition R 𝔤)
    (b : UniversalEnvelopingAlgebra R 𝔤)
    (c : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) :
    HarishChandraMap Δ (b * (c : UniversalEnvelopingAlgebra R 𝔤)) =
    HarishChandraMap Δ b * HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤) := by

  apply evalWeight_separates
  intro wt


  have h_lhs := hc_eval_mul_central Δ b c wt
  have h_rhs : evalWeight Δ wt (HarishChandraMap Δ b *
      HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤)) =
    evalWeight Δ wt (HarishChandraMap Δ b) *
    evalWeight Δ wt (HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤)) :=
    _root_.map_mul (evalWeight Δ wt) _ _
  rw [h_rhs, ← h_lhs]


theorem center_acts_by_scalar_on_hwm (Δ : TriangularDecomposition R 𝔤)
    (_wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hM : IsHighestWeightModule Δ M wt)
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (hcompat : ∀ (x : 𝔤) (m : M),
      ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) :
    ∃ (c : R), ∀ (m : M),
      ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) m = c • m := by

  have hz_comm : ∀ (u : UniversalEnvelopingAlgebra R 𝔤),
      u * (z : UniversalEnvelopingAlgebra R 𝔤) = (z : UniversalEnvelopingAlgebra R 𝔤) * u := by
    intro u; exact (Subalgebra.mem_center_iff.mp z.prop) u

  have hact_comm : ∀ (x : 𝔤) (m : M),
      ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) (ueaAct (UniversalEnvelopingAlgebra.ι R x) m) =
      ueaAct (UniversalEnvelopingAlgebra.ι R x) (ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) m) := by
    intro x m
    have h1 : ueaAct ((z : UniversalEnvelopingAlgebra R 𝔤) * UniversalEnvelopingAlgebra.ι R x) m =
        ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) (ueaAct (UniversalEnvelopingAlgebra.ι R x) m) := by
      have := map_mul ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) (UniversalEnvelopingAlgebra.ι R x)
      rw [this]; rfl
    have h2 : ueaAct (UniversalEnvelopingAlgebra.ι R x * (z : UniversalEnvelopingAlgebra R 𝔤)) m =
        ueaAct (UniversalEnvelopingAlgebra.ι R x) (ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) m) := by
      have := map_mul ueaAct (UniversalEnvelopingAlgebra.ι R x) (z : UniversalEnvelopingAlgebra R 𝔤)
      rw [this]; rfl
    rw [← h1, ← h2, hz_comm]

  have hlie_comm : ∀ (x : 𝔤) (m : M),
      ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) ⁅x, m⁆ =
      ⁅x, ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) m⁆ := by
    intro x m
    rw [← hcompat x m, ← hcompat x (ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) m)]
    exact hact_comm x m

  have hzv_wt : ∀ (h : Δ.𝔥),
      ⁅(h : 𝔤), ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) hM.highestWeightVec⁆ =
      wt h • ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) hM.highestWeightVec := by
    intro h
    rw [← hlie_comm (h : 𝔤) hM.highestWeightVec, hM.cartan_action h, map_smul]

  obtain ⟨c, hc⟩ := IsHighestWeightModule.highestWeightSpace_one_dim hM _ hzv_wt
  refine ⟨c, ?_⟩

  set S : LieSubmodule R 𝔤 M := {
    toSubmodule := {
      carrier := {m : M | ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) m = c • m}
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, ha, hb, smul_add]
      zero_mem' := by simp
      smul_mem' := by
        intro r m hm
        simp only [Set.mem_setOf_eq] at hm ⊢
        rw [map_smul, hm, smul_comm]
    }
    lie_mem := by
      intro x m hm
      simp only [Set.mem_setOf_eq] at hm ⊢
      rw [hlie_comm x m, hm, lie_smul]
  }

  have hv_in_S : hM.highestWeightVec ∈ S := by
    show ueaAct (z : UniversalEnvelopingAlgebra R 𝔤) hM.highestWeightVec = c • hM.highestWeightVec
    exact hc

  have hspan_le_S : LieSubmodule.lieSpan R 𝔤 {hM.highestWeightVec} ≤ S :=
    LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr hv_in_S)
  intro m
  exact (hM.generates ▸ hspan_le_S) (LieSubmodule.mem_top m)

theorem evalWeight_algAction_eq (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (g : wg.W) (wt : Δ.𝔥 →ₗ[R] R) (p : UniversalEnvelopingAlgebra R Δ.𝔥) :
    evalWeight Δ wt ((wg.algAction g) p) = evalWeight Δ (wg.dualAction g⁻¹ wt) p :=
  wg.algDualCompat g wt p

theorem hwm_central_scalar_eq_evalWeight (Δ : TriangularDecomposition R 𝔤)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hM : IsHighestWeightModule Δ M wt)
    (ueaAct : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (hcompat : ∀ (x : 𝔤) (m : M), ueaAct (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (c : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (s : R)
    (hs : ∀ (m : M), ueaAct (c : UniversalEnvelopingAlgebra R 𝔤) m = s • m) :
    s = evalWeight Δ wt (HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤)) := by


  obtain ⟨phi, hphi1, hphi_hc⟩ := pbw_verma_eval_any_hwm Δ wt M hM ueaAct hcompat

  have h := hphi_hc (c : UniversalEnvelopingAlgebra R 𝔤)

  rw [hs hM.highestWeightVec] at h
  simp only [map_smul, hphi1, smul_eq_mul, mul_one] at h
  exact h


theorem hc_W_invariance_axiom
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (c : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) :
    HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤) ∈ wg.invariantSubalgebra := by
  sorry

theorem verma_embedding_scalar_invariance
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    {M₁ : Type*} [AddCommGroup M₁] [Module R M₁] [LieRingModule 𝔤 M₁] [LieModule R 𝔤 M₁]
    {M₂ : Type*} [AddCommGroup M₂] [Module R M₂] [LieRingModule 𝔤 M₂] [LieModule R 𝔤 M₂]
    (wt : Δ.𝔥 →ₗ[R] R) (g : wg.W)
    (hM₁ : IsHighestWeightModule Δ M₁ wt)
    (hM₂ : IsHighestWeightModule Δ M₂ (wg.dualAction g wt))
    (ueaAct₁ : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M₁)
    (ueaAct₂ : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M₂)
    (hcompat₁ : ∀ (x : 𝔤) (m : M₁), ueaAct₁ (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (hcompat₂ : ∀ (x : 𝔤) (m : M₂), ueaAct₂ (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (c : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (s₁ s₂ : R)
    (hs₁ : ∀ (m : M₁), ueaAct₁ (c : UniversalEnvelopingAlgebra R 𝔤) m = s₁ • m)
    (hs₂ : ∀ (m : M₂), ueaAct₂ (c : UniversalEnvelopingAlgebra R 𝔤) m = s₂ • m) :
    s₁ = s₂ := by


  have hs₁_eq := hwm_central_scalar_eq_evalWeight Δ M₁ wt hM₁ ueaAct₁ hcompat₁ c s₁ hs₁
  have hs₂_eq := hwm_central_scalar_eq_evalWeight Δ M₂ (wg.dualAction g wt) hM₂ ueaAct₂ hcompat₂ c s₂ hs₂

  have hW_inv := hc_W_invariance_axiom Δ wg c

  have heval_eq : evalWeight Δ (wg.dualAction g wt)
      (HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤)) =
      evalWeight Δ wt (HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤)) := by
    have hinv := hW_inv g
    conv_lhs => rw [← hinv]
    rw [evalWeight_algAction_eq Δ wg g (wg.dualAction g wt)]

    rw [← wg.dualAction_mul g⁻¹ g wt, inv_mul_cancel, wg.dualAction_one]
  rw [hs₁_eq, hs₂_eq, heval_eq]

theorem harishChandra_verma_eval_invariance
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ) :
    ∀ (g : wg.W) (wt : Δ.𝔥 →ₗ[R] R)
        (c : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)),
        evalWeight Δ (wg.dualAction g wt)
          (HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤)) =
        evalWeight Δ wt
          (HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤)) := by
  intro g wt c

  obtain ⟨M₁, _, _, _, _, hM₁, ueaAct₁, hcompat₁, phi₁, hphi1₁, hphi_hc₁⟩ :=
    pbw_verma_eval Δ wt
  obtain ⟨M₂, _, _, _, _, hM₂, ueaAct₂, hcompat₂, phi₂, hphi1₂, hphi_hc₂⟩ :=
    pbw_verma_eval Δ (wg.dualAction g wt)

  obtain ⟨s₁, hs₁⟩ := center_acts_by_scalar_on_hwm Δ wg M₁ wt hM₁ ueaAct₁ hcompat₁ c
  obtain ⟨s₂, hs₂⟩ := center_acts_by_scalar_on_hwm Δ wg M₂ (wg.dualAction g wt) hM₂
    ueaAct₂ hcompat₂ c


  have hs₁_eq := hwm_central_scalar_eq_evalWeight Δ M₁ wt hM₁ ueaAct₁ hcompat₁ c s₁ hs₁
  have hs₂_eq := hwm_central_scalar_eq_evalWeight Δ M₂ (wg.dualAction g wt) hM₂
    ueaAct₂ hcompat₂ c s₂ hs₂

  have hscalar_eq := verma_embedding_scalar_invariance Δ wg wt g hM₁ hM₂
    ueaAct₁ ueaAct₂ hcompat₁ hcompat₂ c s₁ s₂ hs₁ hs₂


  rw [← hs₁_eq, ← hs₂_eq, hscalar_eq]


theorem filtered_graded_principle_for_hc
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ) :

    (∀ (c₁ c₂ : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)),
        HarishChandraMap Δ (c₁ : UniversalEnvelopingAlgebra R 𝔤) =
        HarishChandraMap Δ (c₂ : UniversalEnvelopingAlgebra R 𝔤) → c₁ = c₂) ∧

    (∀ (p : UniversalEnvelopingAlgebra R Δ.𝔥), p ∈ wg.invariantSubalgebra →
        ∃ c : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤),
            HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤) = p) := by sorry

theorem harishChandra_bijectivity
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ) :

    (∀ (c₁ c₂ : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)),
        HarishChandraMap Δ (c₁ : UniversalEnvelopingAlgebra R 𝔤) =
        HarishChandraMap Δ (c₂ : UniversalEnvelopingAlgebra R 𝔤) → c₁ = c₂) ∧

    (∀ (p : UniversalEnvelopingAlgebra R Δ.𝔥), p ∈ wg.invariantSubalgebra →
        ∃ c : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤),
            HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤) = p) :=
  filtered_graded_principle_for_hc Δ wg

theorem harishChandra_isomorphism_sorry
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ) :

    (∀ (c : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)),
        HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤) ∈ wg.invariantSubalgebra) ∧

    (∀ (c₁ c₂ : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)),
        HarishChandraMap Δ (c₁ : UniversalEnvelopingAlgebra R 𝔤) =
        HarishChandraMap Δ (c₂ : UniversalEnvelopingAlgebra R 𝔤) → c₁ = c₂) ∧

    (∀ (p : UniversalEnvelopingAlgebra R Δ.𝔥), p ∈ wg.invariantSubalgebra →
        ∃ c : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤),
            HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤) = p) := by
  have hVerma := harishChandra_verma_eval_invariance Δ wg
  have hBij := harishChandra_bijectivity Δ wg
  refine ⟨fun c g => ?_, hBij.1, hBij.2⟩


  apply evalWeight_separates
  intro wt

  rw [evalWeight_algAction_eq Δ wg g wt]

  exact hVerma g⁻¹ wt c

theorem WeylGroupData.dualAction_inv_cancel_left {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ) (g : wg.W) (wt : Δ.𝔥 →ₗ[R] R) :
    wg.dualAction g⁻¹ (wg.dualAction g wt) = wt := by
  rw [← wg.dualAction_mul g⁻¹ g wt, inv_mul_cancel, wg.dualAction_one]

theorem harishChandra_W_invariant
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (c : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (g : wg.W) :
    (wg.algAction g) (HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤)) =
    HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤) :=
  (harishChandra_isomorphism_sorry Δ wg).1 c g

theorem hc_eval_weyl_invariant_from_isomorphism
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (g : wg.W) (wt : Δ.𝔥 →ₗ[R] R)
    (c : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) :
    evalWeight Δ (wg.dualAction g wt) (HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤)) =
    evalWeight Δ wt (HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤)) := by
  have hinv := harishChandra_W_invariant Δ wg c g
  conv_lhs => rw [← hinv]

  rw [evalWeight_algAction_eq Δ wg g (wg.dualAction g wt)]
  rw [wg.dualAction_inv_cancel_left g wt]

theorem weyl_linked_central_scalar_eq
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (M₁ : Type*) [AddCommGroup M₁] [Module R M₁] [LieRingModule 𝔤 M₁] [LieModule R 𝔤 M₁]
    (M₂ : Type*) [AddCommGroup M₂] [Module R M₂] [LieRingModule 𝔤 M₂] [LieModule R 𝔤 M₂]
    (wt : Δ.𝔥 →ₗ[R] R) (g : wg.W)
    (hM₁ : IsHighestWeightModule Δ M₁ wt)
    (hM₂ : IsHighestWeightModule Δ M₂ (wg.dualAction g wt))
    (ueaAct₁ : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M₁)
    (ueaAct₂ : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M₂)
    (hcompat₁ : ∀ (x : 𝔤) (m : M₁), ueaAct₁ (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (hcompat₂ : ∀ (x : 𝔤) (m : M₂), ueaAct₂ (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (c : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (s₁ s₂ : R)
    (hs₁ : ∀ (m : M₁), ueaAct₁ (c : UniversalEnvelopingAlgebra R 𝔤) m = s₁ • m)
    (hs₂ : ∀ (m : M₂), ueaAct₂ (c : UniversalEnvelopingAlgebra R 𝔤) m = s₂ • m) :
    s₁ = s₂ := by
  have h₁ := hwm_central_scalar_eq_evalWeight Δ M₁ wt hM₁ ueaAct₁ hcompat₁ c s₁ hs₁
  have h₂ := hwm_central_scalar_eq_evalWeight Δ M₂ (wg.dualAction g wt) hM₂ ueaAct₂ hcompat₂ c s₂ hs₂
  have h₃ := hc_eval_weyl_invariant_from_isomorphism Δ wg g wt c
  rw [h₁, h₂, h₃]

theorem verma_embedding_evalWeight_invariant
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (g : wg.W) (wt : Δ.𝔥 →ₗ[R] R)
    (c : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) :
    evalWeight Δ wt (HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤)) =
    evalWeight Δ (wg.dualAction g wt)
      (HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤)) := by

  obtain ⟨M₁, _, _, _, _, hM₁, ueaAct₁, hcompat₁, phi₁, hphi1₁, hphi_hc₁⟩ :=
    pbw_verma_eval Δ wt
  obtain ⟨M₂, _, _, _, _, hM₂, ueaAct₂, hcompat₂, phi₂, hphi1₂, hphi_hc₂⟩ :=
    pbw_verma_eval Δ (wg.dualAction g wt)

  rw [← hphi_hc₁ (c : UniversalEnvelopingAlgebra R 𝔤)]
  rw [← hphi_hc₂ (c : UniversalEnvelopingAlgebra R 𝔤)]

  obtain ⟨s₁, hs₁⟩ := center_acts_by_scalar_on_hwm Δ wg M₁ wt hM₁ ueaAct₁ hcompat₁ c
  obtain ⟨s₂, hs₂⟩ := center_acts_by_scalar_on_hwm Δ wg M₂ (wg.dualAction g wt) hM₂
    ueaAct₂ hcompat₂ c

  rw [hs₁ hM₁.highestWeightVec, hs₂ hM₂.highestWeightVec]
  simp only [map_smul, hphi1₁, hphi1₂, smul_eq_mul, mul_one]

  exact weyl_linked_central_scalar_eq Δ wg M₁ M₂ wt g hM₁ hM₂
    ueaAct₁ ueaAct₂ hcompat₁ hcompat₂ c s₁ s₂ hs₁ hs₂

theorem verma_embedding_central_scalar_invariant (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ) (g : wg.W) (wt : Δ.𝔥 →ₗ[R] R)
    (c : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) :
    evalWeight Δ wt (HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤)) =
    evalWeight Δ (wg.dualAction g wt)
      (HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤)) := by
  exact verma_embedding_evalWeight_invariant Δ wg g wt c

theorem weyl_linked_same_central_scalar (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (M₁ : Type*) [AddCommGroup M₁] [Module R M₁] [LieRingModule 𝔤 M₁] [LieModule R 𝔤 M₁]
    (M₂ : Type*) [AddCommGroup M₂] [Module R M₂] [LieRingModule 𝔤 M₂] [LieModule R 𝔤 M₂]
    (wt : Δ.𝔥 →ₗ[R] R) (g : wg.W)
    (hM₁ : IsHighestWeightModule Δ M₁ wt)
    (hM₂ : IsHighestWeightModule Δ M₂ (wg.dualAction g wt))
    (ueaAct₁ : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M₁)
    (ueaAct₂ : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M₂)
    (hcompat₁ : ∀ (x : 𝔤) (m : M₁), ueaAct₁ (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (hcompat₂ : ∀ (x : 𝔤) (m : M₂), ueaAct₂ (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (c : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (s₁ s₂ : R)
    (hs₁ : ∀ (m : M₁), ueaAct₁ (c : UniversalEnvelopingAlgebra R 𝔤) m = s₁ • m)
    (hs₂ : ∀ (m : M₂), ueaAct₂ (c : UniversalEnvelopingAlgebra R 𝔤) m = s₂ • m) :
    s₂ = s₁ := by

  have hs₁_eq := hwm_central_scalar_eq_evalWeight Δ M₁ wt hM₁ ueaAct₁ hcompat₁ c s₁ hs₁

  have hs₂_eq := hwm_central_scalar_eq_evalWeight Δ M₂ (wg.dualAction g wt) hM₂
    ueaAct₂ hcompat₂ c s₂ hs₂

  have heval_eq := verma_embedding_central_scalar_invariant Δ wg g wt c

  rw [hs₁_eq, hs₂_eq, heval_eq]

theorem hc_eval_weyl_invariant (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (g : wg.W) (wt : Δ.𝔥 →ₗ[R] R)
    (c : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) :
    evalWeight Δ (wg.dualAction g wt) (HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤)) =
    evalWeight Δ wt (HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤)) := by

  obtain ⟨M₁, _, _, _, _, hM₁, ueaAct₁, hcompat₁, phi₁, hphi1₁, hphi_hc₁⟩ :=
    pbw_verma_eval Δ wt

  obtain ⟨M₂, _, _, _, _, hM₂, ueaAct₂, hcompat₂, phi₂, hphi1₂, hphi_hc₂⟩ :=
    pbw_verma_eval Δ (wg.dualAction g wt)

  rw [← hphi_hc₁]
  rw [← hphi_hc₂]

  obtain ⟨s₁, hs₁⟩ := center_acts_by_scalar_on_hwm Δ wg M₁ wt hM₁ ueaAct₁ hcompat₁ c
  obtain ⟨s₂, hs₂⟩ := center_acts_by_scalar_on_hwm Δ wg M₂ (wg.dualAction g wt) hM₂ ueaAct₂
    hcompat₂ c

  rw [hs₁ hM₁.highestWeightVec, hs₂ hM₂.highestWeightVec]
  simp only [map_smul, hphi1₁, hphi1₂, smul_eq_mul, mul_one]


  exact weyl_linked_same_central_scalar Δ wg M₁ M₂ wt g hM₁ hM₂ ueaAct₁ ueaAct₂
    hcompat₁ hcompat₂ c s₁ s₂ hs₁ hs₂


theorem harishChandra_maps_to_W_invariants (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (c : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) :
    HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤) ∈ wg.invariantSubalgebra := by

  intro g

  apply evalWeight_separates
  intro wt


  rw [evalWeight_algAction_eq Δ wg g wt]
  exact hc_eval_weyl_invariant Δ wg g⁻¹ wt c

theorem harishChandra_map_one (Δ : TriangularDecomposition R 𝔤) :
    HarishChandraMap Δ (1 : UniversalEnvelopingAlgebra R 𝔤) = 1 := by
  apply evalWeight_separates
  intro wt
  obtain ⟨M, _, _, _, _, hM, ueaAct, hcompat, phi, hphi1, hphi_hc⟩ := pbw_verma_eval Δ wt
  rw [← hphi_hc 1]
  simp [map_one, hphi1]

theorem harishChandra_map_algebraMap (Δ : TriangularDecomposition R 𝔤) (r : R) :
    HarishChandraMap Δ (algebraMap R _ r) = algebraMap R _ r := by
  simp [Algebra.algebraMap_eq_smul_one, map_smul, harishChandra_map_one]

def HarishChandraAlgHom (Δ : TriangularDecomposition R 𝔤) :
    ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R]
    (UniversalEnvelopingAlgebra R Δ.𝔥) where
  toFun c := HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤)
  map_one' := by simp [harishChandra_map_one]
  map_mul' c₁ c₂ := by
    show HarishChandraMap Δ ((c₁ : UniversalEnvelopingAlgebra R 𝔤) *
      (c₂ : UniversalEnvelopingAlgebra R 𝔤)) =
      HarishChandraMap Δ (c₁ : UniversalEnvelopingAlgebra R 𝔤) *
      HarishChandraMap Δ (c₂ : UniversalEnvelopingAlgebra R 𝔤)
    exact harishChandra_mul_central Δ (c₁ : UniversalEnvelopingAlgebra R 𝔤) c₂
  map_zero' := by simp [map_zero]
  map_add' c₁ c₂ := by simp [map_add]
  commutes' r := by
    show HarishChandraMap Δ (algebraMap R _ r) = algebraMap R _ r
    exact harishChandra_map_algebraMap Δ r

def HarishChandraAlgHomToInvariant (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ) :
    ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R]
    ↥(wg.invariantSubalgebra) :=
  (HarishChandraAlgHom Δ).codRestrict wg.invariantSubalgebra
    (fun c => harishChandra_maps_to_W_invariants Δ wg c)


theorem chevalley_and_filtered_graded
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ) :
    Function.Bijective (HarishChandraAlgHomToInvariant Δ wg) := by
  obtain ⟨hW, hInj, hSurj⟩ := harishChandra_isomorphism_sorry Δ wg
  constructor
  ·
    intro c₁ c₂ h
    apply hInj


    have hval := congrArg Subtype.val h

    exact hval
  ·
    intro ⟨p, hp⟩
    obtain ⟨c, hc⟩ := hSurj p hp
    exact ⟨c, Subtype.ext (show (HarishChandraAlgHomToInvariant Δ wg c).val = p from hc)⟩

theorem hc_injective_of_filtered_graded
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ) :
    Function.Injective (HarishChandraAlgHomToInvariant Δ wg) :=
  (chevalley_and_filtered_graded Δ wg).1

theorem hc_surjective_of_filtered_graded
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ) :
    Function.Surjective (HarishChandraAlgHomToInvariant Δ wg) :=
  (chevalley_and_filtered_graded Δ wg).2

theorem filtered_graded_bijectivity_principle
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ) :
    Function.Bijective (HarishChandraAlgHomToInvariant Δ wg) :=
  chevalley_and_filtered_graded Δ wg

theorem harishChandra_bijective (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ) :
    Function.Bijective (HarishChandraAlgHomToInvariant Δ wg) :=
  filtered_graded_bijectivity_principle Δ wg

theorem harishChandra_injective_of_chevalley
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (c : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (h : HarishChandraMap Δ (c : UniversalEnvelopingAlgebra R 𝔤) = 0) :
    (c : UniversalEnvelopingAlgebra R 𝔤) = 0 := by

  have hinj := (harishChandra_bijective Δ wg).1

  rw [HarishChandraAlgHomToInvariant, AlgHom.injective_codRestrict] at hinj

  have h0 : HarishChandraAlgHom Δ c = 0 := h

  have hc0 : c = (0 : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) := by
    apply hinj
    rw [h0, map_zero]
  rw [hc0]; simp

theorem harishChandra_center_injective (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (c₁ c₂ : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (h : HarishChandraMap Δ (c₁ : UniversalEnvelopingAlgebra R 𝔤) =
         HarishChandraMap Δ (c₂ : UniversalEnvelopingAlgebra R 𝔤)) :
    c₁ = c₂ := by

  ext

  have hd : HarishChandraMap Δ ((c₁ : UniversalEnvelopingAlgebra R 𝔤) -
      (c₂ : UniversalEnvelopingAlgebra R 𝔤)) = 0 := by
    rw [map_sub, h, sub_self]

  have hzero : (↑(c₁ - c₂) : UniversalEnvelopingAlgebra R 𝔤) = 0 :=
    harishChandra_injective_of_chevalley Δ wg (c₁ - c₂) (by rwa [Subalgebra.coe_sub])


  rwa [Subalgebra.coe_sub, sub_eq_zero] at hzero

theorem chevalley_restriction_surjectivity
    (R : Type*) [CommRing R] (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (p : UniversalEnvelopingAlgebra R Δ.𝔥) (hp : p ∈ wg.invariantSubalgebra) :
    ∃ c : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)),
      HarishChandraAlgHom Δ c = p := by

  have hsurj := (harishChandra_bijective Δ wg).2

  obtain ⟨c, hc⟩ := hsurj ⟨p, hp⟩
  exact ⟨c, congr_arg Subtype.val hc⟩
def HarishChandraIso (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ) :
    ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) ≃ₐ[R] ↥(wg.invariantSubalgebra) :=
  AlgEquiv.ofBijective (HarishChandraAlgHomToInvariant Δ wg) (harishChandra_bijective Δ wg)

abbrev chevalley_restriction_hc_iso (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ) :
    ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) ≃ₐ[R] ↥(wg.invariantSubalgebra) :=
  HarishChandraIso Δ wg


def HarishChandraHom (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ) :
    ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R]
    ↥(wg.invariantSubalgebra) :=
  (HarishChandraIso Δ wg).toAlgHom

structure HasInfinitesimalCharacter
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (chi : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) where
  ueaAction : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M
  compat : ∀ (x : 𝔤) (m : M),
    ueaAction (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆
  center_acts_by_scalar : ∀ (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (m : M), ueaAction (z : UniversalEnvelopingAlgebra R 𝔤) m = chi z • m


theorem schur_lie_module_scalar
    {k : Type*} [Field k] [IsAlgClosed k]
    {𝔤' : Type*} [LieRing 𝔤'] [LieAlgebra k 𝔤']
    {M : Type*} [AddCommGroup M] [Module k M]
    [LieRingModule 𝔤' M] [LieModule k 𝔤' M]
    [Module.Finite k M]
    (hirr : LieModule.IsIrreducible k 𝔤' M)
    (T : Module.End k M)
    (hT : ∀ (x : 𝔤') (m : M), T ⁅x, m⁆ = ⁅x, T m⁆) :
    ∃ c : k, ∀ m : M, T m = c • m := by

  have hM : Nontrivial M := by
    have hne : (⊥ : LieSubmodule k 𝔤' M) ≠ ⊤ := IsSimpleOrder.bot_ne_top
    by_contra h; rw [not_nontrivial_iff_subsingleton] at h
    exact hne (Subsingleton.elim _ _)

  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T

  set S : Module.End k M := T - c • (1 : Module.End k M) with hS_def

  have hS_comm : ∀ (x : 𝔤') (m : M), S ⁅x, m⁆ = ⁅x, S m⁆ := by
    intro x m
    simp only [hS_def, LinearMap.sub_apply, LinearMap.smul_apply]
    change T ⁅x, m⁆ - c • (⁅x, m⁆) = ⁅x, T m - c • m⁆
    rw [hT, lie_sub, lie_smul]

  let kerS : LieSubmodule k 𝔤' M :=
    { LinearMap.ker S with
      lie_mem := by
        intro x m hm
        show S ⁅x, m⁆ = 0
        rw [hS_comm x m]
        have : S m = 0 := hm
        rw [this, lie_zero] }

  have hker_ne_bot : kerS ≠ ⊥ := by
    intro h
    have hker_bot : (kerS : Submodule k M) = ⊥ :=
      (LieSubmodule.toSubmodule_eq_bot kerS).mpr h
    have : T.eigenspace c = ⊥ := by
      rw [Module.End.eigenspace_def]
      exact hker_bot
    exact (Module.End.hasEigenvalue_iff.mp hc) this

  have hker_top : kerS = ⊤ := by
    cases eq_bot_or_eq_top kerS with
    | inl h => exact absurd h hker_ne_bot
    | inr h => exact h

  have hker_sub_top : LinearMap.ker S = ⊤ :=
    (LieSubmodule.toSubmodule_eq_top kerS).mpr hker_top
  have hS_zero : S = 0 := LinearMap.ker_eq_top.mp hker_sub_top

  use c
  intro m
  have hSm : S m = 0 := by simp [hS_zero]
  change T m - c • m = 0 at hSm
  exact sub_eq_zero.mp hSm

set_option maxHeartbeats 800000 in

theorem weyl_orbit_separation (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (mu nu : Δ.𝔥 →ₗ[R] R)
    (h : ∀ p : wg.invariantSubalgebra,
      evalWeight Δ mu (p : UniversalEnvelopingAlgebra R Δ.𝔥) =
      evalWeight Δ nu (p : UniversalEnvelopingAlgebra R Δ.𝔥)) :
    ∃ w : wg.W, nu = wg.dualAction w mu := by


  apply wg.orbitSeparation mu nu
  intro p hp
  exact h ⟨p, hp⟩

theorem evalWeight_weyl_invariant (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (w : wg.W) (mu : Δ.𝔥 →ₗ[R] R)
    (p : wg.invariantSubalgebra) :
    evalWeight Δ (wg.dualAction w mu) (p : UniversalEnvelopingAlgebra R Δ.𝔥) =
    evalWeight Δ mu (p : UniversalEnvelopingAlgebra R Δ.𝔥) := by


  have key := evalWeight_algAction_eq Δ wg w⁻¹ mu (p : UniversalEnvelopingAlgebra R Δ.𝔥)
  rw [p.prop w⁻¹] at key
  rw [inv_inv] at key
  exact key.symm

theorem evalHC_eq_evalWeight_comp_hcIso (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (evalHC : (Δ.𝔥 →ₗ[R] R) →
      (↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R))
    (hdef : ∀ (mu : Δ.𝔥 →ₗ[R] R) (z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))),
      evalHC mu z = evalWeight Δ (mu + wg.ρ)
        ((chevalley_restriction_hc_iso Δ wg z : wg.invariantSubalgebra) : UniversalEnvelopingAlgebra R Δ.𝔥))
    (mu : Δ.𝔥 →ₗ[R] R) (z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))) :
    evalHC mu z = evalWeight Δ (mu + wg.ρ)
      ((chevalley_restriction_hc_iso Δ wg z : wg.invariantSubalgebra) : UniversalEnvelopingAlgebra R Δ.𝔥) :=
  hdef mu z

theorem infinitesimalCharacter_eq_iff_shiftedWeylOrbit
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (evalHC : (Δ.𝔥 →ₗ[R] R) →
      (↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R))
    (hdef : ∀ (mu : Δ.𝔥 →ₗ[R] R) (z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))),
      evalHC mu z = evalWeight Δ (mu + wg.ρ)
        ((chevalley_restriction_hc_iso Δ wg z : wg.invariantSubalgebra) : UniversalEnvelopingAlgebra R Δ.𝔥))
    (mu nu : Δ.𝔥 →ₗ[R] R) :
    evalHC mu = evalHC nu ↔
    ∃ w : wg.W, nu = wg.shiftedAction w mu := by

  constructor
  ·
    intro heq

    have heval_eq : ∀ z, evalHC mu z = evalHC nu z := fun z => by rw [heq]


    have hweight_eq : ∀ z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)),
        evalWeight Δ (mu + wg.ρ)
          ((chevalley_restriction_hc_iso Δ wg z : wg.invariantSubalgebra) : UniversalEnvelopingAlgebra R Δ.𝔥) =
        evalWeight Δ (nu + wg.ρ)
          ((chevalley_restriction_hc_iso Δ wg z : wg.invariantSubalgebra) : UniversalEnvelopingAlgebra R Δ.𝔥) := by
      intro z
      rw [← evalHC_eq_evalWeight_comp_hcIso Δ wg evalHC hdef mu z,
          ← evalHC_eq_evalWeight_comp_hcIso Δ wg evalHC hdef nu z]
      exact heval_eq z

    have hinv_eq : ∀ p : wg.invariantSubalgebra,
        evalWeight Δ (mu + wg.ρ) (p : UniversalEnvelopingAlgebra R Δ.𝔥) =
        evalWeight Δ (nu + wg.ρ) (p : UniversalEnvelopingAlgebra R Δ.𝔥) := by
      intro p

      let z := (chevalley_restriction_hc_iso Δ wg).symm p
      have hz : chevalley_restriction_hc_iso Δ wg z = p :=
        AlgEquiv.apply_symm_apply (chevalley_restriction_hc_iso Δ wg) p
      specialize hweight_eq z
      rwa [hz] at hweight_eq

    obtain ⟨w, hw⟩ := weyl_orbit_separation Δ wg (mu + wg.ρ) (nu + wg.ρ) hinv_eq

    refine ⟨w, ?_⟩


    show nu = wg.shiftedAction w mu
    simp only [WeylGroupData.shiftedAction]


    have := hw

    calc nu = nu + wg.ρ - wg.ρ := by simp [add_sub_cancel_right]
      _ = wg.dualAction w (mu + wg.ρ) - wg.ρ := by rw [this]
  ·
    rintro ⟨w, rfl⟩

    ext z

    rw [evalHC_eq_evalWeight_comp_hcIso Δ wg evalHC hdef mu z,
        evalHC_eq_evalWeight_comp_hcIso Δ wg evalHC hdef (wg.shiftedAction w mu) z]

    have hshift : wg.shiftedAction w mu + wg.ρ = wg.dualAction w (mu + wg.ρ) := by
      simp [WeylGroupData.shiftedAction, sub_add_cancel]
    rw [hshift]

    exact (evalWeight_weyl_invariant Δ wg w (mu + wg.ρ) (chevalley_restriction_hc_iso Δ wg z)).symm

end
