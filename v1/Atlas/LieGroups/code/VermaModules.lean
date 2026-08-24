/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Algebra.Lie.Submodule
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Order.Atoms
import Mathlib.RingTheory.Congruence.Defs

noncomputable section

universe u_mod

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

structure TriangularDecomposition where
  𝔥 : LieSubalgebra R 𝔤
  𝔫_pos : LieSubalgebra R 𝔤
  𝔫_neg : LieSubalgebra R 𝔤
  is_cartan : 𝔥.IsCartanSubalgebra
  h_abelian : IsLieAbelian 𝔥
  decomp_exists : ∀ x : 𝔤, ∃ (n_neg : 𝔫_neg) (h : 𝔥) (n_pos : 𝔫_pos),
    x = (n_neg : 𝔤) + (h : 𝔤) + (n_pos : 𝔤)
  decomp_unique : ∀ (n₁ n₁' : 𝔫_neg) (h₁ h₁' : 𝔥) (p₁ p₁' : 𝔫_pos),
    (n₁ : 𝔤) + (h₁ : 𝔤) + (p₁ : 𝔤) = (n₁' : 𝔤) + (h₁' : 𝔤) + (p₁' : 𝔤) →
    n₁ = n₁' ∧ h₁ = h₁' ∧ p₁ = p₁'

variable {R 𝔤}

namespace TriangularDecomposition

variable (Δ : TriangularDecomposition R 𝔤)

def 𝔟 : LieSubalgebra R 𝔤 := Δ.𝔥 ⊔ Δ.𝔫_pos

def weightSubspace
    (M : Type u_mod) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (μ : Δ.𝔥 →ₗ[R] R) : Submodule R M where
  carrier := {m : M | ∀ h : Δ.𝔥, ⁅(h : 𝔤), m⁆ = μ h • m}
  add_mem' {a b} ha hb h := by rw [lie_add, ha h, hb h, smul_add]
  zero_mem' h := by rw [lie_zero, smul_zero]
  smul_mem' c _ hm h := by rw [LieModule.lie_smul, hm h, smul_comm]

theorem weightSubspace_eq_mathlib
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (μ : Δ.𝔥 →ₗ[R] R) :
    Δ.weightSubspace M μ =
    (LieModule.weightSpace (R := R) (L := Δ.𝔥) M (μ ·)).toSubmodule := by
  ext m
  constructor
  · intro hm
    rw [LieSubmodule.mem_toSubmodule, LieModule.mem_weightSpace]
    intro x; exact hm x
  · intro hm
    rw [LieSubmodule.mem_toSubmodule, LieModule.mem_weightSpace] at hm
    intro h; exact hm h

end TriangularDecomposition

structure IsHighestWeightModule
    (Δ : TriangularDecomposition R 𝔤)
    (M : Type u_mod) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R) where
  highestWeightVec : M
  hwv_ne_zero : highestWeightVec ≠ 0
  cartan_action : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), highestWeightVec⁆ = wt h • highestWeightVec
  npos_action : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), highestWeightVec⁆ = 0
  generates : LieSubmodule.lieSpan R 𝔤 {highestWeightVec} = ⊤

structure IsVermaModule
    (Δ : TriangularDecomposition R 𝔤)
    (M : Type u_mod) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    extends IsHighestWeightModule Δ M wt where
  universal_map :
    ∀ (V : Type u_mod) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
      (v : V),
      (∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = wt h • v) →
      (∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v⁆ = 0) →
      ∃ (η : M →ₗ⁅R, 𝔤⁆ V), η highestWeightVec = v
  universal_unique :
    ∀ (V : Type u_mod) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
      (η₁ η₂ : M →ₗ⁅R, 𝔤⁆ V),
      η₁ highestWeightVec = η₂ highestWeightVec → η₁ = η₂

def ueaSubalgAction (𝔫 : LieSubalgebra R 𝔤)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    UniversalEnvelopingAlgebra R (↥𝔫) →ₐ[R] Module.End R M :=
  UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R (↥𝔫) M)

def instModuleUEASubalg (𝔫 : LieSubalgebra R 𝔤)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    Module (UniversalEnvelopingAlgebra R (↥𝔫)) M :=
  Module.compHom M (ueaSubalgAction 𝔫 M).toRingHom


section UEASubalgHelpers

variable {R : Type*} [CommRing R]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {M : Type*} [AddCommGroup M] [Module R M]
  [LieRingModule 𝔤 M] [LieModule R 𝔤 M]

lemma ueaSubalg_mul_apply
    (u₁ u₂ : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) (m : M) :
    (ueaSubalgAction Δ.𝔫_neg M (u₁ * u₂)) m =
    (ueaSubalgAction Δ.𝔫_neg M u₁) ((ueaSubalgAction Δ.𝔫_neg M u₂) m) := by
  change ((ueaSubalgAction Δ.𝔫_neg M).toRingHom (u₁ * u₂)) m = _
  rw [map_mul]; rfl

lemma ueaSubalg_add_apply
    (u₁ u₂ : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) (m : M) :
    (ueaSubalgAction Δ.𝔫_neg M (u₁ + u₂)) m =
    (ueaSubalgAction Δ.𝔫_neg M u₁) m + (ueaSubalgAction Δ.𝔫_neg M u₂) m := by
  change ((ueaSubalgAction Δ.𝔫_neg M).toRingHom (u₁ + u₂)) m = _
  rw [map_add]; rfl

lemma ueaSubalg_smul_apply
    (r : R) (u₀ : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) (m : M) :
    (ueaSubalgAction Δ.𝔫_neg M (r • u₀)) m =
    r • ((ueaSubalgAction Δ.𝔫_neg M u₀) m) := by
  have : ueaSubalgAction Δ.𝔫_neg M (r • u₀) = r • ueaSubalgAction Δ.𝔫_neg M u₀ :=
    map_smul (ueaSubalgAction Δ.𝔫_neg M) r u₀
  rw [this]; rfl

lemma ueaSubalg_one_apply (m : M) :
    (ueaSubalgAction Δ.𝔫_neg M 1) m = m := by
  change ((ueaSubalgAction Δ.𝔫_neg M).toRingHom 1) m = m
  rw [map_one]; rfl

lemma ueaSubalg_ι_apply (n : ↥Δ.𝔫_neg) (m : M) :
    (ueaSubalgAction Δ.𝔫_neg M (UniversalEnvelopingAlgebra.ι R n)) m = ⁅(n : 𝔤), m⁆ := by
  change ((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R (↥Δ.𝔫_neg) M))
    (UniversalEnvelopingAlgebra.ι R n)) m = ⁅(n : 𝔤), m⁆
  rw [UniversalEnvelopingAlgebra.lift_ι_apply, LieModule.toEnd_apply_apply]; rfl

lemma ueaSubalg_algebraMap_apply (r : R) (m : M) :
    (ueaSubalgAction Δ.𝔫_neg M (algebraMap R _ r)) m = r • m := by
  have : ueaSubalgAction Δ.𝔫_neg M (algebraMap R _ r) = algebraMap R _ r :=
    AlgHom.commutes (ueaSubalgAction Δ.𝔫_neg M) r
  rw [this, Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply]; rfl

end UEASubalgHelpers

set_option maxHeartbeats 3200000 in
theorem nminus_orbit_lie_stable
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt)
    (x : 𝔤) (m : M)
    (hm : ∃ u : UniversalEnvelopingAlgebra R Δ.𝔫_neg,
      (ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec = m) :
    ∃ u' : UniversalEnvelopingAlgebra R Δ.𝔫_neg,
      (ueaSubalgAction Δ.𝔫_neg M u') hM.highestWeightVec = ⁅x, m⁆ := by
  obtain ⟨u, hu⟩ := hm
  subst hu
  let Φ := ueaSubalgAction Δ.𝔫_neg M
  let vhw := hM.highestWeightVec


  suffices Q : ∀ (t : TensorAlgebra R ↥Δ.𝔫_neg) (y : 𝔤) (s : M),
      (∃ u₀, (Φ u₀) vhw = s) →
      (∀ z : 𝔤, ∃ u₀, (Φ u₀) vhw = ⁅z, s⁆) →
      ∃ u₀, (Φ u₀) vhw =
        ⁅y, (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) t)) s⁆ by

    have hvhw : ∃ u₀, (Φ u₀) vhw = vhw := ⟨1, ueaSubalg_one_apply vhw⟩

    have base : ∀ (y : 𝔤), ∃ u₀, (Φ u₀) vhw = ⁅y, vhw⁆ := by
      intro y
      obtain ⟨n_neg, h, n_pos, hdecomp⟩ := Δ.decomp_exists y
      rw [hdecomp, add_lie, add_lie, hM.npos_action n_pos, hM.cartan_action h]
      simp only [add_zero]
      exact ⟨UniversalEnvelopingAlgebra.ι R n_neg + algebraMap R _ (wt h),
        by rw [ueaSubalg_add_apply, ueaSubalg_ι_apply, ueaSubalg_algebraMap_apply]⟩

    obtain ⟨t, rfl⟩ := RingQuot.mkAlgHom_surjective R
      (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) u
    exact Q t x vhw hvhw base

  intro t
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    intro y s hs hstable
    have heq : (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg)
        (algebraMap R _ r))) s = r • s := by
      have : RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg)
        (algebraMap R _ r) = algebraMap R _ r := AlgHom.commutes _ r
      rw [this]; exact ueaSubalg_algebraMap_apply r s
    rw [heq, lie_smul]
    obtain ⟨u', hu'⟩ := hstable y
    exact ⟨r • u', by rw [ueaSubalg_smul_apply, hu']⟩
  | ι n =>
    intro y s hs hstable
    have hι : (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg)
        (TensorAlgebra.ι R n))) s = ⁅(n : 𝔤), s⁆ :=
      ueaSubalg_ι_apply n s
    rw [hι, leibniz_lie]
    obtain ⟨u₁, hu₁⟩ := hstable ⁅y, (n : 𝔤)⁆
    obtain ⟨u₂, hu₂⟩ := hstable y
    exact ⟨u₁ + UniversalEnvelopingAlgebra.ι R n * u₂,
      by rw [ueaSubalg_add_apply, ueaSubalg_mul_apply, ueaSubalg_ι_apply, hu₁, hu₂]⟩
  | add a b iha ihb =>
    intro y s hs hstable
    have hadd : (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg)
        (a + b))) s =
      (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) a)) s +
      (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) b)) s := by
      show (ueaSubalgAction Δ.𝔫_neg M _) s = _
      rw [map_add]; exact ueaSubalg_add_apply _ _ s
    rw [hadd, lie_add]
    obtain ⟨u₁, hu₁⟩ := iha y s hs hstable
    obtain ⟨u₂, hu₂⟩ := ihb y s hs hstable
    exact ⟨u₁ + u₂, by rw [ueaSubalg_add_apply, hu₁, hu₂]⟩
  | mul a b iha ihb =>
    intro y s hs hstable
    have hmul : (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg)
        (a * b))) s =
      (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) a))
        ((Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) b)) s) := by
      show (ueaSubalgAction Δ.𝔫_neg M _) s = _
      rw [map_mul]; exact ueaSubalg_mul_apply _ _ s
    rw [hmul]
    set s' := (Φ (RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) b)) s
    have hs' : ∃ u₀, (Φ u₀) vhw = s' := by
      obtain ⟨u_s, hu_s⟩ := hs
      let mkb : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg :=
        RingQuot.mkAlgHom R (UniversalEnvelopingAlgebra.Rel R ↥Δ.𝔫_neg) b
      exact ⟨mkb * u_s, by rw [ueaSubalg_mul_apply, hu_s]⟩
    have hstable' : ∀ z : 𝔤, ∃ u₀, (Φ u₀) vhw = ⁅z, s'⁆ :=
      fun z => ihb z s hs hstable
    exact iha y s' hs' hstable'

theorem pbw_verma_surjective
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt) :
    letI := instModuleUEASubalg Δ.𝔫_neg M
    Function.Surjective
      (LinearMap.toSpanSingleton (UniversalEnvelopingAlgebra R Δ.𝔫_neg) M
        hM.highestWeightVec) := by
  letI := instModuleUEASubalg Δ.𝔫_neg M
  intro m

  set S : Set M := {m : M | ∃ u : UniversalEnvelopingAlgebra R Δ.𝔫_neg,
    (ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec = m} with hS_def


  have hS_add : ∀ a b : M, a ∈ S → b ∈ S → a + b ∈ S := by
    rintro a b ⟨u₁, rfl⟩ ⟨u₂, rfl⟩
    exact ⟨u₁ + u₂, by simp [map_add, LinearMap.add_apply]⟩
  have hS_zero : (0 : M) ∈ S := ⟨0, by simp [map_zero, LinearMap.zero_apply]⟩
  have hS_smul : ∀ (r : R) (a : M), a ∈ S → r • a ∈ S := by
    rintro r _ ⟨u, rfl⟩
    exact ⟨r • u, by simp [map_smul, LinearMap.smul_apply]⟩

  have hS_lie : ∀ (x : 𝔤) (a : M), a ∈ S → ⁅x, a⁆ ∈ S :=
    fun x a ha => nminus_orbit_lie_stable hM x a ha

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
  obtain ⟨u, hu⟩ : m ∈ S := hm

  exact ⟨u, hu⟩

theorem pbw_verma_retraction_from_pbw
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt) :
    ∃ (ψ : M →ₗ[R] UniversalEnvelopingAlgebra R Δ.𝔫_neg),
      ∀ (u : UniversalEnvelopingAlgebra R Δ.𝔫_neg),
        ψ ((ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec) = u := by
  sorry

theorem pbw_verma_phi_injective_of_action
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt)
    (u : UniversalEnvelopingAlgebra R Δ.𝔫_neg)
    (hu : (ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec = 0) : u = 0 := by


  obtain ⟨ψ, hψ⟩ := pbw_verma_retraction_from_pbw hM


  have : u = ψ ((ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec) := (hψ u).symm
  rw [hu, map_zero] at this
  exact this

theorem pbw_verma_retraction_R
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt) :
    ∃ (ψ : M →ₗ[R] UniversalEnvelopingAlgebra R Δ.𝔫_neg),
      ∀ (u : UniversalEnvelopingAlgebra R Δ.𝔫_neg),
        ψ ((ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec) = u := by

  letI := instModuleUEASubalg Δ.𝔫_neg M
  let φ : UniversalEnvelopingAlgebra R Δ.𝔫_neg →ₗ[R] M :=
    (ueaSubalgAction Δ.𝔫_neg M).toLinearMap.flip hM.highestWeightVec

  have hφ_inj : Function.Injective φ := by
    intro u₁ u₂ h
    have hdiff : (ueaSubalgAction Δ.𝔫_neg M (u₁ - u₂)) hM.highestWeightVec = 0 := by
      have : φ u₁ = φ u₂ := h
      have : φ (u₁ - u₂) = 0 := by simp [map_sub, this]
      exact this
    have := pbw_verma_phi_injective_of_action hM (u₁ - u₂) hdiff
    exact sub_eq_zero.mp this

  have hφ_surj : Function.Surjective φ := by
    intro m
    obtain ⟨u, hu⟩ := pbw_verma_surjective hM m
    exact ⟨u, hu⟩

  let e : UniversalEnvelopingAlgebra R Δ.𝔫_neg ≃ₗ[R] M :=
    LinearEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩

  refine ⟨e.symm.toLinearMap, fun u => ?_⟩

  exact e.symm_apply_apply u

theorem pbw_verma_action_injective
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt)
    (u : UniversalEnvelopingAlgebra R Δ.𝔫_neg)
    (hu : (ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec = 0) : u = 0 := by
  obtain ⟨ψ, hψ⟩ := pbw_verma_retraction_R hM
  have key := hψ u
  rw [hu, map_zero] at key
  exact key.symm

theorem pbw_verma_left_inverse
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt) :
    letI := instModuleUEASubalg Δ.𝔫_neg M
    ∃ (ψ : M →ₗ[UniversalEnvelopingAlgebra R Δ.𝔫_neg] UniversalEnvelopingAlgebra R Δ.𝔫_neg),
      ψ.comp (LinearMap.toSpanSingleton (UniversalEnvelopingAlgebra R Δ.𝔫_neg) M
        hM.highestWeightVec) = LinearMap.id := by
  letI := instModuleUEASubalg Δ.𝔫_neg M
  let φ := LinearMap.toSpanSingleton (UniversalEnvelopingAlgebra R Δ.𝔫_neg) M
    hM.highestWeightVec


  have hφ_inj : Function.Injective φ := by
    intro u₁ u₂ h
    have : φ (u₁ - u₂) = 0 := by simp [map_sub, h]
    have h_eq : (ueaSubalgAction Δ.𝔫_neg M (u₁ - u₂)) hM.highestWeightVec = 0 := by
      change φ (u₁ - u₂) = 0 at this
      exact this
    have := pbw_verma_action_injective hM (u₁ - u₂) h_eq
    exact sub_eq_zero.mp this

  have hφ_surj : Function.Surjective φ := pbw_verma_surjective hM

  let e : UniversalEnvelopingAlgebra R Δ.𝔫_neg ≃ₗ[UniversalEnvelopingAlgebra R Δ.𝔫_neg] M :=
    LinearEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩

  refine ⟨e.symm, ?_⟩
  ext
  simp only [LinearMap.comp_apply, LinearMap.id_apply]
  exact e.symm_apply_apply _

theorem pbw_verma_phi_injective_helper
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt) :
    letI := instModuleUEASubalg Δ.𝔫_neg M
    Function.Injective
      (LinearMap.toSpanSingleton (UniversalEnvelopingAlgebra R Δ.𝔫_neg) M
        hM.highestWeightVec) := by
  letI := instModuleUEASubalg Δ.𝔫_neg M
  obtain ⟨ψ, hψ⟩ := pbw_verma_left_inverse hM
  exact Function.HasLeftInverse.injective ⟨ψ, fun u => by
    have := congr_fun (congr_arg DFunLike.coe hψ) u
    simpa using this⟩

theorem pbw_verma_retraction
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt) :
    letI := instModuleUEASubalg Δ.𝔫_neg M
    ∃ (ψ : M →ₗ[UniversalEnvelopingAlgebra R Δ.𝔫_neg] UniversalEnvelopingAlgebra R Δ.𝔫_neg),
      ψ hM.highestWeightVec = 1 := by
  letI := instModuleUEASubalg Δ.𝔫_neg M

  let φ := LinearMap.toSpanSingleton (UniversalEnvelopingAlgebra R Δ.𝔫_neg) M
    hM.highestWeightVec


  have hinj : Function.Injective φ := pbw_verma_phi_injective_helper hM
  have hsurj : Function.Surjective φ := pbw_verma_surjective hM

  let e : UniversalEnvelopingAlgebra R Δ.𝔫_neg ≃ₗ[UniversalEnvelopingAlgebra R Δ.𝔫_neg] M :=
    LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩

  refine ⟨e.symm, ?_⟩


  have h1 : e 1 = hM.highestWeightVec := by
    show φ 1 = hM.highestWeightVec
    simp [φ, LinearMap.toSpanSingleton_apply, one_smul]
  exact e.symm_apply_eq.mpr h1.symm

theorem pbw_ideal_factorization
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt) :
    letI := instModuleUEASubalg Δ.𝔫_neg M
    ∃ (ψ : M →ₗ[UniversalEnvelopingAlgebra R Δ.𝔫_neg] UniversalEnvelopingAlgebra R Δ.𝔫_neg),
      ψ.comp (LinearMap.toSpanSingleton (UniversalEnvelopingAlgebra R Δ.𝔫_neg) M
        hM.highestWeightVec) = LinearMap.id := by
  letI := instModuleUEASubalg Δ.𝔫_neg M

  obtain ⟨ψ, hψ⟩ := pbw_verma_retraction hM


  refine ⟨ψ, ?_⟩
  ext

  simp only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, LinearMap.id_apply]
  rw [map_smul, hψ, smul_eq_mul, mul_one]

theorem pbw_verma_injective
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt) :
    letI := instModuleUEASubalg Δ.𝔫_neg M
    Function.Injective
      (LinearMap.toSpanSingleton (UniversalEnvelopingAlgebra R Δ.𝔫_neg) M
        hM.highestWeightVec) := by
  letI := instModuleUEASubalg Δ.𝔫_neg M

  obtain ⟨ψ, hψ⟩ := pbw_ideal_factorization hM

  exact Function.HasLeftInverse.injective ⟨ψ, fun u => by
    have := congr_fun (congr_arg DFunLike.coe hψ) u
    simpa using this⟩

theorem pbw_verma_bijective
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt) :
    letI := instModuleUEASubalg Δ.𝔫_neg M
    Function.Bijective
      (LinearMap.toSpanSingleton (UniversalEnvelopingAlgebra R Δ.𝔫_neg) M
        hM.highestWeightVec) :=
  ⟨pbw_verma_injective hM, pbw_verma_surjective hM⟩

section VermaProperties

variable {Δ : TriangularDecomposition R 𝔤}
variable {M : Type u_mod} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
variable {wt : Δ.𝔥 →ₗ[R] R}

lemma IsVermaModule.toSpanSingleton_injective (hM : IsVermaModule Δ M wt) :
    letI := instModuleUEASubalg Δ.𝔫_neg M
    Function.Injective
      (LinearMap.toSpanSingleton (UniversalEnvelopingAlgebra R Δ.𝔫_neg) M
        hM.highestWeightVec) := by
  letI := instModuleUEASubalg Δ.𝔫_neg M

  exact (pbw_verma_bijective hM).1

lemma IsVermaModule.toSpanSingleton_surjective (hM : IsVermaModule Δ M wt) :
    letI := instModuleUEASubalg Δ.𝔫_neg M
    Function.Surjective
      (LinearMap.toSpanSingleton (UniversalEnvelopingAlgebra R Δ.𝔫_neg) M
        hM.highestWeightVec) := by
  letI := instModuleUEASubalg Δ.𝔫_neg M

  exact (pbw_verma_bijective hM).2

theorem IsVermaModule.free_over_nminus (hM : IsVermaModule Δ M wt) :
    letI := instModuleUEASubalg Δ.𝔫_neg M
    ∃ (φ : UniversalEnvelopingAlgebra R Δ.𝔫_neg ≃ₗ[UniversalEnvelopingAlgebra R Δ.𝔫_neg] M),
      φ 1 = hM.highestWeightVec := by
  letI := instModuleUEASubalg Δ.𝔫_neg M
  let φ := LinearMap.toSpanSingleton (UniversalEnvelopingAlgebra R Δ.𝔫_neg) M hM.highestWeightVec
  exact ⟨LinearEquiv.ofBijective φ
    ⟨hM.toSpanSingleton_injective, hM.toSpanSingleton_surjective⟩,
    by simp [φ, LinearMap.toSpanSingleton]⟩

lemma IsVermaModule.hwv_not_mem_proper (hM : IsVermaModule Δ M wt)
    (N : LieSubmodule R 𝔤 M) (hN : N ≠ ⊤) :
    hM.highestWeightVec ∉ N := by
  intro hmem
  apply hN
  rw [eq_top_iff]
  calc ⊤ = LieSubmodule.lieSpan R 𝔤 {hM.highestWeightVec} := hM.generates.symm
    _ ≤ N := LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr hmem)

def augmentationUEA (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L] :
    UniversalEnvelopingAlgebra R L →ₐ[R] R :=
  UniversalEnvelopingAlgebra.lift R (0 : L →ₗ⁅R⁆ R)

theorem pbw_separation_functional
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt) :
    ∃ (f : M →ₗ[R] R),
      f hM.highestWeightVec = 1 ∧
      (∀ u : UniversalEnvelopingAlgebra R Δ.𝔫_neg,
        f ((ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec) =
          augmentationUEA R Δ.𝔫_neg u) ∧
      (∀ (N : LieSubmodule R 𝔤 M), N ≠ ⊤ → ∀ m ∈ N, f m = 0) := by sorry

theorem pbw_augmentation_hwv_component_zero
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt)
    (u : UniversalEnvelopingAlgebra R Δ.𝔫_neg)
    (N : LieSubmodule R 𝔤 M) (hN : N ≠ ⊤)
    (hu : (ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec ∈ N) :
    (augmentationUEA R Δ.𝔫_neg u) • hM.highestWeightVec = 0 := by
  obtain ⟨f, _, hfu, hfN⟩ := pbw_separation_functional hM
  have : augmentationUEA R Δ.𝔫_neg u = 0 := by rw [← hfu u]; exact hfN N hN _ hu
  rw [this, zero_smul]


theorem pbw_augmentation_vanish_proper
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt)
    (u : UniversalEnvelopingAlgebra R Δ.𝔫_neg)
    (N : LieSubmodule R 𝔤 M) (hN : N ≠ ⊤)
    (hu : (ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec ∈ N) :
    augmentationUEA R Δ.𝔫_neg u = 0 := by

  have h1 : (augmentationUEA R Δ.𝔫_neg u) • hM.highestWeightVec = 0 :=
    pbw_augmentation_hwv_component_zero hM u N hN hu

  letI := instModuleUEASubalg Δ.𝔫_neg M
  obtain ⟨φ, hφ⟩ := hM.free_over_nminus

  set c := augmentationUEA R Δ.𝔫_neg u with hc_def


  have hφ_alg : φ (algebraMap R (UniversalEnvelopingAlgebra R Δ.𝔫_neg) c) =
      c • hM.highestWeightVec := by

    have hmul : algebraMap R (UniversalEnvelopingAlgebra R Δ.𝔫_neg) c =
        (algebraMap R _ c) * (1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) := (mul_one _).symm
    conv_lhs => rw [hmul]

    rw [show (algebraMap R (UniversalEnvelopingAlgebra R Δ.𝔫_neg) c) *
      (1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) =
      (algebraMap R (UniversalEnvelopingAlgebra R Δ.𝔫_neg) c) • (1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg)
      from (smul_eq_mul _ _).symm]
    rw [φ.map_smul, hφ]


    show (ueaSubalgAction Δ.𝔫_neg M (algebraMap R _ c)) hM.highestWeightVec = c • hM.highestWeightVec
    rw [AlgHom.commutes]
    exact Module.algebraMap_end_apply R R M c hM.highestWeightVec

  rw [h1] at hφ_alg

  have h3 : algebraMap R (UniversalEnvelopingAlgebra R Δ.𝔫_neg) c = 0 :=
    φ.injective (by rw [hφ_alg, map_zero])

  have h4 : c = (augmentationUEA R Δ.𝔫_neg) (algebraMap R _ c) :=
    ((augmentationUEA R Δ.𝔫_neg).commutes c).symm
  rw [h4, h3, map_zero]

theorem augmentation_retraction_vanish_on_proper (hM : IsVermaModule Δ M wt) :
    letI := instModuleUEASubalg Δ.𝔫_neg M
    ∀ (ψ : M →ₗ[UniversalEnvelopingAlgebra R Δ.𝔫_neg] UniversalEnvelopingAlgebra R Δ.𝔫_neg),
      ψ hM.highestWeightVec = 1 →
        ∀ (N : LieSubmodule R 𝔤 M), N ≠ ⊤ → ∀ m ∈ N,
          augmentationUEA R Δ.𝔫_neg (ψ m) = 0 := by
  letI := instModuleUEASubalg Δ.𝔫_neg M
  intro ψ hψ N hN m hm

  obtain ⟨φ, hφ⟩ := hM.free_over_nminus


  have hψ_eq : ∀ x : M, ψ x = φ.symm x := by
    intro x

    have hx : x = φ (φ.symm x) := (φ.apply_symm_apply x).symm
    conv_lhs => rw [hx]


    set u := φ.symm x

    have hφu_smul : φ u = u • φ 1 := by
      have : u = u * (1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) := (mul_one u).symm
      conv_lhs => rw [this]
      exact φ.map_smul u 1
    rw [hφu_smul, ψ.map_smul, hφ, hψ, smul_eq_mul, mul_one]

  rw [hψ_eq]
  set u := φ.symm m


  have hm_eq : (ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec = m := by
    have key : φ u = u • φ (1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) := by
      have : u = u * (1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) := (mul_one u).symm
      conv_lhs => rw [this]
      exact φ.map_smul u 1
    have : φ u = m := φ.apply_symm_apply m
    rw [← this, key, hφ]
    rfl
  rw [← hm_eq] at hm
  exact pbw_augmentation_vanish_proper hM u N hN hm

theorem pbw_hwv_separation (hM : IsVermaModule Δ M wt) :
    ∃ (f : M →ₗ[R] R), f hM.highestWeightVec = 1 ∧
      ∀ (N : LieSubmodule R 𝔤 M), N ≠ ⊤ → ∀ m ∈ N, f m = 0 := by

  letI := instModuleUEASubalg Δ.𝔫_neg M
  obtain ⟨ψ, hψ⟩ := pbw_verma_retraction hM

  let ε := augmentationUEA R Δ.𝔫_neg

  let f : M →ₗ[R] R :=
    { toFun := fun m => ε (ψ m)
      map_add' := fun x y => by simp [map_add]
      map_smul' := fun r x => by
        simp only [RingHom.id_apply]


        have : ψ (r • x) = algebraMap R (UniversalEnvelopingAlgebra R Δ.𝔫_neg) r • ψ x := by
          have hsmul : r • x = (algebraMap R (UniversalEnvelopingAlgebra R Δ.𝔫_neg) r) • x := by
            change r • x = ueaSubalgAction Δ.𝔫_neg M (algebraMap R _ r) x
            rw [ueaSubalg_algebraMap_apply]
          rw [hsmul, map_smul]
        rw [this]
        simp [Algebra.algebraMap_eq_smul_one, smul_eq_mul] }
  refine ⟨f, ?_, ?_⟩
  ·
    show ε (ψ hM.highestWeightVec) = 1
    rw [hψ]
    exact map_one ε
  ·
    intro N hN m hm
    show ε (ψ m) = 0
    exact augmentation_retraction_vanish_on_proper hM ψ hψ N hN m hm

theorem IsVermaModule.proper_sSup (hM : IsVermaModule Δ M wt) :
    sSup {N : LieSubmodule R 𝔤 M | N ≠ ⊤} ≠ ⊤ := by

  obtain ⟨f, hf_v, hf_proper⟩ := pbw_hwv_separation hM

  haveI hR_nontrivial : Nontrivial R := by
    rw [nontrivial_iff]; use 1, 0; intro h
    apply hM.hwv_ne_zero
    have hsub : Subsingleton R := ⟨fun a b => by
      rw [← one_mul a, ← one_mul b, h, zero_mul, zero_mul]⟩
    calc hM.highestWeightVec = (1 : R) • hM.highestWeightVec := (one_smul R _).symm
      _ = (0 : R) • hM.highestWeightVec := by rw [Subsingleton.elim (1 : R) 0]
      _ = 0 := zero_smul R _

  intro h_eq

  have hv_mem : hM.highestWeightVec ∈
      (sSup {N : LieSubmodule R 𝔤 M | N ≠ ⊤} : LieSubmodule R 𝔤 M).toSubmodule := by
    rw [h_eq]; trivial

  rw [LieSubmodule.sSup_toSubmodule] at hv_mem

  rw [Submodule.mem_sSup] at hv_mem

  have hv_in_ker : hM.highestWeightVec ∈ f.ker := hv_mem f.ker (by
    intro p hp
    obtain ⟨N, hN, hNp⟩ := hp
    rw [← hNp]
    intro m hm
    exact LinearMap.mem_ker.mpr (hf_proper N hN m hm))

  rw [LinearMap.mem_ker] at hv_in_ker
  exact one_ne_zero (hf_v ▸ hv_in_ker)

theorem IsVermaModule.exists_unique_maximal_submodule (hM : IsVermaModule Δ M wt) :
    ∃ (J : LieSubmodule R 𝔤 M), J ≠ ⊤ ∧
      (∀ (N : LieSubmodule R 𝔤 M), N ≠ ⊤ → N ≤ J) := by
  refine ⟨sSup {N : LieSubmodule R 𝔤 M | N ≠ ⊤}, hM.proper_sSup, ?_⟩
  intro N hN
  exact le_sSup hN

theorem IsVermaModule.quotient_by_maximal_irreducible (_hM : IsVermaModule Δ M wt)
    (J : LieSubmodule R 𝔤 M) (hJ_ne_top : J ≠ ⊤)
    (hJ_max : ∀ (N : LieSubmodule R 𝔤 M), N ≠ ⊤ → N ≤ J) :
    LieModule.IsIrreducible R 𝔤 (M ⧸ J) := by

  show IsSimpleOrder (LieSubmodule R 𝔤 (M ⧸ J))

  have : Nontrivial (LieSubmodule R 𝔤 (M ⧸ J)) := by
    refine ⟨⟨⊥, ⊤, ?_⟩⟩
    intro h
    apply hJ_ne_top
    rw [eq_top_iff]
    intro m _
    have hmem : (LieSubmodule.Quotient.mk' J) m ∈ (⊤ : LieSubmodule R 𝔤 (M ⧸ J)) := trivial
    rw [← h] at hmem
    rw [LieSubmodule.mem_bot] at hmem
    rwa [LieSubmodule.Quotient.mk_eq_zero] at hmem

  exact {
    eq_bot_or_eq_top := by
      intro N'

      set N := N'.comap (LieSubmodule.Quotient.mk' J) with hN_def

      have hJN : J ≤ N := by
        intro m hm
        show m ∈ N'.comap (LieSubmodule.Quotient.mk' J)
        rw [LieSubmodule.mem_comap]
        rw [(LieSubmodule.Quotient.mk_eq_zero J).mpr hm]
        exact N'.zero_mem

      by_cases hN : N = ⊤
      ·
        right; rw [eq_top_iff]; intro x _
        obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' J x
        exact (hN ▸ trivial : m ∈ N)
      ·
        left
        have hNJ : N ≤ J := hJ_max N hN
        rw [eq_bot_iff]; intro x hx
        obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' J x
        rw [LieSubmodule.mem_bot]
        exact (LieSubmodule.Quotient.mk_eq_zero J).mpr (hNJ hx) }

theorem pbw_augmentation_ideal_weight_zero
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt)
    (w : UniversalEnvelopingAlgebra R Δ.𝔫_neg)
    (hw_ker : augmentationUEA R Δ.𝔫_neg w = 0)
    (hw_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤),
      (ueaSubalgAction Δ.𝔫_neg M w) hM.highestWeightVec⁆ =
      wt h • (ueaSubalgAction Δ.𝔫_neg M w) hM.highestWeightVec) :
    (ueaSubalgAction Δ.𝔫_neg M w) hM.highestWeightVec = 0 := by sorry

theorem pbw_nminus_weight_zero_scalar
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt)
    (u : UniversalEnvelopingAlgebra R Δ.𝔫_neg)
    (hu : ∀ (h : Δ.𝔥), ⁅(h : 𝔤),
      (ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec⁆ =
      wt h • (ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec) :
    ∃ (c : R), u = algebraMap R _ c := by

  set c := augmentationUEA R Δ.𝔫_neg u

  set w := u - algebraMap R _ c with hw_def

  have hw_ker : augmentationUEA R Δ.𝔫_neg w = 0 := by
    simp only [hw_def, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply]
    exact sub_self _


  have hw_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤),
      (ueaSubalgAction Δ.𝔫_neg M w) hM.highestWeightVec⁆ =
      wt h • (ueaSubalgAction Δ.𝔫_neg M w) hM.highestWeightVec := by
    intro h

    have hact_w : (ueaSubalgAction Δ.𝔫_neg M w) hM.highestWeightVec =
        (ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec -
        c • hM.highestWeightVec := by
      simp only [hw_def, map_sub, LinearMap.sub_apply, ueaSubalg_algebraMap_apply]
    rw [hact_w, lie_sub, hu h, LieModule.lie_smul,
        hM.toIsHighestWeightModule.cartan_action h, smul_comm, smul_sub]

  have hw_zero : (ueaSubalgAction Δ.𝔫_neg M w) hM.highestWeightVec = 0 :=
    pbw_augmentation_ideal_weight_zero hM w hw_ker hw_wt

  have hw_eq_zero : w = 0 := pbw_verma_phi_injective_of_action hM w hw_zero

  exact ⟨c, by rw [← sub_eq_zero]; exact hw_eq_zero⟩
theorem pbw_nminus_singular_proportional
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt)
    (μ : Δ.𝔥 →ₗ[R] R)
    (u₁ u₂ : UniversalEnvelopingAlgebra R Δ.𝔫_neg)
    (hu₁_ne : (ueaSubalgAction Δ.𝔫_neg M u₁) hM.highestWeightVec ≠ 0)
    (hu₁_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤),
      (ueaSubalgAction Δ.𝔫_neg M u₁) hM.highestWeightVec⁆ =
      μ h • (ueaSubalgAction Δ.𝔫_neg M u₁) hM.highestWeightVec)
    (hu₁_npos : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤),
      (ueaSubalgAction Δ.𝔫_neg M u₁) hM.highestWeightVec⁆ = 0)
    (hu₂_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤),
      (ueaSubalgAction Δ.𝔫_neg M u₂) hM.highestWeightVec⁆ =
      μ h • (ueaSubalgAction Δ.𝔫_neg M u₂) hM.highestWeightVec)
    (hu₂_npos : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤),
      (ueaSubalgAction Δ.𝔫_neg M u₂) hM.highestWeightVec⁆ = 0) :
    ∃ (c : R), (ueaSubalgAction Δ.𝔫_neg M u₂) hM.highestWeightVec =
      c • (ueaSubalgAction Δ.𝔫_neg M u₁) hM.highestWeightVec := by sorry

theorem IsVermaModule.highestWeightSpace_one_dim (hM : IsVermaModule Δ M wt)
    (v : M) (hv : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = wt h • v) :
    ∃ (c : R), v = c • hM.highestWeightVec := by

  letI : Module (UniversalEnvelopingAlgebra R Δ.𝔫_neg) M := instModuleUEASubalg Δ.𝔫_neg M
  obtain ⟨φ, hφ⟩ := hM.free_over_nminus

  set u := φ.symm v with hu_def
  have hv_eq : φ u = v := LinearEquiv.apply_symm_apply φ v


  have hφu : φ u = (ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec := by
    have key : φ u = u • φ (1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) := by
      have : u = u * (1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) := (mul_one u).symm
      conv_lhs => rw [this]
      exact φ.map_smul u 1
    rw [key, hφ]

    rfl

  have hu_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤),
      (ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec⁆ =
      wt h • (ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec := by
    intro h
    rw [← hφu, hv_eq]
    exact hv h
  obtain ⟨c, hc⟩ := pbw_nminus_weight_zero_scalar hM u hu_wt

  refine ⟨c, ?_⟩
  rw [← hv_eq, hφu, hc]


  show (ueaSubalgAction Δ.𝔫_neg M (algebraMap R _ c)) hM.highestWeightVec =
    c • hM.highestWeightVec
  have : ueaSubalgAction Δ.𝔫_neg M (algebraMap R _ c) =
      algebraMap R _ c := (ueaSubalgAction Δ.𝔫_neg M).commutes c
  rw [this]
  simp [Algebra.algebraMap_eq_smul_one]

def WeightSpace (Δ : TriangularDecomposition R 𝔤)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (μ : Δ.𝔥 →ₗ[R] R) : Submodule R M where
  carrier := { m : M | ∀ (h : Δ.𝔥), ⁅(h : 𝔤), m⁆ = μ h • m }
  add_mem' := fun {a b} ha hb h => by rw [lie_add, ha h, hb h, smul_add]
  zero_mem' := fun h => by rw [lie_zero, smul_zero]
  smul_mem' := fun r {m} hm h => by rw [lie_smul, hm h, smul_comm]

theorem weightSpace_eq_mathlib_weightSpace {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (μ : Δ.𝔥 →ₗ[R] R) :
    WeightSpace Δ M μ =
    (LieModule.weightSpace (R := R) (L := Δ.𝔥) M (μ ·)).toSubmodule := by
  ext m
  constructor
  · intro hm
    rw [LieSubmodule.mem_toSubmodule, LieModule.mem_weightSpace]
    intro x; exact hm x
  · intro hm
    rw [LieSubmodule.mem_toSubmodule, LieModule.mem_weightSpace] at hm
    intro h; exact hm h

theorem weightSpace_eq_weightSubspace {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (μ : Δ.𝔥 →ₗ[R] R) :
    WeightSpace Δ M μ = Δ.weightSubspace M μ := by
  ext m; exact Iff.rfl

def weights (Δ : TriangularDecomposition R 𝔤)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] : Set (Δ.𝔥 →ₗ[R] R) :=
  { μ | WeightSpace Δ M μ ≠ ⊥ }

structure PositiveRootData (Δ : TriangularDecomposition R 𝔤) where
  posRoots : Finset (Δ.𝔥 →ₗ[R] R)
  posRoots_ne_zero : ∀ α ∈ posRoots, α ≠ 0
  posRoots_pointed_cone : ∀ (α : Δ.𝔥 →ₗ[R] R), α ∈ posRoots →
    ∀ (n : ℤ), n < 0 →
    ¬ ∃ (c : (Δ.𝔥 →ₗ[R] R) → ℕ), n • α = ∑ β ∈ posRoots, (c β) • β
  corootPairing : (Δ.𝔥 →ₗ[R] R) → (Δ.𝔥 →ₗ[R] R) → R
  corootPairing_add_left : ∀ (μ ν α : Δ.𝔥 →ₗ[R] R),
    corootPairing (μ + ν) α = corootPairing μ α + corootPairing ν α
  corootPairing_nsmul_left : ∀ (n : ℕ) (μ α : Δ.𝔥 →ₗ[R] R),
    corootPairing (n • μ) α = n • corootPairing μ α
  corootPairing_self : ∀ α ∈ posRoots, corootPairing α α = 2
  negRootVec : ∀ α ∈ posRoots, ↥(Δ.𝔫_neg)
  negRootVec_weight : ∀ (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ posRoots) (h : Δ.𝔥),
    ⁅(↑h : 𝔤), (↑(negRootVec α hα) : 𝔤)⁆ = -(α h) • (↑(negRootVec α hα) : 𝔤)
  ι_negRootVec_ne_zero : ∀ (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ posRoots),
    UniversalEnvelopingAlgebra.ι R (negRootVec α hα) ≠ 0
  uea_nminus_noZeroDivisors : NoZeroDivisors (UniversalEnvelopingAlgebra R ↥(Δ.𝔫_neg))
  uea_nminus_nontrivial : Nontrivial (UniversalEnvelopingAlgebra R ↥(Δ.𝔫_neg))
  posRootVec : ∀ α ∈ posRoots, ↥(Δ.𝔫_pos)
  posRootVec_weight : ∀ (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ posRoots) (h : Δ.𝔥),
    ⁅(↑h : 𝔤), (↑(posRootVec α hα) : 𝔤)⁆ = (α h) • (↑(posRootVec α hα) : 𝔤)
  npos_span : ∀ (e : Δ.𝔫_pos), ∃ (c : ∀ α ∈ posRoots, R),
    (e : 𝔤) = ∑ x ∈ posRoots.attach, c x.1 x.2 • (↑(posRootVec x.1 x.2) : 𝔤)

theorem PositiveRootData.posRoots_coeff_bound
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (a b : Δ.𝔥 →ₗ[R] R) :
    ∃ (N : ℕ), ∀ (c₁ c₂ : (Δ.𝔥 →ₗ[R] R) → ℕ),
      (b - a + ∑ α ∈ rd.posRoots, (c₁ α) • α = ∑ α ∈ rd.posRoots, (c₂ α) • α) →
      ∀ α ∈ rd.posRoots, c₁ α ≤ N := by sorry

theorem PositiveRootData.cone_inter_finite
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (a b : Δ.𝔥 →ₗ[R] R) :
    ∃ (T : Finset (Δ.𝔥 →ₗ[R] R)),
      ∀ γ, (∃ (c : (Δ.𝔥 →ₗ[R] R) → ℕ), a - γ = ∑ α ∈ rd.posRoots, (c α) • α) →
           (∃ (c : (Δ.𝔥 →ₗ[R] R) → ℕ), b - γ = ∑ α ∈ rd.posRoots, (c α) • α) →
           γ ∈ T := by
  classical

  obtain ⟨N, hN⟩ := rd.posRoots_coeff_bound a b


  refine ⟨(Finset.univ : Finset ({ x // x ∈ rd.posRoots } → Fin (N + 1))).image
    (fun f => a - ∑ x ∈ rd.posRoots.attach, ((f x : ℕ) • x.1)), fun γ h₁ h₂ => ?_⟩

  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂


  have hγ : γ = a - ∑ α ∈ rd.posRoots, (c₁ α) • α := by
    rw [← hc₁, sub_sub_cancel]

  have hconstraint : b - a + ∑ α ∈ rd.posRoots, (c₁ α) • α =
      ∑ α ∈ rd.posRoots, (c₂ α) • α := by
    rw [hγ] at hc₂

    rw [← hc₂]
    abel

  have hbound : ∀ α ∈ rd.posRoots, c₁ α ≤ N := hN c₁ c₂ hconstraint

  rw [Finset.mem_image]
  refine ⟨fun x => ⟨c₁ x.1, Nat.lt_succ_of_le (hbound x.1 x.2)⟩, Finset.mem_univ _, ?_⟩
  rw [hγ]
  congr 1
  exact Finset.sum_attach rd.posRoots (fun α => (c₁ α) • α)

def PositiveRootData.IsInQPlus {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (μ : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∃ (c : (Δ.𝔥 →ₗ[R] R) → ℕ), μ = ∑ α ∈ rd.posRoots, (c α) • α

theorem nminus_UEA_weight_in_QPlus
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (rd : PositiveRootData Δ)
    (v : M) (hv : v ∈ WeightSpace Δ M wt)
    (u : UniversalEnvelopingAlgebra R Δ.𝔫_neg)
    (μ : Δ.𝔥 →ₗ[R] R)
    (hu : (ueaSubalgAction Δ.𝔫_neg M u) v ∈ WeightSpace Δ M μ)
    (hne : (ueaSubalgAction Δ.𝔫_neg M u) v ≠ 0) :
    rd.IsInQPlus (wt - μ) := by sorry

theorem pbw_weight_subset_QPlus (hM : IsVermaModule Δ M wt)
    (rd : PositiveRootData Δ) (μ : Δ.𝔥 →ₗ[R] R)
    (hμ : WeightSpace Δ M μ ≠ ⊥) :
    rd.IsInQPlus (wt - μ) := by

  rw [ne_eq, Submodule.eq_bot_iff] at hμ
  push Not at hμ
  obtain ⟨m, hm_mem, hm_ne⟩ := hμ

  letI : Module (UniversalEnvelopingAlgebra R Δ.𝔫_neg) M := instModuleUEASubalg Δ.𝔫_neg M
  obtain ⟨φ, hφ⟩ := hM.free_over_nminus

  set u := φ.symm m
  have hm_eq_phi : φ u = m := LinearEquiv.apply_symm_apply φ m

  have hm_eq : m = (ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec := by
    rw [← hm_eq_phi]

    have : φ u = u • φ 1 := by
      conv_lhs => rw [show u = u • (1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) from (mul_one u).symm]
      exact φ.map_smul u 1
    rw [this, hφ]

    rfl

  have hv_wt : hM.highestWeightVec ∈ WeightSpace Δ M wt := by
    intro h
    exact hM.cartan_action h

  rw [hm_eq] at hm_mem hm_ne
  exact nminus_UEA_weight_in_QPlus rd hM.highestWeightVec hv_wt u μ hm_mem hm_ne

theorem nminus_QPlus_weight_vector
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (rd : PositiveRootData Δ)
    (v : M) (hv : v ∈ WeightSpace Δ M wt)
    (β : Δ.𝔥 →ₗ[R] R) (hβ : rd.IsInQPlus β) :
    ∃ (u : UniversalEnvelopingAlgebra R Δ.𝔫_neg),
      u ≠ 0 ∧
      (ueaSubalgAction Δ.𝔫_neg M u) v ∈ WeightSpace Δ M (wt - β) := by

  obtain ⟨c, hc⟩ := hβ


  have single_shift : ∀ (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ rd.posRoots)
      (μ : Δ.𝔥 →ₗ[R] R) (m : M) (_ : m ∈ WeightSpace Δ M μ),
      ⁅(↑(rd.negRootVec α hα) : 𝔤), m⁆ ∈ WeightSpace Δ M (μ - α) := by
    intro α hα μ m hm h

    rw [leibniz_lie, rd.negRootVec_weight α hα h, hm h]
    rw [neg_smul, neg_lie, lie_smul]
    simp [LinearMap.sub_apply, sub_smul]
    abel

  have ι_act : ∀ (x : ↥(Δ.𝔫_neg)) (m : M),
      (ueaSubalgAction Δ.𝔫_neg M (UniversalEnvelopingAlgebra.ι R x)) m = ⁅(x : 𝔤), m⁆ := by
    intro x m
    simp [ueaSubalgAction]

  have mul_act : ∀ (a b : UniversalEnvelopingAlgebra R ↥(Δ.𝔫_neg)) (m : M),
      (ueaSubalgAction Δ.𝔫_neg M (a * b)) m =
      (ueaSubalgAction Δ.𝔫_neg M a) ((ueaSubalgAction Δ.𝔫_neg M b) m) := by
    intro a b m
    show (ueaSubalgAction Δ.𝔫_neg M (a * b)) m = _
    rw [map_mul]
    rfl

  have one_act : ∀ (m : M), (ueaSubalgAction Δ.𝔫_neg M 1) m = m := by
    intro m; show (ueaSubalgAction Δ.𝔫_neg M 1) m = m; rw [map_one]; rfl

  have pow_shift : ∀ (α : Δ.𝔥 →ₗ[R] R) (hα : α ∈ rd.posRoots) (n : ℕ)
      (μ : Δ.𝔥 →ₗ[R] R) (m : M) (_ : m ∈ WeightSpace Δ M μ),
      (ueaSubalgAction Δ.𝔫_neg M
        ((UniversalEnvelopingAlgebra.ι R (rd.negRootVec α hα)) ^ n)) m ∈
        WeightSpace Δ M (μ - n • α) := by
    intro α hα n
    induction n with
    | zero => intro μ m hm; simp; simpa using hm
    | succ n ih =>
      intro μ m hm
      rw [pow_succ', mul_act]
      have hrw : μ - (n + 1) • α = (μ - n • α) - α := by
        simp [add_smul, sub_sub]
      rw [hrw]
      have hmid := ih μ m hm
      have : (ueaSubalgAction Δ.𝔫_neg M
          (UniversalEnvelopingAlgebra.ι R (rd.negRootVec α hα)))
          ((ueaSubalgAction Δ.𝔫_neg M
            ((UniversalEnvelopingAlgebra.ι R (rd.negRootVec α hα)) ^ n)) m) =
        ⁅(↑(rd.negRootVec α hα) : 𝔤),
          (ueaSubalgAction Δ.𝔫_neg M
            ((UniversalEnvelopingAlgebra.ι R (rd.negRootVec α hα)) ^ n)) m⁆ := ι_act _ _
      rw [this]
      exact single_shift α hα (μ - n • α) _ hmid


  haveI := rd.uea_nminus_noZeroDivisors
  haveI := rd.uea_nminus_nontrivial
  suffices key : ∀ (S : Finset (Δ.𝔥 →ₗ[R] R)), S ⊆ rd.posRoots →
      ∃ (u : UniversalEnvelopingAlgebra R ↥(Δ.𝔫_neg)),
        u ≠ 0 ∧
        (ueaSubalgAction Δ.𝔫_neg M u) v ∈
          WeightSpace Δ M (wt - ∑ α ∈ S, (c α) • α) by
    rw [hc]
    exact key rd.posRoots (Finset.Subset.refl _)
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨1, one_ne_zero, by rw [one_act]; simpa using hv⟩
  | @insert α₀ S₀ hα₀_notin ih =>
    intro hS
    have hS₀ : S₀ ⊆ rd.posRoots :=
      (Finset.subset_insert α₀ S₀).trans hS
    obtain ⟨u₀, hu₀_ne, hu₀_wt⟩ := ih hS₀


    have hα₀_mem : α₀ ∈ rd.posRoots := hS (Finset.mem_insert_self α₀ S₀)
    set u₁ := (UniversalEnvelopingAlgebra.ι R (rd.negRootVec α₀ hα₀_mem)) ^ (c α₀) * u₀
    refine ⟨u₁, ?_, ?_⟩
    ·
      exact mul_ne_zero (pow_ne_zero _ (rd.ι_negRootVec_ne_zero α₀ hα₀_mem)) hu₀_ne
    ·
      rw [Finset.sum_insert hα₀_notin]
      show (ueaSubalgAction Δ.𝔫_neg M u₁) v ∈ _
      change (ueaSubalgAction Δ.𝔫_neg M
        ((UniversalEnvelopingAlgebra.ι R (rd.negRootVec α₀ hα₀_mem)) ^ (c α₀) * u₀)) v ∈ _
      rw [mul_act]


      have hrw : wt - (c α₀ • α₀ + ∑ α ∈ S₀, c α • α) =
          (wt - ∑ α ∈ S₀, c α • α) - c α₀ • α₀ := by
        simp [sub_sub, add_comm]
      rw [hrw]
      exact pow_shift α₀ hα₀_mem (c α₀) _ _ hu₀_wt

theorem pbw_QPlus_subset_weights (hM : IsVermaModule Δ M wt)
    (rd : PositiveRootData Δ) (μ : Δ.𝔥 →ₗ[R] R)
    (hμ : rd.IsInQPlus (wt - μ)) :
    WeightSpace Δ M μ ≠ ⊥ := by

  have hv_wt : hM.highestWeightVec ∈ WeightSpace Δ M wt := by
    intro h
    exact hM.cartan_action h


  obtain ⟨u, hu_ne, hu_wt⟩ := nminus_QPlus_weight_vector rd hM.highestWeightVec hv_wt
    (wt - μ) hμ

  have hμ_eq : wt - (wt - μ) = μ := by
    ext h
    simp only [sub_sub_cancel]
  rw [hμ_eq] at hu_wt

  have hne : (ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec ≠ 0 := by


    letI : Module (UniversalEnvelopingAlgebra R Δ.𝔫_neg) M := instModuleUEASubalg Δ.𝔫_neg M
    obtain ⟨φ, hφ⟩ := hM.free_over_nminus
    intro heq
    apply hu_ne

    have hφu : φ u = (ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec := by
      have : φ u = u • φ 1 := by
        conv_lhs =>
          rw [show u = u • (1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) from (mul_one u).symm]
        exact φ.map_smul u 1
      rw [this, hφ]
      rfl

    have : φ u = 0 := by rw [hφu]; exact heq
    have : u = 0 := φ.injective (by rw [this, map_zero])
    exact this

  rw [Submodule.ne_bot_iff]
  exact ⟨(ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec, hu_wt, hne⟩

theorem pbw_verma_weight_iff (hM : IsVermaModule Δ M wt)
    (rd : PositiveRootData Δ) (μ : Δ.𝔥 →ₗ[R] R) :
    WeightSpace Δ M μ ≠ ⊥ ↔ rd.IsInQPlus (wt - μ) :=
  ⟨pbw_weight_subset_QPlus hM rd μ, pbw_QPlus_subset_weights hM rd μ⟩

theorem IsVermaModule.weight_subset_QPlus (hM : IsVermaModule Δ M wt)
    (rd : PositiveRootData Δ) (μ : Δ.𝔥 →ₗ[R] R)
    (hμ : WeightSpace Δ M μ ≠ ⊥) :
    rd.IsInQPlus (wt - μ) :=
  (pbw_verma_weight_iff hM rd μ).mp hμ

theorem IsVermaModule.QPlus_subset_weights (hM : IsVermaModule Δ M wt)
    (rd : PositiveRootData Δ) (μ : Δ.𝔥 →ₗ[R] R)
    (hμ : rd.IsInQPlus (wt - μ)) :
    WeightSpace Δ M μ ≠ ⊥ :=
  (pbw_verma_weight_iff hM rd μ).mpr hμ

theorem IsVermaModule.weight_set_eq (hM : IsVermaModule Δ M wt)
    (rd : PositiveRootData Δ) :
    weights Δ M = { μ | rd.IsInQPlus (wt - μ) } := by
  ext μ
  simp only [weights, Set.mem_setOf_eq]
  exact ⟨hM.weight_subset_QPlus rd μ, hM.QPlus_subset_weights rd μ⟩

theorem IsVermaModule.highest_weight_module_is_quotient (hM : IsVermaModule Δ M wt)
    (V : Type u_mod) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (hV : IsHighestWeightModule Δ V wt) :
    ∃ (η : M →ₗ⁅R, 𝔤⁆ V), Function.Surjective η := by

  obtain ⟨η, hη⟩ := hM.universal_map V hV.highestWeightVec hV.cartan_action hV.npos_action
  refine ⟨η, ?_⟩

  rw [← LieModuleHom.range_eq_top]

  have hv_in_range : hV.highestWeightVec ∈ η.range := ⟨hM.highestWeightVec, hη⟩

  have hsub : LieSubmodule.lieSpan R 𝔤 {hV.highestWeightVec} ≤ η.range :=
    LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr hv_in_range)
  rw [hV.generates] at hsub
  exact top_le_iff.mp hsub

theorem IsVermaModule.simpleQuotient_of_hwm (hM : IsVermaModule Δ M wt)
    (J : LieSubmodule R 𝔤 M) (_hJ_ne_top : J ≠ ⊤)
    (hJ_max : ∀ (N : LieSubmodule R 𝔤 M), N ≠ ⊤ → N ≤ J)
    (V : Type u_mod) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (hV : IsHighestWeightModule Δ V wt) :
    ∃ (π : V →ₗ⁅R, 𝔤⁆ (M ⧸ J)), Function.Surjective π := by

  obtain ⟨η, hη_surj⟩ := hM.highest_weight_module_is_quotient V hV

  have hker_ne_top : η.ker ≠ ⊤ := by
    intro h
    have hzero : ∀ m, η m = 0 := fun m => (h ▸ trivial : m ∈ η.ker)
    have hV_zero : ∀ v : V, v = 0 := fun v => by
      obtain ⟨m, rfl⟩ := hη_surj v; exact hzero m
    exact hV.hwv_ne_zero (hV_zero hV.highestWeightVec)

  have hker_le_J : η.ker ≤ J := hJ_max η.ker hker_ne_top


  have hker_sub : η.toLinearMap.ker ≤ (LieSubmodule.Quotient.mk' J).toLinearMap.ker := by
    intro m hm
    rw [LinearMap.mem_ker, LieModuleHom.coe_toLinearMap]
    exact (LieSubmodule.Quotient.mk_eq_zero J).mpr (hker_le_J hm)
  let f_lin : V →ₗ[R] (M ⧸ J) :=
    (η.toLinearMap.ker.liftQ (LieSubmodule.Quotient.mk' J).toLinearMap hker_sub).comp
      (η.toLinearMap.quotKerEquivOfSurjective hη_surj).symm.toLinearMap
  have hf : ∀ m : M, f_lin (η m) = LieSubmodule.Quotient.mk' J m := fun m => by
    show (η.toLinearMap.ker.liftQ (LieSubmodule.Quotient.mk' J).toLinearMap hker_sub)
      ((η.toLinearMap.quotKerEquivOfSurjective hη_surj).symm (η m)) = _
    change (η.toLinearMap.ker.liftQ (LieSubmodule.Quotient.mk' J).toLinearMap hker_sub)
      ((η.toLinearMap.quotKerEquivOfSurjective hη_surj).symm (η.toLinearMap m)) = _
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]; rfl
  refine ⟨⟨f_lin, ?_⟩, ?_⟩
  ·
    intro x v; obtain ⟨m, rfl⟩ := hη_surj v
    change f_lin (⁅x, η m⁆) = ⁅x, f_lin (η m)⁆
    rw [← η.map_lie, hf, hf, (LieSubmodule.Quotient.mk' J).map_lie]
  ·
    intro q
    obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' J q
    exact ⟨η m, hf m⟩

theorem IsVermaModule.exists_maximal_submodule_irreducible_quotient (hM : IsVermaModule Δ M wt) :

    (∃ (J : LieSubmodule R 𝔤 M), J ≠ ⊤ ∧
      (∀ (N : LieSubmodule R 𝔤 M), N ≠ ⊤ → N ≤ J) ∧

      LieModule.IsIrreducible R 𝔤 (M ⧸ J) ∧

      (∀ (V : Type u_mod) [AddCommGroup V] [Module R V]
        [LieRingModule 𝔤 V] [LieModule R 𝔤 V],
        IsHighestWeightModule Δ V wt →
          ∃ (π : V →ₗ⁅R, 𝔤⁆ (M ⧸ J)), Function.Surjective π)) := by

  obtain ⟨J, hJ_ne_top, hJ_max⟩ := hM.exists_unique_maximal_submodule
  refine ⟨J, hJ_ne_top, hJ_max, ?_, ?_⟩

  · exact hM.quotient_by_maximal_irreducible J hJ_ne_top hJ_max

  · intro V _ _ _ _ hV
    exact hM.simpleQuotient_of_hwm J hJ_ne_top hJ_max V hV

noncomputable def IsVermaModule.maxProperSubmodule (hM : IsVermaModule Δ M wt) :
    LieSubmodule R 𝔤 M :=
  sSup {N : LieSubmodule R 𝔤 M | N ≠ ⊤}

theorem IsVermaModule.maxProperSubmodule_ne_top (hM : IsVermaModule Δ M wt) :
    hM.maxProperSubmodule ≠ ⊤ :=
  hM.proper_sSup

theorem IsVermaModule.le_maxProperSubmodule (hM : IsVermaModule Δ M wt)
    (N : LieSubmodule R 𝔤 M) (hN : N ≠ ⊤) :
    N ≤ hM.maxProperSubmodule :=
  le_sSup hN

noncomputable def IsVermaModule.simpleQuotient (hM : IsVermaModule Δ M wt) :
    Type u_mod :=
  M ⧸ hM.maxProperSubmodule

noncomputable instance IsVermaModule.simpleQuotient_addCommGroup (hM : IsVermaModule Δ M wt) :
    AddCommGroup hM.simpleQuotient :=
  inferInstanceAs (AddCommGroup (M ⧸ hM.maxProperSubmodule))

noncomputable instance IsVermaModule.simpleQuotient_module (hM : IsVermaModule Δ M wt) :
    Module R hM.simpleQuotient :=
  inferInstanceAs (Module R (M ⧸ hM.maxProperSubmodule))

noncomputable instance IsVermaModule.simpleQuotient_lieRingModule (hM : IsVermaModule Δ M wt) :
    LieRingModule 𝔤 hM.simpleQuotient :=
  inferInstanceAs (LieRingModule 𝔤 (M ⧸ hM.maxProperSubmodule))

noncomputable instance IsVermaModule.simpleQuotient_lieModule (hM : IsVermaModule Δ M wt) :
    LieModule R 𝔤 hM.simpleQuotient :=
  inferInstanceAs (LieModule R 𝔤 (M ⧸ hM.maxProperSubmodule))

lemma pbw_uea_nminus_action_in_weight_spaces
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt)
    (u : UniversalEnvelopingAlgebra R Δ.𝔫_neg) :
    (ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec ∈
      ⨆ (μ : Δ.𝔥 →ₗ[R] R), Δ.weightSubspace M μ := by sorry

theorem verma_weight_decomposition
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt) :
    ⨆ (μ : Δ.𝔥 →ₗ[R] R), Δ.weightSubspace M μ = ⊤ := by


  rw [eq_top_iff]
  intro m _

  letI : Module (UniversalEnvelopingAlgebra R Δ.𝔫_neg) M := instModuleUEASubalg Δ.𝔫_neg M
  obtain ⟨φ, hφ⟩ := hM.free_over_nminus

  set u := φ.symm m
  have hm_eq : φ u = m := LinearEquiv.apply_symm_apply φ m

  have hφu : φ u = (ueaSubalgAction Δ.𝔫_neg M u) hM.highestWeightVec := by
    have key : φ u = u • φ (1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) := by
      have : u = u * (1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) := (mul_one u).symm
      conv_lhs => rw [this]
      exact φ.map_smul u 1
    rw [key, hφ]; rfl

  rw [← hm_eq, hφu]
  exact pbw_uea_nminus_action_in_weight_spaces hM u

theorem verma_quotient_weight_surj
    {R : Type*} [CommRing R] [IsDomain R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {V : Type*} [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.IsTorsionFree R V]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt)
    (η : M →ₗ⁅R, 𝔤⁆ V) (hη : Function.Surjective η)
    (μ : Δ.𝔥 →ₗ[R] R) (v : V)
    (hv : v ∈ Δ.weightSubspace V μ) :
    ∃ (w : M), w ∈ Δ.weightSubspace M μ ∧ η w = v := by


  have hindep : iSupIndep (Δ.weightSubspace V) := by
    haveI : IsLieAbelian Δ.𝔥 := Δ.h_abelian
    have heq : (Δ.weightSubspace V) = fun μ =>
        (LieModule.weightSpace (R := R) (L := ↥Δ.𝔥) V (μ ·)).toSubmodule := by
      funext μ; exact Δ.weightSubspace_eq_mathlib V μ
    rw [heq]
    have h_gen_indep := LieModule.iSupIndep_genWeightSpace R (↥Δ.𝔥) V
    rw [← LieSubmodule.iSupIndep_toSubmodule] at h_gen_indep
    exact (h_gen_indep.comp (DFunLike.coe_injective (F := Δ.𝔥 →ₗ[R] R))).mono
      (fun μ => LieModule.weightSpace_le_genWeightSpace V (μ ·))


  obtain ⟨w₀, hw₀⟩ := hη v

  have hw₀_top : w₀ ∈ (⊤ : Submodule R M) := Submodule.mem_top
  rw [← verma_weight_decomposition hM] at hw₀_top
  obtain ⟨f, hf_mem, hf_sum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).mp hw₀_top

  have hη_weight : ∀ (ν : Δ.𝔥 →ₗ[R] R) (m : M),
      m ∈ Δ.weightSubspace M ν → η m ∈ Δ.weightSubspace V ν := by
    intro ν m hm h
    show ⁅(h : 𝔤), η m⁆ = ν h • η m
    rw [← η.map_lie, hm h, map_smul]

  have hf_sum_eq : ∑ x ∈ f.support, f x = w₀ := by
    have := hf_sum; unfold Finsupp.sum at this; simpa using this
  have hv_eq_sum : v = ∑ i ∈ f.support, η (f i) := by
    conv_lhs => rw [← hw₀, ← hf_sum_eq]
    simp only [map_sum]

  classical
  have hv_diff_eq : v - η (f μ) =
      ∑ i ∈ f.support.erase μ, η (f i) := by
    rw [hv_eq_sum]
    by_cases hμ_mem : μ ∈ f.support
    · rw [← Finset.add_sum_erase _ _ hμ_mem, add_sub_cancel_left]
    · rw [Finset.erase_eq_of_notMem hμ_mem]
      have : f μ = 0 := Finsupp.notMem_support_iff.mp hμ_mem
      simp [this]

  have hv_diff_in_biSup : v - η (f μ) ∈
      ⨆ j ∈ {j : Δ.𝔥 →ₗ[R] R | j ≠ μ}, Δ.weightSubspace V j := by
    rw [hv_diff_eq]
    refine Submodule.sum_mem _ (fun i hi => ?_)
    have hi_ne : i ≠ μ := Finset.ne_of_mem_erase hi
    exact Submodule.mem_iSup_of_mem i
      (Submodule.mem_iSup_of_mem hi_ne (hη_weight i (f i) (hf_mem i)))

  have hv_diff_in_Vmu : v - η (f μ) ∈ Δ.weightSubspace V μ :=
    (Δ.weightSubspace V μ).sub_mem hv (hη_weight μ (f μ) (hf_mem μ))

  have hz : v - η (f μ) = 0 := by
    have hd : Disjoint (Δ.weightSubspace V μ)
        (⨆ j ∈ {j : Δ.𝔥 →ₗ[R] R | j ≠ μ}, Δ.weightSubspace V j) := by
      apply hindep.disjoint_biSup
      simp only [Set.mem_setOf_eq, ne_eq, not_not]
    exact Submodule.disjoint_def.mp hd _ hv_diff_in_Vmu hv_diff_in_biSup

  exact ⟨f μ, hf_mem μ, by rw [sub_eq_zero] at hz; exact hz.symm⟩


theorem verma_module_exists
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    ∃ (M : Type u_mod) (_ : AddCommGroup M) (_ : Module R M)
      (_ : LieRingModule 𝔤 M) (_ : LieModule R 𝔤 M),
      Nonempty (IsVermaModule Δ M wt) := by sorry

theorem verma_weightSubspace_finite
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt) (μ : Δ.𝔥 →ₗ[R] R) :
    Module.Finite R ↥(Δ.weightSubspace M μ) := by sorry

theorem IsVermaModule.corollary_8_7 (hM : IsVermaModule Δ M wt)
    (rd : PositiveRootData Δ) :

    (weights Δ M = { μ | rd.IsInQPlus (wt - μ) }) ∧

    (∀ (v : M), (∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = wt h • v) →
      ∃ (c : R), v = c • hM.highestWeightVec) ∧

    (∀ (μ : Δ.𝔥 →ₗ[R] R), Module.Finite R ↥(Δ.weightSubspace M μ)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hM.weight_set_eq rd
  · exact hM.highestWeightSpace_one_dim
  · exact fun μ => verma_weightSubspace_finite hM μ

theorem IsHighestWeightModule.highestWeightSpace_one_dim
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type u_mod} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsHighestWeightModule Δ M wt)
    (v : M) (hv : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = wt h • v) :
    ∃ (c : R), v = c • hM.highestWeightVec := by

  obtain ⟨M₀, inst_acg, inst_mod, inst_lrm, inst_lm, ⟨hM₀⟩⟩ := verma_module_exists Δ wt


  obtain ⟨η, hη_gen⟩ := hM₀.universal_map M hM.highestWeightVec hM.cartan_action hM.npos_action

  have hη_surj : Function.Surjective η := by
    rw [← LieModuleHom.range_eq_top]
    have hv_in_range : hM.highestWeightVec ∈ η.range := ⟨hM₀.highestWeightVec, hη_gen⟩
    have hsub : LieSubmodule.lieSpan R 𝔤 {hM.highestWeightVec} ≤ η.range :=
      LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr hv_in_range)
    rw [hM.generates] at hsub
    exact top_le_iff.mp hsub

  have hv_mem : v ∈ Δ.weightSubspace M wt := hv


  haveI : IsDomain R := by sorry
  haveI : Module.IsTorsionFree R M := by sorry
  obtain ⟨w, hw_wt, hw_eq⟩ := verma_quotient_weight_surj hM₀ η hη_surj wt v hv_mem


  obtain ⟨c2, hc2⟩ := hM₀.highestWeightSpace_one_dim w hw_wt

  refine ⟨c2, ?_⟩
  rw [← hw_eq, hc2, map_smul, hη_gen]

theorem IsHighestWeightModule.weight_decomposition
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type u_mod} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsHighestWeightModule Δ M wt) :
    ⨆ (μ : Δ.𝔥 →ₗ[R] R), Δ.weightSubspace M μ = ⊤ := by

  obtain ⟨M₀, inst_acg, inst_mod, inst_lrm, inst_lm, ⟨hM₀⟩⟩ := verma_module_exists Δ wt

  obtain ⟨η, hη_gen⟩ := hM₀.universal_map M hM.highestWeightVec hM.cartan_action hM.npos_action
  have hη_surj : Function.Surjective η := by
    rw [← LieModuleHom.range_eq_top]
    have hv_in_range : hM.highestWeightVec ∈ η.range := ⟨hM₀.highestWeightVec, hη_gen⟩
    have hsub : LieSubmodule.lieSpan R 𝔤 {hM.highestWeightVec} ≤ η.range :=
      LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr hv_in_range)
    rw [hM.generates] at hsub
    exact top_le_iff.mp hsub

  have hη_wt : ∀ μ, Submodule.map η.toLinearMap (Δ.weightSubspace M₀ μ) ≤ Δ.weightSubspace M μ := by
    intro μ
    rw [Submodule.map_le_iff_le_comap]
    intro w hw h
    show ⁅(h : 𝔤), η.toLinearMap w⁆ = μ h • η.toLinearMap w
    rw [show η.toLinearMap w = η w from rfl, ← η.map_lie]
    have hw' : ⁅(h : 𝔤), w⁆ = μ h • w := hw h
    rw [hw', map_smul]


  have hM₀_decomp : ⨆ μ, Δ.weightSubspace M₀ μ = ⊤ := verma_weight_decomposition hM₀

  have : Submodule.map η.toLinearMap (⨆ μ, Δ.weightSubspace M₀ μ) = ⊤ := by
    rw [hM₀_decomp, Submodule.map_top, LinearMap.range_eq_top.mpr hη_surj]
  rw [Submodule.map_iSup] at this


  have hle : ⨆ μ, Submodule.map η.toLinearMap (Δ.weightSubspace M₀ μ) ≤
      ⨆ μ, Δ.weightSubspace M μ :=
    iSup_mono (hη_wt)
  exact top_le_iff.mp (this ▸ hle)

theorem IsHighestWeightModule.weightSubspace_finite
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type u_mod} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsHighestWeightModule Δ M wt) (μ : Δ.𝔥 →ₗ[R] R) :
    Module.Finite R ↥(Δ.weightSubspace M μ) := by

  obtain ⟨M₀, inst_acg, inst_mod, inst_lrm, inst_lm, ⟨hM₀⟩⟩ := verma_module_exists Δ wt

  obtain ⟨η, hη_gen⟩ := hM₀.universal_map M hM.highestWeightVec hM.cartan_action hM.npos_action
  have hη_surj : Function.Surjective η := by
    rw [← LieModuleHom.range_eq_top]
    have hv_in_range : hM.highestWeightVec ∈ η.range := ⟨hM₀.highestWeightVec, hη_gen⟩
    have hsub : LieSubmodule.lieSpan R 𝔤 {hM.highestWeightVec} ≤ η.range :=
      LieSubmodule.lieSpan_le.mpr (Set.singleton_subset_iff.mpr hv_in_range)
    rw [hM.generates] at hsub
    exact top_le_iff.mp hsub


  haveI : IsDomain R := by sorry
  haveI : Module.IsTorsionFree R M := by sorry

  have heq : Δ.weightSubspace M μ = Submodule.map η.toLinearMap (Δ.weightSubspace M₀ μ) := by
    apply le_antisymm

    · intro v hv
      obtain ⟨w, hw_wt, hw_eq⟩ := verma_quotient_weight_surj hM₀ η hη_surj μ v hv
      exact ⟨w, hw_wt, hw_eq⟩

    · rw [Submodule.map_le_iff_le_comap]
      intro w hw h
      show ⁅(h : 𝔤), η.toLinearMap w⁆ = μ h • η.toLinearMap w
      rw [show η.toLinearMap w = η w from rfl, ← η.map_lie]
      have hw' : ⁅(h : 𝔤), w⁆ = μ h • w := hw h
      rw [hw', map_smul]

  rw [heq]
  haveI : Module.Finite R ↥(Δ.weightSubspace M₀ μ) := verma_weightSubspace_finite hM₀ μ
  exact Module.Finite.map (Δ.weightSubspace M₀ μ) η.toLinearMap

end VermaProperties

def vermaIdeal (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    RingCon (UniversalEnvelopingAlgebra R 𝔤) :=
  ringConGen (fun a b =>
    (∃ h : Δ.𝔥, a = UniversalEnvelopingAlgebra.ι R (h : 𝔤) ∧
               b = algebraMap R (UniversalEnvelopingAlgebra R 𝔤) (wt h)) ∨
    (∃ e : Δ.𝔫_pos, a = UniversalEnvelopingAlgebra.ι R (e : 𝔤) ∧ b = 0))

def VermaModule (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    Type _ :=
  (vermaIdeal Δ wt).Quotient

instance VermaModule.instRing (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    Ring (VermaModule Δ wt) :=
  inferInstanceAs (Ring (vermaIdeal Δ wt).Quotient)

instance VermaModule.instAddCommGroup (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    AddCommGroup (VermaModule Δ wt) :=
  inferInstanceAs (AddCommGroup (vermaIdeal Δ wt).Quotient)

instance VermaModule.instModule (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    Module R (VermaModule Δ wt) :=
  ((vermaIdeal Δ wt).mk'.comp (algebraMap R (UniversalEnvelopingAlgebra R 𝔤))).toModule

def VermaModule.highestWeightVec (Δ : TriangularDecomposition R 𝔤) (wt : Δ.𝔥 →ₗ[R] R) :
    VermaModule Δ wt :=
  (vermaIdeal Δ wt).toQuotient 1

lemma liftQ_comp_quotKerEquiv_symm_apply
    {M₀ : Type*} [AddCommGroup M₀] [Module R M₀]
    {N₁ N₂ : Type*} [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    (f₁ : M₀ →ₗ[R] N₁) (hf₁ : Function.Surjective f₁)
    (f₂ : M₀ →ₗ[R] N₂) (h : f₁.ker ≤ f₂.ker) (m : M₀) :
    (f₁.ker.liftQ f₂ h) ((f₁.quotKerEquivOfSurjective hf₁).symm (f₁ m)) = f₂ m := by
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]; rfl

def lieModuleEquivOfSurjEqKer
    {M₀ V₁ V₂ : Type*}
    [AddCommGroup M₀] [Module R M₀] [LieRingModule 𝔤 M₀] [LieModule R 𝔤 M₀]
    [AddCommGroup V₁] [Module R V₁] [LieRingModule 𝔤 V₁] [LieModule R 𝔤 V₁]
    [AddCommGroup V₂] [Module R V₂] [LieRingModule 𝔤 V₂] [LieModule R 𝔤 V₂]
    (η₁ : M₀ →ₗ⁅R,𝔤⁆ V₁) (hη₁ : Function.Surjective η₁)
    (η₂ : M₀ →ₗ⁅R,𝔤⁆ V₂) (hη₂ : Function.Surjective η₂)
    (hker : η₁.ker = η₂.ker) : V₁ ≃ₗ⁅R,𝔤⁆ V₂ := by
  have hker_sub : η₁.toLinearMap.ker = η₂.toLinearMap.ker :=
    congr_arg LieSubmodule.toSubmodule hker
  have h12 : η₁.toLinearMap.ker ≤ η₂.toLinearMap.ker := le_of_eq hker_sub
  have h21 : η₂.toLinearMap.ker ≤ η₁.toLinearMap.ker := le_of_eq hker_sub.symm

  let f_lin : V₁ →ₗ[R] V₂ :=
    (η₁.toLinearMap.ker.liftQ η₂.toLinearMap h12).comp
      (η₁.toLinearMap.quotKerEquivOfSurjective hη₁).symm.toLinearMap

  let g_lin : V₂ →ₗ[R] V₁ :=
    (η₂.toLinearMap.ker.liftQ η₁.toLinearMap h21).comp
      (η₂.toLinearMap.quotKerEquivOfSurjective hη₂).symm.toLinearMap

  have hf : ∀ m, f_lin (η₁ m) = η₂ m := fun m =>
    liftQ_comp_quotKerEquiv_symm_apply η₁.toLinearMap hη₁ η₂.toLinearMap h12 m
  have hg : ∀ m, g_lin (η₂ m) = η₁ m := fun m =>
    liftQ_comp_quotKerEquiv_symm_apply η₂.toLinearMap hη₂ η₁.toLinearMap h21 m
  exact LieModuleEquiv.mk
    { toLinearMap := f_lin
      map_lie' := by
        intro x v₁; obtain ⟨m, rfl⟩ := hη₁ v₁
        change f_lin (⁅x, η₁ m⁆) = ⁅x, f_lin (η₁ m)⁆
        rw [← η₁.map_lie, hf, hf, η₂.map_lie] }
    g_lin
    (fun v₁ => by
      obtain ⟨m, rfl⟩ := hη₁ v₁; change g_lin (f_lin (η₁ m)) = η₁ m; rw [hf, hg])
    (fun v₂ => by
      obtain ⟨m, rfl⟩ := hη₂ v₂; change f_lin (g_lin (η₂ m)) = η₂ m; rw [hg, hf])

lemma ker_ne_top_of_surj_irreducible
    {M₀ V : Type*}
    [AddCommGroup M₀] [Module R M₀] [LieRingModule 𝔤 M₀] [LieModule R 𝔤 M₀]
    [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (η : M₀ →ₗ⁅R,𝔤⁆ V) (hη : Function.Surjective η)
    (hirr : LieModule.IsIrreducible R 𝔤 V) :
    η.ker ≠ ⊤ := by
  intro h
  have hzero : ∀ m, η m = 0 := fun m => (h ▸ trivial : m ∈ η.ker)
  have hV : ∀ v : V, v = 0 := fun v => by obtain ⟨m, rfl⟩ := hη v; exact hzero m
  exact absurd (show (⊥ : LieSubmodule R 𝔤 V) = ⊤ by ext v; simp [hV v]) IsSimpleOrder.bot_ne_top

lemma ker_eq_unique_max_of_surj_irreducible
    {Δ : TriangularDecomposition R 𝔤}
    {M₀ : Type u_mod} [AddCommGroup M₀] [Module R M₀]
    [LieRingModule 𝔤 M₀] [LieModule R 𝔤 M₀]
    {wt : Δ.𝔥 →ₗ[R] R}
    (_hM : IsVermaModule Δ M₀ wt)
    {V : Type u_mod} [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (η : M₀ →ₗ⁅R,𝔤⁆ V) (hη : Function.Surjective η)
    (hirr : LieModule.IsIrreducible R 𝔤 V)
    (J : LieSubmodule R 𝔤 M₀) (hJ_ne_top : J ≠ ⊤)
    (hJ_max : ∀ (N : LieSubmodule R 𝔤 M₀), N ≠ ⊤ → N ≤ J) :
    η.ker = J := by
  apply le_antisymm
  ·
    exact hJ_max η.ker (ker_ne_top_of_surj_irreducible η hη hirr)
  ·

    rcases IsSimpleOrder.eq_bot_or_eq_top (LieSubmodule.map η J) with hbot | htop
    ·
      intro j hj
      have : η j ∈ LieSubmodule.map η J :=
        (LieSubmodule.mem_map (η j)).mpr ⟨j, hj, rfl⟩
      rw [hbot] at this; exact this
    ·
      exfalso; apply hJ_ne_top; rw [eq_top_iff]; intro m _
      have : η m ∈ LieSubmodule.map η J := htop ▸ trivial
      obtain ⟨j, hj, hjm⟩ := (LieSubmodule.mem_map (η m)).mp this
      have hmj : m - j ∈ η.ker := show η (m - j) = 0 by simp [hjm]
      have : m - j ∈ J :=
        hJ_max η.ker (ker_ne_top_of_surj_irreducible η hη hirr) hmj
      have := J.add_mem this hj; rwa [sub_add_cancel] at this

theorem irreducible_highest_weight_unique_up_to_iso
    (Δ : TriangularDecomposition R 𝔤)
    (wt : Δ.𝔥 →ₗ[R] R)
    (V₁ : Type u_mod) [AddCommGroup V₁] [Module R V₁] [LieRingModule 𝔤 V₁] [LieModule R 𝔤 V₁]
    (V₂ : Type u_mod) [AddCommGroup V₂] [Module R V₂] [LieRingModule 𝔤 V₂] [LieModule R 𝔤 V₂]
    (hV₁ : IsHighestWeightModule Δ V₁ wt) (hirr₁ : LieModule.IsIrreducible R 𝔤 V₁)
    (hV₂ : IsHighestWeightModule Δ V₂ wt) (hirr₂ : LieModule.IsIrreducible R 𝔤 V₂) :
    Nonempty (V₁ ≃ₗ⁅R, 𝔤⁆ V₂) := by

  obtain ⟨M, instACG, instMod, instLRM, instLM, ⟨hM⟩⟩ := verma_module_exists Δ wt

  obtain ⟨η₁, hη₁_surj⟩ := hM.highest_weight_module_is_quotient V₁ hV₁
  obtain ⟨η₂, hη₂_surj⟩ := hM.highest_weight_module_is_quotient V₂ hV₂

  obtain ⟨J, hJ_ne_top, hJ_max⟩ := hM.exists_unique_maximal_submodule

  have hker₁ : η₁.ker = J := ker_eq_unique_max_of_surj_irreducible hM η₁ hη₁_surj hirr₁ J hJ_ne_top hJ_max
  have hker₂ : η₂.ker = J := ker_eq_unique_max_of_surj_irreducible hM η₂ hη₂_surj hirr₂ J hJ_ne_top hJ_max

  exact ⟨lieModuleEquivOfSurjEqKer η₁ hη₁_surj η₂ hη₂_surj (hker₁.trans hker₂.symm)⟩

end
