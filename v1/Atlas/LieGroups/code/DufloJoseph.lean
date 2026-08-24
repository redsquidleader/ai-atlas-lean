/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.MaximalQuotients
import Atlas.LieGroups.code.HighestWeightModules
import Atlas.LieGroups.code.HarishChandraCorollaries

noncomputable section

variable {R : Type*} [CommRing R]
variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]

def evalHC (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ) :
    (Δ.𝔥 →ₗ[R] R) →
    (↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :=
  fun wt =>
    (evalWeight Δ (wt + wg.ρ)).comp
      (wg.invariantSubalgebra.val.comp (chevalley_restriction_hc_iso Δ wg).toAlgHom)

def adjointActionOnHom
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (x : 𝔤) (T : M →ₗ[R] N) : M →ₗ[R] N where
  toFun m := ⁅x, T m⁆ - T ⁅x, m⁆
  map_add' a b := by simp [lie_add, sub_add_sub_comm]
  map_smul' c m := by simp [lie_smul, smul_sub]

def IsFiniteTypeMap
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (T : M →ₗ[R] N) : Prop :=
  ∃ (S : Submodule R (M →ₗ[R] N)),
    Module.Finite R S ∧ T ∈ S ∧
    (∀ (x : 𝔤) (f : M →ₗ[R] N), f ∈ S → adjointActionOnHom M N x f ∈ S)

def HomFin
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N] :
    Submodule R (M →ₗ[R] N) where
  carrier := { T | IsFiniteTypeMap (𝔤 := 𝔤) M N T }
  add_mem' := by
    intro a b ha hb
    show IsFiniteTypeMap (𝔤 := 𝔤) M N (a + b)
    obtain ⟨S₁, hfin₁, ha_mem, hstab₁⟩ := ha
    obtain ⟨S₂, hfin₂, hb_mem, hstab₂⟩ := hb
    refine ⟨S₁ ⊔ S₂, Submodule.finite_sup S₁ S₂, Submodule.add_mem_sup ha_mem hb_mem, ?_⟩
    intro x f hf
    rw [Submodule.mem_sup] at hf
    obtain ⟨f₁, hf₁, f₂, hf₂, rfl⟩ := hf
    have : adjointActionOnHom M N x (f₁ + f₂) = adjointActionOnHom M N x f₁ + adjointActionOnHom M N x f₂ := by
      ext m; simp [adjointActionOnHom, lie_add, sub_add_sub_comm]
    rw [this]
    exact Submodule.add_mem_sup (hstab₁ x f₁ hf₁) (hstab₂ x f₂ hf₂)
  zero_mem' := by
    show IsFiniteTypeMap (𝔤 := 𝔤) M N 0
    exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun x f hf => by
      rw [Submodule.mem_bot] at hf ⊢
      subst hf
      ext m
      simp [adjointActionOnHom]⟩
  smul_mem' := by
    intro c f hf
    show IsFiniteTypeMap (𝔤 := 𝔤) M N (c • f)
    obtain ⟨S, hfin, hf_mem, hstab⟩ := hf
    exact ⟨S, hfin, S.smul_mem c hf_mem, hstab⟩

def homLeftComp (M N : Type*) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] :
    Module.End R N →ₐ[R] Module.End R (M →ₗ[R] N) where
  toFun f := { toFun := fun T => f.comp T
               map_add' := fun T₁ T₂ => by ext; simp
               map_smul' := fun r T => by ext; simp }
  map_one' := by ext T m; simp
  map_mul' := fun f g => by ext T m; simp [Module.End.mul_apply]
  map_zero' := by ext T m; simp
  map_add' := fun f g => by ext T m; simp [LinearMap.add_apply]
  commutes' := fun r => by ext T m; simp [Module.algebraMap_end_apply]

def homRightComp (M N : Type*) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] :
    (Module.End R M)ᵐᵒᵖ →ₐ[R] Module.End R (M →ₗ[R] N) where
  toFun gop := { toFun := fun T => T.comp (MulOpposite.unop gop)
                 map_add' := fun T₁ T₂ => by ext; simp
                 map_smul' := fun r T => by ext; simp }
  map_one' := by ext T m; simp
  map_mul' := fun a b => by
    ext T m
    simp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply]
    rfl
  map_zero' := by ext T m; simp
  map_add' := fun a b => by ext T m; simp [MulOpposite.unop_add, LinearMap.add_apply]
  commutes' := fun r => by
    ext T m
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
      Module.algebraMap_end_apply]
    simp [map_smul]

def HomBimodule
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N] :
    LieBimodule R 𝔤 where
  carrier := M →ₗ[R] N
  leftAction :=
    (homLeftComp M N).comp (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N))
  rightAction :=
    (homRightComp M N).comp
      (AlgHom.op (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M)))
  actions_commute := fun u v T => by


    show (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N) u).comp
        (T.comp (MulOpposite.unop (AlgHom.op (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M)) v))) =
      ((UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N) u).comp T).comp
        (MulOpposite.unop (AlgHom.op (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M)) v))
    ext m
    simp [LinearMap.comp_apply]

@[elab_as_elim]
theorem UniversalEnvelopingAlgebra.induction
    {motive : UniversalEnvelopingAlgebra R 𝔤 → Prop}
    (halg : ∀ r, motive (algebraMap R (UniversalEnvelopingAlgebra R 𝔤) r))
    (hι : ∀ x, motive (UniversalEnvelopingAlgebra.ι R x))
    (hmul : ∀ a b, motive a → motive b → motive (a * b))
    (hadd : ∀ a b, motive a → motive b → motive (a + b))
    (u : UniversalEnvelopingAlgebra R 𝔤) : motive u := by
  obtain ⟨t, rfl⟩ := RingQuot.mkAlgHom_surjective R (UniversalEnvelopingAlgebra.Rel R 𝔤) u
  induction t using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact halg r
  | ι x => exact hι x
  | mul a b ha hb => rw [map_mul]; exact hmul _ _ ha hb
  | add a b ha hb => rw [map_add]; exact hadd _ _ ha hb

lemma uea_ad_leibniz (x : 𝔤) (a b : UniversalEnvelopingAlgebra R 𝔤) :
    UniversalEnvelopingAlgebra.ι R x * (a * b) - (a * b) * UniversalEnvelopingAlgebra.ι R x =
    (UniversalEnvelopingAlgebra.ι R x * a - a * UniversalEnvelopingAlgebra.ι R x) * b +
    a * (UniversalEnvelopingAlgebra.ι R x * b - b * UniversalEnvelopingAlgebra.ι R x) := by
  simp only [mul_sub, sub_mul, mul_assoc]; abel

lemma uea_ad_add (x : 𝔤) (v₁ v₂ : UniversalEnvelopingAlgebra R 𝔤) :
    UniversalEnvelopingAlgebra.ι R x * (v₁ + v₂) - (v₁ + v₂) * UniversalEnvelopingAlgebra.ι R x =
    (UniversalEnvelopingAlgebra.ι R x * v₁ - v₁ * UniversalEnvelopingAlgebra.ι R x) +
    (UniversalEnvelopingAlgebra.ι R x * v₂ - v₂ * UniversalEnvelopingAlgebra.ι R x) := by
  simp only [mul_add, add_mul]; abel

lemma uea_comm_rel (x y : 𝔤) :
    UniversalEnvelopingAlgebra.ι R x * UniversalEnvelopingAlgebra.ι R y -
    UniversalEnvelopingAlgebra.ι R y * UniversalEnvelopingAlgebra.ι R x =
    (UniversalEnvelopingAlgebra.ι R) ⁅x, y⁆ := by
  have h := (UniversalEnvelopingAlgebra.ι R (L := 𝔤)).map_lie (x := x) (y := y)
  simp only [LieRing.of_associative_ring_bracket] at h
  exact h.symm

def ueaIotaRange : Submodule R (UniversalEnvelopingAlgebra R 𝔤) :=
  LinearMap.range (UniversalEnvelopingAlgebra.ι R : 𝔤 →ₗ⁅R⁆ UniversalEnvelopingAlgebra R 𝔤).toLinearMap

def ueaScalarsSubmodule : Submodule R (UniversalEnvelopingAlgebra R 𝔤) :=
  LinearMap.range (Algebra.linearMap R (UniversalEnvelopingAlgebra R 𝔤))

lemma ueaScalarsSubmodule_fg : (ueaScalarsSubmodule (R := R) (𝔤 := 𝔤)).FG := by
  rw [ueaScalarsSubmodule, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map _

lemma ueaIotaRange_fg [Module.Finite R 𝔤] : (ueaIotaRange (R := R) (𝔤 := 𝔤)).FG := by
  rw [ueaIotaRange, LinearMap.range_eq_map]
  exact Module.Finite.fg_top.map _

theorem ueaAdLocallyFinite [Module.Finite R 𝔤]
    (u : UniversalEnvelopingAlgebra R 𝔤) :
    ∃ (S : Submodule R (UniversalEnvelopingAlgebra R 𝔤)),
      Module.Finite R S ∧ u ∈ S ∧
      (∀ (x : 𝔤) (v : UniversalEnvelopingAlgebra R 𝔤), v ∈ S →
        (UniversalEnvelopingAlgebra.ι R x * v - v * UniversalEnvelopingAlgebra.ι R x) ∈ S) := by
  induction u using UniversalEnvelopingAlgebra.induction with
  | halg r =>
    refine ⟨ueaScalarsSubmodule, ?_, ?_, ?_⟩
    · rw [Module.Finite.iff_fg]; exact ueaScalarsSubmodule_fg
    · exact ⟨r, rfl⟩
    · intro x v hv
      obtain ⟨c, rfl⟩ := hv
      have : UniversalEnvelopingAlgebra.ι R x * Algebra.linearMap R (UniversalEnvelopingAlgebra R 𝔤) c -
             Algebra.linearMap R (UniversalEnvelopingAlgebra R 𝔤) c * UniversalEnvelopingAlgebra.ι R x = 0 := by
        simp [Algebra.linearMap_apply, Algebra.commutes]
      rw [this]
      exact ⟨0, map_zero _⟩
  | hι y =>
    refine ⟨ueaIotaRange ⊔ ueaScalarsSubmodule, ?_, ?_, ?_⟩
    · rw [Module.Finite.iff_fg]; exact ueaIotaRange_fg.sup ueaScalarsSubmodule_fg
    · exact Submodule.mem_sup_left (LinearMap.mem_range_self _ y)
    · intro x v hv
      rw [Submodule.mem_sup] at hv
      obtain ⟨v₁, hv₁, v₂, hv₂, rfl⟩ := hv
      rw [uea_ad_add]
      apply Submodule.add_mem
      · obtain ⟨z, rfl⟩ := hv₁
        show UniversalEnvelopingAlgebra.ι R x *
          (UniversalEnvelopingAlgebra.ι R : 𝔤 →ₗ⁅R⁆ _).toLinearMap z -
          (UniversalEnvelopingAlgebra.ι R : 𝔤 →ₗ⁅R⁆ _).toLinearMap z *
          UniversalEnvelopingAlgebra.ι R x ∈ _
        simp only [LieHom.coe_toLinearMap]
        rw [uea_comm_rel]
        exact Submodule.mem_sup_left (LinearMap.mem_range_self _ ⁅x, z⁆)
      · obtain ⟨c, rfl⟩ := hv₂
        have : UniversalEnvelopingAlgebra.ι R x * Algebra.linearMap R (UniversalEnvelopingAlgebra R 𝔤) c -
               Algebra.linearMap R (UniversalEnvelopingAlgebra R 𝔤) c * UniversalEnvelopingAlgebra.ι R x = 0 := by
          simp [Algebra.linearMap_apply, Algebra.commutes]
        rw [this]
        exact Submodule.zero_mem _
  | hadd a b iha ihb =>
    obtain ⟨Sa, hSa_fin, ha_mem, hSa_stab⟩ := iha
    obtain ⟨Sb, hSb_fin, hb_mem, hSb_stab⟩ := ihb
    refine ⟨Sa ⊔ Sb, ?_, ?_, ?_⟩
    · rw [Module.Finite.iff_fg]
      exact (Module.Finite.iff_fg.mp hSa_fin).sup (Module.Finite.iff_fg.mp hSb_fin)
    · exact Submodule.add_mem _ (Submodule.mem_sup_left ha_mem) (Submodule.mem_sup_right hb_mem)
    · intro x v hv
      rw [Submodule.mem_sup] at hv
      obtain ⟨va, hva, vb, hvb, rfl⟩ := hv
      rw [uea_ad_add]
      exact Submodule.add_mem _ (Submodule.mem_sup_left (hSa_stab x va hva))
        (Submodule.mem_sup_right (hSb_stab x vb hvb))
  | hmul a b iha ihb =>
    obtain ⟨Sa, hSa_fin, ha_mem, hSa_stab⟩ := iha
    obtain ⟨Sb, hSb_fin, hb_mem, hSb_stab⟩ := ihb
    refine ⟨Sa * Sb, ?_, ?_, ?_⟩
    · rw [Module.Finite.iff_fg]
      exact (Module.Finite.iff_fg.mp hSa_fin).mul (Module.Finite.iff_fg.mp hSb_fin)
    · exact Submodule.mul_mem_mul ha_mem hb_mem
    · intro x v hv
      refine Submodule.mul_induction_on hv ?_ ?_
      · intro sa hsa sb hsb
        rw [uea_ad_leibniz]
        exact Submodule.add_mem _ (Submodule.mul_mem_mul (hSa_stab x sa hsa) hsb)
          (Submodule.mul_mem_mul hsa (hSb_stab x sb hsb))
      · intro v₁ v₂ hv₁ hv₂
        rw [uea_ad_add]
        exact Submodule.add_mem _ hv₁ hv₂

lemma ueaAction_adjoint_intertwine
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (act : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M)
    (hcompat : ∀ (x : 𝔤) (m : M), act (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆)
    (x : 𝔤) (u : UniversalEnvelopingAlgebra R 𝔤) :
    adjointActionOnHom M M x (act u) =
    act (UniversalEnvelopingAlgebra.ι R x * u - u * UniversalEnvelopingAlgebra.ι R x) := by
  ext m
  simp only [adjointActionOnHom, LinearMap.coe_mk, AddHom.coe_mk, map_sub, map_mul,
    LinearMap.sub_apply]
  change ⁅x, (act u) m⁆ - (act u) ⁅x, m⁆ =
    act (UniversalEnvelopingAlgebra.ι R x) ((act u) m) - (act u) (act (UniversalEnvelopingAlgebra.ι R x) m)
  rw [hcompat x ((act u) m), hcompat x m]

lemma adjointActionOnHom_left_comp
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (x : 𝔤) (f : N →ₗ[R] N) (T : M →ₗ[R] N) :
    adjointActionOnHom M N x (f.comp T) =
    (adjointActionOnHom N N x f).comp T + f.comp (adjointActionOnHom M N x T) := by
  ext m
  simp [adjointActionOnHom, LinearMap.comp_apply, LinearMap.add_apply]

lemma adjointActionOnHom_right_comp
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (x : 𝔤) (T : M →ₗ[R] N) (g : M →ₗ[R] M) :
    adjointActionOnHom M N x (T.comp g) =
    (adjointActionOnHom M N x T).comp g + T.comp (adjointActionOnHom M M x g) := by
  ext m
  simp [adjointActionOnHom, LinearMap.comp_apply, LinearMap.add_apply]

theorem ueaAction_preserves_HomFin [Module.Finite R 𝔤]
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (u : UniversalEnvelopingAlgebra R 𝔤) (T : M →ₗ[R] N)
    (hT : T ∈ HomFin (R := R) (𝔤 := 𝔤) M N) :
    (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N) u).comp T ∈
      HomFin (R := R) (𝔤 := 𝔤) M N ∧
    T.comp (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M) u) ∈
      HomFin (R := R) (𝔤 := 𝔤) M N := by
  obtain ⟨S_T, hfin_T, hT_mem, hT_stab⟩ := hT
  obtain ⟨S_u, hfin_u, hu_mem, hu_stab⟩ := ueaAdLocallyFinite (R := R) (𝔤 := 𝔤) u
  let actN := UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N)
  let actM := UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M)
  have hcompatN : ∀ (y : 𝔤) (n : N), actN (UniversalEnvelopingAlgebra.ι R y) n = ⁅y, n⁆ := by
    intro y n; simp [actN, LieModule.toEnd_apply_apply]
  have hcompatM : ∀ (y : 𝔤) (m : M), actM (UniversalEnvelopingAlgebra.ι R y) m = ⁅y, m⁆ := by
    intro y m; simp [actM, LieModule.toEnd_apply_apply]

  let compBilinL : (N →ₗ[R] N) →ₗ[R] (M →ₗ[R] N) →ₗ[R] (M →ₗ[R] N) :=
    LinearMap.llcomp R M N N
  let compBilinR : (M →ₗ[R] N) →ₗ[R] (M →ₗ[R] M) →ₗ[R] (M →ₗ[R] N) :=
    { toFun := fun T' => {
        toFun := fun g => T'.comp g
        map_add' := fun g₁ g₂ => by ext; simp [LinearMap.comp_apply, LinearMap.add_apply]
        map_smul' := fun r g => by ext; simp [LinearMap.comp_apply, LinearMap.smul_apply] }
      map_add' := fun T₁ T₂ => by ext g m; simp [LinearMap.add_apply]
      map_smul' := fun r T₁ => by ext g m; simp [LinearMap.smul_apply] }
  let imgS_uN := S_u.map actN.toLinearMap
  let imgS_uM := S_u.map actM.toLinearMap
  let W_left := Submodule.map₂ compBilinL imgS_uN S_T
  let W_right := Submodule.map₂ compBilinR S_T imgS_uM

  have hfin_imgN : imgS_uN.FG := (Module.Finite.iff_fg.mp (Module.Finite.map S_u actN.toLinearMap))
  have hfin_imgM : imgS_uM.FG := (Module.Finite.iff_fg.mp (Module.Finite.map S_u actM.toLinearMap))
  have hfin_ST : S_T.FG := Module.Finite.iff_fg.mp hfin_T

  have imgN_stab : ∀ (x : 𝔤) (f : N →ₗ[R] N), f ∈ imgS_uN →
      adjointActionOnHom N N x f ∈ imgS_uN := by
    intro x f hf
    obtain ⟨v, hv_mem, rfl⟩ := Submodule.mem_map.mp hf
    simp only [AlgHom.toLinearMap_apply]
    rw [ueaAction_adjoint_intertwine N actN hcompatN x v]
    exact Submodule.mem_map_of_mem (hu_stab x v hv_mem)

  have imgM_stab : ∀ (x : 𝔤) (g : M →ₗ[R] M), g ∈ imgS_uM →
      adjointActionOnHom M M x g ∈ imgS_uM := by
    intro x g hg
    obtain ⟨v, hv_mem, rfl⟩ := Submodule.mem_map.mp hg
    simp only [AlgHom.toLinearMap_apply]
    rw [ueaAction_adjoint_intertwine M actM hcompatM x v]
    exact Submodule.mem_map_of_mem (hu_stab x v hv_mem)
  constructor
  ·
    show IsFiniteTypeMap (𝔤 := 𝔤) M N ((actN u).comp T)
    refine ⟨W_left, ?_, ?_, ?_⟩
    · rw [Module.Finite.iff_fg]; exact hfin_imgN.map₂ compBilinL hfin_ST
    · exact Submodule.apply_mem_map₂ compBilinL (Submodule.mem_map_of_mem hu_mem) hT_mem
    ·
      intro x w hw


      have hW_left_le : W_left ≤ W_left.comap
          ({ toFun := adjointActionOnHom M N x
             map_add' := fun f g => by ext m; simp [adjointActionOnHom, lie_add, sub_add_sub_comm]
             map_smul' := fun c f => by ext m; simp [adjointActionOnHom, lie_smul, smul_sub]
           } : (M →ₗ[R] N) →ₗ[R] (M →ₗ[R] N)) := by
        rw [Submodule.map₂_le]
        intro f hf T' hT'

        show adjointActionOnHom M N x (compBilinL f T') ∈ W_left
        change adjointActionOnHom M N x (f.comp T') ∈ W_left
        rw [adjointActionOnHom_left_comp M N x f T']


        apply W_left.add_mem
        · exact Submodule.apply_mem_map₂ compBilinL (imgN_stab x f hf) hT'
        · exact Submodule.apply_mem_map₂ compBilinL hf (hT_stab x T' hT')
      exact hW_left_le hw
  ·
    show IsFiniteTypeMap (𝔤 := 𝔤) M N (T.comp (actM u))
    refine ⟨W_right, ?_, ?_, ?_⟩
    · rw [Module.Finite.iff_fg]; exact hfin_ST.map₂ compBilinR hfin_imgM
    · exact Submodule.apply_mem_map₂ compBilinR hT_mem (Submodule.mem_map_of_mem hu_mem)
    · intro x w hw
      have hW_right_le : W_right ≤ W_right.comap
          ({ toFun := adjointActionOnHom M N x
             map_add' := fun f g => by ext m; simp [adjointActionOnHom, lie_add, sub_add_sub_comm]
             map_smul' := fun c f => by ext m; simp [adjointActionOnHom, lie_smul, smul_sub]
           } : (M →ₗ[R] N) →ₗ[R] (M →ₗ[R] N)) := by
        rw [Submodule.map₂_le]
        intro T' hT' g hg
        show adjointActionOnHom M N x (compBilinR T' g) ∈ W_right
        change adjointActionOnHom M N x (T'.comp g) ∈ W_right
        rw [adjointActionOnHom_right_comp M N x T' g]
        apply W_right.add_mem
        · exact Submodule.apply_mem_map₂ compBilinR (hT_stab x T' hT') hg
        · exact Submodule.apply_mem_map₂ compBilinR hT' (imgM_stab x g hg)
      exact hW_right_le hw

theorem leftAction_preserves_HomFin [Module.Finite R 𝔤]
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (u : UniversalEnvelopingAlgebra R 𝔤) (T : M →ₗ[R] N)
    (hT : T ∈ HomFin (R := R) (𝔤 := 𝔤) M N) :
    (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N) u).comp T ∈
      HomFin (R := R) (𝔤 := 𝔤) M N :=
  (ueaAction_preserves_HomFin M N u T hT).1

theorem rightAction_preserves_HomFin [Module.Finite R 𝔤]
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (u : UniversalEnvelopingAlgebra R 𝔤) (T : M →ₗ[R] N)
    (hT : T ∈ HomFin (R := R) (𝔤 := 𝔤) M N) :
    T.comp (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M) u) ∈
      HomFin (R := R) (𝔤 := 𝔤) M N :=
  (ueaAction_preserves_HomFin M N u T hT).2

def HomFinBimodule [Module.Finite R 𝔤]
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N] :
    LieBimodule R 𝔤 where
  carrier := ↥(HomFin (R := R) (𝔤 := 𝔤) M N)
  leftAction := {
    toFun := fun u => {
      toFun := fun ⟨T, hT⟩ => ⟨(UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 N) u).comp T,
        leftAction_preserves_HomFin M N u T hT⟩
      map_add' := fun ⟨T₁, _⟩ ⟨T₂, _⟩ => by
        ext m; simp [LinearMap.comp_apply, map_add]
      map_smul' := fun r ⟨T₁, _⟩ => by
        ext m; simp [LinearMap.comp_apply, map_smul]
    }
    map_one' := by ext ⟨T, _⟩ m; simp
    map_mul' := fun u₁ u₂ => by
      ext ⟨T, _⟩ m; simp [Module.End.mul_apply, LinearMap.comp_apply]
    map_zero' := by ext ⟨T, _⟩ m; simp
    map_add' := fun u₁ u₂ => by
      ext ⟨T, _⟩ m; simp [LinearMap.add_apply, LinearMap.comp_apply]
    commutes' := fun r => by
      ext ⟨T, _⟩ m; simp [Module.algebraMap_end_apply]
  }
  rightAction := {
    toFun := fun vop => {
      toFun := fun ⟨T, hT⟩ => ⟨T.comp (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M) (MulOpposite.unop vop)),
        rightAction_preserves_HomFin M N (MulOpposite.unop vop) T hT⟩
      map_add' := fun ⟨T₁, _⟩ ⟨T₂, _⟩ => by
        ext m; simp [LinearMap.comp_apply]
      map_smul' := fun r ⟨T₁, _⟩ => by
        ext m; simp [LinearMap.comp_apply]
    }
    map_one' := by ext ⟨T, _⟩ m; simp
    map_mul' := fun a b => by
      ext ⟨T, _⟩ m
      simp only [Module.End.mul_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
        MulOpposite.unop_mul, map_mul]
    map_zero' := by ext ⟨T, _⟩ m; simp
    map_add' := fun a b => by
      ext ⟨T, _⟩ m; simp [MulOpposite.unop_add, LinearMap.add_apply, LinearMap.comp_apply]
    commutes' := fun r => by
      ext ⟨T, _⟩ m
      simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
        Module.algebraMap_end_apply]
      simp [map_smul]
  }
  actions_commute := fun u v ⟨T, hT⟩ => by
    ext m
    simp [LinearMap.comp_apply]


theorem exercise_8_13_hom_locally_finite_verma
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wtM : Δ.𝔥 →ₗ[R] R) (hM : IsVermaModule Δ M wtM)
    (N : Type*) [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (wtN : Δ.𝔥 →ₗ[R] R) (hN : IsVermaModule Δ N wtN)
    (T : M →ₗ[R] N) :
    ∃ (S : Submodule R (M →ₗ[R] N)),
      Module.Finite R S ∧ T ∈ S ∧
      ∀ (x : 𝔤) (f : M →ₗ[R] N), f ∈ S →
        adjointActionOnHom (R := R) (𝔤 := 𝔤) M N x f ∈ S := by


  sorry


theorem exercise_8_13_hom_admissible_verma
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤] [Module.Finite R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wtM : Δ.𝔥 →ₗ[R] R) (hM : IsVermaModule Δ M wtM)
    (N : Type*) [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (wtN : Δ.𝔥 →ₗ[R] R) (hN : IsVermaModule Δ N wtN)
    (V : Type*) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V] [LieModule.IsIrreducible R 𝔤 V] :
    Module.Finite R (HomAdEquivariant V (HomFinBimodule (R := R) (𝔤 := 𝔤) M N)) := by


  sorry

theorem catO_hom_equivariant_injection_into_verma
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (rd : PositiveRootData Δ)
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (hM : IsCategoryO Δ rd M) (hN : IsCategoryO Δ rd N) :
    ∃ (M' : Type) (N' : Type)
      (_ : AddCommGroup M') (_ : Module R M') (_ : LieRingModule 𝔤 M') (_ : LieModule R 𝔤 M')
      (_ : AddCommGroup N') (_ : Module R N') (_ : LieRingModule 𝔤 N') (_ : LieModule R 𝔤 N')
      (wtM : Δ.𝔥 →ₗ[R] R) (hVM : IsVermaModule Δ M' wtM)
      (wtN : Δ.𝔥 →ₗ[R] R) (hVN : IsVermaModule Δ N' wtN)
      (ι : (M →ₗ[R] N) →ₗ[R] (M' →ₗ[R] N')),
      Function.Injective ι ∧
      (∀ (x : 𝔤) (T : M →ₗ[R] N),
        ι (adjointActionOnHom (R := R) (𝔤 := 𝔤) M N x T) =
        adjointActionOnHom (R := R) (𝔤 := 𝔤) M' N' x (ι T)) := by


  sorry

theorem catO_hom_bimodule_injection_into_verma
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤] [Module.Finite R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (rd : PositiveRootData Δ)
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (hM : IsCategoryO Δ rd M) (hN : IsCategoryO Δ rd N) :
    ∃ (M' : Type) (N' : Type)
      (_ : AddCommGroup M') (_ : Module R M') (_ : LieRingModule 𝔤 M') (_ : LieModule R 𝔤 M')
      (_ : AddCommGroup N') (_ : Module R N') (_ : LieRingModule 𝔤 N') (_ : LieModule R 𝔤 N')
      (wtM : Δ.𝔥 →ₗ[R] R) (hVM : IsVermaModule Δ M' wtM)
      (wtN : Δ.𝔥 →ₗ[R] R) (hVN : IsVermaModule Δ N' wtN)
      (ι : (HomFinBimodule (R := R) (𝔤 := 𝔤) M N).carrier →ₗ[R]
           (HomFinBimodule (R := R) (𝔤 := 𝔤) M' N').carrier),
      Function.Injective ι ∧
      (∀ (u : UniversalEnvelopingAlgebra R 𝔤)
         (m : (HomFinBimodule (R := R) (𝔤 := 𝔤) M N).carrier),
        ι ((HomFinBimodule (R := R) (𝔤 := 𝔤) M N).leftAction u m) =
        (HomFinBimodule (R := R) (𝔤 := 𝔤) M' N').leftAction u (ι m)) ∧
      (∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ)
         (m : (HomFinBimodule (R := R) (𝔤 := 𝔤) M N).carrier),
        ι ((HomFinBimodule (R := R) (𝔤 := 𝔤) M N).rightAction u m) =
        (HomFinBimodule (R := R) (𝔤 := 𝔤) M' N').rightAction u (ι m)) := by


  sorry

theorem hom_locally_finite_catO
    {R : Type*} [CommRing R] [IsNoetherianRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (rd : PositiveRootData Δ)
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (hM : IsCategoryO Δ rd M) (hN : IsCategoryO Δ rd N)
    (T : M →ₗ[R] N) :
    ∃ (S : Submodule R (M →ₗ[R] N)),
      Module.Finite R S ∧ T ∈ S ∧
      ∀ (x : 𝔤) (f : M →ₗ[R] N), f ∈ S →
        adjointActionOnHom (R := R) (𝔤 := 𝔤) M N x f ∈ S := by

  obtain ⟨M', N', instAM', instMM', instLRM', instLM', instAN', instMN', instLRN', instLN',
          wtM, hVM, wtN, hVN, ι, hι_inj, hι_equiv⟩ :=
    catO_hom_equivariant_injection_into_verma Δ rd M N hM hN

  obtain ⟨S', hS'fin, hιT_in_S', hS'stab⟩ :=
    exercise_8_13_hom_locally_finite_verma Δ M' wtM hVM N' wtN hVN (ι T)

  let S := S'.comap ι

  have hι_maps : ∀ x ∈ S, ι x ∈ S' := fun x hx => hx
  let ι_res : ↥S →ₗ[R] ↥S' :=
    { toFun := fun ⟨f, hf⟩ => ⟨ι f, hι_maps f hf⟩
      map_add' := fun ⟨a, _⟩ ⟨b, _⟩ => by
        ext; simp [map_add]
      map_smul' := fun r ⟨a, _⟩ => by
        ext; simp [map_smul] }
  have hι_res_inj : Function.Injective ι_res := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ heq
    simp only [ι_res, LinearMap.coe_mk, AddHom.coe_mk, Subtype.mk.injEq] at heq
    exact Subtype.ext (hι_inj heq)

  haveI : IsNoetherian R ↥S' := isNoetherian_of_isNoetherianRing_of_finite R ↥S'
  refine ⟨S, Module.Finite.of_injective ι_res hι_res_inj, ?_, ?_⟩
  ·
    exact hιT_in_S'
  ·
    intro x f hf
    show ι (adjointActionOnHom M N x f) ∈ S'
    rw [hι_equiv]
    exact hS'stab x (ι f) hf

theorem HomAdEquivariant.finite_of_injection
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {V : Type*} [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    {M N : LieBimodule R 𝔤}
    (ι : M.carrier →ₗ[R] N.carrier)
    (hι_inj : Function.Injective ι)
    (hι_left : ∀ (u : UniversalEnvelopingAlgebra R 𝔤) (m : M.carrier),
      ι (M.leftAction u m) = N.leftAction u (ι m))
    (hι_right : ∀ (u : (UniversalEnvelopingAlgebra R 𝔤)ᵐᵒᵖ) (m : M.carrier),
      ι (M.rightAction u m) = N.rightAction u (ι m))
    (hN_fin : Module.Finite R (HomAdEquivariant V N)) :
    Module.Finite R (HomAdEquivariant V M) := by

  let pc := HomAdEquivariant.postcomp (R := R) (𝔤 := 𝔤) (V := V) ι hι_left hι_right

  have hpc_inj : Function.Injective pc := by
    intro ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ heq
    simp only [pc, HomAdEquivariant.postcomp, LinearMap.coe_mk, AddHom.coe_mk] at heq
    apply Subtype.ext
    ext v
    have : ι (f₁ v) = ι (f₂ v) := by
      have := congr_arg (fun x => (x : V →ₗ[R] N.carrier) v) (Subtype.mk.inj heq)
      simpa [LinearMap.comp_apply] using this
    exact hι_inj this
  exact Module.Finite.of_injective pc hpc_inj

theorem hom_admissible_catO
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤] [Module.Finite R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (rd : PositiveRootData Δ)
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (hM : IsCategoryO Δ rd M) (hN : IsCategoryO Δ rd N)
    (V : Type*) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V] [LieModule.IsIrreducible R 𝔤 V] :
    Module.Finite R (HomAdEquivariant V (HomFinBimodule (R := R) (𝔤 := 𝔤) M N)) := by

  obtain ⟨M', N', instAM', instMM', instLRM', instLM', instAN', instMN', instLRN', instLN',
          wtM, hVM, wtN, hVN, ι, hι_inj, hι_left, hι_right⟩ :=
    catO_hom_bimodule_injection_into_verma Δ rd M N hM hN

  have hVerma_fin := exercise_8_13_hom_admissible_verma Δ M' wtM hVM N' wtN hVN V

  exact HomAdEquivariant.finite_of_injection ι hι_inj hι_left hι_right hVerma_fin

lemma homFinBimodule_adjointAction_val [Module.Finite R 𝔤]
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (x : 𝔤) (T : ↥(HomFin (R := R) (𝔤 := 𝔤) M N)) :
    ((HomFinBimodule (R := R) (𝔤 := 𝔤) M N).adjointAction x T).val =
    adjointActionOnHom (R := R) (𝔤 := 𝔤) M N x T.val := by
  unfold HomFinBimodule LieBimodule.adjointAction adjointActionOnHom
  ext m
  simp [LinearMap.sub_apply, LinearMap.comp_apply]

theorem proposition_18_2 [Module.Finite R 𝔤] [IsNoetherianRing R]
    (Δ : TriangularDecomposition R 𝔤) (rd : PositiveRootData Δ)
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (hM : IsCategoryO Δ rd M) (hN : IsCategoryO Δ rd N) :
    IsAdmissibleBimodule (HomFinBimodule (R := R) (𝔤 := 𝔤) M N) := by
  constructor
  ·
    constructor
    intro ⟨T, hT_mem⟩


    obtain ⟨S', hS'fin, hT_in_S', hS'stab⟩ :=
      hom_locally_finite_catO Δ rd M N hM hN T


    have hS'_le_HomFin : S' ≤ HomFin (R := R) (𝔤 := 𝔤) M N := by
      intro f hf
      exact ⟨S', hS'fin, hf, hS'stab⟩

    let S_sub : Submodule R ↥(HomFin (R := R) (𝔤 := 𝔤) M N) :=
      S'.comap (HomFin (R := R) (𝔤 := 𝔤) M N).subtype
    refine ⟨S_sub, ?_, ?_, ?_⟩
    ·

      have : Module.Finite R S' := hS'fin

      let surj_map : S' →ₗ[R] S_sub := {
        toFun := fun ⟨f, hf⟩ => ⟨⟨f, hS'_le_HomFin hf⟩, show f ∈ S' from hf⟩
        map_add' := fun ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ => by
          ext; rfl
        map_smul' := fun r ⟨f₁, hf₁⟩ => by
          ext; rfl
      }
      have hsurj : Function.Surjective surj_map := by
        intro ⟨⟨f, hf_homfin⟩, hf_S'⟩
        exact ⟨⟨f, hf_S'⟩, by ext; rfl⟩
      exact Module.Finite.of_surjective surj_map hsurj
    ·
      show T ∈ S'
      exact hT_in_S'
    ·
      intro x ⟨f, hf_homfin⟩ (hf_in_S' : f ∈ S')


      show ((HomFinBimodule (R := R) (𝔤 := 𝔤) M N).adjointAction x ⟨f, hf_homfin⟩).val ∈ S'
      rw [homFinBimodule_adjointAction_val]
      exact hS'stab x f hf_in_S'
  ·
    intro V _instACG _instMod _instLRM _instLM _instFin _instIrr
    exact hom_admissible_catO Δ rd M N hM hN V


theorem postcomp_tensor_finiteType_ax
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {M N : Type*} [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    {V : Type*} [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V]
    {VN : Type*} [AddCommGroup VN] [Module R VN] [LieRingModule 𝔤 VN] [LieModule R 𝔤 VN]
    (tensor_VN : V →ₗ[R] N →ₗ[R] VN)
    (hiso_VN : Function.Bijective (TensorProduct.lift tensor_VN :
      TensorProduct R V N →ₗ[R] VN))
    (v : V) (f : ↥(HomFin (R := R) (𝔤 := 𝔤) M N)) :
    (tensor_VN v).comp (↑f : M →ₗ[R] N) ∈ HomFin (R := R) (𝔤 := 𝔤) M VN := by
  sorry


theorem proposition_18_3_bijective_ax
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {M N : Type*} [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    {V : Type*} [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V]
    {VN : Type*} [AddCommGroup VN] [Module R VN] [LieRingModule 𝔤 VN] [LieModule R 𝔤 VN]
    (tensor_VN : V →ₗ[R] N →ₗ[R] VN)
    (hiso_VN : Function.Bijective (TensorProduct.lift tensor_VN :
      TensorProduct R V N →ₗ[R] VN))
    (φ : TensorProduct R V (↥(HomFin (R := R) (𝔤 := 𝔤) M N)) →ₗ[R]
          ↥(HomFin (R := R) (𝔤 := 𝔤) M VN))
    (hφ_nat : ∀ (f : ↥(HomFin (R := R) (𝔤 := 𝔤) M N)) (v : V) (m : M),
      ((φ (v ⊗ₜ[R] f) : M →ₗ[R] VN) m) = tensor_VN v ((↑f : M →ₗ[R] N) m)) :
    Function.Bijective φ := by
  sorry

theorem proposition_18_3
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (rd : PositiveRootData Δ)
    (M N : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (hM : IsCategoryO Δ rd M) (hN : IsCategoryO Δ rd N)
    (V : Type*) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V]
    (VN : Type*) [AddCommGroup VN] [Module R VN] [LieRingModule 𝔤 VN] [LieModule R 𝔤 VN]
    (tensor_VN : V →ₗ[R] N →ₗ[R] VN)
    (hiso_VN : Function.Bijective (TensorProduct.lift tensor_VN :
      TensorProduct R V N →ₗ[R] VN)) :
    ∃ (φ : TensorProduct R V (↥(HomFin (R := R) (𝔤 := 𝔤) M N)) →ₗ[R]
          ↥(HomFin (R := R) (𝔤 := 𝔤) M VN)),
      Function.Bijective φ ∧
      ∀ (f : ↥(HomFin (R := R) (𝔤 := 𝔤) M N)),
        ∀ (v : V) (m : M),
          ((φ (v ⊗ₜ[R] f) : M →ₗ[R] VN) m) = tensor_VN v ((f : M →ₗ[R] N) m) := by
  have image_in_HomFin : ∀ (v : V) (f : ↥(HomFin (R := R) (𝔤 := 𝔤) M N)),
      (tensor_VN v).comp (↑f : M →ₗ[R] N) ∈ HomFin (R := R) (𝔤 := 𝔤) M VN :=
    fun v f => postcomp_tensor_finiteType_ax tensor_VN hiso_VN v f
  let φ : TensorProduct R V (↥(HomFin (R := R) (𝔤 := 𝔤) M N)) →ₗ[R]
      ↥(HomFin (R := R) (𝔤 := 𝔤) M VN) :=
    TensorProduct.lift {
      toFun := fun v => {
        toFun := fun f => ⟨(tensor_VN v).comp (↑f : M →ₗ[R] N), image_in_HomFin v f⟩
        map_add' := fun f g => by
          apply Subtype.ext; ext m
          simp [LinearMap.comp_apply, map_add]
        map_smul' := fun r f => by
          apply Subtype.ext; ext m
          simp [LinearMap.comp_apply, LinearMap.smul_apply]
      }
      map_add' := fun v w => by
        ext f m
        simp [LinearMap.comp_apply, map_add]
      map_smul' := fun r v => by
        ext f m
        simp [LinearMap.comp_apply]
    }
  have hφ_nat : ∀ (f : ↥(HomFin (R := R) (𝔤 := 𝔤) M N)) (v : V) (m : M),
      ((φ (v ⊗ₜ[R] f) : M →ₗ[R] VN) m) = tensor_VN v ((↑f : M →ₗ[R] N) m) := by
    intro f v m
    simp only [φ, TensorProduct.lift.tmul]
    simp [LinearMap.comp_apply]
  exact ⟨φ, proposition_18_3_bijective_ax tensor_VN hiso_VN φ hφ_nat, hφ_nat⟩

def HomEquivariant
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (N : Type*) [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N] :
    Submodule R (M →ₗ[R] N) where
  carrier := { f | ∀ (x : 𝔤) (m : M), f ⁅x, m⁆ = ⁅x, f m⁆ }
  add_mem' := fun {f g} hf hg x m => by
    simp only [LinearMap.add_apply]; rw [hf x m, hg x m, lie_add]
  zero_mem' := fun x m => by simp
  smul_mem' := fun c {f} hf x m => by
    simp only [LinearMap.smul_apply]; rw [hf x m, lie_smul]
theorem exercise_8_14_simpleVermaSubmodule_exists
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hVerma : IsVermaModule Δ M wt) :
    ∃ (M' : Type*) (_ : AddCommGroup M') (_ : Module R M')
      (_ : LieRingModule 𝔤 M') (_ : LieModule R 𝔤 M')
      (_ : LieModule.IsIrreducible R 𝔤 M')
      (wt' : Δ.𝔥 →ₗ[R] R) (_ : IsVermaModule Δ M' wt'),
      Nonempty (M' →ₗ[R] M) := by


  sorry


theorem prop_8_5_tensor_retraction
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hVerma : IsVermaModule Δ M wt)
    (N : Type*) [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (tensor : V →ₗ[R] M →ₗ[R] N)
    (hiso : Function.Surjective (TensorProduct.lift tensor : TensorProduct R V M →ₗ[R] N)) :

    ∃ (r : N →ₗ[R] V),


      (∀ (v : V), r (tensor v hVerma.highestWeightVec) = v) ∧


      (∀ (f : M →ₗ[R] N),
        (∀ (x : 𝔤) (m : M), f ⁅x, m⁆ = ⁅x, f m⁆) →
        r (f hVerma.highestWeightVec) ∈ WeightSpace Δ V 0 ∧
        f hVerma.highestWeightVec = tensor (r (f hVerma.highestWeightVec)) hVerma.highestWeightVec) ∧


      (∀ (f₁ f₂ : M →ₗ[R] N),
        (∀ (x : 𝔤) (m : M), f₁ ⁅x, m⁆ = ⁅x, f₁ m⁆) →
        (∀ (x : 𝔤) (m : M), f₂ ⁅x, m⁆ = ⁅x, f₂ m⁆) →
        f₁ hVerma.highestWeightVec = f₂ hVerma.highestWeightVec → f₁ = f₂) := by


  sorry

lemma prop_18_5_restriction_injective
    (Δ : TriangularDecomposition R 𝔤)
    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (_hVerma : IsVermaModule Δ M wt)
    (N : Type*) [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (_tensor : V →ₗ[R] M →ₗ[R] N)
    (_hiso : Function.Surjective (TensorProduct.lift _tensor : TensorProduct R V M →ₗ[R] N)) :


    ∃ (φ : @HomEquivariant R _ 𝔤 _ _ M _ _ _ _ N _ _ _ _ →ₗ[R]
           WeightSpace Δ V 0),
      Function.Injective φ := by

  obtain ⟨r, hr_left_inv, hr_equiv, hr_unique⟩ :=
    prop_8_5_tensor_retraction Δ V M wt _hVerma N _tensor _hiso

  let hwv := _hVerma.highestWeightVec

  let φ_fun : @HomEquivariant R _ 𝔤 _ _ M _ _ _ _ N _ _ _ _ → WeightSpace Δ V 0 :=
    fun f => ⟨r (f.val hwv), (hr_equiv f.val f.property).1⟩
  have h_add : ∀ f g, φ_fun (f + g) = φ_fun f + φ_fun g := by
    intro f g; ext; simp [φ_fun, LinearMap.add_apply, map_add]
  have h_smul : ∀ (c : R) f, φ_fun (c • f) = c • φ_fun f := by
    intro c f; ext; simp [φ_fun, LinearMap.smul_apply, map_smul]
  let φ : @HomEquivariant R _ 𝔤 _ _ M _ _ _ _ N _ _ _ _ →ₗ[R] WeightSpace Δ V 0 :=
    { toFun := φ_fun
      map_add' := h_add
      map_smul' := h_smul }
  refine ⟨φ, ?_⟩

  intro ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ hφ_eq

  have h_rv : r (f₁ hwv) = r (f₂ hwv) := by
    have := congr_arg Subtype.val hφ_eq
    exact this

  have h_f₁_hwv : f₁ hwv = _tensor (r (f₁ hwv)) hwv := (hr_equiv f₁ hf₁).2
  have h_f₂_hwv : f₂ hwv = _tensor (r (f₂ hwv)) hwv := (hr_equiv f₂ hf₂).2

  have h_hwv_eq : f₁ hwv = f₂ hwv := by rw [h_f₁_hwv, h_rv, ← h_f₂_hwv]

  have h_f_eq : f₁ = f₂ := hr_unique f₁ f₂ hf₁ hf₂ h_hwv_eq
  exact Subtype.ext h_f_eq

theorem tensor_hwv_is_highest_weight
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hVerma : IsVermaModule Δ M wt)
    (N : Type*) [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (tensor : V →ₗ[R] M →ₗ[R] N)
    (_hiso : Function.Surjective (TensorProduct.lift tensor : TensorProduct R V M →ₗ[R] N))
    (v : V) (hv : v ∈ WeightSpace Δ V 0) :
    (∀ (h : Δ.𝔥), ⁅(h : 𝔤), tensor v hVerma.highestWeightVec⁆ = wt h • tensor v hVerma.highestWeightVec) ∧
    (∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), tensor v hVerma.highestWeightVec⁆ = 0) := by


  sorry

theorem tensor_hwv_injective
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hVerma : IsVermaModule Δ M wt)
    (N : Type*) [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (tensor : V →ₗ[R] M →ₗ[R] N)
    (_hiso : Function.Surjective (TensorProduct.lift tensor : TensorProduct R V M →ₗ[R] N))
    (v : V) (hv : tensor v hVerma.highestWeightVec = 0) : v = 0 := by


  sorry

theorem homEquivariant_finite
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (_hVerma : IsVermaModule Δ M wt)
    (N : Type*) [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (tensor : V →ₗ[R] M →ₗ[R] N)
    (_hiso : Function.Surjective (TensorProduct.lift tensor : TensorProduct R V M →ₗ[R] N)) :
    Module.Finite R (@HomEquivariant R _ 𝔤 _ _ M _ _ _ _ N _ _ _ _) := by


  sorry

theorem verma_universal_map_to_N
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hVerma : IsVermaModule Δ M wt)
    (N : Type*) [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (n : N)
    (hn_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), n⁆ = wt h • n)
    (hn_pos : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), n⁆ = 0) :
    ∃ (η : M →ₗ[R] N),
      (∀ (x : 𝔤) (m : M), η ⁅x, m⁆ = ⁅x, η m⁆) ∧
      η hVerma.highestWeightVec = n ∧
      (∀ (η' : M →ₗ[R] N), (∀ (x : 𝔤) (m : M), η' ⁅x, m⁆ = ⁅x, η' m⁆) →
        η' hVerma.highestWeightVec = n → η' = η) := by


  sorry

lemma prop_18_5_ge_injection
    (Δ : TriangularDecomposition R 𝔤)
    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (_hVerma : IsVermaModule Δ M wt)
    (N : Type*) [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (tensor : V →ₗ[R] M →ₗ[R] N)
    (_hiso : Function.Surjective (TensorProduct.lift tensor : TensorProduct R V M →ₗ[R] N)) :
    ∃ (φ : WeightSpace Δ V 0 →ₗ[R] @HomEquivariant R _ 𝔤 _ _ M _ _ _ _ N _ _ _ _),
      Function.Injective φ ∧
      Module.Finite R (@HomEquivariant R _ 𝔤 _ _ M _ _ _ _ N _ _ _ _) := by


  let hwv := _hVerma.highestWeightVec
  have h_univ : ∀ (v : V) (hv : v ∈ WeightSpace Δ V 0),
      ∃ (η : M →ₗ[R] N),
        (∀ (x : 𝔤) (m : M), η ⁅x, m⁆ = ⁅x, η m⁆) ∧
        η hwv = tensor v hwv ∧
        (∀ (η' : M →ₗ[R] N), (∀ (x : 𝔤) (m : M), η' ⁅x, m⁆ = ⁅x, η' m⁆) →
          η' hwv = tensor v hwv → η' = η) := by
    intro v hv
    have ⟨hwt, hpos⟩ := tensor_hwv_is_highest_weight Δ V M wt _hVerma N tensor _hiso v hv
    exact verma_universal_map_to_N Δ M wt _hVerma N (tensor v hwv) hwt hpos


  classical
  let φ : WeightSpace Δ V 0 →ₗ[R] @HomEquivariant R _ 𝔤 _ _ M _ _ _ _ N _ _ _ _ :=
    { toFun := fun ⟨v, hv⟩ => ⟨(h_univ v hv).choose, (h_univ v hv).choose_spec.1⟩
      map_add' := by
        intro ⟨a, ha⟩ ⟨b, hb⟩
        apply Subtype.ext
        have hab := (WeightSpace Δ V 0).add_mem ha hb
        have huniq := (h_univ (a + b) hab).choose_spec.2.2
        apply Eq.symm
        apply huniq
        · intro x m
          show ((h_univ a ha).choose + (h_univ b hb).choose) ⁅x, m⁆ =
            ⁅x, ((h_univ a ha).choose + (h_univ b hb).choose) m⁆
          simp only [LinearMap.add_apply,
            (h_univ a ha).choose_spec.1 x m, (h_univ b hb).choose_spec.1 x m, lie_add]
        · show ((h_univ a ha).choose + (h_univ b hb).choose) hwv = tensor (a + b) hwv
          rw [LinearMap.add_apply, (h_univ a ha).choose_spec.2.1,
            (h_univ b hb).choose_spec.2.1, ← LinearMap.add_apply, ← map_add]
      map_smul' := by
        intro c ⟨a, ha⟩
        apply Subtype.ext
        have hca := (WeightSpace Δ V 0).smul_mem c ha
        have huniq := (h_univ (c • a) hca).choose_spec.2.2
        apply Eq.symm
        apply huniq
        · intro x m
          show (c • (h_univ a ha).choose) ⁅x, m⁆ = ⁅x, (c • (h_univ a ha).choose) m⁆
          simp only [LinearMap.smul_apply,
            (h_univ a ha).choose_spec.1 x m, lie_smul]
        · show (c • (h_univ a ha).choose) hwv = tensor (c • a) hwv
          rw [LinearMap.smul_apply, (h_univ a ha).choose_spec.2.1,
            ← LinearMap.smul_apply, ← map_smul] }


  have h_inj : Function.Injective φ := by
    intro ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩ heq
    have h_map_eq : (h_univ v₁ hv₁).choose = (h_univ v₂ hv₂).choose :=
      congr_arg Subtype.val heq
    have h_ten_eq : tensor v₁ hwv = tensor v₂ hwv := by
      rw [← (h_univ v₁ hv₁).choose_spec.2.1, ← (h_univ v₂ hv₂).choose_spec.2.1, h_map_eq]
    have h_diff : tensor (v₁ - v₂) hwv = 0 := by
      simp only [map_sub, LinearMap.sub_apply, h_ten_eq, sub_self]
    exact Subtype.ext (sub_eq_zero.mp
      (tensor_hwv_injective Δ V M wt _hVerma N tensor _hiso (v₁ - v₂) h_diff))

  have h_fin := homEquivariant_finite Δ V M wt _hVerma N tensor _hiso
  exact ⟨φ, h_inj, h_fin⟩

lemma prop_18_5_ge
    (Δ : TriangularDecomposition R 𝔤)
    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (_hVerma : IsVermaModule Δ M wt)
    (N : Type*) [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (tensor : V →ₗ[R] M →ₗ[R] N)
    (_hiso : Function.Surjective (TensorProduct.lift tensor : TensorProduct R V M →ₗ[R] N)) :
    Module.finrank R (WeightSpace Δ V 0) ≤
    Module.finrank R (@HomEquivariant R _ 𝔤 _ _ M _ _ _ _ N _ _ _ _) := by
  by_cases hR : Nontrivial R
  · obtain ⟨φ, hφ_inj, hφ_fin⟩ := prop_18_5_ge_injection Δ V M wt _hVerma N tensor _hiso
    haveI := hφ_fin
    haveI := commRing_strongRankCondition R
    exact LinearMap.finrank_le_finrank_of_injective hφ_inj
  · rw [not_nontrivial_iff_subsingleton] at hR
    haveI : Subsingleton R := hR
    haveI := Module.subsingleton R (WeightSpace Δ V 0)
    haveI := Module.subsingleton R (@HomEquivariant R _ 𝔤 _ _ M _ _ _ _ N _ _ _ _)
    simp

lemma prop_18_5_le
    (Δ : TriangularDecomposition R 𝔤)
    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (_hVerma : IsVermaModule Δ M wt)
    (N : Type*) [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (tensor : V →ₗ[R] M →ₗ[R] N)
    (_hiso : Function.Surjective (TensorProduct.lift tensor : TensorProduct R V M →ₗ[R] N))
    [IsNoetherianRing R] :
    Module.finrank R (@HomEquivariant R _ 𝔤 _ _ M _ _ _ _ N _ _ _ _) ≤
    Module.finrank R (WeightSpace Δ V 0) := by

  obtain ⟨φ, hφ_inj⟩ := prop_18_5_restriction_injective Δ V M wt _hVerma N tensor _hiso

  by_cases hR : Nontrivial R
  ·
    haveI := hR


    haveI : IsNoetherian R V := isNoetherian_of_isNoetherianRing_of_finite R V
    haveI : Module.Finite R ↥(WeightSpace Δ V 0) := inferInstance
    exact LinearMap.finrank_le_finrank_of_injective hφ_inj
  ·
    rw [not_nontrivial_iff_subsingleton] at hR
    haveI := hR
    simp

theorem proposition_18_5
    (Δ : TriangularDecomposition R 𝔤)
    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hVerma : IsVermaModule Δ M wt)

    (N : Type*) [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]

    (tensor : V →ₗ[R] M →ₗ[R] N)
    (hiso : Function.Surjective (TensorProduct.lift tensor : TensorProduct R V M →ₗ[R] N))
    [IsNoetherianRing R] :
    Module.finrank R (@HomEquivariant R _ 𝔤 _ _ M _ _ _ _ N _ _ _ _ ) =
    Module.finrank R (WeightSpace Δ V 0) := by

  apply le_antisymm
  ·


    exact prop_18_5_le Δ V M wt hVerma N tensor hiso
  ·

    exact prop_18_5_ge Δ V M wt hVerma N tensor hiso

lemma exercise_18_4_equivariant_finrank
    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V]
    [Module.Finite R 𝔤]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (N : Type*) [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N] :
    Module.finrank R (HomAdEquivariant V (HomFinBimodule (R := R) (𝔤 := 𝔤) M N)) =
    Module.finrank R (@HomEquivariant R _ 𝔤 _ _ M _ _ _ _ (TensorProduct R V N) _ _ _ _) := by


  sorry

def ueaActionFromLieModule
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M :=
  UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R 𝔤 M)

theorem ueaActionFromLieModule_compat
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (x : 𝔤) (m : M) :
    ueaActionFromLieModule M (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆ := by
  simp [ueaActionFromLieModule, LieModule.toEnd_apply_apply]

theorem center_scalar_eq_evalHC (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hHW : IsHighestWeightModule Δ M wt)
    (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))
    (c : R)
    (hscal : ∀ (m : M), (ueaActionFromLieModule M) (z : UniversalEnvelopingAlgebra R 𝔤) m = c • m) :
    c = (evalHC Δ wg (wt + wg.ρ)) z := by


  sorry

def vermaHasInfinitesimalCharacter (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R) (hVerma : IsVermaModule Δ M wt) :
    HasInfinitesimalCharacter (R := R) (𝔤 := 𝔤) M (evalHC Δ wg (wt + wg.ρ)) where
  ueaAction := ueaActionFromLieModule M
  compat := ueaActionFromLieModule_compat M
  center_acts_by_scalar := by
    intro z m

    obtain ⟨c, hc⟩ := center_acts_by_scalar_on_hwm Δ wg M wt
      hVerma.toIsHighestWeightModule (ueaActionFromLieModule M)
      (ueaActionFromLieModule_compat M) z

    have c_eq : c = (evalHC Δ wg (wt + wg.ρ)) z :=
      center_scalar_eq_evalHC Δ wg M wt hVerma.toIsHighestWeightModule z c hc

    rw [hc m, c_eq]

theorem actionHom_image_in_HomFin [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R) (_hVerma : IsVermaModule Δ M wt)
    (act : MaximalQuotient (evalHC Δ wg (wt + wg.ρ)) →ₐ[R] Module.End R M)
    (hcompat_act : ∀ (y : 𝔤) (m : M),
      act (MaximalQuotient.proj (evalHC Δ wg (wt + wg.ρ))
        (UniversalEnvelopingAlgebra.ι R y)) m = ⁅y, m⁆)
    (q : MaximalQuotient (evalHC Δ wg (wt + wg.ρ))) :
    (act q : M →ₗ[R] M) ∈ @HomFin R _ 𝔤 _ _ M M _ _ _ _ _ _ _ _ := by


  let χ := evalHC Δ wg (wt + wg.ρ)
  let proj := MaximalQuotient.proj χ
  let actUEA := act.comp proj
  show IsFiniteTypeMap (𝔤 := 𝔤) M M (act q)

  suffices h : ∀ (u : UniversalEnvelopingAlgebra R 𝔤),
      IsFiniteTypeMap (𝔤 := 𝔤) M M (actUEA u) by

    revert q; intro q
    exact Quot.inductionOn q (fun u => h u)
  intro u

  obtain ⟨S, hfin, hu_mem, hstab⟩ := ueaAdLocallyFinite (R := R) (𝔤 := 𝔤) u

  let imgS := S.map actUEA.toLinearMap
  refine ⟨imgS, ?_, ?_, ?_⟩
  ·
    exact Module.Finite.map S actUEA.toLinearMap
  ·
    exact Submodule.mem_map_of_mem hu_mem
  ·
    intro x f hf
    obtain ⟨v, hv_mem, hv_eq⟩ := Submodule.mem_map.mp hf
    subst hv_eq

    show adjointActionOnHom M M x (actUEA v) ∈ imgS

    have hcompat_uea : ∀ (y : 𝔤) (m : M),
        actUEA (UniversalEnvelopingAlgebra.ι R y) m = ⁅y, m⁆ := hcompat_act
    rw [ueaAction_adjoint_intertwine M actUEA hcompat_uea x v]

    exact Submodule.mem_map_of_mem (hstab x v hv_mem)


def actionHom [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hVerma : IsVermaModule Δ M wt) :
    MaximalQuotient (evalHC Δ wg (wt + wg.ρ)) →ₗ[R] (@HomFin R _ 𝔤 _ _ M M _ _ _ _ _ _ _ _) :=
  let χ := evalHC Δ wg (wt + wg.ρ)
  let hic := vermaHasInfinitesimalCharacter Δ wg M wt hVerma
  let ft := MaximalQuotient.factors_through χ M hic
  let act := ft.choose
  have hact_spec := ft.choose_spec
  have hcompat_act : ∀ (y : 𝔤) (m : M),
      act (MaximalQuotient.proj χ (UniversalEnvelopingAlgebra.ι R y)) m = ⁅y, m⁆ := by
    intro y m
    rw [← hact_spec (UniversalEnvelopingAlgebra.ι R y) m]
    exact hic.compat y m
  { toFun := fun q => ⟨act q, actionHom_image_in_HomFin Δ wg M wt hVerma act hcompat_act q⟩
    map_add' := fun q₁ q₂ => by
      ext m
      simp [map_add, LinearMap.add_apply]
    map_smul' := fun r q => by
      ext m
      simp [map_smul, LinearMap.smul_apply] }


def ueaIncl_neg (Δ : TriangularDecomposition R 𝔤) :
    UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg →ₐ[R] UniversalEnvelopingAlgebra R 𝔤 :=
  UniversalEnvelopingAlgebra.lift R
    ((UniversalEnvelopingAlgebra.ι R).comp (Δ.𝔫_neg.incl : Δ.𝔫_neg →ₗ⁅R⁆ 𝔤))

def ueaIncl_pos (Δ : TriangularDecomposition R 𝔤) :
    UniversalEnvelopingAlgebra R ↥Δ.𝔫_pos →ₐ[R] UniversalEnvelopingAlgebra R 𝔤 :=
  UniversalEnvelopingAlgebra.lift R
    ((UniversalEnvelopingAlgebra.ι R).comp (Δ.𝔫_pos.incl : Δ.𝔫_pos →ₗ⁅R⁆ 𝔤))

noncomputable def multMap_xi
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (wt : Δ.𝔥 →ₗ[R] R) :
    TensorProduct R (UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg)
      (UniversalEnvelopingAlgebra R ↥Δ.𝔫_pos) →ₗ[R]
    MaximalQuotient (evalHC Δ wg (wt + wg.ρ)) :=
  TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun b =>
            MaximalQuotient.proj (evalHC Δ wg (wt + wg.ρ))
              (ueaIncl_neg Δ a * ueaIncl_pos Δ b)
          map_add' := fun b₁ b₂ => by simp [mul_add, map_add]
          map_smul' := fun r b => by simp [map_smul] }
      map_add' := fun a₁ a₂ => by ext b; simp [add_mul, map_add]
      map_smul' := fun r a => by ext b; simp [map_smul] }

noncomputable def multMap_ug
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) :
    TensorProduct R (UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg)
      (UniversalEnvelopingAlgebra R ↥Δ.𝔫_pos) →ₗ[R]
    UniversalEnvelopingAlgebra R 𝔤 :=
  TensorProduct.lift
    { toFun := fun a =>
        { toFun := fun b => ueaIncl_neg Δ a * ueaIncl_pos Δ b
          map_add' := fun b₁ b₂ => by simp [mul_add]
          map_smul' := fun r b => by simp }
      map_add' := fun a₁ a₂ => by ext b; simp [add_mul]
      map_smul' := fun r a => by ext b; simp }

lemma multMap_xi_eq_proj_comp_multMap_ug
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (wt : Δ.𝔥 →ₗ[R] R)
    (x : TensorProduct R (UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg)
      (UniversalEnvelopingAlgebra R ↥Δ.𝔫_pos)) :
    multMap_xi Δ wg wt x =
      MaximalQuotient.proj (evalHC Δ wg (wt + wg.ρ)) (multMap_ug Δ x) := by

  induction x using TensorProduct.induction_on with
  | zero => simp [map_zero]
  | tmul a b =>
    simp only [multMap_xi, multMap_ug, TensorProduct.lift.tmul, LinearMap.coe_mk,
      AddHom.coe_mk]
  | add x y hx hy =>
    simp only [map_add, hx, hy]

theorem shapovalov_ueaAction_multMap_ug_ne_zero
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R) (hVerma : IsVermaModule Δ M wt)
    (x : TensorProduct R (UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg)
      (UniversalEnvelopingAlgebra R ↥Δ.𝔫_pos))
    (hx : x ≠ 0) :
    let hic := vermaHasInfinitesimalCharacter Δ wg M wt hVerma
    hic.ueaAction (multMap_ug Δ x) ≠ 0 := by


  sorry

theorem shapovalov_nondeg_act_ne_zero
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R) (hVerma : IsVermaModule Δ M wt)
    (x : TensorProduct R (UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg)
      (UniversalEnvelopingAlgebra R ↥Δ.𝔫_pos))
    (hx : x ≠ 0) :
    let χ := evalHC Δ wg (wt + wg.ρ)
    let hic := vermaHasInfinitesimalCharacter Δ wg M wt hVerma
    let act := (MaximalQuotient.factors_through χ M hic).choose
    act (multMap_xi Δ wg wt x) ≠ 0 := by

  intro χ hic act

  have h_uea_ne := shapovalov_ueaAction_multMap_ug_ne_zero Δ wg M wt hVerma x hx
  simp only at h_uea_ne

  have hact_spec := (MaximalQuotient.factors_through
    (evalHC Δ wg (wt + wg.ρ)) M hic).choose_spec


  rw [multMap_xi_eq_proj_comp_multMap_ug Δ wg wt x]


  suffices heq : act (MaximalQuotient.proj (evalHC Δ wg (wt + wg.ρ)) (multMap_ug Δ x)) =
      hic.ueaAction (multMap_ug Δ x) by
    rwa [heq]
  ext m
  rw [← hact_spec (multMap_ug Δ x) m]

theorem shapovalov_composition_injective
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R) (hVerma : IsVermaModule Δ M wt) :
    let χ := evalHC Δ wg (wt + wg.ρ)
    let hic := vermaHasInfinitesimalCharacter Δ wg M wt hVerma
    let act := (MaximalQuotient.factors_through χ M hic).choose
    Function.Injective (fun x =>
      act (multMap_xi Δ wg wt x)) := by

  intro χ hic act x₁ x₂ heq

  by_contra hne
  have hd : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr hne

  have h_ne := shapovalov_nondeg_act_ne_zero Δ wg M wt hVerma (x₁ - x₂) hd

  simp only at h_ne
  apply h_ne

  rw [map_sub (multMap_xi Δ wg wt), map_sub]

  exact sub_eq_zero.mpr heq

def ueaIncl_h (Δ : TriangularDecomposition R 𝔤) :
    UniversalEnvelopingAlgebra R ↥Δ.𝔥 →ₐ[R] UniversalEnvelopingAlgebra R 𝔤 :=
  UniversalEnvelopingAlgebra.lift R
    ((UniversalEnvelopingAlgebra.ι R).comp (Δ.𝔥.incl : Δ.𝔥 →ₗ⁅R⁆ 𝔤))

theorem pbw_triangular_iso_tmul
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (a : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg)
    (h : UniversalEnvelopingAlgebra R ↥Δ.𝔥)
    (b : UniversalEnvelopingAlgebra R ↥Δ.𝔫_pos) :
    pbw_triangular_iso R 𝔤 Δ (a ⊗ₜ[R] (h ⊗ₜ[R] b)) =
      ueaIncl_neg Δ a * ueaIncl_h Δ h * ueaIncl_pos Δ b := by


  sorry

theorem hc_cartan_acts_scalar_in_quotient
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (wt : Δ.𝔥 →ₗ[R] R)
    (a : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg)
    (h : UniversalEnvelopingAlgebra R ↥Δ.𝔥)
    (b : UniversalEnvelopingAlgebra R ↥Δ.𝔫_pos) :
    ∃ (s : TensorProduct R (UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg)
             (UniversalEnvelopingAlgebra R ↥Δ.𝔫_pos)),
      multMap_xi Δ wg wt s =
        MaximalQuotient.proj (evalHC Δ wg (wt + wg.ρ))
          (ueaIncl_neg Δ a * ueaIncl_h Δ h * ueaIncl_pos Δ b) := by


  sorry

theorem pbw_proj_pure
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (wt : Δ.𝔥 →ₗ[R] R)
    (a : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg)
    (h : UniversalEnvelopingAlgebra R ↥Δ.𝔥)
    (b : UniversalEnvelopingAlgebra R ↥Δ.𝔫_pos) :
    ∃ (s : TensorProduct R (UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg)
             (UniversalEnvelopingAlgebra R ↥Δ.𝔫_pos)),
      multMap_xi Δ wg wt s =
        MaximalQuotient.proj (evalHC Δ wg (wt + wg.ρ))
          (pbw_triangular_iso R 𝔤 Δ (a ⊗ₜ[R] (h ⊗ₜ[R] b))) := by
  rw [pbw_triangular_iso_tmul]
  exact hc_cartan_acts_scalar_in_quotient Δ wg wt a h b

theorem pbw_proj_factors_through_multMap_xi
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (wt : Δ.𝔥 →ₗ[R] R)
    (t : TensorProduct R (UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg)
      (TensorProduct R (UniversalEnvelopingAlgebra R ↥Δ.𝔥)
                       (UniversalEnvelopingAlgebra R ↥Δ.𝔫_pos))) :
    ∃ (s : TensorProduct R (UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg)
             (UniversalEnvelopingAlgebra R ↥Δ.𝔫_pos)),
      multMap_xi Δ wg wt s =
        MaximalQuotient.proj (evalHC Δ wg (wt + wg.ρ))
          (pbw_triangular_iso R 𝔤 Δ t) := by

  induction t using TensorProduct.induction_on with
  | zero =>
    exact ⟨0, by simp [map_zero]⟩
  | tmul a w =>

    induction w using TensorProduct.induction_on with
    | zero =>
      exact ⟨0, by simp [TensorProduct.tmul_zero, map_zero]⟩
    | tmul h b =>
      exact pbw_proj_pure Δ wg wt a h b
    | add x y ihx ihy =>
      obtain ⟨sx, hsx⟩ := ihx
      obtain ⟨sy, hsy⟩ := ihy
      refine ⟨sx + sy, ?_⟩
      rw [map_add, TensorProduct.tmul_add, map_add, map_add, hsx, hsy]
  | add x y ihx ihy =>
    obtain ⟨sx, hsx⟩ := ihx
    obtain ⟨sy, hsy⟩ := ihy
    refine ⟨sx + sy, ?_⟩
    rw [map_add, map_add, map_add, hsx, hsy]

theorem multMap_xi_surjective
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (wt : Δ.𝔥 →ₗ[R] R) :
    Function.Surjective (multMap_xi Δ wg wt) := by


  let χ := evalHC Δ wg (wt + wg.ρ)
  intro q

  have hsurj : Function.Surjective (MaximalQuotient.proj χ) :=
    RingCon.mk'_surjective _
  obtain ⟨u, hu⟩ := hsurj q

  obtain ⟨s, hs⟩ := pbw_proj_factors_through_multMap_xi Δ wg wt
    ((pbw_triangular_iso R 𝔤 Δ).symm u)

  exact ⟨s, by rw [hs, LinearEquiv.apply_symm_apply]; exact hu⟩

theorem nilpotent_cone_domain_contradiction
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R) (hVerma : IsVermaModule Δ M wt)
    (h_xi_inj : let χ := evalHC Δ wg (wt + wg.ρ)
      let hic := vermaHasInfinitesimalCharacter Δ wg M wt hVerma
      let act := (MaximalQuotient.factors_through χ M hic).choose
      Function.Injective (fun x => act (multMap_xi Δ wg wt x))) :
    let χ := evalHC Δ wg (wt + wg.ρ)
    let hic := vermaHasInfinitesimalCharacter Δ wg M wt hVerma
    let act := (MaximalQuotient.factors_through χ M hic).choose
    Function.Injective act := by

  have h_surj := multMap_xi_surjective Δ wg wt

  exact h_xi_inj.of_comp_right h_surj

theorem shapovalov_nondeg_annihilator_axiom
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R) (hVerma : IsVermaModule Δ M wt)
    (u : UniversalEnvelopingAlgebra R 𝔤)
    (hzero : ∀ m : M, (vermaHasInfinitesimalCharacter Δ wg M wt hVerma).ueaAction u m = 0) :
    MaximalQuotient.proj (evalHC Δ wg (wt + wg.ρ)) u = 0 := by

  let χ := evalHC Δ wg (wt + wg.ρ)
  let hic := vermaHasInfinitesimalCharacter Δ wg M wt hVerma
  let ft := MaximalQuotient.factors_through χ M hic
  let act := ft.choose
  have hact_spec := ft.choose_spec

  have h_act_zero : act (MaximalQuotient.proj χ u) = 0 := by
    ext m
    simp only [LinearMap.zero_apply]
    rw [← hact_spec u m]
    exact hzero m

  have h_xi_inj := shapovalov_composition_injective Δ wg M wt hVerma

  have h_act_inj := nilpotent_cone_domain_contradiction Δ wg M wt hVerma h_xi_inj


  have h_act_zero' : act (MaximalQuotient.proj χ u) = act 0 := by
    rw [h_act_zero, map_zero]
  exact h_act_inj h_act_zero'

theorem shapovalov_pbw_injectivity
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R) (hVerma : IsVermaModule Δ M wt) :
    let χ := evalHC Δ wg (wt + wg.ρ)
    let hic := vermaHasInfinitesimalCharacter Δ wg M wt hVerma
    Function.Injective (MaximalQuotient.factors_through χ M hic).choose := by

  let χ := evalHC Δ wg (wt + wg.ρ)
  let hic := vermaHasInfinitesimalCharacter Δ wg M wt hVerma
  let ft := MaximalQuotient.factors_through χ M hic
  let act := ft.choose
  have hact_spec := ft.choose_spec

  have hsurj : Function.Surjective (MaximalQuotient.proj χ) :=
    RingCon.mk'_surjective _

  show Function.Injective act
  intro q₁ q₂ heq

  obtain ⟨u₁, hu₁⟩ := hsurj q₁
  obtain ⟨u₂, hu₂⟩ := hsurj q₂

  have hann : ∀ m : M, hic.ueaAction (u₁ - u₂) m = 0 := by
    intro m
    have h1 := hact_spec u₁ m
    have h2 := hact_spec u₂ m
    rw [hu₁] at h1; rw [hu₂] at h2


    simp only [map_sub, LinearMap.sub_apply]
    rw [h1, h2]
    exact sub_eq_zero.mpr (congr_fun (congr_arg DFunLike.coe heq) m)

  have hproj_zero : MaximalQuotient.proj χ (u₁ - u₂) = 0 :=
    shapovalov_nondeg_annihilator_axiom Δ wg M wt hVerma (u₁ - u₂) hann

  rw [map_sub] at hproj_zero

  rw [← hu₁, ← hu₂]
  exact sub_eq_zero.mp hproj_zero

theorem verma_factoredAction_injective
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R) (hVerma : IsVermaModule Δ M wt) :
    let χ := evalHC Δ wg (wt + wg.ρ)
    let hic := vermaHasInfinitesimalCharacter Δ wg M wt hVerma
    Function.Injective (MaximalQuotient.factors_through χ M hic).choose :=
  shapovalov_pbw_injectivity Δ wg M wt hVerma

theorem verma_ueaAction_zero_implies_proj_zero
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R) (hVerma : IsVermaModule Δ M wt)
    (u : UniversalEnvelopingAlgebra R 𝔤)
    (hzero : (vermaHasInfinitesimalCharacter Δ wg M wt hVerma).ueaAction u = 0) :
    MaximalQuotient.proj (evalHC Δ wg (wt + wg.ρ)) u = 0 := by
  let χ := evalHC Δ wg (wt + wg.ρ)
  let hic := vermaHasInfinitesimalCharacter Δ wg M wt hVerma

  let ft := MaximalQuotient.factors_through χ M hic
  let act := ft.choose
  have hact_spec := ft.choose_spec

  have hact_proj_zero : act (MaximalQuotient.proj χ u) = 0 := by
    ext m
    have := hact_spec u m
    rw [show (hic.ueaAction u) m = 0 from congr_fun (congr_arg DFunLike.coe hzero) m] at this
    exact this.symm

  have hinj := verma_factoredAction_injective Δ wg M wt hVerma
  have h0 : act (0 : MaximalQuotient χ) = 0 := map_zero act
  exact hinj (hact_proj_zero.trans h0.symm)

theorem verma_ueaAction_injective (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R) (hVerma : IsVermaModule Δ M wt)
    (act : MaximalQuotient (evalHC Δ wg (wt + wg.ρ)) →ₐ[R] Module.End R M)
    (hact : ∀ (u : UniversalEnvelopingAlgebra R 𝔤) (m : M),
      (vermaHasInfinitesimalCharacter Δ wg M wt hVerma).ueaAction u m =
        act (MaximalQuotient.proj (evalHC Δ wg (wt + wg.ρ)) u) m) :
    Function.Injective act := by
  let χ := evalHC Δ wg (wt + wg.ρ)
  let hic := vermaHasInfinitesimalCharacter Δ wg M wt hVerma

  intro q₁ q₂ heq

  have hsurj : Function.Surjective (MaximalQuotient.proj χ) :=
    RingCon.mk'_surjective _
  obtain ⟨u₁, hu₁⟩ := hsurj q₁
  obtain ⟨u₂, hu₂⟩ := hsurj q₂

  have hact_diff : hic.ueaAction (u₁ - u₂) = 0 := by
    ext m
    simp only [map_sub, LinearMap.sub_apply, LinearMap.zero_apply]
    have h1 := hact u₁ m
    have h2 := hact u₂ m
    rw [hu₁] at h1; rw [hu₂] at h2
    rw [h1, h2]
    exact sub_eq_zero.mpr (congr_fun (congr_arg DFunLike.coe heq) m)

  have hproj_zero := verma_ueaAction_zero_implies_proj_zero Δ wg M wt hVerma (u₁ - u₂) hact_diff

  rw [map_sub] at hproj_zero
  rw [← hu₁, ← hu₂]
  exact sub_eq_zero.mp hproj_zero

theorem proposition_18_7 [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hVerma : IsVermaModule Δ M wt) :
    Function.Injective (actionHom Δ wg M wt hVerma) := by

  let χ := evalHC Δ wg (wt + wg.ρ)
  let hic := vermaHasInfinitesimalCharacter Δ wg M wt hVerma
  let ft := MaximalQuotient.factors_through χ M hic
  let act := ft.choose
  have hact_spec := ft.choose_spec


  intro q₁ q₂ heq
  have heq_act : act q₁ = act q₂ := Subtype.ext_iff.mp heq


  have h_xi_inj := shapovalov_composition_injective Δ wg M wt hVerma

  have h_act_inj := nilpotent_cone_domain_contradiction Δ wg M wt hVerma h_xi_inj

  exact h_act_inj heq_act

theorem ueaAction_surjective_onto_HomFin
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hVerma : IsVermaModule Δ M wt)
    (f : @HomFin R _ 𝔤 _ _ M M _ _ _ _ _ _ _ _) :
    ∃ u : UniversalEnvelopingAlgebra R 𝔤,
      (vermaHasInfinitesimalCharacter Δ wg M wt hVerma).ueaAction u = (f : M →ₗ[R] M) := by


  sorry

theorem kostant_actionHom_surjective
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hVerma : IsVermaModule Δ M wt) :
    Function.Surjective (actionHom Δ wg M wt hVerma) := by
  intro f

  obtain ⟨u, hu⟩ := ueaAction_surjective_onto_HomFin Δ wg M wt hVerma f

  let χ := evalHC Δ wg (wt + wg.ρ)
  let hic := vermaHasInfinitesimalCharacter Δ wg M wt hVerma
  let ft := MaximalQuotient.factors_through χ M hic
  let act := ft.choose
  have hact_spec := ft.choose_spec
  refine ⟨MaximalQuotient.proj χ u, ?_⟩


  ext m
  show (act (MaximalQuotient.proj χ u) : M →ₗ[R] M) m = (f : M →ₗ[R] M) m
  rw [← hu]
  exact (hact_spec u m).symm

theorem actionHom_surjective [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hVerma : IsVermaModule Δ M wt) :
    Function.Surjective (actionHom Δ wg M wt hVerma) :=
  kostant_actionHom_surjective Δ wg M wt hVerma

theorem actionHom_linearEquiv_of_dimension_argument [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hVerma : IsVermaModule Δ M wt)
    (hinj : Function.Injective (actionHom Δ wg M wt hVerma)) :
    ∃ (e : MaximalQuotient (evalHC Δ wg (wt + wg.ρ)) ≃ₗ[R]
        (@HomFin R _ 𝔤 _ _ M M _ _ _ _ _ _ _ _)),
      (e : MaximalQuotient (evalHC Δ wg (wt + wg.ρ)) →ₗ[R]
        (@HomFin R _ 𝔤 _ _ M M _ _ _ _ _ _ _ _)) = actionHom Δ wg M wt hVerma := by
  have hsurj : Function.Surjective (actionHom Δ wg M wt hVerma) :=
    actionHom_surjective Δ wg M wt hVerma
  exact ⟨LinearEquiv.ofBijective (actionHom Δ wg M wt hVerma) ⟨hinj, hsurj⟩,
         LinearMap.ext (fun x => rfl)⟩

theorem corollary_18_8 [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hVerma : IsVermaModule Δ M wt) :
    Function.Bijective (actionHom Δ wg M wt hVerma) := by


  exact ⟨proposition_18_7 Δ wg M wt hVerma, actionHom_surjective Δ wg M wt hVerma⟩

def dufloJosephIso [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hVerma : IsVermaModule Δ M wt) :
    MaximalQuotient (evalHC Δ wg (wt + wg.ρ)) ≃ₗ[R]
    (@HomFin R _ 𝔤 _ _ M M _ _ _ _ _ _ _ _) :=
  LinearEquiv.ofBijective (actionHom Δ wg M wt hVerma)
    (corollary_18_8 Δ wg M wt hVerma)


lemma isFiniteTypeMap_comp_mk_tensor
    {M N : Type*} [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (V : Type*) [AddCommGroup V] [Module R V] [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [Module.Finite R V]
    (v : V) (T : M →ₗ[R] N) (hT : IsFiniteTypeMap (𝔤 := 𝔤) M N T) :
    IsFiniteTypeMap (𝔤 := 𝔤) M (TensorProduct R V N)
      ((TensorProduct.mk R V N v).comp T) := by

  obtain ⟨S, hfin, hT_mem, hstab⟩ := hT

  let Φ : TensorProduct R V S →ₗ[R] (M →ₗ[R] TensorProduct R V N) :=
    TensorProduct.lift
      { toFun := fun w =>
          { toFun := fun g => (TensorProduct.mk R V N w).comp (g : M →ₗ[R] N)
            map_add' := fun g₁ g₂ => by ext m; simp [LinearMap.comp_apply, map_add]
            map_smul' := fun r g => by ext m; simp [LinearMap.comp_apply, map_smul] }
        map_add' := fun w₁ w₂ => by
          ext g : 1; ext m; simp [TensorProduct.mk]
        map_smul' := fun r w => by
          ext g : 1; ext m; simp [TensorProduct.mk, TensorProduct.smul_tmul'] }

  have hΦ_tmul : ∀ (w : V) (g : S), Φ (w ⊗ₜ[R] g) = (TensorProduct.mk R V N w).comp (g : M →ₗ[R] N) := by
    intro w g; simp [Φ, TensorProduct.lift.tmul]

  let S' : Submodule R (M →ₗ[R] TensorProduct R V N) := LinearMap.range Φ

  haveI : Module.Finite R (TensorProduct R V S) := Module.Finite.tensorProduct R V S
  haveI : Module.Finite R S' := Module.Finite.range Φ
  refine ⟨S', inferInstance, ?_, ?_⟩
  ·
    exact ⟨v ⊗ₜ[R] ⟨T, hT_mem⟩, hΦ_tmul v ⟨T, hT_mem⟩⟩
  ·
    intro x f hf

    obtain ⟨z, rfl⟩ := hf

    induction z using TensorProduct.induction_on with
    | zero =>
      simp only [map_zero]
      have : adjointActionOnHom (R := R) (𝔤 := 𝔤) M (TensorProduct R V N) x 0 = 0 := by
        ext m; simp [adjointActionOnHom]
      rw [this]; exact zero_mem _
    | tmul w g =>


      have key : adjointActionOnHom M (TensorProduct R V N) x
            ((TensorProduct.mk R V N w).comp (g : M →ₗ[R] N)) =
          (TensorProduct.mk R V N ⁅x, w⁆).comp (g : M →ₗ[R] N) +
          (TensorProduct.mk R V N w).comp (adjointActionOnHom M N x (g : M →ₗ[R] N)) := by
        ext m
        simp only [adjointActionOnHom, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
          TensorProduct.mk_apply, LinearMap.add_apply]
        rw [TensorProduct.LieModule.lie_tmul_right]
        rw [add_sub_assoc]
        congr 1
        rw [← TensorProduct.tmul_sub]
      rw [hΦ_tmul, key]
      have hg_stab : adjointActionOnHom M N x (g : M →ₗ[R] N) ∈ S :=
        hstab x g g.property
      exact ⟨⁅x, w⁆ ⊗ₜ[R] g + w ⊗ₜ[R] ⟨adjointActionOnHom M N x (g : M →ₗ[R] N), hg_stab⟩, by
        rw [map_add, hΦ_tmul, hΦ_tmul]⟩
    | add z₁ z₂ ih₁ ih₂ =>

      have hadj_add : adjointActionOnHom M (TensorProduct R V N) x (Φ (z₁ + z₂)) =
          adjointActionOnHom M (TensorProduct R V N) x (Φ z₁) +
          adjointActionOnHom M (TensorProduct R V N) x (Φ z₂) := by
        simp only [map_add]
        ext m; simp [adjointActionOnHom, lie_add, sub_add_sub_comm]
      rw [hadj_add]
      exact Submodule.add_mem S' ih₁ ih₂

def tensorActionMap [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hVerma : IsVermaModule Δ M wt) :
    TensorProduct R V (MaximalQuotient (evalHC Δ wg (wt + wg.ρ))) →ₗ[R]
    (HomFin (R := R) (𝔤 := 𝔤) M (TensorProduct R V M)) :=


  let φ := actionHom Δ wg M wt hVerma
  TensorProduct.lift
    { toFun := fun v =>
        { toFun := fun u =>
            ⟨(TensorProduct.mk R V M v).comp ((φ u) : M →ₗ[R] M),
             isFiniteTypeMap_comp_mk_tensor V v ((φ u) : M →ₗ[R] M) (φ u).property⟩
          map_add' := fun u₁ u₂ => by
            apply Subtype.ext
            ext m
            simp [map_add]
          map_smul' := fun r u => by
            apply Subtype.ext
            simp only [SetLike.val_smul]
            ext m
            simp [map_smul] }
      map_add' := fun v₁ v₂ => by
        ext u : 1
        exact Subtype.ext (by ext m; simp [TensorProduct.mk])
      map_smul' := fun r v => by
        ext u : 1
        exact Subtype.ext (by ext m; simp [TensorProduct.mk, TensorProduct.smul_tmul']) }

def tensorHomMap
    (V : Type*) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V] [Module.Finite R V]
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    TensorProduct R V (HomFin (R := R) (𝔤 := 𝔤) M M) →ₗ[R]
      HomFin (R := R) (𝔤 := 𝔤) M (TensorProduct R V M) :=
  TensorProduct.lift
    { toFun := fun v =>
        { toFun := fun f =>
            ⟨(TensorProduct.mk R V M v).comp (f : M →ₗ[R] M),
             isFiniteTypeMap_comp_mk_tensor V v (f : M →ₗ[R] M) f.property⟩
          map_add' := fun f₁ f₂ => by
            apply Subtype.ext; ext m; simp [map_add]
          map_smul' := fun r f => by
            apply Subtype.ext; simp only [SetLike.val_smul]; ext m; simp [map_smul] }
      map_add' := fun v₁ v₂ => by
        ext f : 1; exact Subtype.ext (by ext m; simp [TensorProduct.mk])
      map_smul' := fun r v => by
        ext f : 1
        exact Subtype.ext (by ext m; simp [TensorProduct.mk, TensorProduct.smul_tmul']) }


theorem tensorHomMap_bijective
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    Function.Bijective (tensorHomMap (R := R) (𝔤 := 𝔤) V M) := by
  apply proposition_18_3_bijective_ax (N := M) (VN := TensorProduct R V M)
    (tensor_VN := TensorProduct.mk R V M)
  ·
    rw [TensorProduct.lift_mk]
    exact Function.bijective_id
  ·
    intro f v m
    rfl

theorem corollary_18_9 [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hVerma : IsVermaModule Δ M wt) :
    Function.Bijective (tensorActionMap Δ wg V M wt hVerma) := by

  have hφ_bij : Function.Bijective (actionHom Δ wg M wt hVerma) :=
    corollary_18_8 Δ wg M wt hVerma

  have hΨ_bij : Function.Bijective (tensorHomMap (R := R) (𝔤 := 𝔤) V M) :=
    tensorHomMap_bijective V M

  let idV_tensor_φ : TensorProduct R V (MaximalQuotient (evalHC Δ wg (wt + wg.ρ))) →ₗ[R]
      TensorProduct R V (HomFin (R := R) (𝔤 := 𝔤) M M) :=
    TensorProduct.map LinearMap.id (actionHom Δ wg M wt hVerma)
  have h_tensor_bij : Function.Bijective idV_tensor_φ :=
    TensorProduct.map_bijective Function.bijective_id hφ_bij

  have h_factor : ∀ x, tensorActionMap Δ wg V M wt hVerma x =
      tensorHomMap (R := R) (𝔤 := 𝔤) V M (idV_tensor_φ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp [map_zero]
    | tmul v u =>
      apply Subtype.ext
      ext m
      simp [tensorActionMap, idV_tensor_φ, tensorHomMap, TensorProduct.lift.tmul,
        TensorProduct.map]
    | add x y hx hy => simp [map_add, hx, hy]

  have h_eq : ⇑(tensorActionMap Δ wg V M wt hVerma) =
      ⇑(tensorHomMap (R := R) (𝔤 := 𝔤) V M) ∘ ⇑idV_tensor_φ :=
    funext h_factor
  rw [h_eq]
  exact hΨ_bij.comp h_tensor_bij

def corollary_18_9_iso [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (wt : Δ.𝔥 →ₗ[R] R)
    (hVerma : IsVermaModule Δ M wt) :
    TensorProduct R V (MaximalQuotient (evalHC Δ wg (wt + wg.ρ))) ≃ₗ[R]
    (HomFin (R := R) (𝔤 := 𝔤) M (TensorProduct R V M)) :=
  LinearEquiv.ofBijective (tensorActionMap Δ wg V M wt hVerma)
    (corollary_18_9 Δ wg V M wt hVerma)

def leftInfChars
    (M : LieBimodule R 𝔤) :
    Set (↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :=
  { θ | ∃ (m : M.carrier), m ≠ 0 ∧
    ∀ (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)),
      M.leftAction (z : UniversalEnvelopingAlgebra R 𝔤) m = θ z • m }


theorem corollary_18_9_leftInfChars_subset
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (lam : Δ.𝔥 →ₗ[R] R) :
    leftInfChars (tensorBimodule (LieBimodule.trivial V) (evalHC Δ wg lam)) ⊆
    { θ | ∃ (ν : Δ.𝔥 →ₗ[R] R), ν ∈ weights Δ V ∧
      θ = evalHC Δ wg (lam + ν) } := by


  sorry

theorem corollary_18_9_leftInfChars_supset
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (lam : Δ.𝔥 →ₗ[R] R) :
    { θ | ∃ (ν : Δ.𝔥 →ₗ[R] R), ν ∈ weights Δ V ∧
      θ = evalHC Δ wg (lam + ν) } ⊆
    leftInfChars (tensorBimodule (LieBimodule.trivial V) (evalHC Δ wg lam)) := by


  sorry

theorem corollary_18_10_i [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)

    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (lam : Δ.𝔥 →ₗ[R] R) :
    leftInfChars (tensorBimodule (LieBimodule.trivial V) (evalHC Δ wg lam)) =
    { θ | ∃ (ν : Δ.𝔥 →ₗ[R] R), ν ∈ weights Δ V ∧
      θ = evalHC Δ wg (lam + ν) } :=
  Set.eq_of_subset_of_subset
    (corollary_18_9_leftInfChars_subset Δ wg V lam)
    (corollary_18_9_leftInfChars_supset Δ wg V lam)

def infCharsOfModule
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] :
    Set (↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :=
  { χ | ∃ (act : UniversalEnvelopingAlgebra R 𝔤 →ₐ[R] Module.End R M),
    (∀ (x : 𝔤) (m : M), act (UniversalEnvelopingAlgebra.ι R x) m = ⁅x, m⁆) ∧
    ∃ (m : M), m ≠ 0 ∧
      ∀ (z : Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)),
        act (z : UniversalEnvelopingAlgebra R 𝔤) m = χ z • m }


theorem infCharsOfModule_tensor_subset_leftInfChars
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (lam : Δ.𝔥 →ₗ[R] R)
    (hchar : HasInfinitesimalCharacter (R := R) (𝔤 := 𝔤) M (evalHC Δ wg lam)) :
    infCharsOfModule (𝔤 := 𝔤) (TensorProduct R V M) ⊆
    leftInfChars (tensorBimodule (LieBimodule.trivial V) (evalHC Δ wg lam)) := by


  sorry

theorem corollary_18_10_ii [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (lam : Δ.𝔥 →ₗ[R] R)

    (hchar : HasInfinitesimalCharacter (R := R) (𝔤 := 𝔤) M (evalHC Δ wg lam)) :
    infCharsOfModule (𝔤 := 𝔤) (TensorProduct R V M) ⊆
    { θ | ∃ (ν : Δ.𝔥 →ₗ[R] R), ν ∈ weights Δ V ∧
      θ = evalHC Δ wg (lam + ν) } := by

  have h_sub := infCharsOfModule_tensor_subset_leftInfChars Δ wg V M lam hchar

  have h_eq := corollary_18_10_i Δ wg V lam

  intro θ hθ
  have hθ' := h_sub hθ
  rw [h_eq] at hθ'
  exact hθ'


theorem corollary_14_5_hc_bimodule_left_char_in_tensor_ax
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (M : LieBimodule R 𝔤)
    (hHC : IsHarishChandraBimodule M)
    (hne : ∃ (m : M.carrier), m ≠ 0)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (hchar : M.HasInfinitesimalCharacterPair (evalHC Δ wg lam) (evalHC Δ wg mu)) :
    ∃ (V : Type) (iACG : AddCommGroup V) (iMod : Module R V) (iFin : Module.Finite R V)
       (iLRM : LieRingModule 𝔤 V) (iLM : LieModule R 𝔤 V)
       (_ : IsNoetherian R V) (_ : Module.IsTorsionFree R V),
       evalHC Δ wg lam ∈
         leftInfChars (tensorBimodule
           (@LieBimodule.trivial R _ 𝔤 _ _ V iACG iMod iLRM iLM)
           (evalHC Δ wg mu)) := by


  sorry

theorem corollary_14_5_left_char_from_weight
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (M : LieBimodule R 𝔤)
    (hHC : IsHarishChandraBimodule M)
    (hne : ∃ (m : M.carrier), m ≠ 0)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (hchar : M.HasInfinitesimalCharacterPair (evalHC Δ wg lam) (evalHC Δ wg mu)) :
    ∃ (ν : Δ.𝔥 →ₗ[R] R),
      (∃ (V : Type) (_ : AddCommGroup V) (_ : Module R V) (_ : Module.Finite R V)
         (_ : LieRingModule 𝔤 V) (_ : LieModule R 𝔤 V)
         (_ : IsNoetherian R V) (_ : Module.IsTorsionFree R V),
         ν ∈ @weights R _ 𝔤 _ _ Δ V _ _ _ _) ∧
      evalHC Δ wg lam = evalHC Δ wg (mu + ν) := by

  obtain ⟨V, iACG, iMod, iFin, iLRM, iLM, iNoeth, iTF, hmem⟩ :=
    corollary_14_5_hc_bimodule_left_char_in_tensor_ax Δ wg M hHC hne lam mu hchar


  letI := iACG; letI := iMod; letI := iFin; letI := iLRM; letI := iLM
  have h_eq := corollary_18_10_i Δ wg V mu
  rw [h_eq] at hmem

  simp only [Set.mem_setOf_eq] at hmem
  obtain ⟨ν, hν_wt, hν_eq⟩ := hmem
  exact ⟨ν, ⟨V, iACG, iMod, iFin, iLRM, iLM, iNoeth, iTF, hν_wt⟩, hν_eq⟩

theorem weights_in_weightLattice
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (chev : ChevalleyData Δ)
    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    [IsNoetherian R V] [Module.IsTorsionFree R V]
    (ν : Δ.𝔥 →ₗ[R] R)
    (hν : ν ∈ weights Δ V) :
    chev.IsInWeightLattice ν := by

  intro i

  have hν' : WeightSpace Δ V ν ≠ ⊥ := hν
  rw [Submodule.ne_bot_iff] at hν'
  obtain ⟨v, hv_mem, hv_ne⟩ := hν'

  have hv_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = ν h • v := hv_mem

  have hh : ⁅(chev.simpleCoroot i : 𝔤), v⁆ = ν (chev.simpleCoroot i) • v := hv_wt _

  by_cases hhz : (chev.simpleCoroot i : 𝔤) = 0
  · have hμv : ν (chev.simpleCoroot i) • v = 0 := by rw [← hh, hhz, zero_lie]
    have hμ0 : ν (chev.simpleCoroot i) = 0 := by
      by_contra hμ
      have hreg : IsRegular (ν (chev.simpleCoroot i)) :=
        ⟨fun a b hab => mul_left_cancel₀ hμ hab,
         fun a b hab => mul_right_cancel₀ hμ hab⟩
      have hsmul : IsSMulRegular V (ν (chev.simpleCoroot i)) :=
        Module.IsTorsionFree.isSMulRegular (M := V) hreg
      exact hv_ne (hsmul (show ν (chev.simpleCoroot i) • v = ν (chev.simpleCoroot i) • 0 by
        simp [hμv]))
    exact ⟨0, by simp [hμ0]⟩
  ·

    have t : IsSl2Triple (chev.simpleCoroot i : 𝔤) (chev.posGen i) (chev.negGen i) :=
      IsSl2Triple.mk hhz
        (chev.bracket_ef i)
        (by rw [two_nsmul]; exact chev.bracket_he i)
        (by rw [two_nsmul]; exact chev.bracket_hf i)
    set μ := ν (chev.simpleCoroot i)
    set e_i := chev.posGen i
    set h_i := (chev.simpleCoroot i : 𝔤)

    set ψ : ℕ → V := fun k => ((LieModule.toEnd R 𝔤 V e_i) ^ k) v

    have hψ_eig : ∀ k : ℕ, ⁅h_i, ψ k⁆ = (μ + 2 * (k : R)) • ψ k := by
      intro k
      induction k with
      | zero => simp [ψ, hh]
      | succ n ih =>
        simp only [ψ, pow_succ', Module.End.mul_apply, LieModule.toEnd_apply_apply]
        rw [leibniz_lie]
        rw [t.lie_h_e_smul R]
        simp only [ψ] at ih
        rw [ih]
        simp only [lie_smul, smul_lie]
        rw [← add_smul]
        congr 1
        push_cast
        ring

    have hψ_zero : ∃ k : ℕ, ψ k = 0 := by
      by_contra! hall

      have hs : (Set.range (fun (n : ℕ) => μ + 2 * (n : R))).Infinite := by
        rw [Set.infinite_range_iff]
        · infer_instance
        · intro a b hab
          simp only at hab
          exact_mod_cast mul_left_cancel₀ (two_ne_zero (α := R)) (add_left_cancel hab)


      exact hs ((LieModule.toEnd R 𝔤 V h_i).eigenvectors_linearIndependent
        (Set.range (fun (n : ℕ) => μ + 2 * (n : R)))
        (fun ⟨_, hs⟩ => ψ (Classical.choose hs))
        (fun ⟨_, hs⟩ => by
          simp only [Module.End.hasEigenvector_iff, Module.End.mem_eigenspace_iff]
          have hk := Classical.choose_spec hs
          simp only at hk
          refine ⟨?_, hall _⟩
          rw [LieModule.toEnd_apply_apply, hψ_eig, hk])).finite


    obtain ⟨k₀, hk₀_ne, hk₀_zero⟩ := Nat.exists_not_and_succ_of_not_zero_of_exists
      (show ¬(ψ 0 = 0) from by simp [ψ, hv_ne]) hψ_zero

    have he_kill : ⁅e_i, ψ k₀⁆ = 0 := by
      show (LieModule.toEnd R 𝔤 V e_i) (((LieModule.toEnd R 𝔤 V e_i) ^ k₀) v) = 0
      rw [← Module.End.mul_apply, ← pow_succ']
      exact hk₀_zero

    have hprim : t.HasPrimitiveVectorWith (ψ k₀) (μ + 2 * (k₀ : R)) :=
      IsSl2Triple.HasPrimitiveVectorWith.mk hk₀_ne (hψ_eig k₀) he_kill

    obtain ⟨n, hn⟩ := hprim.exists_nat

    exact ⟨(n : ℤ) - 2 * (k₀ : ℤ), by push_cast; linear_combination hn⟩

theorem hc_bimodule_weight_shift [IsDomain R] [CharZero R] [IsNoetherianRing R]
    [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (chev : ChevalleyData Δ)
    (M : LieBimodule R 𝔤)
    (hHC : IsHarishChandraBimodule M)
    (hne : ∃ (m : M.carrier), m ≠ 0)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (hchar : M.HasInfinitesimalCharacterPair (evalHC Δ wg lam) (evalHC Δ wg mu)) :
    ∃ (ν : Δ.𝔥 →ₗ[R] R),
      chev.IsInWeightLattice ν ∧
      evalHC Δ wg lam = evalHC Δ wg (mu + ν) := by

  obtain ⟨ν, ⟨V, hAG, hMod, hFin, hLRM, hLM, hNoeth, hTF, hν_wt⟩, hν_char⟩ :=
    corollary_14_5_left_char_from_weight Δ wg M hHC hne lam mu hchar

  refine ⟨ν, ?_, hν_char⟩
  exact @weights_in_weightLattice R _ _ _ _ _ _ _ Δ chev V hAG hMod hFin hLRM hLM hNoeth hTF ν hν_wt


theorem corollary_18_10_iii [IsDomain R] [CharZero R] [IsNoetherianRing R]
    [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (chev : ChevalleyData Δ)
    (M : LieBimodule R 𝔤)
    (hHC : IsHarishChandraBimodule M)
    (hne : ∃ (m : M.carrier), m ≠ 0)
    (lam mu : Δ.𝔥 →ₗ[R] R)

    (hchar : M.HasInfinitesimalCharacterPair (evalHC Δ wg lam) (evalHC Δ wg mu)) :
    ∃ (w : wg.W), chev.IsInWeightLattice (wg.shiftedAction w lam - mu) := by


  have hshift := hc_bimodule_weight_shift Δ wg chev M hHC hne lam mu hchar

  obtain ⟨ν, hν_lattice, hν_char⟩ := hshift


  have hdef : ∀ (wt : Δ.𝔥 →ₗ[R] R)
    (z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))),
    evalHC Δ wg wt z = evalWeight Δ (wt + wg.ρ)
      ((chevalley_restriction_hc_iso Δ wg z : wg.invariantSubalgebra) :
        UniversalEnvelopingAlgebra R Δ.𝔥) := by
    intro wt z; rfl
  rw [infinitesimalCharacter_eq_iff_shiftedWeylOrbit Δ wg (evalHC Δ wg) hdef lam (mu + ν)]
    at hν_char
  obtain ⟨w, hw⟩ := hν_char

  refine ⟨w, ?_⟩
  have heq : wg.shiftedAction w lam - mu = ν := by
    calc wg.shiftedAction w lam - mu
        = (mu + ν) - mu := by rw [← hw]
      _ = ν := by abel
  rw [heq]; exact hν_lattice

theorem corollary_18_10_full [IsDomain R] [CharZero R] [IsNoetherianRing R]
    [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (chev : ChevalleyData Δ)

    (V : Type*) [AddCommGroup V] [Module R V] [Module.Finite R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (lam : Δ.𝔥 →ₗ[R] R)

    (M_ii : Type*) [AddCommGroup M_ii] [Module R M_ii]
    [LieRingModule 𝔤 M_ii] [LieModule R 𝔤 M_ii]
    (hchar_ii : HasInfinitesimalCharacter (R := R) (𝔤 := 𝔤) M_ii (evalHC Δ wg lam))

    (M_iii : LieBimodule R 𝔤)
    (hHC : IsHarishChandraBimodule M_iii)
    (hne : ∃ (m : M_iii.carrier), m ≠ 0)
    (lam_iii mu_iii : Δ.𝔥 →ₗ[R] R)
    (hchar_iii : M_iii.HasInfinitesimalCharacterPair (evalHC Δ wg lam_iii) (evalHC Δ wg mu_iii)) :

    (leftInfChars (tensorBimodule (LieBimodule.trivial V) (evalHC Δ wg lam)) =
      { θ | ∃ (ν : Δ.𝔥 →ₗ[R] R), ν ∈ weights Δ V ∧ θ = evalHC Δ wg (lam + ν) }) ∧
    (infCharsOfModule (𝔤 := 𝔤) (TensorProduct R V M_ii) ⊆
      { θ | ∃ (ν : Δ.𝔥 →ₗ[R] R), ν ∈ weights Δ V ∧ θ = evalHC Δ wg (lam + ν) }) ∧
    (∃ (w : wg.W), chev.IsInWeightLattice (wg.shiftedAction w lam_iii - mu_iii)) :=
  ⟨corollary_18_10_i Δ wg V lam,
   corollary_18_10_ii Δ wg V M_ii lam hchar_ii,
   corollary_18_10_iii Δ wg chev M_iii hHC hne lam_iii mu_iii hchar_iii⟩

def IsDominantIntegralWeight (Δ : TriangularDecomposition R 𝔤)
    (_rd : PositiveRootData Δ) (chev : ChevalleyData Δ) (γ : Δ.𝔥 →ₗ[R] R) : Prop :=
  chev.IsDominantIntegral γ

abbrev CentralCharacter (R : Type*) [CommRing R] (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤] :=
  ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R

def DominantWeights (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ) (chev : ChevalleyData Δ) : Set (Δ.𝔥 →ₗ[R] R) :=
  { γ | IsDominantIntegralWeight Δ rd chev γ }

structure IsInHCBimod
    (M : LieBimodule R 𝔤)
    (θ χ : CentralCharacter R 𝔤) : Prop where
  isHC : IsHarishChandraBimodule M
  charPair : M.HasInfinitesimalCharacterPair θ χ

def IsInHCBimod.ofEvalHC (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ) (M : LieBimodule R 𝔤)
    (hHC : IsHarishChandraBimodule M)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (hchar : M.HasInfinitesimalCharacterPair (evalHC Δ wg lam) (evalHC Δ wg mu)) :
    IsInHCBimod M (evalHC Δ wg lam) (evalHC Δ wg mu) :=
  ⟨hHC, hchar⟩


theorem exercise_15_5 (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ) (rd : PositiveRootData Δ) (chev : ChevalleyData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (w : wg.W) (hw : chev.IsInWeightLattice (wg.shiftedAction w lam - mu)) :
    ∃ (lam' γ : Δ.𝔥 →ₗ[R] R),
      IsDominantIntegralWeight Δ rd chev γ ∧
      evalHC Δ wg lam = evalHC Δ wg (lam' + γ) ∧
      evalHC Δ wg mu = evalHC Δ wg lam' := by


  sorry


theorem character_extension_invariant (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (θ' : ↥(wg.invariantSubalgebra) →ₐ[R] R) :
    ∃ wt : Δ.𝔥 →ₗ[R] R, θ' = (evalWeight Δ wt).comp wg.invariantSubalgebra.val := by


  sorry

theorem evalHC_surjective (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ)
    (θ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R) :
    ∃ (mu : Δ.𝔥 →ₗ[R] R), θ = evalHC Δ wg mu := by

  set iso := chevalley_restriction_hc_iso Δ wg with hiso_def
  set θ' : ↥(wg.invariantSubalgebra) →ₐ[R] R := θ.comp iso.symm.toAlgHom with hθ'_def

  obtain ⟨wt, hwt⟩ := character_extension_invariant Δ wg θ'

  refine ⟨wt - wg.ρ, ?_⟩
  have h_sub_add : wt - wg.ρ + wg.ρ = wt := sub_add_cancel wt wg.ρ

  have hθ_eq : θ = θ'.comp iso.toAlgHom := by
    ext z
    simp [hθ'_def, AlgHom.comp_apply]
  rw [hθ_eq, hwt]
  unfold evalHC
  simp only [h_sub_add]
  ext z; simp only [AlgHom.comp_apply, hiso_def]

def stabilizerOfWeight (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ) (γ : Δ.𝔥 →ₗ[R] R) : Subgroup wg.W where
  carrier := { w | wg.dualAction w γ = γ }
  one_mem' := by
    show wg.dualAction 1 γ = γ
    exact wg.dualAction_one γ
  mul_mem' := by
    intro a b ha hb
    show wg.dualAction (a * b) γ = γ
    rw [wg.dualAction_mul, hb, ha]
  inv_mem' := by
    intro a ha
    show wg.dualAction a⁻¹ γ = γ
    have h := wg.dualAction_mul a⁻¹ a γ
    rw [inv_mul_cancel, wg.dualAction_one, ha] at h
    exact h.symm

def equivModStab (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (γ : Δ.𝔥 →ₗ[R] R) (lam₁ lam₂ : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∃ w ∈ stabilizerOfWeight Δ wg γ, wg.dualAction w lam₁ = lam₂

theorem corollary_18_11_decomposition [IsDomain R] [CharZero R] [IsNoetherianRing R]
    [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ) (rd : PositiveRootData Δ) (chev : ChevalleyData Δ)
    (M : LieBimodule R 𝔤)
    (hHC : IsHarishChandraBimodule M)
    (hne : ∃ (m : M.carrier), m ≠ 0)
    (θ χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R)
    (hchar : M.HasInfinitesimalCharacterPair θ χ) :
    ∃ (γ : Δ.𝔥 →ₗ[R] R) (lam : Δ.𝔥 →ₗ[R] R),
      IsDominantIntegralWeight Δ rd chev γ ∧
      θ = evalHC Δ wg (lam + γ) ∧
      χ = evalHC Δ wg lam := by

  obtain ⟨m, hm⟩ := hne
  obtain ⟨lam₀, hlam₀⟩ := evalHC_surjective Δ wg θ
  obtain ⟨mu₀, hmu₀⟩ := evalHC_surjective Δ wg χ
  have hchar' : M.HasInfinitesimalCharacterPair (evalHC Δ wg lam₀) (evalHC Δ wg mu₀) :=
    hlam₀ ▸ hmu₀ ▸ hchar
  obtain ⟨w, hw⟩ := corollary_18_10_iii Δ wg chev M hHC ⟨m, hm⟩ lam₀ mu₀ hchar'
  obtain ⟨lam', γ, hγ_dom, hlam_eq, hmu_eq⟩ := exercise_15_5 Δ wg rd chev lam₀ mu₀ w hw
  exact ⟨γ, lam', hγ_dom, hlam₀ ▸ hlam_eq, hmu₀ ▸ hmu_eq⟩

theorem corollary_18_11_vanishing [IsDomain R] [CharZero R] [IsNoetherianRing R]
    [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ) (rd : PositiveRootData Δ) (chev : ChevalleyData Δ)
    (θ χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R)
    (h : ∀ (lam γ : Δ.𝔥 →ₗ[R] R),
      IsDominantIntegralWeight Δ rd chev γ →
      ¬(θ = evalHC Δ wg (lam + γ) ∧ χ = evalHC Δ wg lam))
    (M : LieBimodule R 𝔤)
    (hHC : IsHarishChandraBimodule M)
    (hchar : M.HasInfinitesimalCharacterPair θ χ) :
    ∀ (m : M.carrier), m = 0 := by


  by_contra h_ne
  push Not at h_ne
  obtain ⟨m, hm⟩ := h_ne

  obtain ⟨γ, lam, hγ_dom, hθ_eq, hχ_eq⟩ :=
    corollary_18_11_decomposition Δ wg rd chev M hHC ⟨m, hm⟩ θ χ hchar
  exact h lam γ hγ_dom ⟨hθ_eq, hχ_eq⟩
theorem dominant_weights_eq_of_shifted_orbit_ax {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤} (wg : WeylGroupData Δ)
    (rd : PositiveRootData Δ) (chev : ChevalleyData Δ)
    (γ₁ γ₂ lam₁ lam₂ : Δ.𝔥 →ₗ[R] R)
    (hγ₁ : IsDominantIntegralWeight Δ rd chev γ₁)
    (hγ₂ : IsDominantIntegralWeight Δ rd chev γ₂)
    (w : wg.W) (hw : lam₂ = wg.shiftedAction w lam₁)
    (w' : wg.W) (hw' : lam₂ + γ₂ = wg.shiftedAction w' (lam₁ + γ₁)) :
    γ₁ = γ₂ := by


  sorry


theorem equivModStab_of_shifted_orbit_ax {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤} (wg : WeylGroupData Δ)
    (rd : PositiveRootData Δ) (chev : ChevalleyData Δ)
    (γ lam₁ lam₂ : Δ.𝔥 →ₗ[R] R)
    (hγ : IsDominantIntegralWeight Δ rd chev γ)
    (w : wg.W) (hw : lam₂ = wg.shiftedAction w lam₁)
    (w' : wg.W) (hw' : lam₂ + γ = wg.shiftedAction w' (lam₁ + γ)) :
    equivModStab Δ wg γ lam₁ lam₂ := by


  sorry

theorem dominant_weight_uniqueness_in_shifted_orbit (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ) (rd : PositiveRootData Δ) (chev : ChevalleyData Δ)
    (γ₁ γ₂ lam₁ lam₂ : Δ.𝔥 →ₗ[R] R)
    (hγ₁ : IsDominantIntegralWeight Δ rd chev γ₁)
    (hγ₂ : IsDominantIntegralWeight Δ rd chev γ₂)
    (w : wg.W) (hw : lam₂ = wg.shiftedAction w lam₁)
    (w' : wg.W) (hw' : lam₂ + γ₂ = wg.shiftedAction w' (lam₁ + γ₁)) :
    γ₁ = γ₂ ∧ equivModStab Δ wg γ₁ lam₁ lam₂ := by

  have hγeq : γ₁ = γ₂ :=
    dominant_weights_eq_of_shifted_orbit_ax wg rd chev γ₁ γ₂ lam₁ lam₂ hγ₁ hγ₂ w hw w' hw'
  constructor
  · exact hγeq
  ·

    have hw'₁ : lam₂ + γ₁ = wg.shiftedAction w' (lam₁ + γ₁) := by
      rw [← hγeq] at hw'; exact hw'

    exact equivModStab_of_shifted_orbit_ax wg rd chev γ₁ lam₁ lam₂ hγ₁ w hw w' hw'₁

theorem corollary_18_11_uniqueness [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ) (rd : PositiveRootData Δ) (chev : ChevalleyData Δ)
    (γ₁ γ₂ lam₁ lam₂ : Δ.𝔥 →ₗ[R] R)
    (hγ₁ : IsDominantIntegralWeight Δ rd chev γ₁)
    (hγ₂ : IsDominantIntegralWeight Δ rd chev γ₂)
    (hθ : evalHC Δ wg (lam₁ + γ₁) = evalHC Δ wg (lam₂ + γ₂))
    (hχ : evalHC Δ wg lam₁ = evalHC Δ wg lam₂) :
    γ₁ = γ₂ ∧ equivModStab Δ wg γ₁ lam₁ lam₂ := by

  have hdef : ∀ (wt : Δ.𝔥 →ₗ[R] R)
    (z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤))),
    evalHC Δ wg wt z = evalWeight Δ (wt + wg.ρ)
      ((chevalley_restriction_hc_iso Δ wg z : wg.invariantSubalgebra) :
        UniversalEnvelopingAlgebra R Δ.𝔥) := by
    intro wt z; rfl

  rw [infinitesimalCharacter_eq_iff_shiftedWeylOrbit Δ wg (evalHC Δ wg) hdef lam₁ lam₂] at hχ
  obtain ⟨w, hw⟩ := hχ

  rw [infinitesimalCharacter_eq_iff_shiftedWeylOrbit Δ wg (evalHC Δ wg) hdef
    (lam₁ + γ₁) (lam₂ + γ₂)] at hθ
  obtain ⟨w', hw'⟩ := hθ

  exact dominant_weight_uniqueness_in_shifted_orbit Δ wg rd chev
    γ₁ γ₂ lam₁ lam₂ hγ₁ hγ₂ w hw w' hw'

theorem corollary_18_11 [IsDomain R] [CharZero R] [IsNoetherianRing R]
    [Module.Finite R 𝔤] (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ) (rd : PositiveRootData Δ) (chev : ChevalleyData Δ) :

    (∀ (M : LieBimodule R 𝔤) (hHC : IsHarishChandraBimodule M)
       (hne : ∃ (m : M.carrier), m ≠ 0)
       (θ χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R)
       (hchar : M.HasInfinitesimalCharacterPair θ χ),
       ∃ (γ : Δ.𝔥 →ₗ[R] R) (lam : Δ.𝔥 →ₗ[R] R),
         IsDominantIntegralWeight Δ rd chev γ ∧
         θ = evalHC Δ wg (lam + γ) ∧
         χ = evalHC Δ wg lam) ∧

    (∀ (θ χ : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R 𝔤)) →ₐ[R] R)
       (h : ∀ (lam γ : Δ.𝔥 →ₗ[R] R),
         IsDominantIntegralWeight Δ rd chev γ →
         ¬(θ = evalHC Δ wg (lam + γ) ∧ χ = evalHC Δ wg lam))
       (M : LieBimodule R 𝔤)
       (hHC : IsHarishChandraBimodule M)
       (hchar : M.HasInfinitesimalCharacterPair θ χ),
       ∀ (m : M.carrier), m = 0) ∧

    (∀ (γ₁ γ₂ lam₁ lam₂ : Δ.𝔥 →ₗ[R] R)
       (hγ₁ : IsDominantIntegralWeight Δ rd chev γ₁)
       (hγ₂ : IsDominantIntegralWeight Δ rd chev γ₂)
       (hθ : evalHC Δ wg (lam₁ + γ₁) = evalHC Δ wg (lam₂ + γ₂))
       (hχ : evalHC Δ wg lam₁ = evalHC Δ wg lam₂),
       γ₁ = γ₂ ∧ equivModStab Δ wg γ₁ lam₁ lam₂) :=
  ⟨fun M hHC hne θ χ hchar => corollary_18_11_decomposition Δ wg rd chev M hHC hne θ χ hchar,
   fun θ χ h M hHC hchar => corollary_18_11_vanishing Δ wg rd chev θ χ h M hHC hchar,
   fun γ₁ γ₂ lam₁ lam₂ hγ₁ hγ₂ hθ hχ =>
     corollary_18_11_uniqueness Δ wg rd chev γ₁ γ₂ lam₁ lam₂ hγ₁ hγ₂ hθ hχ⟩

end
