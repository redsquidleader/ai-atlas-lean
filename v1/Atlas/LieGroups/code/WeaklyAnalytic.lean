/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.HarishChandraFunctor
import Atlas.LieGroups.code.GKModuleDefs
import Atlas.LieGroups.code.AnalyticityRegularity
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.Analysis.Normed.Group.Quotient

universe uFw

noncomputable section

set_option autoImplicit false

open scoped Manifold

def ContinuousRep.IsWeaklyAnalytic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F)
    (v : F) : Prop :=
  ∀ (h : F →L[ℂ] ℂ) (g₀ : G),
    AnalyticAt ℝ
      (fun (e : E) =>
        (h (π.toMonoidHom ((chartAt H g₀).symm (I.symm e)) v) : ℂ))
      (I (chartAt H g₀ g₀))

namespace EllipticOperator

def IsEllipticAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (symbolAt : E → ℝ) : Prop :=
  ∀ (p : E), p ≠ 0 → symbolAt p ≠ 0

def IsElliptic
    {X : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (σ : X → E → ℝ) : Prop :=
  ∀ (x : X), IsEllipticAt (σ x)

end EllipticOperator

open EllipticOperator in
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (h : IsEllipticAt f)
    (p : E) (hp : p ≠ 0) : f p ≠ 0 := h p hp

theorem lie_iter_vanish_implies_re_vanishes_near_identity_axiom
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (hG_ss : ContinuousRep.IsSemisimpleLieGroup I G)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)]
    (w : ↥(π.kFiniteSubspace K_sub))
    (v : F) (hv : v = (π.kFiniteSubspace K_sub).subtype w)
    (hv_analytic : π.IsWeaklyAnalyticVector I v)
    (h : F →L[ℂ] ℂ)
    (hh_lie_iter_vanish : ∀ (Xs : List 𝔤),
      h ((π.kFiniteSubspace K_sub).subtype (Xs.foldr (fun X acc => ⁅X, acc⁆) w)) = 0) :
    ∃ (U : Set G), (1 : G) ∈ U ∧ IsOpen U ∧
      ∀ g ∈ U, (h ((π.toMonoidHom g) v)).re = 0 := by sorry

theorem lie_iter_vanish_implies_re_vanishes_near_identity
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (hG_ss : ContinuousRep.IsSemisimpleLieGroup I G)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)]
    (w : ↥(π.kFiniteSubspace K_sub))
    (v : F) (hv : v = (π.kFiniteSubspace K_sub).subtype w)
    (hv_analytic : π.IsWeaklyAnalyticVector I v)
    (h : F →L[ℂ] ℂ)
    (hh_lie_iter_vanish : ∀ (Xs : List 𝔤),
      h ((π.kFiniteSubspace K_sub).subtype (Xs.foldr (fun X acc => ⁅X, acc⁆) w)) = 0) :
    ∃ (U : Set G), (1 : G) ∈ U ∧ IsOpen U ∧
      ∀ g ∈ U, (h ((π.toMonoidHom g) v)).re = 0 :=
  lie_iter_vanish_implies_re_vanishes_near_identity_axiom I π K_sub hG_ss 𝔤 w v hv hv_analytic h hh_lie_iter_vanish

theorem analytic_matcoeff_re_vanishes_globally_of_locally_axiom
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F)
    (hG_ss : ContinuousRep.IsSemisimpleLieGroup I G)
    (v : F)
    (hv_analytic : π.IsWeaklyAnalyticVector I v)
    (h : F →L[ℂ] ℂ)
    (U : Set G) (hU_open : IsOpen U) (hU_mem : (1 : G) ∈ U)
    (hU_vanish : ∀ g ∈ U, (h ((π.toMonoidHom g) v)).re = 0)
    (g : G) : (h ((π.toMonoidHom g) v)).re = 0 := by sorry

theorem analytic_matcoeff_re_vanishes_globally_of_locally
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F)
    (hG_ss : ContinuousRep.IsSemisimpleLieGroup I G)
    (v : F)
    (hv_analytic : π.IsWeaklyAnalyticVector I v)
    (h : F →L[ℂ] ℂ)
    (U : Set G) (hU_open : IsOpen U) (hU_mem : (1 : G) ∈ U)
    (hU_vanish : ∀ g ∈ U, (h ((π.toMonoidHom g) v)).re = 0)
    (g : G) : (h ((π.toMonoidHom g) v)).re = 0 :=
  analytic_matcoeff_re_vanishes_globally_of_locally_axiom I π hG_ss v hv_analytic h U hU_open hU_mem hU_vanish g

theorem matrix_coeff_re_vanishes_of_lie_iter_vanish
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (hG_ss : ContinuousRep.IsSemisimpleLieGroup I G)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)]
    (w : ↥(π.kFiniteSubspace K_sub))
    (v : F) (hv : v = (π.kFiniteSubspace K_sub).subtype w)
    (hv_analytic : π.IsWeaklyAnalyticVector I v)
    (h : F →L[ℂ] ℂ)
    (hh_lie_iter_vanish : ∀ (Xs : List 𝔤),
      h ((π.kFiniteSubspace K_sub).subtype (Xs.foldr (fun X acc => ⁅X, acc⁆) w)) = 0)
    (g : G) : (h ((π.toMonoidHom g) v)).re = 0 := by


  obtain ⟨U, hU_mem, hU_open, hU_vanish⟩ :=
    lie_iter_vanish_implies_re_vanishes_near_identity I π K_sub hG_ss 𝔤
      w v hv hv_analytic h hh_lie_iter_vanish


  exact analytic_matcoeff_re_vanishes_globally_of_locally I π hG_ss v hv_analytic h
    U hU_open hU_mem hU_vanish g

theorem analytic_continuation_connected_lie_group
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (hG_ss : ContinuousRep.IsSemisimpleLieGroup I G)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)]
    (w : ↥(π.kFiniteSubspace K_sub))
    (hv_analytic : π.IsWeaklyAnalyticVector I ((π.kFiniteSubspace K_sub).subtype w))
    (h : F →L[ℂ] ℂ)


    (hh_lie_iter_vanish : ∀ (Xs : List 𝔤),
      h ((π.kFiniteSubspace K_sub).subtype (Xs.foldr (fun X acc => ⁅X, acc⁆) w)) = 0)
    (g : G) : h ((π.toMonoidHom g) ((π.kFiniteSubspace K_sub).subtype w)) = 0 := by


  set v := (π.kFiniteSubspace K_sub).subtype w

  have hre : (h ((π.toMonoidHom g) v)).re = 0 :=
    matrix_coeff_re_vanishes_of_lie_iter_vanish I π K_sub hG_ss 𝔤
      w v rfl hv_analytic h hh_lie_iter_vanish g


  set h' : F →L[ℂ] ℂ := (-Complex.I) • h
  have hh'_lie_iter_vanish : ∀ (Xs : List 𝔤),
      h' ((π.kFiniteSubspace K_sub).subtype (Xs.foldr (fun X acc => ⁅X, acc⁆) w)) = 0 := by
    intro Xs
    simp only [h', ContinuousLinearMap.smul_apply, smul_eq_zero]
    right
    exact hh_lie_iter_vanish Xs

  have hre' : (h' ((π.toMonoidHom g) v)).re = 0 :=
    matrix_coeff_re_vanishes_of_lie_iter_vanish I π K_sub hG_ss 𝔤
      w v rfl hv_analytic h' hh'_lie_iter_vanish g


  have him : (h ((π.toMonoidHom g) v)).im = 0 := by
    simp only [h', ContinuousLinearMap.smul_apply] at hre'


    rw [smul_eq_mul] at hre'


    rw [neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg] at hre'

    exact hre'


  exact Complex.ext hre him

theorem analytic_continuation_from_gInvariance
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    [SecondCountableTopology G]
    {F : Type uFw} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (hadm : @ContinuousRep.IsAdmissible.{_, uFw, uFw} _ _ _ _ _ _ _ _ π K_sub)
    (hG_ss : ContinuousRep.IsSemisimpleLieGroup I G)
    [CompactSpace K_sub] [T2Space K_sub]

    (hK_max : IsMaximalCompactSubgroup K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K_sub →* (𝔤 →ₗ[ℂ] 𝔤))
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    [LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)]
    (hequiv : ∀ (k : K_sub) (X : 𝔤) (v : ↥(π.kFiniteSubspace K_sub)),
      (kFiniteSubspace_kAction π K_sub) k (⁅X, v⁆) =
        ⁅Ad k X, (kFiniteSubspace_kAction π K_sub) k v⁆)
    (W : Submodule ℂ ↥(π.kFiniteSubspace K_sub))
    (hW : (harishChandraGKModule I π K_sub hadm 𝔤 𝔨 Ad ι hequiv).IsSubmodule W)
    (w : ↥(π.kFiniteSubspace K_sub)) (hw : w ∈ W)
    (h : F →L[ℂ] ℂ)
    (hh_vanish : ∀ v ∈ closure ((π.kFiniteSubspace K_sub).subtype ''
      (W : Set ↥(π.kFiniteSubspace K_sub))), h v = 0)
    (g : G) : h ((π.toMonoidHom g) ((π.kFiniteSubspace K_sub).subtype w)) = 0 := by

  set v := (π.kFiniteSubspace K_sub).subtype w with hv_def
  have hv_kfin : v ∈ π.kFiniteSubspace K_sub := (π.kFiniteSubspace K_sub).coe_mem w
  have hv_analytic : π.IsWeaklyAnalyticVector I v :=
    ContinuousRep.harish_chandra_analyticity I π K_sub hG_ss hK_max hadm v hv_kfin


  have hh_lie_iter_vanish : ∀ (Xs : List 𝔤),
      h ((π.kFiniteSubspace K_sub).subtype
        (Xs.foldr (fun X acc => ⁅X, acc⁆) w)) = 0 := by
    intro Xs

    have hiter_in_W : Xs.foldr (fun X acc => ⁅X, acc⁆) w ∈ W := by
      induction Xs with
      | nil => exact hw
      | cons X Xs ih => exact hW.lie_invariant X _ ih

    have hiter_in_image : (π.kFiniteSubspace K_sub).subtype
        (Xs.foldr (fun X acc => ⁅X, acc⁆) w) ∈
        (π.kFiniteSubspace K_sub).subtype '' (W : Set ↥(π.kFiniteSubspace K_sub)) :=
      ⟨Xs.foldr (fun X acc => ⁅X, acc⁆) w, hiter_in_W, rfl⟩
    exact hh_vanish _ (subset_closure hiter_in_image)


  exact analytic_continuation_connected_lie_group I π K_sub hG_ss 𝔤
    w hv_analytic h hh_lie_iter_vanish g

theorem hahn_banach_separation_closed_subspace
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (S : Set F) (x : F)
    (hS_subspace : ∃ (M : Submodule ℂ F), (M : Set F) = S)
    (hx : x ∉ closure S) :
    ∃ (h : F →L[ℂ] ℂ), (∀ v ∈ closure S, h v = 0) ∧ h x ≠ 0 := by
  obtain ⟨M, hMS⟩ := hS_subspace

  have hcl : closure S = (M.topologicalClosure : Set F) := by
    rw [← hMS, Submodule.topologicalClosure_coe]
  rw [hcl] at hx

  haveI hclosed : IsClosed (M.topologicalClosure : Set F) :=
    M.isClosed_topologicalClosure

  have hxQ : M.topologicalClosure.mkQ x ≠ 0 := by
    rwa [Submodule.mkQ_apply, ne_eq, Submodule.Quotient.mk_eq_zero]


  obtain ⟨g, hg⟩ : ∃ (g : (F ⧸ M.topologicalClosure) →L[ℂ] ℂ),
      g (M.topologicalClosure.mkQ x) ≠ 0 :=
    SeparatingDual.exists_ne_zero hxQ

  let mkQ_clm : F →L[ℂ] (F ⧸ M.topologicalClosure) :=
    { M.topologicalClosure.mkQ with cont := continuous_quot_mk }
  refine ⟨g.comp mkQ_clm, ?_, ?_⟩
  ·
    intro v hv
    rw [hcl] at hv
    show g (mkQ_clm v) = 0
    suffices hsuff : mkQ_clm v = 0 by rw [hsuff, map_zero]
    show M.topologicalClosure.mkQ v = 0
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  ·
    show g (mkQ_clm x) ≠ 0
    exact hg

theorem gkSubmodule_closure_isInvariant_analyticity_step
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    [SecondCountableTopology G]
    {F : Type uFw} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (hadm : @ContinuousRep.IsAdmissible.{_, uFw, uFw} _ _ _ _ _ _ _ _ π K_sub)
    (hG_ss : ContinuousRep.IsSemisimpleLieGroup I G)
    [CompactSpace K_sub] [T2Space K_sub]

    (hK_max : IsMaximalCompactSubgroup K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K_sub →* (𝔤 →ₗ[ℂ] 𝔤))
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    [LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)]
    (hequiv : ∀ (k : K_sub) (X : 𝔤) (v : ↥(π.kFiniteSubspace K_sub)),
      (kFiniteSubspace_kAction π K_sub) k (⁅X, v⁆) =
        ⁅Ad k X, (kFiniteSubspace_kAction π K_sub) k v⁆)
    (W : Submodule ℂ ↥(π.kFiniteSubspace K_sub))
    (hW : (harishChandraGKModule I π K_sub hadm 𝔤 𝔨 Ad ι hequiv).IsSubmodule W) :
    ∀ (g : G), (π.toMonoidHom g) ''
      ((π.kFiniteSubspace K_sub).subtype '' (W : Set ↥(π.kFiniteSubspace K_sub))) ⊆
      closure ((π.kFiniteSubspace K_sub).subtype '' (W : Set ↥(π.kFiniteSubspace K_sub))) := by
  intro g x hx

  obtain ⟨y, ⟨w', hw'W, rfl⟩, rfl⟩ := hx

  set S := (π.kFiniteSubspace K_sub).subtype '' (W : Set ↥(π.kFiniteSubspace K_sub)) with hS_def

  by_contra h_not_mem

  have hS_subspace : ∃ (M : Submodule ℂ F), (M : Set F) = S := by
    exact ⟨W.map (π.kFiniteSubspace K_sub).subtype, by
      simp only [Submodule.map_coe, hS_def]⟩


  obtain ⟨h, hh_vanish, hh_ne⟩ :=
    hahn_banach_separation_closed_subspace S
      ((π.toMonoidHom g) ((π.kFiniteSubspace K_sub).subtype w'))
      hS_subspace h_not_mem

  have h_zero : h ((π.toMonoidHom g) ((π.kFiniteSubspace K_sub).subtype w')) = 0 :=
    analytic_continuation_from_gInvariance I π K_sub hadm hG_ss hK_max
      𝔤 𝔨 Ad ι hequiv W hW w' hw'W h hh_vanish g

  exact hh_ne h_zero

theorem gkSubmodule_closure_isInvariant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    [SecondCountableTopology G]
    {F : Type uFw} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (hadm : @ContinuousRep.IsAdmissible.{_, uFw, uFw} _ _ _ _ _ _ _ _ π K_sub)
    (hG_ss : ContinuousRep.IsSemisimpleLieGroup I G)
    [CompactSpace K_sub] [T2Space K_sub]

    (hK_max : IsMaximalCompactSubgroup K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K_sub →* (𝔤 →ₗ[ℂ] 𝔤))
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    [LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)]
    (hequiv : ∀ (k : K_sub) (X : 𝔤) (v : ↥(π.kFiniteSubspace K_sub)),
      (kFiniteSubspace_kAction π K_sub) k (⁅X, v⁆) =
        ⁅Ad k X, (kFiniteSubspace_kAction π K_sub) k v⁆)
    (W : Submodule ℂ ↥(π.kFiniteSubspace K_sub))
    (hW : (harishChandraGKModule I π K_sub hadm 𝔤 𝔨 Ad ι hequiv).IsSubmodule W) :


    ∀ (g : G) (v : F),
      v ∈ closure ((π.kFiniteSubspace K_sub).subtype '' (W : Set ↥(π.kFiniteSubspace K_sub))) →
      (π.toMonoidHom g) v ∈
        closure ((π.kFiniteSubspace K_sub).subtype '' (W : Set ↥(π.kFiniteSubspace K_sub))) := by

  have hW_maps : ∀ (g : G), (π.toMonoidHom g) ''
      ((π.kFiniteSubspace K_sub).subtype '' (W : Set ↥(π.kFiniteSubspace K_sub))) ⊆
      closure ((π.kFiniteSubspace K_sub).subtype '' (W : Set ↥(π.kFiniteSubspace K_sub))) :=
    gkSubmodule_closure_isInvariant_analyticity_step I π K_sub hadm hG_ss hK_max 𝔤 𝔨 Ad ι hequiv W hW

  intro g v hv
  set S := (π.kFiniteSubspace K_sub).subtype '' (W : Set ↥(π.kFiniteSubspace K_sub))

  have hcont : Continuous (π.toMonoidHom g) := (π.toMonoidHom g).continuous

  have hmaps : (π.toMonoidHom g) '' S ⊆ closure S := hW_maps g

  have h1 : (π.toMonoidHom g) '' (closure S) ⊆ closure ((π.toMonoidHom g) '' S) :=
    image_closure_subset_closure_image hcont
  have h2 : closure ((π.toMonoidHom g) '' S) ⊆ closure (closure S) :=
    closure_mono hmaps
  have h3 : closure (closure S) = closure S := closure_closure
  have h4 : (π.toMonoidHom g) v ∈ (π.toMonoidHom g) '' (closure S) :=
    Set.mem_image_of_mem _ hv
  exact h3 ▸ h2 (h1 h4)

lemma subrep_orbit_image
    {G : Type*} [Group G] [TopologicalSpace G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (U : Submodule ℂ F) (hU : π.IsInvariantSubspace U) (v : ↥U) :
    U.subtype '' (Set.range (fun k : K_sub =>
      ((π.subrepresentation U hU).toMonoidHom k) v)) =
    Set.range (fun k : K_sub => (π.toMonoidHom k) (v : F)) := by
  ext x
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨y, ⟨k, hk⟩, hy⟩
    exact ⟨k, by simp only [Submodule.subtype_apply] at hy; rw [← hy, ← hk]; rfl⟩
  · rintro ⟨k, hk⟩
    refine ⟨((π.subrepresentation U hU).toMonoidHom k) v, ⟨k, rfl⟩, ?_⟩
    simp only [Submodule.subtype_apply]; rw [← hk]; rfl

lemma kFinite_subrep_to_full
    {G : Type*} [Group G] [TopologicalSpace G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (U : Submodule ℂ F) (hU : π.IsInvariantSubspace U)
    (v : ↥U) (hv : v ∈ ContinuousRep.kFiniteSubspace (π.subrepresentation U hU) K_sub) :
    (v : F) ∈ ContinuousRep.kFiniteSubspace π K_sub := by
  rw [ContinuousRep.mem_kFiniteSubspace] at hv ⊢
  unfold ContinuousRep.IsKFinite at hv ⊢
  have hmap : Submodule.map U.subtype
    (Submodule.span ℂ (Set.range (fun k : K_sub =>
      ((π.subrepresentation U hU).toMonoidHom k) v))) =
    Submodule.span ℂ (Set.range (fun k : K_sub => (π.toMonoidHom k) (v : F))) := by
    rw [Submodule.map_span, subrep_orbit_image]
  rw [← hmap]
  exact Module.Finite.map
    (Submodule.span ℂ (Set.range (fun k : K_sub =>
      ((π.subrepresentation U hU).toMonoidHom k) v)))
    U.subtype

lemma subrep_kFinite_image_subset
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G) [CompactSpace K_sub] [T2Space K_sub]

    (U : Submodule ℂ F) (hU : π.IsInvariantSubspace U) :
    U.subtype '' (ContinuousRep.kFiniteSubspace (π.subrepresentation U hU) K_sub : Set ↥U) ⊆
    ((π.kFiniteSubspace K_sub).subtype ''
      ((Submodule.comap (π.kFiniteSubspace K_sub).subtype U) :
        Set ↥(π.kFiniteSubspace K_sub))) := by
  intro x ⟨v, hv_kfin, hv_eq⟩
  have hx_kfin : x ∈ ContinuousRep.kFiniteSubspace π K_sub := by
    rw [← hv_eq]; exact kFinite_subrep_to_full π K_sub U hU v hv_kfin
  have hx_U : x ∈ (U : Set F) := by
    rw [← hv_eq]; exact v.2
  exact ⟨⟨x, hx_kfin⟩, hx_U, rfl⟩

theorem kFinite_dense_in_invariant_subspace
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (_hadm : π.IsAdmissible K_sub)
    [CompactSpace K_sub] [T2Space K_sub]

    (U : Submodule ℂ F) (hU : π.IsInvariantSubspace U) :
    closure ((π.kFiniteSubspace K_sub).subtype ''
      ((Submodule.comap (π.kFiniteSubspace K_sub).subtype U) :
        Set ↥(π.kFiniteSubspace K_sub))) = (U : Set F) := by
  apply Set.eq_of_subset_of_subset
  ·
    apply closure_minimal
    · intro x ⟨v, hv, hvx⟩
      rw [← hvx]; exact hv
    · exact hU.isClosed
  ·

    intro v hv

    obtain ⟨R, hR_kfin, hR_dirac, hR_pw⟩ :=
      ContinuousRep.measureRep_exists (π.subrepresentation U hU) K_sub


    suffices h : v ∈ closure (U.subtype ''
        (ContinuousRep.kFiniteSubspace (π.subrepresentation U hU) K_sub : Set ↥U)) by
      exact closure_mono (subrep_kFinite_image_subset π K_sub U hU) h


    have hdense : Dense (ContinuousRep.kFiniteSubspace (π.subrepresentation U hU) K_sub : Set ↥U) := by
      intro w
      rw [mem_closure_iff_nhds]
      intro N hN
      rw [mem_nhds_iff] at hN
      obtain ⟨t, htN, ht_open, hw_t⟩ := hN
      have ht_nhds : t ∈ nhds w := ht_open.mem_nhds hw_t
      obtain ⟨f, hft⟩ := hR_dirac w t ht_nhds
      have ht_nhds_Rf : t ∈ nhds (R f w) := ht_open.mem_nhds hft
      obtain ⟨g, hg_kfin, hgt⟩ := hR_pw f w t ht_nhds_Rf
      exact ⟨R g w, htN hgt, hR_kfin g w hg_kfin⟩
    have v_U_mem : (⟨v, hv⟩ : ↥U) ∈
      closure (ContinuousRep.kFiniteSubspace (π.subrepresentation U hU) K_sub : Set ↥U) :=
      hdense ⟨v, hv⟩
    have hcont : Continuous (U.subtype : ↥U → F) := continuous_subtype_val
    have := image_closure_subset_closure_image hcont ⟨⟨v, hv⟩, v_U_mem, rfl⟩
    simp only [Submodule.subtype_apply] at this
    exact this

theorem isotypic_projector_preserves_K_invariant_image
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (P : F →L[ℂ] F)
    (_hP_kfin : ∀ w, P w ∈ π.kFiniteSubspace K_sub)
    (_hP_comm : ∀ (k : K_sub), P.comp (π.toMonoidHom k) = (π.toMonoidHom k).comp P)
    (hP_preserves : ∀ (S : Submodule ℂ F),
      (∀ (k : K_sub) (s : F), s ∈ S → (π.toMonoidHom k) s ∈ S) →
      ∀ (s : F), s ∈ S → s ∈ π.kFiniteSubspace K_sub → P s ∈ S)

    (W : Submodule ℂ ↥(π.kFiniteSubspace K_sub))
    (hW_inv : ∀ (k : K_sub) (w : ↥(π.kFiniteSubspace K_sub)),
      w ∈ W → (kFiniteSubspace_kAction π K_sub) k w ∈ W) :
    ∀ w ∈ (π.kFiniteSubspace K_sub).subtype '' (W : Set ↥(π.kFiniteSubspace K_sub)),
      P w ∈ (π.kFiniteSubspace K_sub).subtype '' (W : Set ↥(π.kFiniteSubspace K_sub)) := by
  intro w ⟨w', hw'_mem, hw'_eq⟩
  subst hw'_eq


  set S := W.map (π.kFiniteSubspace K_sub).subtype with hS_def
  have hS_kstable : ∀ (k : K_sub) (s : F), s ∈ S → (π.toMonoidHom k) s ∈ S := by
    intro k s hs
    rw [hS_def, Submodule.mem_map] at hs ⊢
    obtain ⟨u, hu_mem, hu_eq⟩ := hs
    refine ⟨(kFiniteSubspace_kAction π K_sub) k u, hW_inv k u hu_mem, ?_⟩
    subst hu_eq

    rfl
  have hw'_S : (w' : F) ∈ S := by
    rw [hS_def, Submodule.mem_map]
    exact ⟨w', hw'_mem, rfl⟩
  have hw'_kfin : (w' : F) ∈ π.kFiniteSubspace K_sub := w'.property
  have hPw_S := hP_preserves S hS_kstable (w' : F) hw'_S hw'_kfin

  rw [hS_def, Submodule.mem_map] at hPw_S
  obtain ⟨v, hv_mem, hv_eq⟩ := hPw_S
  exact ⟨v, hv_mem, hv_eq⟩

theorem isotypic_projector_image_closed
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (P : F →L[ℂ] F)
    (hP_fin : FiniteDimensional ℂ (LinearMap.range P.toLinearMap))
    (W : Submodule ℂ ↥(π.kFiniteSubspace K_sub)) :
    IsClosed (P '' ((π.kFiniteSubspace K_sub).subtype '' (W : Set ↥(π.kFiniteSubspace K_sub))) : Set F) := by

  have h_eq : P '' ((π.kFiniteSubspace K_sub).subtype '' (W : Set ↥(π.kFiniteSubspace K_sub))) =
      (((W.map (π.kFiniteSubspace K_sub).subtype).map P.toLinearMap : Submodule ℂ F) : Set F) := by
    ext x; simp
  rw [h_eq]

  have h_le : (W.map (π.kFiniteSubspace K_sub).subtype).map P.toLinearMap ≤
      LinearMap.range P.toLinearMap := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := Submodule.mem_map.mp hx
    exact LinearMap.mem_range.mpr ⟨y, rfl⟩
  haveI : FiniteDimensional ℂ ((W.map (π.kFiniteSubspace K_sub).subtype).map P.toLinearMap) :=
    Submodule.finiteDimensional_of_le h_le
  exact Submodule.closed_of_finiteDimensional _

theorem kFinite_isotypic_decomposition_with_invariance
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (hadm : π.IsAdmissible K_sub)
    [CompactSpace K_sub] [T2Space K_sub]

    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K_sub →* (𝔤 →ₗ[ℂ] 𝔤))
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    [LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)]
    (hequiv : ∀ (k : K_sub) (X : 𝔤) (v : ↥(π.kFiniteSubspace K_sub)),
      (kFiniteSubspace_kAction π K_sub) k (⁅X, v⁆) =
        ⁅Ad k X, (kFiniteSubspace_kAction π K_sub) k v⁆)
    (W : Submodule ℂ ↥(π.kFiniteSubspace K_sub))
    (hW : (harishChandraGKModule I π K_sub hadm 𝔤 𝔨 Ad ι hequiv).IsSubmodule W)
    (v : ↥(π.kFiniteSubspace K_sub)) :
    ∃ (n : ℕ) (Ps : Fin n → F →L[ℂ] F),

      (∀ i, ∀ w : F, Ps i w ∈ π.kFiniteSubspace K_sub) ∧

      (v : F) = ∑ i : Fin n, Ps i (v : F) ∧

      (∀ i, ∀ w ∈ (π.kFiniteSubspace K_sub).subtype '' (W : Set ↥(π.kFiniteSubspace K_sub)),
        Ps i w ∈ (π.kFiniteSubspace K_sub).subtype '' (W : Set ↥(π.kFiniteSubspace K_sub))) ∧

      (∀ i, IsClosed (Ps i '' ((π.kFiniteSubspace K_sub).subtype '' (W : Set ↥(π.kFiniteSubspace K_sub))) : Set F)) := by

  have hv_mem : (v : F) ∈ π.kFiniteSubspace K_sub := (π.kFiniteSubspace K_sub).coe_mem v
  obtain ⟨P, hP_findim, hP_fix, hP_comm, _hP_preserves⟩ :=
    isotypicProjector_finiteRange_fix_commute π K_sub (v : F) hv_mem

  have hP_kfin : ∀ w, P w ∈ π.kFiniteSubspace K_sub :=
    kEquivariant_finiteRange_maps_to_kFinite π K_sub P hP_findim hP_comm

  refine ⟨1, fun _ => P, ?_, ?_, ?_, ?_⟩

  · intro _ w; exact hP_kfin w

  · simp [hP_fix]

  · intro _ w hw
    exact isotypic_projector_preserves_K_invariant_image π K_sub P hP_kfin hP_comm _hP_preserves W
      hW.group_invariant w hw


  · intro _
    exact isotypic_projector_image_closed π K_sub P hP_findim W

theorem closure_gkSubmodule_kfinite_subset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (hadm : π.IsAdmissible K_sub)
    [CompactSpace K_sub] [T2Space K_sub]

    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K_sub →* (𝔤 →ₗ[ℂ] 𝔤))
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    [LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)]
    (hequiv : ∀ (k : K_sub) (X : 𝔤) (v : ↥(π.kFiniteSubspace K_sub)),
      (kFiniteSubspace_kAction π K_sub) k (⁅X, v⁆) =
        ⁅Ad k X, (kFiniteSubspace_kAction π K_sub) k v⁆)
    (W : Submodule ℂ ↥(π.kFiniteSubspace K_sub))
    (hW : (harishChandraGKModule I π K_sub hadm 𝔤 𝔨 Ad ι hequiv).IsSubmodule W)
    (v : ↥(π.kFiniteSubspace K_sub))
    (hv : (v : F) ∈ closure ((π.kFiniteSubspace K_sub).subtype ''
      (W : Set ↥(π.kFiniteSubspace K_sub)))) :
    v ∈ W := by

  obtain ⟨n, Ps, hPs_kfin, hv_sum, hPs_maps_W, hPs_closed⟩ :=
    kFinite_isotypic_decomposition_with_invariance I π K_sub hadm 𝔤 𝔨 Ad ι hequiv W hW v
  set W_image := (π.kFiniteSubspace K_sub).subtype '' (W : Set ↥(π.kFiniteSubspace K_sub))
    with hW_image_def


  have hPs_in_W_image : ∀ i : Fin n, Ps i (v : F) ∈ W_image := by
    intro i

    have hPv_closure : Ps i (v : F) ∈ closure (Ps i '' W_image) :=
      image_closure_subset_closure_image (Ps i).continuous ⟨(v : F), hv, rfl⟩

    have hPs_sub : Ps i '' W_image ⊆ W_image := by
      rintro y ⟨w, hw_mem, rfl⟩
      exact hPs_maps_W i w hw_mem

    rw [(hPs_closed i).closure_eq] at hPv_closure
    exact hPs_sub hPv_closure

  choose wi hwi_mem hwi_eq using (fun i => hPs_in_W_image i :
    ∀ i : Fin n, Ps i (v : F) ∈ W_image)

  have hv_eq_sum : (v : F) = ∑ i : Fin n, (π.kFiniteSubspace K_sub).subtype (wi i) := by
    simp only [hwi_eq]
    exact hv_sum
  have hv_eq_sum_kfin : v = ∑ i : Fin n, wi i := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.subtype_apply] at hv_eq_sum ⊢
    exact hv_eq_sum

  rw [hv_eq_sum_kfin]
  exact W.sum_mem (fun i _ => hwi_mem i)

theorem subrep_gkSubmodule_bijection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (hadm : π.IsAdmissible K_sub)
    [CompactSpace K_sub] [T2Space K_sub]

    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K_sub →* (𝔤 →ₗ[ℂ] 𝔤))
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    [LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)]
    (hequiv : ∀ (k : K_sub) (X : 𝔤) (v : ↥(π.kFiniteSubspace K_sub)),
      (kFiniteSubspace_kAction π K_sub) k (⁅X, v⁆) =
        ⁅Ad k X, (kFiniteSubspace_kAction π K_sub) k v⁆) :

    (∀ (U : Submodule ℂ F), π.IsInvariantSubspace U →
      closure ((π.kFiniteSubspace K_sub).subtype ''
        ((Submodule.comap (π.kFiniteSubspace K_sub).subtype U) :
          Set ↥(π.kFiniteSubspace K_sub))) = (U : Set F))
    ∧


    (∀ (W : Submodule ℂ ↥(π.kFiniteSubspace K_sub)),
      (harishChandraGKModule I π K_sub hadm 𝔤 𝔨 Ad ι hequiv).IsSubmodule W →
      ∀ (v : ↥(π.kFiniteSubspace K_sub)),
        v ∈ W ↔
        (v : F) ∈ closure ((π.kFiniteSubspace K_sub).subtype ''
          (W : Set ↥(π.kFiniteSubspace K_sub))))
    ∧

    (∀ (U₁ U₂ : Submodule ℂ F), π.IsInvariantSubspace U₁ → π.IsInvariantSubspace U₂ →
      Submodule.comap (π.kFiniteSubspace K_sub).subtype U₁ =
        Submodule.comap (π.kFiniteSubspace K_sub).subtype U₂ →
      U₁ = U₂) := by
  refine ⟨?_, ?_, ?_⟩
  ·


    intro U hU
    exact kFinite_dense_in_invariant_subspace π K_sub hadm U hU
  ·


    intro W hW v
    constructor
    ·
      intro hv_mem
      exact subset_closure ⟨v, hv_mem, rfl⟩
    ·

      intro hv_closure
      exact closure_gkSubmodule_kfinite_subset I π K_sub hadm 𝔤 𝔨 Ad ι hequiv W hW v hv_closure
  ·


    intro U₁ U₂ hU₁ hU₂ heq
    have h1 := kFinite_dense_in_invariant_subspace π K_sub hadm U₁ hU₁
    have h2 := kFinite_dense_in_invariant_subspace π K_sub hadm U₂ hU₂

    have : (U₁ : Set F) = (U₂ : Set F) := by rw [← h1, ← h2]; congr 1; simp [heq]
    exact SetLike.coe_injective this

def ContinuousRep.IsFiniteLength
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (π : ContinuousRep G V) : Prop :=
  ∃ (n : ℕ) (chain : Fin (n + 1) → Submodule ℂ V),
    chain ⟨0, Nat.zero_lt_succ n⟩ = ⊥ ∧
    chain ⟨n, Nat.lt_succ_iff.mpr (le_refl n)⟩ = ⊤ ∧
    (∀ (i : Fin n), chain i.castSucc < chain i.succ) ∧
    (∀ (i : Fin n), π.IsInvariantSubspace (chain i.castSucc)) ∧
    (∀ (i : Fin n), π.IsInvariantSubspace (chain i.succ)) ∧


    (∀ (i : Fin n) (W : Submodule ℂ V), π.IsInvariantSubspace W →
      chain i.castSucc ≤ W → W ≤ chain i.succ →
      W = chain i.castSucc ∨ W = chain i.succ)


theorem kFiniteSubspace_finiteLength_of_rep_finiteLength
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (hadm : π.IsAdmissible K_sub)
    [CompactSpace K_sub] [T2Space K_sub]

    (hfl : π.IsFiniteLength)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K_sub →* (𝔤 →ₗ[ℂ] 𝔤))
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    [LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)]
    (hequiv : ∀ (k : K_sub) (X : 𝔤) (v : ↥(π.kFiniteSubspace K_sub)),
      (kFiniteSubspace_kAction π K_sub) k (⁅X, v⁆) =
        ⁅Ad k X, (kFiniteSubspace_kAction π K_sub) k v⁆)
    (hι_compat : ∀ (X : 𝔤) (w : ↥(π.kFiniteSubspace K_sub)),
      (π.kFiniteSubspace K_sub).subtype ⁅X, w⁆ = ι X ((π.kFiniteSubspace K_sub).subtype w))
    (_hι_preserves : ∀ (U : Submodule ℂ F), π.IsInvariantSubspace U →
      ∀ (X : 𝔤) (v : F), v ∈ U → ι X v ∈ U) :
    (harishChandraGKModule I π K_sub hadm 𝔤 𝔨 Ad ι hequiv).IsFiniteLength := by

  set M := harishChandraGKModule I π K_sub hadm 𝔤 𝔨 Ad ι hequiv
  obtain ⟨hbij_fwd, hbij_inv, hbij_inj⟩ :=
    gkSubmodule_closure_correspondence I π K_sub hadm 𝔤 𝔨 Ad ι hequiv hι_compat

  obtain ⟨n, chain, h0, hn, hlt, hinv_cast, hinv_succ, hirr⟩ := hfl

  let chain' : Fin (n + 1) → Submodule ℂ ↥(π.kFiniteSubspace K_sub) :=
    fun i => Submodule.comap (π.kFiniteSubspace K_sub).subtype (chain i)


  refine ⟨n, chain', ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    show Submodule.comap (π.kFiniteSubspace K_sub).subtype (chain ⟨0, _⟩) = ⊥
    rw [h0]
    ext ⟨v, hv⟩
    simp [Submodule.mem_bot]
  ·
    show Submodule.comap (π.kFiniteSubspace K_sub).subtype (chain ⟨n, _⟩) = ⊤
    rw [hn]
    ext ⟨v, hv⟩
    simp [Submodule.mem_top]
  ·
    intro i


    have hle : chain' ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ≤
               chain' ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ := by
      intro ⟨v, hv⟩ hmem
      show v ∈ chain ⟨i.val + 1, _⟩
      exact (hlt i).le hmem
    have hne : chain' ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ ≠
               chain' ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ := by
      intro heq


      have := hbij_inj (chain i.castSucc) (chain i.succ) (hinv_cast i) (hinv_succ i) heq
      exact (ne_of_lt (hlt i)) this
    exact lt_of_le_of_ne hle hne
  ·
    intro i
    exact hbij_fwd (chain i.castSucc) (hinv_cast i)
  ·
    intro i
    exact hbij_fwd (chain i.succ) (hinv_succ i)
  ·
    intro i W hW hW_lo hW_hi

    obtain ⟨U, hU_inv, hU_eq⟩ := hbij_inv W hW


    have hU_lo : chain i.castSucc ≤ U := by
      rw [← kFinite_dense_in_invariant_subspace_submodule I π K_sub hadm
            (chain i.castSucc) (hinv_cast i)]
      rw [← kFinite_dense_in_invariant_subspace_submodule I π K_sub hadm U hU_inv]
      apply Submodule.topologicalClosure_mono
      apply Submodule.map_mono
      rw [hU_eq]
      exact hW_lo
    have hU_hi : U ≤ chain i.succ := by
      rw [← kFinite_dense_in_invariant_subspace_submodule I π K_sub hadm U hU_inv]
      rw [← kFinite_dense_in_invariant_subspace_submodule I π K_sub hadm
            (chain i.succ) (hinv_succ i)]
      apply Submodule.topologicalClosure_mono
      apply Submodule.map_mono
      rw [hU_eq]
      exact hW_hi

    rcases hirr i U hU_inv hU_lo hU_hi with heq_lo | heq_hi
    · left
      rw [← hU_eq, heq_lo]
      rfl
    · right
      rw [← hU_eq, heq_hi]
      rfl

theorem GKModule.finiteLength_finitelyGenerated
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (hfl : M.IsFiniteLength) :
    ∃ (S : Finset V), ∀ v : V,
      v ∈ Submodule.span ℂ
        (⋃ (s : V) (_ : s ∈ S) (Xs : List 𝔤),
          ({GKModule.lieIterate Xs s} : Set V)) := by
  classical

  obtain ⟨n, chain, h0, hn, hlt, hsub_i, hsub_si, hirr⟩ := hfl

  have hexists_vi : ∀ (i : Fin n),
      ∃ v : V, v ∈ chain ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ ∧
              v ∉ chain ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩ := by
    intro i
    have hi := hlt i
    rw [SetLike.lt_iff_le_and_exists] at hi
    exact hi.2
  choose vi hvi_in hvi_nin using hexists_vi

  have hkorbit_fg : ∀ (i : Fin n),
      (Submodule.span ℂ (Set.range (fun k : K => M.σ k (vi i)))).FG := by
    intro i
    rw [Submodule.fg_iff_finiteDimensional]
    exact M.locallyFinite (vi i)

  choose Bi hBi using fun i => (hkorbit_fg i)

  use Finset.univ.biUnion Bi

  set TS := Submodule.span ℂ
      (⋃ (s : V) (_ : s ∈ Finset.univ.biUnion Bi) (Xs : List 𝔤),
        ({GKModule.lieIterate Xs s} : Set V)) with hTS_def

  have hmem_gen : ∀ (s : V) (Xs : List 𝔤), s ∈ Finset.univ.biUnion Bi →
      GKModule.lieIterate Xs s ∈ TS := by
    intro s Xs hs
    apply Submodule.subset_span
    simp only [Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨s, Finset.mem_coe.mpr hs, Xs, rfl⟩

  have hS_sub_TS : ∀ s, s ∈ Finset.univ.biUnion Bi → s ∈ TS := by
    intro s hs; exact hmem_gen s [] hs

  have hBi_sub_TS : ∀ (i : Fin n), (Submodule.span ℂ ↑(Bi i) : Submodule ℂ V) ≤ TS := by
    intro i
    apply Submodule.span_le.mpr
    intro w hw
    exact hS_sub_TS w (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hw⟩)

  have hvi_in_TS : ∀ (i : Fin n), vi i ∈ TS := by
    intro i
    have h1 : vi i ∈ Submodule.span ℂ (Set.range (fun k : K => M.σ k (vi i))) := by
      apply Submodule.subset_span
      exact ⟨1, by simp [map_one]⟩
    rw [← hBi i] at h1
    exact hBi_sub_TS i h1

  have hTS_lie : ∀ (X : 𝔤) (w : V), w ∈ TS → ⁅X, w⁆ ∈ TS := by
    intro X w hw
    induction hw using Submodule.span_induction with
    | mem u hu =>
      simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hu
      obtain ⟨s, hs, Xs, rfl⟩ := hu
      exact hmem_gen s (X :: Xs) hs
    | zero => simp [lie_zero]
    | add x y _ _ hx hy => rw [lie_add]; exact TS.add_mem hx hy
    | smul c x _ hx => rw [lie_smul]; exact TS.smul_mem c hx

  have hS_Kstable : ∀ (k : K) (s : V), s ∈ Finset.univ.biUnion Bi → M.σ k s ∈ TS := by
    intro k s hs
    rw [Finset.mem_biUnion] at hs
    obtain ⟨i, _, hs_in_Bi⟩ := hs


    have hs_korbit : s ∈ Submodule.span ℂ (Set.range (fun k' : K => M.σ k' (vi i))) := by
      rw [← hBi i]; exact Submodule.subset_span (Finset.mem_coe.mpr hs_in_Bi)
    have hks_korbit : M.σ k s ∈ Submodule.span ℂ (Set.range (fun k' : K => M.σ k' (vi i))) := by

      have hle : Submodule.map (M.σ k) (Submodule.span ℂ (Set.range (fun k' : K => M.σ k' (vi i)))) ≤
          Submodule.span ℂ (Set.range (fun k' : K => M.σ k' (vi i))) := by
        rw [Submodule.map_span_le]
        intro u ⟨k', hk'⟩
        subst hk'
        exact Submodule.subset_span ⟨k * k', by simp [map_mul]⟩
      exact hle (Submodule.mem_map_of_mem hs_korbit)

    rw [← hBi i] at hks_korbit
    exact hBi_sub_TS i hks_korbit

  have hTS_K : ∀ (k : K) (w : V), w ∈ TS → M.σ k w ∈ TS := by
    intro k w hw
    induction hw using Submodule.span_induction with
    | mem u hu =>
      simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hu
      obtain ⟨s, hs, Xs, rfl⟩ := hu

      induction Xs with
      | nil =>
        simp only [GKModule.lieIterate, List.foldr_nil]
        exact hS_Kstable k s hs
      | cons X Xs' ihXs =>
        simp only [GKModule.lieIterate, List.foldr_cons]
        rw [M.equivariance k X (List.foldr (fun X acc => ⁅X, acc⁆) s Xs')]
        exact hTS_lie _ _ ihXs
    | zero => simp [map_zero]
    | add x y _ _ hx hy => rw [map_add]; exact TS.add_mem hx hy
    | smul c x _ hx => rw [LinearMap.map_smul]; exact TS.smul_mem c hx

  have hTS_sub : M.IsSubmodule TS := ⟨hTS_lie, hTS_K⟩

  suffices h_chain : ∀ (j : Fin (n + 1)), chain j ≤ TS by
    intro v
    have hv_top : v ∈ (⊤ : Submodule ℂ V) := Submodule.mem_top
    rw [← hn] at hv_top
    exact h_chain ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ hv_top
  intro ⟨j, hj⟩
  induction j with
  | zero =>
    show chain ⟨0, _⟩ ≤ TS
    rw [h0]; exact bot_le
  | succ j' ih =>
    have hj'_lt_n : j' < n := Nat.lt_of_succ_lt_succ hj
    have ih_j' : chain ⟨j', Nat.lt_succ_of_lt hj'_lt_n⟩ ≤ TS :=
      ih (Nat.lt_succ_of_lt hj'_lt_n)

    set W := TS ⊓ chain ⟨j' + 1, hj⟩
    have hW_sub : M.IsSubmodule W := by
      exact ⟨fun X w hw => Submodule.mem_inf.mpr
        ⟨hTS_lie X w (Submodule.mem_inf.mp hw).1,
         (hsub_si ⟨j', hj'_lt_n⟩).lie_invariant X w (Submodule.mem_inf.mp hw).2⟩,
       fun k w hw => Submodule.mem_inf.mpr
        ⟨hTS_K k w (Submodule.mem_inf.mp hw).1,
         (hsub_si ⟨j', hj'_lt_n⟩).group_invariant k w (Submodule.mem_inf.mp hw).2⟩⟩
    have hchain_le_W : chain ⟨j', Nat.lt_succ_of_lt hj'_lt_n⟩ ≤ W := by
      intro w hw
      exact Submodule.mem_inf.mpr ⟨ih_j' hw, (hlt ⟨j', hj'_lt_n⟩).le hw⟩
    have hW_le_chain : W ≤ chain ⟨j' + 1, hj⟩ := inf_le_right

    have hvi_in_W : vi ⟨j', hj'_lt_n⟩ ∈ W :=
      Submodule.mem_inf.mpr ⟨hvi_in_TS ⟨j', hj'_lt_n⟩, hvi_in ⟨j', hj'_lt_n⟩⟩

    have hW_ne : W ≠ chain ⟨j', Nat.lt_succ_of_lt hj'_lt_n⟩ := by
      intro heq; exact hvi_nin ⟨j', hj'_lt_n⟩ (heq ▸ hvi_in_W)

    rcases hirr ⟨j', hj'_lt_n⟩ W hW_sub hchain_le_W hW_le_chain with h_low | h_high
    · exact absurd h_low hW_ne
    ·
      show chain ⟨j' + 1, hj⟩ ≤ TS
      rw [← h_high]
      exact inf_le_left

theorem finiteLength_implies_harishChandraModule
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (hadm : π.IsAdmissible K_sub)
    [CompactSpace K_sub] [T2Space K_sub]

    (hfl : π.IsFiniteLength)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K_sub →* (𝔤 →ₗ[ℂ] 𝔤))
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    [LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)]
    (hequiv : ∀ (k : K_sub) (X : 𝔤) (v : ↥(π.kFiniteSubspace K_sub)),
      (kFiniteSubspace_kAction π K_sub) k (⁅X, v⁆) =
        ⁅Ad k X, (kFiniteSubspace_kAction π K_sub) k v⁆)
    (hι_compat : ∀ (X : 𝔤) (w : ↥(π.kFiniteSubspace K_sub)),
      (π.kFiniteSubspace K_sub).subtype ⁅X, w⁆ = ι X ((π.kFiniteSubspace K_sub).subtype w))
    (hι_preserves : ∀ (U : Submodule ℂ F), π.IsInvariantSubspace U →
      ∀ (X : 𝔤) (v : F), v ∈ U → ι X v ∈ U) :
    (harishChandraGKModule I π K_sub hadm 𝔤 𝔨 Ad ι hequiv).IsHarishChandraModule := by
  set M := harishChandraGKModule I π K_sub hadm 𝔤 𝔨 Ad ι hequiv

  have hadm_gk : M.IsAdmissible :=
    harishChandraGKModule_isAdmissible I π K_sub hadm 𝔤 𝔨 Ad ι hequiv

  have hfl_gk : M.IsFiniteLength :=
    kFiniteSubspace_finiteLength_of_rep_finiteLength I π K_sub hadm hfl 𝔤 𝔨 Ad ι hequiv hι_compat hι_preserves

  have hfg := GKModule.finiteLength_finitelyGenerated M hfl_gk
  exact ⟨hadm_gk, hfg⟩

end
