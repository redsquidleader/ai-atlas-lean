/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.Admissible
import Atlas.LieGroups.code.GKModule
import Atlas.LieGroups.code.GKModuleDefs
import Atlas.LieGroups.code.SmoothVectors
import Atlas.LieGroups.code.KFiniteProps

noncomputable section

set_option autoImplicit false

open scoped Manifold

@[reducible]
def kFiniteSubspace_lieRingModule
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (_hadm : π.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    (hι_stable : ∀ (X : 𝔤) (v : F),
      v ∈ π.kFiniteSubspace K_sub → (ι X) v ∈ π.kFiniteSubspace K_sub) :
    LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub) :=
  letI : Bracket 𝔤 ↥(π.kFiniteSubspace K_sub) :=
    ⟨fun X v => ⟨(ι X) v.val, hι_stable X v.val v.prop⟩⟩
  { add_lie := fun x y m => by
      apply Subtype.ext
      show (ι (x + y)) m.val = (ι x) m.val + (ι y) m.val
      simp [map_add, LinearMap.add_apply]
    lie_add := fun x m n => by
      apply Subtype.ext
      show (ι x) (m.val + n.val) = (ι x) m.val + (ι x) n.val
      simp [map_add]
    leibniz_lie := fun x y m => by
      apply Subtype.ext
      show (ι x) ((ι y) m.val) = (ι ⁅x, y⁆) m.val + (ι y) ((ι x) m.val)
      rw [ι.map_lie x y, Ring.lie_def]; simp [LinearMap.sub_apply] }

@[reducible]
def kFiniteSubspace_lieModule
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (_hadm : π.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    (hι_stable : ∀ (X : 𝔤) (v : F),
      v ∈ π.kFiniteSubspace K_sub → (ι X) v ∈ π.kFiniteSubspace K_sub) :
    @LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub) _ _ _ _ _
      (kFiniteSubspace_lieRingModule I π K_sub _hadm 𝔤 ι hι_stable) :=
  @LieModule.mk ℂ 𝔤 ↥(π.kFiniteSubspace K_sub) _ _ _ _ _
    (kFiniteSubspace_lieRingModule I π K_sub _hadm 𝔤 ι hι_stable)
    (fun t x m => by
      apply Subtype.ext
      show (ι (t • x)) m.val = t • ((ι x) m.val)
      simp [map_smul, LinearMap.smul_apply])
    (fun t x m => by
      apply Subtype.ext
      show (ι x) (t • m.val) = t • ((ι x) m.val)
      simp [map_smul])

def kFiniteSubspace_kAction
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G) :
    Representation ℂ K_sub ↥(π.kFiniteSubspace K_sub) where
  toFun k :=
  { toFun := fun ⟨v, hv⟩ =>
      ⟨(π.toMonoidHom k) v,
       ContinuousRep.kFiniteSubspace_stable π K_sub k v hv⟩
    map_add' := fun ⟨v, _⟩ ⟨w, _⟩ => by
      ext; simp [map_add]
    map_smul' := fun c ⟨v, _⟩ => by
      ext; simp [map_smul] }
  map_one' := by
    ext ⟨v, _⟩; simp
  map_mul' := fun k₁ k₂ => by
    ext ⟨v, _⟩; simp

theorem kFiniteSubspace_kAction_locallyFinite
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G) :
    (kFiniteSubspace_kAction π K_sub).IsLocallyFinite := by
  intro ⟨v, hv⟩


  set σ := kFiniteSubspace_kAction π K_sub
  set S_VK := Submodule.span ℂ (Set.range (fun k : K_sub => σ k ⟨v, hv⟩))
  set S_F := Submodule.span ℂ (Set.range (fun k : K_sub => (π.toMonoidHom k) v))

  have hmap : S_VK.map (π.kFiniteSubspace K_sub).subtype ≤ S_F := by
    rw [Submodule.map_span]
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨⟨w, hw⟩, hk, rfl⟩ := hx
    obtain ⟨k, hk'⟩ := hk
    simp only [Submodule.subtype_apply]
    have : w = (π.toMonoidHom k) v := (congr_arg Subtype.val hk').symm
    rw [this]
    exact Submodule.subset_span ⟨k, rfl⟩

  haveI : FiniteDimensional ℂ S_F := hv

  haveI : FiniteDimensional ℂ (S_VK.map (π.kFiniteSubspace K_sub).subtype) :=
    Module.Finite.of_injective (Submodule.inclusion hmap) (Submodule.inclusion_injective hmap)

  exact Module.Finite.of_injective
    (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) S_VK).toLinearMap
    (LinearEquiv.injective _)

def harishChandraGKModule
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (_hadm : π.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K_sub →* (𝔤 →ₗ[ℂ] 𝔤))
    (_ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    [LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)]
    (hequiv : ∀ (k : K_sub) (X : 𝔤) (v : ↥(π.kFiniteSubspace K_sub)),
      (kFiniteSubspace_kAction π K_sub) k (⁅X, v⁆) =
        ⁅Ad k X, (kFiniteSubspace_kAction π K_sub) k v⁆) :
    GKModule 𝔤 K_sub 𝔨 Ad ↥(π.kFiniteSubspace K_sub) where
  σ := kFiniteSubspace_kAction π K_sub
  locallyFinite := kFiniteSubspace_kAction_locallyFinite π K_sub
  diffσ := (LieModule.toEnd ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)).toLinearMap.comp 𝔨.incl.toLinearMap
  diff_eq_lie := fun X v => by
    rfl
  equivariance := hequiv


theorem peterWeyl_isotypic_embedding
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K_sub →* (𝔤 →ₗ[ℂ] 𝔤)}
    [LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)]
    (M : GKModule 𝔤 K_sub 𝔨 Ad ↥(π.kFiniteSubspace K_sub))
    (hMσ : M.σ = kFiniteSubspace_kAction π K_sub)
    (W₀ : Submodule ℂ ↥(π.kFiniteSubspace K_sub))
    (hW₀ : M.IsKIrreducible W₀) :
    ∃ (Wσ : Type*) (_ : AddCommGroup Wσ) (_ : Module ℂ Wσ) (_ : TopologicalSpace Wσ)
      (σ : ContinuousRep K_sub Wσ) (_ : σ.IsIrreducible),
      (M.KIsotypicComponent W₀ hW₀).map (π.kFiniteSubspace K_sub).subtype ≤
        π.IsotypicComponent K_sub σ := by sorry

theorem harishChandraGKModule_isAdmissible
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (hadm : π.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K_sub →* (𝔤 →ₗ[ℂ] 𝔤))
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    [LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)]
    (hequiv : ∀ (k : K_sub) (X : 𝔤) (v : ↥(π.kFiniteSubspace K_sub)),
      (kFiniteSubspace_kAction π K_sub) k (⁅X, v⁆) =
        ⁅Ad k X, (kFiniteSubspace_kAction π K_sub) k v⁆) :
    (harishChandraGKModule I π K_sub hadm 𝔤 𝔨 Ad ι hequiv).IsAdmissible := by
  set M := harishChandraGKModule I π K_sub hadm 𝔤 𝔨 Ad ι hequiv
  intro W₀ hW₀


  have hMσ : M.σ = kFiniteSubspace_kAction π K_sub := rfl
  obtain ⟨Wσ, hACG, hMod, hTop, σ, hσirr, hembed⟩ :=
    peterWeyl_isotypic_embedding π K_sub M hMσ W₀ hW₀

  haveI : FiniteDimensional ℂ (π.IsotypicComponent K_sub σ) :=
    hadm Wσ σ hσirr

  set ιmap := (π.kFiniteSubspace K_sub).subtype
  set IC_image := (M.KIsotypicComponent W₀ hW₀).map ιmap
  haveI : FiniteDimensional ℂ IC_image :=
    Module.Finite.of_injective (Submodule.inclusion hembed)
      (Submodule.inclusion_injective hembed)

  exact Module.Finite.of_injective
    (Submodule.equivMapOfInjective ιmap (Submodule.injective_subtype _)
      (M.KIsotypicComponent W₀ hW₀)).toLinearMap
    (LinearEquiv.injective _)

theorem kFiniteSubspace_dense_admissible
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    [CompactSpace K_sub]
    (hadm : π.IsAdmissible K_sub) :
    Dense (π.kFiniteSubspace K_sub : Set F) := by


  obtain ⟨R, hR_kfin, hR_dirac, hR_pw⟩ :=
    ContinuousRep.measureRep_exists π K_sub
  intro v
  rw [mem_closure_iff_nhds]
  intro U hU
  rw [mem_nhds_iff] at hU
  obtain ⟨t, htU, ht_open, hv_t⟩ := hU

  have ht_nhds_v : t ∈ nhds v := ht_open.mem_nhds hv_t
  obtain ⟨f, hft⟩ := hR_dirac v t ht_nhds_v

  have ht_nhds_Rfv : t ∈ nhds (R f v) := ht_open.mem_nhds hft

  obtain ⟨g, hg_kfin, hgt⟩ := hR_pw f v t ht_nhds_Rfv

  have hRg_kfin : R g v ∈ (π.kFiniteSubspace K_sub : Set F) := hR_kfin g v hg_kfin

  exact ⟨R g v, htU hgt, hRg_kfin⟩

def iterLieAction
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {F : Type*} [AddCommGroup F] [Module ℂ F]
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F)) (Xs : List 𝔤) (v : F) : F :=
  Xs.foldr (fun X w => (ι X) w) v

lemma iterLieAction_mem_kFiniteSubspace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    (hι_stable : ∀ (X : 𝔤) (w : F), w ∈ π.kFiniteSubspace K_sub →
      (ι X) w ∈ π.kFiniteSubspace K_sub)
    (Xs : List 𝔤) (v : F) (hv : v ∈ π.kFiniteSubspace K_sub) :
    iterLieAction ι Xs v ∈ π.kFiniteSubspace K_sub := by
  induction Xs with
  | nil => exact hv
  | cons X rest ih =>
    simp only [iterLieAction, List.foldr_cons]
    exact hι_stable X _ ih

lemma iterLieAction_agree_of_eq_on_kFinite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (ι₁ ι₂ : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    (hlie_eq : ∀ (X : 𝔤) (w : F), w ∈ π.kFiniteSubspace K_sub →
      (ι₁ X) w = (ι₂ X) w)
    (hι₁_stable : ∀ (X : 𝔤) (w : F), w ∈ π.kFiniteSubspace K_sub →
      (ι₁ X) w ∈ π.kFiniteSubspace K_sub)
    (hι₂_stable : ∀ (X : 𝔤) (w : F), w ∈ π.kFiniteSubspace K_sub →
      (ι₂ X) w ∈ π.kFiniteSubspace K_sub)
    (Xs : List 𝔤) (v : F) (hv : v ∈ π.kFiniteSubspace K_sub) :
    iterLieAction ι₁ Xs v = iterLieAction ι₂ Xs v := by
  induction Xs with
  | nil => rfl
  | cons X rest ih =>
    show (ι₁ X) (iterLieAction ι₁ rest v) = (ι₂ X) (iterLieAction ι₂ rest v)
    rw [ih, hlie_eq X _ (iterLieAction_mem_kFiniteSubspace I π K_sub 𝔤 ι₂ hι₂_stable rest v hv)]

theorem elliptic_regularity_analytic_continuation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π₁ π₂ : ContinuousRep G F) (K_sub : Subgroup G)
    [CompactSpace K_sub]
    (_hadm₁ : π₁.IsAdmissible K_sub) (_hadm₂ : π₂.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (ι₁ ι₂ : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    (v : F) (_hv : v ∈ π₁.kFiniteSubspace K_sub)
    (h : F →L[ℂ] ℂ)
    (hiter_eq : ∀ (Xs : List 𝔤),
      h (iterLieAction ι₁ Xs v) = h (iterLieAction ι₂ Xs v))
    (g : G) : h ((π₁.toMonoidHom g) v) = h ((π₂.toMonoidHom g) v) := by sorry

theorem analytic_matcoeff_eq_of_iterAction_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π₁ π₂ : ContinuousRep G F) (K_sub : Subgroup G)
    [CompactSpace K_sub]
    (_hadm₁ : π₁.IsAdmissible K_sub) (_hadm₂ : π₂.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (ι₁ ι₂ : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    (v : F) (hv : v ∈ π₁.kFiniteSubspace K_sub)
    (h : F →L[ℂ] ℂ)
    (hiter_eq : ∀ (Xs : List 𝔤),
      h (iterLieAction ι₁ Xs v) = h (iterLieAction ι₂ Xs v))
    (g : G) : h ((π₁.toMonoidHom g) v) = h ((π₂.toMonoidHom g) v) :=
  elliptic_regularity_analytic_continuation I π₁ π₂ K_sub _hadm₁ _hadm₂ 𝔤 ι₁ ι₂ v hv h hiter_eq g

theorem trivialRep_isAdmissible
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (K_sub : Subgroup G) [CompactSpace K_sub] :
    ({
      toMonoidHom := 1
      continuous_action := continuous_snd
    } : ContinuousRep G F).IsAdmissible K_sub := by
  sorry

theorem analytic_matcoeff_vanishing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    [CompactSpace K_sub]
    (_hadm : π.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    (v : F) (_hv : v ∈ π.kFiniteSubspace K_sub)
    (h : F →L[ℂ] ℂ)
    (hvanish : ∀ (Xs : List 𝔤), h (iterLieAction ι Xs v) = 0)
    (g : G) : h ((π.toMonoidHom g) v) = 0 := by

  have hv_eq : h v = 0 := hvanish []
  have key := elliptic_regularity_analytic_continuation I π
    ⟨(1 : G →* (F →L[ℂ] F)), continuous_snd⟩
    K_sub _hadm (trivialRep_isAdmissible.{_, _, 0} (F := F) K_sub) 𝔤 ι 0 v _hv h (fun Xs => by
      rw [hvanish Xs]; cases Xs with
      | nil => exact hv_eq.symm
      | cons X rest =>
        simp [iterLieAction, List.foldr, LieHom.coe_zero,
          LinearMap.zero_apply, map_zero]) g
  simp only [MonoidHom.one_apply, ContinuousLinearMap.one_apply] at key
  rw [key, hv_eq]

lemma separation_from_closed_submodule
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (S : Submodule ℂ F) (hS : IsClosed (S : Set F))
    (x : F) (hx : x ∉ S) :
    ∃ h : F →L[ℂ] ℂ, (∀ s ∈ S, h s = 0) ∧ h x ≠ 0 := by
  haveI : IsClosed (S : Set F) := hS
  have hx_bar : (Submodule.Quotient.mk (p := S) x : F ⧸ S) ≠ 0 := by
    rwa [ne_eq, Submodule.Quotient.mk_eq_zero]
  obtain ⟨g, hg⟩ := SeparatingDual.exists_ne_zero (R := ℂ) (V := F ⧸ S) hx_bar
  have hcont : Continuous S.mkQ := continuous_quotient_mk'
  set h := g.comp (⟨S.mkQ, hcont⟩ : F →L[ℂ] F ⧸ S) with hh_def
  refine ⟨h, ?_, ?_⟩
  · intro s hs
    simp only [hh_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_mk']
    have : (Submodule.Quotient.mk (p := S) s : F ⧸ S) = 0 :=
      (Submodule.Quotient.mk_eq_zero S).mpr hs
    simp [this]
  · simp only [hh_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_mk']
    exact hg

lemma iterLieAction_mem_image_submodule
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {F : Type*} [AddCommGroup F] [Module ℂ F]
    {V : Submodule ℂ F}
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    [LieRingModule 𝔤 V]
    [LieModule ℂ 𝔤 V]
    (hι_compat : ∀ (X : 𝔤) (w : V),
      V.subtype ⁅X, w⁆ = ι X (V.subtype w))
    (W : Submodule ℂ V)
    (hW_lie : ∀ (X : 𝔤) (w : V), w ∈ W → ⁅X, w⁆ ∈ W)
    (Xs : List 𝔤) (w : V) (hw : w ∈ W) :
    iterLieAction ι Xs (V.subtype w) ∈ Submodule.map V.subtype W := by
  induction Xs with
  | nil =>
    exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩
  | cons X Xs ih =>
    change ι X (iterLieAction ι Xs (V.subtype w)) ∈ Submodule.map V.subtype W
    obtain ⟨w', hw', heq⟩ := Submodule.mem_map.mp ih
    rw [← heq, ← hι_compat]
    exact Submodule.mem_map.mpr ⟨⁅X, w'⁆, hW_lie X w' hw', rfl⟩

theorem analytic_matrixCoeff_eq_of_lie_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π₁ π₂ : ContinuousRep G F) (K_sub : Subgroup G)
    [CompactSpace K_sub]
    (hadm₁ : π₁.IsAdmissible K_sub) (hadm₂ : π₂.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (ι₁ : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    (ι₂ : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    (hlie_eq : ∀ (X : 𝔤) (v : F), v ∈ π₁.kFiniteSubspace K_sub →
      (ι₁ X) v = (ι₂ X) v)
    (hι₂_stable : ∀ (X : 𝔤) (w : F), w ∈ π₁.kFiniteSubspace K_sub →
      (ι₂ X) w ∈ π₁.kFiniteSubspace K_sub)
    (h : F →L[ℂ] ℂ) (g : G) (v : F) (hv : v ∈ π₁.kFiniteSubspace K_sub) :
    h ((π₁.toMonoidHom g) v) = h ((π₂.toMonoidHom g) v) := by

  have hι₁_stable : ∀ (X : 𝔤) (w : F), w ∈ π₁.kFiniteSubspace K_sub →
      (ι₁ X) w ∈ π₁.kFiniteSubspace K_sub := by
    intro X w hw
    rw [hlie_eq X w hw]
    exact hι₂_stable X w hw

  apply analytic_matcoeff_eq_of_iterAction_eq I π₁ π₂ K_sub hadm₁ hadm₂ 𝔤 ι₁ ι₂ v hv h

  intro Xs
  congr 1
  exact iterLieAction_agree_of_eq_on_kFinite I π₁ K_sub 𝔤 ι₁ ι₂
    hlie_eq hι₁_stable hι₂_stable Xs v hv

theorem harish_chandra_analyticity_matrixCoeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π₁ π₂ : ContinuousRep G F) (K_sub : Subgroup G)
    [CompactSpace K_sub]
    (hadm₁ : π₁.IsAdmissible K_sub) (hadm₂ : π₂.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (ι₁ : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    (ι₂ : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    (hlie_eq : ∀ (X : 𝔤) (v : F), v ∈ π₁.kFiniteSubspace K_sub →
      (ι₁ X) v = (ι₂ X) v)
    (hι₂_stable : ∀ (X : 𝔤) (w : F), w ∈ π₁.kFiniteSubspace K_sub →
      (ι₂ X) w ∈ π₁.kFiniteSubspace K_sub)
    (hK_eq : ∀ (k : K_sub) (v : F), v ∈ π₁.kFiniteSubspace K_sub →
      (π₁.toMonoidHom k) v = (π₂.toMonoidHom k) v)
    (h : F →L[ℂ] ℂ) (g : G) (v : F) (hv : v ∈ π₁.kFiniteSubspace K_sub) :
    h ((π₁.toMonoidHom g) v) = h ((π₂.toMonoidHom g) v) :=


  analytic_matrixCoeff_eq_of_lie_eq I π₁ π₂ K_sub hadm₁ hadm₂ 𝔤 ι₁ ι₂
    hlie_eq hι₂_stable h g v hv

theorem gAction_on_kFinite_determined_by_gkModule
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π₁ π₂ : ContinuousRep G F) (K_sub : Subgroup G)
    [CompactSpace K_sub]
    (hadm₁ : π₁.IsAdmissible K_sub) (hadm₂ : π₂.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K_sub →* (𝔤 →ₗ[ℂ] 𝔤))
    (ι₁ : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    (ι₂ : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    [LieRingModule 𝔤 ↥(π₁.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π₁.kFiniteSubspace K_sub)]
    [LieRingModule 𝔤 ↥(π₂.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π₂.kFiniteSubspace K_sub)]
    (hequiv₁ : ∀ (k : K_sub) (X : 𝔤) (v : ↥(π₁.kFiniteSubspace K_sub)),
      (kFiniteSubspace_kAction π₁ K_sub) k (⁅X, v⁆) =
        ⁅Ad k X, (kFiniteSubspace_kAction π₁ K_sub) k v⁆)
    (hequiv₂ : ∀ (k : K_sub) (X : 𝔤) (v : ↥(π₂.kFiniteSubspace K_sub)),
      (kFiniteSubspace_kAction π₂ K_sub) k (⁅X, v⁆) =
        ⁅Ad k X, (kFiniteSubspace_kAction π₂ K_sub) k v⁆)
    (hkfin_eq : (π₁.kFiniteSubspace K_sub : Set F) = (π₂.kFiniteSubspace K_sub : Set F))
    (hlie_eq : ∀ (X : 𝔤) (v : F), v ∈ π₁.kFiniteSubspace K_sub →
      (ι₁ X) v = (ι₂ X) v)
    (hι₂_stable : ∀ (X : 𝔤) (w : F), w ∈ π₁.kFiniteSubspace K_sub →
      (ι₂ X) w ∈ π₁.kFiniteSubspace K_sub)
    (hK_eq : ∀ (k : K_sub) (v : F), v ∈ π₁.kFiniteSubspace K_sub →
      (π₁.toMonoidHom k) v = (π₂.toMonoidHom k) v) :
    ∀ (g : G) (v : F), v ∈ π₁.kFiniteSubspace K_sub →
      (π₁.toMonoidHom g) v = (π₂.toMonoidHom g) v := by


  intro g v hv

  rw [NormedSpace.eq_iff_forall_dual_eq ℂ]


  intro h
  exact harish_chandra_analyticity_matrixCoeff I π₁ π₂ K_sub hadm₁ hadm₂ 𝔤 ι₁ ι₂
    hlie_eq hι₂_stable hK_eq h g v hv

theorem gAction_determined_by_gkModule
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π₁ π₂ : ContinuousRep G F) (K_sub : Subgroup G)
    [CompactSpace K_sub]
    (_hK_max : IsMaximalCompactSubgroup K_sub)
    (hadm₁ : π₁.IsAdmissible K_sub) (hadm₂ : π₂.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K_sub →* (𝔤 →ₗ[ℂ] 𝔤))
    (ι₁ : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    (ι₂ : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    [LieRingModule 𝔤 ↥(π₁.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π₁.kFiniteSubspace K_sub)]
    [LieRingModule 𝔤 ↥(π₂.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π₂.kFiniteSubspace K_sub)]
    (hequiv₁ : ∀ (k : K_sub) (X : 𝔤) (v : ↥(π₁.kFiniteSubspace K_sub)),
      (kFiniteSubspace_kAction π₁ K_sub) k (⁅X, v⁆) =
        ⁅Ad k X, (kFiniteSubspace_kAction π₁ K_sub) k v⁆)
    (hequiv₂ : ∀ (k : K_sub) (X : 𝔤) (v : ↥(π₂.kFiniteSubspace K_sub)),
      (kFiniteSubspace_kAction π₂ K_sub) k (⁅X, v⁆) =
        ⁅Ad k X, (kFiniteSubspace_kAction π₂ K_sub) k v⁆)
    (hkfin_eq : (π₁.kFiniteSubspace K_sub : Set F) = (π₂.kFiniteSubspace K_sub : Set F))
    (hlie_eq : ∀ (X : 𝔤) (v : F), v ∈ π₁.kFiniteSubspace K_sub →
      (ι₁ X) v = (ι₂ X) v)
    (hι₂_stable : ∀ (X : 𝔤) (w : F), w ∈ π₁.kFiniteSubspace K_sub →
      (ι₂ X) w ∈ π₁.kFiniteSubspace K_sub)
    (hK_eq : ∀ (k : K_sub) (v : F), v ∈ π₁.kFiniteSubspace K_sub →
      (π₁.toMonoidHom k) v = (π₂.toMonoidHom k) v) :
    π₁ = π₂ := by

  have hkfin_agree := gAction_on_kFinite_determined_by_gkModule I π₁ π₂ K_sub
    hadm₁ hadm₂ 𝔤 𝔨 Ad ι₁ ι₂ hequiv₁ hequiv₂ hkfin_eq hlie_eq hι₂_stable hK_eq

  have hdense : Dense (π₁.kFiniteSubspace K_sub : Set F) :=
    kFiniteSubspace_dense_admissible I π₁ K_sub hadm₁


  have hpointwise : ∀ g : G, (π₁.toMonoidHom g) = (π₂.toMonoidHom g) := by
    intro g
    have hfun_eq : ((π₁.toMonoidHom g) : F → F) = ((π₂.toMonoidHom g) : F → F) :=
      Continuous.ext_on hdense (π₁.toMonoidHom g).continuous
        (π₂.toMonoidHom g).continuous (fun v hv => hkfin_agree g v hv)
    exact ContinuousLinearMap.ext (congr_fun hfun_eq)

  have h_monoid_hom_eq : π₁.toMonoidHom = π₂.toMonoidHom := MonoidHom.ext hpointwise
  cases π₁; cases π₂; simp_all

theorem continuous_map_eq_of_eq_on_kFinite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    [CompactSpace K_sub]
    (hadm : π.IsAdmissible K_sub)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    (f g : F →L[ℂ] W)
    (heq : ∀ v ∈ π.kFiniteSubspace K_sub, f v = g v) :
    f = g := by
  have hdense : Dense (π.kFiniteSubspace K_sub : Set F) :=
    kFiniteSubspace_dense_admissible I π K_sub hadm
  have hfun_eq : (f : F → W) = (g : F → W) :=
    Continuous.ext_on hdense f.continuous g.continuous heq
  exact ContinuousLinearMap.ext (congr_fun hfun_eq)


theorem derived_rep_preserves_closed_ginvariant_subspace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (hadm : π.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    (U : Submodule ℂ F) (hU : π.IsInvariantSubspace U) :
    ∀ (X : 𝔤) (v : F), v ∈ U → ι X v ∈ U := by sorry

theorem lie_action_preserves_invariant_subspace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (hadm : π.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [LieRingModule 𝔤 ↥(π.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π.kFiniteSubspace K_sub)]
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    (hι_compat : ∀ (X : 𝔤) (w : ↥(π.kFiniteSubspace K_sub)),
      (π.kFiniteSubspace K_sub).subtype ⁅X, w⁆ = ι X ((π.kFiniteSubspace K_sub).subtype w))
    (U : Submodule ℂ F) (hU : π.IsInvariantSubspace U)
    (hι_inv : ∀ (X : 𝔤) (v : F), v ∈ U → ι X v ∈ U)
    (X : 𝔤) (w : ↥(π.kFiniteSubspace K_sub))
    (hw : (π.kFiniteSubspace K_sub).subtype w ∈ U) :
    (π.kFiniteSubspace K_sub).subtype ⁅X, w⁆ ∈ U := by
  rw [hι_compat]
  exact hι_inv X _ hw


theorem gkSubmodule_image_maps_into_closure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    [CompactSpace K_sub]
    (hadm : π.IsAdmissible K_sub)
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
    (W : Submodule ℂ ↥(π.kFiniteSubspace K_sub))
    (hW : (harishChandraGKModule I π K_sub hadm 𝔤 𝔨 Ad ι hequiv).IsSubmodule W) :
    let S := Submodule.map (π.kFiniteSubspace K_sub).subtype W
    ∀ (g : G) (v : F), v ∈ S →
      (π.toMonoidHom g) v ∈ S.topologicalClosure := by
  intro S g v hv

  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hv

  by_contra h_not_mem

  have hS_closed : IsClosed (S.topologicalClosure : Set F) :=
    S.isClosed_topologicalClosure
  obtain ⟨φ, hφ_vanish, hφ_ne⟩ := separation_from_closed_submodule
    S.topologicalClosure hS_closed _ h_not_mem

  have hφ_vanish_S : ∀ s ∈ S, φ s = 0 := fun s hs =>
    hφ_vanish s (Submodule.le_topologicalClosure S hs)

  have hiter_in_S : ∀ (Xs : List 𝔤),
      iterLieAction ι Xs ((π.kFiniteSubspace K_sub).subtype w) ∈ S := by
    intro Xs
    exact iterLieAction_mem_image_submodule ι hι_compat W
      (fun X v hv => hW.lie_invariant X v hv) Xs w hw

  have hφ_iter_vanish : ∀ (Xs : List 𝔤),
      φ (iterLieAction ι Xs ((π.kFiniteSubspace K_sub).subtype w)) = 0 := by
    intro Xs
    exact hφ_vanish_S _ (hiter_in_S Xs)

  have hv_kfin : (π.kFiniteSubspace K_sub).subtype w ∈ π.kFiniteSubspace K_sub :=
    w.prop

  have hφ_zero := analytic_matcoeff_vanishing I π K_sub hadm 𝔤 ι
    ((π.kFiniteSubspace K_sub).subtype w) hv_kfin φ hφ_iter_vanish g

  exact hφ_ne hφ_zero

theorem closure_gkSubmodule_gInvariant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    [CompactSpace K_sub]
    (hadm : π.IsAdmissible K_sub)
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
    (W : Submodule ℂ ↥(π.kFiniteSubspace K_sub))
    (hW : (harishChandraGKModule I π K_sub hadm 𝔤 𝔨 Ad ι hequiv).IsSubmodule W) :
    let S := Submodule.map (π.kFiniteSubspace K_sub).subtype W
    ∀ (g : G) (v : F), v ∈ S.topologicalClosure →
      (π.toMonoidHom g) v ∈ S.topologicalClosure := by
  intro S g v hv

  have hS_into_closure : ∀ (w : F), w ∈ S → (π.toMonoidHom g) w ∈ S.topologicalClosure :=
    gkSubmodule_image_maps_into_closure I π K_sub hadm 𝔤 𝔨 Ad ι hequiv hι_compat W hW g

  have hcont : Continuous (π.toMonoidHom g) := (π.toMonoidHom g).continuous

  have hmaps : Set.MapsTo (π.toMonoidHom g) (S : Set F) (S.topologicalClosure : Set F) :=
    hS_into_closure
  have hmaps_closure : Set.MapsTo (π.toMonoidHom g)
      (closure (S : Set F)) (closure (S.topologicalClosure : Set F)) :=
    hmaps.closure hcont

  have hv' : v ∈ closure (S : Set F) := by
    rwa [← Submodule.topologicalClosure_coe]
  have hgv : (π.toMonoidHom g) v ∈ closure (S.topologicalClosure : Set F) :=
    hmaps_closure hv'
  rw [Submodule.topologicalClosure_coe, closure_closure] at hgv
  rwa [← Submodule.topologicalClosure_coe] at hgv


theorem peterWeyl_finsupp_projector
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (v : F) (hv : v ∈ π.kFiniteSubspace K_sub) :
    ∃ (c : K_sub →₀ ℂ),
      (c.sum (fun k a => a • π.toMonoidHom k)) v = v ∧
      ∀ {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
        (π₂ : ContinuousRep G F₂),
        FiniteDimensional ℂ
          (LinearMap.range (c.sum (fun k a => a • π₂.toMonoidHom k)).toLinearMap) ∧
        (∀ (k : K_sub),
          (c.sum (fun k a => a • π₂.toMonoidHom k)).comp (π₂.toMonoidHom k) =
          (π₂.toMonoidHom k).comp (c.sum (fun k a => a • π₂.toMonoidHom k))) := by sorry

theorem isotypicProjector_finiteRange_fix_commute
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (v : F) (hv : v ∈ π.kFiniteSubspace K_sub) :
    ∃ P : F →L[ℂ] F,
      FiniteDimensional ℂ (LinearMap.range P.toLinearMap) ∧
      P v = v ∧
      (∀ (k : K_sub), P.comp (π.toMonoidHom k) = (π.toMonoidHom k).comp P) ∧
      (∀ (S : Submodule ℂ F),
        (∀ (k : K_sub) (s : F), s ∈ S → (π.toMonoidHom k) s ∈ S) →
        ∀ (s : F), s ∈ S → s ∈ π.kFiniteSubspace K_sub → P s ∈ S) := by

  obtain ⟨c, hc_fix, hc_props⟩ := peterWeyl_finsupp_projector π K_sub v hv

  refine ⟨c.sum (fun k a => a • π.toMonoidHom k), ?_, hc_fix, (hc_props π).2, ?_⟩
  ·
    exact (hc_props π).1
  ·
    intro S hS_stable s hs _hs_kfin


    simp only [Finsupp.sum]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    apply Submodule.sum_mem
    intro ⟨k, hk⟩ _
    exact S.smul_mem _ (hS_stable ⟨k, hk⟩ s hs)

theorem closure_kFinite_roundtrip
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (hadm : π.IsAdmissible K_sub)
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
    let S := Submodule.map (π.kFiniteSubspace K_sub).subtype W
    ∀ (v : ↥(π.kFiniteSubspace K_sub)),
      (v : F) ∈ S.topologicalClosure →
      v ∈ W := by
  intro S v hv_closure

  have hv_kfin : (v : F) ∈ π.kFiniteSubspace K_sub := v.prop
  obtain ⟨P, hP_fin, hP_fix, hP_comm, hP_preserves_kstable⟩ :=
    isotypicProjector_finiteRange_fix_commute π K_sub (v : F) hv_kfin

  have hS_kstable : ∀ (k : K_sub) (s : F), s ∈ S → (π.toMonoidHom k) s ∈ S := by
    intro k s hs
    rw [Submodule.mem_map] at hs ⊢
    obtain ⟨w, hw_mem, hw_eq⟩ := hs
    refine ⟨(kFiniteSubspace_kAction π K_sub k) w, ?_, ?_⟩
    · exact hW.group_invariant k w hw_mem
    · rw [← hw_eq]; rfl

  have hP_preserves : ∀ s : F, s ∈ S → s ∈ π.kFiniteSubspace K_sub → P s ∈ S := by
    intro s hs hs_kfin
    exact hP_preserves_kstable S hS_kstable s hs hs_kfin


  have hP_cont : Continuous P := P.continuous


  have hS_kfin : ∀ s : F, s ∈ S → s ∈ π.kFiniteSubspace K_sub := by
    intro s hs
    rw [Submodule.mem_map] at hs
    obtain ⟨w, _, hw_eq⟩ := hs
    rw [← hw_eq]
    exact w.prop
  have hPS_sub_S : P '' (↑S : Set F) ⊆ (↑S : Set F) := by
    intro y hy
    obtain ⟨s, hs, rfl⟩ := hy
    exact hP_preserves s hs (hS_kfin s hs)

  have hPS_sub_range : P '' (↑S : Set F) ⊆ ↑(LinearMap.range P.toLinearMap) := by
    intro y hy
    obtain ⟨s, _, rfl⟩ := hy
    exact LinearMap.mem_range.mpr ⟨s, rfl⟩

  have hPS_sub_inter : P '' (↑S : Set F) ⊆ (↑S : Set F) ∩ ↑(LinearMap.range P.toLinearMap) := by
    exact Set.subset_inter hPS_sub_S hPS_sub_range

  set T := S ⊓ (LinearMap.range P.toLinearMap) with hT_def
  have hT_le_range : T ≤ (LinearMap.range P.toLinearMap) := inf_le_right
  haveI : FiniteDimensional ℂ T := by
    exact Module.Finite.of_injective (Submodule.inclusion hT_le_range)
      (Submodule.inclusion_injective hT_le_range)

  have hT_closed : IsClosed (↑T : Set F) := Submodule.closed_of_finiteDimensional T

  have hv_in_closure_PS : (v : F) ∈ closure (P '' (↑S : Set F)) := by
    rw [← hP_fix]
    exact image_closure_subset_closure_image hP_cont (Set.mem_image_of_mem P hv_closure)
  have hv_in_closure_T : (v : F) ∈ closure (↑T : Set F) := by
    apply closure_mono (s := P '' (↑S : Set F)) (t := ↑T)
    · intro x hx
      exact hPS_sub_inter hx
    · exact hv_in_closure_PS
  have hv_in_T : (v : F) ∈ (↑T : Set F) := hT_closed.closure_eq ▸ hv_in_closure_T

  have hv_in_S : (v : F) ∈ (↑S : Set F) := (Submodule.mem_inf.mp hv_in_T).1


  have hv_in_S' : (v : F) ∈ S := hv_in_S
  rw [Submodule.mem_map] at hv_in_S'
  obtain ⟨w, hw_mem, hw_eq⟩ := hv_in_S'
  have : v = w := Subtype.ext (by exact hw_eq.symm)
  rw [this]
  exact hw_mem

theorem kFinite_dense_in_invariant_subspace_submodule
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    [CompactSpace K_sub]
    (hadm : π.IsAdmissible K_sub)
    (U : Submodule ℂ F) (hU : π.IsInvariantSubspace U) :
    let S := Submodule.map (π.kFiniteSubspace K_sub).subtype (Submodule.comap (π.kFiniteSubspace K_sub).subtype U)
    S.topologicalClosure = U := by
  intro S
  apply le_antisymm
  ·
    apply S.topologicalClosure_minimal
    · intro x hx
      obtain ⟨w, hw, hwx⟩ := hx
      rw [← hwx]
      exact hw
    · exact hU.isClosed
  ·


    intro v hv

    suffices hcl : v ∈ closure (S : Set F) by
      rw [← Submodule.topologicalClosure_coe] at hcl
      exact hcl

    obtain ⟨R, hR_kfin, hR_dirac, hR_pw⟩ :=
      ContinuousRep.measureRep_exists (π.subrepresentation U hU) K_sub

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

    have kfin_subrep_to_full : ∀ (w : ↥U),
        w ∈ ContinuousRep.kFiniteSubspace (π.subrepresentation U hU) K_sub →
        (w : F) ∈ ContinuousRep.kFiniteSubspace π K_sub := by
      intro w hw
      rw [ContinuousRep.mem_kFiniteSubspace] at hw ⊢
      unfold ContinuousRep.IsKFinite at hw ⊢

      have hmap : Submodule.map U.subtype
          (Submodule.span ℂ (Set.range (fun k : K_sub =>
            ((π.subrepresentation U hU).toMonoidHom k) w))) =
          Submodule.span ℂ (Set.range (fun k : K_sub => (π.toMonoidHom k) (w : F))) := by
        rw [Submodule.map_span]
        congr 1
        ext x
        simp only [Set.mem_image, Set.mem_range]
        constructor
        · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
          exact ⟨k, rfl⟩
        · rintro ⟨k, rfl⟩
          exact ⟨((π.subrepresentation U hU).toMonoidHom k) w, ⟨k, rfl⟩, rfl⟩
      rw [← hmap]
      exact Module.Finite.map _ U.subtype

    have image_subset : U.subtype ''
        (ContinuousRep.kFiniteSubspace (π.subrepresentation U hU) K_sub : Set ↥U) ⊆ (S : Set F) := by
      intro x ⟨w, hw_kfin, hw_eq⟩
      have hx_kfin : x ∈ ContinuousRep.kFiniteSubspace π K_sub := by
        rw [← hw_eq]; exact kfin_subrep_to_full w hw_kfin
      have hx_U : x ∈ (U : Set F) := by
        rw [← hw_eq]; exact w.2
      exact ⟨⟨x, hx_kfin⟩, hx_U, rfl⟩


    have v_U_mem : (⟨v, hv⟩ : ↥U) ∈
        closure (ContinuousRep.kFiniteSubspace (π.subrepresentation U hU) K_sub : Set ↥U) :=
      hdense ⟨v, hv⟩

    have hcont : Continuous (U.subtype : ↥U → F) := continuous_subtype_val

    have hv_in_closure_image : v ∈ closure (U.subtype ''
        (ContinuousRep.kFiniteSubspace (π.subrepresentation U hU) K_sub : Set ↥U)) := by
      have := image_closure_subset_closure_image hcont ⟨⟨v, hv⟩, v_U_mem, rfl⟩
      simp only [Submodule.subtype_apply] at this
      exact this
    exact closure_mono image_subset hv_in_closure_image

theorem gkSubmodule_closure_correspondence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    [CompactSpace K_sub]
    (hadm : π.IsAdmissible K_sub)
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
      (π.kFiniteSubspace K_sub).subtype ⁅X, w⁆ = ι X ((π.kFiniteSubspace K_sub).subtype w)) :
    let M := harishChandraGKModule I π K_sub hadm 𝔤 𝔨 Ad ι hequiv

    (∀ (U : Submodule ℂ F), π.IsInvariantSubspace U →
      M.IsSubmodule (Submodule.comap (π.kFiniteSubspace K_sub).subtype U)) ∧

    (∀ (W : Submodule ℂ ↥(π.kFiniteSubspace K_sub)), M.IsSubmodule W →
      ∃ (U : Submodule ℂ F), π.IsInvariantSubspace U ∧
        Submodule.comap (π.kFiniteSubspace K_sub).subtype U = W) ∧


    (∀ (U₁ U₂ : Submodule ℂ F), π.IsInvariantSubspace U₁ → π.IsInvariantSubspace U₂ →
      Submodule.comap (π.kFiniteSubspace K_sub).subtype U₁ =
        Submodule.comap (π.kFiniteSubspace K_sub).subtype U₂ → U₁ = U₂) := by
  intro M
  refine ⟨fun U hU => ⟨fun X w hw => ?_, fun k w hw => ?_⟩,
         fun W hW => ?_, fun U₁ U₂ h1 h2 heq => ?_⟩
  ·

    rw [Submodule.mem_comap] at hw ⊢
    exact lie_action_preserves_invariant_subspace I π K_sub hadm 𝔤 ι hι_compat U hU
      (derived_rep_preserves_closed_ginvariant_subspace I π K_sub hadm 𝔤 ι U hU) X w hw

  ·
    simp only [Submodule.mem_comap] at hw ⊢
    show ((kFiniteSubspace_kAction π K_sub) k w).val ∈ U
    exact hU.invariant (↑k) w.val hw
  ·

    let S := Submodule.map (π.kFiniteSubspace K_sub).subtype W
    refine ⟨S.topologicalClosure, ?_, ?_⟩
    ·
      constructor
      ·
        exact S.isClosed_topologicalClosure
      ·
        exact closure_gkSubmodule_gInvariant I π K_sub hadm 𝔤 𝔨 Ad ι hequiv hι_compat W hW
    ·
      ext ⟨x, hx_kfin⟩
      simp only [Submodule.mem_comap, Submodule.coe_subtype]
      constructor
      ·
        intro hx_closure
        exact closure_kFinite_roundtrip I π K_sub hadm 𝔤 𝔨 Ad ι hequiv W hW ⟨x, hx_kfin⟩ hx_closure
      ·
        intro hx_W
        apply Submodule.le_topologicalClosure
        exact ⟨⟨x, hx_kfin⟩, hx_W, rfl⟩
  ·


    have hcl1 := kFinite_dense_in_invariant_subspace_submodule I π K_sub hadm U₁ h1
    have hcl2 := kFinite_dense_in_invariant_subspace_submodule I π K_sub hadm U₂ h2


    have hmap_eq : Submodule.map (π.kFiniteSubspace K_sub).subtype (Submodule.comap (π.kFiniteSubspace K_sub).subtype U₁) =
                   Submodule.map (π.kFiniteSubspace K_sub).subtype (Submodule.comap (π.kFiniteSubspace K_sub).subtype U₂) := by
      rw [heq]

    have hcl_eq : (Submodule.map (π.kFiniteSubspace K_sub).subtype (Submodule.comap (π.kFiniteSubspace K_sub).subtype U₁)).topologicalClosure =
                  (Submodule.map (π.kFiniteSubspace K_sub).subtype (Submodule.comap (π.kFiniteSubspace K_sub).subtype U₂)).topologicalClosure := by
      rw [hmap_eq]
    rw [hcl1, hcl2] at hcl_eq
    exact hcl_eq

theorem harishChandra_preserves_irreducibility
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    [CompactSpace K_sub]
    (hadm : π.IsAdmissible K_sub)
    (hirr : π.IsIrreducible)
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
    (harishChandraGKModule I π K_sub hadm 𝔤 𝔨 Ad ι hequiv).IsIrreducibleGKModule := by


  intro W hW
  obtain ⟨_, hbij_inv, _⟩ := gkSubmodule_closure_correspondence I π K_sub hadm 𝔤 𝔨 Ad ι hequiv hι_compat

  obtain ⟨U, hU_inv, hU_eq⟩ := hbij_inv W hW
  rcases hirr U hU_inv with hbot | htop
  · left
    rw [← hU_eq, hbot]
    ext ⟨v, hv⟩
    simp [Submodule.mem_bot]
  · right
    rw [← hU_eq, htop]
    ext ⟨v, hv⟩
    simp [Submodule.mem_top]

theorem harishChandra_reflects_irreducibility
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    [CompactSpace K_sub]
    (hadm : π.IsAdmissible K_sub)
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
      ∀ (X : 𝔤) (v : F), v ∈ U → ι X v ∈ U)
    (hirr_gk : (harishChandraGKModule I π K_sub hadm 𝔤 𝔨 Ad ι hequiv).IsIrreducibleGKModule) :
    π.IsIrreducible := by


  intro U hU
  obtain ⟨hbij_fwd, _, hbij_inj⟩ := gkSubmodule_closure_correspondence I π K_sub hadm 𝔤 𝔨 Ad ι hequiv hι_compat

  have hW_sub := hbij_fwd U hU
  rcases hirr_gk _ hW_sub with hbot | htop
  ·
    left
    have hbot_inv : π.IsInvariantSubspace ⊥ := by
      constructor
      · exact isClosed_singleton
      · intro g v hv
        rw [Submodule.mem_bot] at hv ⊢
        rw [hv, map_zero]
    have hcomap_bot : Submodule.comap (π.kFiniteSubspace K_sub).subtype ⊥ = ⊥ := by
      ext ⟨v, hv⟩
      simp [Submodule.mem_bot]
    exact hbij_inj U ⊥ hU hbot_inv (hbot.trans hcomap_bot.symm)
  ·
    right
    have htop_inv : π.IsInvariantSubspace ⊤ := by
      constructor
      · exact isClosed_univ
      · intro g v _
        exact Submodule.mem_top
    have hcomap_top : Submodule.comap (π.kFiniteSubspace K_sub).subtype ⊤ = ⊤ := by
      ext ⟨v, hv⟩
      simp [Submodule.mem_top]
    exact hbij_inj U ⊤ hU htop_inv (htop.trans hcomap_top.symm)

theorem harishChandra_irreducibility_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    [CompactSpace K_sub]
    (hadm : π.IsAdmissible K_sub)
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
    π.IsIrreducible ↔
    (harishChandraGKModule I π K_sub hadm 𝔤 𝔨 Ad ι hequiv).IsIrreducibleGKModule :=
  ⟨fun hirr => harishChandra_preserves_irreducibility I π K_sub hadm hirr 𝔤 𝔨 Ad ι hequiv hι_compat hι_preserves,
   fun hirr_gk => harishChandra_reflects_irreducibility I π K_sub hadm 𝔤 𝔨 Ad ι hequiv hι_compat hι_preserves hirr_gk⟩

theorem repHom_maps_kFinite
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
    (π₁ : ContinuousRep G F₁) (π₂ : ContinuousRep G F₂)
    (K_sub : Subgroup G)
    (T : RepHom π₁ π₂)
    (v : F₁) (hv : v ∈ π₁.kFiniteSubspace K_sub) :
    T.toContinuousLinearMap v ∈ π₂.kFiniteSubspace K_sub := by
  rw [ContinuousRep.mem_kFiniteSubspace] at hv ⊢
  unfold ContinuousRep.IsKFinite at *

  have hsub : Submodule.span ℂ
      (Set.range (fun k : K_sub => (π₂.toMonoidHom k) (T.toContinuousLinearMap v))) ≤
      (Submodule.span ℂ (Set.range (fun k : K_sub => (π₁.toMonoidHom k) v))).map
        T.toContinuousLinearMap.toLinearMap := by
    apply Submodule.span_le.mpr
    intro x hx; obtain ⟨k, rfl⟩ := hx

    dsimp only
    have hintertwine := T.intertwines (k : G)
    have heq : (π₂.toMonoidHom ↑k) (T.toContinuousLinearMap v) =
        T.toContinuousLinearMap ((π₁.toMonoidHom ↑k) v) := by
      have := ContinuousLinearMap.ext_iff.mp hintertwine v
      simp [ContinuousLinearMap.comp_apply] at this
      exact this.symm
    rw [heq]
    exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨k, rfl⟩)
  haveI : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range (fun k : K_sub => (π₁.toMonoidHom k) v))) := hv
  haveI : FiniteDimensional ℂ
      ((Submodule.span ℂ (Set.range (fun k : K_sub => (π₁.toMonoidHom k) v))).map
        T.toContinuousLinearMap.toLinearMap) :=
    inferInstance
  exact Module.Finite.of_injective
    (Submodule.inclusion hsub) (Submodule.inclusion_injective hsub)

def repHom_restrict_kFinite
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
    (π₁ : ContinuousRep G F₁) (π₂ : ContinuousRep G F₂)
    (K_sub : Subgroup G)
    (T : RepHom π₁ π₂) :
    ↥(π₁.kFiniteSubspace K_sub) →ₗ[ℂ] ↥(π₂.kFiniteSubspace K_sub) where
  toFun v := ⟨T.toContinuousLinearMap v.val,
    repHom_maps_kFinite π₁ π₂ K_sub T v.val v.prop⟩
  map_add' u v := by
    apply Subtype.ext
    simp [map_add]
  map_smul' c v := by
    apply Subtype.ext
    simp [map_smul]


theorem kEquivariant_finiteRange_maps_to_kFinite
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    (P : F →L[ℂ] F)
    (hfin : FiniteDimensional ℂ (LinearMap.range P.toLinearMap))
    (hcomm : ∀ (k : K_sub), P.comp (π.toMonoidHom k) = (π.toMonoidHom k).comp P) :
    ∀ w, P w ∈ π.kFiniteSubspace K_sub := by
  intro w
  show ContinuousRep.IsKFinite π K_sub (P w)
  unfold ContinuousRep.IsKFinite


  have h_in_range : ∀ k : K_sub, (π.toMonoidHom ↑k) (P w) ∈
      LinearMap.range P.toLinearMap := by
    intro k
    have heq := congr_fun (congr_arg DFunLike.coe (hcomm k)) w
    simp only [ContinuousLinearMap.comp_apply] at heq
    rw [← heq]
    exact LinearMap.mem_range.mpr ⟨(π.toMonoidHom ↑k) w, rfl⟩
  have h_span_le : Submodule.span ℂ
      (Set.range (fun k : K_sub => (π.toMonoidHom ↑k) (P w))) ≤
      LinearMap.range P.toLinearMap := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨k, rfl⟩ := hx
    exact h_in_range k
  exact Module.Finite.of_injective (Submodule.inclusion h_span_le)
    (Submodule.inclusion_injective h_span_le)

lemma finsupp_rep_intertwines
    {G : Type*} [Group G] [TopologicalSpace G]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
    {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace ℂ F₃]
    (π₂ : ContinuousRep G F₂) (π₃ : ContinuousRep G F₃)
    (S : RepHom π₂ π₃)
    (K_sub : Subgroup G)
    (c : K_sub →₀ ℂ)
    (w : F₂) :
    S.toContinuousLinearMap
      ((c.sum (fun k a => a • π₂.toMonoidHom k)) w) =
    (c.sum (fun k a => a • π₃.toMonoidHom k))
      (S.toContinuousLinearMap w) := by
  simp only [Finsupp.sum]

  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  rw [map_sum]
  congr 1
  ext ⟨k, hk⟩
  rw [map_smul]
  congr 1
  have := S.intertwines (k : G)
  exact congr_fun (congr_arg DFunLike.coe this) w

theorem peter_weyl_surjective_kfinite_lift
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
    {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace ℂ F₃]
    (π₂ : ContinuousRep G F₂) (π₃ : ContinuousRep G F₃)
    (K_sub : Subgroup G)
    (S : RepHom π₂ π₃)
    (hS_surj : Function.Surjective S.toContinuousLinearMap)
    (v₃ : F₃) (hv₃ : v₃ ∈ π₃.kFiniteSubspace K_sub) :
    ∃ w ∈ π₂.kFiniteSubspace K_sub, S.toContinuousLinearMap w = v₃ := by

  obtain ⟨w₀, hw₀⟩ := hS_surj v₃

  obtain ⟨c, hc_fix, hc_props⟩ := peterWeyl_finsupp_projector π₃ K_sub v₃ hv₃

  let P₂ := c.sum (fun k a => a • π₂.toMonoidHom k)

  have hP₂_kfin : ∀ w, P₂ w ∈ π₂.kFiniteSubspace K_sub :=
    kEquivariant_finiteRange_maps_to_kFinite π₂ K_sub P₂ (hc_props π₂).1 (hc_props π₂).2

  refine ⟨P₂ w₀, hP₂_kfin w₀, ?_⟩

  rw [finsupp_rep_intertwines π₂ π₃ S K_sub c w₀, hw₀, hc_fix]

theorem surjective_repHom_kFinite
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
    {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace ℂ F₃]
    (π₂ : ContinuousRep G F₂) (π₃ : ContinuousRep G F₃)
    (K_sub : Subgroup G)
    (S : RepHom π₂ π₃)
    (hS_surj : Function.Surjective S.toContinuousLinearMap)
    (v₃ : F₃) (hv₃ : v₃ ∈ π₃.kFiniteSubspace K_sub) :
    ∃ w ∈ π₂.kFiniteSubspace K_sub, S.toContinuousLinearMap w = v₃ := by
  exact peter_weyl_surjective_kfinite_lift π₂ π₃ K_sub S hS_surj v₃ hv₃

theorem theorem_6_16_irreducibility
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K_sub : Subgroup G)
    [CompactSpace K_sub]
    (hadm : π.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K_sub →* (𝔤 →ₗ[ℂ] 𝔤))
    (ι : 𝔤 →ₗ⁅ℂ⁆ (F →ₗ[ℂ] F))
    [LieRingModule 𝔤 ↑(π.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↑(π.kFiniteSubspace K_sub)]
    (hequiv : ∀ (k : K_sub) (X : 𝔤) (v : ↑(π.kFiniteSubspace K_sub)),
      (kFiniteSubspace_kAction π K_sub) k (⁅X, v⁆) =
        ⁅Ad k X, (kFiniteSubspace_kAction π K_sub) k v⁆)
    (hι_compat : ∀ (X : 𝔤) (w : ↑(π.kFiniteSubspace K_sub)),
      (π.kFiniteSubspace K_sub).subtype ⁅X, w⁆ = ι X ((π.kFiniteSubspace K_sub).subtype w))
    (hι_preserves : ∀ (U : Submodule ℂ F), π.IsInvariantSubspace U →
      ∀ (X : 𝔤) (v : F), v ∈ U → ι X v ∈ U) :
    π.IsIrreducible ↔
    (harishChandraGKModule I π K_sub hadm 𝔤 𝔨 Ad ι hequiv).IsIrreducibleGKModule :=
  harishChandra_irreducibility_iff I π K_sub hadm 𝔤 𝔨 Ad ι hequiv hι_compat hι_preserves

structure UnitaryRepEquiv
    {G : Type*} [Group G] [TopologicalSpace G]
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]
    (π₁ : ContinuousRep G V) (π₂ : ContinuousRep G W) extends RepEquiv π₁ π₂ where
  inner_preserving : ∀ (v w : V),
    @inner ℂ W _ (toContinuousLinearEquiv v) (toContinuousLinearEquiv w) =
    @inner ℂ V _ v w

theorem prop_7_1_schur_and_equivariance
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [InnerProductSpace ℂ F₂] [CompleteSpace F₂]
    (π₁ : ContinuousRep G F₁) (π₂ : ContinuousRep G F₂)
    (K_sub : Subgroup G)
    [hK_compact : CompactSpace K_sub]
    (hadm₁ : π₁.IsAdmissible K_sub) (hadm₂ : π₂.IsAdmissible K_sub)
    (hunit₁ : π₁.IsUnitary) (hunit₂ : π₂.IsUnitary)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K_sub →* (𝔤 →ₗ[ℂ] 𝔤))
    (ι₁ : 𝔤 →ₗ⁅ℂ⁆ (F₁ →ₗ[ℂ] F₁))
    (ι₂ : 𝔤 →ₗ⁅ℂ⁆ (F₂ →ₗ[ℂ] F₂))
    [LieRingModule 𝔤 ↥(π₁.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π₁.kFiniteSubspace K_sub)]
    [LieRingModule 𝔤 ↥(π₂.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π₂.kFiniteSubspace K_sub)]
    (A : ↥(π₁.kFiniteSubspace K_sub) ≃ₗ[ℂ] ↥(π₂.kFiniteSubspace K_sub))
    (hA_lie : ∀ (X : 𝔤) (v : ↥(π₁.kFiniteSubspace K_sub)),
      A ⁅X, v⁆ = ⁅X, A v⁆)
    (hA_K : ∀ (k : K_sub) (v : ↥(π₁.kFiniteSubspace K_sub)),
      A ((kFiniteSubspace_kAction π₁ K_sub) k v) =
        (kFiniteSubspace_kAction π₂ K_sub) k (A v))
    (h_dense₁ : DenseRange (π₁.kFiniteSubspace K_sub).subtype)
    (h_dense₂ : DenseRange (π₂.kFiniteSubspace K_sub).subtype) :
    ∃ (h_norm : ∀ x : ↑(π₁.kFiniteSubspace K_sub),
        ‖(π₂.kFiniteSubspace K_sub).subtype (A x)‖ =
        ‖(π₁.kFiniteSubspace K_sub).subtype x‖),
    ∀ (g : G) (v : F₁),
      (A.extendOfIsometry (π₁.kFiniteSubspace K_sub).subtype
        (π₂.kFiniteSubspace K_sub).subtype h_dense₁ h_dense₂ h_norm)
        (π₁.toMonoidHom g v) =
      π₂.toMonoidHom g
        ((A.extendOfIsometry (π₁.kFiniteSubspace K_sub).subtype
          (π₂.kFiniteSubspace K_sub).subtype h_dense₁ h_dense₂ h_norm) v) := by
  sorry

end
