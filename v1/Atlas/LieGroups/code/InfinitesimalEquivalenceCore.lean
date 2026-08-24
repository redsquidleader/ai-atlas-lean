/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.GKModule
import Atlas.LieGroups.code.GKModuleDefs
import Atlas.LieGroups.code.HarishChandraFunctor
import Atlas.LieGroups.code.Admissible
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Module.Completion

noncomputable section

structure GKModuleIso
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W]
    (M : GKModule 𝔤 K 𝔨 Ad V) (N : GKModule 𝔤 K 𝔨 Ad W) where
  toLinearEquiv : V ≃ₗ[ℂ] W
  lie_comm : ∀ (X : 𝔤) (v : V), toLinearEquiv ⁅X, v⁆ = ⁅X, toLinearEquiv v⁆
  group_comm : ∀ (k : K) (v : V), toLinearEquiv (M.σ k v) = N.σ k (toLinearEquiv v)

def InfinitesimallyEquivalent
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [LieRingModule 𝔤 V₁] [LieModule ℂ 𝔤 V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    [LieRingModule 𝔤 V₂] [LieModule ℂ 𝔤 V₂]
    (M₁ : GKModule 𝔤 K 𝔨 Ad V₁) (M₂ : GKModule 𝔤 K 𝔨 Ad V₂) : Prop :=
  Nonempty (GKModuleIso M₁ M₂)

structure GKModule.IsUnitary
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) where
  form : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ
  conj_symm : ∀ (v w : V), form w v = starRingEnd ℂ (form v w)
  re_nonneg : ∀ (v : V), 0 ≤ (form v v).re
  definite : ∀ (v : V), form v v = 0 → v = 0
  pos_def : ∀ v : V, v ≠ 0 → 0 < (form v v).re
  K_invariant : ∀ (k : K) (v w : V), form (M.σ k v) (M.σ k w) = form v w
  lie_invariant : ∀ (X : 𝔤) (v w : V), form ⁅X, v⁆ w + form v ⁅X, w⁆ = 0

def GKModule.IsUnitary.mk'
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (form : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (conj_symm : ∀ (v w : V), form w v = starRingEnd ℂ (form v w))
    (pos_def : ∀ v : V, v ≠ 0 → 0 < (form v v).re)
    (K_invariant : ∀ (k : K) (v w : V), form (M.σ k v) (M.σ k w) = form v w)
    (lie_invariant : ∀ (X : 𝔤) (v w : V), form ⁅X, v⁆ w + form v ⁅X, w⁆ = 0) :
    M.IsUnitary where
  form := form
  conj_symm := conj_symm
  re_nonneg := fun v => by
    by_cases hv : v = 0
    · subst hv; simp [map_zero, LinearMap.map_zero]
    · exact le_of_lt (pos_def v hv)
  definite := fun v hfv => by
    by_contra hv
    have h := pos_def v hv
    rw [hfv, Complex.zero_re] at h
    exact lt_irrefl 0 h
  pos_def := pos_def
  K_invariant := K_invariant
  lie_invariant := lie_invariant

noncomputable def GKModule.IsUnitary.toInnerProductSpaceCore
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {M : GKModule 𝔤 K 𝔨 Ad V}
    (hu : M.IsUnitary) : InnerProductSpace.Core ℂ V where
  inner v w := hu.form v w
  conj_inner_symm x y := (hu.conj_symm y x).symm
  re_inner_nonneg x := hu.re_nonneg x
  add_left x y z := by simp [map_add, LinearMap.add_apply]
  smul_left x y r := by simp [LinearMapClass.map_smul]
  definite x hx := hu.definite x (by exact_mod_cast hx)

structure Globalization
    (G : Type*) [Group G] [TopologicalSpace G]
    {K : Type*} [Group K]
    (K_sub : K →* G)
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) where
  Ŵ : Type*
  instNACG : NormedAddCommGroup Ŵ
  instIPS : @InnerProductSpace ℂ Ŵ _ instNACG.toSeminormedAddCommGroup
  instCS : @CompleteSpace Ŵ instNACG.toUniformSpace
  π : @ContinuousRep G _ _ Ŵ instNACG.toAddCommGroup instIPS.toNormedSpace.toModule
      instNACG.toUniformSpace.toTopologicalSpace
  isUnitary : @ContinuousRep.IsUnitary G _ _ Ŵ instNACG instIPS instCS π
  isIrreducible : @ContinuousRep.IsIrreducible G _ _ Ŵ
      instNACG.toAddCommGroup instIPS.toNormedSpace.toModule
      instNACG.toUniformSpace.toTopologicalSpace π
  ι : @LinearMap ℂ ℂ _ _ (RingHom.id ℂ) V Ŵ
      _ instNACG.toAddCommGroup.toAddCommMonoid _ instIPS.toNormedSpace.toModule
  ι_injective : Function.Injective ι
  K_compat : ∀ (k : K) (v : V), ι (M.σ k v) = (π.toMonoidHom (K_sub k)) (ι v)
  lie_action_Ŵ : 𝔤 → Ŵ → Ŵ
  lie_compat_ι : ∀ (X : 𝔤) (v : V), ι ⁅X, v⁆ = lie_action_Ŵ X (ι v)
  kfin_image : Set.range ι =
    ↑(@ContinuousRep.kFiniteSubspace G _ _ Ŵ
      instNACG.toAddCommGroup instIPS.toNormedSpace.toModule
      instNACG.toUniformSpace.toTopologicalSpace
      π K_sub.range)

attribute [instance] Globalization.instNACG Globalization.instIPS Globalization.instCS

noncomputable def hilbertCompletionBundle
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (_hunit : M.IsUnitary) :
    Σ' (W : Type _) (nacg : NormedAddCommGroup W)
       (ips : @InnerProductSpace ℂ W _ nacg.toSeminormedAddCommGroup)
       (_ : @CompleteSpace W nacg.toUniformSpace)
       (emb : @LinearMap ℂ ℂ _ _ (RingHom.id ℂ) V W
         _ nacg.toAddCommGroup.toAddCommMonoid
         _ ips.toNormedSpace.toModule),
       Function.Injective emb := by sorry

noncomputable def hilbertCompletionType
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hunit : M.IsUnitary) : Type* :=
  (hilbertCompletionBundle M hunit).1

@[reducible] noncomputable def hilbertCompletion_instNACG
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K] {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hunit : M.IsUnitary) :
    NormedAddCommGroup (hilbertCompletionType M hunit) :=
  (hilbertCompletionBundle M hunit).2.1

@[reducible] noncomputable def hilbertCompletion_instIPS
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K] {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hunit : M.IsUnitary) :
    @InnerProductSpace ℂ (hilbertCompletionType M hunit) _
      (hilbertCompletion_instNACG M hunit).toSeminormedAddCommGroup :=
  (hilbertCompletionBundle M hunit).2.2.1

@[reducible] noncomputable def hilbertCompletion_instCS
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K] {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hunit : M.IsUnitary) :
    @CompleteSpace (hilbertCompletionType M hunit)
      (hilbertCompletion_instNACG M hunit).toUniformSpace :=
  (hilbertCompletionBundle M hunit).2.2.2.1

noncomputable def hilbertCompletion_embedding
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K] {𝔨 : LieSubalgebra ℂ 𝔤} {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V) (hunit : M.IsUnitary) :
    @LinearMap ℂ ℂ _ _ (RingHom.id ℂ) V (hilbertCompletionType M hunit)
      _ (hilbertCompletion_instNACG M hunit).toAddCommGroup.toAddCommMonoid
      _ (hilbertCompletion_instIPS M hunit).toNormedSpace.toModule :=
  (hilbertCompletionBundle M hunit).2.2.2.2.1

theorem hilbertCompletionRepBundle_axiom
    (G : Type*) [Group G] [TopologicalSpace G]
    {K : Type*} [Group K]
    (K_sub : K →* G)
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (hirr : M.IsIrreducibleGKModule)
    (hunit : M.IsUnitary) :
    Nonempty (Globalization G K_sub M) := by sorry

theorem globalization_rep_admissible_axiom
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K : Type*} [Group K]
    {K_sub : K →* G}
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {M : GKModule 𝔤 K 𝔨 Ad V}
    (G_glob : Globalization G K_sub M)
    (hirr : M.IsIrreducibleGKModule)
    (hunit : M.IsUnitary) :
    @ContinuousRep.IsAdmissible G _ _ _ G_glob.Ŵ
      G_glob.instNACG.toAddCommGroup G_glob.instIPS.toNormedSpace.toModule
      G_glob.instNACG.toUniformSpace.toTopologicalSpace
      G_glob.π K_sub.range := by sorry

theorem gk_morphism_norm_bound_axiom
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Type*} [Group K]
    {K_sub : K →* G}
    [CompactSpace K_sub.range]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [LieRingModule 𝔤 V₁] [LieModule ℂ 𝔤 V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    [LieRingModule 𝔤 V₂] [LieModule ℂ 𝔤 V₂]
    (M₁ : GKModule 𝔤 K 𝔨 Ad V₁) (M₂ : GKModule 𝔤 K 𝔨 Ad V₂)
    (G₁ : Globalization G K_sub M₁) (G₂ : Globalization G K_sub M₂)
    (φ : GKModuleHom M₁ M₂) :
    ∃ (C : ℝ), ∀ (v : V₁),
      @norm G₂.Ŵ G₂.instNACG.toNorm (G₂.ι (φ.toLinearMap v)) ≤
        C * @norm G₁.Ŵ G₁.instNACG.toNorm (G₁.ι v) := by sorry

theorem gk_morphism_extension_equivariant_axiom
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Type*} [Group K]
    {K_sub : K →* G}
    [CompactSpace K_sub.range]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [LieRingModule 𝔤 V₁] [LieModule ℂ 𝔤 V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    [LieRingModule 𝔤 V₂] [LieModule ℂ 𝔤 V₂]
    (M₁ : GKModule 𝔤 K 𝔨 Ad V₁) (M₂ : GKModule 𝔤 K 𝔨 Ad V₂)
    (G₁ : Globalization G K_sub M₁) (G₂ : Globalization G K_sub M₂)
    (φ : GKModuleHom M₁ M₂)
    (T : G₁.Ŵ → G₂.Ŵ)
    (hT_cont : @Continuous G₁.Ŵ G₂.Ŵ
      G₁.instNACG.toUniformSpace.toTopologicalSpace
      G₂.instNACG.toUniformSpace.toTopologicalSpace T)
    (hT_ext : ∀ (v : V₁), T (G₁.ι v) = G₂.ι (φ.toLinearMap v)) :
    ∀ (g : G) (w : G₁.Ŵ),
      T ((G₁.π.toMonoidHom g) w) = (G₂.π.toMonoidHom g) (T w) := by sorry

theorem harish_chandra_globalization_exists
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Type*} [Group K]
    {K_sub : K →* G}
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (hirr : M.IsIrreducibleGKModule)
    (hunit : M.IsUnitary) :
    Nonempty (Globalization G K_sub M) :=
  hilbertCompletionRepBundle_axiom G K_sub M hirr hunit

theorem harish_chandra_globalization_admissible
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K : Type*} [Group K]
    {K_sub : K →* G}
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (hirr : M.IsIrreducibleGKModule)
    (hunit : M.IsUnitary)
    (G_glob : Globalization G K_sub M) :
    @ContinuousRep.IsAdmissible G _ _ _ G_glob.Ŵ
      G_glob.instNACG.toAddCommGroup G_glob.instIPS.toNormedSpace.toModule
      G_glob.instNACG.toUniformSpace.toTopologicalSpace
      G_glob.π K_sub.range :=
  globalization_rep_admissible_axiom G_glob hirr hunit

theorem Globalization.ι_denseRange
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Type*} [Group K]
    {K_sub : K →* G}
    [CompactSpace K_sub.range]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (G_glob : Globalization G K_sub M) :
    @DenseRange G_glob.Ŵ
      G_glob.instNACG.toUniformSpace.toTopologicalSpace V G_glob.ι := by
  letI := G_glob.instNACG
  letI := G_glob.instIPS
  letI := G_glob.instCS
  have hdense : Dense (ContinuousRep.kFiniteSubspace G_glob.π K_sub.range : Set G_glob.Ŵ) :=
    ContinuousRep.kFiniteSubspace_dense G_glob.π K_sub.range
  rw [DenseRange, G_glob.kfin_image]
  exact hdense

theorem globalization_hom_extension
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Type*} [Group K]
    {K_sub : K →* G}
    [CompactSpace K_sub.range]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁]
    [LieRingModule 𝔤 V₁] [LieModule ℂ 𝔤 V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    [LieRingModule 𝔤 V₂] [LieModule ℂ 𝔤 V₂]
    (M₁ : GKModule 𝔤 K 𝔨 Ad V₁) (M₂ : GKModule 𝔤 K 𝔨 Ad V₂)
    (G₁ : Globalization G K_sub M₁) (G₂ : Globalization G K_sub M₂)
    (φ : GKModuleHom M₁ M₂) :
    ∃ (T : G₁.Ŵ → G₂.Ŵ),
      (@Continuous G₁.Ŵ G₂.Ŵ
        G₁.instNACG.toUniformSpace.toTopologicalSpace
        G₂.instNACG.toUniformSpace.toTopologicalSpace T) ∧
      (∀ (g : G) (w : G₁.Ŵ),
        T ((G₁.π.toMonoidHom g) w) = (G₂.π.toMonoidHom g) (T w)) ∧
      (∀ (v : V₁), T (G₁.ι v) = G₂.ι (φ.toLinearMap v)) := by

  have h_bound := gk_morphism_norm_bound_axiom M₁ M₂ G₁ G₂ φ

  letI := G₁.instNACG
  letI := G₁.instIPS
  letI := G₁.instCS
  letI := G₂.instNACG
  letI := G₂.instIPS
  letI := G₂.instCS
  let f : V₁ →ₗ[ℂ] G₂.Ŵ := G₂.ι.comp φ.toLinearMap
  let e : V₁ →ₗ[ℂ] G₁.Ŵ := G₁.ι
  have h_dense : DenseRange e := Globalization.ι_denseRange M₁ G₁
  let T_cl := LinearMap.extendOfNorm f e
  have hT_cont : Continuous T_cl := T_cl.continuous
  have hT_ext : ∀ (v : V₁), T_cl (G₁.ι v) = G₂.ι (φ.toLinearMap v) :=
    fun v => LinearMap.extendOfNorm_eq h_dense h_bound v

  have hT_equiv := gk_morphism_extension_equivariant_axiom M₁ M₂ G₁ G₂ φ T_cl hT_cont hT_ext
  exact ⟨T_cl, hT_cont, hT_equiv, hT_ext⟩

theorem harish_chandra_globalization_unique
    {G : Type*} [Group G] [TopologicalSpace G]
    {K : Type*} [Group K]
    {K_sub : K →* G}
    [CompactSpace K_sub.range]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (_hirr : M.IsIrreducibleGKModule)
    (_hunit : M.IsUnitary)
    (G₁ G₂ : Globalization G K_sub M) :
    ∃ (U : G₁.Ŵ → G₂.Ŵ),
      Function.Bijective U ∧
      (∀ (g : G) (w : G₁.Ŵ),
        U ((G₁.π.toMonoidHom g) w) = (G₂.π.toMonoidHom g) (U w)) ∧
      (∀ (v : V), U (G₁.ι v) = G₂.ι v) := by

  let φ_id : GKModuleHom M M :=
    { toLinearMap := LinearMap.id
      lie_comm := fun _ _ => rfl
      group_comm := fun _ _ => rfl }

  obtain ⟨U, hU_cont, hU_equiv, hU_ext⟩ := globalization_hom_extension M M G₁ G₂ φ_id
  have hU_ext' : ∀ (v : V), U (G₁.ι v) = G₂.ι v := by
    intro v; rw [hU_ext v]; simp [φ_id]
  obtain ⟨S, hS_cont, _, hS_ext⟩ := globalization_hom_extension M M G₂ G₁ φ_id
  have hS_ext' : ∀ (v : V), S (G₂.ι v) = G₁.ι v := by
    intro v; rw [hS_ext v]; simp [φ_id]

  let top₁ := G₁.instNACG.toUniformSpace.toTopologicalSpace
  let top₂ := G₂.instNACG.toUniformSpace.toTopologicalSpace
  have hSU_eq : ∀ w, S (U w) = w := by
    have h_agree : (S ∘ U) ∘ G₁.ι = id ∘ G₁.ι := by
      ext v; simp [Function.comp, hU_ext', hS_ext']
    have h_dense₁ : @DenseRange G₁.Ŵ top₁ V G₁.ι := Globalization.ι_denseRange M G₁
    haveI : @T2Space G₁.Ŵ top₁ := inferInstance
    have hSU_cont : @Continuous G₁.Ŵ G₁.Ŵ top₁ top₁ (S ∘ U) := hS_cont.comp hU_cont
    have := @DenseRange.equalizer V G₁.Ŵ G₁.Ŵ top₁ top₁ ‹_› G₁.ι h_dense₁
      (g := S ∘ U) (h := id) hSU_cont continuous_id h_agree
    exact congr_fun this

  have hUS_eq : ∀ w, U (S w) = w := by
    have h_agree : (U ∘ S) ∘ G₂.ι = id ∘ G₂.ι := by
      ext v; simp [Function.comp, hS_ext', hU_ext']
    have h_dense₂ : @DenseRange G₂.Ŵ top₂ V G₂.ι := Globalization.ι_denseRange M G₂
    haveI : @T2Space G₂.Ŵ top₂ := inferInstance
    have hUS_cont : @Continuous G₂.Ŵ G₂.Ŵ top₂ top₂ (U ∘ S) := hU_cont.comp hS_cont
    have := @DenseRange.equalizer V G₂.Ŵ G₂.Ŵ top₂ top₂ ‹_› G₂.ι h_dense₂
      (g := U ∘ S) (h := id) hUS_cont continuous_id h_agree
    exact congr_fun this

  have hU_bij : Function.Bijective U := by
    constructor
    · intro x y hxy
      have := congr_arg S hxy
      rwa [hSU_eq, hSU_eq] at this
    · intro w₂
      exact ⟨S w₂, hUS_eq w₂⟩
  exact ⟨U, hU_bij, hU_equiv, hU_ext'⟩

end
