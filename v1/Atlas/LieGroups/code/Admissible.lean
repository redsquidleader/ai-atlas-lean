/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.ContinuousRep
import Atlas.LieGroups.code.KFinite
import Atlas.LieGroups.code.SmoothVectors
import Atlas.LieGroups.code.SmoothVectorsProps
import Atlas.LieGroups.code.SchurLemma

universe uF

noncomputable section

open scoped ComplexOrder Manifold

namespace ContinuousRep

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]

def IsAdmissible (π : ContinuousRep G V) (K : Subgroup G) : Prop :=
  ∀ (Wσ : Type*) [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ), σ.IsIrreducible →
    FiniteDimensional ℂ (π.IsotypicComponent K σ)

end ContinuousRep

theorem ContinuousLinearMap.continuous_symm_of_bijective
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [TopologicalSpace V₁]
    [IsTopologicalAddGroup V₁] [ContinuousSMul ℂ V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂] [TopologicalSpace V₂]
    [IsTopologicalAddGroup V₂] [ContinuousSMul ℂ V₂] [T2Space V₂]
    [FiniteDimensional ℂ V₂]
    (f : V₁ →L[ℂ] V₂) (hf : Function.Bijective f) :
    Continuous (LinearEquiv.ofBijective f.toLinearMap hf).symm :=
  (LinearEquiv.ofBijective f.toLinearMap hf).symm.toLinearMap.continuous_of_finiteDimensional

def ContinuousLinearMap.continuousLinearEquivOfBijective
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [TopologicalSpace V₁]
    [IsTopologicalAddGroup V₁] [ContinuousSMul ℂ V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂] [TopologicalSpace V₂]
    [IsTopologicalAddGroup V₂] [ContinuousSMul ℂ V₂] [T2Space V₂]
    [FiniteDimensional ℂ V₂]
    (f : V₁ →L[ℂ] V₂) (hf : Function.Bijective f) :
    V₁ ≃L[ℂ] V₂ := by
  let linEquiv : V₁ ≃ₗ[ℂ] V₂ := LinearEquiv.ofBijective f.toLinearMap hf
  exact ⟨linEquiv, f.continuous,
    ContinuousLinearMap.continuous_symm_of_bijective f hf⟩

theorem ContinuousLinearMap.continuousLinearEquivOfBijective_apply
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [TopologicalSpace V₁]
    [IsTopologicalAddGroup V₁] [ContinuousSMul ℂ V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂] [TopologicalSpace V₂]
    [IsTopologicalAddGroup V₂] [ContinuousSMul ℂ V₂] [T2Space V₂]
    [FiniteDimensional ℂ V₂]
    (f : V₁ →L[ℂ] V₂) (hf : Function.Bijective f) (v : V₁) :
    ContinuousLinearMap.continuousLinearEquivOfBijective f hf v = f v := by
  simp [ContinuousLinearMap.continuousLinearEquivOfBijective, LinearEquiv.ofBijective]

theorem ContinuousLinearMap.continuousLinearEquivOfBijective_coe
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [TopologicalSpace V₁]
    [IsTopologicalAddGroup V₁] [ContinuousSMul ℂ V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂] [TopologicalSpace V₂]
    [IsTopologicalAddGroup V₂] [ContinuousSMul ℂ V₂] [T2Space V₂]
    [FiniteDimensional ℂ V₂]
    (f : V₁ →L[ℂ] V₂) (hf : Function.Bijective f) :
    (ContinuousLinearMap.continuousLinearEquivOfBijective f hf : V₁ →L[ℂ] V₂) = f := by
  ext v
  exact ContinuousLinearMap.continuousLinearEquivOfBijective_apply f hf v

noncomputable def characterIntegralOperator
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) : F →L[ℂ] F := by sorry

theorem characterIntegralOperator_fixes_isotypic
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) :
    ∀ v, v ∈ π.IsotypicComponent K σ →
      characterIntegralOperator π K σ hirr v = v := by sorry

theorem characterIntegralOperator_range_isotypic
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) :
    ∀ v, characterIntegralOperator π K σ hirr v ∈ π.IsotypicComponent K σ := by sorry

theorem characterIntegralOperator_commutes
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) :
    ∀ (g : G) (v : F),
      characterIntegralOperator π K σ hirr ((π.toMonoidHom g) v) =
      (π.toMonoidHom g) (characterIntegralOperator π K σ hirr v) := by sorry

theorem characterIntegralOperator_annihilates
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) :
    ∀ (W' : Submodule ℂ F)
      (hW' : (π.restrictSubgroup K).IsInvariantSubspace W'),
      ((π.restrictSubgroup K).subrepresentation W' hW').IsIrreducible →
      ¬ Nonempty (RepEquiv
          ((π.restrictSubgroup K).subrepresentation W' hW') σ) →
      ∀ v ∈ W', characterIntegralOperator π K σ hirr v = 0 := by sorry

theorem schurProjector_exists_raw
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) :
    ∃ (P : F →L[ℂ] F),
      (∀ v, v ∈ π.IsotypicComponent K σ → P v = v) ∧
      (∀ v, P v ∈ π.IsotypicComponent K σ) ∧
      (∀ (g : G) (v : F), P ((π.toMonoidHom g) v) = (π.toMonoidHom g) (P v)) ∧
      (∀ (W' : Submodule ℂ F)
        (hW' : (π.restrictSubgroup K).IsInvariantSubspace W'),
        ((π.restrictSubgroup K).subrepresentation W' hW').IsIrreducible →
        ¬ Nonempty (RepEquiv
            ((π.restrictSubgroup K).subrepresentation W' hW') σ) →
        ∀ v ∈ W', P v = 0) :=
  ⟨characterIntegralOperator π K σ hirr,
   characterIntegralOperator_fixes_isotypic π K σ hirr,
   characterIntegralOperator_range_isotypic π K σ hirr,
   characterIntegralOperator_commutes π K σ hirr,
   characterIntegralOperator_annihilates π K σ hirr⟩

noncomputable def schurProjector
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) : F →L[ℂ] F :=
  (schurProjector_exists_raw π K σ hirr).choose

theorem schurProjector_fixes_isotypic
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) :
    ∀ v, v ∈ π.IsotypicComponent K σ → schurProjector π K σ hirr v = v :=
  (schurProjector_exists_raw π K σ hirr).choose_spec.1

theorem schurProjector_range_isotypic
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) :
    ∀ v, schurProjector π K σ hirr v ∈ π.IsotypicComponent K σ :=
  (schurProjector_exists_raw π K σ hirr).choose_spec.2.1

theorem schurProjector_commutes_action
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) :
    ∀ (g : G) (v : F),
      schurProjector π K σ hirr ((π.toMonoidHom g) v) =
        (π.toMonoidHom g) (schurProjector π K σ hirr v) :=
  (schurProjector_exists_raw π K σ hirr).choose_spec.2.2.1

theorem schurProjector_annihilates
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) :
    ∀ (W' : Submodule ℂ F)
      (hW' : (π.restrictSubgroup K).IsInvariantSubspace W'),
      ((π.restrictSubgroup K).subrepresentation W' hW').IsIrreducible →
      ¬ Nonempty (RepEquiv
          ((π.restrictSubgroup K).subrepresentation W' hW') σ) →
      ∀ v ∈ W', schurProjector π K σ hirr v = 0 :=
  (schurProjector_exists_raw π K σ hirr).choose_spec.2.2.2

theorem schurProjector_exists
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) :
    ∃ (P : F →L[ℂ] F),
      (∀ v, v ∈ π.IsotypicComponent K σ → P v = v) ∧
      (∀ v, P v ∈ π.IsotypicComponent K σ) ∧
      (∀ (g : G) (v : F), P ((π.toMonoidHom g) v) = (π.toMonoidHom g) (P v)) ∧
      (∀ (W' : Submodule ℂ F)
        (hW' : (π.restrictSubgroup K).IsInvariantSubspace W'),
        ((π.restrictSubgroup K).subrepresentation W' hW').IsIrreducible →
        ¬ Nonempty (RepEquiv
            ((π.restrictSubgroup K).subrepresentation W' hW') σ) →
        ∀ v ∈ W', P v = 0) :=
  ⟨schurProjector π K σ hirr,
   schurProjector_fixes_isotypic π K σ hirr,
   schurProjector_range_isotypic π K σ hirr,
   schurProjector_commutes_action π K σ hirr,
   schurProjector_annihilates π K σ hirr⟩

theorem clm_commuting_preserves_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F)
    (P : F →L[ℂ] F)
    (hcomm : ∀ (g : G) (v : F), P ((π.toMonoidHom g) v) = (π.toMonoidHom g) (P v)) :
    ∀ v, v ∈ π.smoothSubspace I → P v ∈ π.smoothSubspace I := by
  intro v hv

  show π.IsSmoothVector I (P v)
  have hv' : π.IsSmoothVector I v := hv
  unfold ContinuousRep.IsSmoothVector ContinuousRep.orbitMap at *


  have heq : (fun g : G => (π.toMonoidHom g) (P v)) =
             (fun g : G => P ((π.toMonoidHom g) v)) := by
    ext g; exact (hcomm g v).symm
  rw [heq]

  let P_real : F →L[ℝ] F := {
    toFun := P
    map_add' := P.map_add
    map_smul' := fun r w => by
      rw [show (r • w : F) = ((r : ℂ) • w : F) from by simp, map_smul]; simp
    cont := P.cont
  }
  exact P_real.contDiff.comp_contMDiff hv'

theorem schurProjector_commutes
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (_hirr : σ.IsIrreducible)
    (P : F →L[ℂ] F)
    (_hP_fix : ∀ v, v ∈ π.IsotypicComponent K σ → P v = v)
    (_hP_range : ∀ v, P v ∈ π.IsotypicComponent K σ)
    (hP_comm : ∀ (g : G) (v : F), P ((π.toMonoidHom g) v) = (π.toMonoidHom g) (P v)) :
    ∀ (g : G) (v : F), P ((π.toMonoidHom g) v) = (π.toMonoidHom g) (P v) :=
  hP_comm

theorem schurProjector_preserves_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible)
    (P : F →L[ℂ] F)
    (hP_fix : ∀ v, v ∈ π.IsotypicComponent K σ → P v = v)
    (hP_range : ∀ v, P v ∈ π.IsotypicComponent K σ)
    (hP_comm : ∀ (g : G) (v : F), P ((π.toMonoidHom g) v) = (π.toMonoidHom g) (P v)) :
    ∀ v, v ∈ π.smoothSubspace I → P v ∈ π.smoothSubspace I :=
  clm_commuting_preserves_smooth I π P
    (schurProjector_commutes π K σ hirr P hP_fix hP_range hP_comm)


theorem isotypicProjection_continuous_and_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) :
    ∃ (P : F →L[ℂ] F),
      (∀ v, v ∈ π.IsotypicComponent K σ → P v = v) ∧
      (∀ v, P v ∈ π.IsotypicComponent K σ) ∧
      (∀ v, v ∈ π.smoothSubspace I → P v ∈ π.smoothSubspace I) := by

  obtain ⟨P, hP_fix, hP_range, hP_comm, _hP_annihilate⟩ := schurProjector_exists π K σ hirr

  exact ⟨P, hP_fix, hP_range,
    schurProjector_preserves_smooth I π K σ hirr P hP_fix hP_range hP_comm⟩


theorem smoothSubspace_dense_of_lieGroup
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    [SecondCountableTopology G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]
    (π : ContinuousRep G F) :
    Dense (π.smoothSubspace I : Set F) := by

  haveI : T1Space G := I.t1Space G
  haveI : RegularSpace G := inferInstance
  haveI : T2Space G := inferInstance

  haveI : LocallyCompactSpace G := Manifold.locallyCompact_of_finiteDimensional I
  letI : MeasurableSpace G := borel G
  haveI : BorelSpace G := ⟨rfl⟩

  haveI : MeasurableMul G := ContinuousMul.measurableMul

  letI : MeasureTheory.MeasureSpace G := ⟨MeasureTheory.Measure.haar⟩

  haveI : MeasureTheory.Measure.IsHaarMeasure
      (MeasureTheory.MeasureSpace.volume (α := G)) :=
    MeasureTheory.Measure.isHaarMeasure_haarMeasure _

  have hGardDense := ContinuousRep.gardingSubspace_dense I π

  have hGardLeSmooth : (π.gardingSubspace I : Set F) ⊆ (π.smoothSubspace I : Set F) := by
    intro w hw
    have hsub : π.gardingSubspace I ≤ π.smoothSubspace I := by
      apply Submodule.span_le.mpr
      intro x ⟨f, v, hf, hx⟩
      rw [hx]
      exact ContinuousRep.gardingVector_isSmooth I π f hf v
    exact hsub hw

  exact Dense.mono hGardLeSmooth hGardDense

theorem smooth_dirac_approx
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    [SecondCountableTopology G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]
    (π : ContinuousRep G F) (v : F) :
    ∃ (vn : ℕ → F),
      (∀ n, vn n ∈ π.smoothSubspace I) ∧
      Filter.Tendsto vn Filter.atTop (nhds v) := by

  have hdense : Dense (π.smoothSubspace I : Set F) :=
    smoothSubspace_dense_of_lieGroup I π

  have hv_mem : v ∈ closure (π.smoothSubspace I : Set F) :=
    hdense.closure_eq ▸ trivial


  rwa [mem_closure_iff_seq_limit] at hv_mem

theorem smooth_vectors_dense_in_isotypic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    [SecondCountableTopology G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible) :
    (π.IsotypicComponent K σ : Set F) ⊆
      closure ((π.smoothSubspace I ⊓ π.IsotypicComponent K σ : Submodule ℂ F) : Set F) := by
  intro v hv

  obtain ⟨P, hP_fix, hP_range, hP_smooth⟩ :=
    isotypicProjection_continuous_and_smooth I π K σ hirr

  obtain ⟨vn, hvn_smooth, hvn_lim⟩ := smooth_dirac_approx I π v

  have hPv_eq : P v = v := hP_fix v hv
  have hPvn_lim : Filter.Tendsto (fun n => P (vn n)) Filter.atTop (nhds v) := by
    rw [← hPv_eq]
    exact Filter.Tendsto.comp P.continuous.continuousAt.tendsto hvn_lim

  have hPvn_mem : ∀ n, P (vn n) ∈
      ((π.smoothSubspace I ⊓ π.IsotypicComponent K σ : Submodule ℂ F) : Set F) := by
    intro n
    exact Submodule.mem_inf.mpr ⟨hP_smooth _ (hvn_smooth n), hP_range _⟩

  exact mem_closure_of_tendsto hPvn_lim (Filter.Eventually.of_forall hPvn_mem)

theorem isotypic_le_smooth_of_finiteDimensional
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    [SecondCountableTopology G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]
    (π : ContinuousRep G F) (K : Subgroup G)
    {Wσ : Type*} [AddCommGroup Wσ] [Module ℂ Wσ] [TopologicalSpace Wσ]
    (σ : ContinuousRep K Wσ) (hirr : σ.IsIrreducible)
    (hfin : FiniteDimensional ℂ (π.IsotypicComponent K σ)) :
    π.IsotypicComponent K σ ≤ π.smoothSubspace I := by

  have hdense := smooth_vectors_dense_in_isotypic I π K σ hirr

  set M := π.smoothSubspace I ⊓ π.IsotypicComponent K σ with hM_def
  haveI : FiniteDimensional ℂ M :=
    Submodule.finiteDimensional_of_le inf_le_right

  have hM_closed : IsClosed (M : Set F) := M.closed_of_finiteDimensional

  have hcl : closure (M : Set F) = (M : Set F) := hM_closed.closure_eq

  intro v hv
  have hv_in_cl := hdense hv
  rw [hcl] at hv_in_cl
  exact (Submodule.mem_inf.mp hv_in_cl).1

theorem haar_integral_averaging_axiom
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (πW_hom : K →* (W →L[ℂ] W))
    (U : Submodule ℂ W)
    (hU_inv : ∀ (g : K) (v : W), v ∈ U → (πW_hom g) v ∈ U)
    (p₀ : W →ₗ[ℂ] ↥U) (hp₀ : ∀ u : ↥U, p₀ (↑u : W) = u) :
    ∃ (p_lin : W →ₗ[ℂ] ↥U),
      (∀ u : ↥U, p_lin (↑u : W) = u) ∧
      (∀ (k : K) (v : W),
        (p_lin ((πW_hom k) v) : W) = (πW_hom k) ((p_lin v) : W)) := by sorry

theorem haar_averaging_retraction_core
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W]
    (πW : ContinuousRep K W)
    (U : Submodule ℂ W)
    (hU_inv : πW.IsInvariantSubspace U)
    (p₀ : W →ₗ[ℂ] ↥U) (hp₀ : ∀ u : ↥U, p₀ (↑u : W) = u) :
    ∃ (p : W →L[ℂ] ↥U),
      T1Space ↥U ∧
      (∀ u : ↥U, p (↑u : W) = u) ∧
      (∀ (k : K) (v : W),
        (p ((πW.toMonoidHom k) v) : W) = (πW.toMonoidHom k) ((p v) : W)) := by
  have hU_inv' : ∀ (g : K) (v : W), v ∈ U → (πW.toMonoidHom g) v ∈ U :=
    fun g v hv => hU_inv.invariant g v hv
  obtain ⟨p_lin, hp_ret, hp_equiv⟩ :=
    haar_integral_averaging_axiom πW.toMonoidHom U hU_inv' p₀ hp₀
  haveI : CompleteSpace ℂ := inferInstance
  let p_clm : W →L[ℂ] ↥U := LinearMap.toContinuousLinearMap p_lin
  refine ⟨p_clm, inferInstance, ?_, ?_⟩
  · intro u
    show (LinearMap.toContinuousLinearMap p_lin) ↑u = u
    rw [LinearMap.coe_toContinuousLinearMap']
    exact hp_ret u
  · intro k v
    show ↑((LinearMap.toContinuousLinearMap p_lin) ((πW.toMonoidHom k) v)) =
      (πW.toMonoidHom k) ↑((LinearMap.toContinuousLinearMap p_lin) v)
    simp only [LinearMap.coe_toContinuousLinearMap']
    exact hp_equiv k v

theorem haar_averaging_retraction
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W]
    (πW : ContinuousRep K W)
    (U : Submodule ℂ W)
    (hU_inv : πW.IsInvariantSubspace U)
    (p₀ : W →ₗ[ℂ] ↥U) (hp₀ : ∀ u : ↥U, p₀ (↑u : W) = u) :
    ∃ (p : W →ₗ[ℂ] ↥U),
      (∀ u : ↥U, p (↑u : W) = u) ∧
      (∀ (k : K) (v : W),
        (p ((πW.toMonoidHom k) v) : W) = (πW.toMonoidHom k) ((p v) : W)) ∧
      IsClosed (LinearMap.ker p : Set W) := by

  obtain ⟨p, hT1, hp_ret, hp_equiv⟩ :=
    haar_averaging_retraction_core πW U hU_inv p₀ hp₀
  exact ⟨p.toLinearMap, hp_ret, hp_equiv, by haveI := hT1; exact p.isClosed_ker⟩

theorem haar_equivariant_retraction_axiom
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W]
    (πW : ContinuousRep K W)
    (U : Submodule ℂ W)
    (hU_inv : πW.IsInvariantSubspace U) :
    ∃ (p : W →ₗ[ℂ] ↥U),
      (∀ u : ↥U, p (↑u : W) = u) ∧
      (∀ (k : K) (v : W),
        (p ((πW.toMonoidHom k) v) : W) = (πW.toMonoidHom k) ((p v) : W)) ∧
      IsClosed (LinearMap.ker p : Set W) := by

  obtain ⟨Q, hUQ⟩ := Submodule.exists_isCompl U

  let p₀ : W →ₗ[ℂ] ↥U := U.linearProjOfIsCompl Q hUQ
  have hp₀ : ∀ u : ↥U, p₀ (↑u : W) = u :=
    fun u => Submodule.linearProjOfIsCompl_apply_left hUQ u

  exact haar_averaging_retraction πW U hU_inv p₀ hp₀

theorem haar_invariant_complement_axiom
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W]
    (πW : ContinuousRep K W)
    (U : Submodule ℂ W)
    (hU_inv : πW.IsInvariantSubspace U) :
    ∃ (Q : Submodule ℂ W),
      IsCompl U Q ∧
      (∀ (k : K) (v : W), v ∈ Q → (πW.toMonoidHom k) v ∈ Q) ∧
      IsClosed (Q : Set W) := by

  obtain ⟨p, hp_ret, hp_equiv, hp_closed⟩ := haar_equivariant_retraction_axiom πW U hU_inv

  refine ⟨LinearMap.ker p, LinearMap.isCompl_of_proj hp_ret, ?_, ?_⟩

  · intro k v hv
    rw [LinearMap.mem_ker] at hv ⊢


    have h1 := hp_equiv k v
    rw [hv] at h1
    simp only [Submodule.coe_zero, map_zero] at h1
    exact Subtype.val_injective h1

  · exact hp_closed

theorem haar_equivariant_idempotent_projection_axiom
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W]
    (πW : ContinuousRep K W)
    (U : Submodule ℂ W)
    (hU_inv : πW.IsInvariantSubspace U) :
    ∃ (p : W →ₗ[ℂ] W),
      (p.comp p = p) ∧
      (p.range = U) ∧
      (∀ (k : K) (v : W), p ((πW.toMonoidHom k) v) = (πW.toMonoidHom k) (p v)) ∧
      (IsClosed (p.ker : Set W)) := by

  obtain ⟨Q, hUQ, hQ_inv, hQ_closed⟩ := haar_invariant_complement_axiom πW U hU_inv

  let proj := U.linearProjOfIsCompl Q hUQ
  let p : W →ₗ[ℂ] W := U.subtype ∘ₗ proj

  have proj_left : ∀ (u : ↥U), proj (U.subtype u) = u :=
    fun u => Submodule.linearProjOfIsCompl_apply_left hUQ u

  have proj_right : ∀ (w : W), w ∈ Q → proj w = 0 :=
    fun w hw => Submodule.linearProjOfIsCompl_apply_right' hUQ w hw
  refine ⟨p, ?_, ?_, ?_, ?_⟩

  · ext v
    show U.subtype (proj (U.subtype (proj v))) = U.subtype (proj v)
    congr 1
    exact proj_left (proj v)

  · ext w
    simp only [LinearMap.mem_range]
    constructor
    · rintro ⟨v, hv⟩
      rw [← hv]
      exact (proj v).2
    · intro hw
      exact ⟨w, show U.subtype (proj w) = w from by
        have h2 : U.subtype (⟨w, hw⟩ : ↥U) = w := rfl
        have h3 := proj_left ⟨w, hw⟩
        rw [show proj w = proj (U.subtype ⟨w, hw⟩) from by rw [h2]]
        rw [h3, h2]⟩


  · intro k v

    have hpv_mem : (p v : W) ∈ U := (proj v).2

    have hq_part : v - p v ∈ Q := by
      suffices h : proj (v - p v) = 0 by
        rwa [Submodule.linearProjOfIsCompl_apply_eq_zero_iff] at h

      show proj (v - U.subtype (proj v)) = 0
      rw [map_sub]

      have h := proj_left (proj v)
      rw [h]
      exact sub_self _

    have hkq_mem : (πW.toMonoidHom k) (v - p v) ∈ Q := hQ_inv k _ hq_part
    have hku_mem : (πW.toMonoidHom k) (p v) ∈ U := hU_inv.invariant k (p v) hpv_mem

    have hkv_eq : (πW.toMonoidHom k) v =
        (πW.toMonoidHom k) (p v) + (πW.toMonoidHom k) (v - p v) := by
      rw [map_sub]; abel
    rw [hkv_eq, map_add]

    have h1 : p ((πW.toMonoidHom k) (p v)) = (πW.toMonoidHom k) (p v) := by
      show U.subtype (proj ((πW.toMonoidHom k) (p v))) = (πW.toMonoidHom k) (p v)
      have h := proj_left ⟨(πW.toMonoidHom k) (p v), hku_mem⟩
      simp only [Submodule.subtype_apply] at h ⊢

      rw [h]

    have h2 : p ((πW.toMonoidHom k) (v - p v)) = 0 := by
      show U.subtype (proj ((πW.toMonoidHom k) (v - p v))) = 0
      rw [proj_right _ hkq_mem, map_zero]
    rw [h1, h2, add_zero]

  · have hker_eq : p.ker = Q := by
      ext w
      simp only [LinearMap.mem_ker]
      show U.subtype (proj w) = 0 ↔ w ∈ Q
      constructor
      · intro h
        have h2 : (proj w : ↥U) = 0 := by
          ext
          simpa using h
        rwa [Submodule.linearProjOfIsCompl_apply_eq_zero_iff] at h2
      · intro hw
        rw [proj_right _ hw, map_zero]
    rw [show (p.ker : Set W) = (Q : Set W) from by rw [hker_eq]]
    exact hQ_closed

theorem haar_invariant_complement_of_haar
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W]
    (πW : ContinuousRep K W)
    (U : Submodule ℂ W)
    (hU_inv : πW.IsInvariantSubspace U) :
    ∃ (Q : Submodule ℂ W), IsCompl U Q ∧
      IsClosed (Q : Set W) ∧
      ∀ (k : K) (v : W), v ∈ Q → (πW.toMonoidHom k) v ∈ Q := by

  obtain ⟨p, hp_idem, hp_range, hp_equiv, hp_ker_closed⟩ :=
    haar_equivariant_idempotent_projection_axiom πW U hU_inv

  refine ⟨p.ker, ?_, hp_ker_closed, ?_⟩

  · rw [← hp_range]
    exact LinearMap.IsIdempotentElem.isCompl hp_idem

  · intro k v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hp_equiv k v, hv, map_zero]

theorem haar_equivariant_projection
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W]
    (πW : ContinuousRep K W)
    (U : Submodule ℂ W)
    (hU_inv : πW.IsInvariantSubspace U) :
    ∃ (p : W →ₗ[ℂ] ↥U),
      (∀ u : ↥U, p (↑u : W) = u) ∧
      IsClosed (LinearMap.ker p : Set W) ∧
      (∀ (k : K) (v : W),
        (p ((πW.toMonoidHom k) v) : W) = (πW.toMonoidHom k) ((p v) : W)) := by

  obtain ⟨Q, hUQ, hQ_closed, hQ_inv⟩ := haar_invariant_complement_of_haar πW U hU_inv

  let p := U.linearProjOfIsCompl Q hUQ
  refine ⟨p, ?_, ?_, ?_⟩

  · exact Submodule.linearProjOfIsCompl_apply_left hUQ

  · have hker_eq : LinearMap.ker p = Q := Submodule.linearProjOfIsCompl_ker hUQ
    rw [show (LinearMap.ker p : Set W) = (Q : Set W) from by
      simp only [SetLike.coe_set_eq]; exact hker_eq]
    exact hQ_closed

  · intro k v

    have hq_mem : v - ↑(p v) ∈ Q := by
      have : v - ↑(p v) ∈ LinearMap.ker p := by
        rw [LinearMap.mem_ker, map_sub]
        rw [Submodule.linearProjOfIsCompl_apply_left hUQ (p v)]
        exact sub_self _
      rwa [Submodule.linearProjOfIsCompl_ker hUQ] at this

    have hkv_decomp : (πW.toMonoidHom k) v =
        (πW.toMonoidHom k) ↑(p v) + (πW.toMonoidHom k) (v - ↑(p v)) := by
      rw [map_sub, add_sub_cancel]

    have hku_mem : (πW.toMonoidHom k) (↑(p v) : W) ∈ U :=
      hU_inv.invariant k ↑(p v) (p v).prop

    have hkq_mem : (πW.toMonoidHom k) (v - ↑(p v)) ∈ Q :=
      hQ_inv k _ hq_mem

    set ku : W := (πW.toMonoidHom k) ↑(p v) with hku_def
    set kq : W := (πW.toMonoidHom k) (v - ↑(p v)) with hkq_def

    have hp_left : p ku = ⟨ku, hku_mem⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hUQ ⟨ku, hku_mem⟩
    have hp_right : p kq = 0 :=
      Submodule.linearProjOfIsCompl_apply_right hUQ ⟨kq, hkq_mem⟩
    have hp_kv : p ((πW.toMonoidHom k) v) = ⟨ku, hku_mem⟩ := by
      rw [hkv_decomp, map_add, hp_left, hp_right, add_zero]

    show ↑(p ((πW.toMonoidHom k) v)) = (πW.toMonoidHom k) ↑(p v)
    simp only [hp_kv, hku_def]

theorem haar_invariant_complement
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W]
    (πW : ContinuousRep K W)
    (U : Submodule ℂ W)
    (hU_inv : πW.IsInvariantSubspace U) :
    ∃ (Q : Submodule ℂ W), IsCompl U Q ∧
      IsClosed (Q : Set W) ∧
      ∀ (k : K) (v : W), v ∈ Q → (πW.toMonoidHom k) v ∈ Q := by

  obtain ⟨p, hp_retract, hp_closed, hp_equiv⟩ := haar_equivariant_projection πW U hU_inv

  refine ⟨LinearMap.ker p, LinearMap.isCompl_of_proj hp_retract, ?_, ?_⟩

  · exact hp_closed

  · intro k v hv
    rw [LinearMap.mem_ker] at hv ⊢


    have hpv_zero : p v = 0 := hv
    have hpv_coe : (p v : W) = (0 : W) := by rw [hpv_zero]; rfl
    ext
    rw [hp_equiv k v, hpv_coe, map_zero]
    rfl

theorem haar_equivariant_retraction
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G) [CompactSpace ↥K] [T2Space ↥K]
    (W : Submodule ℂ F)
    (hW_inv : (π.restrictSubgroup K).IsInvariantSubspace W)
    [FiniteDimensional ℂ W]
    (U : Submodule ℂ ↥W)
    (hU_inv : ((π.restrictSubgroup K).subrepresentation W hW_inv).IsInvariantSubspace U) :
    ∃ (p : ↥W →ₗ[ℂ] ↥U),
      (∀ u : ↥U, p (↑u : ↥W) = u) ∧
      (IsClosed (LinearMap.ker p : Set ↥W)) ∧
      (∀ (k : ↥K) (v : ↥W),
        (p (((π.restrictSubgroup K).subrepresentation W hW_inv).toMonoidHom k v) : ↥W) =
        ((π.restrictSubgroup K).subrepresentation W hW_inv).toMonoidHom k (↑(p v) : ↥W)) := by

  set πW := (π.restrictSubgroup K).subrepresentation W hW_inv with hπW_def


  obtain ⟨Q, hUQ, hQ_closed, hQ_inv⟩ := haar_invariant_complement πW U hU_inv

  let p := U.linearProjOfIsCompl Q hUQ
  refine ⟨p, ?_, ?_, ?_⟩

  · exact Submodule.linearProjOfIsCompl_apply_left hUQ

  · have hker_eq : LinearMap.ker p = Q := Submodule.linearProjOfIsCompl_ker hUQ
    rw [show (LinearMap.ker p : Set ↥W) = (Q : Set ↥W) from by
      simp only [SetLike.coe_set_eq]; exact hker_eq]
    exact hQ_closed

  · intro k v


    have hq_mem : v - ↑(p v) ∈ Q := by
      have : v - ↑(p v) ∈ LinearMap.ker p := by
        rw [LinearMap.mem_ker, map_sub]
        rw [Submodule.linearProjOfIsCompl_apply_left hUQ (p v)]
        exact sub_self _
      rwa [Submodule.linearProjOfIsCompl_ker hUQ] at this


    have hkv_decomp : (πW.toMonoidHom k) v =
        (πW.toMonoidHom k) ↑(p v) + (πW.toMonoidHom k) (v - ↑(p v)) := by
      rw [map_sub, add_sub_cancel]

    have hku_mem : (πW.toMonoidHom k) (↑(p v) : ↥W) ∈ U :=
      hU_inv.invariant k ↑(p v) (p v).prop

    have hkq_mem : (πW.toMonoidHom k) (v - ↑(p v)) ∈ Q :=
      hQ_inv k _ hq_mem

    set ku : ↥W := (πW.toMonoidHom k) ↑(p v) with hku_def
    set kq : ↥W := (πW.toMonoidHom k) (v - ↑(p v)) with hkq_def

    have hp_left : p ku = ⟨ku, hku_mem⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hUQ ⟨ku, hku_mem⟩
    have hp_right : p kq = 0 :=
      Submodule.linearProjOfIsCompl_apply_right hUQ ⟨kq, hkq_mem⟩

    have hp_kv : p ((πW.toMonoidHom k) v) = ⟨ku, hku_mem⟩ := by
      rw [hkv_decomp, map_add, hp_left, hp_right, add_zero]

    show ↑(p ((πW.toMonoidHom k) v)) = (πW.toMonoidHom k) ↑(p v)
    simp only [hp_kv, hku_def]

theorem compact_group_invariant_complement
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G) [CompactSpace ↥K] [T2Space ↥K]
    (W : Submodule ℂ F)
    (hW_inv : (π.restrictSubgroup K).IsInvariantSubspace W)
    [FiniteDimensional ℂ W]
    (U : Submodule ℂ ↥W)
    (hU_inv : ((π.restrictSubgroup K).subrepresentation W hW_inv).IsInvariantSubspace U) :
    ∃ (U' : Submodule ℂ ↥W),
      IsCompl U U' ∧
      ((π.restrictSubgroup K).subrepresentation W hW_inv).IsInvariantSubspace U' := by

  obtain ⟨p, hp_retract, hp_closed, hp_equiv⟩ :=
    haar_equivariant_retraction π K W hW_inv U hU_inv

  refine ⟨LinearMap.ker p, LinearMap.isCompl_of_proj hp_retract, ?_⟩

  let πW := (π.restrictSubgroup K).subrepresentation W hW_inv
  constructor
  ·
    exact hp_closed
  ·
    intro k v hv
    rw [LinearMap.mem_ker] at hv ⊢


    have : (↑(p (πW.toMonoidHom k v)) : ↥W) = πW.toMonoidHom k (↑(p v) : ↥W) :=
      hp_equiv k v
    simp only [hv, Submodule.coe_zero, map_zero] at this
    exact Subtype.val_injective this

theorem invariant_subspace_map_subtype
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G) [CompactSpace ↥K] [T2Space ↥K]

    (W : Submodule ℂ F)
    (hW_inv : (π.restrictSubgroup K).IsInvariantSubspace W)
    [FiniteDimensional ℂ W]
    (U : Submodule ℂ ↥W)
    (hU_inv : ((π.restrictSubgroup K).subrepresentation W hW_inv).IsInvariantSubspace U) :
    (π.restrictSubgroup K).IsInvariantSubspace (Submodule.map W.subtype U) where


  isClosed := by
    rw [Submodule.map_coe]
    exact (hW_inv.isClosed.isClosedEmbedding_subtypeVal.isClosedMap _ hU_inv.isClosed)


  invariant := by
    intro ⟨k, hk⟩ v hv
    rw [Submodule.mem_map] at hv ⊢
    obtain ⟨⟨w, hw⟩, hwU, hwv⟩ := hv

    have hkw := hU_inv.invariant ⟨k, hk⟩ ⟨w, hw⟩ hwU

    refine ⟨((π.restrictSubgroup K).subrepresentation W hW_inv).toMonoidHom ⟨k, hk⟩ ⟨w, hw⟩, hkw, ?_⟩


    subst hwv

    rfl

theorem map_subtype_lt_of_ne_top
    {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (W : Submodule R M) (U : Submodule R ↥W) (hU : U ≠ ⊤) :
    Submodule.map W.subtype U < W := by
  refine lt_of_le_of_ne (Submodule.map_subtype_le W U) ?_
  intro h
  apply hU
  rw [eq_top_iff]
  intro ⟨v, hv⟩ _
  have hmem : v ∈ Submodule.map W.subtype U := by rw [h]; exact hv
  rw [Submodule.mem_map] at hmem
  obtain ⟨⟨w, hw⟩, hwU, hwv⟩ := hmem
  have : (⟨v, hv⟩ : ↥W) = ⟨w, hw⟩ := Subtype.ext (by simpa using hwv.symm)
  rw [this]; exact hwU

theorem compact_group_maschke_step
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G) [CompactSpace ↥K] [T2Space ↥K]
    (W : Submodule ℂ F)
    (hW_inv : (π.restrictSubgroup K).IsInvariantSubspace W)
    [FiniteDimensional ℂ W]
    (hnirr : ¬ ((π.restrictSubgroup K).subrepresentation W hW_inv).IsIrreducible) :
    ∃ (W₁ W₂ : Submodule ℂ F),
      W₁ < W ∧ W₂ < W ∧ W₁ ⊔ W₂ = W ∧
      (π.restrictSubgroup K).IsInvariantSubspace W₁ ∧
      (π.restrictSubgroup K).IsInvariantSubspace W₂ := by

  simp only [ContinuousRep.IsIrreducible] at hnirr
  push Not at hnirr
  obtain ⟨U, hU_inv, hU_ne_bot, hU_ne_top⟩ := hnirr

  obtain ⟨U', hcompl, hU'_inv⟩ :=
    compact_group_invariant_complement π K W hW_inv U hU_inv

  have hU'_ne_top : U' ≠ ⊤ := by
    intro h
    apply hU_ne_bot
    have := hcompl.inf_eq_bot
    rw [h, inf_top_eq] at this
    exact this

  refine ⟨Submodule.map W.subtype U, Submodule.map W.subtype U', ?_, ?_, ?_, ?_, ?_⟩

  · exact map_subtype_lt_of_ne_top W U hU_ne_top

  · exact map_subtype_lt_of_ne_top W U' hU'_ne_top

  · rw [← Submodule.map_sup, hcompl.sup_eq_top, Submodule.map_subtype_top]

  · exact invariant_subspace_map_subtype π K W hW_inv U hU_inv

  · exact invariant_subspace_map_subtype π K W hW_inv U' hU'_inv

theorem compact_group_complete_reducibility_in_submodule
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G) [CompactSpace ↥K] [T2Space ↥K]

    (W : Submodule ℂ F)
    (hW_inv : (π.restrictSubgroup K).IsInvariantSubspace W)
    [FiniteDimensional ℂ W]
    (v : F) (hv : v ∈ W) :
    ∃ (n : ℕ) (ws : Fin n → F),
      v = ∑ i, ws i ∧
      ∀ i, ∃ (Wi : Submodule ℂ F),
        Wi ≤ W ∧
        ws i ∈ Wi ∧
        ∃ (hWi : (π.restrictSubgroup K).IsInvariantSubspace Wi),
          ((π.restrictSubgroup K).subrepresentation Wi hWi).IsIrreducible := by


  suffices h : ∀ (n : ℕ) (W : Submodule ℂ F)
      (hW_inv : (π.restrictSubgroup K).IsInvariantSubspace W)
      [FiniteDimensional ℂ W],
      Module.finrank ℂ ↥W = n →
      ∀ (v : F), v ∈ W →
      ∃ (m : ℕ) (ws : Fin m → F),
        v = ∑ i, ws i ∧
        ∀ i, ∃ (Wi : Submodule ℂ F),
          Wi ≤ W ∧
          ws i ∈ Wi ∧
          ∃ (hWi : (π.restrictSubgroup K).IsInvariantSubspace Wi),
            ((π.restrictSubgroup K).subrepresentation Wi hWi).IsIrreducible from
    h _ W hW_inv rfl v hv
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro W hW_inv _ hn v hv_mem

  by_cases hv0 : v = 0
  · exact ⟨0, Fin.elim0, by simp [hv0], fun i => Fin.elim0 i⟩

  by_cases hirr : ((π.restrictSubgroup K).subrepresentation W hW_inv).IsIrreducible
  · exact ⟨1, fun _ => v, by simp, fun _ => ⟨W, le_refl W, hv_mem, hW_inv, hirr⟩⟩

  · obtain ⟨W₁, W₂, hW₁_lt, hW₂_lt, hW_sup, hW₁_inv, hW₂_inv⟩ :=
      compact_group_maschke_step π K W hW_inv hirr

    have hv_sup : v ∈ (W₁ ⊔ W₂ : Submodule ℂ F) := hW_sup ▸ hv_mem
    rw [Submodule.mem_sup] at hv_sup
    obtain ⟨v₁, hv₁_mem, v₂, hv₂_mem, hv_eq⟩ := hv_sup

    have hW₁_le : W₁ ≤ W := le_of_lt hW₁_lt
    have hW₂_le : W₂ ≤ W := le_of_lt hW₂_lt
    haveI : FiniteDimensional ℂ ↥W₁ :=
      Submodule.finiteDimensional_of_le hW₁_le
    haveI : FiniteDimensional ℂ ↥W₂ :=
      Submodule.finiteDimensional_of_le hW₂_le

    have hfr₁ : Module.finrank ℂ ↥W₁ < n := by
      rw [← hn]; exact Submodule.finrank_lt_finrank_of_lt hW₁_lt
    have hfr₂ : Module.finrank ℂ ↥W₂ < n := by
      rw [← hn]; exact Submodule.finrank_lt_finrank_of_lt hW₂_lt

    obtain ⟨n₁, ws₁, hsum₁, hprop₁⟩ :=
      ih _ hfr₁ W₁ hW₁_inv rfl v₁ hv₁_mem
    obtain ⟨n₂, ws₂, hsum₂, hprop₂⟩ :=
      ih _ hfr₂ W₂ hW₂_inv rfl v₂ hv₂_mem

    refine ⟨n₁ + n₂, Fin.addCases ws₁ ws₂, ?_, ?_⟩
    ·
      have hsum_add := Fin.sum_univ_add (Fin.addCases ws₁ ws₂)
      simp only [Fin.addCases_left, Fin.addCases_right] at hsum_add
      rw [← hv_eq, hsum₁, hsum₂, hsum_add]

    ·
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      ·
        simp only [Fin.addCases_left]
        obtain ⟨Wi, hWi_le, hws_mem, hWi_inv, hWi_irr⟩ := hprop₁ j
        exact ⟨Wi, le_trans hWi_le hW₁_le, hws_mem, hWi_inv, hWi_irr⟩
      ·
        simp only [Fin.addCases_right]
        obtain ⟨Wi, hWi_le, hws_mem, hWi_inv, hWi_irr⟩ := hprop₂ j
        exact ⟨Wi, le_trans hWi_le hW₂_le, hws_mem, hWi_inv, hWi_irr⟩

theorem kfinite_le_isotypic_sup
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G) [CompactSpace ↥K] [T2Space ↥K]

    (v : F) (hv : π.IsKFinite K v) :
    ∃ (n : ℕ) (ws : Fin n → F),
      v = ∑ i, ws i ∧
      ∀ i, ∃ (Wσ : Type uF) (_ : AddCommGroup Wσ) (_ : Module ℂ Wσ) (_ : TopologicalSpace Wσ)
             (σ : ContinuousRep K Wσ), σ.IsIrreducible ∧
             ws i ∈ π.IsotypicComponent K σ := by

  set W := Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom (↑k)) v)) with hW_def
  haveI hv_fd : FiniteDimensional ℂ W := hv

  have hv_mem : v ∈ W := by
    apply Submodule.subset_span
    exact ⟨⟨1, K.one_mem⟩, by simp⟩

  have hW_inv : (π.restrictSubgroup K).IsInvariantSubspace W := by
    constructor
    ·
      exact W.closed_of_finiteDimensional
    ·
      intro ⟨k, hk⟩ w hw

      change (π.toMonoidHom (k : G)) w ∈ W

      have hgen : ∀ x ∈ Set.range (fun k' : K => (π.toMonoidHom (↑k')) v),
          (π.toMonoidHom (k : G)) x ∈ W := by
        rintro x ⟨⟨k', hk'⟩, rfl⟩

        have : (π.toMonoidHom (k : G)) ((π.toMonoidHom (k' : G)) v) =
            (π.toMonoidHom ((k : G) * (k' : G))) v := by
          rw [map_mul]; rfl
        rw [this]
        apply Submodule.subset_span
        exact ⟨⟨k * k', K.mul_mem hk hk'⟩, rfl⟩
      rw [hW_def] at hw
      exact Submodule.span_induction
        (p := fun x _ => (π.toMonoidHom (k : G)) x ∈ W)
        (fun x hx => hgen x hx)
        (by show (π.toMonoidHom (k : G)) 0 ∈ W; rw [map_zero]; exact W.zero_mem)
        (fun x y _ _ hxW hyW => by
          simp only [map_add]; exact W.add_mem hxW hyW)
        (fun c x _ hxW => by
          simp only [map_smul]; exact W.smul_mem c hxW)
        hw

  obtain ⟨n, ws, hsum, hirr_decomp⟩ :=
    compact_group_complete_reducibility_in_submodule π K W hW_inv v hv_mem

  exact ⟨n, ws, hsum, fun i => by
    obtain ⟨Wi, hWi_le, hwi_mem, hWi_inv, hWi_irr⟩ := hirr_decomp i

    let σ := (π.restrictSubgroup K).subrepresentation Wi hWi_inv

    have hWi_in_set : Wi ∈ { W' : Submodule ℂ F |
        ∃ (hW' : (π.restrictSubgroup K).IsInvariantSubspace W'),
          ((π.restrictSubgroup K).subrepresentation W' hW').IsIrreducible ∧
          Nonempty (RepEquiv
            ((π.restrictSubgroup K).subrepresentation W' hW') σ) } := by
      refine ⟨hWi_inv, hWi_irr, ⟨?_⟩⟩

      exact ⟨ContinuousLinearEquiv.refl ℂ _, fun g => by ext; rfl⟩

    have hWi_le_iso : Wi ≤ π.IsotypicComponent K σ :=
      le_sSup hWi_in_set
    exact ⟨↥Wi, inferInstance, inferInstance, inferInstance, σ, hWi_irr, hWi_le_iso hwi_mem⟩⟩

set_option maxHeartbeats 800000 in
theorem admissible_kfinite_le_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    [SecondCountableTopology G]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]
    (π : ContinuousRep G F) (K : Subgroup G) [CompactSpace ↥K] [T2Space ↥K]

    (hadm : ContinuousRep.IsAdmissible.{_, uF, uF} π K) :
    π.kFiniteSubspace K ≤ π.smoothSubspace I := by
  intro v hv

  obtain ⟨n, ws, hsum, hiso⟩ := kfinite_le_isotypic_sup π K v hv

  rw [hsum]
  apply Submodule.sum_mem
  intro i _

  obtain ⟨Wσ, instACG, instMod, instTop, σ, hirr, hmem⟩ := hiso i

  haveI hfin : FiniteDimensional ℂ (π.IsotypicComponent K σ) := hadm Wσ σ hirr

  exact isotypic_le_smooth_of_finiteDimensional I π K σ hirr hfin hmem

theorem exercise_5_8_ad_equivariance_axiom
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    (lieExp : E → G) :
    ∃ (Ad : ↥K → (E →ₗ[ℝ] E)),
      FiniteDimensional ℝ E ∧
      (∀ (k : ↥K) (X : E) (v : F),
        π.toMonoidHom (↑k) (π.derivedRep lieExp X v) =
          π.derivedRep lieExp ((Ad k) X) (π.toMonoidHom (↑k) v)) ∧
      (∀ (v : F), ∀ (a : ℝ) (X Y : E),
        π.derivedRep lieExp (a • X + Y) v =
          a • π.derivedRep lieExp X v + π.derivedRep lieExp Y v) := by sorry

theorem exercise_5_8_orbit_diff_axiom
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F)
    (lieExp : E → G) :
    ∀ (X : E) (u : F), DifferentiableAt ℝ
      (fun (t : ℝ) => (π.toMonoidHom (lieExp (t • X))) u) 0 := by sorry


theorem exercise_5_8_core_axiom
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    (lieExp : E → G) :
    ∃ (Ad : ↥K → (E →ₗ[ℝ] E)),
      FiniteDimensional ℝ E ∧
      (∀ (k : ↥K) (X : E) (v : F),
        π.toMonoidHom (↑k) (π.derivedRep lieExp X v) =
          π.derivedRep lieExp ((Ad k) X) (π.toMonoidHom (↑k) v)) ∧
      (∀ (v : F), ∀ (a : ℝ) (X Y : E),
        π.derivedRep lieExp (a • X + Y) v =
          a • π.derivedRep lieExp X v + π.derivedRep lieExp Y v) ∧
      (∀ (X : E) (u : F), DifferentiableAt ℝ
        (fun (t : ℝ) => (π.toMonoidHom (lieExp (t • X))) u) 0) := by
  obtain ⟨Ad, hfin, hequiv, hRlin⟩ := exercise_5_8_ad_equivariance_axiom I π K lieExp
  exact ⟨Ad, hfin, hequiv, hRlin, exercise_5_8_orbit_diff_axiom I π lieExp⟩

theorem exercise_5_8_equivariance

    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    (lieExp : E → G) :
    ∃ (Ad : ↥K → (E →ₗ[ℝ] E)),

      FiniteDimensional ℝ E ∧

      (∀ (k : ↥K) (X : E) (v : F),
        π.toMonoidHom (↑k) (π.derivedRep lieExp X v) =
          π.derivedRep lieExp ((Ad k) X) (π.toMonoidHom (↑k) v)) ∧

      (∀ (v : F), ∀ (a : ℝ) (X Y : E),
        π.derivedRep lieExp (a • X + Y) v =
          a • π.derivedRep lieExp X v + π.derivedRep lieExp Y v) ∧

      (∀ (X : E) (c : ℂ) (v w : F),
        π.derivedRep lieExp X (c • v + w) =
          c • π.derivedRep lieExp X v + π.derivedRep lieExp X w) := by


  obtain ⟨Ad, hfin, hequiv, hRlin, hdiff⟩ :
    ∃ (Ad : ↥K → (E →ₗ[ℝ] E)),
      FiniteDimensional ℝ E ∧
      (∀ (k : ↥K) (X : E) (v : F),
        π.toMonoidHom (↑k) (π.derivedRep lieExp X v) =
          π.derivedRep lieExp ((Ad k) X) (π.toMonoidHom (↑k) v)) ∧
      (∀ (v : F), ∀ (a : ℝ) (X Y : E),
        π.derivedRep lieExp (a • X + Y) v =
          a • π.derivedRep lieExp X v + π.derivedRep lieExp Y v) ∧
      (∀ (X : E) (u : F), DifferentiableAt ℝ
        (fun (t : ℝ) => (π.toMonoidHom (lieExp (t • X))) u) 0) :=
    exercise_5_8_core_axiom I π K lieExp
  refine ⟨Ad, hfin, hequiv, hRlin, ?_⟩


  intro X c v w
  simp only [ContinuousRep.derivedRep, map_add, map_smul]
  exact ((hdiff X v).hasDerivAt.const_smul c |>.add (hdiff X w).hasDerivAt).deriv

lemma isKFinite_of_orbit_le_finiteDim
    {G : Type*} [Group G] [TopologicalSpace G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G) (w : F)
    (W : Submodule ℂ F) [FiniteDimensional ℂ W]

    (hle : Submodule.span ℂ (Set.range (fun k : ↥K => π.toMonoidHom (↑k) w)) ≤ W) :
    ContinuousRep.IsKFinite π K w := by
  unfold ContinuousRep.IsKFinite
  exact Module.Finite.of_injective
    (Submodule.inclusion hle) (Submodule.inclusion_injective hle)

end
