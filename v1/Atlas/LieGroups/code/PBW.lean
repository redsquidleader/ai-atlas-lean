/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.VermaModules
import Mathlib.RingTheory.TensorProduct.Basic

noncomputable section

open scoped TensorProduct

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]

def pbw_triangular_iso (Δ : TriangularDecomposition R 𝔤) :
    (TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔫_neg)
      (TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔥)
                       (UniversalEnvelopingAlgebra R Δ.𝔫_pos))) ≃ₗ[R]
    UniversalEnvelopingAlgebra R 𝔤 := by
  exact sorry

theorem pbw_triangular_iso_maps_one (Δ : TriangularDecomposition R 𝔤) :
    pbw_triangular_iso R 𝔤 Δ
      ((1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) ⊗ₜ[R]
        ((1 : UniversalEnvelopingAlgebra R Δ.𝔥) ⊗ₜ[R]
          (1 : UniversalEnvelopingAlgebra R Δ.𝔫_pos))) =
      (1 : UniversalEnvelopingAlgebra R 𝔤) := by
  sorry

theorem pbw_triangular_iso_one
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤) :
    pbw_triangular_iso R 𝔤 Δ
      ((1 : UniversalEnvelopingAlgebra R Δ.𝔫_neg) ⊗ₜ[R]
        ((1 : UniversalEnvelopingAlgebra R Δ.𝔥) ⊗ₜ[R]
          (1 : UniversalEnvelopingAlgebra R Δ.𝔫_pos))) =
      (1 : UniversalEnvelopingAlgebra R 𝔤) :=
  pbw_triangular_iso_maps_one R 𝔤 Δ

def pbw_triangular_inv (Δ : TriangularDecomposition R 𝔤) :
    UniversalEnvelopingAlgebra R 𝔤 ≃ₗ[R]
    (TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔫_neg)
      (TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔥)
                       (UniversalEnvelopingAlgebra R Δ.𝔫_pos))) :=
  (pbw_triangular_iso R 𝔤 Δ).symm

def pbw_assoc_iso (Δ : TriangularDecomposition R 𝔤) :
    (TensorProduct R
      (TensorProduct R (UniversalEnvelopingAlgebra R Δ.𝔫_neg)
                       (UniversalEnvelopingAlgebra R Δ.𝔥))
      (UniversalEnvelopingAlgebra R Δ.𝔫_pos)) ≃ₗ[R]
    UniversalEnvelopingAlgebra R 𝔤 :=
  (TensorProduct.assoc R _ _ _) ≪≫ₗ pbw_triangular_iso R 𝔤 Δ
theorem pbw_weightSpace_surjection_from_fin
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (S : Finset M)
    (hS : LieSubmodule.lieSpan R 𝔤 (S : Set M) = ⊤)
    (hS_wt : ∀ v ∈ S, ∃ wt : Δ.𝔥 →ₗ[R] R, v ∈ WeightSpace Δ M wt)
    (hbnd : ∃ (bds : Finset (Δ.𝔥 →ₗ[R] R)),
      ∀ ν ∈ weights Δ M, ∃ w ∈ bds, rd.IsInQPlus (w - ν))
    (μ : Δ.𝔥 →ₗ[R] R)
    (hμ : WeightSpace Δ M μ ≠ ⊥) :
    ∃ (n : ℕ) (φ : (Fin n → R) →ₗ[R] (WeightSpace Δ M μ)),
      Function.Surjective φ := by sorry

theorem pbw_weightSpace_moduleFinite
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (S : Finset M)
    (hS : LieSubmodule.lieSpan R 𝔤 (S : Set M) = ⊤)
    (hS_wt : ∀ v ∈ S, ∃ wt : Δ.𝔥 →ₗ[R] R, v ∈ WeightSpace Δ M wt)
    (hbnd : ∃ (bds : Finset (Δ.𝔥 →ₗ[R] R)),
      ∀ ν ∈ weights Δ M, ∃ w ∈ bds, rd.IsInQPlus (w - ν))
    (μ : Δ.𝔥 →ₗ[R] R)
    (hμ : WeightSpace Δ M μ ≠ ⊥) :
    Module.Finite R (WeightSpace Δ M μ) := by

  obtain ⟨n, φ, hφ⟩ := pbw_weightSpace_surjection_from_fin S hS hS_wt hbnd μ hμ

  exact Module.Finite.of_surjective φ hφ

theorem pbw_weightSpace_spanFinite_axiom
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (S : Finset M)
    (hS : LieSubmodule.lieSpan R 𝔤 (S : Set M) = ⊤)
    (hS_wt : ∀ v ∈ S, ∃ wt : Δ.𝔥 →ₗ[R] R, v ∈ WeightSpace Δ M wt)
    (hbnd : ∃ (bds : Finset (Δ.𝔥 →ₗ[R] R)),
      ∀ ν ∈ weights Δ M, ∃ w ∈ bds, rd.IsInQPlus (w - ν))
    (μ : Δ.𝔥 →ₗ[R] R)
    (hμ : WeightSpace Δ M μ ≠ ⊥) :
    ∃ (T : Finset (WeightSpace Δ M μ)),
      Submodule.span R (T : Set (WeightSpace Δ M μ)) = ⊤ := by
  have hfin := pbw_weightSpace_moduleFinite S hS hS_wt hbnd μ hμ
  exact hfin.fg_top

theorem pbw_weightSpace_spanFinite
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (S : Finset M)
    (hS : LieSubmodule.lieSpan R 𝔤 (S : Set M) = ⊤)
    (hS_wt : ∀ v ∈ S, ∃ wt : Δ.𝔥 →ₗ[R] R, v ∈ WeightSpace Δ M wt)
    (hbnd : ∃ (bds : Finset (Δ.𝔥 →ₗ[R] R)),
      ∀ ν ∈ weights Δ M, ∃ w ∈ bds, rd.IsInQPlus (w - ν))
    (μ : Δ.𝔥 →ₗ[R] R) :
    ∃ (T : Finset (WeightSpace Δ M μ)),
      Submodule.span R (T : Set (WeightSpace Δ M μ)) = ⊤ := by

  by_cases hμ : WeightSpace Δ M μ = ⊥
  · refine ⟨∅, ?_⟩
    rw [Finset.coe_empty, Submodule.span_empty]
    rw [eq_comm, Submodule.eq_bot_iff]
    intro ⟨x, hx⟩
    simp only [Submodule.mem_top, true_implies]
    ext
    exact (Submodule.mem_bot R).mp (hμ ▸ hx)
  ·
    exact pbw_weightSpace_spanFinite_axiom S hS hS_wt hbnd μ hμ

theorem IsVermaModule.weight_subspace_finiteDimensional
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt)
    (rd : PositiveRootData Δ)
    (μ : Δ.𝔥 →ₗ[R] R) :
    Module.Finite R (WeightSpace Δ M μ) := by

  by_cases hμ : WeightSpace Δ M μ = ⊥
  ·
    rw [hμ]
    infer_instance
  ·


    have hv_wt : hM.highestWeightVec ∈ WeightSpace Δ M wt := by
      intro h
      exact hM.cartan_action h

    have hgen : LieSubmodule.lieSpan R 𝔤 ({hM.highestWeightVec} : Set M) = ⊤ :=
      hM.generates

    have hS_wt : ∀ v ∈ ({hM.highestWeightVec} : Finset M),
        ∃ wt' : Δ.𝔥 →ₗ[R] R, v ∈ WeightSpace Δ M wt' := by
      intro v hv
      rw [Finset.mem_singleton] at hv
      exact ⟨wt, hv ▸ hv_wt⟩

    have hbnd : ∃ (bds : Finset (Δ.𝔥 →ₗ[R] R)),
        ∀ ν ∈ weights Δ M, ∃ w ∈ bds, rd.IsInQPlus (w - ν) := by
      refine ⟨{wt}, fun ν hν => ?_⟩
      exact ⟨wt, Finset.mem_singleton.mpr rfl, hM.weight_subset_QPlus rd ν hν⟩

    have hgen' : LieSubmodule.lieSpan R 𝔤 (({hM.highestWeightVec} : Finset M) : Set M) = ⊤ := by
      simp only [Finset.coe_singleton]
      exact hgen

    exact pbw_weightSpace_moduleFinite {hM.highestWeightVec} hgen' hS_wt hbnd μ hμ

theorem verma_weightSubspace_finite'
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {wt : Δ.𝔥 →ₗ[R] R}
    (hM : IsVermaModule Δ M wt) (rd : PositiveRootData Δ) (μ : Δ.𝔥 →ₗ[R] R) :
    Module.Finite R ↥(Δ.weightSubspace M μ) := by
  have h := hM.weight_subspace_finiteDimensional rd μ
  rwa [weightSpace_eq_weightSubspace] at h

end section
