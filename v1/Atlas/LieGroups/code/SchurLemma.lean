/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.ContinuousRep
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula


noncomputable section

open scoped ComplexOrder

structure FinDimRep (G : Type*) [Group G] (V : Type*) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] where
  toMonoidHom : G →* (V →ₗ[ℂ] V)

namespace FinDimRep

variable {G : Type*} [Group G]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

def IsIrreducible (π : FinDimRep G V) : Prop :=
  ∀ (W : Submodule ℂ V), (∀ g : G, ∀ v ∈ W, π.toMonoidHom g v ∈ W) → W = ⊥ ∨ W = ⊤

end FinDimRep

theorem schur_scalar_finiteDim {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
    (π : FinDimRep G V) (hirr : π.IsIrreducible)
    (T : V →ₗ[ℂ] V) (hT : ∀ g : G, T ∘ₗ π.toMonoidHom g = π.toMonoidHom g ∘ₗ T) :
    ∃ c : ℂ, T = c • LinearMap.id := by

  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T

  set S : Module.End ℂ V := T - μ • 1 with hS_def

  have hS_intertwines : ∀ g : G, S ∘ₗ π.toMonoidHom g = π.toMonoidHom g ∘ₗ S := by
    intro g
    ext v
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, hS_def]
    have h1 : (1 : Module.End ℂ V) (π.toMonoidHom g v) = π.toMonoidHom g v := rfl
    have h2 : (1 : Module.End ℂ V) v = v := rfl
    rw [h1, h2, map_sub, map_smul]
    congr 1
    exact LinearMap.ext_iff.mp (hT g) v

  have hker_inv : ∀ g : G, ∀ v ∈ LinearMap.ker S,
      π.toMonoidHom g v ∈ LinearMap.ker S := by
    intro g v hv
    rw [LinearMap.mem_ker] at hv ⊢
    have := LinearMap.ext_iff.mp (hS_intertwines g) v
    simp only [LinearMap.comp_apply] at this
    rw [hv, map_zero] at this
    exact this

  have hker_ne_bot : LinearMap.ker S ≠ ⊥ := by
    rw [hS_def, ← Module.End.eigenspace_def]
    exact Module.End.hasEigenvalue_iff.mp hμ

  have hker_top : LinearMap.ker S = ⊤ := by
    cases hirr (LinearMap.ker S) hker_inv with
    | inl h => exact absurd h hker_ne_bot
    | inr h => exact h

  have hS_zero : S = 0 := LinearMap.ker_eq_top.mp hker_top
  exact ⟨μ, by have := sub_eq_zero.mp hS_zero; rw [this]; rfl⟩


theorem schur_zero_or_iso_continuous
    {G : Type*} [Group G] [TopologicalSpace G]
    {V₁ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [TopologicalSpace V₁]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂] [TopologicalSpace V₂]
    (π₁ : ContinuousRep G V₁) (π₂ : ContinuousRep G V₂)
    (hirr₁ : π₁.IsIrreducible) (hirr₂ : π₂.IsIrreducible)
    (T : RepHom π₁ π₂) :
    T.toContinuousLinearMap = 0 ∨ Function.Bijective T.toContinuousLinearMap := by sorry

theorem schur_scalar_topological
    {G : Type*} [Group G] [TopologicalSpace G]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (π : ContinuousRep G E) (hirr : π.IsIrreducible)
    (T : RepHom π π) :
    ∃ c : ℂ, T.toContinuousLinearMap = c • ContinuousLinearMap.id ℂ E := by

  by_cases hE : Subsingleton E
  · exact ⟨0, by ext x; exact @Subsingleton.elim _ hE _ _⟩
  ·
    rw [not_subsingleton_iff_nontrivial] at hE

    let f := T.toContinuousLinearMap


    obtain ⟨c, hc⟩ := (spectrum.nonempty f : (spectrum ℂ f).Nonempty)

    let S_clm : E →L[ℂ] E := f - c • ContinuousLinearMap.id ℂ E
    have hS_intertwines : ∀ g : G, S_clm.comp (π.toMonoidHom g) =
        (π.toMonoidHom g).comp S_clm := by
      intro g


      simp only [S_clm, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
                 ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
                 ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
      congr 1
      exact T.intertwines g
    let S : RepHom π π := ⟨S_clm, hS_intertwines⟩

    rcases schur_zero_or_iso_continuous π π hirr hirr S with hzero | hbij
    ·
      exact ⟨c, sub_eq_zero.mp hzero⟩
    ·

      exfalso
      apply hc

      show IsUnit (algebraMap ℂ (E →L[ℂ] E) c - f)

      have hunit : IsUnit S_clm := by
        rw [ContinuousLinearMap.isUnit_iff_bijective]
        exact hbij

      have hne : algebraMap ℂ (E →L[ℂ] E) c - f = -S_clm := by
        simp [S_clm, Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.one_def]
      rw [hne]
      exact hunit.neg

end
