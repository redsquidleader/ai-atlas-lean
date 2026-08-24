/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Atlas.DifferentialGeometry.code.Hypersurfaces

noncomputable section

open scoped Topology
open LinearMap (ker range)
open Set Filter

theorem ContinuousLinearMap.range_eq_top_of_ne_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E →L[ℝ] ℝ) (hf : f ≠ 0) : (f : E →ₗ[ℝ] ℝ).range = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro c
  have ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (ContinuousLinearMap.ext (fun v => h v))
  exact ⟨(c / f v) • v, by simp [hv]⟩


theorem implicit_function_inverse_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (ψ : E → ℝ) (y : E)
    (Φ : OpenPartialHomeomorph E (ℝ × (ker (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ))))
    {V : Set E} (hV : IsOpen V)
    (hψ_smooth : ContDiffOn ℝ ⊤ ψ V)
    (hψ_deriv : fderiv ℝ ψ y ≠ 0)
    (hy_source : y ∈ Φ.source)
    (h_source_sub : Φ.source ⊆ V)
    (h_fwd_smooth : ContDiffOn ℝ ⊤ Φ Φ.source)
    : ContDiffOn ℝ ⊤ Φ.symm Φ.target := by sorry

theorem implicit_function_straightening
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {V : Set E} (hV : IsOpen V)
    (ψ : E → ℝ) (y : E) (hy : y ∈ V)
    (hψ_smooth : ContDiffOn ℝ ⊤ ψ V)
    (hψ_zero : ψ y = 0)
    (hψ_deriv : fderiv ℝ ψ y ≠ 0) :
    ∃ (Φ : OpenPartialHomeomorph E (ℝ × (ker (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ)))),
      y ∈ Φ.source ∧
      Φ.source ⊆ V ∧
      Φ y = (0, 0) ∧
      (∀ x ∈ Φ.source, ψ x = (Φ x).1) ∧
      ContDiffOn ℝ ⊤ Φ Φ.source ∧
      ContDiffOn ℝ ⊤ Φ.symm Φ.target := by
  have hψ_at : ContDiffAt ℝ ⊤ ψ y := hψ_smooth.contDiffAt (hV.mem_nhds hy)
  have htop : (⊤ : WithTop ℕ∞) ≠ 0 := WithTop.top_ne_coe
  have hstrict : HasStrictFDerivAt ψ (fderiv ℝ ψ y) y := hψ_at.hasStrictFDerivAt htop
  have hrange : (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).range = ⊤ :=
    ContinuousLinearMap.range_eq_top_of_ne_zero _ hψ_deriv
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  let Φ₀ := hstrict.implicitToOpenPartialHomeomorph ψ (fderiv ℝ ψ y) hrange
  let Φ := Φ₀.restrOpen V hV
  have hΦ_source : Φ.source = Φ₀.source ∩ V := Φ₀.restrOpen_source V hV
  have hΦ_source_sub_V : Φ.source ⊆ V := by
    rw [hΦ_source]; exact Set.inter_subset_right
  have hy_source : y ∈ Φ.source := by
    rw [hΦ_source]
    exact ⟨hstrict.mem_implicitToOpenPartialHomeomorph_source hrange, hy⟩
  have hcoe : (Φ : E → ℝ × (ker (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ))) = Φ₀ := Φ₀.coe_restrOpen hV
  have h_fwd_smooth : ContDiffOn ℝ ⊤ Φ Φ.source := by
    rw [hcoe]
    let proj := Classical.choose
      (fderiv ℝ ψ y).ker_closedComplemented_of_finiteDimensional_range
    have hsmooth_Φ₀ : ContDiffOn ℝ ⊤ (fun x => (ψ x, proj (x - y))) V :=
      ContDiffOn.prodMk hψ_smooth
        ((proj.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn)
    exact hsmooth_Φ₀.mono hΦ_source_sub_V
  refine ⟨Φ, hy_source, hΦ_source_sub_V, ?_, ?_, h_fwd_smooth, ?_⟩

  · change Φ₀ y = (0, 0)
    rw [hstrict.implicitToOpenPartialHomeomorph_self hrange, hψ_zero]

  · intro x _
    change ψ x = (Φ₀ x).1
    exact (hstrict.implicitToOpenPartialHomeomorph_fst hrange x).symm

  · exact implicit_function_inverse_smooth ψ y Φ hV hψ_smooth hψ_deriv hy_source
      hΦ_source_sub_V h_fwd_smooth

theorem implicit_function_diffeomorphism
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {V : Set E} (hV : IsOpen V)
    (ψ : E → ℝ) (y : E) (hy : y ∈ V)
    (hψ_smooth : ContDiffOn ℝ ⊤ ψ V)
    (hψ_zero : ψ y = 0)
    (hψ_deriv : fderiv ℝ ψ y ≠ 0) :
    ∃ (Φ : OpenPartialHomeomorph E (ℝ × (ker (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ)))),
      y ∈ Φ.source ∧
      Φ.source ⊆ V ∧
      Φ y = (0, 0) ∧
      (∀ x ∈ Φ.source, ψ x = (Φ x).1) ∧
      ContDiffOn ℝ ⊤ Φ Φ.source ∧
      ContDiffOn ℝ ⊤ Φ.symm Φ.target := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hψ_at : ContDiffAt ℝ ⊤ ψ y := hψ_smooth.contDiffAt (hV.mem_nhds hy)
  have htop_ne : (⊤ : WithTop ℕ∞) ≠ 0 := WithTop.top_ne_coe
  have hstrict : HasStrictFDerivAt ψ (fderiv ℝ ψ y) y := hψ_at.hasStrictFDerivAt htop_ne
  have hrange : (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).range = ⊤ :=
    ContinuousLinearMap.range_eq_top_of_ne_zero _ hψ_deriv

  let Φ₀ := hstrict.implicitToOpenPartialHomeomorph ψ (fderiv ℝ ψ y) hrange
  let proj := Classical.choose
    (fderiv ℝ ψ y).ker_closedComplemented_of_finiteDimensional_range

  let F : E → ℝ × (ker (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ)) := fun x => (ψ x, proj (x - y))
  have hF_smooth_V : ContDiffOn ℝ ⊤ F V :=
    ContDiffOn.prodMk hψ_smooth
      ((proj.contDiff.comp (contDiff_id.sub contDiff_const)).contDiffOn)

  let Φ := Φ₀.restrOpen V hV
  have hΦ_source : Φ.source = Φ₀.source ∩ V := Φ₀.restrOpen_source V hV
  have hΦ_source_sub_V : Φ.source ⊆ V := by
    rw [hΦ_source]; exact Set.inter_subset_right
  have hy_source : y ∈ Φ.source := by
    rw [hΦ_source]
    exact ⟨hstrict.mem_implicitToOpenPartialHomeomorph_source hrange, hy⟩
  have hΦ_coe : (Φ : E → ℝ × (ker (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ))) = Φ₀ :=
    Φ₀.coe_restrOpen hV
  refine ⟨Φ, hy_source, hΦ_source_sub_V, ?_, ?_, ?_, ?_⟩

  · change Φ₀ y = (0, 0)
    rw [hstrict.implicitToOpenPartialHomeomorph_self hrange, hψ_zero]

  · intro x _
    change ψ x = (Φ₀ x).1
    exact (hstrict.implicitToOpenPartialHomeomorph_fst hrange x).symm

  · rw [hΦ_coe]
    exact hF_smooth_V.mono hΦ_source_sub_V


  · have h_fwd : ContDiffOn ℝ ⊤ Φ Φ.source := by
      rw [hΦ_coe]; exact hF_smooth_V.mono hΦ_source_sub_V
    exact implicit_function_inverse_smooth ψ y Φ hV hψ_smooth hψ_deriv hy_source
      hΦ_source_sub_V h_fwd

theorem inverse_function_theorem
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {φ : E → F} {y : E}
    (hφ_smooth : ContDiff ℝ ⊤ φ)
    {f' : E ≃L[ℝ] F}
    (hf' : HasStrictFDerivAt φ (f' : E →L[ℝ] F) y)
    : ∃ (Φ : OpenPartialHomeomorph E F),
      (∀ x ∈ Φ.source, Φ x = φ x) ∧
      y ∈ Φ.source ∧
      IsOpen Φ.source ∧
      IsOpen Φ.target ∧
      ContDiffOn ℝ ⊤ Φ Φ.source ∧
      ContDiffOn ℝ ⊤ Φ.symm Φ.target := by

  let Φ₀ := hf'.toOpenPartialHomeomorph φ

  have hopen_equiv : IsOpen (Set.range (ContinuousLinearEquiv.toContinuousLinearMap
    (σ₁₂ := RingHom.id ℝ) (M₁ := E) (M₂ := F))) := ContinuousLinearEquiv.isOpen
  have hy_mem : fderiv ℝ φ y ∈ Set.range (ContinuousLinearEquiv.toContinuousLinearMap
    (σ₁₂ := RingHom.id ℝ) (M₁ := E) (M₂ := F)) := ⟨f', (hf'.hasFDerivAt.fderiv).symm⟩
  have htop_ne : (⊤ : WithTop ℕ∞) ≠ 0 := WithTop.top_ne_coe
  have hcont_fderiv : Continuous (fderiv ℝ φ) := hφ_smooth.continuous_fderiv htop_ne
  let W := fderiv ℝ φ ⁻¹' (Set.range ContinuousLinearEquiv.toContinuousLinearMap)
  have hW_open : IsOpen W := hcont_fderiv.isOpen_preimage _ hopen_equiv
  have hy_W : y ∈ W := hy_mem

  let Φ := Φ₀.restrOpen W hW_open
  have hΦ_source : Φ.source = Φ₀.source ∩ W := Φ₀.restrOpen_source W hW_open
  have hy_source : y ∈ Φ.source := by
    rw [hΦ_source]
    exact ⟨hf'.mem_toOpenPartialHomeomorph_source, hy_W⟩

  have hΦ_eq : (Φ : E → F) = φ := by
    have h1 : (Φ₀ : E → F) = φ := hf'.toOpenPartialHomeomorph_coe
    have h2 : (Φ : E → F) = (Φ₀ : E → F) := Φ₀.coe_restrOpen hW_open
    exact h2.trans h1
  refine ⟨Φ, ?_, hy_source, Φ.open_source, Φ.open_target, ?_, ?_⟩

  · intro x _
    exact congr_fun hΦ_eq x

  · exact hΦ_eq ▸ hφ_smooth.contDiffOn

  · rw [Φ.open_target.contDiffOn_iff]
    intro a ha
    have hsymm_source : Φ.symm a ∈ Φ.source := Φ.map_target ha
    have hsymm_W : Φ.symm a ∈ W := by
      rw [hΦ_source] at hsymm_source
      exact hsymm_source.2
    obtain ⟨e, he⟩ := hsymm_W

    have hhas_fderiv_Φ : HasFDerivAt (Φ : E → F) (e : E →L[ℝ] F) (Φ.symm a) := by
      have hfderiv_eq : fderiv ℝ φ (Φ.symm a) = (e : E →L[ℝ] F) := he.symm
      have hhas_fderiv : HasFDerivAt φ (e : E →L[ℝ] F) (Φ.symm a) := by
        rw [← hfderiv_eq]
        exact (hφ_smooth.differentiable htop_ne).differentiableAt.hasFDerivAt
      rw [hΦ_eq]
      exact hhas_fderiv

    have hcd : ContDiffAt ℝ ⊤ (Φ : E → F) (Φ.symm a) := by
      rw [hΦ_eq]
      exact hφ_smooth.contDiffAt
    exact Φ.contDiffAt_symm ha hhas_fderiv_Φ hcd

section InverseFunctionTheoremLemmas

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace F] in
theorem inverse_function_theorem_local_homeomorph
    (φ : E → F) (y : E)
    (hφ_smooth : ContDiff ℝ ⊤ φ)
    (f' : E ≃L[ℝ] F)
    (hf' : HasStrictFDerivAt φ (f' : E →L[ℝ] F) y) :
    ∃ (Φ : OpenPartialHomeomorph E F),
      (∀ x ∈ Φ.source, Φ x = φ x) ∧
      y ∈ Φ.source ∧
      IsOpen Φ.source ∧
      IsOpen Φ.target ∧
      ContDiffOn ℝ ⊤ Φ Φ.source := by
  let Φ := hf'.toOpenPartialHomeomorph φ
  exact ⟨Φ, fun _ _ => rfl,
    hf'.mem_toOpenPartialHomeomorph_source,
    Φ.open_source,
    Φ.open_target,
    hφ_smooth.contDiffOn⟩

end InverseFunctionTheoremLemmas

structure IsDiffeomorphism
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : E → F) (V : Set E) (U : Set F) : Prop where
  isOpen_source : IsOpen V
  isOpen_target : IsOpen U
  bijOn : Set.BijOn φ V U
  smooth_forward : ContDiffOn ℝ ⊤ φ V
  smooth_inverse : ∃ g : F → E, ContDiffOn ℝ ⊤ g U ∧
    (∀ x ∈ V, g (φ x) = x) ∧ (∀ y ∈ U, φ (g y) = y)

variable {n : ℕ}

namespace Hypersurface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure IsLocalDefiningFunction (ψ : E → ℝ) (M : Set E) (y : E) : Prop where
  exists_open_nhd : ∃ U : Set E, IsOpen U ∧ y ∈ U ∧
    ContDiffOn ℝ 1 ψ U ∧ (∀ x ∈ U, x ∈ M ↔ ψ x = 0)
  fderiv_ne_zero : fderiv ℝ ψ y ≠ 0

theorem IsLocalDefiningFunction.differentiableAt {ψ : E → ℝ} {M : Set E} {y : E}
    (hψ : IsLocalDefiningFunction ψ M y) : DifferentiableAt ℝ ψ y := by
  obtain ⟨U, hUo, hyU, hψU, _⟩ := hψ.exists_open_nhd
  exact (hψU.differentiableOn (by norm_num)).differentiableAt (hUo.mem_nhds hyU)

def IsHypersurface (M : Set E) : Prop :=
  ∀ y ∈ M, ∃ ψ : E → ℝ, IsLocalDefiningFunction ψ M y

def tangentSpace (ψ : E → ℝ) (y : E) : Submodule ℝ E :=
  LinearMap.ker (fderiv ℝ ψ y).toLinearMap

def IsRegularPoint (ψ : E → ℝ) (y : E) : Prop :=
  DifferentiableAt ℝ ψ y ∧ fderiv ℝ ψ y ≠ 0

theorem mem_tangentSpace_iff {ψ : E → ℝ} {y v : E} :
    v ∈ tangentSpace ψ y ↔ fderiv ℝ ψ y v = 0 := by
  simp [tangentSpace, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]

theorem IsLocalDefiningFunction.eq_zero_of_mem {ψ : E → ℝ} {M : Set E} {y : E}
    (hψ : IsLocalDefiningFunction ψ M y) (hy : y ∈ M) : ψ y = 0 := by
  obtain ⟨U, _, hyU, _, hU⟩ := hψ.exists_open_nhd
  exact (hU y hyU).mp hy

theorem IsLocalDefiningFunction.isRegularPoint {ψ : E → ℝ} {M : Set E} {y : E}
    (hψ : IsLocalDefiningFunction ψ M y) : IsRegularPoint ψ y :=
  ⟨hψ.differentiableAt, hψ.fderiv_ne_zero⟩

structure IsSmoothLocalDefiningFunction (ψ : E → ℝ) (M : Set E) (y : E) : Prop where
  exists_open_nhd : ∃ V : Set E, IsOpen V ∧ y ∈ V ∧
    ContDiffOn ℝ ⊤ ψ V ∧
    (∀ x ∈ V, x ∈ M ↔ ψ x = 0) ∧
    (∀ x ∈ V, x ∈ M → fderiv ℝ ψ x ≠ 0)

theorem IsSmoothLocalDefiningFunction.toIsLocalDefiningFunction {ψ : E → ℝ} {M : Set E} {y : E}
    (hy : y ∈ M) (h : IsSmoothLocalDefiningFunction ψ M y) :
    IsLocalDefiningFunction ψ M y := by
  obtain ⟨V, hVo, hyV, hψV, hzero, hderiv⟩ := h.exists_open_nhd
  exact {
    exists_open_nhd := ⟨V, hVo, hyV, hψV.of_le le_top, hzero⟩
    fderiv_ne_zero := hderiv y hyV hy
  }

theorem IsSmoothLocalDefiningFunction.eq_zero_of_mem {ψ : E → ℝ} {M : Set E} {y : E}
    (hψ : IsSmoothLocalDefiningFunction ψ M y) (hy : y ∈ M) : ψ y = 0 := by
  obtain ⟨V, _, hyV, _, hzero, _⟩ := hψ.exists_open_nhd
  exact (hzero y hyV).mp hy

theorem IsSmoothLocalDefiningFunction.isRegularPoint {ψ : E → ℝ} {M : Set E} {y : E}
    (hψ : IsSmoothLocalDefiningFunction ψ M y) (hy : y ∈ M) : IsRegularPoint ψ y := by
  obtain ⟨V, hVo, hyV, hψV, _, hderiv⟩ := hψ.exists_open_nhd
  exact ⟨(hψV.differentiableOn (by norm_num)).differentiableAt (hVo.mem_nhds hyV),
    hderiv y hyV hy⟩

def IsHypersurfaceSubset (M : Set E) : Prop :=
  ∀ y ∈ M, ∃ ψ : E → ℝ, IsSmoothLocalDefiningFunction ψ M y

theorem smooth_division
    {ψ : E → ℝ} {M : Set E} {y : E}
    (hψ : IsSmoothLocalDefiningFunction ψ M y)
    (φ : E → ℝ) (hφ_smooth : ContDiff ℝ ⊤ φ)
    (hφ_vanish : ∃ V : Set E, IsOpen V ∧ y ∈ V ∧ ∀ x ∈ V, x ∈ M → φ x = 0) :
    ∃ W : Set E, IsOpen W ∧ y ∈ W ∧
      ∃ q : E → ℝ, ContDiffOn ℝ ⊤ q W ∧ (∀ x ∈ W, φ x = q x * ψ x) ∧
        (∀ q' : E → ℝ, ContDiffOn ℝ ⊤ q' W → (∀ x ∈ W, φ x = q' x * ψ x) → ∀ x ∈ W, q' x = q x) := by sorry

def IsConvexHypersurface (M : Set E) : Prop :=
  IsHypersurface M ∧
  ∀ y ∈ M, ∃ ψ : E → ℝ, IsLocalDefiningFunction ψ M y ∧
    (∀ z ∈ M, fderiv ℝ ψ y (z - y) ≤ 0)

end Hypersurface

namespace Hypersurface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure IsPartialParametrization
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (M : Set E) where
  ambientNhd : Set E
  ambientNhd_open : IsOpen ambientNhd
  paramDomain : Set F
  paramDomain_open : IsOpen paramDomain
  f : F → E
  smooth : ContDiffOn ℝ ⊤ f paramDomain
  injective : Set.InjOn f paramDomain
  image_eq : f '' paramDomain = M ∩ ambientNhd
  immersion : ∀ x ∈ paramDomain, Function.Injective (fderiv ℝ f x)

def AdmitsPartialParametrization (M : Set E) (y : E) : Prop :=
  ∃ ψ : E → ℝ, IsLocalDefiningFunction ψ M y ∧
    ∃ (P : IsPartialParametrization (F := tangentSpace ψ y) M), y ∈ P.ambientNhd


theorem hypersurface_admits_partial_parametrization
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {M : Set E} (hM : IsHypersurfaceSubset M) (y : E) (hy : y ∈ M)
    : AdmitsPartialParametrization M y := by

  obtain ⟨ψ, hψ⟩ := hM y hy
  obtain ⟨V, hV_open, hyV, hψ_smooth, hzero, hderiv⟩ := hψ.exists_open_nhd

  have hψ_local : IsLocalDefiningFunction ψ M y := hψ.toIsLocalDefiningFunction hy

  have hψ_zero : ψ y = 0 := (hzero y hyV).mp hy
  have hψ_deriv_ne : fderiv ℝ ψ y ≠ 0 := hderiv y hyV hy
  obtain ⟨Φ, hy_source, hsource_sub, hΦy, hstraighten, hΦ_smooth, hΦ_symm_smooth⟩ :=
    implicit_function_diffeomorphism hV_open ψ y hyV hψ_smooth hψ_zero hψ_deriv_ne

  let P : IsPartialParametrization (F := tangentSpace ψ y) M := {
    ambientNhd := Φ.source
    ambientNhd_open := Φ.open_source
    paramDomain := {w : tangentSpace ψ y | ((0 : ℝ), w) ∈ Φ.target}
    paramDomain_open :=
      Φ.open_target.preimage (Continuous.prodMk continuous_const continuous_id)
    f := fun w => Φ.symm ((0 : ℝ), w)
    smooth := by
      exact hΦ_symm_smooth.comp (contDiff_prodMk_right (0 : ℝ)).contDiffOn (fun w hw => hw)
    injective := by
      intro w₁ hw₁ w₂ hw₂ heq
      have h1 : ((0 : ℝ), w₁) ∈ Φ.target := hw₁
      have h2 : ((0 : ℝ), w₂) ∈ Φ.target := hw₂
      have heq' : Φ.symm ((0 : ℝ), w₁) = Φ.symm ((0 : ℝ), w₂) := heq
      have hinj : ((0 : ℝ), w₁) = ((0 : ℝ), w₂) :=
        (Φ.right_inv h1).symm.trans ((congr_arg Φ heq').trans (Φ.right_inv h2))
      exact (Prod.mk.inj hinj).2
    image_eq := by
      have hiff : ∀ x ∈ Φ.source, x ∈ M ↔ (Φ x).1 = 0 := by
        intro x hx
        rw [← hstraighten x hx]
        exact hzero x (hsource_sub hx)
      ext x
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨w, hw, rfl⟩
        have hx_source : Φ.symm ((0 : ℝ), w) ∈ Φ.source := Φ.map_target hw
        refine ⟨?_, hx_source⟩
        have h_right_inv : Φ (Φ.symm ((0 : ℝ), w)) = ((0 : ℝ), w) := Φ.right_inv hw
        rw [hiff _ hx_source, h_right_inv]
      · intro ⟨hxM, hx_source⟩
        refine ⟨(Φ x).2, ?_, ?_⟩
        · have hΦx_target : Φ x ∈ Φ.target := Φ.map_source hx_source
          have h0 : (Φ x).1 = 0 := (hiff x hx_source).mp hxM
          rw [← h0]
          exact hΦx_target
        · have h0 : (Φ x).1 = 0 := (hiff x hx_source).mp hxM
          conv_rhs => rw [← Φ.left_inv hx_source]
          congr 1
          exact Prod.ext h0.symm rfl
    immersion := by
      intro w hw
      have htop_ne : (⊤ : WithTop ℕ∞) ≠ 0 := WithTop.top_ne_coe
      have hΦ_symm_diff : DifferentiableAt ℝ Φ.symm ((0 : ℝ), w) :=
        (hΦ_symm_smooth.differentiableOn htop_ne).differentiableAt
          (Φ.open_target.mem_nhds hw)
      have h_embed_diff : DifferentiableAt ℝ (fun w : tangentSpace ψ y => ((0 : ℝ), w)) w :=
        (ContinuousLinearMap.inr ℝ ℝ (tangentSpace ψ y)).differentiableAt
      have hchain : fderiv ℝ (fun w : tangentSpace ψ y => Φ.symm ((0 : ℝ), w)) w =
          (fderiv ℝ Φ.symm ((0 : ℝ), w)).comp
            (fderiv ℝ (fun w : tangentSpace ψ y => ((0 : ℝ), w)) w) :=
        fderiv_comp w hΦ_symm_diff h_embed_diff
      have h_embed_fderiv : fderiv ℝ (fun w : tangentSpace ψ y => ((0 : ℝ), w)) w =
          ContinuousLinearMap.inr ℝ ℝ (tangentSpace ψ y) :=
        (ContinuousLinearMap.inr ℝ ℝ (tangentSpace ψ y)).hasFDerivAt.fderiv
      suffices h : Function.Injective ((fderiv ℝ Φ.symm ((0 : ℝ), w)).comp
          (ContinuousLinearMap.inr ℝ ℝ (tangentSpace ψ y))) by
        have heq : fderiv ℝ (fun w => Φ.symm ((0 : ℝ), w)) w =
            (fderiv ℝ Φ.symm ((0 : ℝ), w)).comp
              (ContinuousLinearMap.inr ℝ ℝ (tangentSpace ψ y)) := by
          rw [← h_embed_fderiv]; exact hchain
        rwa [← heq] at h
      have hΦ_diff : DifferentiableAt ℝ Φ (Φ.symm ((0 : ℝ), w)) :=
        (hΦ_smooth.differentiableOn htop_ne).differentiableAt
          (Φ.open_source.mem_nhds (Φ.map_target hw))
      have hΦ_symm_inj : Function.Injective (fderiv ℝ Φ.symm ((0 : ℝ), w)) := by
        have hid : fderiv ℝ (Φ ∘ Φ.symm) ((0 : ℝ), w) = ContinuousLinearMap.id ℝ _ := by
          have heq : ∀ᶠ x in nhds ((0 : ℝ), w), (Φ ∘ Φ.symm) x = x :=
            Filter.eventually_of_mem (Φ.open_target.mem_nhds hw)
              (fun x hx => Φ.right_inv hx)
          exact (Filter.EventuallyEq.fderiv_eq heq).trans fderiv_id
        have hchain' : fderiv ℝ (Φ ∘ Φ.symm) ((0 : ℝ), w) =
            (fderiv ℝ Φ (Φ.symm ((0 : ℝ), w))).comp (fderiv ℝ Φ.symm ((0 : ℝ), w)) :=
          fderiv_comp _ hΦ_diff hΦ_symm_diff
        rw [hid] at hchain'
        exact Function.HasLeftInverse.injective ⟨fderiv ℝ Φ (Φ.symm ((0 : ℝ), w)),
          fun v => by
            have := congr_fun (congr_arg DFunLike.coe hchain'.symm) v
            simpa using this⟩
      have h_inr_inj : Function.Injective
          (ContinuousLinearMap.inr ℝ ℝ (tangentSpace ψ y)) := by
        intro a b h; exact congr_arg Prod.snd h
      exact hΦ_symm_inj.comp h_inr_inj
  }
  exact ⟨ψ, hψ_local, P, hy_source⟩

end Hypersurface

namespace Hypersurface

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure IsGaussMap (ν : E → E) (M : Set E) : Prop where
  smooth : ContDiffOn ℝ ⊤ ν M
  norm_eq_one : ∀ y ∈ M, ‖ν y‖ = 1
  orthogonal_tangent : ∀ y ∈ M, ∀ ψ : E → ℝ,
    IsLocalDefiningFunction ψ M y →
      ∀ v ∈ tangentSpace ψ y, @inner ℝ _ _ (ν y) v = 0

def IsOrientable (M : Set E) : Prop :=
  ∃ ν : E → E, IsGaussMap ν M

structure OrientedHypersurface (M : Set E) where
  isHypersurface : IsHypersurface M
  gaussMap : E → E
  isGaussMap : IsGaussMap gaussMap M

end Hypersurface

namespace Hypersurface.Curvature

open scoped InnerProductSpace
open Finset

variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def gaussCurvatureMatrix (ψ : E → ℝ) (y : E) (Y : Fin n → E)
    (b : OrthonormalBasis (Fin (n + 1)) ℝ E) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun j i =>
    if h : (i : ℕ) < n then
      (fderiv ℝ (fderiv ℝ ψ) y) (Y ⟨i, h⟩) (b j)
    else
      (fderiv ℝ ψ y) (b j)

def gaussCurvatureLevelSet (ψ : E → ℝ) (y : E) (Y : Fin n → E)
    (b : OrthonormalBasis (Fin (n + 1)) ℝ E) : ℝ :=
  (gaussCurvatureMatrix ψ y Y b).det / ‖fderiv ℝ ψ y‖ ^ (n + 1)

def shapeOperatorLevelSet (ψ : E → ℝ) (y : E) (Y : Fin n → E) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => (1 / ‖fderiv ℝ ψ y‖) * (fderiv ℝ (fderiv ℝ ψ) y) (Y i) (Y j)

end Hypersurface.Curvature

end


theorem secondFundamentalForm_eq_hessian_div_gradNorm
    {n : ℕ}
    (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain)
    (ψ : (Fin (n + 1) → ℝ) → ℝ)
    (hψ_ne_zero : fderiv ℝ ψ (patch.f x) ≠ 0)
    (hψ_smooth : ContDiffAt ℝ 2 ψ (patch.f x))
    (himage : ∀ u ∈ patch.domain, ψ (patch.f u) = 0) :
    ∃ (s : ℝ) (_ : s = 1 ∨ s = -1), ∀ (i j : Fin n),
      secondFundamentalForm patch x i j = s *
        ((fderiv ℝ (fderiv ℝ ψ) (patch.f x))
          (patch.partialDeriv x i) (patch.partialDeriv x j) /
          ‖fderiv ℝ ψ (patch.f x)‖) := by sorry


theorem trace_firstFundamentalForm_inv_mul_eq_sum_orthonormal
    {n : ℕ}
    (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain)
    (ψ : (Fin (n + 1) → ℝ) → ℝ)
    (hψ_ne_zero : fderiv ℝ ψ (patch.f x) ≠ 0)
    (B : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (Y : Fin n → (Fin (n + 1) → ℝ))
    (hY_tangent : ∀ i, fderiv ℝ ψ (patch.f x) (Y i) = 0)
    (hY_orthonormal : ∀ i j : Fin n,
      Finset.univ.sum (fun k => Y i k * Y j k) = if i = j then 1 else 0) :
    ((firstFundamentalForm patch x)⁻¹ *
      Matrix.of (fun i j : Fin n =>
        B (patch.partialDeriv x i) (patch.partialDeriv x j))).trace =
    ∑ i : Fin n, B (Y i) (Y i) := by sorry

theorem meanCurvature_parametric_eq_levelSet
    {n : ℕ}
    (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain)
    (ψ : (Fin (n + 1) → ℝ) → ℝ)
    (hψ_ne_zero : fderiv ℝ ψ (patch.f x) ≠ 0)
    (hψ_smooth : ContDiffAt ℝ 2 ψ (patch.f x))
    (himage : ∀ u ∈ patch.domain, ψ (patch.f u) = 0)
    (Y : Fin n → (Fin (n + 1) → ℝ))
    (hY_tangent : ∀ i, fderiv ℝ ψ (patch.f x) (Y i) = 0)
    (hY_orthonormal : ∀ i j : Fin n,
      Finset.univ.sum (fun k => Y i k * Y j k) = if i = j then 1 else 0) :
    ∃ (s : ℝ) (_ : s = 1 ∨ s = -1),
      meanCurvature patch x = s *
        ((1 / ‖fderiv ℝ ψ (patch.f x)‖) *
          ∑ i : Fin n, (fderiv ℝ (fderiv ℝ ψ) (patch.f x)) (Y i) (Y i)) := by

  obtain ⟨s, hs, hH⟩ := secondFundamentalForm_eq_hessian_div_gradNorm
    patch x hx ψ hψ_ne_zero hψ_smooth himage

  refine ⟨s, hs, ?_⟩
  unfold meanCurvature shapeOperator

  have hH_matrix : secondFundamentalForm patch x =
      s • Matrix.of (fun i j : Fin n =>
        (fderiv ℝ (fderiv ℝ ψ) (patch.f x))
          (patch.partialDeriv x i) (patch.partialDeriv x j) /
          ‖fderiv ℝ ψ (patch.f x)‖) := by
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    exact hH i j
  rw [hH_matrix, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  congr 1


  have hM_factor : (Matrix.of (fun i j : Fin n =>
      (fderiv ℝ (fderiv ℝ ψ) (patch.f x))
        (patch.partialDeriv x i) (patch.partialDeriv x j) /
        ‖fderiv ℝ ψ (patch.f x)‖)) =
    (1 / ‖fderiv ℝ ψ (patch.f x)‖) • Matrix.of (fun i j : Fin n =>
      (fderiv ℝ (fderiv ℝ ψ) (patch.f x))
        (patch.partialDeriv x i) (patch.partialDeriv x j)) := by
    ext i j; simp [Matrix.smul_apply, Matrix.of_apply, div_eq_mul_inv, mul_comm]
  rw [hM_factor, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  congr 1


  exact trace_firstFundamentalForm_inv_mul_eq_sum_orthonormal
    patch x hx ψ hψ_ne_zero
    (fun v w => (fderiv ℝ (fderiv ℝ ψ) (patch.f x)) v w)
    Y hY_tangent hY_orthonormal


open scoped Topology
open LinearMap (ker range)
open Set Filter

namespace Hypersurface

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

structure IsTangentCurve (c : ℝ → E) (M : Set E) (y v : E) : Prop where
  at_zero : c 0 = y
  hasDerivAt : HasDerivAt c v 0
  image_in_M : ∀ᶠ t in 𝓝 0, c t ∈ M

theorem tangent_of_curve {ψ : E → ℝ} {M : Set E} {y v : E} {c : ℝ → E}
    (hψ : IsLocalDefiningFunction ψ M y)
    (hc : IsTangentCurve c M y v) :
    v ∈ tangentSpace ψ y := by
  rw [tangentSpace, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  obtain ⟨U, hUo, hyU, hψU, hzero⟩ := hψ.exists_open_nhd
  have hψ_diff : DifferentiableAt ℝ ψ y :=
    (hψU.differentiableOn (by norm_num : (1 : WithTop ℕ∞) ≠ 0)).differentiableAt (hUo.mem_nhds hyU)
  have hψ_hasFDerivAt : HasFDerivAt ψ (fderiv ℝ ψ y) y := hψ_diff.hasFDerivAt

  have hchain : HasDerivAt (ψ ∘ c) ((fderiv ℝ ψ y) v) 0 := by
    have key : HasFDerivAt ψ (fderiv ℝ ψ y) (c 0) := by rw [hc.at_zero]; exact hψ_hasFDerivAt
    exact key.comp_hasDerivAt 0 hc.hasDerivAt

  have hconst : HasDerivAt (ψ ∘ c) 0 0 := by
    apply (hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
    have h1 : ∀ᶠ t in 𝓝 0, c t ∈ U := by
      have hcont : ContinuousAt c 0 := hc.hasDerivAt.continuousAt
      exact hcont.preimage_mem_nhds (by rw [hc.at_zero]; exact hUo.mem_nhds hyU)
    filter_upwards [h1, hc.image_in_M] with t ht1 ht2
    simp [Function.comp, (hzero (c t) ht1).mp ht2]
  exact hchain.unique hconst

theorem curve_of_tangent [FiniteDimensional ℝ E] {ψ : E → ℝ} {M : Set E} {y : E} {v : E}
    (hψ : IsLocalDefiningFunction ψ M y)
    (hy : y ∈ M)
    (hv : v ∈ tangentSpace ψ y)
    (hstrict : HasStrictFDerivAt ψ (fderiv ℝ ψ y) y) :
    ∃ c : ℝ → E, IsTangentCurve c M y v := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hrange : (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).range = ⊤ :=
    ContinuousLinearMap.range_eq_top_of_ne_zero _ hψ.fderiv_ne_zero
  let g := hstrict.implicitFunction ψ (fderiv ℝ ψ y) hrange
  have hψ_zero : ψ y = 0 := by
    obtain ⟨U, _, hyU, _, hU⟩ := hψ.exists_open_nhd
    exact (hU y hyU).mp hy
  have hg_zero : g 0 0 = y := by
    have := hstrict.implicitFunction_apply_image hrange
    rwa [hψ_zero] at this
  have hg_map : ∀ᶠ p : ℝ × (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).ker in
      𝓝 (0, (0 : (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).ker)),
      ψ (g p.1 p.2) = p.1 := by
    have := hstrict.map_implicitFunction_eq hrange
    rwa [hψ_zero] at this
  have hg_deriv : HasStrictFDerivAt (g 0)
      (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).ker.subtypeL 0 := by
    have := hstrict.to_implicitFunction hrange
    rwa [hψ_zero] at this
  have hv_mem : v ∈ (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).ker := by
    rwa [tangentSpace, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv
  let w : (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).ker := ⟨v, hv_mem⟩

  have hderiv_c : HasDerivAt (fun t : ℝ => g 0 (t • w)) v 0 := by
    have hderiv_smul : HasDerivAt (fun t : ℝ => t • w) w 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const w
    have key : (fun t : ℝ => t • w) 0 = 0 := by simp
    have hg' : HasFDerivAt (g 0) (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).ker.subtypeL
        ((fun t : ℝ => t • w) 0) := by
      rw [key]; exact hg_deriv.hasFDerivAt
    have hcomp := hg'.comp_hasDerivAt (x := (0 : ℝ)) hderiv_smul
    simp at hcomp
    exact hcomp
  let c : ℝ → E := fun t => g 0 (t • w)
  refine ⟨c, ?_, ?_, ?_⟩

  · show g 0 ((0 : ℝ) • w) = y
    simp [hg_zero]

  · exact hderiv_c

  · show ∀ᶠ t in 𝓝 0, g 0 (t • w) ∈ M
    obtain ⟨U, hUo, hyU, _, hzero⟩ := hψ.exists_open_nhd

    have hψ_eq_zero : ∀ᶠ t in 𝓝 (0 : ℝ), ψ (g 0 (t • w)) = 0 := by
      have hcont_tw : ContinuousAt (fun t : ℝ => ((0 : ℝ), t • w)) 0 := by fun_prop
      have h0 : (fun t : ℝ => ((0 : ℝ), t • w)) 0 =
          (0, (0 : (fderiv ℝ ψ y : E →ₗ[ℝ] ℝ).ker)) := by simp
      have hmem := hcont_tw.eventually (h0 ▸ hg_map)
      simpa [Function.comp] using hmem

    have hcont_c : ContinuousAt c 0 := hderiv_c.continuousAt
    have hc_in_U : ∀ᶠ t in 𝓝 (0 : ℝ), c t ∈ U := by
      apply hcont_c.preimage_mem_nhds
      change U ∈ 𝓝 (c 0)
      simp only [c, zero_smul, hg_zero]
      exact hUo.mem_nhds hyU
    filter_upwards [hψ_eq_zero, hc_in_U] with t ht1 ht2
    exact (hzero (g 0 (t • w)) ht2).mpr ht1

end Hypersurface
