/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.SmoothVectors
import Atlas.LieGroups.code.KFinite
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.Geometry.Manifold.BumpFunction

noncomputable section

open scoped Manifold
open MeasureTheory

namespace ContinuousRep

section GStable

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable [LieGroup I ⊤ G]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

end GStable

section Subspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable [LieGroup I ⊤ G]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

omit [LieGroup I ⊤ G] in
theorem smoothVector_zero (π : ContinuousRep G F) :
    π.IsSmoothVector I 0 :=
  (π.smoothSubspace I).zero_mem

omit [LieGroup I ⊤ G] in
theorem smoothVector_add (π : ContinuousRep G F) {v w : F}
    (hv : π.IsSmoothVector I v) (hw : π.IsSmoothVector I w) :
    π.IsSmoothVector I (v + w) :=
  (π.smoothSubspace I).add_mem hv hw

omit [LieGroup I ⊤ G] in
theorem smoothVector_smul (π : ContinuousRep G F) (c : ℂ) {v : F}
    (hv : π.IsSmoothVector I v) :
    π.IsSmoothVector I (c • v) :=
  (π.smoothSubspace I).smul_mem c hv

end Subspace

section Prop413

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable [LieGroup I ⊤ G]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

omit [LieGroup I ⊤ G] in
theorem contDiffWithinAt_deriv_parametric
    {E₀ F₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]
    {f : E₀ → ℝ → F₀} {s : Set E₀} {e₀ : E₀} {y₀ : ℝ}
    (hf : ContDiffWithinAt ℝ ↑(⊤ : ℕ∞) (Function.uncurry f) (s ×ˢ Set.univ) (e₀, y₀))
    (he₀ : e₀ ∈ s) :
    ContDiffWithinAt ℝ ↑(⊤ : ℕ∞) (fun e => deriv (f e) y₀) s e₀ := by
  have hfW : ContDiffWithinAt ℝ ↑(⊤ : ℕ∞) (fun x => fderivWithin ℝ (f x) Set.univ y₀) s e₀ :=
    ContDiffWithinAt.fderivWithin (m := ↑(⊤ : ℕ∞)) hf contDiffWithinAt_const uniqueDiffOn_univ
      le_rfl he₀ (fun _ _ => Set.mem_univ _)
  simp only [fderivWithin_univ] at hfW
  exact hfW.continuousLinearMap_comp (ContinuousLinearMap.apply ℝ F₀ (1 : ℝ))


theorem derivedRep_maps_smooth (π : ContinuousRep G F) (lieExp : E → G)
    (hExp : ContMDiff 𝓘(ℝ, E) I ⊤ lieExp)
    (hExp1 : lieExp 0 = 1)
    (b : E) (v : F)
    (hv : π.IsSmoothVector I v) :
    π.IsSmoothVector I (π.derivedRep lieExp b v) := by

  haveI : IsScalarTower ℝ ℂ F :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)


  have hΦ_diff : ContDiff ℝ ↑(⊤ : ℕ∞) (fun t : ℝ => (π.toMonoidHom (lieExp (t • b))) v) := by
    have h1 : ContMDiff I 𝓘(ℝ, F) ↑(⊤ : ℕ∞) (π.orbitMap v) := hv
    have h3 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ↑(⊤ : ℕ∞) ((π.orbitMap v) ∘ lieExp) :=
      h1.comp (hExp.of_le le_top)
    rw [contMDiff_iff_contDiff] at h3
    exact h3.comp (contDiff_id.smul contDiff_const)
  have hΦ_hasderiv : HasDerivAt (fun t : ℝ => (π.toMonoidHom (lieExp (t • b))) v)
      (π.derivedRep lieExp b v) 0 :=
    (hΦ_diff.differentiable (by exact_mod_cast ENat.top_ne_zero)).differentiableAt.hasDerivAt


  have key_identity : ∀ g : G,
      (π.toMonoidHom g) (π.derivedRep lieExp b v) =
      deriv (fun t : ℝ => (π.toMonoidHom (g * lieExp (t • b))) v) 0 := by
    intro g


    have h_rep : (fun (t : ℝ) => (π.toMonoidHom (g * lieExp (t • b))) v) =
        (fun (t : ℝ) => (π.toMonoidHom g) ((π.toMonoidHom (lieExp (t • b))) v)) := by
      ext t
      show (π.toMonoidHom (g * lieExp (t • b))) v =
        (π.toMonoidHom g) ((π.toMonoidHom (lieExp (t • b))) v)
      rw [map_mul]; rfl
    rw [h_rep]

    have hcomp := (((π.toMonoidHom g).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt 0 hΦ_hasderiv).deriv
    simp only [ContinuousLinearMap.coe_restrictScalars', Function.comp_def] at hcomp
    exact hcomp.symm

  unfold IsSmoothVector orbitMap
  have heq : (fun g : G => (π.toMonoidHom g) (π.derivedRep lieExp b v)) =
      (fun g : G => deriv (fun t : ℝ => (π.toMonoidHom (g * lieExp (t • b))) v) 0) :=
    funext key_identity
  rw [heq]


  let Φ := fun (p : G × ℝ) => (π.toMonoidHom (p.1 * lieExp (p.2 • b))) v
  let J := modelWithCornersSelf ℝ ℝ
  have hΦ_smooth : ContMDiff (I.prod J) 𝓘(ℝ, F) ↑(⊤ : ℕ∞) Φ := by
    have h_orbitmap : ContMDiff I 𝓘(ℝ, F) ↑(⊤ : ℕ∞) (π.orbitMap v) := hv
    have h_mul_exp : ContMDiff (I.prod J) I ↑(⊤ : ℕ∞)
        (fun (p : G × ℝ) => p.1 * lieExp (p.2 • b)) :=
      (ContMDiff.mul contMDiff_fst (hExp.comp (contMDiff_snd.smul contMDiff_const))).of_le le_top
    exact h_orbitmap.comp h_mul_exp


  intro g₀

  rw [contMDiffAt_iff]
  constructor
  ·
    have hcont : ContinuousAt (fun g => (π.toMonoidHom g) (π.derivedRep lieExp b v)) g₀ :=
      (π.continuous_action.comp (continuous_id.prodMk continuous_const)).continuousAt
    refine hcont.congr (Filter.Eventually.of_forall (fun g => ?_))
    show (π.toMonoidHom g) (π.derivedRep lieExp b v) =
      deriv (fun t => (π.toMonoidHom (g * lieExp (t • b))) v) 0
    exact key_identity g
  ·

    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp]

    have hΦ_at := (contMDiffAt_iff.mp (hΦ_smooth.contMDiffAt (x := (g₀, (0 : ℝ))))).2

    rw [extChartAt_prod] at hΦ_at
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      ModelWithCorners.range_prod, ModelWithCorners.Boundaryless.range_eq_univ,
      Function.id_comp] at hΦ_at

    simp only [PartialEquiv.prod_symm, PartialEquiv.prod_coe] at hΦ_at


    apply contDiffWithinAt_deriv_parametric
    ·
      convert hΦ_at using 1
    · exact ⟨chartAt H g₀ g₀, rfl⟩

omit [LieGroup I ⊤ G] in
lemma contDiff_orbitMap_comp_lieExp (π : ContinuousRep G F) (lieExp : E → G)
    (hExp : ContMDiff 𝓘(ℝ, E) I ⊤ lieExp)
    (v : F)
    (hv : π.IsSmoothVector I v) :
    ContDiff ℝ ↑(⊤ : ℕ∞) (fun x : E => (π.toMonoidHom (lieExp x)) v) := by
  have h1 : ContMDiff I 𝓘(ℝ, F) ↑(⊤ : ℕ∞) (π.orbitMap v) := hv
  have h3 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ↑(⊤ : ℕ∞)
    ((π.orbitMap v) ∘ lieExp) := h1.comp (hExp.of_le le_top)
  rw [contMDiff_iff_contDiff] at h3
  exact h3

omit [LieGroup I ⊤ G] in
lemma derivedRep_eq_fderiv (π : ContinuousRep G F) (lieExp : E → G)
    (hExp : ContMDiff 𝓘(ℝ, E) I ⊤ lieExp)
    (v : F) (b : E)
    (hv : π.IsSmoothVector I v) :
    π.derivedRep lieExp b v =
    (fderiv ℝ (fun x : E => (π.toMonoidHom (lieExp x)) v) 0) b := by
  unfold derivedRep
  set f : E → F := fun x => (π.toMonoidHom (lieExp x)) v with hf_def
  have hf_diff : DifferentiableAt ℝ f 0 :=
    (contDiff_orbitMap_comp_lieExp I π lieExp hExp v hv).differentiable
      (by exact_mod_cast ENat.top_ne_zero) |>.differentiableAt
  have hg_deriv : HasDerivAt (fun t : ℝ => t • b) b 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const b
  have h0 : (fun t : ℝ => t • b) 0 = 0 := by simp
  have hfg : HasDerivAt (f ∘ (fun t : ℝ => t • b)) ((fderiv ℝ f 0) b) 0 :=
    hf_diff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hg_deriv h0.symm
  show deriv (fun t => f (t • b)) 0 = (fderiv ℝ f 0) b
  rw [show (fun t => f (t • b)) = (f ∘ (fun t => t • b)) from rfl]
  exact hfg.deriv

omit [LieGroup I ⊤ G] in

theorem derivedRep_linear (π : ContinuousRep G F) (lieExp : E → G)
    (hExp : ContMDiff 𝓘(ℝ, E) I ⊤ lieExp)
    (_hExp1 : lieExp 0 = 1)
    (v : F)
    (hv : π.IsSmoothVector I v) :
    IsLinearMap ℝ (fun b => π.derivedRep lieExp b v) := by
  have heq : ∀ b, π.derivedRep lieExp b v =
      (fderiv ℝ (fun x : E => (π.toMonoidHom (lieExp x)) v) 0) b :=
    fun b => derivedRep_eq_fderiv I π lieExp hExp v b hv
  set L : E →L[ℝ] F := fderiv ℝ (fun x : E => (π.toMonoidHom (lieExp x)) v) 0
  constructor
  · intro b₁ b₂
    rw [heq, heq, heq]
    exact L.map_add b₁ b₂
  · intro c b
    rw [heq, heq]
    exact L.map_smul c b

variable [LieRing E] [LieAlgebra ℝ E]


theorem derivedRep_bracket (π : ContinuousRep G F) (lieExp : E → G)
    (hExp : ContMDiff 𝓘(ℝ, E) I ⊤ lieExp)
    (hExp1 : lieExp 0 = 1)


    (hExpAdd : ∀ (X : E) (t s : ℝ), lieExp ((t + s) • X) = lieExp (t • X) * lieExp (s • X))


    (h_bracket : ∀ (X Y : E),
      ⁅X, Y⁆ = (fderiv ℝ (fun s : ℝ =>
        (fderiv ℝ (fun t : ℝ =>
          (extChartAt I (1 : G))
            (lieExp (t • X) * lieExp (s • Y) * (lieExp (t • X))⁻¹ *
              (lieExp (s • Y))⁻¹)) 0) (1 : ℝ)) 0) (1 : ℝ))
    (X Y : E) (v : F)
    (hv : π.IsSmoothVector I v) :
    π.derivedRep lieExp ⁅X, Y⁆ v =
    π.derivedRep lieExp X (π.derivedRep lieExp Y v) -
    π.derivedRep lieExp Y (π.derivedRep lieExp X v) := by


  sorry

end Prop413

section Garding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable [LieGroup I ⊤ G]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable [MeasureSpace G] [CompleteSpace F]
variable [FiniteDimensional ℝ E] [T2Space G]
variable [MeasurableMul G] [Measure.IsMulLeftInvariant (volume : Measure G)]
variable [BorelSpace G]
variable [SecondCountableTopology G] [LocallyCompactSpace G]

def repOfFunction (π : ContinuousRep G F) (f : G → ℂ) (v : F) : F :=
  ∫ g, (f g) • ((π.toMonoidHom g) v)

def IsSmoothCompactlySupportedFunction (f : G → ℂ) : Prop :=
  ContMDiff I 𝓘(ℝ, ℂ) (↑(⊤ : ℕ∞)) f ∧ HasCompactSupport f

def gardingSubspace (π : ContinuousRep G F) : Submodule ℂ F :=
  Submodule.span ℂ
    { w : F | ∃ (f : G → ℂ) (v : F),
        IsSmoothCompactlySupportedFunction I f ∧ w = π.repOfFunction f v }


theorem contDiffOn_convolution_chartCoord
    (f : G → ℂ) (hf : IsSmoothCompactlySupportedFunction I f)
    (w : G → F) (x₀ : G) :
    ContDiffOn ℝ ↑(⊤ : ℕ∞)
      (fun x => ∫ g, (f (((extChartAt I x₀).symm x)⁻¹ * g)) • w g)
      (extChartAt I x₀).target := by


  sorry

theorem contMDiff_convolution_integral
    (f : G → ℂ) (hf : IsSmoothCompactlySupportedFunction I f)
    (w : G → F) :
    ContMDiff I 𝓘(ℝ, F) ↑(⊤ : ℕ∞) (fun h => ∫ g, (f (h⁻¹ * g)) • w g) := by

  intro h₀

  rw [contMDiffAt_iff]

  set φ := fun x => ∫ g, (f (((extChartAt I h₀).symm x)⁻¹ * g)) • w g with hφ_def
  have hsmooth := contDiffOn_convolution_chartCoord I f hf w h₀
  have hmem_src : h₀ ∈ (extChartAt I h₀).source := mem_extChartAt_source h₀
  have hmem_tgt : (extChartAt I h₀) h₀ ∈ (extChartAt I h₀).target :=
    (extChartAt I h₀).map_source hmem_src

  have heq : ∀ x ∈ (extChartAt I h₀).source,
      (fun h => ∫ g, (f (h⁻¹ * g)) • w g) x = φ ((extChartAt I h₀) x) := by
    intro x hx
    simp only [hφ_def, (extChartAt I h₀).left_inv hx]
  have hcont_φ := hsmooth.continuousOn
  constructor
  ·


    have hcont_comp : ContinuousOn (φ ∘ (extChartAt I h₀)) (extChartAt I h₀).source := by
      apply hcont_φ.comp (continuousOn_extChartAt h₀)
      intro x hx; exact (extChartAt I h₀).map_source hx

    have hcont_on_src : ContinuousOn (fun h => ∫ g, (f (h⁻¹ * g)) • w g)
        (extChartAt I h₀).source := by
      apply hcont_comp.congr
      intro x hx
      exact heq x hx
    exact hcont_on_src.continuousAt ((isOpen_extChartAt_source h₀).mem_nhds hmem_src)
  ·

    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe]


    exact (hsmooth.contDiffWithinAt hmem_tgt).mono_of_mem_nhdsWithin
      (extChartAt_target_mem_nhdsWithin h₀)

theorem continuous_lieGroup_convolution
    (f : G → ℂ) (hf : IsSmoothCompactlySupportedFunction I f)
    (w : G → F) :
    Continuous (fun h => ∫ g, (f (h⁻¹ * g)) • w g) :=
  (contMDiff_convolution_integral I f hf w).continuous

theorem contDiffOn_lieGroup_convolution_chartCoord
    (f : G → ℂ) (hf : IsSmoothCompactlySupportedFunction I f)
    (w : G → F) (x₀ : G) (y₀ : F) :
    ContDiffOn ℝ ↑(⊤ : ℕ∞)
      (↑(extChartAt 𝓘(ℝ, F) y₀) ∘ (fun h => ∫ g, (f (h⁻¹ * g)) • w g) ∘
        ↑(extChartAt I x₀).symm)
      ((extChartAt I x₀).target ∩
        ↑(extChartAt I x₀).symm ⁻¹'
          ((fun h => ∫ g, (f (h⁻¹ * g)) • w g) ⁻¹' (extChartAt 𝓘(ℝ, F) y₀).source)) := by
  have h := contMDiff_convolution_integral I f hf w
  rw [contMDiff_iff] at h
  exact h.2 x₀ y₀

omit [T2Space G] [BorelSpace G] [SecondCountableTopology G] [LocallyCompactSpace G] in
lemma orbitMap_gardingVector_eq
    (π : ContinuousRep G F) (f : G → ℂ) (v : F) (h : G)
    (hint : Integrable (fun g => f g • (π.toMonoidHom g) v)) :
    π.orbitMap (π.repOfFunction f v) h =
    ∫ g, (f (h⁻¹ * g)) • ((π.toMonoidHom g) v) := by

  simp only [orbitMap, repOfFunction]

  have h1 := (ContinuousLinearMap.integral_comp_comm (π.toMonoidHom h) hint).symm
  rw [h1]

  simp_rw [ContinuousLinearMap.map_smul]

  simp_rw [← ContinuousLinearMap.mul_apply, ← map_mul π.toMonoidHom]


  have h4 : (fun g => f g • (π.toMonoidHom (h * g)) v) =
      (fun g => f (h⁻¹ * g) • (π.toMonoidHom g) v) ∘ (fun g => h * g) := by
    ext g; simp
  rw [h4]; simp only [Function.comp_def]
  exact @MeasureTheory.integral_mul_left_eq_self G F _ _ _ (volume : Measure G) _ _ _
    (fun g => f (h⁻¹ * g) • (π.toMonoidHom g) v) h

theorem gardingVector_isSmooth
    (π : ContinuousRep G F) (f : G → ℂ)
    (hf : IsSmoothCompactlySupportedFunction I f)
    (v : F) :
    π.IsSmoothVector I (π.repOfFunction f v) := by

  show ContMDiff I 𝓘(ℝ, F) ↑(⊤ : ℕ∞) (π.orbitMap (π.repOfFunction f v))


  by_cases hint : Integrable (fun g => f g • (π.toMonoidHom g) v)
  ·
    have heq : π.orbitMap (π.repOfFunction f v) =
        fun h => ∫ g, (f (h⁻¹ * g)) • ((π.toMonoidHom g) v) := by
      ext h; exact orbitMap_gardingVector_eq π f v h hint
    rw [heq]
    exact contMDiff_convolution_integral I f hf (fun g => (π.toMonoidHom g) v)
  ·
    have h0 : π.repOfFunction f v = 0 := by
      simp only [repOfFunction]
      exact integral_undef hint
    rw [h0]
    show ContMDiff I 𝓘(ℝ, F) ↑(⊤ : ℕ∞) (π.orbitMap 0)
    have : π.orbitMap 0 = fun _ => (0 : F) := by
      ext g; simp [orbitMap]
    rw [this]
    exact contMDiff_const

omit [MeasurableMul G] [Measure.IsMulLeftInvariant (volume : Measure G)] in
lemma exists_smooth_dirac_sequence
    [Measure.IsHaarMeasure (volume : Measure G)] :
    ∃ (φ : ℕ → G → ℂ),
      (∀ n, IsSmoothCompactlySupportedFunction I (φ n)) ∧
      (∀ n, ∀ g, (φ n g).im = 0 ∧ 0 ≤ (φ n g).re) ∧
      (∀ n, ∫ g, (φ n g).re = 1) ∧
      (∀ U ∈ nhds (1 : G), ∃ N, ∀ n, N ≤ n → Function.support (φ n) ⊆ U) := by

  have hmanif : IsManifold I (↑(⊤ : ℕ∞)) G := IsManifold.of_le le_top


  have hbasis := SmoothBumpFunction.nhds_basis_tsupport (I := I) (1 : G)
  obtain ⟨ψ, _, hanti⟩ := hbasis.exists_antitone_subbasis

  have hint_pos : ∀ n, 0 < ∫ g, (ψ n : G → ℝ) g := by
    intro n
    exact integral_pos_of_integrable_nonneg_nonzero
      (ψ n).contMDiff.continuous
      ((ψ n).contMDiff.continuous.integrable_of_hasCompactSupport (ψ n).hasCompactSupport)
      (fun g => (ψ n).nonneg)
      (by rw [(ψ n).eq_one]; exact one_ne_zero)


  refine ⟨fun n g => (↑(ψ n g * (∫ x, (ψ n : G → ℝ) x)⁻¹) : ℂ), ?_, ?_, ?_, ?_⟩

  · intro n
    refine ⟨?_, ?_⟩

    ·
      show ContMDiff I 𝓘(ℝ, ℂ) (↑(⊤ : ℕ∞)) (fun g => (↑(ψ n g * (∫ x, (ψ n : G → ℝ) x)⁻¹) : ℂ))
      have heq : (fun g => (↑(ψ n g * (∫ x, (ψ n : G → ℝ) x)⁻¹) : ℂ)) =
          Complex.ofRealCLM ∘ (fun g => (∫ x, (ψ n : G → ℝ) x)⁻¹ * ψ n g) := by
        ext g; simp [mul_comm]
      rw [heq]

      have h_inner : ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞))
          (fun g => (∫ x, (ψ n : G → ℝ) x)⁻¹ * (ψ n : G → ℝ) g) := by
        show ContMDiff I 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞)) ((∫ x, (ψ n : G → ℝ) x)⁻¹ • (ψ n : G → ℝ))
        exact contMDiff_const.smul (ψ n).contMDiff
      have h_ofReal : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) (↑(⊤ : ℕ∞)) Complex.ofRealCLM :=
        Complex.ofRealCLM.contMDiff.of_le le_top
      exact h_ofReal.comp h_inner

    ·
      show HasCompactSupport (fun g => (↑(ψ n g * (∫ x, (ψ n : G → ℝ) x)⁻¹) : ℂ))
      apply HasCompactSupport.of_support_subset_isCompact (ψ n).hasCompactSupport.isCompact
      intro g hg
      rw [Function.mem_support] at hg
      apply subset_closure
      rw [Function.mem_support]
      intro h
      apply hg
      simp [h]

  · intro n g
    constructor
    ·
      show (↑(ψ n g * (∫ x, (ψ n : G → ℝ) x)⁻¹) : ℂ).im = 0
      exact Complex.ofReal_im _
    ·
      show 0 ≤ (↑(ψ n g * (∫ x, (ψ n : G → ℝ) x)⁻¹) : ℂ).re
      rw [Complex.ofReal_re]
      exact mul_nonneg (ψ n).nonneg (le_of_lt (inv_pos.mpr (hint_pos n)))

  · intro n
    show ∫ g, (↑(ψ n g * (∫ x, (ψ n : G → ℝ) x)⁻¹) : ℂ).re = 1
    simp_rw [Complex.ofReal_re]
    rw [integral_mul_const]
    rw [mul_inv_cancel₀]
    exact ne_of_gt (hint_pos n)

  · intro U hU

    obtain ⟨N, _, hN⟩ := hanti.toHasBasis.mem_iff.mp hU
    refine ⟨N, fun n hn g hg => ?_⟩
    apply hN
    apply hanti.antitone hn

    rw [Function.mem_support] at hg
    apply subset_closure
    rw [Function.mem_support]
    intro h; apply hg; simp [h]

omit [LieGroup I ⊤ G] [FiniteDimensional ℝ E] [MeasurableMul G]
  [Measure.IsMulLeftInvariant (volume : Measure G)] in
lemma smooth_dirac_convolution_tendsto
    (π : ContinuousRep G F)
    [Measure.IsHaarMeasure (volume : Measure G)]
    (v : F)
    (φ : ℕ → G → ℂ)
    (hφsmooth : ∀ n, IsSmoothCompactlySupportedFunction I (φ n))
    (hφnonneg : ∀ n, ∀ g, (φ n g).im = 0 ∧ 0 ≤ (φ n g).re)
    (hφnorm : ∀ n, ∫ g, (φ n g).re = 1)
    (hφshrink : ∀ U ∈ nhds (1 : G), ∃ N, ∀ n, N ≤ n → Function.support (φ n) ⊆ U) :
    Filter.Tendsto (fun n => π.repOfFunction (φ n) v) Filter.atTop (nhds v) := by

  rw [NormedAddCommGroup.tendsto_atTop]
  intro ε hε

  have hcont_action : Continuous (fun g : G => (π.toMonoidHom g) v) :=
    π.continuous_action.comp (continuous_id.prodMk continuous_const)
  have hpi1 : (π.toMonoidHom 1) v = v := by
    rw [MonoidHom.map_one]; exact ContinuousLinearMap.one_apply v

  have hε2 : (0 : ℝ) < ε / 2 := half_pos hε
  have hU : {g : G | ‖(π.toMonoidHom g) v - v‖ < ε / 2} ∈ nhds (1 : G) := by
    have heq : {g : G | ‖(π.toMonoidHom g) v - v‖ < ε / 2} =
        (fun g => (π.toMonoidHom g) v - v) ⁻¹' Metric.ball 0 (ε / 2) := by
      ext g; simp [Metric.mem_ball, dist_zero_right]
    rw [heq]
    apply (hcont_action.sub continuous_const).continuousAt
    have : (fun g : G => (π.toMonoidHom g) v - v) 1 = 0 := by simp [MonoidHom.map_one, ContinuousLinearMap.one_apply]
    rw [this]; exact Metric.ball_mem_nhds 0 hε2

  obtain ⟨N, hN⟩ := hφshrink _ hU

  refine ⟨N, fun n hn => ?_⟩

  have hφreal : ∀ g, φ n g = ((φ n g).re : ℂ) := by
    intro g; apply Complex.ext <;> simp [(hφnonneg n g).1]

  have hφnorm_eq : ∀ g, ‖φ n g‖ = (φ n g).re := by
    intro g; conv_lhs => rw [hφreal g]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hφnonneg n g).2]

  have hφint_one : ∫ g, φ n g = (1 : ℂ) := by
    have heq : (fun g => φ n g) = fun g => ((φ n g).re : ℂ) := funext hφreal
    rw [heq, integral_complex_ofReal, hφnorm n]; simp

  have hφcont : Continuous (φ n) := (hφsmooth n).1.continuous
  have hφsupp : HasCompactSupport (φ n) := (hφsmooth n).2

  have hint1 : MeasureTheory.Integrable (fun g => (φ n g) • ((π.toMonoidHom g) v)) :=
    hcont_action.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφcont hφsupp

  have hint2 : MeasureTheory.Integrable (fun g => (φ n g) • v) :=
    continuous_const.locallyIntegrable.integrable_smul_left_of_hasCompactSupport hφcont hφsupp

  have hv_eq : v = ∫ g, (φ n g) • v := by
    rw [integral_smul_const]; erw [hφint_one]; simp

  have hkey : π.repOfFunction (φ n) v - v = ∫ g, (φ n g) • ((π.toMonoidHom g) v - v) := by
    have hsub : (∫ g, (φ n g) • ((π.toMonoidHom g) v)) - (∫ g, (φ n g) • v)
        = ∫ g, (φ n g) • ((π.toMonoidHom g) v - v) := by
      rw [← MeasureTheory.integral_sub hint1 hint2]
      congr 1; ext g; rw [smul_sub]
    simp only [repOfFunction]
    rw [← hsub]
    congr 1
  rw [hkey]

  have hint_re : MeasureTheory.Integrable (fun g => (φ n g).re) := by
    apply (Complex.continuous_re.comp hφcont).integrable_of_hasCompactSupport
    exact hφsupp.comp_left (show Complex.re 0 = 0 from rfl)

  calc ‖∫ g, (φ n g) • ((π.toMonoidHom g) v - v)‖
      ≤ ∫ g, ‖(φ n g) • ((π.toMonoidHom g) v - v)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ = ∫ g, ‖φ n g‖ * ‖(π.toMonoidHom g) v - v‖ := by
        congr 1; ext g; exact norm_smul _ _
    _ ≤ ∫ g, (φ n g).re * (ε / 2) := by
        apply MeasureTheory.integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun g => by positivity)
        · exact hint_re.mul_const (ε / 2)
        · apply Filter.Eventually.of_forall; intro g
          show ‖φ n g‖ * ‖(π.toMonoidHom g) v - v‖ ≤ (φ n g).re * (ε / 2)
          rw [hφnorm_eq g]
          by_cases hg : g ∈ Function.support (φ n)
          · exact mul_le_mul_of_nonneg_left (le_of_lt (hN n hn hg)) (hφnonneg n g).2
          · rw [Function.mem_support, not_not] at hg; simp [hg]
    _ = (ε / 2) * ∫ g, (φ n g).re := by
        rw [MeasureTheory.integral_mul_const]; ring
    _ = (ε / 2) * 1 := by rw [hφnorm n]
    _ = ε / 2 := mul_one _
    _ < ε := half_lt_self hε

omit [MeasurableMul G]
  [Measure.IsMulLeftInvariant (volume : Measure G)] in
lemma exists_gardingVector_tendsto
    (π : ContinuousRep G F)
    [Measure.IsHaarMeasure (volume : Measure G)]
    (v : F) :
    ∃ (φ : ℕ → G → ℂ),
      (∀ n, IsSmoothCompactlySupportedFunction I (φ n)) ∧
      Filter.Tendsto (fun n => π.repOfFunction (φ n) v) Filter.atTop (nhds v) := by

  obtain ⟨φ, hφsmooth, hφnonneg, hφnorm, hφshrink⟩ :=
    exists_smooth_dirac_sequence (G := G) I

  exact ⟨φ, hφsmooth,
    smooth_dirac_convolution_tendsto I π v φ hφsmooth hφnonneg hφnorm hφshrink⟩

omit [MeasurableMul G] [Measure.IsMulLeftInvariant (volume : Measure G)] in
theorem gardingSubspace_dense
    (π : ContinuousRep G F)
    [Measure.IsHaarMeasure (volume : Measure G)] :
    Dense (π.gardingSubspace I : Set F) := by
  rw [Dense]
  intro v

  obtain ⟨φ, hφsmooth, hφconv⟩ := exists_gardingVector_tendsto I π v

  have hmem : ∀ n, π.repOfFunction (φ n) v ∈ (π.gardingSubspace I : Set F) := by
    intro n
    apply Submodule.subset_span
    exact ⟨φ n, v, hφsmooth n, rfl⟩

  exact mem_closure_of_tendsto hφconv (Filter.Eventually.of_forall hmem)

end Garding

section DerivedOnGarding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable [LieGroup I ⊤ G]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable [MeasureSpace G] [CompleteSpace F]
variable [MeasurableMul G] [Measure.IsMulLeftInvariant (volume : Measure G)]

def leftInvariantDeriv (lieExp : E → G) (X : E) (f : G → ℂ) (g : G) : ℂ :=
  deriv (fun t : ℝ => f (g * lieExp (t • X))) 0


theorem derivedRep_gardingVector
    (π : ContinuousRep G F) (lieExp : E → G)
    (hExp : ContMDiff 𝓘(ℝ, E) I ⊤ lieExp)
    (hExp1 : lieExp 0 = 1)
    (X : E) (f : G → ℂ) (v : F)
    (hf : IsSmoothCompactlySupportedFunction I f) :
    π.derivedRep lieExp X (π.repOfFunction f v) =
    π.repOfFunction (leftInvariantDeriv lieExp X f) v := by


  sorry

end DerivedOnGarding

theorem contMDiff_orbitMap_of_finiteDimensional
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {W : Submodule ℂ F} [FiniteDimensional ℂ W]
    (ρ : G →* (W →L[ℂ] W))
    (hρ_cont : Continuous (fun p : G × W => (ρ p.1) p.2))
    (w : W) :
    ContMDiff I 𝓘(ℝ, F) ↑(⊤ : ℕ∞) (fun g => ((ρ g) w : F)) := by


  sorry

section FiniteSubsetSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable [LieGroup I ⊤ G]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem lieGroup_finiteDimOrbit_smooth_orbitMap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : G →* (F →L[ℂ] F))
    (hπ_cont : Continuous (fun p : G × F => (π p.1) p.2))
    (v : F)
    (hfin : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range (fun g : G => (π g) v)))) :
    ContMDiff I 𝓘(ℝ, F) ↑(⊤ : ℕ∞) (fun g => (π g) v) := by

  set W := Submodule.span ℂ (Set.range (fun g : G => (π g) v)) with hW_def
  haveI : FiniteDimensional ℂ W := hfin

  have hW_inv : ∀ h : G, ∀ w ∈ W, (π h) w ∈ W := by
    intro h w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      have : (π h) ((π g) v) = (π (h * g)) v := by
        simp [map_mul, ContinuousLinearMap.mul_apply]
      rw [this]
      exact Submodule.subset_span ⟨h * g, rfl⟩
    | zero => simp [map_zero]
    | add x y _ _ ihx ihy =>
      rw [map_add]
      exact W.add_mem ihx ihy
    | smul c x _ ihx =>
      rw [ContinuousLinearMap.map_smul]
      exact W.smul_mem c ihx

  have hv_mem : v ∈ W := by
    have : v = (π 1) v := by simp [map_one]
    rw [this]
    exact Submodule.subset_span ⟨1, rfl⟩

  let ρ_fun : G → (↥W →L[ℂ] ↥W) := fun g => {
    toFun := fun w => ⟨(π g) w, hW_inv g w w.prop⟩
    map_add' := by intro x y; ext; simp [map_add]
    map_smul' := by intro c x; ext; simp
    cont := Continuous.subtype_mk ((π g).continuous.comp continuous_subtype_val) _
  }
  let ρ : G →* (↥W →L[ℂ] ↥W) := {
    toFun := ρ_fun
    map_one' := by
      ext ⟨w, hw⟩
      simp only [ρ_fun, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
      simp [map_one]
    map_mul' := by
      intro g₁ g₂
      ext ⟨w, hw⟩
      simp only [ρ_fun, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
      simp [map_mul, ContinuousLinearMap.mul_apply]
  }

  have hfactor : (fun g => (π g) v) = (fun g => ((ρ g) ⟨v, hv_mem⟩ : F)) := by
    ext g
    simp [ρ, ρ_fun]
  rw [hfactor]

  have hρ_cont : Continuous (fun p : G × ↥W => (ρ p.1) p.2) := by
    apply continuous_induced_rng.mpr
    show Continuous (fun p : G × ↥W => ((ρ p.1) p.2 : F))
    have heq : (fun p : G × ↥W => ((ρ p.1) p.2 : F)) =
               (fun p : G × ↥W => (π p.1) (p.2 : F)) := by
      ext ⟨g, ⟨w, hw⟩⟩; simp [ρ, ρ_fun]
    rw [heq]
    exact hπ_cont.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))

  exact contMDiff_orbitMap_of_finiteDimensional I (W := W) ρ hρ_cont ⟨v, hv_mem⟩

theorem finDimRep_orbitMap_smooth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : G →* (F →L[ℂ] F))
    (hπ_cont : Continuous (fun p : G × F => (π p.1) p.2))
    (v : F)
    (hfin : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range (fun g : G => (π g) v)))) :
    ContMDiff I 𝓘(ℝ, F) ↑(⊤ : ℕ∞) (fun g => (π g) v) :=
  lieGroup_finiteDimOrbit_smooth_orbitMap I π hπ_cont v hfin

theorem orbitMap_smooth_of_finiteDim_span
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (v : F)
    (hfin : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range (fun g : G => (π.toMonoidHom g) v)))) :
    ContMDiff I 𝓘(ℝ, F) ↑(⊤ : ℕ∞) (π.orbitMap v) := by

  show ContMDiff I 𝓘(ℝ, F) ↑(⊤ : ℕ∞) (fun g => (π.toMonoidHom g) v)
  exact finDimRep_orbitMap_smooth I π.toMonoidHom π.continuous_action v hfin

theorem kfinite_le_smooth
    (π : ContinuousRep G F) :
    π.kFiniteSubspace ⊤ ≤ π.smoothSubspace I := by
  intro v hv

  rw [ContinuousRep.mem_kFiniteSubspace] at hv
  unfold ContinuousRep.IsKFinite at hv


  show π.IsSmoothVector I v
  unfold ContinuousRep.IsSmoothVector


  apply orbitMap_smooth_of_finiteDim_span I π v

  have heq : Set.range (fun g : G => (π.toMonoidHom g) v) =
             Set.range (fun k : (⊤ : Subgroup G) => (π.toMonoidHom ↑k) v) := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩
    · rintro ⟨⟨g, _⟩, rfl⟩
      exact ⟨g, rfl⟩
  rw [heq]
  exact hv

end FiniteSubsetSmooth

end ContinuousRep

end
