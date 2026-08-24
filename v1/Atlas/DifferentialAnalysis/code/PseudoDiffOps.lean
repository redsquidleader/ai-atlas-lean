/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.DifferentialOperators
import Atlas.DifferentialAnalysis.code.ConvolutionTheorem
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.Compactness.LocallyCompact

noncomputable section

open scoped SchwartzMap Pointwise
open MeasureTheory Set Function TemperedDistribution

namespace DifferentialOperators

variable {n : ℕ}

/-- A tempered distribution `u` on Euclidean space has compact support if there is a
compact `K` such that `u` annihilates every Schwartz function whose support is disjoint
from `K`. -/
def HasCompactSupport (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∃ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K ∧
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (Function.support (⇑φ) ∩ K = ∅) → u φ = 0

/-- If `μ` has compact support in the Schwartz-pairing sense, then its distributional
support `Distribution.dsupport μ` is compact. -/
theorem hasCompactDsupport_of_hasCompactSupport
    (μ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ) :
    HasCompactDsupport μ := by
  obtain ⟨K, hK_compact, hK_supp⟩ := hμ

  have hclosed := Distribution.isClosed_dsupport (f := μ)

  have hK_closed : IsClosed K := hK_compact.isClosed
  have hvanish : Distribution.IsVanishingOn μ Kᶜ := by
    intro φ hφ
    apply hK_supp
    rw [Set.eq_empty_iff_forall_notMem]
    intro y ⟨hy_supp, hy_K⟩
    have hy_tsupp : y ∈ tsupport (⇑φ) := subset_tsupport _ hy_supp
    exact absurd hy_K (Set.mem_compl_iff K y |>.mp (hφ hy_tsupp))
  have hsubset : Distribution.dsupport μ ⊆ K := by
    have hd := hvanish.disjoint_dsupport hK_closed.isOpen_compl
    rwa [Set.disjoint_compl_left_iff_subset] at hd
  exact hK_compact.of_isClosed_subset hclosed hsubset

/-- The reflection `φ ↦ φ ∘ (-id)` as a continuous linear endomorphism of the Schwartz
space `𝓢(EuclideanSpace ℝ (Fin n), ℂ)`. -/
def schwNegReflCLM :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ)

/-- Cross-correlation with a compactly supported distribution `μ`, viewed as a continuous
linear endomorphism of `𝓢(EuclideanSpace ℝ (Fin n), ℂ)`. -/
def crossCorrSchwartzCLM
    (μ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ) :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  let hμ' := hasCompactDsupport_of_hasCompactSupport μ hμ
  { toLinearMap :=
      { toFun := compactDsupportConvolutionSchwartzMap μ hμ'
        map_add' := compactDsupportConvolution_map_add μ hμ'
        map_smul' := compactDsupportConvolution_map_smul μ hμ' }
    cont := continuous_compactDsupportConvolution μ hμ' }

/-- Convolution with a compactly supported distribution `μ` on Schwartz functions, given
as the reflection composed with cross-correlation. -/
def convolutionSchwartzCLM
    (μ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ) :
    𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), ℂ) :=
  schwNegReflCLM.comp (crossCorrSchwartzCLM μ hμ)

/-- The convolution `μ * f` of two tempered distributions, defined when the left factor
`μ` has compact support, by precomposing `f` with convolution by `μ` on Schwartz test
functions. -/
def distribConvolution
    (μ f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ) :
    𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (PointwiseConvergenceCLM.precomp ℂ (convolutionSchwartzCLM μ hμ)) f

/-- A decomposition of a tempered distribution `u = singular + smooth` into a singular
part with compact support contained in `supportSet` and a globally smooth, compactly
supported part. Used in the proof of `singularSupport_convolution_subset`. -/
structure SmoothDecomp (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) where
  singular : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)
  smooth : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)
  supportSet : Set (EuclideanSpace ℝ (Fin n))
  supportSet_compact : IsCompact supportSet
  singular_supported :
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (Function.support (⇑φ) ∩ supportSet = ∅) → singular φ = 0
  singular_compactSupport : HasCompactSupport singular
  smooth_isSmooth : ∀ x₀ : EuclideanSpace ℝ (Fin n), isSmoothNear smooth x₀
  smooth_compactSupport : HasCompactSupport smooth
  sum_eq : u = singular + smooth


/-- If `u` has compact support, then its singular support is compact (in particular,
closed and contained in the support of `u`). -/
theorem singularSupport_compact_of_compactSupport
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hu : HasCompactSupport u) :
    IsCompact (singularSupport u) := by
  obtain ⟨K, hK_compact, hK_supp⟩ := hu
  have hclosed : IsClosed (singularSupport u) := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_forall_mem_open.mpr
    intro x₀ hx₀
    have hsmooth : isSmoothNear u x₀ := not_not.mp hx₀
    obtain ⟨U, hU_open, hx₀_mem, f, hf_smooth, hf_eq⟩ := hsmooth
    refine ⟨U, fun x₁ hx₁ => ?_, hU_open, hx₀_mem⟩
    exact not_not.mpr ⟨U, hU_open, hx₁, f, hf_smooth, hf_eq⟩
  have hsubset : singularSupport u ⊆ K := by
    intro x₀ hx₀
    by_contra hx₀K
    apply hx₀
    have hK_closed : IsClosed K := hK_compact.isClosed
    refine ⟨Kᶜ, hK_closed.isOpen_compl, hx₀K, 0, contDiff_const, fun φ hφ => ?_⟩
    have hsup : Function.support (⇑φ) ∩ K = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro y hy
      exact absurd (hφ y (not_not.mpr hy.2)) (mem_support.mp hy.1)
    rw [hK_supp φ hsup]
    simp [integral_zero]
  exact hK_compact.of_isClosed_subset hclosed hsubset


/-- Partition-of-unity identity for left multiplication by a tempered-growth function `χ`:
`χ · u + (1 - χ) · u = u`. -/
theorem smulLeft_add_complement
    (χ : EuclideanSpace ℝ (Fin n) → ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hχ : Function.HasTemperateGrowth χ := by fun_prop) :
    smulLeftCLM ℂ χ u + smulLeftCLM ℂ (1 - χ) u = u := by
  have h1χ : Function.HasTemperateGrowth (1 - χ) :=
    (Function.HasTemperateGrowth.const (1 : ℂ)).sub hχ
  ext φ
  simp only [UniformConvergenceCLM.add_apply, smulLeftCLM_apply_apply]
  rw [← map_add u]
  congr 1
  ext x
  simp only [SchwartzMap.add_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply hχ, SchwartzMap.smulLeftCLM_apply_apply h1χ]
  simp [Pi.sub_apply, smul_eq_mul, sub_mul, one_mul]


/-- Multiplying a Schwartz function `φ` by a function `χ` (via `SchwartzMap.smulLeftCLM`)
can only shrink the support: `supp (χ · φ) ⊆ supp φ`. -/
lemma support_schwartz_smulLeft_subset
    (χ : EuclideanSpace ℝ (Fin n) → ℂ)
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    Function.support (⇑(SchwartzMap.smulLeftCLM ℂ χ φ)) ⊆ Function.support (⇑φ) := by
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro h
  apply hx
  unfold SchwartzMap.smulLeftCLM
  split
  · simp [SchwartzMap.bilinLeftCLM_apply, h]
  · simp


/-- If `u` has compact support, then so does the distribution `χ · u` obtained by left
multiplication by an arbitrary function `χ`. -/
theorem smulLeft_hasCompactSupport
    (χ : EuclideanSpace ℝ (Fin n) → ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hu : HasCompactSupport u) :
    HasCompactSupport (smulLeftCLM ℂ χ u) := by
  obtain ⟨K, hK_compact, hK_supp⟩ := hu
  exact ⟨K, hK_compact, fun φ hφ => by
    simp only [smulLeftCLM_apply_apply]
    apply hK_supp
    rw [Set.eq_empty_iff_forall_notMem]
    intro y ⟨hy_supp, hy_K⟩
    have : y ∈ Function.support (⇑φ) := support_schwartz_smulLeft_subset χ φ hy_supp
    exact Set.eq_empty_iff_forall_notMem.mp hφ y ⟨this, hy_K⟩⟩


/-- If the support of the cutoff function `χ` is contained in `S`, then the distribution
`χ · u` annihilates every Schwartz function whose support is disjoint from `S`. -/
theorem smulLeft_supported
    (χ : EuclideanSpace ℝ (Fin n) → ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS : tsupport χ ⊆ S) :
    ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (Function.support (⇑φ) ∩ S = ∅) → (smulLeftCLM ℂ χ u) φ = 0 := by
  classical
  intro φ hφ
  rw [smulLeftCLM_apply_apply]
  suffices h : SchwartzMap.smulLeftCLM ℂ χ φ = 0 by
    rw [h, map_zero]
  by_cases hg : HasTemperateGrowth χ
  · ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply hg]
    simp only [SchwartzMap.coe_zero, Pi.zero_apply]
    by_cases hx : x ∈ support (⇑φ)
    · have hxS : x ∉ S := fun hxS =>
        (eq_empty_iff_forall_notMem.mp hφ) x ⟨hx, hxS⟩
      have hx_notin_supp : x ∉ support χ := fun h =>
        hxS (hS (subset_tsupport χ h))
      rw [notMem_support.mp hx_notin_supp, zero_smul]
    · rw [notMem_support.mp hx, smul_zero]
  · change (if hg : HasTemperateGrowth χ
        then SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul ℂ ℂ).flip hg
        else 0) φ = 0
    rw [dif_neg hg]
    simp [ContinuousLinearMap.zero_apply]


/-- If a smooth function `χ` vanishes on the singular support of `u`, then the
distribution `χ · u` is smooth near every point. -/
theorem smulLeft_smooth_of_vanishesOnSingSupp
    (χ : EuclideanSpace ℝ (Fin n) → ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hχ_vanish : ∀ x ∈ singularSupport u, χ x = 0)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    isSmoothNear (smulLeftCLM ℂ χ u) x₀ := by sorry


set_option maxHeartbeats 400000 in
/-- Existence of a smooth complex-valued bump function which equals `1` on a neighbourhood
of a closed set `F` and is supported in a given compact superset `K` (with `F ⊆ int K`). -/
theorem exists_smooth_bump_subset
    (F : Set (EuclideanSpace ℝ (Fin n)))
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (hF : IsClosed F)
    (hK : IsCompact K)
    (hFK : F ⊆ interior K) :
    ∃ χ : EuclideanSpace ℝ (Fin n) → ℂ,
      ContDiff ℝ (↑(⊤ : ℕ∞)) χ ∧
      _root_.HasCompactSupport χ ∧
      tsupport χ ⊆ K ∧
      (∃ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V ∧ F ⊆ V ∧ ∀ x ∈ V, χ x = 1) := by
  obtain ⟨f, hf_one, hf_zero, _⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior
      (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (n := ⊤) (s := F) (t := K) hF hFK
  let χ : EuclideanSpace ℝ (Fin n) → ℂ := fun x => ((f : EuclideanSpace ℝ (Fin n) → ℝ) x : ℂ)
  have hf_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) (f : EuclideanSpace ℝ (Fin n) → ℝ) :=
    contMDiff_iff_contDiff.mp f.2
  have hsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) χ :=
    Complex.ofRealCLM.contDiff.comp hf_contDiff
  have hsupp : Function.support (f : EuclideanSpace ℝ (Fin n) → ℝ) ⊆ K := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra h
    exact hx (hf_zero x h)
  have htsupp : tsupport χ ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    rw [Function.mem_support] at hx
    have hxne : (f : EuclideanSpace ℝ (Fin n) → ℝ) x ≠ 0 := by
      intro heq; apply hx; simp [χ, heq]
    exact hsupp (Function.mem_support.mpr hxne)
  have hcompsupp : _root_.HasCompactSupport χ :=
    hK.of_isClosed_subset (isClosed_tsupport χ) htsupp
  refine ⟨χ, hsmooth, hcompsupp, htsupp, ?_⟩
  rw [eventually_nhdsSet_iff_forall] at hf_one
  refine ⟨interior {x | (f : EuclideanSpace ℝ (Fin n) → ℝ) x = 1}, isOpen_interior, ?_, ?_⟩
  · intro x hx
    exact mem_interior_iff_mem_nhds.mpr (hf_one x hx)
  · intro x hx
    have hfx := interior_subset hx
    simp only [χ, Set.mem_setOf_eq] at hfx ⊢
    rw [hfx, Complex.ofReal_one]


/-- Existence of a `SmoothDecomp` of a compactly supported tempered distribution `u` into
a singular part supported in any compact set `K` containing the singular support in its
interior, plus a globally smooth, compactly supported remainder. -/
theorem exists_smoothDecomp
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hu : HasCompactSupport u)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K)
    (hK_contains : singularSupport u ⊆ interior K) :
    ∃ d : SmoothDecomp u, d.supportSet ⊆ K := by

  have hSS_closed : IsClosed (singularSupport u) := by
    have hSS_compact := singularSupport_compact_of_compactSupport u hu
    exact hSS_compact.isClosed

  obtain ⟨χ, hχ_smooth, hχ_compsupp, hχ_tsupp, V, hV_open, hSS_sub_V, hχ_one⟩ :=
    exists_smooth_bump_subset (singularSupport u) K hSS_closed hK hK_contains


  have hsum : u = smulLeftCLM ℂ χ u + smulLeftCLM ℂ (1 - χ) u :=
    (smulLeft_add_complement χ u (hχ_compsupp.hasTemperateGrowth hχ_smooth)).symm

  refine ⟨⟨smulLeftCLM ℂ χ u,
           smulLeftCLM ℂ (1 - χ) u,
           K,
           hK,
           ?singular_supp,
           ?singular_cs,
           ?smooth_smooth,
           ?smooth_cs,
           hsum⟩,
         Subset.rfl⟩
  case singular_supp =>
    exact smulLeft_supported χ u K hχ_tsupp
  case singular_cs =>
    exact smulLeft_hasCompactSupport χ u hu
  case smooth_smooth =>

    intro x₀
    apply smulLeft_smooth_of_vanishesOnSingSupp (1 - χ) u
    · exact contDiff_const.sub hχ_smooth
    · intro x hx
      have hxV : x ∈ V := hSS_sub_V hx
      simp [hχ_one x hxV]
  case smooth_cs =>
    exact smulLeft_hasCompactSupport (1 - χ) u hu


/-- If a tempered distribution `f` is smooth near every point, then it is globally
represented by a single smooth function `g`: `⟨f, φ⟩ = ∫ φ(y) • g(y) dy`. -/
theorem globally_smooth_has_global_representative
    (f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hf : ∀ x₀ : EuclideanSpace ℝ (Fin n), isSmoothNear f x₀) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℂ, ContDiff ℝ ⊤ g ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), f φ = ∫ y, φ y • g y := by sorry


/-- Distributional Fubini for the convolution `μ * φ` of a compactly supported `μ` with a
Schwartz function `φ`, tested against a smooth function `g`: there is a Schwartz
representative `ψ` whose `μ`-convolution `tempDistSchwartzConv μ ψ` realises the
swap-of-order integral identity. -/
theorem distributional_fubini_compact_support
    (μ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ)
    (g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hg : ContDiff ℝ ⊤ g) :
    ∃ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      ContDiff ℝ ⊤ (tempDistSchwartzConv μ ψ) ∧
        ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
          ∫ y, (convolutionSchwartzCLM μ hμ φ) y • g y =
          ∫ y, φ y • (tempDistSchwartzConv μ ψ) y := by sorry

/-- Given a compactly supported distribution `μ` and a smooth function `g`, there is a
smooth function `h` realising the swap-of-order identity for the `μ`-convolution against
`g`. Wrapper around `distributional_fubini_compact_support`. -/
theorem exists_smooth_convolution_representative
    (μ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ)
    (g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hg : ContDiff ℝ ⊤ g) :
    ∃ h : EuclideanSpace ℝ (Fin n) → ℂ, ContDiff ℝ ⊤ h ∧
      ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        ∫ y, (convolutionSchwartzCLM μ hμ φ) y • g y =
        ∫ y, φ y • h y := by
  obtain ⟨ψ, hsmooth, hintegral⟩ := distributional_fubini_compact_support μ hμ g hg
  exact ⟨tempDistSchwartzConv μ ψ, hsmooth, hintegral⟩


/-- If the right factor `f` of a distributional convolution `μ * f` is represented by a
smooth function `g`, then `μ * f` is smooth near every point. -/
theorem distribConvolution_of_smooth_function_isSmoothNear
    (μ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ)
    (f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (g : EuclideanSpace ℝ (Fin n) → ℂ)
    (hg : ContDiff ℝ ⊤ g)
    (hfg : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), f φ = ∫ y, φ y • g y)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    isSmoothNear (distribConvolution μ f hμ) x₀ := by

  obtain ⟨h, hh_smooth, hh_eq⟩ := exists_smooth_convolution_representative μ hμ g hg

  refine ⟨Set.univ, isOpen_univ, Set.mem_univ x₀, h, hh_smooth.of_le le_top, fun φ _ => ?_⟩


  show f (convolutionSchwartzCLM μ hμ φ) = ∫ y, φ y • h y

  rw [hfg]

  exact hh_eq φ

/-- If the right factor `f` is globally smooth, then the distributional convolution
`μ * f` is smooth near every point. -/
theorem isSmoothNear_distribConvolution_of_smooth_right
    (μ f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ)
    (hf_smooth : ∀ x₀, isSmoothNear f x₀)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    isSmoothNear (distribConvolution μ f hμ) x₀ := by
  obtain ⟨g, hg_smooth, hg_eq⟩ := globally_smooth_has_global_representative f hf_smooth
  exact distribConvolution_of_smooth_function_isSmoothNear μ hμ f g hg_smooth hg_eq x₀


/-- If the left factor `μ` is represented by a smooth function `g_μ`, then the
distributional convolution `μ * f` is smooth near every point. -/
theorem distribConvolution_of_smooth_left_function_isSmoothNear
    (μ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ)
    (g_μ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hgμ : ContDiff ℝ ⊤ g_μ)
    (hμg : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), μ φ = ∫ y, φ y • g_μ y)
    (f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    isSmoothNear (distribConvolution μ f hμ) x₀ := by sorry

/-- If the left factor `μ` is globally smooth, then the distributional convolution
`μ * f` is smooth near every point. -/
theorem isSmoothNear_distribConvolution_of_smooth_left
    (μ f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ)
    (hμ_smooth : ∀ x₀, isSmoothNear μ x₀)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    isSmoothNear (distribConvolution μ f hμ) x₀ := by
  obtain ⟨g_μ, hg_smooth, hg_eq⟩ := globally_smooth_has_global_representative μ hμ_smooth
  exact distribConvolution_of_smooth_left_function_isSmoothNear μ hμ g_μ hg_smooth hg_eq f x₀


/-- If `μ` is supported in `K₁` and `f` is supported in `K₂` (in the Schwartz-pairing
sense), then `distribConvolution μ f` vanishes on the complement of the sum `K₁ + K₂`.
This is the support property `supp (μ * f) ⊆ supp μ + supp f`. -/
theorem distribConvolution_vanishesOn_compl
    (μ f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ)
    (K₁ K₂ : Set (EuclideanSpace ℝ (Fin n)))
    (hμK : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (Function.support (⇑φ) ∩ K₁ = ∅) → μ φ = 0)
    (hfK : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (Function.support (⇑φ) ∩ K₂ = ∅) → f φ = 0) :
    vanishesOn (distribConvolution μ f hμ) (K₁ + K₂)ᶜ := by


  intro φ hφ
  apply hfK
  rw [Set.eq_empty_iff_forall_notMem]
  intro x ⟨hx_supp, hx_K₂⟩


  have hconv_zero : (convolutionSchwartzCLM μ hμ φ).1 x = 0 := by


    show μ (SchwartzMap.compSubConstCLM ℂ (-x) φ) = 0
    apply hμK
    rw [Set.eq_empty_iff_forall_notMem]
    intro y ⟨hy_supp, hy_K₁⟩


    have hmem : y + x ∈ K₁ + K₂ := Set.add_mem_add hy_K₁ hx_K₂
    have hvanish : φ (y + x) = 0 := hφ _ (by rwa [Set.mem_compl_iff, not_not])
    rw [Function.mem_support] at hy_supp
    exact hy_supp (by simp only [SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]; exact hvanish)
  rw [Function.mem_support] at hx_supp
  exact hx_supp hconv_zero

/-- If a distribution `u` vanishes on an open neighbourhood `U` of `p`, then it is smooth
near `p` (with representative the zero function). -/
theorem isSmoothNear_of_vanishes_near
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (p : EuclideanSpace ℝ (Fin n))
    (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hp : p ∈ U)
    (hv : vanishesOn u U) :
    isSmoothNear u p := by
  refine ⟨U, hU, hp, 0, contDiff_const, fun φ hφ => ?_⟩
  rw [hv φ hφ]
  simp [smul_zero, integral_zero]


/-- The sum `u₁ + u₂` of two tempered distributions is smooth near `p` whenever both
summands are. -/
theorem isSmoothNear_add
    (u₁ u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (p : EuclideanSpace ℝ (Fin n))
    (h₁ : isSmoothNear u₁ p) (h₂ : isSmoothNear u₂ p) :
    isSmoothNear (u₁ + u₂) p := by
  obtain ⟨U₁, hU₁_open, hp₁, f₁, hf₁_smooth, hf₁_eq⟩ := h₁
  obtain ⟨U₂, hU₂_open, hp₂, f₂, hf₂_smooth, hf₂_eq⟩ := h₂
  refine ⟨U₁ ∩ U₂, hU₁_open.inter hU₂_open, ⟨hp₁, hp₂⟩, f₁ + f₂,
    hf₁_smooth.add hf₂_smooth, ?_⟩
  intro φ hφ_supp
  have hφ₁ : ∀ y, y ∉ U₁ → φ y = 0 := fun y hy =>
    hφ_supp y (fun ⟨hyU₁, _⟩ => hy hyU₁)
  have hφ₂ : ∀ y, y ∉ U₂ → φ y = 0 := fun y hy =>
    hφ_supp y (fun ⟨_, hyU₂⟩ => hy hyU₂)
  simp only [UniformConvergenceCLM.add_apply]
  rw [hf₁_eq φ hφ₁, hf₂_eq φ hφ₂]
  have h_int₁ : Integrable (fun y => φ y • f₁ y) volume :=
    schwartz_smul_smooth_integrable u₁ U₁ hU₁_open f₁ hf₁_smooth hf₁_eq φ hφ₁
  have h_int₂ : Integrable (fun y => φ y • f₂ y) volume :=
    schwartz_smul_smooth_integrable u₂ U₂ hU₂_open f₂ hf₂_smooth hf₂_eq φ hφ₂
  simp_rw [Pi.add_apply, smul_add]
  exact (integral_add h_int₁ h_int₂).symm


/-- Additivity of `distribConvolution` in the left compactly-supported factor. -/
theorem distribConvolution_add_left
    (μ₁ μ₂ f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ₁ : HasCompactSupport μ₁)
    (hμ₂ : HasCompactSupport μ₂)
    (hμ : HasCompactSupport (μ₁ + μ₂)) :
    distribConvolution (μ₁ + μ₂) f hμ =
    distribConvolution μ₁ f hμ₁ + distribConvolution μ₂ f hμ₂ := by

  ext φ

  show f (convolutionSchwartzCLM (μ₁ + μ₂) hμ φ) =
    f (convolutionSchwartzCLM μ₁ hμ₁ φ) + f (convolutionSchwartzCLM μ₂ hμ₂ φ)


  rw [← map_add f]
  congr 1


/-- Additivity of `distribConvolution` in the right factor. -/
theorem distribConvolution_add_right
    (μ f₁ f₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ) :
    distribConvolution μ (f₁ + f₂) hμ =
    distribConvolution μ f₁ hμ + distribConvolution μ f₂ hμ :=
  map_add (PointwiseConvergenceCLM.precomp ℂ (convolutionSchwartzCLM μ hμ)) f₁ f₂


/-- Tube-lemma–style enlargement: given compact `K₁, K₂` and a point `p` outside
`K₁ + K₂`, there exist compact `L₁, L₂` containing `K₁, K₂` in their interiors with
`p ∉ L₁ + L₂`. -/
theorem exists_compact_neighborhood_disjoint_sum
    (K₁ K₂ : Set (EuclideanSpace ℝ (Fin n)))
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (p : EuclideanSpace ℝ (Fin n))
    (hp : p ∉ K₁ + K₂) :
    ∃ (L₁ L₂ : Set (EuclideanSpace ℝ (Fin n))),
      IsCompact L₁ ∧ IsCompact L₂ ∧ K₁ ⊆ interior L₁ ∧ K₂ ⊆ interior L₂ ∧ p ∉ L₁ + L₂ := by


  have hprod : K₁ ×ˢ K₂ ⊆ (fun xy : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => xy.1 + xy.2) ⁻¹' {p}ᶜ := by
    intro ⟨x, y⟩ ⟨hx, hy⟩ hmem
    apply hp
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hmem
    exact ⟨x, hx, y, hy, hmem⟩
  have hopen : IsOpen ((fun xy : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => xy.1 + xy.2) ⁻¹' {p}ᶜ) :=
    isOpen_compl_iff.mpr (isClosed_singleton.preimage (continuous_fst.add continuous_snd))

  obtain ⟨U₁, U₂, hU₁_open, hU₂_open, hK₁U₁, hK₂U₂, hprod_sub⟩ :=
    generalized_tube_lemma hK₁ hK₂ hopen hprod
  obtain ⟨L₁, hL₁_compact, hK₁_int, hL₁_sub⟩ := exists_compact_between hK₁ hU₁_open hK₁U₁
  obtain ⟨L₂, hL₂_compact, hK₂_int, hL₂_sub⟩ := exists_compact_between hK₂ hU₂_open hK₂U₂
  refine ⟨L₁, L₂, hL₁_compact, hL₂_compact, hK₁_int, hK₂_int, ?_⟩
  intro hmem
  obtain ⟨a, ha, b, hb, hab⟩ := hmem
  have hab_mem : (a, b) ∈ U₁ ×ˢ U₂ := ⟨hL₁_sub ha, hL₂_sub hb⟩
  have := hprod_sub hab_mem
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at this
  exact this hab


/-- If the cutoff function `χ` is compactly supported, then `χ · u` is a compactly
supported distribution for every tempered `u`. -/
theorem hasCompactSupport_smulLeft_of_compactSupport_function
    (χ : EuclideanSpace ℝ (Fin n) → ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hχ : _root_.HasCompactSupport χ) :
    HasCompactSupport (smulLeftCLM ℂ χ u) := by sorry


/-- Multiplying a distribution `u` by a smooth function `χ` can only shrink the singular
support: `singsupp (χ · u) ⊆ singsupp u`. -/
theorem singularSupport_smulLeft_subset
    (χ : EuclideanSpace ℝ (Fin n) → ℂ)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ) :
    singularSupport (smulLeftCLM ℂ χ u) ⊆ singularSupport u := by
  classical
  by_cases htemp : Function.HasTemperateGrowth χ
  · exact singularSupport_smulLeft_subset_of_temperate χ hχ htemp u
  ·

    have hSchwartzZero : SchwartzMap.smulLeftCLM ℂ χ = (0 : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) := by
      unfold SchwartzMap.smulLeftCLM
      split
      · exact absurd ‹_› htemp
      · rfl
    have hzero : smulLeftCLM ℂ χ u = 0 := by
      ext φ
      simp only [smulLeftCLM_apply_apply]
      rw [hSchwartzZero]
      simp
    intro x₀ hx₀
    exfalso
    apply hx₀
    rw [hzero]
    refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, 0, contDiff_const, fun φ _ => ?_⟩
    simp [integral_zero]


/-- If `ψ` equals `1` on an open set `V`, then the support of `1 - ψ` is contained in the
complement of `V`. -/
theorem tsupport_one_sub_subset_compl
    (ψ : EuclideanSpace ℝ (Fin n) → ℂ)
    (V : Set (EuclideanSpace ℝ (Fin n)))
    (hV : IsOpen V)
    (hψ_one : ∀ x ∈ V, ψ x = 1) :
    tsupport (1 - ψ) ⊆ Vᶜ := by sorry


/-- The Minkowski sum `K + C` of a compact set `K` and a closed set `C` in Euclidean
space is closed. -/
theorem isClosed_compact_add_closed
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (C : Set (EuclideanSpace ℝ (Fin n)))
    (hK : IsCompact K)
    (hC : IsClosed C) :
    IsClosed (K + C) := by sorry


/-- Reduction step: to check smoothness of `distribConvolution μ f` near a point `p`
outside `singsupp μ + singsupp f`, one may replace `f` by a compactly supported
distribution `f'` with smaller singular support whose convolution carries the same local
smoothness information. -/
theorem distribConvolution_reduce_to_compact_support
    (μ f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ)
    (p : EuclideanSpace ℝ (Fin n))
    (hp : p ∉ singularSupport μ + singularSupport f) :
    ∃ (f' : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)),
      HasCompactSupport f' ∧
      singularSupport f' ⊆ singularSupport f ∧
      (isSmoothNear (distribConvolution μ f' hμ) p →
       isSmoothNear (distribConvolution μ f hμ) p) := by

  have ⟨Kμ, hKμ_compact, hKμ_supp⟩ := hμ


  set F : Set (EuclideanSpace ℝ (Fin n)) := (fun x => p - x) '' Kμ with hF_def
  have hF_compact : IsCompact F := hKμ_compact.image (continuous_const.sub continuous_id)
  have hF_closed : IsClosed F := hF_compact.isClosed


  obtain ⟨K', hK'_compact, hF_int_K'⟩ := exists_compact_superset hF_compact
  obtain ⟨ψ, hψ_smooth, hψ_compsupp, hψ_tsupp, V, hV_open, hF_sub_V, hψ_one⟩ :=
    exists_smooth_bump_subset F K' hF_closed hK'_compact hF_int_K'

  set f' := smulLeftCLM ℂ ψ f with hf'_def
  refine ⟨f', ?_, ?_, ?_⟩

  · exact hasCompactSupport_smulLeft_of_compactSupport_function ψ f hψ_compsupp

  · exact singularSupport_smulLeft_subset ψ f hψ_smooth

  · intro hsmooth_f'

    have hf_split : f = smulLeftCLM ℂ ψ f + smulLeftCLM ℂ (1 - ψ) f :=
      (smulLeft_add_complement ψ f (hψ_compsupp.hasTemperateGrowth hψ_smooth)).symm

    have hconv_split : distribConvolution μ f hμ =
        distribConvolution μ f' hμ + distribConvolution μ (smulLeftCLM ℂ (1 - ψ) f) hμ := by
      conv_lhs => rw [hf_split]
      exact distribConvolution_add_right μ f' (smulLeftCLM ℂ (1 - ψ) f) hμ

    rw [hconv_split]
    apply isSmoothNear_add _ _ p hsmooth_f'


    have h_tsupp : tsupport (1 - ψ) ⊆ Vᶜ :=
      tsupport_one_sub_subset_compl ψ V hV_open hψ_one
    have h_1mψf_supp : ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
        (Function.support (⇑φ) ∩ Vᶜ = ∅) → (smulLeftCLM ℂ (1 - ψ) f) φ = 0 :=
      smulLeft_supported (1 - ψ) f Vᶜ h_tsupp

    have h_vanish : vanishesOn (distribConvolution μ (smulLeftCLM ℂ (1 - ψ) f) hμ) (Kμ + Vᶜ)ᶜ :=
      distribConvolution_vanishesOn_compl μ (smulLeftCLM ℂ (1 - ψ) f) hμ
        Kμ Vᶜ hKμ_supp h_1mψf_supp


    have hp_notin : p ∉ Kμ + Vᶜ := by
      intro hmem
      rw [Set.mem_add] at hmem
      obtain ⟨a, ha, b, hb, hab⟩ := hmem
      have hap : p - a ∈ F := Set.mem_image_of_mem _ ha
      have hapV : p - a ∈ V := hF_sub_V hap
      have hbeq : b = p - a := by rw [← hab, add_sub_cancel_left]
      exact absurd (hbeq ▸ hapV) hb
    have h_open : IsOpen (Kμ + Vᶜ)ᶜ := by
      rw [isOpen_compl_iff]
      exact isClosed_compact_add_closed Kμ Vᶜ hKμ_compact
        hV_open.isClosed_compl
    exact isSmoothNear_of_vanishes_near _ p _ h_open hp_notin h_vanish

/-- Bilinear expansion `(μ₁ + μ₂) * (f₁ + f₂) = μ₁ * f₁ + μ₁ * f₂ + μ₂ * f₁ + μ₂ * f₂`
for distributional convolution, used in the singular-support proof. -/
theorem distribConvolution_four_term_expansion
    (μ₁ μ₂ f₁ f₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ₁ : HasCompactSupport μ₁)
    (hμ₂ : HasCompactSupport μ₂)
    (hμ : HasCompactSupport (μ₁ + μ₂)) :
    distribConvolution (μ₁ + μ₂) (f₁ + f₂) hμ =
    distribConvolution μ₁ f₁ hμ₁ + distribConvolution μ₁ f₂ hμ₁ +
    (distribConvolution μ₂ f₁ hμ₂ + distribConvolution μ₂ f₂ hμ₂) := by
  rw [distribConvolution_add_left μ₁ μ₂ (f₁ + f₂) hμ₁ hμ₂ hμ,
      distribConvolution_add_right μ₁ f₁ f₂ hμ₁,
      distribConvolution_add_right μ₂ f₁ f₂ hμ₂]

/-- Congruence: replacing the arguments of `distribConvolution` by equal distributions
gives equal results, independent of the chosen compact-support witness. -/
theorem distribConvolution_congr
    {a a' b b' : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    (ha_eq : a = a') (hb_eq : b = b')
    (ha : HasCompactSupport a) (ha' : HasCompactSupport a') :
    distribConvolution a b ha = distribConvolution a' b' ha' := by
  subst ha_eq; subst hb_eq; rfl

/-- The singular support of a distributional convolution is contained in the Minkowski
sum of the singular supports of the factors: `singsupp (μ * f) ⊆ singsupp μ + singsupp f`.
This is the central property underlying pseudodifferential calculus (Melrose,
Section 12). -/
theorem singularSupport_convolution_subset
    (μ f : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hμ : HasCompactSupport μ) :
    singularSupport (distribConvolution μ f hμ) ⊆
      singularSupport μ + singularSupport f := by
  intro p hp
  by_contra h_not_mem
  apply hp

  obtain ⟨f', hf'_compact, hf'_ss, hf'_impl⟩ :=
    distribConvolution_reduce_to_compact_support μ f hμ p h_not_mem
  apply hf'_impl

  have h_not_mem' : p ∉ singularSupport μ + singularSupport f' :=
    fun hmem => h_not_mem (Set.add_subset_add_left hf'_ss hmem)

  obtain ⟨K₁, K₂, hK₁c, hK₂c, hK₁s, hK₂s, hp_notin⟩ :=
    exists_compact_neighborhood_disjoint_sum
      (singularSupport μ) (singularSupport f')
      (singularSupport_compact_of_compactSupport μ hμ)
      (singularSupport_compact_of_compactSupport f' hf'_compact)
      p h_not_mem'

  obtain ⟨dμ, hdμ_sub⟩ := exists_smoothDecomp μ hμ K₁ hK₁c hK₁s
  obtain ⟨df, hdf_sub⟩ := exists_smoothDecomp f' hf'_compact K₂ hK₂c hK₂s

  have h_p_notin_supp : p ∉ dμ.supportSet + df.supportSet :=
    fun h => hp_notin (Set.add_subset_add hdμ_sub hdf_sub h)

  have h_term1 : isSmoothNear (distribConvolution dμ.singular df.singular
      dμ.singular_compactSupport) p :=
    isSmoothNear_of_vanishes_near _ p (dμ.supportSet + df.supportSet)ᶜ
      (by rw [isOpen_compl_iff]; exact isClosed_compact_add_closed dμ.supportSet df.supportSet dμ.supportSet_compact df.supportSet_compact.isClosed)
      h_p_notin_supp
      (distribConvolution_vanishesOn_compl dμ.singular df.singular
        dμ.singular_compactSupport dμ.supportSet df.supportSet
        dμ.singular_supported df.singular_supported)

  have h_term2 : isSmoothNear (distribConvolution dμ.singular df.smooth
      dμ.singular_compactSupport) p :=
    isSmoothNear_distribConvolution_of_smooth_right _ _ _ df.smooth_isSmooth p

  have h_term3 : isSmoothNear (distribConvolution dμ.smooth df.singular
      dμ.smooth_compactSupport) p :=
    isSmoothNear_distribConvolution_of_smooth_left _ _ _ dμ.smooth_isSmooth p

  have h_term4 : isSmoothNear (distribConvolution dμ.smooth df.smooth
      dμ.smooth_compactSupport) p :=
    isSmoothNear_distribConvolution_of_smooth_left _ _ _ dμ.smooth_isSmooth p

  have hμ_sum : HasCompactSupport (dμ.singular + dμ.smooth) :=
    dμ.sum_eq ▸ hμ
  have h_expand := distribConvolution_four_term_expansion dμ.singular dμ.smooth
    df.singular df.smooth dμ.singular_compactSupport dμ.smooth_compactSupport hμ_sum
  have h_four_smooth : isSmoothNear (
      distribConvolution dμ.singular df.singular dμ.singular_compactSupport +
      distribConvolution dμ.singular df.smooth dμ.singular_compactSupport +
      (distribConvolution dμ.smooth df.singular dμ.smooth_compactSupport +
       distribConvolution dμ.smooth df.smooth dμ.smooth_compactSupport)) p :=
    isSmoothNear_add _ _ p
      (isSmoothNear_add _ _ p h_term1 h_term2)
      (isSmoothNear_add _ _ p h_term3 h_term4)


  have h_conv_eq : distribConvolution μ f' hμ =
      distribConvolution (dμ.singular + dμ.smooth) (df.singular + df.smooth) hμ_sum :=
    distribConvolution_congr dμ.sum_eq df.sum_eq hμ hμ_sum
  rw [h_conv_eq, h_expand]
  exact h_four_smooth

end DifferentialOperators
