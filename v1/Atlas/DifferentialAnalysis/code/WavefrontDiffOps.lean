/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.WavefrontSet
import Atlas.DifferentialAnalysis.code.ConeSupportCorollary
import Atlas.DifferentialAnalysis.code.WavefrontCharacterization

noncomputable section

open scoped SchwartzMap FourierTransform
open MeasureTheory ConeSupport

namespace WavefrontDiffOps

variable {n : ℕ}


/-- If a tempered distribution `u` is smooth near a point `x`, then the pair `(x, ω)` is not in
the wavefront set of `u` for any direction `ω`. -/
theorem not_mem_wavefrontSet_of_isSmoothNear
    {n : ℕ} (u : 𝓢'(E n, ℂ)) (x : E n) (ω : Sphere n)
    (hsmooth : IsSmoothNear u x) :
    (x, ω) ∉ wavefrontSet u := by

  obtain ⟨φ, hφ_smooth, hφ_compact, hφx, f, hf⟩ := hsmooth


  intro hmem

  apply hmem
  refine ⟨φ, hφ_smooth, hφ_compact, hφx, ?_⟩


  rw [hf, TemperedDistribution.fourier_toTemperedDistributionCLM_eq]


  rw [schwartz_conicSingularSupportSphere_empty]
  simp


/-- The singular support of the Fourier transform of a compactly cut-off tempered distribution
`φ · u` is empty: the result is smooth everywhere. -/
theorem singularSupport_fourier_compactCutoff_empty
    {n : ℕ} (u : 𝓢'(E n, ℂ))
    (φ : E n → ℂ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ) :
    singularSupport (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ u)) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  simp only [singularSupport, Set.mem_setOf_eq] at hx
  apply hx


  obtain ⟨f, hf⟩ := fourier_smulLeftCLM_eq_schwartzConvolution φ hφ hφc u
  rw [hf]
  exact isSmoothNear_schwartzConvolution (𝓕 u) f x

/-- If the conic singular support sphere of `𝓕(φ · u)` is empty and `φ` is a smooth compactly
supported cutoff, then `φ · u` is itself a Schwartz function. -/
theorem cssSphere_empty_compactCutoff_isSchwartz
    {n : ℕ} (u : 𝓢'(E n, ℂ))
    (φ : E n → ℂ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hcss : ConicSingularSupportSphere
      (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ u)) = ∅) :
    ∃ (f : SchwartzMap (E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ φ u = (f : 𝓢'(E n, ℂ)) := by


  have hss : singularSupport (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ u)) = ∅ :=
    singularSupport_fourier_compactCutoff_empty u φ hφ hφc
  have hcss_full : coneSingularSupport (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ u)) = ∅ := by
    simp only [coneSingularSupport, hss, hcss, Set.image_empty, Set.empty_union]

  obtain ⟨g, hg⟩ := (coneSingularSupport_eq_empty_iff _).mp hcss_full


  refine ⟨𝓕⁻ g, ?_⟩
  have h1 : 𝓕⁻ (schwEmbed g : 𝓢'(E n, ℂ)) = schwEmbed (𝓕⁻ g) := by
    change 𝓕⁻ ((g : 𝓢'(E n, ℂ))) = ((𝓕⁻ g : 𝓢(E n, ℂ)) : 𝓢'(E n, ℂ))
    exact TemperedDistribution.fourierInv_toTemperedDistributionCLM_eq g
  have h2 : 𝓕⁻ (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ u)) =
      TemperedDistribution.smulLeftCLM ℂ φ u :=
    FourierTransform.fourierInv_fourier_eq _
  rw [← h1, hg, h2]

/-- For any open set `U` and point `x ∈ U`, there exists a smooth compactly supported complex
bump function `φ` with `φ x ≠ 0` and `tsupport φ ⊆ U`. -/
theorem exists_smooth_compactly_supported_in_open
    {n : ℕ} (U : Set (E n)) (hU : IsOpen U) (x : E n) (hx : x ∈ U) :
    ∃ (φ : E n → ℂ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧ φ x ≠ 0 ∧
      tsupport φ ⊆ U := by
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hU x hx
  have hr3 : (0 : ℝ) < r / 3 := by linarith
  have hr2 : r / 3 < r / 2 := by linarith
  set b : ContDiffBump x := ⟨r/3, r/2, hr3, hr2⟩
  refine ⟨fun y => Complex.ofReal (b y), ?_, ?_, ?_, ?_⟩
  · rw [contDiff_infty]; intro k
    exact Complex.ofRealCLM.contDiff.comp b.contDiff
  · exact b.hasCompactSupport.comp_left Complex.ofReal_zero
  · simp only [Complex.ofReal_ne_zero]
    have h := b.one_of_mem_closedBall (Metric.mem_closedBall_self (le_of_lt hr3))
    linarith
  · calc tsupport (fun y => (Complex.ofReal (b y) : ℂ))
        ⊆ tsupport b.toFun := tsupport_comp_subset Complex.ofReal_zero _
      _ = Metric.closedBall x (r/2) := b.tsupport_eq
      _ ⊆ Metric.ball x r := Metric.closedBall_subset_ball (by linarith)
      _ ⊆ U := hr_sub

/-- Converse to `not_mem_wavefrontSet_of_isSmoothNear`: if no direction `(x, ω)` belongs to the
wavefront set of `u`, then `u` is smooth near `x`. Uses compactness of the sphere of directions. -/
theorem isSmoothNear_of_forall_not_mem_wavefrontSet
    {n : ℕ} (u : 𝓢'(E n, ℂ)) (x : E n)
    (h : ∀ ω : Sphere n, (x, ω) ∉ wavefrontSet u) :
    IsSmoothNear u x := by


  have h' : ∀ ω : Sphere n, ∃ (φ : E n → ℂ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ ∧ φ x ≠ 0 ∧
      ω ∉ ConicSingularSupportSphere (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ u)) := by
    intro ω
    have hω := h ω
    simp only [wavefrontSet, Set.mem_setOf_eq, not_not] at hω
    exact hω


  choose φ_ω hφ_smooth hφ_compact hφ_ne hω_notin using h'


  set V : Sphere n → Set (Sphere n) :=
    fun ω => (ConicSingularSupportSphere
      (𝓕 (TemperedDistribution.smulLeftCLM ℂ (φ_ω ω) u)))ᶜ with hV_def
  have hV_open : ∀ ω, IsOpen (V ω) := by
    intro ω
    exact (cssSphere_isClosed _).isOpen_compl
  have hV_mem : ∀ ω, ω ∈ V ω := fun ω => hω_notin ω
  have hV_cover : ∀ ω : Sphere n, ∃ ω₀ : Sphere n, ω ∈ V ω₀ := fun ω => ⟨ω, hV_mem ω⟩


  have hcompact : IsCompact (Set.univ : Set (Sphere n)) := isCompact_univ
  have hcover : Set.univ ⊆ ⋃ ω : Sphere n, V ω := by
    intro ω _
    exact Set.mem_iUnion.mpr (hV_cover ω)
  obtain ⟨S, hS_cover⟩ :=
    hcompact.elim_finite_subcover (fun ω => V ω) (fun ω => hV_open ω) hcover


  have hsupp_open : ∀ ω : Sphere n, IsOpen (Function.support (φ_ω ω)) :=
    fun ω => (hφ_smooth ω).continuous.isOpen_support
  have hx_in_supp : ∀ ω : Sphere n, x ∈ Function.support (φ_ω ω) :=
    fun ω => Function.mem_support.mpr (hφ_ne ω)

  set U := ⋂ ω ∈ S, Function.support (φ_ω ω) with hU_def
  have hU_open : IsOpen U := isOpen_biInter_finset fun ω _ => hsupp_open ω
  have hx_in_U : x ∈ U := Set.mem_iInter₂.mpr fun ω _ => hx_in_supp ω

  obtain ⟨φ, hφ_sm, hφ_cs, hφ_ne_x, hφ_supp⟩ :=
    exists_smooth_compactly_supported_in_open U hU_open x hx_in_U

  have hmono : ∀ ω ∈ S,
      ConicSingularSupportSphere (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ u)) ⊆
      ConicSingularSupportSphere (𝓕 (TemperedDistribution.smulLeftCLM ℂ (φ_ω ω) u)) := by
    intro ω hωS
    apply cssSphere_mono_compact_cutoff u (φ_ω ω) φ (hφ_smooth ω) (hφ_compact ω) hφ_sm hφ_cs
    intro y hy
    exact (Set.mem_iInter₂.mp (hφ_supp hy)) ω hωS

  have hcss_empty : ConicSingularSupportSphere
      (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ u)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro ω hω_mem

    have hω_univ : (ω : Sphere n) ∈ Set.univ := Set.mem_univ ω
    have hω_in_cover := hS_cover hω_univ
    rw [Set.mem_iUnion₂] at hω_in_cover
    obtain ⟨j, hjS, hj⟩ := hω_in_cover

    have hω_notin_j : ω ∉ ConicSingularSupportSphere
        (𝓕 (TemperedDistribution.smulLeftCLM ℂ (φ_ω j) u)) := hj

    exact hω_notin_j (hmono j hjS hω_mem)

  obtain ⟨f, hf⟩ := cssSphere_empty_compactCutoff_isSchwartz u φ hφ_sm hφ_cs hcss_empty
  exact ⟨φ, hφ_sm, hφ_cs, hφ_ne_x, f, hf⟩

/-- The projection to the base of the wavefront set is contained in the singular support. -/
theorem wavefrontSet_proj_fst_subset_singularSupport
    (u : 𝓢'(E n, ℂ)) :
    Prod.fst '' wavefrontSet u ⊆ singularSupport u := by
  intro x ⟨⟨_, ω⟩, hxω_mem, rfl⟩
  intro hsmooth
  exact not_mem_wavefrontSet_of_isSmoothNear u x ω hsmooth hxω_mem

/-- The singular support is contained in the projection to the base of the wavefront set. -/
theorem singularSupport_subset_wavefrontSet_proj_fst
    (u : 𝓢'(E n, ℂ)) :
    singularSupport u ⊆ Prod.fst '' wavefrontSet u := by
  intro x hx
  by_contra habs
  apply hx
  apply isSmoothNear_of_forall_not_mem_wavefrontSet u x
  intro ω hxω_mem
  apply habs
  exact ⟨(x, ω), hxω_mem, rfl⟩

/-- The projection to the base of the wavefront set equals the singular support. -/
theorem wavefrontSet_proj_fst_eq_singularSupport
    (u : 𝓢'(E n, ℂ)) :
    Prod.fst '' wavefrontSet u = singularSupport u :=
  Set.Subset.antisymm
    (wavefrontSet_proj_fst_subset_singularSupport u)
    (singularSupport_subset_wavefrontSet_proj_fst u)

/-- The "boundary" subset of pairs `(p, q)` where at least one of the components corresponds to
a direction at infinity (an `Sum.inr` of `Sphere n`). -/
def boundaryOfProd : Set ((E n ⊕ Sphere n) × (E n ⊕ Sphere n)) :=
  {p | (∃ ω : Sphere n, p.1 = Sum.inr ω) ∨ (∃ ω : Sphere n, p.2 = Sum.inr ω)}

/-- The scattering wavefront set is always contained in the boundary subset `boundaryOfProd`. -/
theorem scatteringWavefrontSet_subset_boundary
    (u : 𝓢'(E n, ℂ)) :
    scatteringWavefrontSet u ⊆ boundaryOfProd := by
  intro p hp
  simp only [scatteringWavefrontSet, Set.mem_union, Set.mem_image] at hp
  rcases hp with ⟨⟨x, ω⟩, _, rfl⟩ | ⟨⟨ω, q⟩, _, rfl⟩
  · right
    exact ⟨ω, rfl⟩
  · left
    exact ⟨ω, rfl⟩

/-- The wavefront set of a tempered distribution is a closed subset of `E n × Sphere n`. -/
theorem wavefrontSet_isClosed
    {n : ℕ} (u : 𝓢'(E n, ℂ)) :
    IsClosed (wavefrontSet u) := by
  rw [← isOpen_compl_iff]
  rw [isOpen_iff_forall_mem_open]
  intro ⟨x₀, ω₀⟩ h₀
  simp only [Set.mem_compl_iff] at h₀

  simp only [wavefrontSet, Set.mem_setOf_eq, not_not] at h₀
  obtain ⟨φ₀, hφ₀_smooth, hφ₀_compact, hφ₀x₀, hω₀_notin⟩ := h₀

  refine ⟨(Function.support φ₀) ×ˢ
    (ConicSingularSupportSphere (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ₀ u)))ᶜ,
    ?_, ?_, ?_⟩

  · intro ⟨x', ω'⟩ hx'ω'
    simp only [Set.mem_prod, Function.mem_support, Set.mem_compl_iff] at hx'ω'
    rw [Set.mem_compl_iff]
    simp only [wavefrontSet, Set.mem_setOf_eq, not_not]
    exact ⟨φ₀, hφ₀_smooth, hφ₀_compact, hx'ω'.1, hx'ω'.2⟩

  · exact IsOpen.prod (contDiff_isOpen_support φ₀ hφ₀_smooth)
      (cssSphere_isClosed _).isOpen_compl

  · exact Set.mk_mem_prod (Function.mem_support.mpr hφ₀x₀) hω₀_notin

/-- The singular support of a tempered distribution is closed in `E n`. -/
theorem singularSupport_isClosed {n : ℕ} (u : 𝓢'(E n, ℂ)) :
    IsClosed (singularSupport u) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x₀ h₀
  simp only [Set.mem_compl_iff, singularSupport, Set.mem_setOf_eq, not_not] at h₀
  obtain ⟨φ₀, hφ₀_smooth, hφ₀_compact, hφ₀x₀, f₀, hf₀⟩ := h₀
  refine ⟨Function.support φ₀, ?_, contDiff_isOpen_support φ₀ hφ₀_smooth,
    Function.mem_support.mpr hφ₀x₀⟩
  intro x hx
  simp only [Set.mem_compl_iff, singularSupport, Set.mem_setOf_eq, not_not]
  exact ⟨φ₀, hφ₀_smooth, hφ₀_compact, Function.mem_support.mp hx, f₀, hf₀⟩

/-- The cone singular support of a tempered distribution is closed in `E n ⊕ Sphere n`. -/
theorem coneSingularSupport_isClosed {n : ℕ} (u : 𝓢'(E n, ℂ)) :
    IsClosed (coneSingularSupport u) := by
  simp only [coneSingularSupport]
  apply IsClosed.union
  · exact Topology.IsClosedEmbedding.inl.isClosedMap _ (singularSupport_isClosed u)
  · exact Topology.IsClosedEmbedding.inr.isClosedMap _ (cssSphere_isClosed u)

/-- The set of sphere directions `ω` for which `g` is a conic cutoff near `ω` is open. -/
theorem isConicCutoffNear_isOpen {n : ℕ} (g : E n → ℂ) :
    IsOpen {ω : Sphere n | IsConicCutoffNear g ω} := by
  rw [isOpen_iff_forall_mem_open]
  intro ω₀ hω₀
  simp only [Set.mem_setOf_eq] at hω₀
  obtain ⟨hg_smooth, R, hR, hR_lt, R₀, hR₀, hsupp, ψ, hψ_hom, hψ_ne, hψ_eq⟩ := hω₀

  refine ⟨{σ : Sphere n | ψ (σ : E n) ≠ 0}, ?_, ?_, hψ_ne⟩
  · intro σ hσ
    simp only [Set.mem_setOf_eq] at hσ ⊢
    exact ⟨hg_smooth, R, hR, hR_lt, R₀, hR₀, hsupp, ψ, hψ_hom, hσ, hψ_eq⟩
  ·


    set t := R + 1 with ht_def
    have ht_pos : (0 : ℝ) < t := by linarith
    have ht : R < t := by linarith

    have sphere_norm : ∀ (σ : Sphere n), ‖(σ : E n)‖ = 1 := by
      intro σ
      have hσ := σ.2
      simp only [Metric.mem_sphere, dist_zero_right] at hσ
      exact hσ
    have sphere_ne_zero : ∀ (σ : Sphere n), (σ : E n) ≠ 0 := by
      intro σ h
      have := sphere_norm σ
      rw [h, norm_zero] at this
      linarith
    have sphere_smul_norm : ∀ (σ : Sphere n), R < ‖t • (σ : E n)‖ := by
      intro σ
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht_pos, sphere_norm, mul_one]
      exact ht

    have key : ∀ (σ : Sphere n), ψ (σ : E n) = g (t • (σ : E n)) := by
      intro σ
      rw [← hψ_hom t ht_pos _ (sphere_ne_zero σ), hψ_eq _ (sphere_smul_norm σ)]

    have : {σ : Sphere n | ψ (σ : E n) ≠ 0} =
        (fun σ : Sphere n => g (t • (σ : E n))) ⁻¹' {0}ᶜ := by
      ext σ; simp [key]
    rw [this]
    exact (isClosed_singleton (X := ℂ)).isOpen_compl.preimage
      (hg_smooth.continuous.comp (continuous_const_smul t |>.comp continuous_subtype_val))

/-- The scattering wavefront set at infinity is a closed subset of `Sphere n × (E n ⊕ Sphere n)`. -/
theorem scatteringWavefrontSetAtInfinity_isClosed
    {n : ℕ} (u : 𝓢'(E n, ℂ)) :
    IsClosed (scatteringWavefrontSetAtInfinity u) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro ⟨ω₀, q₀⟩ h₀
  simp only [Set.mem_compl_iff, scatteringWavefrontSetAtInfinity, Set.mem_setOf_eq, not_not] at h₀
  obtain ⟨g₀, hg₀_conic, hq₀_notin⟩ := h₀
  refine ⟨{σ : Sphere n | IsConicCutoffNear g₀ σ} ×ˢ
    (coneSingularSupport (𝓕 (TemperedDistribution.smulLeftCLM ℂ g₀ u)))ᶜ, ?_, ?_, ?_⟩
  · intro ⟨σ, q⟩ hσq
    simp only [Set.mem_prod, Set.mem_setOf_eq, Set.mem_compl_iff] at hσq
    rw [Set.mem_compl_iff]
    simp only [scatteringWavefrontSetAtInfinity, Set.mem_setOf_eq, not_not]
    exact ⟨g₀, hσq.1, hσq.2⟩
  · exact IsOpen.prod (isConicCutoffNear_isOpen g₀) (coneSingularSupport_isClosed _).isOpen_compl
  · exact Set.mk_mem_prod hg₀_conic hq₀_notin

/-- The full scattering wavefront set (union of finite-part and at-infinity components) is closed. -/
theorem scatteringWavefrontSet_isClosed
    {n : ℕ} (u : 𝓢'(E n, ℂ)) :
    IsClosed (scatteringWavefrontSet u) := by
  simp only [scatteringWavefrontSet]
  apply IsClosed.union
  ·
    have hemb : Topology.IsClosedEmbedding
        (Prod.map (Sum.inl : E n → E n ⊕ Sphere n) (Sum.inr : Sphere n → E n ⊕ Sphere n)) := by
      constructor
      · exact Topology.IsEmbedding.prodMap
          Topology.IsClosedEmbedding.inl.isEmbedding
          Topology.IsClosedEmbedding.inr.isEmbedding
      · rw [Set.range_prodMap]
        exact isClosed_range_inl.prod isClosed_range_inr
    exact hemb.isClosedMap _ (wavefrontSet_isClosed u)
  ·
    have hemb : Topology.IsClosedEmbedding
        (Prod.map (Sum.inr : Sphere n → E n ⊕ Sphere n)
          (id : E n ⊕ Sphere n → E n ⊕ Sphere n)) := by
      constructor
      · exact Topology.IsEmbedding.prodMap
          Topology.IsClosedEmbedding.inr.isEmbedding
          Topology.IsClosedEmbedding.id.isEmbedding
      · rw [Set.range_prodMap]
        simp only [Set.range_id]
        exact isClosed_range_inr.prod isClosed_univ
    exact hemb.isClosedMap _ (scatteringWavefrontSetAtInfinity_isClosed u)


/-- If the first projection `p` is outside the cone singular support, then no pair `(p, q)`
belongs to the scattering wavefront set. -/
theorem not_mem_scatteringWavefrontSet_of_not_mem_coneSingularSupport
    {n : ℕ} (u : 𝓢'(E n, ℂ)) (p : E n ⊕ Sphere n) (q : E n ⊕ Sphere n)
    (hp : p ∉ coneSingularSupport u) :
    (p, q) ∉ scatteringWavefrontSet u := by


  intro hmem
  simp only [scatteringWavefrontSet, Set.mem_union, Set.mem_image] at hmem
  rcases p with x | ω
  ·


    have hx_smooth : IsSmoothNear u x := by
      by_contra h_not_smooth
      apply hp
      exact Set.mem_union_left _ (Set.mem_image_of_mem Sum.inl h_not_smooth)
    rcases hmem with ⟨⟨x', ω'⟩, hxω, hprod⟩ | ⟨⟨ω', q'⟩, _, hprod⟩
    ·
      have hx_eq : x' = x := Sum.inl_injective (Prod.mk.inj hprod).1
      subst hx_eq
      exact not_mem_wavefrontSet_of_isSmoothNear u x' ω' hx_smooth hxω
    ·

      exact absurd (Prod.mk.inj hprod).1 Sum.inr_ne_inl
  ·


    have hω_not_css : ω ∉ ConicSingularSupportSphere u := by
      intro hω_css
      apply hp
      exact Set.mem_union_right _ (Set.mem_image_of_mem Sum.inr hω_css)

    simp only [ConicSingularSupportSphere, Set.mem_setOf_eq, not_not] at hω_not_css
    obtain ⟨g, hg_conic, f, hf⟩ := hω_not_css
    rcases hmem with ⟨⟨x', ω'⟩, _, hprod⟩ | ⟨⟨ω', q'⟩, hωq, hprod⟩
    ·

      exact absurd (Prod.mk.inj hprod).1 Sum.inl_ne_inr
    ·
      have hω_eq : ω' = ω := Sum.inr_injective (Prod.mk.inj hprod).1
      have hq_eq : q' = q := (Prod.mk.inj hprod).2
      subst hω_eq; subst hq_eq


      apply hωq
      refine ⟨g, hg_conic, ?_⟩


      rw [hf, TemperedDistribution.fourier_toTemperedDistributionCLM_eq]
      simp only [coneSingularSupport, schwartz_singularSupport_empty,
        schwartz_conicSingularSupportSphere_empty, Set.image_empty, Set.empty_union]
      exact Set.notMem_empty q'


/-- If `g` is a conic cutoff near `ω`, then the singular support of `𝓕(g · u)` is empty: it is
smooth everywhere as the Fourier transform of a conically localized distribution. -/
theorem singularSupport_fourier_conicCutoff_smul_empty
    {n : ℕ} (u : 𝓢'(E n, ℂ))
    (g : E n → ℂ) (ω : Sphere n) (hg : IsConicCutoffNear g ω) :
    singularSupport (𝓕 (TemperedDistribution.smulLeftCLM ℂ g u)) = ∅ := by


  obtain ⟨f, hf⟩ := fourier_conic_cutoff_eq_schwartz_convolution u g g ω hg hg (le_refl _)

  rw [hf]
  exact singularSupport_schwartzConvolution_eq_empty _ f


/-- A tempered distribution is itself given by a Schwartz function whenever its Fourier transform
is. -/
theorem isSchwartz_of_fourier_isSchwartz
    {n : ℕ} (v : 𝓢'(E n, ℂ))
    (hv : ∃ (f : SchwartzMap (E n) ℂ), 𝓕 v = (f : 𝓢'(E n, ℂ))) :
    ∃ (f : SchwartzMap (E n) ℂ),
      v = (f : 𝓢'(E n, ℂ)) := by
  obtain ⟨f, hf⟩ := hv
  refine ⟨𝓕⁻ f, ?_⟩
  have h1 : 𝓕⁻ (f : 𝓢'(E n, ℂ)) = ((𝓕⁻ f : 𝓢(E n, ℂ)) : 𝓢'(E n, ℂ)) :=
    TemperedDistribution.fourierInv_toTemperedDistributionCLM_eq f
  have h2 : 𝓕⁻ (𝓕 v) = v := FourierTransform.fourierInv_fourier_eq _
  rw [← h2, hf, h1]


/-- If `g` is a conic cutoff near `ω` and the conic singular support sphere of `𝓕(g · u)` is
empty, then `g · u` is given by a Schwartz function. -/
theorem cssSphere_empty_conicCutoff_isSchwartz
    {n : ℕ} (u : 𝓢'(E n, ℂ))
    (g : E n → ℂ) (ω : Sphere n) (hg : IsConicCutoffNear g ω)
    (hcss : ConicSingularSupportSphere
      (𝓕 (TemperedDistribution.smulLeftCLM ℂ g u)) = ∅) :
    ∃ (f : SchwartzMap (E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ g u = (f : 𝓢'(E n, ℂ)) := by

  have hsing := singularSupport_fourier_conicCutoff_smul_empty u g ω hg

  have hcone : coneSingularSupport (𝓕 (TemperedDistribution.smulLeftCLM ℂ g u)) = ∅ := by
    simp only [coneSingularSupport, hsing, hcss, Set.image_empty, Set.empty_union]

  obtain ⟨f₁, hf₁⟩ := (coneSingularSupport_eq_empty_iff _).mp hcone

  exact isSchwartz_of_fourier_isSchwartz
    (TemperedDistribution.smulLeftCLM ℂ g u) ⟨f₁, hf₁ ▸ rfl⟩


/-- For any direction `ω` and open neighbourhood `U` of `ω`, there exists a function `g` that is
a conic cutoff near `ω` whose support is contained in `U`. -/
theorem exists_conic_cutoff_near_in_open
    {n : ℕ} (ω : Sphere n) (U : Set (E n)) (hU : IsOpen U) (hω : (ω : E n) ∈ U) :
    ∃ (g : E n → ℂ),
      IsConicCutoffNear g ω ∧ Function.support g ⊆ U := by sorry


/-- Converse direction for the cone singular support: if no second component `q` makes `(p, q)`
land in the scattering wavefront set, then `p` is outside the cone singular support. -/
theorem not_mem_coneSingularSupport_of_forall_not_mem_scatteringWavefrontSet
    {n : ℕ} (u : 𝓢'(E n, ℂ)) (p : E n ⊕ Sphere n)
    (h : ∀ q : E n ⊕ Sphere n, (p, q) ∉ scatteringWavefrontSet u) :
    p ∉ coneSingularSupport u := by


  rcases p with x | ω
  ·


    have hwf : ∀ ω' : Sphere n, (x, ω') ∉ wavefrontSet u := by
      intro ω' hxω

      have hq := h (Sum.inr ω')
      apply hq

      exact Set.mem_union_left _ ⟨(x, ω'), hxω, rfl⟩

    have hsmooth := isSmoothNear_of_forall_not_mem_wavefrontSet u x hwf

    intro hmem
    simp only [coneSingularSupport, Set.mem_union, Set.mem_image] at hmem
    rcases hmem with ⟨y, hy, hxy⟩ | ⟨σ, _, hσ⟩
    · have : y = x := Sum.inl_injective hxy
      subst this
      exact hy hsmooth
    · exact absurd hσ Sum.inr_ne_inl
  ·


    have hwf_inf : ∀ q, (ω, q) ∉ scatteringWavefrontSetAtInfinity u := by
      intro q hωq
      exact h q (Set.mem_union_right _ ⟨(ω, q), hωq, rfl⟩)


    have h' : ∀ σ : Sphere n, ∃ (g : E n → ℂ),
        IsConicCutoffNear g ω ∧
        σ ∉ ConicSingularSupportSphere
          (𝓕 (TemperedDistribution.smulLeftCLM ℂ g u)) := by
      intro σ
      have hσ := hwf_inf (Sum.inr σ)
      simp only [scatteringWavefrontSetAtInfinity, Set.mem_setOf_eq, not_not] at hσ
      obtain ⟨g, hg_conic, hσ_notin⟩ := hσ
      refine ⟨g, hg_conic, ?_⟩


      intro habs
      apply hσ_notin
      exact Set.mem_union_right _ (Set.mem_image_of_mem Sum.inr habs)

    choose g_σ hg_conic hσ_notin using h'
    set V : Sphere n → Set (Sphere n) :=
      fun σ => (ConicSingularSupportSphere
        (𝓕 (TemperedDistribution.smulLeftCLM ℂ (g_σ σ) u)))ᶜ with hV_def
    have hV_open : ∀ σ, IsOpen (V σ) := by
      intro σ
      exact (cssSphere_isClosed _).isOpen_compl
    have hV_mem : ∀ σ, σ ∈ V σ := fun σ => hσ_notin σ

    have hcompact : IsCompact (Set.univ : Set (Sphere n)) := isCompact_univ
    have hcover : Set.univ ⊆ ⋃ σ : Sphere n, V σ := by
      intro σ _
      exact Set.mem_iUnion.mpr ⟨σ, hV_mem σ⟩
    obtain ⟨S, hS_cover⟩ :=
      hcompact.elim_finite_subcover (fun σ => V σ) (fun σ => hV_open σ) hcover

    have hsupp_open : ∀ σ : Sphere n, IsOpen (Function.support (g_σ σ)) :=
      fun σ => conicCutoff_support_isOpen (g_σ σ) ω (hg_conic σ)
    have hω_in_supp : ∀ σ : Sphere n, (ω : E n) ∈ Function.support (g_σ σ) :=
      fun σ => conicCutoff_mem_support (g_σ σ) ω (hg_conic σ)
    set U := ⋂ σ ∈ S, Function.support (g_σ σ) with hU_def
    have hU_open : IsOpen U := isOpen_biInter_finset fun σ _ => hsupp_open σ
    have hω_in_U : (ω : E n) ∈ U := Set.mem_iInter₂.mpr fun σ _ => hω_in_supp σ

    obtain ⟨g, hg_conic', hg_supp⟩ :=
      exists_conic_cutoff_near_in_open ω U hU_open hω_in_U

    have hmono : ∀ σ ∈ S,
        ConicSingularSupportSphere (𝓕 (TemperedDistribution.smulLeftCLM ℂ g u)) ⊆
        ConicSingularSupportSphere (𝓕 (TemperedDistribution.smulLeftCLM ℂ (g_σ σ) u)) := by
      intro σ hσS
      apply cssSphere_mono_conic_cutoff u (g_σ σ) g ω (hg_conic σ) hg_conic'
      intro y hy
      exact (Set.mem_iInter₂.mp (hg_supp hy)) σ hσS

    have hcss_empty : ConicSingularSupportSphere
        (𝓕 (TemperedDistribution.smulLeftCLM ℂ g u)) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro σ hσ_mem
      have hσ_univ : (σ : Sphere n) ∈ Set.univ := Set.mem_univ σ
      have hσ_in_cover := hS_cover hσ_univ
      rw [Set.mem_iUnion₂] at hσ_in_cover
      obtain ⟨j, hjS, hj⟩ := hσ_in_cover
      exact hj (hmono j hjS hσ_mem)

    obtain ⟨f, hf⟩ := cssSphere_empty_conicCutoff_isSchwartz u g ω hg_conic' hcss_empty

    intro hmem
    simp only [coneSingularSupport, Set.mem_union, Set.mem_image] at hmem
    rcases hmem with ⟨y, _, hy⟩ | ⟨σ, hσ, hσ_eq⟩
    · exact absurd hy Sum.inl_ne_inr
    ·
      have hω_eq : σ = ω := Sum.inr_injective hσ_eq
      subst hω_eq

      exact hσ ⟨g, hg_conic', f, hf⟩

/-- The projection to the first factor of the scattering wavefront set is contained in the cone
singular support. -/
theorem scatteringWavefrontSet_proj_fst_subset_coneSingularSupport
    (u : 𝓢'(E n, ℂ)) :
    Prod.fst '' scatteringWavefrontSet u ⊆ coneSingularSupport u := by
  intro p ⟨⟨_, q⟩, hpq_mem, rfl⟩
  by_contra hp
  exact absurd hpq_mem
    (not_mem_scatteringWavefrontSet_of_not_mem_coneSingularSupport u p q hp)

/-- The cone singular support is contained in the projection to the first factor of the
scattering wavefront set. -/
theorem coneSingularSupport_subset_scatteringWavefrontSet_proj_fst
    (u : 𝓢'(E n, ℂ)) :
    coneSingularSupport u ⊆ Prod.fst '' scatteringWavefrontSet u := by
  intro p hp
  by_contra habs
  have : p ∉ coneSingularSupport u :=
    not_mem_coneSingularSupport_of_forall_not_mem_scatteringWavefrontSet u p
      (fun q hpq_mem => habs ⟨(p, q), hpq_mem, rfl⟩)
  exact this hp

/-- The projection to the first factor of the scattering wavefront set equals the cone
singular support. -/
theorem scatteringWavefrontSet_proj_fst_eq_coneSingularSupport
    (u : 𝓢'(E n, ℂ)) :
    Prod.fst '' scatteringWavefrontSet u = coneSingularSupport u :=
  Set.Subset.antisymm
    (scatteringWavefrontSet_proj_fst_subset_coneSingularSupport u)
    (coneSingularSupport_subset_scatteringWavefrontSet_proj_fst u)

/-- Melrose Proposition 12.14: the scattering wavefront set lies in the boundary, both wavefront
sets are closed, and the projections to the first factor recover the singular support and the
cone singular support respectively. -/
theorem prop_12_14 (u : 𝓢'(E n, ℂ)) :

    scatteringWavefrontSet u ⊆ boundaryOfProd ∧

    IsClosed (wavefrontSet u) ∧
    IsClosed (scatteringWavefrontSet u) ∧

    Prod.fst '' wavefrontSet u = singularSupport u ∧

    Prod.fst '' scatteringWavefrontSet u = coneSingularSupport u :=
  ⟨scatteringWavefrontSet_subset_boundary u,
   wavefrontSet_isClosed u,
   scatteringWavefrontSet_isClosed u,
   wavefrontSet_proj_fst_eq_singularSupport u,
   scatteringWavefrontSet_proj_fst_eq_coneSingularSupport u⟩

end WavefrontDiffOps

end
