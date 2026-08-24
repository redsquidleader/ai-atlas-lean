/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.WavefrontSet
import Atlas.DifferentialAnalysis.code.ConeSupportCorollary
import Atlas.DifferentialAnalysis.code.PseudoDiffOps
import Atlas.DifferentialAnalysis.code.WavefrontCharacterization
import Mathlib.Algebra.Group.Pointwise.Set.Basic

noncomputable section

open scoped SchwartzMap FourierTransform Pointwise
open MeasureTheory

namespace ConeSupport

variable {n : ℕ}

/-- Two tempered distributions `u`, `v` admit an extended convolution as soon as at least one of
them has empty conic singular support on the sphere; this is the side condition under which
the convolution `u * v` can be defined microlocally. -/
def HasExtendedConvolution (u v : 𝓢'(E n, ℂ)) : Prop :=
  ConicSingularSupportSphere u = ∅ ∨ ConicSingularSupportSphere v = ∅

/-- The extended convolution `u * v` defined under `HasExtendedConvolution u v` by splitting
the distribution with empty conic singular support into a Schwartz part and a compactly
supported part. -/
def extConv (u v : 𝓢'(E n, ℂ)) (h : HasExtendedConvolution u v) : 𝓢'(E n, ℂ) :=
  if hu : ConicSingularSupportSphere u = ∅ then
    let hecs := hasEmptyConicSingularSupportSphere_of_eq_empty u hu
    let d := hecs.hasDecomp.some
    let cs := standardConvolutionSystem v
    cs.convSchwartz d.schwartzPart + cs.convCompact d.compactPart
  else
    let hv : ConicSingularSupportSphere v = ∅ := h.resolve_left hu
    let hecs := hasEmptyConicSingularSupportSphere_of_eq_empty v hv
    let d := hecs.hasDecomp.some
    let cs := standardConvolutionSystem u
    cs.convSchwartz d.schwartzPart + cs.convCompact d.compactPart


/-- Independence of the extended convolution on the Schwartz/compact decomposition: any choice
of `SchwartzCompactDecomp u` (under `ConicSingularSupportSphere u = ∅`) yields the same value
for `extConv u v h`. -/
theorem extConv_eq_of_decomp
    (u v : 𝓢'(E n, ℂ))
    (h : HasExtendedConvolution u v)
    (hu : ConicSingularSupportSphere u = ∅)
    (d : SchwartzCompactDecomp u) :
    extConv u v h =
      (standardConvolutionSystem v).convSchwartz d.schwartzPart +
      (standardConvolutionSystem v).convCompact d.compactPart := by


  unfold extConv
  rw [dif_pos hu]


  exact convolution_decomp_well_defined_of_css_empty hu _ d

/-- The product of two conic cutoff functions near a direction `ω` is again a conic cutoff
near `ω`: the smoothness, support, and conic-extension properties are preserved by
multiplication. -/
lemma IsConicCutoffNear.mul {ga gb : E n → ℂ} {ω : Sphere n}
    (ha : IsConicCutoffNear ga ω) (hb : IsConicCutoffNear gb ω) :
    IsConicCutoffNear (ga * gb) ω := by
  obtain ⟨hga_smooth, Ra, hRa, hRa_lt, R0a, hR0a, hsupp_a, ψa, hψa_hom, hψa_ne, hga_eq⟩ := ha
  obtain ⟨hgb_smooth, Rb, hRb, hRb_lt, R0b, hR0b, hsupp_b, ψb, hψb_hom, hψb_ne, hgb_eq⟩ := hb
  refine ⟨hga_smooth.mul hgb_smooth, max Ra Rb, lt_max_of_lt_left hRa,
         max_lt hRa_lt hRb_lt,
         max R0a R0b, lt_max_of_lt_left hR0a, ?_, ψa * ψb, ?_, ?_, ?_⟩
  ·
    intro x hx
    simp only [Set.mem_setOf_eq]
    have hx_ne : (ga * gb) x ≠ 0 := Function.mem_support.mp hx
    simp only [Pi.mul_apply] at hx_ne
    have hga_ne : ga x ≠ 0 := left_ne_zero_of_mul hx_ne
    have hgb_ne : gb x ≠ 0 := right_ne_zero_of_mul hx_ne
    have hRa_le := hsupp_a (Function.mem_support.mpr hga_ne)
    have hRb_le := hsupp_b (Function.mem_support.mpr hgb_ne)
    simp only [Set.mem_setOf_eq] at hRa_le hRb_le
    exact max_le hRa_le hRb_le
  ·
    intro c hc x hx
    simp [Pi.mul_apply, hψa_hom c hc x hx, hψb_hom c hc x hx]
  ·
    show ψa (ω : E n) * ψb (ω : E n) ≠ 0
    exact mul_ne_zero hψa_ne hψb_ne
  ·
    intro x hx
    simp only [Pi.mul_apply]
    have hRa' : Ra < ‖x‖ := lt_of_le_of_lt (le_max_left Ra Rb) hx
    have hRb' : Rb < ‖x‖ := lt_of_le_of_lt (le_max_right Ra Rb) hx
    rw [hga_eq x hRa', hgb_eq x hRb']

/-- Subadditivity of the conic singular support on the sphere under addition of distributions:
`ConicSingularSupportSphere (a + b) ⊆ ConicSingularSupportSphere a ∪ ConicSingularSupportSphere b`. -/
theorem ConicSingularSupportSphere_add_subset
    (a b : 𝓢'(E n, ℂ)) :
    ConicSingularSupportSphere (a + b) ⊆
      ConicSingularSupportSphere a ∪ ConicSingularSupportSphere b := by
  intro ω hω

  by_contra hω_not_union
  simp only [Set.mem_union, not_or] at hω_not_union
  obtain ⟨hω_not_a, hω_not_b⟩ := hω_not_union

  simp only [ConicSingularSupportSphere, Set.mem_setOf_eq, not_not] at hω_not_a hω_not_b
  obtain ⟨ga, hga_conic, fa, hfa⟩ := hω_not_a
  obtain ⟨gb, hgb_conic, fb, hfb⟩ := hω_not_b


  apply hω


  by_cases hga_temp : Function.HasTemperateGrowth ga
  · by_cases hgb_temp : Function.HasTemperateGrowth gb
    ·

      have hprod_conic := hga_conic.mul hgb_conic


      have hcomp_a : TemperedDistribution.smulLeftCLM ℂ (ga * gb) a =
          TemperedDistribution.smulLeftCLM ℂ gb (TemperedDistribution.smulLeftCLM ℂ ga a) :=
        (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hga_temp hgb_temp a).symm
      rw [hfa, smulLeftCLM_schwEmbed_eq gb fa] at hcomp_a


      have hcomm : (ga * gb : E n → ℂ) = gb * ga := mul_comm ga gb
      have hcomp_b : TemperedDistribution.smulLeftCLM ℂ (ga * gb) b =
          TemperedDistribution.smulLeftCLM ℂ ga (TemperedDistribution.smulLeftCLM ℂ gb b) := by
        rw [hcomm]
        exact (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hgb_temp hga_temp b).symm
      rw [hfb, smulLeftCLM_schwEmbed_eq ga fb] at hcomp_b


      have hlin := map_add (TemperedDistribution.smulLeftCLM ℂ (ga * gb)) a b
      rw [hcomp_a, hcomp_b, ← map_add schwEmbed] at hlin
      exact ⟨ga * gb, hprod_conic,
        SchwartzMap.smulLeftCLM ℂ gb fa + SchwartzMap.smulLeftCLM ℂ ga fb, hlin⟩
    ·

      have h0 : SchwartzMap.smulLeftCLM (𝕜 := ℂ) ℂ gb = 0 := by
        unfold SchwartzMap.smulLeftCLM; exact dif_neg hgb_temp
      exact ⟨gb, hgb_conic, 0, by
        ext φ
        simp [TemperedDistribution.smulLeftCLM_apply_apply, h0]⟩
  ·
    have h0 : SchwartzMap.smulLeftCLM (𝕜 := ℂ) ℂ ga = 0 := by
      unfold SchwartzMap.smulLeftCLM; exact dif_neg hga_temp
    exact ⟨ga, hga_conic, 0, by
      ext φ
      simp [TemperedDistribution.smulLeftCLM_apply_apply, h0]⟩


/-- Subadditivity of the singular support under addition of tempered distributions:
`sing supp (a + b) ⊆ sing supp a ∪ sing supp b`. -/
theorem singularSupport_add_subset
    (a b : 𝓢'(E n, ℂ)) :
    singularSupport (a + b) ⊆ singularSupport a ∪ singularSupport b := by

  intro x hx
  by_contra h_not_mem

  have ha_not : x ∉ singularSupport a :=
    fun h => h_not_mem (Set.mem_union_left _ h)
  have hb_not : x ∉ singularSupport b :=
    fun h => h_not_mem (Set.mem_union_right _ h)

  have ha : IsSmoothNear a x := by
    simp only [singularSupport, Set.mem_setOf_eq, not_not] at ha_not
    exact ha_not
  have hb : IsSmoothNear b x := by
    simp only [singularSupport, Set.mem_setOf_eq, not_not] at hb_not
    exact hb_not

  obtain ⟨φ_a, hφa_smooth, hφa_compact, hφa_ne, f_a, hf_a⟩ := ha
  obtain ⟨φ_b, hφb_smooth, hφb_compact, hφb_ne, f_b, hf_b⟩ := hb

  have hφa_temp : φ_a.HasTemperateGrowth := hφa_compact.hasTemperateGrowth hφa_smooth
  have hφb_temp : φ_b.HasTemperateGrowth := hφb_compact.hasTemperateGrowth hφb_smooth

  have hφ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ_a * φ_b) :=
    hφa_smooth.mul hφb_smooth
  have hφ_compact : HasCompactSupport (φ_a * φ_b) := hφa_compact.mul_right
  have hφ_ne : (φ_a * φ_b) x ≠ 0 := mul_ne_zero hφa_ne hφb_ne

  have ha_eq : TemperedDistribution.smulLeftCLM ℂ (φ_a * φ_b) a =
      TemperedDistribution.smulLeftCLM ℂ φ_b (TemperedDistribution.smulLeftCLM ℂ φ_a a) :=
    (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hφa_temp hφb_temp a).symm

  have ha_schwartz : TemperedDistribution.smulLeftCLM ℂ (φ_a * φ_b) a =
      schwEmbed (SchwartzMap.smulLeftCLM ℂ φ_b f_a) := by
    rw [ha_eq, hf_a, smulLeftCLM_schwEmbed_eq]

  have hb_eq : TemperedDistribution.smulLeftCLM ℂ (φ_b * φ_a) b =
      TemperedDistribution.smulLeftCLM ℂ φ_a (TemperedDistribution.smulLeftCLM ℂ φ_b b) :=
    (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hφb_temp hφa_temp b).symm
  have hb_schwartz : TemperedDistribution.smulLeftCLM ℂ (φ_a * φ_b) b =
      schwEmbed (SchwartzMap.smulLeftCLM ℂ φ_a f_b) := by
    rw [show φ_a * φ_b = φ_b * φ_a from mul_comm φ_a φ_b, hb_eq, hf_b, smulLeftCLM_schwEmbed_eq]

  have h_sum : TemperedDistribution.smulLeftCLM ℂ (φ_a * φ_b) (a + b) =
      schwEmbed (SchwartzMap.smulLeftCLM ℂ φ_b f_a + SchwartzMap.smulLeftCLM ℂ φ_a f_b) := by
    rw [map_add (TemperedDistribution.smulLeftCLM ℂ (φ_a * φ_b)) a b,
        ha_schwartz, hb_schwartz, map_add]

  have h_smooth : IsSmoothNear (a + b) x :=
    ⟨φ_a * φ_b, hφ_smooth, hφ_compact, hφ_ne,
     SchwartzMap.smulLeftCLM ℂ φ_b f_a + SchwartzMap.smulLeftCLM ℂ φ_a f_b, h_sum⟩

  exact absurd h_smooth (by rwa [singularSupport, Set.mem_setOf_eq] at hx)


/-- The singular support of `extConv u v h` is contained in the union of the singular supports
of the convolutions of `v` with the Schwartz and compact parts of `u`. -/
theorem singularSupport_extConv_decomp
    (u v : 𝓢'(E n, ℂ))
    (h : HasExtendedConvolution u v)
    (hu : ConicSingularSupportSphere u = ∅)
    (d : SchwartzCompactDecomp u) :
    singularSupport (extConv u v h) ⊆
      singularSupport ((standardConvolutionSystem v).convSchwartz d.schwartzPart) ∪
      singularSupport ((standardConvolutionSystem v).convCompact d.compactPart) := by
  rw [extConv_eq_of_decomp u v h hu d]
  exact singularSupport_add_subset _ _


/-- Multiplying the Schwartz convolution `v * φ` on the left by a smooth compactly supported
function `ψ` produces a tempered distribution which is again represented by a Schwartz function. -/
theorem smulLeft_schwartzConvolution_of_compactBump
    (v : 𝓢'(E n, ℂ)) (φ : 𝓢(E n, ℂ))
    (ψ : E n → ℂ)
    (hψ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ) :
    ∃ f : 𝓢(E n, ℂ),
      TemperedDistribution.smulLeftCLM ℂ ψ (schwartzConvolution v φ) = schwEmbed f :=
  smulLeftCLM_schwartzConvolution_eq_schwartz v φ ψ hψ_smooth hψ_compact

/-- The convolution of a tempered distribution with a Schwartz function is smooth at every
point: locally one can multiply by a compactly supported bump to obtain a Schwartz
representative. -/
theorem schwartzConvolution_isSmoothNear
    (v : 𝓢'(E n, ℂ)) (φ : 𝓢(E n, ℂ)) (x : E n) :
    IsSmoothNear (schwartzConvolution v φ) x := by

  have hx_nhds : (Set.univ : Set (E n)) ∈ nhds x := Filter.univ_mem
  obtain ⟨ψ₀, -, hψ₀_compact, hψ₀_smooth, -, hψ₀_x⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) hx_nhds
  let ψ : E n → ℂ := Complex.ofRealCLM ∘ ψ₀
  have hψ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ :=
    Complex.ofRealCLM.contDiff.comp hψ₀_smooth
  have hψ_compact : HasCompactSupport ψ := hψ₀_compact.comp_left (map_zero _)
  have hψ_x : ψ x ≠ 0 := by
    simp only [ψ, Function.comp, Complex.ofRealCLM_apply, Complex.ofReal_ne_zero, hψ₀_x]
    exact one_ne_zero

  obtain ⟨f, hf⟩ := smulLeft_schwartzConvolution_of_compactBump v φ ψ hψ_smooth hψ_compact
  exact ⟨ψ, hψ_smooth, hψ_compact, hψ_x, f, hf⟩

/-- Convolution of any tempered distribution with a Schwartz function has empty singular
support: it is smooth everywhere. -/
theorem singularSupport_convSchwartz_empty
    (v : 𝓢'(E n, ℂ))
    (φ : 𝓢(E n, ℂ)) :
    singularSupport ((standardConvolutionSystem v).convSchwartz φ) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  apply hx
  rw [standardConvolutionSystem_convSchwartz_eq]
  exact schwartzConvolution_isSmoothNear v φ x

/-- The two notions of "compactly supported distribution" used in the cone-support and
differential-operators namespaces coincide definitionally. -/
lemma isCompactlySupportedDistribution_iff_hasCompactSupport
    (w : 𝓢'(E n, ℂ)) :
    IsCompactlySupportedDistribution w ↔ DifferentialOperators.HasCompactSupport w :=
  Iff.rfl


/-- The convolution-system specialisation `convCompact v w` for a compactly supported `w`
coincides with the `DifferentialOperators.distribConvolution w v hw` construction. -/
theorem convCompact_eq_distribConvolution
    (v w : 𝓢'(E n, ℂ))
    (hw : DifferentialOperators.HasCompactSupport w) :
    (standardConvolutionSystem v).convCompact w =
      DifferentialOperators.distribConvolution w v hw := by sorry


/-- The `ConeSupport.singularSupport` and `DifferentialOperators.singularSupport`
definitions of the singular support of a tempered distribution agree. -/
theorem singularSupport_eq_of_namespaces
    (u : 𝓢'(E n, ℂ)) :
    ConeSupport.singularSupport u = DifferentialOperators.singularSupport u := by sorry

/-- Singular support of a convolution with a compactly supported distribution: the standard
microlocal inclusion `sing supp (v * w) ⊆ sing supp w + sing supp v`. -/
theorem singularSupport_convCompact_subset
    (v : 𝓢'(E n, ℂ))
    (w : 𝓢'(E n, ℂ))
    (hw : IsCompactlySupportedDistribution w) :
    singularSupport ((standardConvolutionSystem v).convCompact w) ⊆
      singularSupport w + singularSupport v := by

  have hw' : DifferentialOperators.HasCompactSupport w := hw

  simp only [singularSupport_eq_of_namespaces]

  rw [convCompact_eq_distribConvolution v w hw']

  exact DifferentialOperators.singularSupport_convolution_subset w v hw'


/-- Singular support of the compact part of a Schwartz/compact decomposition is contained in
the singular support of the original distribution. -/
theorem singularSupport_compactPart_subset
    (u : 𝓢'(E n, ℂ))
    (d : SchwartzCompactDecomp u) :
    singularSupport d.compactPart ⊆ singularSupport u := by
  intro x hx
  rw [singularSupport, Set.mem_setOf_eq] at hx ⊢
  intro hu_smooth
  apply hx
  obtain ⟨φ, hφ_smooth, hφ_compact, hφ_ne, f_u, hf_u⟩ := hu_smooth
  refine ⟨φ, hφ_smooth, hφ_compact, hφ_ne, ?_⟩
  have hg_eq : d.compactPart = u - schwEmbed d.schwartzPart :=
    eq_sub_of_add_eq' d.sum_eq.symm
  refine ⟨f_u - SchwartzMap.smulLeftCLM ℂ φ d.schwartzPart, ?_⟩
  rw [hg_eq, map_sub, hf_u, smulLeftCLM_schwEmbed_eq, map_sub]

/-- Singular support of the extended convolution: `sing supp (extConv u v h) ⊆
sing supp u + sing supp v`, the microlocal inclusion for the extended convolution. -/
theorem singularSupport_extConv_subset
    (u v : 𝓢'(E n, ℂ))
    (h : HasExtendedConvolution u v)
    (hu : ConicSingularSupportSphere u = ∅) :
    singularSupport (extConv u v h) ⊆ singularSupport u + singularSupport v := by

  have hdecomp := hasEmptyConicSingularSupportSphere_of_eq_empty u hu
  obtain ⟨d⟩ := hdecomp.hasDecomp

  have h_decomp := singularSupport_extConv_decomp u v h hu d

  have h_schwartz := singularSupport_convSchwartz_empty v d.schwartzPart

  have h_compact := singularSupport_convCompact_subset v d.compactPart
    d.compactPart_isCompactlySupported

  have h_compact_sub := singularSupport_compactPart_subset u d

  intro x hx
  have hx_union := h_decomp hx
  simp only [h_schwartz, Set.empty_union] at hx_union
  have hx_compact := h_compact hx_union
  exact Set.add_subset_add_right h_compact_sub hx_compact


/-- The conic singular support of `extConv u v h` is contained in the union of the conic
singular supports of the Schwartz and compact convolution components. -/
theorem cssSphere_extConv_decomp
    (u v : 𝓢'(E n, ℂ))
    (h : HasExtendedConvolution u v)
    (hu : ConicSingularSupportSphere u = ∅)
    (d : SchwartzCompactDecomp u) :
    ConicSingularSupportSphere (extConv u v h) ⊆
      ConicSingularSupportSphere ((standardConvolutionSystem v).convSchwartz d.schwartzPart) ∪
      ConicSingularSupportSphere ((standardConvolutionSystem v).convCompact d.compactPart) := by
  rw [extConv_eq_of_decomp u v h hu d]
  exact ConicSingularSupportSphere_add_subset _ _


/-- Conic singular support is monotone under convolution with a Schwartz function:
`CSS_sphere (v * φ) ⊆ CSS_sphere v`. -/
theorem cssSphere_convSchwartz_subset
    (v : 𝓢'(E n, ℂ))
    (φ : 𝓢(E n, ℂ)) :
    ConicSingularSupportSphere ((standardConvolutionSystem v).convSchwartz φ) ⊆
      ConicSingularSupportSphere v := by
  rw [standardConvolutionSystem_convSchwartz_eq]
  exact css_schwartz_convolution v φ

/-- Additivity of `convCompact` in the right argument of `standardConvolutionSystem`:
`(v₁ + v₂) * w = v₁ * w + v₂ * w` for compactly supported `w`. -/
theorem standardConvolutionSystem_convCompact_add_right
    (v₁ v₂ w : 𝓢'(E n, ℂ)) :
    (standardConvolutionSystem (v₁ + v₂)).convCompact w =
      (standardConvolutionSystem v₁).convCompact w +
      (standardConvolutionSystem v₂).convCompact w := by
  show compactDistribConv (v₁ + v₂) w = compactDistribConv v₁ w + compactDistribConv v₂ w
  exact compactDistribConv_add_right v₁ v₂ w


/-- Associativity of distributional convolution with Schwartz functions: pairing the Schwartz
function `φ` against the convolution `w * ψ` equals pairing `w` against the Schwartz
convolution `φ * ψ`. -/
theorem distribConvolution_assoc
    (w : 𝓢'(E n, ℂ))
    (hw : DifferentialOperators.HasCompactSupport w)
    (φ ψ : 𝓢(E n, ℂ)) :
    (schwEmbed φ) ((DifferentialOperators.convolutionSchwartzCLM w hw) ψ) =
      w (((SchwartzMap.convolution (.lsmul ℂ ℂ)) φ) ψ) := by sorry


/-- A distributional Fubini formula: the integral of `(w * ψ) · φ` equals the pairing of `w`
with the Schwartz function `F(y) = ∫ φ(x) ψ(y - x) dx`. -/
theorem distribFubini_conv
    (w : 𝓢'(E n, ℂ))
    (hw : DifferentialOperators.HasCompactSupport w)
    (φ ψ : 𝓢(E n, ℂ))
    (F : 𝓢(E n, ℂ))
    (hF : ∀ y, F y = ∫ (x : E n), φ x • ψ (y - x) ∂volume) :
    ∫ (x : E n), ((DifferentialOperators.convolutionSchwartzCLM w hw) ψ) x • φ x ∂volume = w F := by

  have lhs_eq : ∫ (x : E n), ((DifferentialOperators.convolutionSchwartzCLM w hw) ψ) x • φ x ∂volume =
      (schwEmbed φ) ((DifferentialOperators.convolutionSchwartzCLM w hw) ψ) := by
    simp only [schwEmbed, SchwartzMap.toTemperedDistributionCLM_apply_apply]
  rw [lhs_eq]

  rw [distribConvolution_assoc w hw φ ψ]

  congr 1
  ext y
  rw [SchwartzMap.convolution_apply, MeasureTheory.convolution]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  exact (hF y).symm

/-- `L²` symmetry of the convolution operator with a compactly supported distribution `w`:
`⟨w * ψ, φ⟩_{L²} = ⟨ψ, w * φ⟩_{L²}`, an instance of the Fubini-type identity. -/
theorem convolutionSchwartzCLM_L2_symmetric
    (w : 𝓢'(E n, ℂ))
    (hw : DifferentialOperators.HasCompactSupport w)
    (φ ψ : 𝓢(E n, ℂ)) :
    ∫ (x : E n), ((DifferentialOperators.convolutionSchwartzCLM w hw) ψ) x • φ x ∂volume =
    ∫ (x : E n), ψ x • ((DifferentialOperators.convolutionSchwartzCLM w hw) φ) x ∂volume := by

  set F := ((SchwartzMap.convolution (.lsmul ℂ ℂ)) φ) ψ
  have hF_eq : ∀ y, F y = ∫ x, φ x • ψ (y - x) ∂volume := by
    intro y
    simp [F, SchwartzMap.convolution_apply, MeasureTheory.convolution, smul_eq_mul]

  rw [distribFubini_conv w hw φ ψ F hF_eq]

  rw [show ∫ (x : E n), ψ x • ((DifferentialOperators.convolutionSchwartzCLM w hw) φ) x ∂volume =
    ∫ (x : E n), ((DifferentialOperators.convolutionSchwartzCLM w hw) φ) x • ψ x ∂volume from
    by congr 1; ext x; rw [smul_eq_mul, smul_eq_mul, mul_comm]]

  have hF_eq' : ∀ y, F y = ∫ x, ψ x • φ (y - x) ∂volume := by
    intro y; rw [hF_eq]; simp_rw [smul_eq_mul]
    rw [← MeasureTheory.integral_sub_left_eq_self (f := fun x => ψ x * φ (y - x))
      (μ := MeasureTheory.volume) (x' := y)]
    simp_rw [sub_sub_cancel]; congr 1; ext x; exact mul_comm _ _
  rw [distribFubini_conv w hw ψ φ F hF_eq']

/-- Convolution of a compactly supported distribution `w` with the embedded Schwartz function
`φ` yields a tempered distribution represented by a Schwartz function. -/
theorem distribConvolution_schwEmbed_isSchwartz
    (φ : 𝓢(E n, ℂ))
    (w : 𝓢'(E n, ℂ))
    (hw : DifferentialOperators.HasCompactSupport w) :
    ∃ f : 𝓢(E n, ℂ),
      DifferentialOperators.distribConvolution w (schwEmbed φ) hw = schwEmbed f := by
  use DifferentialOperators.convolutionSchwartzCLM w hw φ
  ext ψ
  show (schwEmbed φ) (DifferentialOperators.convolutionSchwartzCLM w hw ψ) =
    (schwEmbed (DifferentialOperators.convolutionSchwartzCLM w hw φ)) ψ
  simp only [schwEmbed, SchwartzMap.toTemperedDistributionCLM_apply_apply]
  exact convolutionSchwartzCLM_L2_symmetric w hw φ ψ


/-- `convCompact` of a compactly supported distribution with the embedded Schwartz function
`φ` is itself represented by a Schwartz function. -/
theorem convCompact_schwEmbed_isSchwartz
    (φ : 𝓢(E n, ℂ))
    (w : 𝓢'(E n, ℂ))
    (hw : IsCompactlySupportedDistribution w) :
    ∃ f : 𝓢(E n, ℂ),
      (standardConvolutionSystem (schwEmbed φ)).convCompact w = schwEmbed f := by
  have hw' : DifferentialOperators.HasCompactSupport w :=
    (isCompactlySupportedDistribution_iff_hasCompactSupport w).mp hw
  obtain ⟨f, hf⟩ := distribConvolution_schwEmbed_isSchwartz φ w hw'
  exact ⟨f, by rw [convCompact_eq_distribConvolution (schwEmbed φ) w hw', hf]⟩

/-- When the parameter of `standardConvolutionSystem` is a Schwartz function (embedded as a
distribution), `convCompact` always has empty conic singular support on the sphere. -/
theorem cssSphere_convCompact_schwartz_param_empty
    (φ : 𝓢(E n, ℂ))
    (w : 𝓢'(E n, ℂ))
    (hw : IsCompactlySupportedDistribution w) :
    ConicSingularSupportSphere
      ((standardConvolutionSystem (schwEmbed φ)).convCompact w) = ∅ := by
  obtain ⟨f, hf⟩ := convCompact_schwEmbed_isSchwartz φ w hw
  rw [hf]
  exact schwartz_conicSingularSupportSphere_empty f


/-- Vanishing of `compactDistribConv` in the left argument when this is zero:
`(0) * w = 0`. -/
theorem compactDistribConv_zero_right (w : 𝓢'(E n, ℂ)) :
    compactDistribConv 0 w = 0 := by
  have h := compactDistribConv_add_right (n := n) (0 : 𝓢'(E n, ℂ)) 0 w
  simp only [add_zero] at h


  have := add_left_cancel (a := compactDistribConv (0 : 𝓢'(E n, ℂ)) w)
    (show compactDistribConv 0 w + 0 = compactDistribConv 0 w + compactDistribConv 0 w
      from by rw [add_zero]; exact h)
  exact this.symm


/-- If multiplication of `v` by `g₀` annihilates `v`, then the same multiplication annihilates
`compactDistribConv v w` for any compactly supported `w`. -/
theorem smulLeftCLM_compactDistribConv_vanishing
    (v : 𝓢'(E n, ℂ))
    (w : 𝓢'(E n, ℂ))
    (hw : IsCompactlySupportedDistribution w)
    (g₀ : E n → ℂ)
    (hg₀_vanish : TemperedDistribution.smulLeftCLM ℂ g₀ v = 0) :
    TemperedDistribution.smulLeftCLM ℂ g₀ (compactDistribConv v w) = 0 := by
  rw [smulLeftCLM_compactDistribConv_comm v w hw g₀, hg₀_vanish,
    compactDistribConv_zero_right]


/-- If a conic cutoff `g₀` near `ω` annihilates `v`, then `g₀ · (v * w)` is a Schwartz
function for any compactly supported `w`; here this is exhibited by the zero Schwartz
function. -/
theorem conicCutoff_smul_compactConvolution_schwartz_of_vanishing
    (v : 𝓢'(E n, ℂ))
    (w : 𝓢'(E n, ℂ))
    (hw : IsCompactlySupportedDistribution w)
    (g₀ : E n → ℂ) (ω : Sphere n)
    (hg₀ : IsConicCutoffNear g₀ ω)
    (hg₀_vanish : TemperedDistribution.smulLeftCLM ℂ g₀ v = 0) :
    ∃ (f : SchwartzMap (E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ g₀
        ((standardConvolutionSystem v).convCompact w) = (f : 𝓢'(E n, ℂ)) := by
  refine ⟨0, ?_⟩
  have h := smulLeftCLM_compactDistribConv_vanishing v w hw g₀ hg₀_vanish
  simp only [standardConvolutionSystem] at *
  rw [h, map_zero]


/-- Microlocal control: if a direction set `Γ` is disjoint from the conic support of `v`,
then it is also disjoint from the conic singular support of `v * w` for compactly supported
`w`. -/
theorem cssSphere_convCompact_coneSupportDisjoint
    (v w : 𝓢'(E n, ℂ))
    (hw : IsCompactlySupportedDistribution w)
    (Γ : Set (Sphere n))
    (hdisjoint : Disjoint (ConicSupportSphere v) Γ) :
    Disjoint (ConicSingularSupportSphere
      ((standardConvolutionSystem v).convCompact w)) Γ := by
  rw [Set.disjoint_left]
  intro ω hω_css hω_Γ

  have hω_not_csp : ω ∉ ConicSupportSphere v :=
    Set.disjoint_right.mp hdisjoint hω_Γ

  simp only [ConicSupportSphere, Set.mem_setOf_eq, not_not] at hω_not_csp
  obtain ⟨g₀, hg₀_conic, hg₀_zero⟩ := hω_not_csp

  obtain ⟨f, hf⟩ := conicCutoff_smul_compactConvolution_schwartz_of_vanishing
    v w hw g₀ ω hg₀_conic hg₀_zero

  exact hω_css ⟨g₀, hg₀_conic, f, hf⟩


/-- Short-name alias for the subadditivity of `ConicSingularSupportSphere` under addition. -/
theorem cssSphere_add_subset
    (u₁ u₂ : 𝓢'(E n, ℂ)) :
    ConicSingularSupportSphere (u₁ + u₂) ⊆
      ConicSingularSupportSphere u₁ ∪ ConicSingularSupportSphere u₂ :=
  ConicSingularSupportSphere_add_subset u₁ u₂

/-- Convolution with a compactly supported distribution does not enlarge the conic singular
support on the sphere: `CSS_sphere (v * w) ⊆ CSS_sphere v`. -/
theorem cssSphere_convCompact_subset
    (v : 𝓢'(E n, ℂ))
    (w : 𝓢'(E n, ℂ))
    (hw : IsCompactlySupportedDistribution w) :
    ConicSingularSupportSphere ((standardConvolutionSystem v).convCompact w) ⊆
      ConicSingularSupportSphere v := by

  intro ω hω_mem
  by_contra hω_not_mem

  have hω_singleton_closed : IsClosed ({⟨ω.val, ω.property⟩} : Set (Sphere n)) :=
    isClosed_singleton
  have hω_disjoint : Disjoint (ConicSingularSupportSphere v)
      ({⟨ω.val, ω.property⟩} : Set (Sphere n)) := by
    rw [Set.disjoint_singleton_right]
    exact hω_not_mem

  obtain ⟨v₁', v₁'', v₂, hv_sum, hv₁'_compact, _, _, hv_cone_disjoint⟩ :=
    exists_decomposition_disjoint_conicSingularSupport v
      {⟨ω.val, ω.property⟩} hω_singleton_closed hω_disjoint

  have hv_eq : v = (v₁' + v₁'') + (schwEmbed v₂) := by
    rw [hv_sum]


  have hconv_decomp :=
    standardConvolutionSystem_convCompact_add_right (v₁' + v₁'') (schwEmbed v₂) w
  rw [hv_eq] at hω_mem
  rw [hconv_decomp] at hω_mem

  have hω_union := cssSphere_add_subset _ _ hω_mem
  cases hω_union with
  | inl hω_left =>


    have hcone_disjoint := cssSphere_convCompact_coneSupportDisjoint
      (v₁' + v₁'') w hw {⟨ω.val, ω.property⟩} hv_cone_disjoint
    exact absurd (Set.disjoint_singleton_right.mp hcone_disjoint) (not_not.mpr hω_left)

  | inr hω_right =>

    have hempty := cssSphere_convCompact_schwartz_param_empty v₂ w hw
    rw [hempty] at hω_right
    exact absurd hω_right (Set.notMem_empty _)

/-- Conic singular support of the extended convolution: `CSS_sphere (extConv u v h) ⊆
CSS_sphere v`, recovering the microlocal direction control. -/
theorem cssSphere_extConv_subset
    (u v : 𝓢'(E n, ℂ))
    (h : HasExtendedConvolution u v)
    (hu : ConicSingularSupportSphere u = ∅) :
    ConicSingularSupportSphere (extConv u v h) ⊆ ConicSingularSupportSphere v := by

  have hdecomp := hasEmptyConicSingularSupportSphere_of_eq_empty u hu
  obtain ⟨d⟩ := hdecomp.hasDecomp

  have h_decomp := cssSphere_extConv_decomp u v h hu d

  have h_schwartz := cssSphere_convSchwartz_subset v d.schwartzPart

  have h_compact := cssSphere_convCompact_subset v d.compactPart
    d.compactPart_isCompactlySupported

  intro ω hω
  have hω_union := h_decomp hω
  cases hω_union with
  | inl h_left => exact h_schwartz h_left
  | inr h_right => exact h_compact h_right

/-- Microlocal inclusion for the cone singular support of the extended convolution: the cone
singular support of `extConv u v h` is contained in the union of the Minkowski sum of singular
supports (in the `Sum.inl` block) and the conic singular support of `v` (in the `Sum.inr`
block). This is Cor 12.17 in Melrose. -/
theorem css_convolution_subset
    (u v : 𝓢'(E n, ℂ))
    (h : HasExtendedConvolution u v)
    (hu : ConicSingularSupportSphere u = ∅) :
    coneSingularSupport (extConv u v h) ⊆
      Sum.inl '' (singularSupport u + singularSupport v) ∪
      Sum.inr '' (ConicSingularSupportSphere v) := by

  intro p hp
  simp only [coneSingularSupport, Set.mem_union, Set.mem_image] at hp
  cases hp with
  | inl hp =>

    obtain ⟨x, hx, rfl⟩ := hp

    left
    exact Set.mem_image_of_mem Sum.inl (singularSupport_extConv_subset u v h hu hx)
  | inr hp =>

    obtain ⟨ω, hω, rfl⟩ := hp

    right
    exact Set.mem_image_of_mem Sum.inr (cssSphere_extConv_subset u v h hu hω)

end ConeSupport

end
