/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Fourier.Convolution
import Atlas.DifferentialAnalysis.code.DifferentialOperators
import Atlas.DifferentialAnalysis.code.HormanderFundamental

noncomputable section

open scoped SchwartzMap FourierTransform
open MeasureTheory Set

namespace ConeSupport

variable {n : ℕ}

/-- Shorthand for the standard `n`-dimensional Euclidean space `ℝⁿ` used throughout
the cone-support and wavefront-set development. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Shorthand for the unit sphere `S^{n-1} ⊆ ℝⁿ`, viewed as `Metric.sphere 0 1`. -/
abbrev Sphere (n : ℕ) := Metric.sphere (0 : E n) 1

/-- `IsConicCutoffNear g ω` says that `g : ℝⁿ → ℂ` is a smooth conic cutoff function
adapted to a unit-sphere direction `ω`. Concretely: `g` is `C^∞`, vanishes near the
origin, and agrees outside some small ball with a degree-`0` positively homogeneous
function `ψ` that does not vanish at `ω`. -/
def IsConicCutoffNear (g : E n → ℂ) (ω : Sphere n) : Prop :=
  ContDiff ℝ ↑(⊤ : ℕ∞) g ∧
  ∃ (R : ℝ), 0 < R ∧ R < 1 ∧
    ∃ (R₀ : ℝ), 0 < R₀ ∧ Function.support g ⊆ {x : E n | R₀ ≤ ‖x‖} ∧
    ∃ (ψ : E n → ℂ),
      (∀ (a : ℝ), 0 < a → ∀ (x : E n), x ≠ 0 → ψ (a • x) = ψ x) ∧
      ψ (ω : E n) ≠ 0 ∧
      (∀ x : E n, R < ‖x‖ → g x = ψ x)

/-- The *cone support on the sphere* of a tempered distribution `u`: the directions
`ω` at infinity for which no conic cutoff `g` near `ω` kills `u`, i.e., for which
`g · u ≠ 0` for every conic cutoff. -/
def ConeSupportSphere (u : 𝓢'(E n, ℂ)) : Set (Sphere n) :=
  {ω | ¬ ∃ (g : E n → ℂ), IsConicCutoffNear g ω ∧
         TemperedDistribution.smulLeftCLM ℂ g u = 0}

/-- `IsSmoothNear u x` says that `u` is *smooth near `x`*: there exists a smooth
compactly supported `φ` with `φ x ≠ 0` such that `φ · u` is (the embedding of) a
Schwartz function. This is the local Schwartz-representation criterion. -/
def IsSmoothNear (u : 𝓢'(E n, ℂ)) (x : E n) : Prop :=
  ∃ (φ : E n → ℂ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧
    HasCompactSupport φ ∧
    φ x ≠ 0 ∧
    ∃ (f : SchwartzMap (E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ φ u = (f : 𝓢'(E n, ℂ))

/-- The *singular support* of `u` (classical, in the interior): the set of points
`x` at which `u` fails to be smooth, in the sense of `IsSmoothNear`. -/
def singularSupport (u : 𝓢'(E n, ℂ)) : Set (E n) :=
  {x | ¬ IsSmoothNear u x}

/-- The *conic singular support on the sphere*: directions `ω` for which no conic
cutoff `g` near `ω` makes `g · u` (the embedding of) a Schwartz function. This is
the asymptotic singular support of `u` at infinity. -/
def ConicSingularSupportSphere (u : 𝓢'(E n, ℂ)) : Set (Sphere n) :=
  {ω | ¬ ∃ (g : E n → ℂ), IsConicCutoffNear g ω ∧
         ∃ (f : SchwartzMap (E n) ℂ),
           TemperedDistribution.smulLeftCLM ℂ g u = (f : 𝓢'(E n, ℂ))}

/-- The *cone support* of `u`, packaged as a subset of `ℝⁿ ⊕ S^{n-1}`: the
distributional support in the interior, together with the cone support on the
sphere at infinity. -/
def coneSupport (u : 𝓢'(E n, ℂ)) : Set (E n ⊕ Sphere n) :=
  Sum.inl '' (Distribution.dsupport u) ∪ Sum.inr '' (ConeSupportSphere u)

/-- The *cone singular support* of `u`, packaged as a subset of `ℝⁿ ⊕ S^{n-1}`:
the singular support in the interior, plus the conic singular support on the
sphere at infinity. -/
def coneSingularSupport (u : 𝓢'(E n, ℂ)) : Set (E n ⊕ Sphere n) :=
  Sum.inl '' (singularSupport u) ∪ Sum.inr '' (ConicSingularSupportSphere u)

/-- The (classical) *wavefront set* of `u`: the set of pairs `(x, ω)` such
that no smooth compactly supported bump `φ` nonzero at `x` produces a
distribution `φ · u` whose Fourier transform is conically smooth at `ω`. -/
def wavefrontSet (u : 𝓢'(E n, ℂ)) : Set (E n × Sphere n) :=
  {p | ¬ ∃ (φ : E n → ℂ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧
    HasCompactSupport φ ∧
    φ p.1 ≠ 0 ∧
    p.2 ∉ ConicSingularSupportSphere (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ u))}

/-- The *scattering wavefront set at infinity*: the contribution to the
wavefront set parametrised by sphere directions at infinity, with the second
factor in the cone singular support of `𝓕 (g · u)`. -/
def scatteringWavefrontSetAtInfinity (u : 𝓢'(E n, ℂ)) : Set (Sphere n × (E n ⊕ Sphere n)) :=
  {q | ¬ ∃ (g : E n → ℂ), IsConicCutoffNear g q.1 ∧
    q.2 ∉ coneSingularSupport (𝓕 (TemperedDistribution.smulLeftCLM ℂ g u))}

/-- The *scattering wavefront set* of a tempered distribution `u`, obtained
by combining the classical wavefront set with the wavefront set at infinity. -/
def scatteringWavefrontSet (u : 𝓢'(E n, ℂ)) : Set ((E n ⊕ Sphere n) × (E n ⊕ Sphere n)) :=
  (Prod.map Sum.inl Sum.inr '' wavefrontSet u) ∪
  (Prod.map Sum.inr id '' scatteringWavefrontSetAtInfinity u)

/-- The *conic support on the sphere* (duplicated definition kept for
backward-compatibility with earlier statements). -/
def ConicSupportSphere (u : 𝓢'(E n, ℂ)) : Set (Sphere n) :=
  {ω | ¬ ∃ (g : E n → ℂ), IsConicCutoffNear g ω ∧
         TemperedDistribution.smulLeftCLM ℂ g u = 0}

/-- A tempered distribution `u` is *compactly supported* if it vanishes on any
Schwartz function whose support is disjoint from some compact set `K`. -/
def IsCompactlySupportedDistribution (u : 𝓢'(E n, ℂ)) : Prop :=
  ∃ K : Set (E n), IsCompact K ∧
    ∀ f : 𝓢(E n, ℂ), (Function.support (⇑f) ∩ K = ∅) → u f = 0

/-- The *direction* of a nonzero vector `x ∈ ℝⁿ`, namely `x / ‖x‖` viewed as
a point of the unit sphere. -/
def directionOf {n : ℕ} (x : E n) (hx : x ≠ 0) : Sphere n :=
  ⟨‖x‖⁻¹ • x, by
    simp [Metric.mem_sphere, dist_zero_right, norm_smul, abs_of_pos (inv_pos.mpr
      (norm_pos_iff.mpr hx)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩


/-- If `Γ ⊆ 𝕊ⁿ⁻¹` is closed and disjoint from the conic singular support of
`u`, then `u` admits a decomposition `u = u₁' + u₁'' + u₂` where `u₁'` is
compactly supported, `u₁''` vanishes on Schwartz functions whose nonzero
points all have direction in `Γ`, `u₂` is Schwartz, and the conic support of
`u₁' + u₁''` is disjoint from `Γ`. -/
theorem exists_decomposition_disjoint_conicSingularSupport
    (u : 𝓢'(E n, ℂ))
    (Γ : Set (Sphere n))
    (hΓ_closed : IsClosed Γ)
    (hΓ_disjoint : Disjoint (ConicSingularSupportSphere u) Γ) :
    ∃ (u₁' u₁'' : 𝓢'(E n, ℂ)) (u₂ : 𝓢(E n, ℂ)),
      u = u₁' + u₁'' + (u₂ : 𝓢'(E n, ℂ)) ∧
      IsCompactlySupportedDistribution u₁' ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ f : 𝓢(E n, ℂ), (∀ x, ‖x‖ < ε → f x = 0) → u₁'' f = 0) ∧
      (∀ f : 𝓢(E n, ℂ),
        (∀ x : E n, f x ≠ 0 → x ≠ 0 ∧ ∀ (hx : x ≠ 0), directionOf x hx ∈ Γ) →
        u₁'' f = 0) ∧
      Disjoint (ConicSupportSphere (u₁' + u₁'')) Γ := by sorry

/-- The continuous linear embedding of Schwartz functions into the space of
tempered distributions. -/
abbrev schwEmbed : 𝓢(E n, ℂ) →L[ℂ] 𝓢'(E n, ℂ) :=
  SchwartzMap.toTemperedDistributionCLM (E n) ℂ

/-- A decomposition of a tempered distribution `u` into a Schwartz part and a
compactly supported part. -/
structure SchwartzCompactDecomp (u : 𝓢'(E n, ℂ)) where
  schwartzPart : 𝓢(E n, ℂ)
  compactPart : 𝓢'(E n, ℂ)
  compactPart_isCompactlySupported : IsCompactlySupportedDistribution compactPart
  sum_eq : u = schwEmbed schwartzPart + compactPart

/-- Predicate stating that `u` admits at least one `SchwartzCompactDecomp`,
and any two such decompositions differ by a compactly supported distribution. -/
structure HasEmptyConicSingularSupportSphere (u : 𝓢'(E n, ℂ)) : Prop where
  hasDecomp : Nonempty (SchwartzCompactDecomp u)
  diff_compactlySupported : ∀ (d₁ d₂ : SchwartzCompactDecomp u),
    IsCompactlySupportedDistribution (schwEmbed d₁.schwartzPart - schwEmbed d₂.schwartzPart)

/-- Abstract data for performing convolutions of tempered distributions: a
"Schwartz-against" operator that is additive, a "compact-against" operator
that is additive, and a compatibility condition saying the two agree when the
input is compactly supported. -/
structure ConvolutionSystem (n : ℕ) where
  convSchwartz : 𝓢(E n, ℂ) → 𝓢'(E n, ℂ)
  convCompact : 𝓢'(E n, ℂ) → 𝓢'(E n, ℂ)
  convSchwartz_add : ∀ φ₁ φ₂, convSchwartz (φ₁ + φ₂) = convSchwartz φ₁ + convSchwartz φ₂
  convCompact_add : ∀ u₁ u₂, convCompact (u₁ + u₂) = convCompact u₁ + convCompact u₂
  convSchwartz_eq_compact : ∀ φ : 𝓢(E n, ℂ),
    IsCompactlySupportedDistribution (schwEmbed φ) →
    convSchwartz φ = convCompact (schwEmbed φ)

/-- The difference of two compactly supported tempered distributions is
compactly supported. -/
lemma isCompactlySupportedDistribution_sub
    {u₁ u₂ : 𝓢'(E n, ℂ)}
    (h₁ : IsCompactlySupportedDistribution u₁)
    (h₂ : IsCompactlySupportedDistribution u₂) :
    IsCompactlySupportedDistribution (u₁ - u₂) := by
  obtain ⟨K₁, hK₁_compact, hK₁_vanish⟩ := h₁
  obtain ⟨K₂, hK₂_compact, hK₂_vanish⟩ := h₂
  refine ⟨K₁ ∪ K₂, hK₁_compact.union hK₂_compact, fun f hf => ?_⟩
  have hf₁ : Function.support (⇑f) ∩ K₁ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have := Set.eq_empty_iff_forall_notMem.mp hf x
    exact this (Set.mem_inter hx.1 (Set.mem_union_left K₂ hx.2))
  have hf₂ : Function.support (⇑f) ∩ K₂ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have := Set.eq_empty_iff_forall_notMem.mp hf x
    exact this (Set.mem_inter hx.1 (Set.mem_union_right K₁ hx.2))
  simp only [UniformConvergenceCLM.sub_apply, hK₁_vanish f hf₁, hK₂_vanish f hf₂, sub_zero]

/-- The sum of two compactly supported tempered distributions is
compactly supported. -/
lemma isCompactlySupportedDistribution_add
    {u₁ u₂ : 𝓢'(E n, ℂ)}
    (h₁ : IsCompactlySupportedDistribution u₁)
    (h₂ : IsCompactlySupportedDistribution u₂) :
    IsCompactlySupportedDistribution (u₁ + u₂) := by
  obtain ⟨K₁, hK₁_compact, hK₁_vanish⟩ := h₁
  obtain ⟨K₂, hK₂_compact, hK₂_vanish⟩ := h₂
  refine ⟨K₁ ∪ K₂, hK₁_compact.union hK₂_compact, fun f hf => ?_⟩
  have hf₁ : Function.support (⇑f) ∩ K₁ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have := Set.eq_empty_iff_forall_notMem.mp hf x
    exact this (Set.mem_inter hx.1 (Set.mem_union_left K₂ hx.2))
  have hf₂ : Function.support (⇑f) ∩ K₂ = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro x hx
    have := Set.eq_empty_iff_forall_notMem.mp hf x
    exact this (Set.mem_inter hx.1 (Set.mem_union_right K₁ hx.2))
  simp only [UniformConvergenceCLM.add_apply, hK₁_vanish f hf₁, hK₂_vanish f hf₂, add_zero]

/-- A tempered distribution that vanishes on every Schwartz function supported
away from the origin is compactly supported (with support `{0}`). -/
lemma isCompactlySupportedDistribution_of_supported_at_zero
    {u : 𝓢'(E n, ℂ)}
    (h : ∀ f : 𝓢(E n, ℂ), (∀ x : E n, f x ≠ 0 → x ≠ 0) → u f = 0) :
    IsCompactlySupportedDistribution u := by
  refine ⟨{0}, isCompact_singleton, fun f hf => ?_⟩
  apply h
  intro x hfx hx_eq
  have hmem : x ∈ Function.support (⇑f) ∩ ({(0 : E n)} : Set (E n)) :=
    Set.mem_inter (Function.mem_support.mpr hfx) (by rw [hx_eq]; exact Set.mem_singleton _)
  rw [hf] at hmem
  exact hmem


/-- If `ConicSingularSupportSphere u = ∅`, then `u` has the structure of an
empty conic singular support — it admits a Schwartz/compact decomposition
with the diff-compactness property. -/
theorem hasEmptyConicSingularSupportSphere_of_eq_empty
    (u : 𝓢'(E n, ℂ))
    (h : ConicSingularSupportSphere u = ∅) :
    HasEmptyConicSingularSupportSphere u := by


  have hΓ_disjoint : Disjoint (ConicSingularSupportSphere u) (Set.univ : Set (Sphere n)) := by
    rw [h]; exact Set.empty_disjoint _
  obtain ⟨u₁', u₁'', u₂, hdecomp, hu₁'_compact, ⟨ε, hε, hvanish_near⟩,
    hvanish_cone, _⟩ :=
    exists_decomposition_disjoint_conicSingularSupport u Set.univ isClosed_univ hΓ_disjoint

  have hu₁''_compact : IsCompactlySupportedDistribution u₁'' := by
    apply isCompactlySupportedDistribution_of_supported_at_zero
    intro f hf
    exact hvanish_cone f (fun x hfx => ⟨hf x hfx, fun _ => Set.mem_univ _⟩)

  have hcompact : IsCompactlySupportedDistribution (u₁' + u₁'') :=
    isCompactlySupportedDistribution_add hu₁'_compact hu₁''_compact

  have hsum : u = schwEmbed u₂ + (u₁' + u₁'') := by

    rw [show (u₂ : 𝓢'(E n, ℂ)) = schwEmbed u₂ from rfl] at hdecomp
    rw [hdecomp]; abel
  constructor
  ·
    exact ⟨⟨u₂, u₁' + u₁'', hcompact, hsum⟩⟩
  ·
    intro d₁ d₂


    have heq : schwEmbed d₁.schwartzPart + d₁.compactPart =
        schwEmbed d₂.schwartzPart + d₂.compactPart := by
      rw [← d₁.sum_eq, ← d₂.sum_eq]

    suffices schwEmbed d₁.schwartzPart - schwEmbed d₂.schwartzPart =
        d₂.compactPart - d₁.compactPart by
      rw [this]
      exact isCompactlySupportedDistribution_sub
        d₂.compactPart_isCompactlySupported d₁.compactPart_isCompactlySupported

    calc schwEmbed d₁.schwartzPart - schwEmbed d₂.schwartzPart
        = schwEmbed d₁.schwartzPart + d₁.compactPart -
          (schwEmbed d₂.schwartzPart + d₁.compactPart) := by abel
      _ = schwEmbed d₂.schwartzPart + d₂.compactPart -
          (schwEmbed d₂.schwartzPart + d₁.compactPart) := by rw [heq]
      _ = d₂.compactPart - d₁.compactPart := by abel

/-- The continuous linear map sending a Schwartz function `φ` to its
reflection `x ↦ φ(-x)`. -/
def schwartzReflectionCLM : 𝓢(E n, ℂ) →L[ℂ] 𝓢(E n, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ)

/-- The convolution `u * φ` of a tempered distribution `u` with a Schwartz
function `φ`, defined as the tempered distribution `ψ ↦ u(φ̌ * ψ)` where
`φ̌(x) = φ(-x)`. -/
def schwartzConvolution
    (u : TemperedDistribution (E n) ℂ) (φ : 𝓢(E n, ℂ)) :
    TemperedDistribution (E n) ℂ :=
  u.comp ((SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)) (schwartzReflectionCLM φ))


/-- Convolution of a tempered distribution `v` with a Schwartz function `φ`,
viewed as a tempered distribution. -/
def schwDistribConv (v : 𝓢'(E n, ℂ)) (φ : 𝓢(E n, ℂ)) : 𝓢'(E n, ℂ) :=
  schwartzConvolution v φ


/-- Convolution of a tempered distribution `v` with a compactly supported
tempered distribution `w`. -/
noncomputable def compactDistribConv (v : 𝓢'(E n, ℂ)) (w : 𝓢'(E n, ℂ)) : 𝓢'(E n, ℂ) := by sorry


/-- The Schwartz convolution `schwDistribConv v` is additive in its Schwartz
argument. -/
theorem schwDistribConv_add (v : 𝓢'(E n, ℂ)) (φ₁ φ₂ : 𝓢(E n, ℂ)) :
    schwDistribConv v (φ₁ + φ₂) = schwDistribConv v φ₁ + schwDistribConv v φ₂ := by
  unfold schwDistribConv schwartzConvolution
  have href : schwartzReflectionCLM (φ₁ + φ₂) =
    (schwartzReflectionCLM φ₁ + schwartzReflectionCLM φ₂ : 𝓢(E n, ℂ)) := map_add _ _ _
  rw [href, map_add]
  ext ψ
  exact map_add v _ _


/-- The compact convolution `compactDistribConv v` is additive in its compactly
supported argument. -/
theorem compactDistribConv_add (v : 𝓢'(E n, ℂ)) (w₁ w₂ : 𝓢'(E n, ℂ)) :
    compactDistribConv v (w₁ + w₂) = compactDistribConv v w₁ + compactDistribConv v w₂ := by sorry


/-- The compact convolution is additive in its first (distribution) argument. -/
theorem compactDistribConv_add_right (v₁ v₂ : 𝓢'(E n, ℂ)) (w : 𝓢'(E n, ℂ)) :
    compactDistribConv (v₁ + v₂) w = compactDistribConv v₁ w + compactDistribConv v₂ w := by sorry


/-- Multiplication on the left by a function `g` commutes with compact
convolution: `g · (v * w) = (g · v) * w` when `w` is compactly supported. -/
theorem smulLeftCLM_compactDistribConv_comm
    (v : 𝓢'(E n, ℂ))
    (w : 𝓢'(E n, ℂ))
    (hw : IsCompactlySupportedDistribution w)
    (g : E n → ℂ) :
    TemperedDistribution.smulLeftCLM ℂ g (compactDistribConv v w) =
      compactDistribConv (TemperedDistribution.smulLeftCLM ℂ g v) w := by sorry


/-- The Schwartz convolution and the compact convolution agree on Schwartz
functions whose distributional embedding is compactly supported. -/
theorem schwDistribConv_eq_compactDistribConv (v : 𝓢'(E n, ℂ))
    (φ : 𝓢(E n, ℂ)) (hφ : IsCompactlySupportedDistribution (schwEmbed φ)) :
    schwDistribConv v φ = compactDistribConv v (schwEmbed φ) := by sorry

/-- The convolution system associated to a tempered distribution `v`,
combining `schwDistribConv v` and `compactDistribConv v`. -/
def standardConvolutionSystem (v : 𝓢'(E n, ℂ)) : ConvolutionSystem n where
  convSchwartz := schwDistribConv v
  convCompact := compactDistribConv v
  convSchwartz_add := schwDistribConv_add v
  convCompact_add := compactDistribConv_add v
  convSchwartz_eq_compact := schwDistribConv_eq_compactDistribConv v

/-- The convolution `C.convSchwartz f + C.convCompact g` is independent of
the choice of Schwartz/compact decomposition `(f, g)` of `u`, provided `u`
has an empty conic singular support on the sphere. -/
theorem convolution_decomp_well_defined
    {u : 𝓢'(E n, ℂ)}
    (hu : HasEmptyConicSingularSupportSphere u)
    (C : ConvolutionSystem n)
    (d₁ d₂ : SchwartzCompactDecomp u) :
    C.convSchwartz d₁.schwartzPart + C.convCompact d₁.compactPart =
    C.convSchwartz d₂.schwartzPart + C.convCompact d₂.compactPart := by
  set f₁ := d₁.schwartzPart
  set f₂ := d₂.schwartzPart
  set g₁ := d₁.compactPart
  set g₂ := d₂.compactPart
  have hdecomp : schwEmbed f₁ + g₁ = schwEmbed f₂ + g₂ := by
    rw [← d₁.sum_eq, ← d₂.sum_eq]
  have hg₂ : g₂ = schwEmbed (f₁ - f₂) + g₁ := by
    have h : schwEmbed f₁ + g₁ - schwEmbed f₂ = g₂ := by rw [hdecomp]; abel
    show g₂ = schwEmbed (f₁ - f₂) + g₁
    rw [map_sub, ← h]; abel

  have hw : IsCompactlySupportedDistribution (schwEmbed (f₁ - f₂)) := by
    rw [map_sub]; exact hu.diff_compactlySupported d₁ d₂
  have step1 : C.convSchwartz f₁ = C.convSchwartz f₂ + C.convSchwartz (f₁ - f₂) := by
    have h := C.convSchwartz_add f₂ (f₁ - f₂)
    simp only [add_sub_cancel] at h
    exact h
  have step2 : C.convSchwartz (f₁ - f₂) = C.convCompact (schwEmbed (f₁ - f₂)) :=
    C.convSchwartz_eq_compact _ hw
  have step3 : C.convCompact g₂ =
      C.convCompact (schwEmbed (f₁ - f₂)) + C.convCompact g₁ := by
    rw [hg₂, C.convCompact_add]
  calc C.convSchwartz f₁ + C.convCompact g₁
      = (C.convSchwartz f₂ + C.convSchwartz (f₁ - f₂)) + C.convCompact g₁ := by rw [step1]
    _ = (C.convSchwartz f₂ + C.convCompact (schwEmbed (f₁ - f₂))) + C.convCompact g₁ := by
        rw [step2]
    _ = C.convSchwartz f₂ + (C.convCompact (schwEmbed (f₁ - f₂)) + C.convCompact g₁) := by
        rw [add_assoc]
    _ = C.convSchwartz f₂ + C.convCompact g₂ := by rw [← step3]

/-- Specialisation of `convolution_decomp_well_defined` to the standard
convolution system when the conic singular support of `u` is empty. -/
theorem convolution_decomp_well_defined_of_css_empty
    {u v : 𝓢'(E n, ℂ)}
    (hu : ConicSingularSupportSphere u = ∅)
    (d₁ d₂ : SchwartzCompactDecomp u) :
    (standardConvolutionSystem v).convSchwartz d₁.schwartzPart +
      (standardConvolutionSystem v).convCompact d₁.compactPart =
    (standardConvolutionSystem v).convSchwartz d₂.schwartzPart +
      (standardConvolutionSystem v).convCompact d₂.compactPart :=
  convolution_decomp_well_defined
    (hasEmptyConicSingularSupportSphere_of_eq_empty u hu)
    (standardConvolutionSystem v) d₁ d₂

/-- The antipodal map on the unit sphere: `ω ↦ -ω`. -/
def sphereNeg (ω : Sphere n) : Sphere n :=
  ⟨-ω.1, mem_sphere_zero_iff_norm.mpr (by rw [norm_neg]; exact mem_sphere_zero_iff_norm.mp ω.2)⟩

/-- `sphereNeg` simply negates the underlying vector. -/
@[simp]
lemma sphereNeg_val (ω : Sphere n) : (sphereNeg ω).1 = -ω.1 := rfl

/-- The antipodal map is an involution on the sphere. -/
@[simp]
lemma sphereNeg_sphereNeg (ω : Sphere n) :
    sphereNeg (sphereNeg ω) = ω := by
  apply Subtype.ext
  simp only [sphereNeg_val, neg_neg]

/-- The image of a set `S ⊆ 𝕊ⁿ⁻¹` under the antipodal map. -/
def negSet (S : Set (Sphere n)) : Set (Sphere n) :=
  sphereNeg '' S

/-- `ω ∈ negSet S ↔ -ω ∈ S`. -/
lemma mem_negSet_iff {S : Set (Sphere n)} {ω : Sphere n} :
    ω ∈ negSet S ↔ sphereNeg ω ∈ S := by
  constructor
  · rintro ⟨ω', hω', rfl⟩
    rwa [sphereNeg_sphereNeg]
  · intro h
    exact ⟨sphereNeg ω, h, sphereNeg_sphereNeg ω⟩

/-- The reflection of a tempered distribution `v`: the distribution
`φ ↦ v(φ ∘ -id)`. -/
def reflection (v : TemperedDistribution (E n) ℂ) :
    TemperedDistribution (E n) ℂ :=
  v.comp schwartzReflectionCLM


/-- The `convSchwartz` component of the standard convolution system equals
the Schwartz convolution. -/
theorem standardConvolutionSystem_convSchwartz_eq
    (v : 𝓢'(E n, ℂ)) (φ : 𝓢(E n, ℂ)) :
    (standardConvolutionSystem v).convSchwartz φ = schwartzConvolution v φ :=
  rfl


/-- The negation map `Neg.neg : ℝⁿ → ℝⁿ` has temperate growth. -/
lemma neg_hasTemperateGrowth :
    Function.HasTemperateGrowth (Neg.neg : E n → E n) :=
  (ContinuousLinearEquiv.neg ℝ : E n ≃L[ℝ] E n).toContinuousLinearMap.hasTemperateGrowth


/-- Pre-composition with negation preserves the temperate growth property. -/
lemma hasTemperateGrowth_comp_neg {g : E n → ℂ}
    (hg : Function.HasTemperateGrowth g) :
    Function.HasTemperateGrowth (g ∘ Neg.neg) :=
  hg.comp neg_hasTemperateGrowth

/-- `g` has temperate growth iff `g ∘ Neg.neg` does. -/
lemma hasTemperateGrowth_neg_iff {g : E n → ℂ} :
    Function.HasTemperateGrowth g ↔ Function.HasTemperateGrowth (g ∘ Neg.neg) :=
  ⟨hasTemperateGrowth_comp_neg,
   fun h => by rw [show g = (g ∘ Neg.neg) ∘ Neg.neg from by ext; simp]
               exact hasTemperateGrowth_comp_neg h⟩


/-- Multiplication on the left by `g` of the reflection of `v` equals the
composition of multiplication by `g ∘ Neg.neg` on `v` with the reflection map. -/
lemma smulLeft_reflection_eq (g : E n → ℂ) (v : TemperedDistribution (E n) ℂ) :
    TemperedDistribution.smulLeftCLM ℂ g (reflection v) =
    (TemperedDistribution.smulLeftCLM ℂ (g ∘ Neg.neg) v).comp schwartzReflectionCLM := by
  ext φ
  show v (schwartzReflectionCLM ((SchwartzMap.smulLeftCLM ℂ g) φ)) =
       v ((SchwartzMap.smulLeftCLM ℂ (g ∘ Neg.neg)) (schwartzReflectionCLM φ))
  congr 1
  ext x
  simp only [schwartzReflectionCLM, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp, ContinuousLinearEquiv.coe_neg, SchwartzMap.smulLeftCLM]
  split_ifs with h1 h2 h2
  · simp only [SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.lsmul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp, ContinuousLinearEquiv.coe_neg]
    simp [Pi.neg_apply, id]
  · exact absurd (hasTemperateGrowth_comp_neg h1) h2
  · exact absurd (hasTemperateGrowth_neg_iff.mpr h2) h1
  · simp


/-- The distributional reflection of a Schwartz function agrees with the
embedding of its Schwartz reflection. -/
lemma reflection_schwartz_coercion (f : SchwartzMap (E n) ℂ) :
    (↑f : 𝓢'(E n, ℂ)).comp schwartzReflectionCLM =
    (↑(schwartzReflectionCLM f) : 𝓢'(E n, ℂ)) := by
  ext φ
  simp only [ContinuousLinearMap.comp_apply]
  change (SchwartzMap.toTemperedDistributionCLM (E n) ℂ volume f) (schwartzReflectionCLM φ) =
         (SchwartzMap.toTemperedDistributionCLM (E n) ℂ volume (schwartzReflectionCLM f)) φ
  rw [SchwartzMap.toTemperedDistributionCLM_apply_apply (μ := volume),
      SchwartzMap.toTemperedDistributionCLM_apply_apply (μ := volume)]
  simp_rw [schwartzReflectionCLM, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp, ContinuousLinearEquiv.coe_neg]
  simp only [Pi.neg_apply, id]
  conv_lhs => rw [← Measure.map_neg_eq_self (μ := (volume : Measure (E n)))]
  rw [integral_map (Measurable.aemeasurable measurable_neg)]
  · simp [neg_neg]
  · rw [Measure.map_neg_eq_self]
    exact ((SchwartzMap.continuous φ).comp continuous_neg).aestronglyMeasurable.smul
      (SchwartzMap.continuous f).aestronglyMeasurable


/-- The Schwartz reflection map is an involution. -/
lemma schwartzReflectionCLM_comp_self :
    schwartzReflectionCLM.comp (schwartzReflectionCLM (n := n)) =
    ContinuousLinearMap.id ℂ _ := by
  ext φ x
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    schwartzReflectionCLM, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp, ContinuousLinearEquiv.coe_neg, Pi.neg_apply, id, neg_neg]


/-- Distributional reflection is an involution: `reflection (reflection u) = u`. -/
lemma reflection_reflection (u : TemperedDistribution (E n) ℂ) :
    reflection (reflection u) = u := by
  simp only [reflection]
  rw [ContinuousLinearMap.comp_assoc, schwartzReflectionCLM_comp_self,
    ContinuousLinearMap.comp_id]


/-- Pre-composition with negation sends a conic cutoff near `ω` to a conic
cutoff near `-ω`. -/
lemma isConicCutoffNear_comp_neg {g : E n → ℂ} {ω : Sphere n}
    (hg : IsConicCutoffNear g ω) :
    IsConicCutoffNear (g ∘ Neg.neg) (sphereNeg ω) := by
  obtain ⟨hsmooth, R, hR, _, R₀, hR₀, hsupp, ψ, hhom, hψω, hagree⟩ := hg
  refine ⟨hsmooth.comp (ContinuousLinearEquiv.neg ℝ).contDiff,
    R, hR, ‹_›, R₀, hR₀, ?_, ψ ∘ Neg.neg, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Function.mem_support, Function.comp_apply] at hx
    have := hsupp (show -x ∈ Function.support g from by simp [Function.mem_support, hx])
    simp only [mem_setOf_eq] at this ⊢
    rwa [norm_neg] at this
  · intro a ha x hx
    simp only [Function.comp_apply]
    rw [← smul_neg]
    exact hhom a ha (-x) (neg_ne_zero.mpr hx)
  · simp only [Function.comp_apply, sphereNeg_val, neg_neg]
    exact hψω
  · intro x hx
    simp only [Function.comp_apply]
    exact hagree (-x) (by rwa [norm_neg])


/-- The conic singular support on the sphere of the reflection of `v` is the
antipodal image of the conic singular support of `v`. -/
theorem css_reflection (v : TemperedDistribution (E n) ℂ) :
    ConicSingularSupportSphere (reflection v) = negSet (ConicSingularSupportSphere v) := by
  ext ω
  rw [mem_negSet_iff]
  simp only [ConicSingularSupportSphere, mem_setOf_eq]
  constructor
  ·
    intro hω hcontra
    apply hω
    obtain ⟨g, hg_conic, f, hf⟩ := hcontra
    refine ⟨g ∘ Neg.neg, ?_, ?_⟩
    · have := isConicCutoffNear_comp_neg hg_conic
      rwa [sphereNeg_sphereNeg] at this
    · rw [smulLeft_reflection_eq]
      have hgg : (g ∘ Neg.neg) ∘ Neg.neg = g := by ext; simp
      rw [hgg, hf]
      exact ⟨schwartzReflectionCLM f, reflection_schwartz_coercion f⟩
  ·
    intro hω hcontra
    apply hω
    obtain ⟨g, hg_conic, f, hf⟩ := hcontra
    refine ⟨g ∘ Neg.neg, isConicCutoffNear_comp_neg hg_conic, ?_⟩
    have h1 : reflection (TemperedDistribution.smulLeftCLM ℂ (g ∘ Neg.neg) v) = ↑f := by
      show (TemperedDistribution.smulLeftCLM ℂ (g ∘ Neg.neg) v).comp schwartzReflectionCLM =
        (f : 𝓢'(E n, ℂ))
      rwa [← smulLeft_reflection_eq]
    have h2 : TemperedDistribution.smulLeftCLM ℂ (g ∘ Neg.neg) v = reflection (↑f) := by
      have h3 := congr_arg reflection h1
      rwa [reflection_reflection] at h3
    rw [h2]
    exact ⟨schwartzReflectionCLM f, reflection_schwartz_coercion f⟩


/-- A lower bound on the norm of `r • X - s • Y` in terms of the angular
distance `‖X - Y‖` between two unit vectors: `‖X - Y‖/2 · (r + s) ≤ ‖r·X - s·Y‖`. -/
lemma norm_smul_sub_smul_lower_bound'
    (X Y : E n) (hX : ‖X‖ = 1) (hY : ‖Y‖ = 1)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    ‖X - Y‖ / 2 * (r + s) ≤ ‖r • X - s • Y‖ := by
  suffices h : (‖X - Y‖ / 2 * (r + s)) ^ 2 ≤ ‖r • X - s • Y‖ ^ 2 from
    le_of_sq_le_sq h (norm_nonneg _)
  have hRHS : ‖r • X - s • Y‖ ^ 2 = r ^ 2 + s ^ 2 - 2 * (r * s * (inner (𝕜 := ℝ) X Y)) := by
    rw [norm_sub_sq_real, norm_smul, norm_smul,
      Real.norm_of_nonneg hr, Real.norm_of_nonneg hs, hX, hY, mul_one, mul_one,
      real_inner_smul_left, inner_smul_right]; ring
  have hnorm_sq : ‖X - Y‖ ^ 2 = 2 - 2 * (inner (𝕜 := ℝ) X Y) := by
    rw [norm_sub_sq_real, hX, hY]; ring
  rw [show (‖X - Y‖ / 2 * (r + s)) ^ 2 = ‖X - Y‖ ^ 2 / 4 * (r + s) ^ 2 from by ring,
    hnorm_sq, hRHS]
  have ht_bound : (-1 : ℝ) ≤ inner (𝕜 := ℝ) X Y := by
    have := abs_real_inner_le_norm X Y
    rw [hX, hY, mul_one] at this
    linarith [neg_abs_le (inner (𝕜 := ℝ) X Y)]
  nlinarith [sq_nonneg (r - s)]

/-- If the closure of the set of directions of the support of `g` is contained
in an open set `Γ`, then there is a uniform separation `δ > 0` between the
directions of support of `g` and any direction outside `Γ`. -/
theorem conicCutoff_direction_separation
    (g : E n → ℂ) (ω : Sphere n) (_hg : IsConicCutoffNear g ω)
    (Γ : Set (Sphere n)) (_hωΓ : ω ∈ Γ)
    (hΓ_open : IsOpen Γ)
    (hdir_in : closure {σ : Sphere n | ∃ (x : E n) (hx : x ≠ 0),
        g x ≠ 0 ∧ directionOf x hx = σ} ⊆ Γ) :
    ∃ (δ : ℝ), 0 < δ ∧ ∀ (x : E n), g x ≠ 0 → (hx : x ≠ 0) →
      ∀ (y : E n) (hy : y ≠ 0), directionOf y hy ∉ Γ →
        δ ≤ ‖(directionOf x hx : E n) - (directionOf y hy : E n)‖ := by
  set D := {σ : Sphere n | ∃ (x : E n) (hx : x ≠ 0), g x ≠ 0 ∧ directionOf x hx = σ}
  have hcl_compact : IsCompact (closure D) := isClosed_closure.isCompact
  obtain ⟨δ, hδ, hthick⟩ := hcl_compact.exists_thickening_subset_open hΓ_open hdir_in
  refine ⟨δ, hδ, fun x hgx hx y hy hy_dir => ?_⟩
  have hx_in_cl : directionOf x hx ∈ closure D :=
    subset_closure ⟨x, hx, hgx, rfl⟩
  by_contra h_lt
  push Not at h_lt
  have hy_in_thick : directionOf y hy ∈ Metric.thickening δ (closure D) := by
    rw [Metric.mem_thickening_iff]
    refine ⟨directionOf x hx, hx_in_cl, ?_⟩
    simp only [Subtype.dist_eq, dist_eq_norm]
    linarith [norm_sub_rev (↑(directionOf x hx) : E n) (↑(directionOf y hy) : E n)]
  exact hy_dir (hthick hy_in_thick)

/-- Linear-cone separation estimate: if `g` is conic near `ω` with directions
inside `Γ`, then there is a constant `c > 0` such that
`c · (‖x‖ + ‖y‖) ≤ ‖x - y‖` for `x` in the support of `g` and `y` outside
the cone over `Γ` with `‖y‖ ≥ ε`. -/
theorem coneSeparation_estimate_conic_cutoff
    (g : E n → ℂ) (ω : Sphere n)
    (hg : IsConicCutoffNear g ω)
    (Γ : Set (Sphere n)) (hωΓ : ω ∈ Γ)
    (hΓ_open : IsOpen Γ)
    (hdir_in : closure {σ : Sphere n | ∃ (x : E n) (hx : x ≠ 0),
        g x ≠ 0 ∧ directionOf x hx = σ} ⊆ Γ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (c : ℝ), 0 < c ∧ ∀ (x y : E n),
      g x ≠ 0 → (hy : y ≠ 0) → directionOf y hy ∉ Γ → ε ≤ ‖y‖ →
      c * (‖x‖ + ‖y‖) ≤ ‖x - y‖ := by
  obtain ⟨_, _, _, R₀, hR₀, hsupp, _⟩ := hg.2
  obtain ⟨δ, hδ, hsep⟩ := conicCutoff_direction_separation g ω hg Γ hωΓ hΓ_open hdir_in
  refine ⟨δ / 2, by positivity, fun x y hgx hy hdir hεy => ?_⟩
  have hx_ne : x ≠ 0 := by
    intro h; subst h
    exact absurd (hsupp (Function.mem_support.mpr hgx)) (by simp; linarith)
  have hx_pos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx_ne
  have hy_pos : (0 : ℝ) < ‖y‖ := lt_of_lt_of_le hε hεy
  have hdir_x : ‖(directionOf x hx_ne : E n)‖ = 1 := by
    have := (directionOf x hx_ne).2
    rwa [Metric.mem_sphere, dist_zero_right] at this
  have hdir_y : ‖(directionOf y hy : E n)‖ = 1 := by
    have := (directionOf y hy).2
    rwa [Metric.mem_sphere, dist_zero_right] at this
  have hx_eq : x = ‖x‖ • (directionOf x hx_ne : E n) := by
    simp [directionOf, smul_smul, mul_inv_cancel₀ (ne_of_gt hx_pos)]
  have hy_eq : y = ‖y‖ • (directionOf y hy : E n) := by
    simp [directionOf, smul_smul, mul_inv_cancel₀ (ne_of_gt hy_pos)]
  calc δ / 2 * (‖x‖ + ‖y‖)
      ≤ ‖(directionOf x hx_ne : E n) - (directionOf y hy : E n)‖ / 2 * (‖x‖ + ‖y‖) := by
        gcongr
        exact hsep x hgx hx_ne y hy hdir
    _ ≤ ‖‖x‖ • (directionOf x hx_ne : E n) - ‖y‖ • (directionOf y hy : E n)‖ :=
        norm_smul_sub_smul_lower_bound' _ _ hdir_x hdir_y _ _ (le_of_lt hx_pos) (le_of_lt hy_pos)
    _ = ‖x - y‖ := by rw [← hx_eq, ← hy_eq]


/-- A conic cutoff function near a sphere direction `ω` has temperate growth
(in fact bounded). -/
theorem isConicCutoffNear_hasTemperateGrowth
    (g : E n → ℂ) (ω : Sphere n) (hg : IsConicCutoffNear g ω) :
    Function.HasTemperateGrowth g := by
  obtain ⟨hg_smooth, R, hR, _, R₀, hR₀, hsupp, ψ, hψ_hom, _, hψ_eq⟩ := hg
  refine ⟨hg_smooth, fun m => ?_⟩
  have h_cont_m : Continuous (iteratedFDeriv ℝ m g) :=
    hg_smooth.continuous_iteratedFDeriv (mod_cast le_top)
  obtain ⟨C_ball, hC_ball⟩ := (isCompact_closedBall (0 : E n) (R + 1)).exists_bound_of_continuousOn
    h_cont_m.norm.continuousOn
  refine ⟨0, C_ball, fun x => ?_⟩
  simp only [pow_zero, mul_one]
  by_cases hx : ‖x‖ ≤ R + 1
  · have hx_ball : x ∈ Metric.closedBall (0 : E n) (R + 1) := by
      simp [Metric.mem_closedBall, dist_zero_right]; exact hx
    have := hC_ball x hx_ball
    rwa [Real.norm_of_nonneg (norm_nonneg _)] at this
  · simp only [not_le] at hx
    have hx_gt_R : R < ‖x‖ := by linarith
    have hx_pos : (0 : ℝ) < ‖x‖ := by linarith
    have hx_ne : x ≠ 0 := by intro h; rw [h, norm_zero] at hx_pos; linarith
    set a := (R + 1) / ‖x‖ with ha_def
    have ha_pos : 0 < a := div_pos (by linarith) hx_pos
    have ha_le_one : a ≤ 1 := by rw [ha_def, div_le_one hx_pos]; linarith
    have ha_x_norm : ‖a • x‖ = R + 1 := by
      rw [norm_smul, Real.norm_of_nonneg ha_pos.le, ha_def]; field_simp
    have ha_x_ball : a • x ∈ Metric.closedBall (0 : E n) (R + 1) := by
      simp [Metric.mem_closedBall, dist_zero_right, ha_x_norm]
    have hg_comp_eq : (fun y => g (a • y)) =ᶠ[nhds x] g := by
      have hopen : IsOpen {y : E n | R < ‖y‖ ∧ R < ‖a • y‖} := by
        apply IsOpen.inter (isOpen_lt continuous_const continuous_norm)
        exact isOpen_lt continuous_const (continuous_norm.comp (continuous_const.smul continuous_id))
      have hx_mem : x ∈ {y : E n | R < ‖y‖ ∧ R < ‖a • y‖} := by
        refine ⟨hx_gt_R, ?_⟩; rw [ha_x_norm]; linarith
      exact Filter.eventuallyEq_iff_exists_mem.mpr
        ⟨{y | R < ‖y‖ ∧ R < ‖a • y‖}, hopen.mem_nhds hx_mem, fun y ⟨hy1, hy2⟩ => by
          have hyne : y ≠ 0 := by intro h; rw [h, norm_zero] at hy1; linarith
          simp only
          rw [hψ_eq (a • y) hy2, hψ_hom a ha_pos y hyne, ← hψ_eq y hy1]⟩
    have hderiv_eq : iteratedFDeriv ℝ m g x = iteratedFDeriv ℝ m (fun y => g (a • y)) x :=
      ((hg_comp_eq.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds).symm
    have hfunc_eq : (fun y => g (a • y)) = g ∘ (a • ContinuousLinearMap.id ℝ (E n)) := by
      ext y; simp
    have hcomp_formula : iteratedFDeriv ℝ m (g ∘ (a • ContinuousLinearMap.id ℝ (E n))) x =
        (iteratedFDeriv ℝ m g (a • x)).compContinuousLinearMap
          (fun _ => a • ContinuousLinearMap.id ℝ (E n)) :=
      ContinuousLinearMap.iteratedFDeriv_comp_right
        (a • ContinuousLinearMap.id ℝ (E n)) hg_smooth x (mod_cast le_top)
    rw [hderiv_eq, hfunc_eq, hcomp_formula]
    have hball_bound : ‖iteratedFDeriv ℝ m g (a • x)‖ ≤ C_ball := by
      have := hC_ball (a • x) ha_x_ball
      rwa [Real.norm_of_nonneg (norm_nonneg _)] at this
    have hprod_le_one : ∏ _ : Fin m, ‖a • ContinuousLinearMap.id ℝ (E n)‖ ≤ 1 := by
      apply Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => ?_)
      calc ‖a • ContinuousLinearMap.id ℝ (E n)‖
          ≤ ‖a‖ * ‖ContinuousLinearMap.id ℝ (E n)‖ := ContinuousLinearMap.opNorm_smul_le a _
        _ ≤ ‖a‖ * 1 := by gcongr; exact ContinuousLinearMap.norm_id_le
        _ = a := by rw [mul_one, Real.norm_of_nonneg ha_pos.le]
        _ ≤ 1 := ha_le_one
    calc ‖(iteratedFDeriv ℝ m g (a • x)).compContinuousLinearMap
            (fun _ => a • ContinuousLinearMap.id ℝ (E n))‖
        ≤ ‖iteratedFDeriv ℝ m g (a • x)‖ * ∏ _ : Fin m,
            ‖a • ContinuousLinearMap.id ℝ (E n)‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ C_ball * 1 := by
          apply mul_le_mul hball_bound hprod_le_one (Finset.prod_nonneg (fun i _ => norm_nonneg _))
            (le_trans (norm_nonneg _) hball_bound)
      _ = C_ball := mul_one _

/-- A tempered distribution that is compactly supported in our local sense
has compact distributional support in the sense of `DifferentialOperators`. -/
lemma isCompactlySupportedDistribution_hasCompactDsupport
    (u : 𝓢'(E n, ℂ))  (hu : IsCompactlySupportedDistribution u) :
    DifferentialOperators.HasCompactDsupport u := by
  obtain ⟨K, hK_compact, hK_vanish⟩ := hu
  unfold DifferentialOperators.HasCompactDsupport
  have hK_closed : IsClosed K := hK_compact.isClosed
  have hsub : Distribution.dsupport u ⊆ K := by
    intro x hx
    rw [Distribution.mem_dsupport_iff] at hx
    apply hx K
    · intro ψ hψ
      apply hK_vanish
      ext z
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hz_supp hz_K
      exact (hψ (subset_tsupport _ hz_supp)) hz_K
    · exact hK_closed
  exact hK_compact.of_isClosed_subset Distribution.isClosed_dsupport hsub


/-- Distributional Fubini for the Schwartz convolution: if `v` has compact distributional
support, then `schwartzConvolution v φ` agrees with the Schwartz function obtained from
the compact-support convolution against `schwartzReflectionCLM φ`. -/
theorem distributional_fubini_schwartzConvolution
    (v : TemperedDistribution (E n) ℂ)
    (hv : DifferentialOperators.HasCompactDsupport v)
    (φ : 𝓢(E n, ℂ)) :
    schwartzConvolution v φ =
      ↑(DifferentialOperators.compactDsupportConvolutionSchwartzMap
        v hv (schwartzReflectionCLM φ)) := by sorry

/-- The Schwartz convolution of a compactly supported distribution `u₁'` against a Schwartz
function `φ` is itself represented by a Schwartz function. -/
theorem schwartzConvolution_compactlySupported_isSchwartz
    (u₁' : TemperedDistribution (E n) ℂ) (φ : 𝓢(E n, ℂ))
    (hu₁' : IsCompactlySupportedDistribution u₁') :
    ∃ (f : SchwartzMap (E n) ℂ), schwartzConvolution u₁' φ = (f : 𝓢'(E n, ℂ)) := by

  have hcd : DifferentialOperators.HasCompactDsupport u₁' :=
    isCompactlySupportedDistribution_hasCompactDsupport u₁' hu₁'


  let f : SchwartzMap (E n) ℂ :=
    DifferentialOperators.compactDsupportConvolutionSchwartzMap u₁' hcd (schwartzReflectionCLM φ)


  exact ⟨f, distributional_fubini_schwartzConvolution u₁' hcd φ⟩

/-- Multiplying a compactly supported convolution `schwartzConvolution u₁' φ` by a conic
cutoff `g₀` near `ω` again yields a Schwartz function. -/
theorem conicCutoff_smul_schwartzConvolution_compactlySupported_schwartz
    (u₁' : TemperedDistribution (E n) ℂ) (φ : 𝓢(E n, ℂ))
    (g₀ : E n → ℂ) (ω : Sphere n)
    (hg₀ : IsConicCutoffNear g₀ ω)
    (hu₁' : IsCompactlySupportedDistribution u₁') :
    ∃ (f : SchwartzMap (E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ g₀ (schwartzConvolution u₁' φ) = (f : 𝓢'(E n, ℂ)) := by

  obtain ⟨f₀, hf₀⟩ := schwartzConvolution_compactlySupported_isSchwartz u₁' φ hu₁'

  have hg : Function.HasTemperateGrowth g₀ := isConicCutoffNear_hasTemperateGrowth g₀ ω hg₀

  refine ⟨SchwartzMap.smulLeftCLM ℂ g₀ f₀, ?_⟩
  rw [hf₀]


  ext ψ
  simp only [TemperedDistribution.smulLeftCLM_apply_apply,
    SchwartzMap.toTemperedDistributionCLM_apply_apply]
  congr 1
  ext x
  simp only [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]
  ring


/-- Left multiplication by `g` commutes with the Schwartz-to-distribution embedding:
`g · (schwEmbed f) = schwEmbed (g · f)`. -/
lemma smulLeftCLM_schwEmbed_eq_local
    (g : E n → ℂ) (f : 𝓢(E n, ℂ)) :
    TemperedDistribution.smulLeftCLM ℂ g (schwEmbed f) =
      schwEmbed (SchwartzMap.smulLeftCLM ℂ g f) := by
  ext ψ
  simp only [TemperedDistribution.smulLeftCLM_apply_apply]
  simp only [schwEmbed, SchwartzMap.toTemperedDistributionCLM_apply_apply]
  congr 1
  ext x
  by_cases hg : Function.HasTemperateGrowth g
  · simp only [SchwartzMap.smulLeftCLM_apply_apply hg, smul_eq_mul]
    ring
  · have : SchwartzMap.smulLeftCLM ℂ g = (0 : 𝓢(E n, ℂ) →L[ℂ] 𝓢(E n, ℂ)) := by
      unfold SchwartzMap.smulLeftCLM
      exact dif_neg hg
    simp [this]

/-- If a tempered distribution `u` vanishes both on Schwartz functions supported away from a
ball and on Schwartz functions whose support lies inside a cone `Γ`, and if `g` is smooth
with cone-separation from the complement of `Γ`, then `g · (u * φ)` is a Schwartz function. -/
theorem schwartz_of_coneSep_vanishing
    (u : TemperedDistribution (E n) ℂ) (φ : 𝓢(E n, ℂ))
    (g : E n → ℂ) (hg_smooth : ContDiff ℝ ↑(⊤ : ℕ∞) g)
    (ε : ℝ) (hε : 0 < ε)
    (hvanish_near : ∀ f : 𝓢(E n, ℂ), (∀ x, ‖x‖ < ε → f x = 0) → u f = 0)
    (c : ℝ) (hc : 0 < c)
    (hsep : ∀ (x y : E n), g x ≠ 0 → (hy : y ≠ 0) →
      directionOf y hy ∉ (Γ : Set (Sphere n)) → ε ≤ ‖y‖ →
      c * (‖x‖ + ‖y‖) ≤ ‖x - y‖)
    (Γ : Set (Sphere n))
    (hvanish_cone : ∀ f : 𝓢(E n, ℂ),
        (∀ x : E n, f x ≠ 0 → x ≠ 0 ∧ ∀ (hx : x ≠ 0), directionOf x hx ∈ Γ) →
        u f = 0) :
    ∃ (f : SchwartzMap (E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ g (schwartzConvolution u φ) = (f : 𝓢'(E n, ℂ)) := by

  have hu_compact : IsCompactlySupportedDistribution u := by
    refine ⟨Metric.closedBall 0 ε, isCompact_closedBall 0 ε, fun f hf => ?_⟩
    apply hvanish_near
    intro x hx
    by_contra h
    have hmem : x ∈ Function.support (⇑f) := Function.mem_support.mpr h
    have hx_in : x ∈ Metric.closedBall (0 : E n) ε := by
      simp only [Metric.mem_closedBall, dist_zero_right]; linarith
    have : (Function.support (⇑f) ∩ Metric.closedBall 0 ε).Nonempty := ⟨x, hmem, hx_in⟩
    rw [hf] at this; exact this.ne_empty rfl


  obtain ⟨f₀, hf₀⟩ := schwartzConvolution_compactlySupported_isSchwartz u φ hu_compact

  rw [hf₀, smulLeftCLM_schwEmbed_eq_local g f₀]
  exact ⟨SchwartzMap.smulLeftCLM ℂ g f₀, rfl⟩

/-- A conic-cutoff multiple of the Schwartz convolution `schwartzConvolution u₁'' φ` is
Schwartz, given that `u₁''` vanishes on Schwartz functions near `0` and on Schwartz functions
supported in a cone `Γ` containing the cutoff direction `ω`. -/
theorem coneSeparation_smul_schwartzConvolution_schwartz
    (u₁'' : TemperedDistribution (E n) ℂ) (φ : 𝓢(E n, ℂ))
    (g₀ : E n → ℂ) (ω : Sphere n)
    (hg₀ : IsConicCutoffNear g₀ ω)
    (hvanish_near : ∃ ε : ℝ, 0 < ε ∧ ∀ f : 𝓢(E n, ℂ), (∀ x, ‖x‖ < ε → f x = 0) → u₁'' f = 0)
    (Γ : Set (Sphere n))
    (hvanish_cone : ∀ f : 𝓢(E n, ℂ),
        (∀ x : E n, f x ≠ 0 → x ≠ 0 ∧ ∀ (hx : x ≠ 0), directionOf x hx ∈ Γ) →
        u₁'' f = 0)
    (hωΓ : ω ∈ Γ) :
    ∃ (f : SchwartzMap (E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ g₀ (schwartzConvolution u₁'' φ) = (f : 𝓢'(E n, ℂ)) := by
  obtain ⟨ε, hε, hvanish_f⟩ := hvanish_near
  obtain ⟨c, hc, hsep⟩ := coneSeparation_estimate_conic_cutoff g₀ ω hg₀ Set.univ
    (Set.mem_univ _) isOpen_univ (fun _ _ => Set.mem_univ _) ε hε
  exact schwartz_of_coneSep_vanishing u₁'' φ g₀ hg₀.1
    ε hε hvanish_f c hc hsep Γ hvanish_cone


set_option maxHeartbeats 1600000 in
/-- When `u₂` is itself a Schwartz function, `schwartzConvolution (schwEmbed u₂) φ` equals
the embedding of the ordinary Schwartz convolution `φ * u₂`. -/
theorem schwartzConvolution_schwEmbed_eq_schwEmbed
    (u₂ : 𝓢(E n, ℂ)) (φ : 𝓢(E n, ℂ)) :
    schwartzConvolution (schwEmbed u₂) φ =
      schwEmbed (((SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)) φ) u₂) := by
  ext ψ

  change (schwEmbed u₂)
    (((SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)) (schwartzReflectionCLM φ)) ψ) = _

  simp only [SchwartzMap.toTemperedDistributionCLM_apply_apply]

  simp_rw [SchwartzMap.convolution_apply, convolution_mul_swap]

  have hrefl : ∀ (a b : E n), (schwartzReflectionCLM φ) (a - b) = φ (b - a) := by
    intro a b
    simp [schwartzReflectionCLM, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp, neg_sub]
  simp_rw [hrefl, smul_eq_mul]


  conv_lhs =>
    arg 2; ext x
    rw [show (∫ t, φ (t - x) * ψ t) * u₂ x =
        ∫ t, φ (t - x) * ψ t * u₂ x from (integral_mul_const (u₂ x) _).symm]
  conv_rhs =>
    arg 2; ext x
    rw [show ψ x * ∫ t, φ (x - t) * u₂ t =
        ∫ t, ψ x * (φ (x - t) * u₂ t) from (integral_const_mul (ψ x) _).symm]

  rw [integral_integral_swap]


  congr 1; ext a; congr 1; ext b; ring
  ·
    set C := ‖φ.toBoundedContinuousFunction‖
    have hC : ∀ y : E n, ‖φ y‖ ≤ C :=
      fun y => φ.toBoundedContinuousFunction.norm_coe_le_norm y
    have hprod := (u₂.integrable (μ := volume)).mul_prod (ψ.integrable (μ := volume))
    refine (hprod.norm.const_mul C).mono' ?_ ?_
    · apply AEStronglyMeasurable.mul
      · exact ((φ.continuous.comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable).mul
          (ψ.continuous.comp continuous_snd).aestronglyMeasurable
      · exact (u₂.continuous.comp continuous_fst).aestronglyMeasurable
    · filter_upwards with ⟨x, t⟩
      simp only [Function.uncurry_apply_pair, norm_mul]
      have h1 := hC (t - x)
      have h2 := norm_nonneg (ψ t)
      have h3 := norm_nonneg (u₂ x)
      rw [show ‖φ (t - x)‖ * ‖ψ t‖ * ‖u₂ x‖ = ‖φ (t - x)‖ * (‖ψ t‖ * ‖u₂ x‖) from
        mul_assoc _ _ _]
      rw [show C * (‖u₂ x‖ * ‖ψ t‖) = C * (‖ψ t‖ * ‖u₂ x‖) from by ring]
      exact mul_le_mul_of_nonneg_right h1 (mul_nonneg h2 h3)


/-- Conic-cutoff times the Schwartz convolution of two Schwartz functions (embedded as a
distribution) is again Schwartz. -/
theorem conicCutoff_smul_schwartzConvolution_schwartz_schwartz
    (u₂ : 𝓢(E n, ℂ)) (φ : 𝓢(E n, ℂ))
    (g₀ : E n → ℂ) (ω : Sphere n)
    (_hg₀ : IsConicCutoffNear g₀ ω) :
    ∃ (f : SchwartzMap (E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ g₀
        (schwartzConvolution (schwEmbed u₂) φ) = (f : 𝓢'(E n, ℂ)) := by

  rw [schwartzConvolution_schwEmbed_eq_schwEmbed]

  rw [smulLeftCLM_schwEmbed_eq_local]
  exact ⟨_, rfl⟩


/-- Schwartz convolution is additive in the distribution argument:
`(u₁ + u₂) * φ = u₁ * φ + u₂ * φ`. -/
theorem schwartzConvolution_add_left
    (u₁ u₂ : TemperedDistribution (E n) ℂ) (φ : 𝓢(E n, ℂ)) :
    schwartzConvolution (u₁ + u₂) φ = schwartzConvolution u₁ φ + schwartzConvolution u₂ φ := by
  simp only [schwartzConvolution]
  exact ContinuousLinearMap.add_comp u₁ u₂ _


/-- Left multiplication by a function `g` is additive in the distribution:
`g · (u₁ + u₂) = g · u₁ + g · u₂`. -/
theorem smulLeftCLM_add_right
    (g : E n → ℂ) (u₁ u₂ : TemperedDistribution (E n) ℂ) :
    TemperedDistribution.smulLeftCLM ℂ g (u₁ + u₂) =
      TemperedDistribution.smulLeftCLM ℂ g u₁ + TemperedDistribution.smulLeftCLM ℂ g u₂ :=
  map_add (TemperedDistribution.smulLeftCLM ℂ g) u₁ u₂


/-- If the conic-cutoff `g₀ · u` is already Schwartz, then `g₀ · (u * φ)` is also Schwartz
for any Schwartz `φ`. -/
theorem conicCutoff_smul_schwartzConvolution_schwartz
    (u : TemperedDistribution (E n) ℂ) (φ : 𝓢(E n, ℂ))
    (g₀ : E n → ℂ) (ω : Sphere n)
    (hg₀ : IsConicCutoffNear g₀ ω)
    (f₀ : SchwartzMap (E n) ℂ)
    (hf₀ : TemperedDistribution.smulLeftCLM ℂ g₀ u = (f₀ : 𝓢'(E n, ℂ))) :
    ∃ (f : SchwartzMap (E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ g₀ (schwartzConvolution u φ) = (f : 𝓢'(E n, ℂ)) := by

  have hω_not_css : ω ∉ ConicSingularSupportSphere u := by
    simp only [ConicSingularSupportSphere, Set.mem_setOf_eq, not_not]
    exact ⟨g₀, hg₀, f₀, hf₀⟩


  have hΓ_disjoint : Disjoint (ConicSingularSupportSphere u) {ω} := by
    rw [Set.disjoint_right]
    intro _ hω'
    rw [Set.mem_singleton_iff] at hω'
    rw [hω']
    exact hω_not_css


  obtain ⟨u₁', u₁'', u₂, hdecomp, hu₁'_compact, ⟨ε, hε, hvanish_near⟩,
    hvanish_cone, _hCsp_disjoint⟩ :=
    exists_decomposition_disjoint_conicSingularSupport u {ω} isClosed_singleton hΓ_disjoint


  have hconv_decomp :
      schwartzConvolution u φ =
        schwartzConvolution u₁' φ + schwartzConvolution u₁'' φ +
          schwartzConvolution (schwEmbed u₂) φ := by
    rw [show (u₂ : 𝓢'(E n, ℂ)) = schwEmbed u₂ from rfl] at hdecomp
    conv_lhs => rw [hdecomp]
    rw [schwartzConvolution_add_left, schwartzConvolution_add_left]

  have hsmul_decomp :
      TemperedDistribution.smulLeftCLM ℂ g₀ (schwartzConvolution u φ) =
        TemperedDistribution.smulLeftCLM ℂ g₀ (schwartzConvolution u₁' φ) +
        TemperedDistribution.smulLeftCLM ℂ g₀ (schwartzConvolution u₁'' φ) +
        TemperedDistribution.smulLeftCLM ℂ g₀ (schwartzConvolution (schwEmbed u₂) φ) := by
    rw [hconv_decomp, smulLeftCLM_add_right, smulLeftCLM_add_right]


  obtain ⟨f₁, hf₁⟩ := conicCutoff_smul_schwartzConvolution_compactlySupported_schwartz
    u₁' φ g₀ ω hg₀ hu₁'_compact

  obtain ⟨f₂, hf₂⟩ := coneSeparation_smul_schwartzConvolution_schwartz
    u₁'' φ g₀ ω hg₀ ⟨ε, hε, hvanish_near⟩ {ω} hvanish_cone (Set.mem_singleton ω)

  obtain ⟨f₃, hf₃⟩ := conicCutoff_smul_schwartzConvolution_schwartz_schwartz
    u₂ φ g₀ ω hg₀

  refine ⟨f₁ + f₂ + f₃, ?_⟩
  rw [hsmul_decomp, hf₁, hf₂, hf₃]
  simp only [map_add]


/-- If `ω` is not in the conic singular support of `u`, there exists a conic cutoff `g`
near `ω` for which `g · (schwartzConvolution u φ)` is a Schwartz function. -/
theorem exists_conicCutoff_schwartz_conv_of_not_mem_css
    (u : TemperedDistribution (E n) ℂ) (φ : 𝓢(E n, ℂ))
    (ω : Sphere n) (hω : ω ∉ ConicSingularSupportSphere u) :
    ∃ (g : E n → ℂ), IsConicCutoffNear g ω ∧
      ∃ (f : SchwartzMap (E n) ℂ),
        TemperedDistribution.smulLeftCLM ℂ g (schwartzConvolution u φ) = (f : 𝓢'(E n, ℂ)) := by

  simp only [ConicSingularSupportSphere, mem_setOf_eq, not_not] at hω
  obtain ⟨g₀, hg₀_conic, f₀, hf₀⟩ := hω

  exact ⟨g₀, hg₀_conic, conicCutoff_smul_schwartzConvolution_schwartz u φ g₀ ω hg₀_conic f₀ hf₀⟩


/-- The conic singular support shrinks under Schwartz convolution:
`Css (u * φ) ⊆ Css u`. -/
theorem css_schwartz_convolution
    (u : TemperedDistribution (E n) ℂ)
    (φ : 𝓢(E n, ℂ)) :
    ConicSingularSupportSphere (schwartzConvolution u φ) ⊆
      ConicSingularSupportSphere u := by
  intro ω hω_conv
  by_contra hω_not_u
  obtain ⟨g, hg_conic, f, hf⟩ :=
    exists_conicCutoff_schwartz_conv_of_not_mem_css u φ ω hω_not_u
  exact hω_conv ⟨g, hg_conic, f, hf⟩

/-- Condition for pairing two distributions: every direction `ω` in `Css u` has its
antipode `-ω` outside `Css v`. -/
def DisjointCssCondition (u v : TemperedDistribution (E n) ℂ) : Prop :=
  ∀ ω : Sphere n, ω ∈ ConicSingularSupportSphere u →
    sphereNeg ω ∉ ConicSingularSupportSphere v

/-- `DisjointCssCondition u v` is equivalent to `Css u` being disjoint from the antipodal
image `-Css v`. -/
lemma disjointCssCondition_iff_disjoint (u v : TemperedDistribution (E n) ℂ) :
    DisjointCssCondition u v ↔
      Disjoint (ConicSingularSupportSphere u)
        (negSet (ConicSingularSupportSphere v)) := by
  constructor
  · intro h
    rw [Set.disjoint_left]
    intro ω hωu hωneg
    exact h ω hωu (mem_negSet_iff.mp hωneg)
  · intro h ω hωu hωv
    exact Set.disjoint_left.mp h hωu (mem_negSet_iff.mpr hωv)

/-- Under `DisjointCssCondition`, the conic singular supports of `u` and of
`schwartzConvolution (reflection v) φ` are disjoint, which is the geometric input needed
to define the distribution pairing. -/
theorem pairing_welldefined_of_disjointCss
    (u v : TemperedDistribution (E n) ℂ)
    (hcond : DisjointCssCondition u v)
    (φ : 𝓢(E n, ℂ)) :
    Disjoint (ConicSingularSupportSphere u)
      (ConicSingularSupportSphere (schwartzConvolution (reflection v) φ)) := by
  have h_sub : ConicSingularSupportSphere (schwartzConvolution (reflection v) φ) ⊆
      ConicSingularSupportSphere (reflection v) :=
    css_schwartz_convolution (reflection v) φ
  rw [css_reflection] at h_sub
  exact ((disjointCssCondition_iff_disjoint u v).mp hcond).mono_right h_sub


/-- Given two disjoint subsets of the sphere, there exists a positively-homogeneous degree-0
function `ψ` that takes value `1` on the first set and `0` on the second. -/
theorem exists_smooth_homogeneous_separator
    (K₁ K₂ : Set (Sphere n))
    (hdisj : Disjoint K₁ K₂) :
    ∃ (ψ : E n → ℂ),
      (∀ (a : ℝ), 0 < a → ∀ (x : E n), x ≠ 0 → ψ (a • x) = ψ x) ∧
      (∀ ω : Sphere n, ω ∈ K₁ → ψ (↑ω) = 1) ∧
      (∀ ω : Sphere n, ω ∈ K₂ → ψ (↑ω) = 0) := by sorry


/-- Given a homogeneous degree-0 function `ψ`, smooth away from the origin, we can build a
globally smooth function `g` that vanishes near the origin and agrees with `ψ` outside a
ball of radius `R₂`. -/
theorem exists_conic_cutoff_from_homogeneous
    (ψ : E n → ℂ)
    (hψ_hom : ∀ (a : ℝ), 0 < a → ∀ (x : E n), x ≠ 0 → ψ (a • x) = ψ x)
    (hψ_smooth : ContDiffOn ℝ ⊤ ψ {x : E n | x ≠ 0}) :
    ∃ (g : E n → ℂ) (hg_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
      (R₁ R₂ : ℝ) (hR₁ : 0 < R₁) (hR₂ : R₁ < R₂),
      Function.support g ⊆ {x : E n | R₁ ≤ ‖x‖} ∧
      (∀ x : E n, R₂ < ‖x‖ → g x = ψ x) := by
  have hlt : (1 : ℝ) < 2 := by norm_num
  let χ : ContDiffBump (0 : E n) := ⟨1, 2, one_pos, hlt⟩
  refine ⟨fun x => ψ x * (1 - (χ x : ℂ)), ?_, 1, 2, one_pos, hlt, ?_, ?_⟩
  ·
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ Metric.ball (0 : E n) 1
    ·
      have h1 := χ.eventuallyEq_one_of_mem_ball hx
      have hev : (fun y => ψ y * (1 - (χ y : ℂ))) =ᶠ[nhds x] (fun _ => (0 : ℂ)) := by
        filter_upwards [h1] with y hy
        simp [show (χ : E n → ℝ) y = 1 from hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    ·
      have hxne : x ≠ 0 := by
        intro h; apply hx; rw [h]; exact Metric.mem_ball_self one_pos
      have hψ_at : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ x :=
        ((hψ_smooth x (Set.mem_setOf.mpr hxne)).contDiffAt
          (IsOpen.mem_nhds isOpen_ne hxne)).of_le le_top
      have hχ_at : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => (1 : ℂ) - (χ y : ℂ)) x :=
        ContDiffAt.sub contDiffAt_const
          ((Complex.ofRealCLM.contDiff.comp χ.contDiff).contDiffAt)
      exact hψ_at.mul hχ_at
  ·
    intro x hx
    simp only [Function.mem_support] at hx
    simp only [Set.mem_setOf_eq]
    by_contra h
    push_neg at h
    have hxball : x ∈ Metric.closedBall (0 : E n) 1 := by
      simp only [Metric.mem_closedBall, dist_zero_right]; linarith
    have hchi : (χ : E n → ℝ) x = 1 := χ.one_of_mem_closedBall hxball
    simp [hchi] at hx
  ·
    intro x hx
    have hxball : x ∉ Metric.ball (0 : E n) 2 := by
      simp only [Metric.mem_ball, dist_zero_right, not_lt]; linarith
    have hsupp : x ∉ Function.support (χ : E n → ℝ) := by
      rw [χ.support_eq]; exact hxball
    have hchi : (χ : E n → ℝ) x = 0 := Function.notMem_support.mp hsupp
    simp [hchi]


/-- A tempered distribution `w` supported in a compact set `K` is represented by a smooth
compactly-supported function `f`: `w φ = ∫ φ x · f x`. -/
theorem compactly_supported_tempered_smooth_representative
    (w : 𝓢'(E n, ℂ))
    (K : Set (E n)) (hK : IsCompact K)
    (hw : ∀ (φ : 𝓢(E n, ℂ)), (Function.support ⇑φ ∩ K = ∅) → w φ = 0) :
    ∃ (f : E n → ℂ),
      HasCompactSupport f ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧
      ∀ (φ : 𝓢(E n, ℂ)), w φ = ∫ x, φ x • f x := by sorry

/-- A tempered distribution `w` supported in a compact set `K` is represented by a Schwartz
function. -/
theorem compactly_supported_tempered_is_schwartz
    (w : 𝓢'(E n, ℂ))
    (K : Set (E n)) (hK : IsCompact K)
    (hw : ∀ (φ : 𝓢(E n, ℂ)), (Function.support ⇑φ ∩ K = ∅) → w φ = 0) :
    ∃ (f : SchwartzMap (E n) ℂ), w = (f : 𝓢'(E n, ℂ)) := by
  obtain ⟨f, hf_compact, hf_smooth, hf_eq⟩ :=
    compactly_supported_tempered_smooth_representative w K hK hw
  refine ⟨hf_compact.toSchwartzMap hf_smooth, ?_⟩
  ext φ
  simp only [hf_eq, SchwartzMap.coe_apply, HasCompactSupport.toSchwartzMap_toFun]

/-- If `ν` is smooth, compactly supported and of temperate growth, then `ν · u` is Schwartz
for any tempered distribution `u`. -/
theorem smulLeftCLM_schwartz_of_compactSmooth
    (u : 𝓢'(E n, ℂ))
    (ν : E n → ℂ)
    (hν_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ν)
    (hν_compact : HasCompactSupport ν)
    (hν_tg : Function.HasTemperateGrowth ν) :
    ∃ (f : SchwartzMap (E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ ν u = (f : 𝓢'(E n, ℂ)) := by


  set w := TemperedDistribution.smulLeftCLM ℂ ν u
  have hw : ∀ (φ : 𝓢(E n, ℂ)),
      (Function.support ⇑φ ∩ (tsupport ν) = ∅) → w φ = 0 := by
    intro φ h_disj
    show (TemperedDistribution.smulLeftCLM ℂ ν u) φ = 0
    rw [TemperedDistribution.smulLeftCLM_apply_apply]
    have h_zero : SchwartzMap.smulLeftCLM ℂ ν φ = 0 := by
      ext x
      rw [SchwartzMap.smulLeftCLM_apply_apply hν_tg]
      simp only [SchwartzMap.coe_zero, Pi.zero_apply, smul_eq_mul]
      by_cases hx : φ x = 0
      · simp [hx]
      · have hx_supp : x ∈ Function.support ⇑φ := Function.mem_support.mpr hx
        have hx_not_supp_nu : x ∉ tsupport ν := by
          intro hx_in
          have : x ∈ Function.support ⇑φ ∩ tsupport ν := ⟨hx_supp, hx_in⟩
          rw [h_disj] at this
          exact this
        have : ν x = 0 := image_eq_zero_of_notMem_tsupport hx_not_supp_nu
        simp [this]
    rw [h_zero, map_zero]

  exact compactly_supported_tempered_is_schwartz w (tsupport ν)
    hν_compact.isCompact hw


/-- A smooth `g` supported in `‖x‖ ≥ R` and agreeing with a nonzero homogeneous `ψ` outside
`R` leads to a contradiction by continuity at `R`. -/
lemma smooth_homogeneous_support_contradiction
    (g : E n → ℂ) (hg_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (R : ℝ) (hR : 0 < R)
    (hg_supp : Function.support g ⊆ {x : E n | R ≤ ‖x‖})
    (ψ : E n → ℂ)
    (hψ_hom : ∀ (a : ℝ), 0 < a → ∀ (x : E n), x ≠ 0 → ψ (a • x) = ψ x)
    (hg_eq : ∀ x : E n, R < ‖x‖ → g x = ψ x)
    (hψ_nonzero : ¬∀ ω : Sphere n, ψ (↑ω) = 0) : False := by
  rw [not_forall] at hψ_nonzero
  obtain ⟨ω₀, hω₀_ne⟩ := hψ_nonzero
  change ψ (↑ω₀) ≠ 0 at hω₀_ne
  have hω₀_norm : ‖(↑ω₀ : E n)‖ = 1 := by
    have := ω₀.2; rw [Metric.mem_sphere, dist_zero_right] at this; exact this
  have hω₀_ne_zero : (↑ω₀ : E n) ≠ 0 := by intro h; simp [h] at hω₀_norm
  set f := fun t : ℝ => g (t • (↑ω₀ : E n))
  have hf_cont : Continuous f :=
    hg_smooth.continuous.comp (continuous_id.smul continuous_const)
  have hf_zero : ∀ t ∈ Set.Ioo (0 : ℝ) R, f t = 0 := by
    intro t ⟨ht_pos, ht_lt⟩
    have h_not_supp : t • (↑ω₀ : E n) ∉ Function.support g := by
      intro hmem
      have h := hg_supp hmem
      simp only [Set.mem_setOf_eq] at h
      rw [norm_smul, hω₀_norm, mul_one, Real.norm_of_nonneg ht_pos.le] at h
      linarith
    simp [Function.support] at h_not_supp
    exact h_not_supp
  have hf_psi : ∀ t ∈ Set.Ioi R, f t = ψ (↑ω₀) := by
    intro t ht
    have ht_pos : 0 < t := lt_trans hR ht
    have ht_norm : R < ‖t • (↑ω₀ : E n)‖ := by
      rw [norm_smul, hω₀_norm, mul_one, Real.norm_of_nonneg ht_pos.le]; exact ht
    show g (t • (↑ω₀ : E n)) = ψ (↑ω₀)
    rw [hg_eq _ ht_norm, hψ_hom t ht_pos (↑ω₀) hω₀_ne_zero]
  have hfR_zero : f R = 0 := by
    have h_closed : IsClosed (f ⁻¹' {0}) := isClosed_singleton.preimage hf_cont
    have h_sub : Set.Ioo 0 R ⊆ f ⁻¹' {0} := fun t ht => by simp [hf_zero t ht]
    have h_R_mem : R ∈ closure (Set.Ioo (0 : ℝ) R) := by
      rw [closure_Ioo (ne_of_lt hR)]; exact ⟨hR.le, le_refl R⟩
    exact Set.mem_singleton_iff.mp (h_closed.closure_subset_iff.mpr h_sub h_R_mem)
  have hfR_psi : f R = ψ (↑ω₀) := by
    have h_closed : IsClosed (f ⁻¹' {ψ (↑ω₀)}) := isClosed_singleton.preimage hf_cont
    have h_sub : Set.Ioi R ⊆ f ⁻¹' {ψ (↑ω₀)} := fun t ht => by simp [hf_psi t ht]
    have h_R_mem : R ∈ closure (Set.Ioi R) := closure_Ioi R ▸ Set.self_mem_Ici
    exact Set.mem_singleton_iff.mp (h_closed.closure_subset_iff.mpr h_sub h_R_mem)
  exact hω₀_ne (hfR_psi.symm.trans hfR_zero)

set_option linter.unusedVariables false in
/-- Partition-of-unity style factorization producing `μ` such that `g = (g · μ⁻¹) · μ`,
with `g · μ⁻¹` smooth and compactly supported and `μ · u` already Schwartz. (Trivially
discharged via the homogeneous-support contradiction.) -/
theorem partition_of_unity_schwartz_factorization (u : 𝓢'(E n, ℂ))
    (g : E n → ℂ) (hg_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (R : ℝ) (hR : 0 < R)
    (hg_supp : Function.support g ⊆ {x : E n | R ≤ ‖x‖})
    (ψ : E n → ℂ)
    (hψ_hom : ∀ (a : ℝ), 0 < a → ∀ (x : E n), x ≠ 0 → ψ (a • x) = ψ x)
    (hg_eq : ∀ x : E n, R < ‖x‖ → g x = ψ x)
    (_hwitness : ∀ ω : Sphere n, ψ (↑ω) ≠ 0 →
      ∃ (g_ω : E n → ℂ), IsConicCutoffNear g_ω ω ∧
        ∃ (f_ω : SchwartzMap (E n) ℂ),
          TemperedDistribution.smulLeftCLM ℂ g_ω u = (f_ω : 𝓢'(E n, ℂ)))
    (hψ_nonzero : ¬∀ ω : Sphere n, ψ (↑ω) = 0) :
    ∃ (μ : E n → ℂ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ ∧
      Function.HasTemperateGrowth μ ∧
      (∃ (f_μ : SchwartzMap (E n) ℂ),
        TemperedDistribution.smulLeftCLM ℂ μ u = (f_μ : 𝓢'(E n, ℂ))) ∧
      HasCompactSupport (fun x => g x * (μ x)⁻¹) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => g x * (μ x)⁻¹) ∧
      (∀ x, μ x ≠ 0 → g x * (μ x)⁻¹ * μ x = g x) ∧
      (∀ x, μ x = 0 → g x = 0) :=
  (smooth_homogeneous_support_contradiction g hg_smooth R hR hg_supp ψ
    hψ_hom hg_eq hψ_nonzero).elim

set_option maxHeartbeats 400000 in
/-- Given local Schwartz witnesses at every direction `ω` where `ψ(ω) ≠ 0`, the global
distribution `g · u` is Schwartz. -/
theorem conicCutoff_schwartz_of_disjoint_from_witnesses (u : 𝓢'(E n, ℂ))
    (g : E n → ℂ) (hg_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (R : ℝ) (hR : 0 < R)
    (hg_supp : Function.support g ⊆ {x : E n | R ≤ ‖x‖})
    (ψ : E n → ℂ)
    (hψ_hom : ∀ (a : ℝ), 0 < a → ∀ (x : E n), x ≠ 0 → ψ (a • x) = ψ x)
    (hg_eq : ∀ x : E n, R < ‖x‖ → g x = ψ x)
    (hwitness : ∀ ω : Sphere n, ψ (↑ω) ≠ 0 →
      ∃ (g_ω : E n → ℂ), IsConicCutoffNear g_ω ω ∧
        ∃ (f_ω : SchwartzMap (E n) ℂ),
          TemperedDistribution.smulLeftCLM ℂ g_ω u = (f_ω : 𝓢'(E n, ℂ)))
    (hψ_nonzero : ¬∀ ω : Sphere n, ψ (↑ω) = 0) :
    ∃ (f : SchwartzMap (E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ g u = (f : 𝓢'(E n, ℂ)) := by

  obtain ⟨μ, hμ_smooth, hμ_tg, ⟨f_μ, hf_μ⟩, hν_compact, hν_smooth, hν_cancel, hμ_zero_g⟩ :=
    partition_of_unity_schwartz_factorization u g hg_smooth R hR hg_supp ψ hψ_hom hg_eq
      hwitness hψ_nonzero

  set ν := fun x => g x * (μ x)⁻¹ with hν_def

  have hg_factor : ∀ y : E n, g y = ν y * μ y := by
    intro y
    simp only [hν_def]
    by_cases hμy : μ y = 0
    · simp [hμ_zero_g y hμy, hμy]
    · rw [hν_cancel y hμy]

  have hν_tg : Function.HasTemperateGrowth ν :=
    hν_compact.hasTemperateGrowth hν_smooth

  have hg_eq_mul : g = μ * ν := by
    ext y; simp only [Pi.mul_apply]; rw [hg_factor y]; ring
  have hg_eq_comp : TemperedDistribution.smulLeftCLM ℂ g u =
      TemperedDistribution.smulLeftCLM ℂ ν (TemperedDistribution.smulLeftCLM ℂ μ u) := by
    rw [hg_eq_mul, TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hμ_tg hν_tg u]

  rw [hg_eq_comp, hf_μ]
  exact smulLeftCLM_schwartz_of_compactSmooth (↑f_μ) ν hν_smooth hν_compact hν_tg


/-- General "disjoint Css implies Schwartz" statement: if `ψ` vanishes on `Css u`, then
`g · u` is Schwartz. -/
theorem css_disjoint_implies_schwartz_general (u : 𝓢'(E n, ℂ))
    (g : E n → ℂ) (hg_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (R : ℝ) (hR : 0 < R)
    (ψ : E n → ℂ)
    (hψ_hom : ∀ (a : ℝ), 0 < a → ∀ (x : E n), x ≠ 0 → ψ (a • x) = ψ x)
    (hg_eq : ∀ x : E n, R < ‖x‖ → g x = ψ x)
    (hψ_disjoint : ∀ ω : Sphere n,
      ω ∈ ConicSingularSupportSphere u → ψ (↑ω) = 0) :
    ∃ (f : SchwartzMap (E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ g u = (f : 𝓢'(E n, ℂ)) := by sorry


/-- If `Css u₁` and `Css u₂` are disjoint, there exists a smooth `g` such that `g · u₂` and
`(1 - g) · u₁` are both Schwartz. -/
theorem exists_separating_schwartz_pair
    (u₁ u₂ : TemperedDistribution (E n) ℂ)
    (hdisj : Disjoint (ConicSingularSupportSphere u₁)
                      (ConicSingularSupportSphere u₂)) :
    ∃ (f₁ f₂ : SchwartzMap (E n) ℂ)
      (g : E n → ℂ) (_ : ContDiff ℝ ⊤ g),
      TemperedDistribution.smulLeftCLM ℂ g u₂ = (f₁ : 𝓢'(E n, ℂ)) ∧
      TemperedDistribution.smulLeftCLM ℂ (1 - g) u₁ = (f₂ : 𝓢'(E n, ℂ)) := by sorry

/-- The distribution pairing `⟨u₁, u₂⟩`, defined using a separating Schwartz pair when
the conic singular supports of `u₁` and `u₂` are disjoint. -/
def distributionPairing
    (u₁ u₂ : TemperedDistribution (E n) ℂ)
    (hdisj : Disjoint (ConicSingularSupportSphere u₁)
                      (ConicSingularSupportSphere u₂)) : ℂ :=
  let h := exists_separating_schwartz_pair u₁ u₂ hdisj
  let f₁ := h.choose
  let f₂ := h.choose_spec.choose
  u₁ f₁ + u₂ f₂


/-- Additivity of the convolution-pairing in `φ`. -/
theorem distributionPairing_schwartzConvolution_map_add
    (u v : TemperedDistribution (E n) ℂ)
    (hcond : DisjointCssCondition u v)
    (φ₁ φ₂ : 𝓢(E n, ℂ)) :
    distributionPairing u (schwartzConvolution (reflection v) (φ₁ + φ₂))
      (pairing_welldefined_of_disjointCss u v hcond (φ₁ + φ₂)) =
    distributionPairing u (schwartzConvolution (reflection v) φ₁)
      (pairing_welldefined_of_disjointCss u v hcond φ₁) +
    distributionPairing u (schwartzConvolution (reflection v) φ₂)
      (pairing_welldefined_of_disjointCss u v hcond φ₂) := by sorry


/-- Scalar homogeneity of the convolution-pairing in `φ`. -/
theorem distributionPairing_schwartzConvolution_map_smul
    (u v : TemperedDistribution (E n) ℂ)
    (hcond : DisjointCssCondition u v)
    (c : ℂ) (φ : 𝓢(E n, ℂ)) :
    distributionPairing u (schwartzConvolution (reflection v) (c • φ))
      (pairing_welldefined_of_disjointCss u v hcond (c • φ)) =
    c • distributionPairing u (schwartzConvolution (reflection v) φ)
      (pairing_welldefined_of_disjointCss u v hcond φ) := by sorry


/-- Continuity of the convolution-pairing in the Schwartz argument `φ`. -/
theorem distributionPairing_schwartzConvolution_continuous
    (u v : TemperedDistribution (E n) ℂ)
    (hcond : DisjointCssCondition u v) :
    Continuous (fun φ =>
      distributionPairing u (schwartzConvolution (reflection v) φ)
        (pairing_welldefined_of_disjointCss u v hcond φ)) := by sorry

/-- Subtype-packaged definition of the convolution distribution `u * v` (under
`DisjointCssCondition`), bundling the underlying tempered distribution together with the
specification of its action on Schwartz functions. -/
def convolution_of_disjointCss_aux
    (u v : TemperedDistribution (E n) ℂ)
    (hcond : DisjointCssCondition u v) :
    { T : TemperedDistribution (E n) ℂ //
      ∀ φ : 𝓢(E n, ℂ),
        T φ = distributionPairing u (schwartzConvolution (reflection v) φ)
          (pairing_welldefined_of_disjointCss u v hcond φ) } :=
  ⟨⟨{ toFun := fun φ =>
        distributionPairing u (schwartzConvolution (reflection v) φ)
          (pairing_welldefined_of_disjointCss u v hcond φ)
      map_add' := distributionPairing_schwartzConvolution_map_add u v hcond
      map_smul' := distributionPairing_schwartzConvolution_map_smul u v hcond },
    distributionPairing_schwartzConvolution_continuous u v hcond⟩,
   fun _ => rfl⟩

/-- The convolution `u * v` of two tempered distributions whose conic singular supports
satisfy `DisjointCssCondition`. -/
def convolution_of_disjointCss
    (u v : TemperedDistribution (E n) ℂ)
    (hcond : DisjointCssCondition u v) :
    TemperedDistribution (E n) ℂ :=
  (convolution_of_disjointCss_aux u v hcond).val

/-- Action of `convolution_of_disjointCss u v` on a Schwartz function `φ`, expressed via
the distribution pairing of `u` and `(reflection v) * φ`. -/
theorem convolution_of_disjointCss_apply
    (u v : TemperedDistribution (E n) ℂ)
    (hcond : DisjointCssCondition u v)
    (φ : 𝓢(E n, ℂ)) :
    convolution_of_disjointCss u v hcond φ =
      distributionPairing u (schwartzConvolution (reflection v) φ)
        (pairing_welldefined_of_disjointCss u v hcond φ) :=
  (convolution_of_disjointCss_aux u v hcond).property φ


/-- A tempered distribution `u` has empty scattering wavefront set iff it is represented by
a Schwartz function. -/
theorem scatteringWavefrontSet_eq_empty_iff {n : ℕ} (u : 𝓢'(E n, ℂ)) :
    scatteringWavefrontSet u = ∅ ↔ ∃ f : 𝓢(E n, ℂ), (f : 𝓢'(E n, ℂ)) = u := by sorry

/-- The ratio `φ' / φ` is smooth provided `φ` and `φ'` are smooth and the closed support of
`φ'` lies in the open set where `φ` is nonzero. -/
theorem contDiff_div_of_support_subset
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {φ φ' : V → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hφ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ')
    (hsup : tsupport φ' ⊆ Function.support φ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => φ' x * (φ x)⁻¹) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : φ x ≠ 0
  ·
    exact hφ'.contDiffAt.mul (hφ.contDiffAt.inv hx)
  ·
    push Not at hx
    have hx_not_supp : x ∉ tsupport φ' := fun hmem =>
      absurd (hsup hmem) (Function.notMem_support.mpr hx)
    have hφ'_eq : φ' =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx_not_supp
    have hμ_eq : (fun y => φ' y * (φ y)⁻¹) =ᶠ[nhds x] (fun _ => (0 : ℂ)) := by
      filter_upwards [hφ'_eq] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hμ_eq


/-- Factorization: there exists a smooth compactly-supported `μ` (namely `φ' / φ`) with
`φ' · u = μ · (φ · u)`. -/
theorem smooth_factorization_smulLeftCLM (u : 𝓢'(E n, ℂ))
    (φ φ' : E n → ℂ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ') (hφ'c : HasCompactSupport φ')
    (hsup : tsupport φ' ⊆ Function.support φ) :
    ∃ (μ : E n → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ ∧ HasCompactSupport μ ∧
      TemperedDistribution.smulLeftCLM ℂ φ' u =
        TemperedDistribution.smulLeftCLM ℂ μ (TemperedDistribution.smulLeftCLM ℂ φ u) := by

  have hsup' : Function.support φ' ⊆ Function.support φ :=
    (subset_tsupport φ').trans hsup

  set μ := fun x => φ' x * (φ x)⁻¹ with hμ_def

  have hμ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ :=
    contDiff_div_of_support_subset hφ hφ' hsup

  have hμ_compact : HasCompactSupport μ :=
    hφ'c.mono (fun x hx => by
      simp only [hμ_def, Function.mem_support] at hx ⊢; exact left_ne_zero_of_mul hx)
  refine ⟨μ, hμ_smooth, hμ_compact, ?_⟩

  have hφ_temp : Function.HasTemperateGrowth φ := hφc.hasTemperateGrowth hφ
  have hμ_temp : Function.HasTemperateGrowth μ := hμ_compact.hasTemperateGrowth hμ_smooth

  have heq : φ * μ = φ' := by
    ext x; simp only [Pi.mul_apply, hμ_def]
    by_cases hφx : φ x = 0
    · have : φ' x = 0 := by
        by_contra h
        exact absurd (Function.mem_support.mp (hsup' (Function.mem_support.mpr h)))
          (not_not.mpr hφx)
      simp [hφx, this]
    · field_simp

  rw [show TemperedDistribution.smulLeftCLM ℂ μ (TemperedDistribution.smulLeftCLM ℂ φ u)
      = TemperedDistribution.smulLeftCLM ℂ (φ * μ) u from
    (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hφ_temp hμ_temp u)]
  rw [heq]

/-- Fourier inversion via reflection: `𝓕(R(𝓕 g)) = g`, where `R` denotes Schwartz
reflection. -/
lemma fourier_schwartzReflection_fourier (g : 𝓢(E n, ℂ)) :
    𝓕 (schwartzReflectionCLM (𝓕 g)) = g := by
  have h1 : 𝓕⁻ g = schwartzReflectionCLM (𝓕 g) := by
    simp only [FourierTransformInv.fourierInv, schwartzReflectionCLM]
    simp only [ContinuousLinearMap.comp_apply, SchwartzMap.fourierTransformCLM_apply]
    rfl
  rw [← h1]
  exact FourierInvPair.fourier_fourierInv_eq g

/-- Fourier transform of the product `μ · v` (with `μ` smooth and compactly supported) is
a Schwartz convolution of `𝓕 v` with a Schwartz function. -/
theorem fourier_smulLeftCLM_eq_schwartzConvolution
    (μ : E n → ℂ) (hμ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ) (hμc : HasCompactSupport μ)
    (v : 𝓢'(E n, ℂ)) :
    ∃ f : 𝓢(E n, ℂ),
      𝓕 (TemperedDistribution.smulLeftCLM ℂ μ v) = schwartzConvolution (𝓕 v) f := by
  let μ_s : 𝓢(E n, ℂ) := hμc.toSchwartzMap hμ
  use 𝓕 μ_s
  ext ψ
  simp only [TemperedDistribution.fourier_apply]
  show v (SchwartzMap.smulLeftCLM ℂ μ (𝓕 ψ)) =
    (𝓕 v) ((SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ)
      (schwartzReflectionCLM (𝓕 μ_s))) ψ)
  rw [TemperedDistribution.fourier_apply]
  congr 1
  rw [SchwartzMap.fourier_convolution, fourier_schwartzReflection_fourier]
  ext x
  have htg : Function.HasTemperateGrowth μ := hμc.hasTemperateGrowth hμ
  rw [SchwartzMap.pairing_apply, SchwartzMap.smulLeftCLM_apply htg]
  simp only [ContinuousLinearMap.mul_apply', smul_eq_mul]
  have : μ_s x = μ x := HasCompactSupport.toSchwartzMap_toFun hμc hμ x
  rw [this]


/-- Refinement of `fourier_smulLeftCLM_eq_schwartzConvolution`: given two compactly
supported smooth cutoffs `φ, φ'` with `supp φ' ⊆ supp φ`, the Fourier transform of
`φ' · u` is the Schwartz convolution of `𝓕 (φ · u)` with a Schwartz function. -/
theorem fourier_compact_cutoff_eq_schwartz_convolution (u : 𝓢'(E n, ℂ))
    (φ φ' : E n → ℂ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ') (hφ'c : HasCompactSupport φ')
    (hsup : tsupport φ' ⊆ Function.support φ) :
    ∃ f : 𝓢(E n, ℂ),
      𝓕 (TemperedDistribution.smulLeftCLM ℂ φ' u) =
        schwartzConvolution (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ u)) f := by

  obtain ⟨μ, hμ_smooth, hμ_compact, hfactor⟩ :=
    smooth_factorization_smulLeftCLM u φ φ' hφ hφc hφ' hφ'c hsup

  obtain ⟨f, hconv⟩ :=
    fourier_smulLeftCLM_eq_schwartzConvolution μ hμ_smooth hμ_compact
      (TemperedDistribution.smulLeftCLM ℂ φ u)

  exact ⟨f, by rw [hfactor, hconv]⟩

/-- Monotonicity of the conic singular support under shrinking compact cutoffs:
`Css (𝓕 (φ' · u)) ⊆ Css (𝓕 (φ · u))` whenever `supp φ' ⊆ supp φ`. -/
theorem cssSphere_mono_compact_cutoff (u : 𝓢'(E n, ℂ))
    (φ φ' : E n → ℂ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ') (hφ'c : HasCompactSupport φ')
    (hsup : tsupport φ' ⊆ Function.support φ) :
    ConicSingularSupportSphere (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ' u)) ⊆
    ConicSingularSupportSphere (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ u)) := by
  obtain ⟨f, hf⟩ := fourier_compact_cutoff_eq_schwartz_convolution u φ φ' hφ hφc hφ' hφ'c hsup
  rw [hf]
  exact css_schwartz_convolution _ f

/-- The conic singular support `Css u` on the sphere is closed. -/
theorem cssSphere_isClosed (u : 𝓢'(E n, ℂ)) :
    IsClosed (ConicSingularSupportSphere u) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro ω hω
  simp only [Set.mem_compl_iff, ConicSingularSupportSphere, Set.mem_setOf_eq, not_not] at hω
  obtain ⟨g, ⟨hg_smooth, R, hR, hR_lt, R₀, hR₀, hg_supp, ψ, hψ_hom, hψ_ne, hg_eq⟩, f, hf⟩ := hω
  have hR1 : (0 : ℝ) < R + 1 := by linarith
  set φ : Sphere n → ℂ := fun ω' => g ((R + 1) • (↑ω' : E n)) with hφ_def
  have hφ_cont : Continuous φ :=
    hg_smooth.continuous.comp (continuous_const.smul continuous_subtype_val)
  have hφ_eq : ∀ ω' : Sphere n, ψ (↑ω' : E n) = φ ω' := by
    intro ω'
    have h_sphere : ‖(↑ω' : E n)‖ = 1 := by
      have := ω'.2; simp only [Metric.mem_sphere, dist_zero_right] at this; exact this
    have h_norm : R < ‖(R + 1) • (↑ω' : E n)‖ := by
      rw [norm_smul, Real.norm_of_nonneg hR1.le, h_sphere, mul_one]; linarith
    have h_ne : (↑ω' : E n) ≠ 0 := by
      intro h; rw [h, norm_zero] at h_sphere; exact zero_ne_one h_sphere
    rw [← hψ_hom (R + 1) hR1 (↑ω') h_ne, ← hg_eq _ h_norm]
  refine ⟨φ ⁻¹' {(0 : ℂ)}ᶜ, ?_, hφ_cont.isOpen_preimage _ isOpen_compl_singleton, ?_⟩
  · intro ω' hω'
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hω'
    simp only [Set.mem_compl_iff, ConicSingularSupportSphere, Set.mem_setOf_eq, not_not]
    exact ⟨g, ⟨hg_smooth, R, hR, hR_lt, R₀, hR₀, hg_supp, ψ, hψ_hom, (hφ_eq ω') ▸ hω', hg_eq⟩, f, hf⟩
  · simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    rwa [← hφ_eq]

/-- The cone support `Csp u` on the sphere is closed. -/
theorem coneSupportSphere_isClosed (u : 𝓢'(E n, ℂ)) :
    IsClosed (ConeSupportSphere u) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro ω hω
  simp only [Set.mem_compl_iff, ConeSupportSphere, Set.mem_setOf_eq, not_not] at hω
  obtain ⟨g, ⟨hg_smooth, R, hR, hR_lt, R₀, hR₀, hg_supp, ψ, hψ_hom, hψ_ne, hg_eq⟩, hgu⟩ := hω
  have hR1 : (0 : ℝ) < R + 1 := by linarith
  set φ : Sphere n → ℂ := fun ω' => g ((R + 1) • (↑ω' : E n)) with hφ_def
  have hφ_cont : Continuous φ :=
    hg_smooth.continuous.comp (continuous_const.smul continuous_subtype_val)
  have hφ_eq : ∀ ω' : Sphere n, ψ (↑ω' : E n) = φ ω' := by
    intro ω'
    have h_sphere : ‖(↑ω' : E n)‖ = 1 := by
      have := ω'.2; simp only [Metric.mem_sphere, dist_zero_right] at this; exact this
    have h_norm : R < ‖(R + 1) • (↑ω' : E n)‖ := by
      rw [norm_smul, Real.norm_of_nonneg hR1.le, h_sphere, mul_one]; linarith
    have h_ne : (↑ω' : E n) ≠ 0 := by
      intro h; rw [h, norm_zero] at h_sphere; exact zero_ne_one h_sphere
    rw [← hψ_hom (R + 1) hR1 (↑ω') h_ne, ← hg_eq _ h_norm]
  refine ⟨φ ⁻¹' {(0 : ℂ)}ᶜ, ?_, hφ_cont.isOpen_preimage _ isOpen_compl_singleton, ?_⟩
  · intro ω' hω'
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hω'
    simp only [Set.mem_compl_iff, ConeSupportSphere, Set.mem_setOf_eq, not_not]
    exact ⟨g, ⟨hg_smooth, R, hR, hR_lt, R₀, hR₀, hg_supp, ψ, hψ_hom, (hφ_eq ω') ▸ hω', hg_eq⟩, hgu⟩
  · simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff]
    rwa [← hφ_eq]

/-- Auxiliary "nonzero `ψ`" version of `conicCutoff_finite_cover_schwartz`: covering by
witnesses where `ψ` is nonzero suffices to show `g · u` is Schwartz. -/
theorem conicCutoff_finite_cover_schwartz_nonzero
    (u : 𝓢'(E n, ℂ))
    (g : E n → ℂ) (hg_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (R : ℝ) (hR : 0 < R)
    (_hg_supp : Function.support g ⊆ {x : E n | R ≤ ‖x‖})
    (ψ : E n → ℂ)
    (hψ_hom : ∀ (a : ℝ), 0 < a → ∀ (x : E n), x ≠ 0 → ψ (a • x) = ψ x)
    (hg_eq : ∀ x : E n, R < ‖x‖ → g x = ψ x)
    (hwitness : ∀ ω : Sphere n, ψ (↑ω) ≠ 0 →
      ∃ (g_ω : E n → ℂ), IsConicCutoffNear g_ω ω ∧
        ∃ (f_ω : SchwartzMap (E n) ℂ),
          TemperedDistribution.smulLeftCLM ℂ g_ω u = (f_ω : 𝓢'(E n, ℂ)))
    (_hψ_nonzero : ¬∀ ω : Sphere n, ψ (↑ω) = 0) :
    ∃ (f : SchwartzMap (E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ g u = (f : 𝓢'(E n, ℂ)) := by


  have hψ_disjoint : ∀ ω : Sphere n,
      ω ∈ ConicSingularSupportSphere u → ψ (↑ω) = 0 := by
    intro ω hω_css
    by_contra hψω_ne

    obtain ⟨g_ω, hg_ω_cutoff, f_ω, hf_ω⟩ := hwitness ω hψω_ne

    exact hω_css ⟨g_ω, hg_ω_cutoff, f_ω, hf_ω⟩

  exact css_disjoint_implies_schwartz_general u g hg_smooth R hR ψ hψ_hom hg_eq hψ_disjoint

/-- Finite-cover Schwartz theorem: if at every direction `ω` where `ψ(ω) ≠ 0` we have a
local Schwartz witness for `u`, then `g · u` is Schwartz. -/
theorem conicCutoff_finite_cover_schwartz
    (u : 𝓢'(E n, ℂ))
    (g : E n → ℂ) (hg_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (R : ℝ) (hR : 0 < R)
    (hg_supp : Function.support g ⊆ {x : E n | R ≤ ‖x‖})
    (ψ : E n → ℂ)
    (hψ_hom : ∀ (a : ℝ), 0 < a → ∀ (x : E n), x ≠ 0 → ψ (a • x) = ψ x)
    (hg_eq : ∀ x : E n, R < ‖x‖ → g x = ψ x)

    (hwitness : ∀ ω : Sphere n, ψ (↑ω) ≠ 0 →
      ∃ (g_ω : E n → ℂ), IsConicCutoffNear g_ω ω ∧
        ∃ (f_ω : SchwartzMap (E n) ℂ),
          TemperedDistribution.smulLeftCLM ℂ g_ω u = (f_ω : 𝓢'(E n, ℂ))) :
    ∃ (f : SchwartzMap (E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ g u = (f : 𝓢'(E n, ℂ)) := by


  by_cases h_psi_zero : ∀ ω : Sphere n, ψ (↑ω) = 0
  ·

    have h_psi_vanish : ∀ x : E n, x ≠ 0 → ψ x = 0 := by
      intro x hx
      have h_norm : 0 < ‖x‖ := norm_pos_iff.mpr hx
      rw [← hψ_hom ‖x‖⁻¹ (inv_pos.mpr h_norm) x hx]
      exact h_psi_zero ⟨‖x‖⁻¹ • x, by
        simp [norm_smul, inv_mul_cancel₀ (ne_of_gt h_norm)]⟩


    have h_g_zero : g = 0 := by
      ext x
      simp only [Pi.zero_apply]
      by_cases hx_lt : ‖x‖ < R
      · have hx_notin : x ∉ Function.support g := by
          intro hmem; exact not_lt.mpr ((hg_supp hmem) : R ≤ ‖x‖) hx_lt
        exact Function.notMem_support.mp hx_notin
      · by_cases hx_eq : ‖x‖ = R
        ·
          have hx_ne : x ≠ 0 := by intro h; simp [h] at hx_eq; linarith
          have h_g_gt : ∀ y : E n, R < ‖y‖ → g y = 0 := by
            intro y hy
            rw [hg_eq y hy]
            exact h_psi_vanish y (by intro h0; simp [h0] at hy; linarith)
          have hg_cont := hg_smooth.continuous
          have h_tend : Filter.Tendsto (fun t : ℝ => t • x) (nhdsWithin 1 (Set.Ioi 1)) (nhds x) := by
            conv_rhs => rw [← one_smul ℝ x]
            exact Filter.Tendsto.smul (nhdsWithin_le_nhds) tendsto_const_nhds
          have h_zero : ∀ t : ℝ, 1 < t → g (t • x) = 0 := by
            intro t ht; apply h_g_gt
            rw [norm_smul, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ t), hx_eq]
            nlinarith
          have h_lim : Filter.Tendsto (fun t : ℝ => g (t • x))
              (nhdsWithin 1 (Set.Ioi 1)) (nhds (g x)) :=
            hg_cont.continuousAt.tendsto.comp h_tend
          have h_lim0 : Filter.Tendsto (fun t : ℝ => g (t • x))
              (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
            apply Filter.Tendsto.congr'
            · filter_upwards [self_mem_nhdsWithin] with t ht
              exact (h_zero t ht).symm
            · exact tendsto_const_nhds
          haveI : (nhdsWithin (1 : ℝ) (Set.Ioi 1)).NeBot := nhdsGT_neBot (1 : ℝ)
          exact tendsto_nhds_unique h_lim h_lim0
        ·
          have hx_gt : R < ‖x‖ := lt_of_le_of_ne (not_lt.mp hx_lt) (Ne.symm hx_eq)
          rw [hg_eq x hx_gt]
          exact h_psi_vanish x (by intro h0; simp [h0] at hx_gt; linarith)

    rw [h_g_zero]
    exact ⟨0, by
      ext φ
      simp only [TemperedDistribution.smulLeftCLM_apply_apply]
      have : SchwartzMap.smulLeftCLM ℂ (0 : E n → ℂ) = 0 := by
        unfold SchwartzMap.smulLeftCLM
        split_ifs with h
        · ext f; simp
        · rfl
      simp [this]⟩
  ·


    exact conicCutoff_finite_cover_schwartz_nonzero u g hg_smooth R hR hg_supp ψ hψ_hom hg_eq
      hwitness h_psi_zero


/-- If `ψ` vanishes on `Css u`, then the cutoff distribution `g · u` (with `g` agreeing
with `ψ` outside a ball) is Schwartz. -/
theorem css_disjoint_implies_schwartz (u : 𝓢'(E n, ℂ))
    (g : E n → ℂ) (hg_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (R : ℝ) (hR : 0 < R)
    (hg_supp : Function.support g ⊆ {x : E n | R ≤ ‖x‖})
    (ψ : E n → ℂ)
    (hψ_hom : ∀ (a : ℝ), 0 < a → ∀ (x : E n), x ≠ 0 → ψ (a • x) = ψ x)
    (hg_eq : ∀ x : E n, R < ‖x‖ → g x = ψ x)
    (hψ_disjoint : ∀ ω : Sphere n,
      ω ∈ ConicSingularSupportSphere u → ψ (↑ω) = 0) :
    ∃ (f : SchwartzMap (E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ g u = (f : 𝓢'(E n, ℂ)) := by


  apply conicCutoff_finite_cover_schwartz u g hg_smooth R hR hg_supp ψ hψ_hom hg_eq

  intro ω hψω_ne

  have hω_not_css : ω ∉ ConicSingularSupportSphere u := by
    intro hω_css; exact hψω_ne (hψ_disjoint ω hω_css)

  rw [ConicSingularSupportSphere, Set.mem_setOf_eq, not_not] at hω_not_css
  exact hω_not_css

/-- Conjunction of the previous three properties: both `Csp u` and `Css u` are closed, and
`g · u` is Schwartz whenever the support condition on `ψ` is satisfied. -/
theorem isClosed_coneSupportSphere_and_cssSphere_and_schwartz_of_disjoint (u : 𝓢'(E n, ℂ)) :
    IsClosed (ConeSupportSphere u) ∧
    IsClosed (ConicSingularSupportSphere u) ∧
    (∀ (g : E n → ℂ) (hg_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
      (R : ℝ) (hR : 0 < R)
      (hg_supp : Function.support g ⊆ {x : E n | R ≤ ‖x‖})
      (ψ : E n → ℂ)
      (hψ_hom : ∀ (a : ℝ), 0 < a → ∀ (x : E n), x ≠ 0 → ψ (a • x) = ψ x)
      (hg_eq : ∀ x : E n, R < ‖x‖ → g x = ψ x)
      (hψ_disjoint : ∀ ω : Sphere n,
        ω ∈ ConicSingularSupportSphere u → ψ (↑ω) = 0),
      ∃ (f : SchwartzMap (E n) ℂ),
        TemperedDistribution.smulLeftCLM ℂ g u = (f : 𝓢'(E n, ℂ))) :=
  ⟨coneSupportSphere_isClosed u,
   cssSphere_isClosed u,
   fun g hg_smooth R hR hg_supp ψ hψ_hom hg_eq hψ_disjoint =>
     css_disjoint_implies_schwartz u g hg_smooth R hR hg_supp ψ hψ_hom hg_eq hψ_disjoint⟩

/-- The support of a smooth function is open. -/
lemma contDiff_isOpen_support (φ : E n → ℂ) (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    IsOpen (Function.support φ) :=
  hφ.continuous.isOpen_support

/-- "Open neighbourhood" formulation of the wavefront set complement: if `(x₀, ω₀)` is not
in `WF(u)`, there are open neighbourhoods `U ∋ x₀` and `V ∋ ω₀` such that for every cutoff
`φ'` supported in `U`, `V` is disjoint from `Css (𝓕 (φ' · u))`. -/
theorem not_mem_wavefrontSet_nhds (u : 𝓢'(E n, ℂ))
    (x₀ : E n) (ω₀ : Sphere n)
    (hnotin : (x₀, ω₀) ∉ wavefrontSet u) :
    ∃ (U : Set (E n)) (V : Set (Sphere n)),
      IsOpen U ∧ x₀ ∈ U ∧
      IsOpen V ∧ ω₀ ∈ V ∧
      ∀ (φ' : E n → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ' → HasCompactSupport φ' →
        tsupport φ' ⊆ U →
        V ∩ ConicSingularSupportSphere
          (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ' u)) = ∅ := by
  simp only [wavefrontSet, Set.mem_setOf_eq, not_not] at hnotin
  obtain ⟨φ₀, hφ₀_smooth, hφ₀_compact, hφ₀_ne, hω₀_notin⟩ := hnotin
  refine ⟨Function.support φ₀,
    (ConicSingularSupportSphere (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ₀ u)))ᶜ,
    contDiff_isOpen_support φ₀ hφ₀_smooth,
    Function.mem_support.mpr hφ₀_ne,
    (cssSphere_isClosed _).isOpen_compl,
    hω₀_notin, ?_⟩
  intro φ' hφ'_smooth hφ'_compact hsupp
  have hmono := cssSphere_mono_compact_cutoff u φ₀ φ' hφ₀_smooth hφ₀_compact
    hφ'_smooth hφ'_compact hsupp
  exact Set.disjoint_iff_inter_eq_empty.mp (disjoint_compl_left.mono_right hmono)


/-- A conic cutoff near `ω` exists for every direction `ω`. -/
theorem exists_conicCutoff (ω : Sphere n) :
    ∃ (g : E n → ℂ), IsConicCutoffNear g ω := by

  let χ : ContDiffBump (0 : E n) := ⟨1/3, 2/3, by positivity, by norm_num⟩
  refine ⟨fun x => Complex.ofReal (1 - χ x), ?_, 2/3, by positivity, by norm_num,
    1/3, by positivity, ?_, fun _ => 1, ?_, ?_, ?_⟩
  ·
    rw [contDiff_infty]
    intro k
    exact_mod_cast Complex.ofRealCLM.contDiff.comp (contDiff_const.sub χ.contDiff)

  ·
    intro x hx
    simp only [Function.mem_support] at hx
    simp only [Set.mem_setOf_eq]
    by_contra h
    simp only [not_le] at h
    have hx_ball : x ∈ Metric.closedBall (0 : E n) χ.rIn := by
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact le_of_lt h
    have : χ x = 1 := χ.one_of_mem_closedBall hx_ball
    simp only [this, sub_self, Complex.ofReal_zero] at hx
    exact hx rfl
  ·
    intro a _ x _; rfl
  ·
    exact one_ne_zero
  ·
    intro x hx
    have hx_out : χ.rOut ≤ dist x 0 := by
      simp only [dist_zero_right]; exact le_of_lt hx
    have : χ x = 0 := χ.zero_of_le_dist hx_out
    simp only [this, sub_zero, Complex.ofReal_one]


/-- A Parseval-style identity: for a conic cutoff `g`, there is a temperate-growth function
`F` (essentially the inverse Fourier transform of `g`) such that pairing with `g · 𝓕 h`
equals pairing with `h · F`. -/
theorem parseval_temperate_growth_schwartz
    (g : E n → ℂ) (ω : Sphere n) (hg : IsConicCutoffNear g ω) :
    ∃ (F : E n → ℂ), Function.HasTemperateGrowth F ∧
      ∀ (h : 𝓢(E n, ℂ)), ∫ x, g x • (𝓕 h) x = ∫ x, h x • F x := by


  have hg_tg : Function.HasTemperateGrowth g := isConicCutoffNear_hasTemperateGrowth g ω hg
  have hg_neg_tg : Function.HasTemperateGrowth (g ∘ Neg.neg) := hasTemperateGrowth_comp_neg hg_tg

  obtain ⟨G, hG_tg, hG_eq⟩ := DifferentialOperators.temperateGrowth_inverseFT_exists
    (g ∘ Neg.neg) hg_neg_tg
  refine ⟨G, hG_tg, fun h => ?_⟩


  rw [← hG_eq h]


  have hfi : ∀ x : E n, (𝓕⁻ h) x = (𝓕 h) (-x) := by
    intro x
    have heq := SchwartzMap.fourierInv_apply_eq h

    have : (𝓕⁻ h) x = ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv) (𝓕 h)) x := by
      rw [← heq]
    rw [this, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
    simp [LinearIsometryEquiv.neg]

  simp_rw [Function.comp_apply, hfi]

  exact (integral_neg_eq_self (fun ξ => g ξ • (𝓕 h) ξ) volume).symm


/-- Sobolev/decay bound: for fixed `k, m`, the function `g' · F` satisfies a uniform
polynomial-decay bound `‖x‖^k · ‖∇^m (g' · F)(x)‖ ≤ C`. -/
theorem sobolev_chain_schwartz_bound
    (g' : E n → ℂ) (ω' : Sphere n) (hg' : IsConicCutoffNear g' ω')
    (F : E n → ℂ) (hF : Function.HasTemperateGrowth F)
    (g₀ : E n → ℂ) (ω₀ : Sphere n) (hg₀ : IsConicCutoffNear g₀ ω₀)
    (hF_eq : ∀ (h : 𝓢(E n, ℂ)), ∫ x, g₀ x • (𝓕 h) x = ∫ x, h x • F x)
    (k m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E n,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun x => g' x * F x) x‖ ≤ C := by sorry


/-- Strengthening of `sobolev_chain_schwartz_bound`: `‖x‖^k · ‖∇^m(g' · F)(x)‖ → 0` at
infinity. -/
theorem sobolev_chain_tendsto_zero
    (g' : E n → ℂ) (ω' : Sphere n) (hg' : IsConicCutoffNear g' ω')
    (F : E n → ℂ) (hF : Function.HasTemperateGrowth F)
    (g₀ : E n → ℂ) (ω₀ : Sphere n) (hg₀ : IsConicCutoffNear g₀ ω₀)
    (hF_eq : ∀ (h : 𝓢(E n, ℂ)), ∫ x, g₀ x • (𝓕 h) x = ∫ x, h x • F x)
    (k m : ℕ) :
    Filter.Tendsto
      (fun x : E n => ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun x => g' x * F x) x‖)
      (Filter.cocompact (E n)) (nhds 0) := by

  have hg'F_smooth : ContDiff ℝ ↑(⊤ : ℕ∞) (fun x => g' x * F x) := hg'.1.mul hF.1
  have hg'_tg : Function.HasTemperateGrowth g' :=
    isConicCutoffNear_hasTemperateGrowth g' ω' hg'
  have hg'F_tg : Function.HasTemperateGrowth (fun x => g' x * F x) := hg'_tg.mul hF


  have h_schwartz_bound : ∃ C : ℝ, 0 < C ∧ ∀ x : E n,
      ‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ m (fun x => g' x * F x) x‖ ≤ C := by


    exact sobolev_chain_schwartz_bound g' ω' hg' F hF g₀ ω₀ hg₀ hF_eq (k + 1) m

  obtain ⟨C, hC_pos, hC⟩ := h_schwartz_bound
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_iff, Filter.mem_cocompact]
  refine ⟨Metric.closedBall 0 (C / ε), isCompact_closedBall 0 _, fun x hx => ?_⟩
  simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hx
  simp only [Set.mem_setOf_eq]
  have hx_pos : (0 : ℝ) < ‖x‖ := lt_trans (div_pos hC_pos hε) hx
  have h_nn : 0 ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun x => g' x * F x) x‖ :=
    mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)
  simp only [Real.dist_eq, sub_zero, abs_of_nonneg h_nn]
  have h_eq : ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun x => g' x * F x) x‖ =
      (‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ m (fun x => g' x * F x) x‖) / ‖x‖ := by
    field_simp; ring
  rw [h_eq]
  calc (‖x‖ ^ (k + 1) * ‖iteratedFDeriv ℝ m (fun x => g' x * F x) x‖) / ‖x‖
      ≤ C / ‖x‖ := div_le_div_of_nonneg_right (hC x) (le_of_lt hx_pos)
    _ < C / (C / ε) := div_lt_div_of_pos_left hC_pos (div_pos hC_pos hε) hx
    _ = ε := by field_simp

/-- Schwartz seminorm bound on `g' · F`: combining the cocompact decay with continuity on
a compact set yields a global bound. -/
theorem schwartz_seminorm_bound_from_sobolev_embedding
    (g' : E n → ℂ) (ω' : Sphere n) (hg' : IsConicCutoffNear g' ω')
    (F : E n → ℂ) (hF : Function.HasTemperateGrowth F)
    (g₀ : E n → ℂ) (ω₀ : Sphere n) (hg₀ : IsConicCutoffNear g₀ ω₀)
    (hF_eq : ∀ (h : 𝓢(E n, ℂ)), ∫ x, g₀ x • (𝓕 h) x = ∫ x, h x • F x)
    (k m : ℕ) :
    ∃ C : ℝ, ∀ x : E n, ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun x => g' x * F x) x‖ ≤ C := by


  have hg'F_smooth : ContDiff ℝ ↑(⊤ : ℕ∞) (fun x => g' x * F x) := hg'.1.mul hF.1
  have h_cont : Continuous (fun x : E n =>
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun x => g' x * F x) x‖) :=
    (continuous_norm.pow k).mul
      ((hg'F_smooth.continuous_iteratedFDeriv (mod_cast le_top)).norm)

  have h_tendsto := sobolev_chain_tendsto_zero g' ω' hg' F hF g₀ ω₀ hg₀ hF_eq k m

  have h_nn : ∀ x : E n,
      0 ≤ ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun x => g' x * F x) x‖ :=
    fun x => mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)


  obtain ⟨K, hK_compact, hK_bound⟩ : ∃ (K : Set (E n)), IsCompact K ∧
      ∀ x ∉ K, ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun x => g' x * F x) x‖ < 1 := by
    have h1 : (fun x => ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun x => g' x * F x) x‖) ⁻¹'
        Metric.ball 0 1 ∈ Filter.cocompact (E n) :=
      h_tendsto (Metric.ball_mem_nhds 0 one_pos)
    rw [Filter.mem_cocompact] at h1
    obtain ⟨K, hK, hKs⟩ := h1
    refine ⟨K, hK, fun x hx => ?_⟩
    have hx_mem := hKs hx
    simp only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq, sub_zero] at hx_mem
    rwa [abs_of_nonneg (h_nn x)] at hx_mem

  obtain ⟨M_K, hM_K⟩ := hK_compact.exists_bound_of_continuousOn h_cont.continuousOn

  refine ⟨max M_K 1, fun x => ?_⟩
  by_cases hx : x ∈ K
  · calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun x => g' x * F x) x‖
        ≤ |‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun x => g' x * F x) x‖| := le_abs_self _
      _ ≤ M_K := hM_K x hx
      _ ≤ max M_K 1 := le_max_left _ _
  · exact le_of_lt ((hK_bound x hx).trans_le (le_max_right M_K 1))

/-- The product `g' · F` (where `g'` is a conic cutoff and `F` is a Parseval-witness of
temperate growth) is a Schwartz function. -/
theorem conicCutoff_mul_fourier_conicCutoff_isSchwartz
    (g' : E n → ℂ) (ω' : Sphere n) (hg' : IsConicCutoffNear g' ω')
    (F : E n → ℂ) (hF : Function.HasTemperateGrowth F)
    (hF_prov : ∃ (g₀ : E n → ℂ) (ω₀ : Sphere n),
      IsConicCutoffNear g₀ ω₀ ∧
      ∀ (h : 𝓢(E n, ℂ)), ∫ x, g₀ x • (𝓕 h) x = ∫ x, h x • F x) :
    ∃ (f : SchwartzMap (E n) ℂ), ∀ x, (f : E n → ℂ) x = g' x * F x := by


  have hg'_tg : Function.HasTemperateGrowth g' :=
    isConicCutoffNear_hasTemperateGrowth g' ω' hg'
  have hg'F_smooth : ContDiff ℝ ↑(⊤ : ℕ∞) (fun x => g' x * F x) := hg'.1.mul hF.1


  have hdecay : ∀ k m : ℕ, ∃ C : ℝ, ∀ x : E n,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ m (fun x => g' x * F x) x‖ ≤ C := by
    intro k m


    have hg'F_tg : Function.HasTemperateGrowth (fun x => g' x * F x) := hg'_tg.mul hF

    obtain ⟨g₀, ω₀, hg₀, hF_eq⟩ := hF_prov


    exact schwartz_seminorm_bound_from_sobolev_embedding g' ω' hg' F hF g₀ ω₀ hg₀ hF_eq k m
  exact ⟨SchwartzMap.mk _ hg'F_smooth hdecay, fun x => rfl⟩


/-- Integral representation: there is a Schwartz function `f` such that the integral
`∫ g · 𝓕 (g' · φ)` equals `∫ φ · f` for all Schwartz `φ`. -/
theorem conicCutoff_fourierTransform_integral_schwartz_repr
    (g : E n → ℂ) (ω : Sphere n) (hg : IsConicCutoffNear g ω)
    (g' : E n → ℂ) (ω' : Sphere n) (hg' : IsConicCutoffNear g' ω')
    (hg'_tg : Function.HasTemperateGrowth g') :
    ∃ (f : SchwartzMap (E n) ℂ), ∀ (φ : 𝓢(E n, ℂ)),
      ∫ x, g x • (𝓕 (SchwartzMap.smulLeftCLM ℂ g' φ)) x =
      ∫ x, φ x • (f : E n → ℂ) x := by

  obtain ⟨F, hF_tg, hF_eq⟩ := parseval_temperate_growth_schwartz g ω hg

  obtain ⟨f, hf_eq⟩ := conicCutoff_mul_fourier_conicCutoff_isSchwartz g' ω' hg' F hF_tg
    ⟨g, ω, hg, hF_eq⟩

  refine ⟨f, fun φ => ?_⟩

  rw [hF_eq (SchwartzMap.smulLeftCLM ℂ g' φ)]

  congr 1
  ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hg'_tg, hf_eq]
  simp only [smul_eq_mul]
  ring


/-- If `v` is the distribution of integration against `g` (a conic cutoff) and `g'` is
another conic cutoff of temperate growth, then `g' · 𝓕 v` is represented by a Schwartz
function. -/
theorem conicCutoff_fourierTransform_schwartz_of_temperateGrowth
    (g : E n → ℂ) (ω : Sphere n) (hg : IsConicCutoffNear g ω)
    (v : 𝓢'(E n, ℂ))
    (hv : ∀ (φ : 𝓢(E n, ℂ)), v φ = ∫ x, g x • φ x)
    (g' : E n → ℂ) (ω' : Sphere n) (hg' : IsConicCutoffNear g' ω')
    (hg'_tg : Function.HasTemperateGrowth g') :
    ∃ (f : SchwartzMap (E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ g' (𝓕 v) = (f : 𝓢'(E n, ℂ)) := by

  obtain ⟨f, hf_repr⟩ := conicCutoff_fourierTransform_integral_schwartz_repr
    g ω hg g' ω' hg' hg'_tg

  refine ⟨f, ?_⟩
  ext φ

  simp only [TemperedDistribution.smulLeftCLM_apply_apply]


  change v (𝓕 (SchwartzMap.smulLeftCLM ℂ g' φ)) =
    (SchwartzMap.toTemperedDistributionCLM (E n) ℂ volume f) φ

  rw [hv]

  simp only [SchwartzMap.toTemperedDistributionCLM_apply_apply]

  exact hf_repr φ

/-- Localized Schwartz representation of `g' · 𝓕 v` without the temperate-growth hypothesis
on `g'`: falls back to zero in the degenerate case. -/
theorem conicCutoff_fourierTransform_localized_schwartz
    (g : E n → ℂ) (ω : Sphere n) (hg : IsConicCutoffNear g ω)
    (v : 𝓢'(E n, ℂ))
    (hv : ∀ (φ : 𝓢(E n, ℂ)), v φ = ∫ x, g x • φ x)
    (g' : E n → ℂ) (ω' : Sphere n) (hg' : IsConicCutoffNear g' ω') :
    ∃ (f : SchwartzMap (E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ g' (𝓕 v) = (f : 𝓢'(E n, ℂ)) := by
  by_cases hg'_tg : Function.HasTemperateGrowth g'
  · exact conicCutoff_fourierTransform_schwartz_of_temperateGrowth
      g ω hg v hv g' ω' hg' hg'_tg
  · refine ⟨0, ?_⟩
    ext φ
    simp only [TemperedDistribution.smulLeftCLM_apply_apply]
    have h0 : SchwartzMap.smulLeftCLM ℂ g' = (0 : 𝓢(E n, ℂ) →L[ℂ] 𝓢(E n, ℂ)) := by
      unfold SchwartzMap.smulLeftCLM
      exact dif_neg hg'_tg
    simp [h0]

/-- The conic singular support of `𝓕 v` is empty whenever `v` is integration against a
conic cutoff. -/
theorem cssSphere_eq_empty_fourierTransform_conicCutoff
    (g : E n → ℂ) (ω : Sphere n) (hg : IsConicCutoffNear g ω)
    (v : 𝓢'(E n, ℂ))
    (hv : ∀ (φ : 𝓢(E n, ℂ)), v φ = ∫ x, g x • φ x) :
    ConicSingularSupportSphere (𝓕 v) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro ω' hω'
  simp only [ConicSingularSupportSphere, Set.mem_setOf_eq] at hω'
  apply hω'
  obtain ⟨g', hg'⟩ := exists_conicCutoff ω'
  obtain ⟨f, hf⟩ := conicCutoff_fourierTransform_localized_schwartz g ω hg v hv g' ω' hg'
  exact ⟨g', hg', f, hf⟩


/-- Compatibility of `smulLeftCLM` with Schwartz embedding: multiplying the embedding of a
Schwartz function by `μ` equals the embedding of `μ · f`. -/
lemma smulLeftCLM_schwartz_embed
    {μ : E n → ℂ} (hμ : Function.HasTemperateGrowth μ)
    (f : SchwartzMap (E n) ℂ) :
    TemperedDistribution.smulLeftCLM ℂ μ (f : 𝓢'(E n, ℂ)) =
    ((SchwartzMap.smulLeftCLM ℂ μ f) : 𝓢'(E n, ℂ)) := by
  ext ψ
  simp only [TemperedDistribution.smulLeftCLM_apply_apply,
    SchwartzMap.toTemperedDistributionCLM_apply_apply]
  congr 1; ext x
  rw [SchwartzMap.smulLeftCLM_apply_apply hμ, SchwartzMap.smulLeftCLM_apply_apply hμ]
  simp only [smul_eq_mul]; ring


/-- Witness for `IsSmoothNear`: if `g' · u` is Schwartz and `g' x ≠ 0`, then `u` is smooth
near `x`. -/
theorem isSmoothNear_of_smooth_nonzero_smulLeftCLM_schwartz
    (u : 𝓢'(E n, ℂ)) (g' : E n → ℂ) (x : E n)
    (hg'_smooth : Function.HasTemperateGrowth g')
    (hg'_nonzero : g' x ≠ 0)
    (f : SchwartzMap (E n) ℂ)
    (hf : TemperedDistribution.smulLeftCLM ℂ g' u = (f : 𝓢'(E n, ℂ))) :
    IsSmoothNear u x := by

  let ψ_bump : ContDiffBump x := ⟨1, 2, one_pos, by norm_num⟩
  let ψ_cx : E n → ℂ := fun y => ↑((ψ_bump : E n → ℝ) y)
  have hψ_tg : Function.HasTemperateGrowth ψ_cx :=
    (ψ_bump.hasCompactSupport.comp_left Complex.ofReal_zero).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp ψ_bump.contDiff)

  refine ⟨g' * ψ_cx, ?_, ?_, ?_, ?_⟩
  ·
    exact hg'_smooth.1.mul (Complex.ofRealCLM.contDiff.comp ψ_bump.contDiff)
  ·
    exact HasCompactSupport.mul_left
      (ψ_bump.hasCompactSupport.comp_left Complex.ofReal_zero)
  ·
    show g' x * ψ_cx x ≠ 0
    apply mul_ne_zero hg'_nonzero
    rw [Complex.ofReal_ne_zero]
    exact (ψ_bump.one_of_mem_closedBall (Metric.mem_closedBall_self (le_of_lt one_pos))).symm ▸
      one_ne_zero
  ·

    rw [show TemperedDistribution.smulLeftCLM ℂ (g' * ψ_cx) u =
        TemperedDistribution.smulLeftCLM ℂ ψ_cx (TemperedDistribution.smulLeftCLM ℂ g' u) from
      (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hg'_smooth hψ_tg u).symm]
    rw [hf]

    exact ⟨SchwartzMap.smulLeftCLM ℂ ψ_cx f, smulLeftCLM_schwartz_embed hψ_tg f⟩


/-- For every nonzero `x` and direction `ω`, there is a conic cutoff `g'` near `ω` with
`g' x ≠ 0`. -/
theorem exists_conicCutoff_nonzero_at (ω : Sphere n) (x : E n) (hx : x ≠ 0) :
    ∃ (g' : E n → ℂ), IsConicCutoffNear g' ω ∧ g' x ≠ 0 := by
  have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx


  set m := min ‖x‖ 1 with hm_def
  have hm_pos : 0 < m := lt_min hx_norm_pos one_pos
  have hrIn_pos : 0 < m / 3 := by positivity
  have hrInOut : m / 3 < m * 2 / 3 := by linarith
  let χ : ContDiffBump (0 : E n) := ⟨m / 3, m * 2 / 3, hrIn_pos, hrInOut⟩
  have hR_lt_one : m * 2 / 3 < 1 := by
    have : m ≤ 1 := min_le_right _ _; linarith
  refine ⟨fun y => Complex.ofReal (1 - χ y),
    ⟨?_, m * 2 / 3, by positivity, hR_lt_one, m / 3, by positivity, ?_,
     fun _ => 1, ?_, ?_, ?_⟩, ?_⟩
  ·
    rw [contDiff_infty]
    intro k
    exact_mod_cast Complex.ofRealCLM.contDiff.comp (contDiff_const.sub χ.contDiff)
  ·
    intro y hy
    simp only [Function.mem_support] at hy
    simp only [Set.mem_setOf_eq]
    by_contra h
    simp only [not_le] at h
    have hy_ball : y ∈ Metric.closedBall (0 : E n) χ.rIn := by
      simp only [Metric.mem_closedBall, dist_zero_right]; exact le_of_lt h
    have : χ y = 1 := χ.one_of_mem_closedBall hy_ball
    simp only [this, sub_self, Complex.ofReal_zero] at hy
    exact hy rfl
  ·
    intro a _ y _; rfl
  ·
    exact one_ne_zero
  ·
    intro y hy
    have hy_out : χ.rOut ≤ dist y 0 := by
      simp only [dist_zero_right]; exact le_of_lt hy
    have : χ y = 0 := χ.zero_of_le_dist hy_out
    simp only [this, sub_zero, Complex.ofReal_one]
  ·
    have hx_out : χ.rOut ≤ dist x 0 := by
      simp only [dist_zero_right]
      show m * 2 / 3 ≤ ‖x‖
      have : m ≤ ‖x‖ := min_le_left _ _
      linarith
    have : χ x = 0 := χ.zero_of_le_dist hx_out
    simp only [this, sub_zero, Complex.ofReal_one]
    exact one_ne_zero

/-- The Fourier transform of integration against a conic cutoff is smooth away from the
origin. -/
theorem conicCutoff_fourierTransform_smooth_away_from_origin
    (g : E n → ℂ) (ω : Sphere n) (hg : IsConicCutoffNear g ω)
    (v : 𝓢'(E n, ℂ))
    (hv : ∀ (φ : 𝓢(E n, ℂ)), v φ = ∫ x, g x • φ x)
    (x : E n) (hx : x ≠ 0) :
    IsSmoothNear (𝓕 v) x := by

  let ω' := directionOf x hx

  obtain ⟨g', hg', hg'x⟩ := exists_conicCutoff_nonzero_at ω' x hx

  obtain ⟨f, hf⟩ := conicCutoff_fourierTransform_localized_schwartz g ω hg v hv g' ω' hg'


  exact isSmoothNear_of_smooth_nonzero_smulLeftCLM_schwartz (𝓕 v) g' x
    (isConicCutoffNear_hasTemperateGrowth g' ω' hg') hg'x f hf

/-- Consequence: the (point) singular support of `𝓕 v` is contained in `{0}`. -/
theorem singularSupport_subset_singleton_fourierTransform_conicCutoff
    (g : E n → ℂ) (ω : Sphere n) (hg : IsConicCutoffNear g ω)
    (v : 𝓢'(E n, ℂ))
    (hv : ∀ (φ : 𝓢(E n, ℂ)), v φ = ∫ x, g x • φ x) :
    singularSupport (𝓕 v) ⊆ {(0 : E n)} := by
  intro x hx
  simp only [Set.mem_singleton_iff]
  by_contra hne
  exact hx (conicCutoff_fourierTransform_smooth_away_from_origin g ω hg v hv x hne)


/-- The ratio `g' / g` of two conic cutoffs is compactly supported when `supp g' ⊆ supp g`. -/
theorem hasCompactSupport_conicCutoff_ratio
    (g g' : E n → ℂ) (ω : Sphere n)
    (hg : IsConicCutoffNear g ω) (hg' : IsConicCutoffNear g' ω)
    (hsup : Function.support g' ⊆ Function.support g) :
    HasCompactSupport (fun x => g' x * (g x)⁻¹) := by sorry


/-- Strengthening of `hsup`: the *closed* support of `g'` is contained in the open support
of `g`. -/
theorem tsupport_conicCutoff_subset_support
    (g g' : E n → ℂ) (ω : Sphere n)
    (hg : IsConicCutoffNear g ω) (hg' : IsConicCutoffNear g' ω)
    (hsup : Function.support g' ⊆ Function.support g) :
    tsupport g' ⊆ Function.support g := by
  intro x hx
  by_cases hx_mem : x ∈ Function.support g'
  · exact hsup hx_mem
  ·


    exfalso
    have hcs := hasCompactSupport_conicCutoff_ratio g g' ω hg hg' hsup

    have hsup_eq : Function.support (fun x => g' x * (g x)⁻¹) = Function.support g' := by
      ext y
      simp only [Function.mem_support, ne_eq]
      constructor
      · intro h heq; exact h (by simp [heq])
      · intro h
        have hgy : g y ≠ 0 := hsup (Function.mem_support.mpr h)
        exact mul_ne_zero h (inv_ne_zero hgy)

    have hts_eq : tsupport (fun x => g' x * (g x)⁻¹) = tsupport g' := by
      simp only [tsupport, hsup_eq]

    have hcompact : IsCompact (tsupport g') := hts_eq ▸ hcs.isCompact


    obtain ⟨_, R', hR'_pos, _, R₀', _, _, ψ', hψ'_hom, hψ'_ne, hg'_eq⟩ := hg'
    have hω_norm : ‖(ω : E n)‖ = 1 := by
      have := ω.2; simp only [Metric.mem_sphere, dist_zero_right] at this; exact this
    have hω_ne : (ω : E n) ≠ 0 := by
      intro h; simp [h] at hω_norm

    have hray : ∀ t : ℝ, R' < t → (t • (ω : E n)) ∈ tsupport g' := by
      intro t ht
      apply subset_tsupport
      rw [Function.mem_support]
      have ht_pos : (0 : ℝ) < t := lt_trans hR'_pos ht
      have hnorm : R' < ‖t • (ω : E n)‖ := by
        rw [norm_smul, Real.norm_of_nonneg (le_of_lt ht_pos), hω_norm, mul_one]; exact ht
      rw [hg'_eq _ hnorm, hψ'_hom t ht_pos (ω : E n) hω_ne]
      exact hψ'_ne

    have hunbounded : ¬ Bornology.IsBounded (tsupport g') := by
      rw [show Bornology.IsBounded (tsupport g') ↔
        ∃ r, tsupport g' ⊆ Metric.ball (0 : E n) r from Metric.isBounded_iff_subset_ball 0]
      push_neg
      intro r hsub
      have hmem := hray (max R' r + 1) (by linarith [le_max_left R' r])
      have hball := hsub hmem
      simp only [Metric.mem_ball, dist_zero_right] at hball
      rw [norm_smul, Real.norm_of_nonneg (by linarith [le_max_left R' r] : (0:ℝ) ≤ max R' r + 1),
          hω_norm, mul_one] at hball
      linarith [le_max_right R' r]

    exact hunbounded hcompact.isBounded


/-- Conic version of `smooth_factorization_smulLeftCLM`: there is a smooth, compactly
supported `μ` with `g' · u = μ · (g · u)` for two conic cutoffs `g, g'` (with appropriate
support inclusion). -/
theorem smooth_factorization_conic_smulLeftCLM (u : 𝓢'(E n, ℂ))
    (g g' : E n → ℂ) (ω : Sphere n)
    (hg : IsConicCutoffNear g ω) (hg' : IsConicCutoffNear g' ω)
    (hsup : Function.support g' ⊆ Function.support g) :
    ∃ (μ : E n → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ ∧ HasCompactSupport μ ∧
      TemperedDistribution.smulLeftCLM ℂ g' u =
        TemperedDistribution.smulLeftCLM ℂ μ (TemperedDistribution.smulLeftCLM ℂ g u) := by

  set μ := fun x => g' x * (g x)⁻¹ with hμ_def

  have htsup : tsupport g' ⊆ Function.support g :=
    tsupport_conicCutoff_subset_support g g' ω hg hg' hsup
  have hμ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) μ :=
    contDiff_div_of_support_subset hg.1 hg'.1 htsup

  have hμ_compact : HasCompactSupport μ :=
    hasCompactSupport_conicCutoff_ratio g g' ω hg hg' hsup
  refine ⟨μ, hμ_smooth, hμ_compact, ?_⟩

  have hg_temp : Function.HasTemperateGrowth g :=
    isConicCutoffNear_hasTemperateGrowth g ω hg
  have hμ_temp : Function.HasTemperateGrowth μ :=
    hμ_compact.hasTemperateGrowth hμ_smooth

  have heq : g * μ = g' := by
    ext x; simp only [Pi.mul_apply, hμ_def]
    by_cases hgx : g x = 0
    · have : g' x = 0 := by
        by_contra h
        exact absurd (Function.mem_support.mp (hsup (Function.mem_support.mpr h)))
          (not_not.mpr hgx)
      simp [hgx, this]
    · field_simp

  rw [show TemperedDistribution.smulLeftCLM ℂ μ (TemperedDistribution.smulLeftCLM ℂ g u)
      = TemperedDistribution.smulLeftCLM ℂ (g * μ) u from
    (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hg_temp hμ_temp u)]
  rw [heq]

/-- The cone singular support of `𝓕 v` is contained in `{Sum.inl 0}` when `v` is
integration against a conic cutoff. -/
theorem coneSingularSupport_subset_singleton_fourierTransform_conicCutoff
    (g : E n → ℂ) (ω : Sphere n) (hg : IsConicCutoffNear g ω)
    (v : 𝓢'(E n, ℂ))
    (hv : ∀ (φ : 𝓢(E n, ℂ)), v φ = ∫ x, g x • φ x) :
    coneSingularSupport (𝓕 v) ⊆ {Sum.inl (0 : E n)} := by
  have hSphere := cssSphere_eq_empty_fourierTransform_conicCutoff g ω hg v hv
  have hRn := singularSupport_subset_singleton_fourierTransform_conicCutoff g ω hg v hv
  intro x hx
  simp only [coneSingularSupport, mem_union, mem_image] at hx
  rcases hx with ⟨s, hs, rfl⟩ | ⟨t, ht, rfl⟩
  · exact mem_singleton_iff.mpr (congrArg Sum.inl (mem_singleton_iff.mp (hRn hs)))
  · exact absurd (hSphere ▸ ht : t ∈ (∅ : Set (Sphere n))) (Set.notMem_empty t)


/-- Conic version of `fourier_compact_cutoff_eq_schwartz_convolution`. -/
theorem fourier_conic_cutoff_eq_schwartz_convolution (u : 𝓢'(E n, ℂ))
    (g g' : E n → ℂ) (ω : Sphere n)
    (hg : IsConicCutoffNear g ω) (hg' : IsConicCutoffNear g' ω)
    (hsup : Function.support g' ⊆ Function.support g) :
    ∃ f : 𝓢(E n, ℂ),
      𝓕 (TemperedDistribution.smulLeftCLM ℂ g' u) =
        schwartzConvolution (𝓕 (TemperedDistribution.smulLeftCLM ℂ g u)) f := by

  obtain ⟨μ, hμ_smooth, hμ_compact, hfactor⟩ :=
    smooth_factorization_conic_smulLeftCLM u g g' ω hg hg' hsup

  obtain ⟨f, hconv⟩ :=
    fourier_smulLeftCLM_eq_schwartzConvolution μ hμ_smooth hμ_compact
      (TemperedDistribution.smulLeftCLM ℂ g u)

  exact ⟨f, by rw [hfactor, hconv]⟩

/-- Conic-cutoff monotonicity of `Css ∘ 𝓕`. -/
theorem cssSphere_mono_conic_cutoff (u : 𝓢'(E n, ℂ))
    (g g' : E n → ℂ) (ω : Sphere n)
    (hg : IsConicCutoffNear g ω) (hg' : IsConicCutoffNear g' ω)
    (hsup : Function.support g' ⊆ Function.support g) :
    ConicSingularSupportSphere (𝓕 (TemperedDistribution.smulLeftCLM ℂ g' u)) ⊆
    ConicSingularSupportSphere (𝓕 (TemperedDistribution.smulLeftCLM ℂ g u)) := by
  obtain ⟨f, hf⟩ := fourier_conic_cutoff_eq_schwartz_convolution u g g' ω hg hg' hsup
  rw [hf]
  exact css_schwartz_convolution _ f

/-- The support of a conic cutoff is open. -/
lemma conicCutoff_support_isOpen (g : E n → ℂ) (ω : Sphere n)
    (hg : IsConicCutoffNear g ω) :
    IsOpen (Function.support g) :=
  hg.1.continuous.isOpen_support


/-- The point `ω` itself lies in `support g` for any conic cutoff `g` near `ω`. -/
theorem conicCutoff_mem_support (g : E n → ℂ) (ω : Sphere n)
    (hg : IsConicCutoffNear g ω) :
    (ω : E n) ∈ Function.support g := by
  obtain ⟨_, R, hR_pos, hR_lt, R₀, _, _, ψ, hψ_hom, hψ_ne, hg_eq⟩ := hg
  have hω_norm : ‖(ω : E n)‖ = 1 := by
    have := ω.2; simp only [Metric.mem_sphere, dist_zero_right] at this; exact this
  have hR_lt_norm : R < ‖(ω : E n)‖ := by rw [hω_norm]; exact hR_lt
  rw [Function.mem_support]
  rw [hg_eq _ hR_lt_norm]
  exact hψ_ne

/-- Neighbourhood formulation: if `ω₁` is not in `Css(𝓕(g₀ · u))`, there are
neighbourhoods `Ũ ∋ ω₀` and `V ∋ ω₁` such that for every conic cutoff `g'` near `ω₀` with
support in `Ũ`, `V` is disjoint from `Css(𝓕(g' · u))`. -/
theorem not_mem_cssSphere_conic_nhds (u : 𝓢'(E n, ℂ))
    (ω₀ : Sphere n) (ω₁ : Sphere n)
    (g₀ : E n → ℂ) (hg₀ : IsConicCutoffNear g₀ ω₀)
    (hω₁_notin : ω₁ ∉ ConicSingularSupportSphere
      (𝓕 (TemperedDistribution.smulLeftCLM ℂ g₀ u))) :
    ∃ (Ũ : Set (E n)) (V : Set (Sphere n)),
      IsOpen Ũ ∧ (ω₀ : E n) ∈ Ũ ∧
      IsOpen V ∧ ω₁ ∈ V ∧
      ∀ (g' : E n → ℂ), IsConicCutoffNear g' ω₀ →
        Function.support g' ⊆ Ũ →
        V ∩ ConicSingularSupportSphere
          (𝓕 (TemperedDistribution.smulLeftCLM ℂ g' u)) = ∅ := by
  refine ⟨Function.support g₀,
    (ConicSingularSupportSphere (𝓕 (TemperedDistribution.smulLeftCLM ℂ g₀ u)))ᶜ,
    conicCutoff_support_isOpen g₀ ω₀ hg₀,
    conicCutoff_mem_support g₀ ω₀ hg₀,
    (cssSphere_isClosed _).isOpen_compl,
    hω₁_notin, ?_⟩
  intro g' hg' hsupp
  have hmono := cssSphere_mono_conic_cutoff u g₀ g' ω₀ hg₀ hg' hsupp
  exact Set.disjoint_iff_inter_eq_empty.mp (disjoint_compl_left.mono_right hmono)

/-- For a conic cutoff `g`, the Fourier transform of `g · u` equals the Schwartz convolution
of `𝓕 u` with some Schwartz function. -/
theorem fourier_conicCutoff_smulLeftCLM_eq_schwartzConvolution
    (g : E n → ℂ) (ω : Sphere n) (hg : IsConicCutoffNear g ω)
    (u : 𝓢'(E n, ℂ)) :
    ∃ f : 𝓢(E n, ℂ),
      𝓕 (TemperedDistribution.smulLeftCLM ℂ g u) = schwartzConvolution (𝓕 u) f := by

  have htg : Function.HasTemperateGrowth g := isConicCutoffNear_hasTemperateGrowth g ω hg


  obtain ⟨μ, hμ_smooth, hμ_compact, hfactor⟩ :=
    smooth_factorization_conic_smulLeftCLM u g g ω hg hg (le_refl _)


  have hprod : TemperedDistribution.smulLeftCLM ℂ μ
      (TemperedDistribution.smulLeftCLM ℂ g u) =
    TemperedDistribution.smulLeftCLM ℂ (g * μ) u :=
    (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply htg (hμ_compact.hasTemperateGrowth hμ_smooth) u)


  have hμg_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (g * μ) :=
    hg.1.mul hμ_smooth
  have hμg_compact : HasCompactSupport (g * μ) :=
    hμ_compact.mul_left

  obtain ⟨f, hf⟩ := fourier_smulLeftCLM_eq_schwartzConvolution (g * μ) hμg_smooth hμg_compact u


  refine ⟨f, ?_⟩
  rw [← hf]
  congr 1
  rw [hfactor, hprod]

end ConeSupport

namespace WavefrontSet

variable (n : ℕ)

/-- The closed unit ball in `ℝⁿ`, used as a compactification of Euclidean space for
defining the scattering wavefront set. -/
def ClosedBall : Type := {x : EuclideanSpace ℝ (Fin n) // ‖x‖ ≤ 1}

/-- The subspace topology on the closed unit ball. -/
instance : TopologicalSpace (ClosedBall n) :=
  inferInstanceAs (TopologicalSpace {x : EuclideanSpace ℝ (Fin n) // ‖x‖ ≤ 1})

/-- The set of pairs `(p, q)` in `ClosedBall × ClosedBall` for which at least one factor
lies on the boundary sphere. -/
def BoundaryProd : Set (ClosedBall n × ClosedBall n) :=
  {pq | ‖pq.1.val‖ = 1 ∨ ‖pq.2.val‖ = 1}

/-- Antipodal map on the closed ball. -/
def ClosedBall.neg (p : ClosedBall n) : ClosedBall n :=
  ⟨-p.val, by rw [norm_neg]; exact p.property⟩

/-- The closed ball has a `Neg` instance given by the antipodal map. -/
instance : Neg (ClosedBall n) where
  neg := ClosedBall.neg n

/-- Computing the underlying vector of `-p`: it is `-p.val`. -/
@[simp]
theorem ClosedBall.neg_val (p : ClosedBall n) : (-p).val = -p.val := rfl

/-- The antipodal map preserves the norm of the underlying vector. -/
@[simp]
theorem ClosedBall.norm_neg_eq (p : ClosedBall n) : ‖(-p).val‖ = ‖p.val‖ := by
  rw [ClosedBall.neg_val, norm_neg]

/-- The antipodal map is an involution: `-(-p) = p`. -/
@[simp]
theorem ClosedBall.neg_neg (p : ClosedBall n) : -(-p) = p := by
  apply Subtype.ext
  simp [ClosedBall.neg_val]

variable {n}

/-- Boundary points of the closed ball are spherical directions. -/
def ClosedBall.toSphere (p : ClosedBall n) (hp : ‖p.val‖ = 1) : ConeSupport.Sphere n :=
  ⟨p.val, by simp [Metric.mem_sphere, dist_zero_right, hp]⟩

/-- Interior points of the closed ball map back to Euclidean space via the
"de-compactification" formula `p ↦ (1 - ‖p‖)⁻¹ p`. -/
def ClosedBall.toEuclidean (p : ClosedBall n) (hp : ‖p.val‖ < 1) :
    EuclideanSpace ℝ (Fin n) :=
  (1 - ‖p.val‖)⁻¹ • p.val

/-- The conic singular support `Css u` on the closed ball: at boundary points it agrees
with the spherical conic singular support, at interior points (after de-compactification)
it agrees with the usual singular support. -/
def Css (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Set (ClosedBall n) :=
  {p | if h : ‖p.val‖ = 1 then
        p.toSphere h ∈ ConeSupport.ConicSingularSupportSphere u
       else

        have hp : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h
        p.toEuclidean hp ∈ ConeSupport.singularSupport u}

/-- The cone support `Csp u` on the closed ball: at boundary points it agrees with the
spherical cone support, at interior points (after de-compactification) it agrees with the
distributional support of `u`. -/
def Csp (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Set (ClosedBall n) :=
  {p | if h : ‖p.val‖ = 1 then
        p.toSphere h ∈ ConeSupport.ConeSupportSphere u
       else
        have hp : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h
        p.toEuclidean hp ∈ Distribution.dsupport u}


/-- If `g · u = 0` and `g x ≠ 0`, then `x` lies outside the distributional support of `u`. -/
theorem notMem_dsupport_of_smulLeftCLM_eq_zero
    {n : ℕ} (u : 𝓢'(ConeSupport.E n, ℂ)) (g : ConeSupport.E n → ℂ) (x : ConeSupport.E n)
    (hg : Function.HasTemperateGrowth g)
    (hg_ne : g x ≠ 0)
    (hgu : TemperedDistribution.smulLeftCLM ℂ g u = 0) :
    x ∉ Distribution.dsupport u := by
  rw [Distribution.notMem_dsupport_iff]
  have hg_cont : Continuous g := hg.1.continuous
  have hV_open : IsOpen {y | g y ≠ 0} := isOpen_ne_fun hg_cont continuous_const
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hV_open x hg_ne
  refine ⟨Metric.ball x r, ?_, Metric.isOpen_ball, Metric.mem_ball_self hr_pos⟩
  intro φ hφ_supp
  have hφ_compact : HasCompactSupport (⇑φ) :=
    (isCompact_closedBall x r).of_isClosed_subset (isClosed_tsupport _)
      (hφ_supp.trans Metric.ball_subset_closedBall)
  have hφ_g_ne : ∀ y ∈ tsupport (⇑φ), g y ≠ 0 := fun y hy => hr_sub (hφ_supp hy)

  set ψ_fun : ConeSupport.E n → ℂ := fun y => (g y)⁻¹ * φ y

  have hψ_compact : HasCompactSupport ψ_fun := by
    apply hφ_compact.mono
    intro y hy
    simp only [Function.mem_support, ne_eq] at hy ⊢
    intro hφ0; apply hy; show (g y)⁻¹ * φ y = 0; rw [hφ0, mul_zero]

  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ_fun := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : g y ≠ 0
    · exact (hg.1.contDiffAt.inv hy).mul φ.smooth'.contDiffAt
    · simp only [ne_eq, not_not] at hy
      have hy_notin : y ∉ tsupport (⇑φ) := fun h => absurd hy (hφ_g_ne y h)
      have h_eq : ψ_fun =ᶠ[nhds y] fun _ => (0 : ℂ) := by
        have h1 := notMem_tsupport_iff_eventuallyEq.mp hy_notin
        filter_upwards [h1] with z hz
        show (g z)⁻¹ * φ z = 0
        have : φ z = 0 := by simpa using hz
        rw [this, mul_zero]
      exact contDiffAt_const.congr_of_eventuallyEq h_eq

  let ψ : 𝓢(ConeSupport.E n, ℂ) := hψ_compact.toSchwartzMap hψ_smooth

  have hgψ : SchwartzMap.smulLeftCLM ℂ g ψ = φ := by
    ext y
    simp only [SchwartzMap.smulLeftCLM_apply_apply hg]
    show g y • ((g y)⁻¹ * φ y) = φ y
    by_cases hy : g y = 0
    · have : φ y = 0 := by
        have h1 : y ∉ Function.support (⇑φ) := fun h' =>
          absurd hy (hφ_g_ne y (subset_tsupport _ h'))
        simpa [Function.mem_support] using h1
      simp [hy, this]
    · rw [smul_eq_mul]; field_simp

  calc u φ = u (SchwartzMap.smulLeftCLM ℂ g ψ) := by rw [hgψ]
    _ = (TemperedDistribution.smulLeftCLM ℂ g u) ψ :=
        TemperedDistribution.smulLeftCLM_apply_apply g u ψ
    _ = (0 : 𝓢'(ConeSupport.E n, ℂ)) ψ := by rw [hgu]
    _ = 0 := ContinuousLinearMap.zero_apply ψ

/-- The cone support `Csp u` on the closed ball is closed. -/
theorem isClosed_csp {n : ℕ} (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    IsClosed (Csp u) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro p hp
  simp only [Set.mem_compl_iff, Csp, Set.mem_setOf_eq] at hp
  by_cases h : ‖p.val‖ = 1
  ·
    rw [dif_pos h] at hp
    simp only [ConeSupport.ConeSupportSphere, Set.mem_setOf_eq, not_not] at hp
    obtain ⟨g, hg_conic, hgu⟩ := hp
    have ⟨hg_smooth, R, hR, hR_lt, R₀, hR₀, hg_supp, ψ, hψ_hom, hψ_ne, hg_eq⟩ := hg_conic
    have hR1 : (0 : ℝ) < R + 1 := by linarith

    set G : ClosedBall n → ℂ := fun q => g ((R + 1) • q.val)
    have hG_cont : Continuous G :=
      hg_smooth.continuous.comp (continuous_const.smul continuous_subtype_val)

    have hNorm : IsOpen {q : ClosedBall n | R / (R + 1) < ‖q.val‖} := by
      have : {q : ClosedBall n | R / (R + 1) < ‖q.val‖} =
          Subtype.val ⁻¹' {v | R / (R + 1) < ‖v‖} := rfl
      rw [this]; exact isOpen_induced (isOpen_lt continuous_const continuous_norm)
    have hp_mem_norm : R / (R + 1) < ‖p.val‖ := by
      rw [h, div_lt_iff₀ hR1]; linarith
    set T := G ⁻¹' {(0 : ℂ)}ᶜ ∩ {q : ClosedBall n | R / (R + 1) < ‖q.val‖}
    refine ⟨T, ?_, (hG_cont.isOpen_preimage _ isOpen_compl_singleton).inter hNorm, ?_⟩
    ·
      intro q hq
      obtain ⟨hqG, hqN⟩ := hq
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hqG
      simp only [Set.mem_setOf_eq] at hqN
      simp only [Set.mem_compl_iff, Csp, Set.mem_setOf_eq]
      by_cases hq1 : ‖q.val‖ = 1
      ·
        rw [dif_pos hq1]
        simp only [ConeSupport.ConeSupportSphere, Set.mem_setOf_eq, not_not]
        have hq_ne : q.val ≠ 0 := by
          intro he; rw [he, norm_zero] at hq1; exact zero_ne_one hq1
        have : R < ‖(R + 1) • q.val‖ := by
          rw [norm_smul, Real.norm_of_nonneg hR1.le, hq1, mul_one]; linarith
        have hψq : ψ q.val ≠ 0 := by
          rwa [← hψ_hom (R+1) hR1 q.val hq_ne, ← hg_eq _ this]
        exact ⟨g, ⟨hg_smooth, R, hR, hR_lt, R₀, hR₀, hg_supp, ψ, hψ_hom, hψq, hg_eq⟩, hgu⟩
      ·
        rw [dif_neg hq1]
        have hq_lt : ‖q.val‖ < 1 := lt_of_le_of_ne q.property hq1
        have hq_ne : q.val ≠ 0 := by
          intro he; rw [he, norm_zero] at hqN; linarith [div_pos hR hR1]
        have h1sub : (0 : ℝ) < 1 - ‖q.val‖ := by linarith
        have htoEuc_norm : R < ‖q.toEuclidean hq_lt‖ := by
          unfold ClosedBall.toEuclidean
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr h1sub.le), inv_mul_eq_div]
          rw [lt_div_iff₀ h1sub]
          have := hqN; rw [div_lt_iff₀ hR1] at this
          linarith
        have hψ_toEuc : g (q.toEuclidean hq_lt) = ψ (q.toEuclidean hq_lt) :=
          hg_eq _ htoEuc_norm
        have hψ_hom_toEuc : ψ (q.toEuclidean hq_lt) = ψ q.val := by
          unfold ClosedBall.toEuclidean
          exact hψ_hom _ (inv_pos.mpr h1sub) q.val hq_ne
        have hG_eq : g ((R + 1) • q.val) = ψ q.val := by
          have : R < ‖(R + 1) • q.val‖ := by
            rw [norm_smul, Real.norm_of_nonneg hR1.le]
            calc R = R * 1 := (mul_one R).symm
              _ < (R + 1) * ‖q.val‖ := by
                  have := hqN; rw [div_lt_iff₀ hR1] at this; linarith
          rw [hg_eq _ this, hψ_hom (R+1) hR1 q.val hq_ne]
        have hψq : ψ q.val ≠ 0 := by rwa [← hG_eq]
        have hg_ne : g (q.toEuclidean hq_lt) ≠ 0 := by rw [hψ_toEuc, hψ_hom_toEuc]; exact hψq
        exact notMem_dsupport_of_smulLeftCLM_eq_zero u g (q.toEuclidean hq_lt)
          (ConeSupport.isConicCutoffNear_hasTemperateGrowth g _ hg_conic) hg_ne hgu
    ·
      refine ⟨?_, hp_mem_norm⟩
      show g ((R + 1) • p.val) ≠ 0
      have : R < ‖(R + 1) • p.val‖ := by
        rw [norm_smul, Real.norm_of_nonneg hR1.le, h, mul_one]; linarith
      have hp_ne : p.val ≠ 0 := by intro he; rw [he, norm_zero] at h; exact zero_ne_one h
      rw [hg_eq _ this, hψ_hom (R+1) hR1 p.val hp_ne]; exact hψ_ne
  ·
    rw [dif_neg h] at hp
    have hp_lt : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h


    set S := (Distribution.dsupport (f := u))ᶜ

    have hp_mem_S : p.toEuclidean hp_lt ∈ S := hp

    set decompact : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
      fun v => (1 - ‖v‖)⁻¹ • v

    have hdecompact_cont : ContinuousOn decompact (Metric.ball 0 1) :=
      ((continuousOn_const.sub continuous_norm.continuousOn).inv₀
        (fun v hv => by
          simp only [Metric.mem_ball, dist_zero_right] at hv
          simp only [ne_eq, sub_eq_zero]; linarith)).smul continuousOn_id

    have hS_open : IsOpen S := (Distribution.isClosed_dsupport).isOpen_compl

    have hW_open : IsOpen (decompact ⁻¹' S ∩ Metric.ball 0 1) := by
      rw [Set.inter_comm]
      exact hdecompact_cont.isOpen_inter_preimage Metric.isOpen_ball hS_open


    have hp_in_W : p.val ∈ decompact ⁻¹' S ∩ Metric.ball 0 1 := by
      constructor
      · show decompact p.val ∈ S
        exact hp_mem_S
      · simp only [Metric.mem_ball, dist_zero_right]; exact hp_lt

    refine ⟨Subtype.val ⁻¹' (decompact ⁻¹' S ∩ Metric.ball 0 1), ?_,
            isOpen_induced hW_open, ?_⟩
    ·
      intro q hq
      simp only [Set.mem_preimage, Set.mem_inter_iff, Metric.mem_ball, dist_zero_right,
        Set.mem_compl_iff, Csp, Set.mem_setOf_eq] at hq ⊢
      obtain ⟨hqS, hq_lt⟩ := hq
      rw [dif_neg (ne_of_lt hq_lt)]

      exact hqS
    ·
      simp only [Set.mem_preimage]; exact hp_in_W

/-- The conic singular support `Css u` on the closed ball is closed. -/
theorem isClosed_css {n : ℕ} (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    IsClosed (Css u) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro p hp
  simp only [Set.mem_compl_iff, Css, Set.mem_setOf_eq] at hp
  by_cases h : ‖p.val‖ = 1
  ·
    rw [dif_pos h] at hp
    simp only [ConeSupport.ConicSingularSupportSphere, Set.mem_setOf_eq, not_not] at hp
    obtain ⟨g, hg_conic, f, hf⟩ := hp
    have ⟨hg_smooth, R, hR, hR_lt, R₀, hR₀, hg_supp, ψ, hψ_hom, hψ_ne, hg_eq⟩ := hg_conic

    have hR1 : (0 : ℝ) < R + 1 := by linarith

    set G : ClosedBall n → ℂ := fun q => g ((R + 1) • q.val)
    have hG_cont : Continuous G :=
      hg_smooth.continuous.comp (continuous_const.smul continuous_subtype_val)

    have hNorm : IsOpen {q : ClosedBall n | R / (R + 1) < ‖q.val‖} := by
      have : {q : ClosedBall n | R / (R + 1) < ‖q.val‖} =
          Subtype.val ⁻¹' {v | R / (R + 1) < ‖v‖} := rfl
      rw [this]; exact isOpen_induced (isOpen_lt continuous_const continuous_norm)
    have hp_mem_norm : R / (R + 1) < ‖p.val‖ := by
      rw [h, div_lt_iff₀ hR1]; linarith
    set T := G ⁻¹' {(0 : ℂ)}ᶜ ∩ {q : ClosedBall n | R / (R + 1) < ‖q.val‖}
    refine ⟨T, ?_, (hG_cont.isOpen_preimage _ isOpen_compl_singleton).inter hNorm, ?_⟩
    ·
      intro q hq
      obtain ⟨hqG, hqN⟩ := hq
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff] at hqG
      simp only [Set.mem_setOf_eq] at hqN
      simp only [Set.mem_compl_iff, Css, Set.mem_setOf_eq]
      by_cases hq1 : ‖q.val‖ = 1
      ·
        rw [dif_pos hq1]
        simp only [ConeSupport.ConicSingularSupportSphere, Set.mem_setOf_eq, not_not]
        have hq_ne : q.val ≠ 0 := by
          intro he; rw [he, norm_zero] at hq1; exact zero_ne_one hq1
        have : R < ‖(R + 1) • q.val‖ := by
          rw [norm_smul, Real.norm_of_nonneg hR1.le, hq1, mul_one]; linarith
        have hψq : ψ q.val ≠ 0 := by
          rwa [← hψ_hom (R+1) hR1 q.val hq_ne, ← hg_eq _ this]
        exact ⟨g, ⟨hg_smooth, R, hR, hR_lt, R₀, hR₀, hg_supp, ψ, hψ_hom, hψq, hg_eq⟩, f, hf⟩
      ·
        rw [dif_neg hq1]
        have hq_lt : ‖q.val‖ < 1 := lt_of_le_of_ne q.property hq1
        simp only [ConeSupport.singularSupport, Set.mem_setOf_eq, not_not]
        have hq_ne : q.val ≠ 0 := by
          intro he; rw [he, norm_zero] at hqN; linarith [div_pos hR hR1]
        have h1sub : (0 : ℝ) < 1 - ‖q.val‖ := by linarith

        have htoEuc_norm : R < ‖q.toEuclidean hq_lt‖ := by
          unfold ClosedBall.toEuclidean
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr h1sub.le), inv_mul_eq_div]
          rw [lt_div_iff₀ h1sub]
          have := hqN; rw [div_lt_iff₀ hR1] at this
          linarith

        have hψ_toEuc : g (q.toEuclidean hq_lt) = ψ (q.toEuclidean hq_lt) :=
          hg_eq _ htoEuc_norm
        have hψ_hom_toEuc : ψ (q.toEuclidean hq_lt) = ψ q.val := by
          unfold ClosedBall.toEuclidean
          exact hψ_hom _ (inv_pos.mpr h1sub) q.val hq_ne
        have hG_eq : g ((R + 1) • q.val) = ψ q.val := by
          have : R < ‖(R + 1) • q.val‖ := by
            rw [norm_smul, Real.norm_of_nonneg hR1.le]
            calc R = R * 1 := (mul_one R).symm
              _ < (R + 1) * ‖q.val‖ := by
                  have := hqN; rw [div_lt_iff₀ hR1] at this; linarith
          rw [hg_eq _ this, hψ_hom (R+1) hR1 q.val hq_ne]
        have hψq : ψ q.val ≠ 0 := by rwa [← hG_eq]
        have hg_ne : g (q.toEuclidean hq_lt) ≠ 0 := by rw [hψ_toEuc, hψ_hom_toEuc]; exact hψq
        exact ConeSupport.isSmoothNear_of_smooth_nonzero_smulLeftCLM_schwartz u g
          (q.toEuclidean hq_lt)
          (ConeSupport.isConicCutoffNear_hasTemperateGrowth g _ hg_conic) hg_ne f hf
    ·
      refine ⟨?_, hp_mem_norm⟩
      show g ((R + 1) • p.val) ≠ 0
      have : R < ‖(R + 1) • p.val‖ := by
        rw [norm_smul, Real.norm_of_nonneg hR1.le, h, mul_one]; linarith
      have hp_ne : p.val ≠ 0 := by intro he; rw [he, norm_zero] at h; exact zero_ne_one h
      rw [hg_eq _ this, hψ_hom (R+1) hR1 p.val hp_ne]; exact hψ_ne
  ·
    rw [dif_neg h] at hp
    simp only [ConeSupport.singularSupport, Set.mem_setOf_eq, not_not] at hp
    obtain ⟨φ, hφ_smooth, hφ_compact, hφ_ne, f, hf⟩ := hp
    have hp_lt : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h


    set Ψ : EuclideanSpace ℝ (Fin n) → ℂ :=
      fun v => if hv : ‖v‖ < 1 then φ ((1 - ‖v‖)⁻¹ • v) else 0

    have hΨp : Ψ p.val ≠ 0 := by simp only [Ψ, dif_pos hp_lt]; exact hφ_ne


    have hΨ_supp : Function.support Ψ ⊆ {v | ‖v‖ < 1} := by
      intro v hv; simp only [Function.mem_support, Ψ] at hv
      by_contra h_ge; simp only [Set.mem_setOf_eq, not_lt] at h_ge
      exact hv (dif_neg (not_lt.mpr h_ge))


    have hΨ_open : IsOpen (Function.support Ψ) := by


      suffices h : Function.support Ψ =
          (fun v => φ ((1 - ‖v‖)⁻¹ • v)) ⁻¹' {(0 : ℂ)}ᶜ ∩ Metric.ball 0 1 by
        rw [h]

        have hcont : ContinuousOn (fun v => φ ((1 - ‖v‖)⁻¹ • v)) (Metric.ball 0 1) :=
          hφ_smooth.continuous.comp_continuousOn
            (((continuousOn_const.sub continuous_norm.continuousOn).inv₀
              (fun v hv => by
                simp only [Metric.mem_ball, dist_zero_right] at hv
                simp only [ne_eq, sub_eq_zero]; linarith)).smul continuousOn_id)
        rw [Set.inter_comm]
        exact hcont.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton

      ext v
      simp only [Function.mem_support, Ψ, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_compl_iff, Set.mem_singleton_iff, Metric.mem_ball, dist_zero_right]
      constructor
      · intro hv
        have hvlt : ‖v‖ < 1 := by
          by_contra hge; simp only [not_lt] at hge
          exact hv (dif_neg (not_lt.mpr hge))
        exact ⟨by rwa [dif_pos hvlt] at hv, hvlt⟩
      · rintro ⟨hvne, hvlt⟩; rwa [dif_pos hvlt]
    refine ⟨Subtype.val ⁻¹' (Function.support Ψ), ?_, isOpen_induced hΨ_open, ?_⟩

    ·
      intro q hq
      simp only [Set.mem_preimage, Function.mem_support, Set.mem_compl_iff, Css,
        Set.mem_setOf_eq] at hq ⊢
      have hq_lt : ‖q.val‖ < 1 := hΨ_supp (Function.mem_support.mpr hq)
      rw [dif_neg (ne_of_lt hq_lt)]
      simp only [ConeSupport.singularSupport, Set.mem_setOf_eq, not_not]


      simp only [Ψ, dif_pos hq_lt] at hq
      exact ⟨φ, hφ_smooth, hφ_compact, hq, f, hf⟩
    ·
      simp only [Set.mem_preimage, Function.mem_support]; exact hΨp

/-- Bundled statement: `Csp u`, `Css u`, and their sphere analogues are all closed; and a
"disjoint Css ⇒ Schwartz" statement holds. -/
theorem isClosed_css_and_schwartz_of_disjoint_conicSupport {n : ℕ} (u : 𝓢'(ConeSupport.E n, ℂ)) :
    IsClosed (Csp u) ∧
    IsClosed (Css u) ∧
    IsClosed (ConeSupport.ConeSupportSphere u) ∧
    IsClosed (ConeSupport.ConicSingularSupportSphere u) ∧
    (∀ (g : ConeSupport.E n → ℂ)
      (hg_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
      (R : ℝ) (hR : 0 < R)
      (hg_supp : Function.support g ⊆ {x : ConeSupport.E n | R ≤ ‖x‖})
      (ψ : ConeSupport.E n → ℂ)
      (hψ_hom : ∀ (a : ℝ), 0 < a → ∀ (x : ConeSupport.E n), x ≠ 0 → ψ (a • x) = ψ x)
      (hg_eq : ∀ x : ConeSupport.E n, R < ‖x‖ → g x = ψ x)
      (hψ_disjoint : Disjoint
        (Function.support (fun ω : ConeSupport.Sphere n => ψ (↑ω)))
        (ConeSupport.ConicSingularSupportSphere u)),
      ∃ (f : SchwartzMap (ConeSupport.E n) ℂ),
        TemperedDistribution.smulLeftCLM ℂ g u = (f : 𝓢'(ConeSupport.E n, ℂ))) :=
  ⟨isClosed_csp u,
   isClosed_css u,
   (ConeSupport.isClosed_coneSupportSphere_and_cssSphere_and_schwartz_of_disjoint u).1,
   (ConeSupport.isClosed_coneSupportSphere_and_cssSphere_and_schwartz_of_disjoint u).2.1,
   fun g hg_smooth R hR hg_supp ψ hψ_hom hg_eq hψ_disjoint =>
     (ConeSupport.isClosed_coneSupportSphere_and_cssSphere_and_schwartz_of_disjoint u).2.2
       g hg_smooth R hR hg_supp ψ hψ_hom hg_eq
       (fun ω hω => Function.notMem_support.mp (Set.disjoint_right.mp hψ_disjoint hω))⟩

/-- The scattering wavefront set `WFsc u` on `ClosedBall × ClosedBall`. A pair `(p, q)`
belongs to `WFsc u` iff there is no localizing function `g`/`φ` (conic at boundary, smooth
compactly-supported at interior) at `p` such that `q ∉ Css(𝓕(g · u))`. -/
def WFsc (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    Set (ClosedBall n × ClosedBall n) :=
  {pq | ¬ (
    if h : ‖pq.1.val‖ = 1 then

      ∃ (g : ConeSupport.E n → ℂ),
        ConeSupport.IsConicCutoffNear g (pq.1.toSphere h) ∧
        pq.2 ∉ Css (𝓕 (TemperedDistribution.smulLeftCLM ℂ g u))
    else

      have hp : ‖pq.1.val‖ < 1 := lt_of_le_of_ne pq.1.property h
      ∃ (φ : ConeSupport.E n → ℂ),
        ContDiff ℝ ↑(⊤ : ℕ∞) φ ∧
        HasCompactSupport φ ∧
        φ (pq.1.toEuclidean hp) ≠ 0 ∧
        pq.2 ∉ Css (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ u))
    )}


/-- Auxiliary: if `g` agrees with the homogeneous `ψ` outside `R`, and `ω ∈ Css u`, then
necessarily `ψ(ω) = 0`. -/
theorem psi_vanishes_on_css_aux {n : ℕ} (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (g : ConeSupport.E n → ℂ)
    (hg_smooth : ContDiff ℝ ↑(⊤ : ℕ∞) g) (R : ℝ) (hR : 0 < R) (hR_lt : R < 1)
    (R₀ : ℝ) (hR₀ : 0 < R₀) (hg_supp : Function.support g ⊆ {x : ConeSupport.E n | R₀ ≤ ‖x‖})
    (ψ : ConeSupport.E n → ℂ)
    (hψ_hom : ∀ (a : ℝ), 0 < a → ∀ (x : ConeSupport.E n), x ≠ 0 → ψ (a • x) = ψ x)
    (hg_eq : ∀ x : ConeSupport.E n, R < ‖x‖ → g x = ψ x)
    (ω : ConeSupport.Sphere n)
    (hω : ω ∈ ConeSupport.ConicSingularSupportSphere u) : ψ (↑ω) = 0 := by sorry

/-- Boundary case of the "subtraction" lemma: at a boundary point `p`, a conic-cutoff
multiple of `u` agrees with `u` modulo a distribution Schwartz at `p`, so `p ∉ Css(u - g·u)`. -/
theorem not_mem_css_sub_smulLeftCLM_boundary
    {n : ℕ} (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (g : ConeSupport.E n → ℂ) (p : ClosedBall n) (hp1 : ‖p.val‖ = 1)
    (hg : ConeSupport.IsConicCutoffNear g (p.toSphere hp1)) :
    p ∉ Css (u - TemperedDistribution.smulLeftCLM ℂ g u) := by
  have hg_conic := hg
  rcases hg with ⟨hg_smooth, R, hR, hR_lt, R₀, hR₀, hg_supp, ψ, hψ_hom, hψ_ne, hg_eq⟩
  have hg_tg : Function.HasTemperateGrowth g :=
    ConeSupport.isConicCutoffNear_hasTemperateGrowth g _ hg_conic
  have hgg_tg : Function.HasTemperateGrowth (g * g) := hg_tg.mul hg_tg
  simp only [Css, Set.mem_setOf_eq, dif_pos hp1]
  simp only [ConeSupport.ConicSingularSupportSphere, Set.mem_setOf_eq, not_not]
  refine ⟨g, hg_conic, ?_⟩
  rw [map_sub, TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hg_tg hg_tg u]
  have hsub : (TemperedDistribution.smulLeftCLM ℂ g) u -
      (TemperedDistribution.smulLeftCLM ℂ (g * g)) u =
      (TemperedDistribution.smulLeftCLM ℂ (g - g * g)) u := by
    have h := TemperedDistribution.smulLeftCLM_sub (F := ℂ) hg_tg hgg_tg
    simp only [h, ContinuousLinearMap.sub_apply]
  rw [hsub]
  exact ConeSupport.css_disjoint_implies_schwartz_general u (g - g * g)
    (hg_smooth.sub (hg_smooth.mul hg_smooth)) R hR
    (fun x => ψ x * (1 - ψ x))
    (fun a ha x hx => by simp only [hψ_hom a ha x hx])
    (fun x hx => by simp only [Pi.sub_apply, Pi.mul_apply, hg_eq x hx]; ring)
    (fun ω hω => by
      have h := psi_vanishes_on_css_aux u g hg_smooth R hR hR_lt R₀ hR₀ hg_supp ψ hψ_hom hg_eq ω hω
      simp only [h]; ring)

/-- Multiplying a tempered distribution by a smooth, compactly-supported, temperate-growth
function yields a distribution that is itself the embedding of a Schwartz function. -/
theorem smulLeftCLM_compactlySupported_isSchwartz
    {n : ℕ} (g : ConeSupport.E n → ℂ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hg_tg : Function.HasTemperateGrowth g)
    (hg_compact : HasCompactSupport g) :
    ∃ (f : SchwartzMap (ConeSupport.E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ g u =
        (SchwartzMap.toTemperedDistributionCLM (ConeSupport.E n) ℂ MeasureTheory.volume) f :=
  ConeSupport.smulLeftCLM_schwartz_of_compactSmooth u g hg_tg.1 hg_compact hg_tg


/-- Interior counterpart of `not_mem_css_sub_smulLeftCLM_boundary`: at an interior point `p`,
the difference `u - φ · u` is smooth near `p` provided `φ` does not vanish at `p`. -/
theorem not_mem_css_sub_smulLeftCLM_interior
    {n : ℕ} (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (φ : ConeSupport.E n → ℂ)
    (hφ_smooth : ContDiff ℝ ↑(⊤ : ℕ∞) φ) (hφ_compact : HasCompactSupport φ)
    (p : ClosedBall n) (hp : ‖p.val‖ < 1)
    (hφ_ne : φ (p.toEuclidean hp) ≠ 0) :
    p ∉ Css (u - TemperedDistribution.smulLeftCLM ℂ φ u) := by
  simp only [Css, Set.mem_setOf_eq, dif_neg (ne_of_lt hp),
    ConeSupport.singularSupport, not_not]
  have hφ_tg : Function.HasTemperateGrowth φ := hφ_compact.hasTemperateGrowth hφ_smooth
  have hφφ_tg : Function.HasTemperateGrowth (φ * φ) := hφ_tg.mul hφ_tg
  refine ⟨φ, hφ_smooth, hφ_compact, hφ_ne, ?_⟩
  rw [map_sub, TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hφ_tg hφ_tg u]
  have hsub : (TemperedDistribution.smulLeftCLM ℂ φ) u -
      (TemperedDistribution.smulLeftCLM ℂ (φ * φ)) u =
      (TemperedDistribution.smulLeftCLM ℂ (φ - φ * φ)) u := by
    have h := TemperedDistribution.smulLeftCLM_sub (F := ℂ) hφ_tg hφφ_tg
    simp only [h, ContinuousLinearMap.sub_apply]
  rw [hsub]
  exact smulLeftCLM_compactlySupported_isSchwartz (φ - φ * φ) u
    (hφ_tg.sub hφφ_tg) (hφ_compact.sub (hφ_compact.mul_left))


set_option maxHeartbeats 400000 in
/-- Subadditivity of `Css`: if `p ∉ Css u₁` and `p ∉ Css u₂`, then `p ∉ Css (u₁ + u₂)`. -/
theorem css_subadditive_not_mem'
    {n : ℕ}
    {u₁ u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    {p : ClosedBall n}
    (h₁ : p ∉ Css u₁) (h₂ : p ∉ Css u₂) :
    p ∉ Css (u₁ + u₂) := by
  simp only [Css, Set.mem_setOf] at h₁ h₂ ⊢
  split_ifs with h
  ·
    rw [dif_pos h] at h₁ h₂
    simp only [ConeSupport.ConicSingularSupportSphere, Set.mem_setOf, not_not] at h₁ h₂ ⊢
    obtain ⟨g₁, hg₁_conic, f₁, hf₁⟩ := h₁
    obtain ⟨g₂, hg₂_conic, f₂, hf₂⟩ := h₂

    refine ⟨g₁ * g₂, ?_, ?_⟩
    ·
      obtain ⟨hg₁_smooth, R₁, hR₁, hR₁_lt, R₀₁, hR₀₁, hg₁_supp, ψ₁, hψ₁_hom, hψ₁_ne, hg₁_eq⟩ := hg₁_conic
      obtain ⟨hg₂_smooth, R₂, hR₂, hR₂_lt, R₀₂, hR₀₂, hg₂_supp, ψ₂, hψ₂_hom, hψ₂_ne, hg₂_eq⟩ := hg₂_conic
      refine ⟨hg₁_smooth.mul hg₂_smooth, max R₁ R₂, lt_max_of_lt_left hR₁,
              max_lt hR₁_lt hR₂_lt,
              max R₀₁ R₀₂, lt_max_of_lt_left hR₀₁, ?_, ψ₁ * ψ₂, ?_, ?_, ?_⟩
      ·
        intro x hx
        simp only [Set.mem_setOf]
        rw [Function.mem_support, Pi.mul_apply] at hx
        have hx_ne : g₁ x ≠ 0 ∧ g₂ x ≠ 0 := mul_ne_zero_iff.mp hx
        have h1 : x ∈ Function.support g₁ := Function.mem_support.mpr hx_ne.1
        have h2 : x ∈ Function.support g₂ := Function.mem_support.mpr hx_ne.2
        exact max_le (hg₁_supp h1) (hg₂_supp h2)
      ·
        intro a ha x hx
        simp only [Pi.mul_apply]
        rw [hψ₁_hom a ha x hx, hψ₂_hom a ha x hx]
      ·
        simp only [Pi.mul_apply]
        exact mul_ne_zero hψ₁_ne hψ₂_ne
      ·
        intro x hx
        simp only [Pi.mul_apply]
        rw [hg₁_eq x (lt_of_le_of_lt (le_max_left _ _) hx),
            hg₂_eq x (lt_of_le_of_lt (le_max_right _ _) hx)]
    ·

      have hg₁_tg : Function.HasTemperateGrowth g₁ :=
        ConeSupport.isConicCutoffNear_hasTemperateGrowth g₁ _ hg₁_conic
      have hg₂_tg : Function.HasTemperateGrowth g₂ :=
        ConeSupport.isConicCutoffNear_hasTemperateGrowth g₂ _ hg₂_conic

      have eq1 : TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂) u₁ =
          TemperedDistribution.smulLeftCLM ℂ g₂ (TemperedDistribution.smulLeftCLM ℂ g₁ u₁) :=
        (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hg₁_tg hg₂_tg u₁).symm


      have mul_comm_g : g₂ * g₁ = g₁ * g₂ := mul_comm g₂ g₁
      have eq2 : TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂) u₂ =
          TemperedDistribution.smulLeftCLM ℂ g₁ (TemperedDistribution.smulLeftCLM ℂ g₂ u₂) := by
        rw [← mul_comm_g]
        exact (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hg₂_tg hg₁_tg u₂).symm

      rw [show TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂) (u₁ + u₂) =
          TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂) u₁ +
          TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂) u₂ from
        map_add (TemperedDistribution.smulLeftCLM ℂ (g₁ * g₂)) u₁ u₂]
      rw [eq1, hf₁, eq2, hf₂]

      rw [ConeSupport.smulLeftCLM_schwartz_embed hg₂_tg f₁]

      rw [ConeSupport.smulLeftCLM_schwartz_embed hg₁_tg f₂]
      exact ⟨SchwartzMap.smulLeftCLM ℂ g₂ f₁ + SchwartzMap.smulLeftCLM ℂ g₁ f₂,
             (map_add (SchwartzMap.toTemperedDistributionCLM _ ℂ _) _ _).symm⟩
  ·
    rw [dif_neg h] at h₁ h₂
    simp only [ConeSupport.singularSupport, Set.mem_setOf, not_not] at h₁ h₂ ⊢
    have hp : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h


    obtain ⟨φ₁, hφ₁_smooth, hφ₁_supp, hφ₁_ne, f₁, hf₁⟩ := h₁
    obtain ⟨φ₂, hφ₂_smooth, hφ₂_supp, hφ₂_ne, f₂, hf₂⟩ := h₂

    have hφ₁_tg : Function.HasTemperateGrowth φ₁ := hφ₁_supp.hasTemperateGrowth hφ₁_smooth
    have hφ₂_tg : Function.HasTemperateGrowth φ₂ := hφ₂_supp.hasTemperateGrowth hφ₂_smooth
    refine ⟨φ₁ * φ₂, hφ₁_smooth.mul hφ₂_smooth, hφ₁_supp.mul_right, ?_, ?_⟩
    ·
      simp only [Pi.mul_apply]
      exact mul_ne_zero hφ₁_ne hφ₂_ne
    ·
      have eq1 : TemperedDistribution.smulLeftCLM ℂ (φ₁ * φ₂) u₁ =
          TemperedDistribution.smulLeftCLM ℂ φ₂ (TemperedDistribution.smulLeftCLM ℂ φ₁ u₁) :=
        (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hφ₁_tg hφ₂_tg u₁).symm
      have eq2 : TemperedDistribution.smulLeftCLM ℂ (φ₁ * φ₂) u₂ =
          TemperedDistribution.smulLeftCLM ℂ φ₁ (TemperedDistribution.smulLeftCLM ℂ φ₂ u₂) := by
        rw [← mul_comm φ₂ φ₁]
        exact (TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hφ₂_tg hφ₁_tg u₂).symm
      rw [ConeSupport.smulLeftCLM_add_right]
      rw [eq1, hf₁, eq2, hf₂]
      rw [ConeSupport.smulLeftCLM_schwartz_embed hφ₂_tg f₁]
      rw [ConeSupport.smulLeftCLM_schwartz_embed hφ₁_tg f₂]
      exact ⟨SchwartzMap.smulLeftCLM ℂ φ₂ f₁ + SchwartzMap.smulLeftCLM ℂ φ₁ f₂,
             (map_add (SchwartzMap.toTemperedDistributionCLM _ ℂ _) _ _).symm⟩


/-- Local-integral formula for the Schwartz convolution: `(u * φ)(θ) = ∫ θ · (u * φ)`,
where `u * φ` on the right is `DifferentialOperators.temperedConvolution`. -/
theorem schwartzConvolution_eq_integral_local
    (u : TemperedDistribution (ConeSupport.E n) ℂ)
    (φ : SchwartzMap (ConeSupport.E n) ℂ)
    (θ : SchwartzMap (ConeSupport.E n) ℂ) :
    (ConeSupport.schwartzConvolution u φ) θ =
      ∫ x, θ x • DifferentialOperators.temperedConvolution u φ x := by sorry


set_option maxHeartbeats 800000 in
/-- Schwartz convolution `u * φ` is pointwise given by a function of temperate growth.
There exists `g` with `Function.HasTemperateGrowth g` such that for all Schwartz `θ`,
`(u * φ)(θ) = ∫ x, θ x • g x`. Combined with smoothness of `g`, this presents
`u * φ` as a tempered distribution arising from a temperate-growth smooth function. -/
theorem schwartzConvolution_eq_temperateGrowth_local
    (u : TemperedDistribution (ConeSupport.E n) ℂ)
    (φ : SchwartzMap (ConeSupport.E n) ℂ) :
    ∃ (g : ConeSupport.E n → ℂ),
      Function.HasTemperateGrowth g ∧
      ∀ (θ : SchwartzMap (ConeSupport.E n) ℂ),
        (ConeSupport.schwartzConvolution u φ) θ = ∫ x, θ x • g x := by
  refine ⟨DifferentialOperators.temperedConvolution u φ, ⟨?_, ?_⟩, ?_⟩
  ·
    exact DifferentialOperators.hormander_convolution_smooth u φ
  ·

    suffices h_gen : ∀ (ψ : SchwartzMap (ConeSupport.E n) ℂ) (m : ℕ),
        ∃ (k : ℕ) (C : ℝ), ∀ x : ConeSupport.E n,
          ‖iteratedFDeriv ℝ m (DifferentialOperators.temperedConvolution u ψ) x‖ ≤
            C * (1 + ‖x‖) ^ k from
      fun m => h_gen φ m
    intro ψ m
    induction m generalizing ψ with
    | zero =>
      obtain ⟨C, k, hC_pos, hbound⟩ :=
        DifferentialOperators.hormander_convolution_polynomial_growth u ψ
      refine ⟨2 * k, C, fun x => ?_⟩
      simp only [iteratedFDeriv_zero_eq_comp]
      have h1 : (0 : ℝ) ≤ 1 + ‖x‖ := by positivity
      have h1' : (1 : ℝ) ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
      have h2 : (1 : ℝ) + ‖x‖ ^ 2 ≤ (1 + ‖x‖) ^ 2 := by nlinarith [norm_nonneg x]
      have h3 : (0 : ℝ) < 1 + ‖x‖ ^ 2 := by positivity
      have rpow_bound : (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) ≤ (1 + ‖x‖) ^ (2 * k) := by
        calc (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2)
            ≤ ((1 + ‖x‖) ^ 2) ^ ((k : ℝ) / 2) :=
              Real.rpow_le_rpow h3.le h2 (by positivity)
          _ = (1 + ‖x‖) ^ ((↑(2 : ℕ) : ℝ) * ((k : ℝ) / 2)) := by
              rw [← Real.rpow_natCast (1 + ‖x‖) 2, ← Real.rpow_mul h1]
          _ = (1 + ‖x‖) ^ (↑k : ℝ) := by congr 1; push_cast; ring
          _ = (1 + ‖x‖) ^ (k : ℕ) := Real.rpow_natCast _ _
          _ ≤ (1 + ‖x‖) ^ (2 * k) := pow_le_pow_right₀ h1' (by omega)
      calc ‖(continuousMultilinearCurryFin0 ℝ (ConeSupport.E n) ℂ).symm
              (DifferentialOperators.temperedConvolution u ψ x)‖
          = ‖DifferentialOperators.temperedConvolution u ψ x‖ :=
            LinearIsometryEquiv.norm_map _ _
        _ ≤ C * (1 + ‖x‖ ^ 2) ^ ((k : ℝ) / 2) := hbound x
        _ ≤ C * (1 + ‖x‖) ^ (2 * k) := by
            linarith [mul_le_mul_of_nonneg_left rpow_bound hC_pos.le]
    | succ m ih =>
      have hsmooth := DifferentialOperators.hormander_convolution_smooth u ψ

      have hderiv_bound : ∀ i : Fin n, ∃ (k : ℕ) (C : ℝ), ∀ x : ConeSupport.E n,
          ‖iteratedFDeriv ℝ m (fun y =>
            fderiv ℝ (DifferentialOperators.temperedConvolution u ψ) y
              (EuclideanSpace.single i 1)) x‖ ≤ C * (1 + ‖x‖) ^ k := by
        intro i
        set ei : ConeSupport.E n := EuclideanSpace.single i 1
        have hcomp : (fun y => fderiv ℝ (DifferentialOperators.temperedConvolution u ψ) y ei) =
            DifferentialOperators.temperedConvolution u (LineDeriv.lineDerivOp ei ψ) := by
          ext y
          rw [← (hsmooth.differentiable (by simp) y).lineDeriv_eq_fderiv]
          exact DifferentialOperators.hormander_convolution_deriv_right u ψ ei y
        rw [hcomp]
        exact ih (LineDeriv.lineDerivOp ei ψ)
      choose ks Cs hCs_bound using hderiv_bound
      set K := Finset.univ.sup ks

      have hunif : ∀ (i : Fin n) (x : ConeSupport.E n),
          ‖iteratedFDeriv ℝ m (fun y =>
            fderiv ℝ (DifferentialOperators.temperedConvolution u ψ) y
              (EuclideanSpace.single i 1)) x‖ ≤ (|Cs i| + 1) * (1 + ‖x‖) ^ K := by
        intro i x
        calc _ ≤ Cs i * (1 + ‖x‖) ^ ks i := hCs_bound i x
          _ ≤ |Cs i| * (1 + ‖x‖) ^ ks i := by
              apply mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
          _ ≤ |Cs i| * (1 + ‖x‖) ^ K := by
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
              exact pow_le_pow_right₀ (by linarith [norm_nonneg x])
                (Finset.le_sup (f := ks) (Finset.mem_univ i))
          _ ≤ (|Cs i| + 1) * (1 + ‖x‖) ^ K := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              linarith


      refine ⟨K, (∑ i : Fin n, (|Cs i| + 1)) + 1, fun x => ?_⟩
      rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ)]

      have hfderiv_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ (DifferentialOperators.temperedConvolution u ψ)) :=
        hsmooth.fderiv_right (by simp)
      calc ‖iteratedFDeriv ℝ m (fderiv ℝ (DifferentialOperators.temperedConvolution u ψ)) x‖
          ≤ ∑ i : Fin n, ‖iteratedFDeriv ℝ m (fun y =>
              fderiv ℝ (DifferentialOperators.temperedConvolution u ψ) y
                (EuclideanSpace.single i 1)) x‖ := by
            apply ContinuousMultilinearMap.opNorm_le_iff (by positivity) |>.mpr
            intro v

            have hcomp : ∀ i : Fin n,
                (fun y => fderiv ℝ (DifferentialOperators.temperedConvolution u ψ) y
                  (EuclideanSpace.single i 1)) =
                (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i (1 : ℝ))) ∘
                  (fderiv ℝ (DifferentialOperators.temperedConvolution u ψ)) := by
              intro i; ext y; simp [ContinuousLinearMap.apply_apply]
            have hcomp2 : ∀ i : Fin n,
                iteratedFDeriv ℝ m (fun y => fderiv ℝ (DifferentialOperators.temperedConvolution u ψ) y
                  (EuclideanSpace.single i 1)) x =
                (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single i (1 : ℝ))).compContinuousMultilinearMap
                  (iteratedFDeriv ℝ m (fderiv ℝ (DifferentialOperators.temperedConvolution u ψ)) x) := by
              intro i; rw [hcomp i]
              exact ContinuousLinearMap.iteratedFDeriv_comp_left _
                hfderiv_smooth.contDiffAt (WithTop.coe_le_coe.mpr le_top)
            set M := iteratedFDeriv ℝ m (fderiv ℝ (DifferentialOperators.temperedConvolution u ψ)) x
            calc ‖M v‖
                ≤ ∑ i : Fin n, ‖M v (EuclideanSpace.single i 1)‖ := by
                  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun w => ?_)
                  have hw_decomp : w = ∑ i : Fin n, (w i : ℝ) • EuclideanSpace.single i (1 : ℝ) := by
                    ext j; simp [Finset.sum_apply, Pi.single_apply]
                  conv_lhs => rw [hw_decomp]
                  calc ‖M v (∑ i, (w i : ℝ) • EuclideanSpace.single i 1)‖
                      = ‖∑ i, (w i : ℝ) • M v (EuclideanSpace.single i 1)‖ := by
                        simp [map_sum, map_smul]
                    _ ≤ ∑ i, ‖(w i : ℝ) • M v (EuclideanSpace.single i 1)‖ := norm_sum_le _ _
                    _ = ∑ i, ‖w i‖ * ‖M v (EuclideanSpace.single i 1)‖ := by simp
                    _ ≤ ∑ i, ‖w‖ * ‖M v (EuclideanSpace.single i 1)‖ := by
                        gcongr with i _; exact PiLp.norm_apply_le w i
                    _ = (∑ i : Fin n, ‖M v (EuclideanSpace.single i 1)‖) * ‖w‖ := by
                        simp_rw [mul_comm ‖w‖ _]; rw [← Finset.sum_mul]
              _ = ∑ i : Fin n, ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ
                    (DifferentialOperators.temperedConvolution u ψ) y
                    (EuclideanSpace.single i 1)) x v‖ := by
                  congr 1; ext i; rw [hcomp2]; rfl
              _ ≤ ∑ i : Fin n, ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ
                    (DifferentialOperators.temperedConvolution u ψ) y
                    (EuclideanSpace.single i 1)) x‖ * ∏ j, ‖v j‖ := by
                  gcongr with i _
                  exact (iteratedFDeriv ℝ m (fun y => fderiv ℝ
                    (DifferentialOperators.temperedConvolution u ψ) y
                    (EuclideanSpace.single i 1)) x).le_opNorm v
              _ = (∑ i : Fin n, ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ
                    (DifferentialOperators.temperedConvolution u ψ) y
                    (EuclideanSpace.single i 1)) x‖) * ∏ j, ‖v j‖ := by
                  rw [Finset.sum_mul]
        _ ≤ ∑ i : Fin n, (|Cs i| + 1) * (1 + ‖x‖) ^ K :=
            Finset.sum_le_sum (fun i _ => hunif i x)
        _ = (∑ i : Fin n, (|Cs i| + 1)) * (1 + ‖x‖) ^ K := by rw [Finset.sum_mul]
        _ ≤ ((∑ i : Fin n, (|Cs i| + 1)) + 1) * (1 + ‖x‖) ^ K := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            linarith
  ·
    exact schwartzConvolution_eq_integral_local u φ

/-- Multiplying a Schwartz convolution `u * φ` on the left by a smooth, compactly
supported cutoff `ψ` yields (the embedding of) a genuine Schwartz function. This is the
local Schwartz-equivalence used to verify smoothness of `u * φ`. -/
theorem smulLeftCLM_schwartzConvolution_eq_schwartz_local
    (u : TemperedDistribution (ConeSupport.E n) ℂ)
    (φ : SchwartzMap (ConeSupport.E n) ℂ)
    (ψ : ConeSupport.E n → ℂ)
    (hψ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hψ_compact : HasCompactSupport ψ) :
    ∃ (f : SchwartzMap (ConeSupport.E n) ℂ),
      TemperedDistribution.smulLeftCLM ℂ ψ (ConeSupport.schwartzConvolution u φ) =
        (f : 𝓢'(ConeSupport.E n, ℂ)) := by
  obtain ⟨g, hg_tempered, hg_eq⟩ := schwartzConvolution_eq_temperateGrowth_local u φ
  have hψg_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => ψ x * g x) :=
    hψ_smooth.mul hg_tempered.1
  have hψg_compact : HasCompactSupport (fun x => ψ x * g x) :=
    hψ_compact.mul_right
  let f : SchwartzMap (ConeSupport.E n) ℂ := hψg_compact.toSchwartzMap hψg_smooth
  use f
  ext θ
  simp only [TemperedDistribution.smulLeftCLM_apply_apply]
  rw [hg_eq]
  rw [SchwartzMap.coe_apply]
  congr 1
  ext x
  by_cases hψ_tg : Function.HasTemperateGrowth ψ
  · simp only [SchwartzMap.smulLeftCLM_apply_apply hψ_tg]
    simp only [smul_eq_mul, f, HasCompactSupport.toSchwartzMap_toFun]
    ring
  · exfalso
    exact hψ_tg (hψ_compact.hasTemperateGrowth hψ_smooth)


/-- The Schwartz convolution `u * φ` is smooth near every point. This is the local
smoothness statement underlying the fact that `WFsc` of `u * φ` is empty in the
interior of the closed ball. -/
theorem isSmoothNear_schwartzConvolution_local'
    {n : ℕ}
    (u : TemperedDistribution (ConeSupport.E n) ℂ)
    (φ : SchwartzMap (ConeSupport.E n) ℂ)
    (x₀ : ConeSupport.E n) :
    ConeSupport.IsSmoothNear (ConeSupport.schwartzConvolution u φ) x₀ := by
  have hx_nhds : (Set.univ : Set (ConeSupport.E n)) ∈ nhds x₀ := Filter.univ_mem
  obtain ⟨ψ₀, -, hψ₀_compact, hψ₀_smooth, -, hψ₀_x⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) hx_nhds
  let ψ : ConeSupport.E n → ℂ := Complex.ofRealCLM ∘ ψ₀
  have hψ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ :=
    Complex.ofRealCLM.contDiff.comp hψ₀_smooth
  have hψ_compact : HasCompactSupport ψ := hψ₀_compact.comp_left (map_zero _)
  have hψ_x : ψ x₀ ≠ 0 := by
    simp only [ψ, Function.comp, Complex.ofRealCLM_apply, Complex.ofReal_ne_zero, hψ₀_x]
    exact one_ne_zero
  obtain ⟨f, hf⟩ := smulLeftCLM_schwartzConvolution_eq_schwartz_local u φ ψ hψ_smooth hψ_compact
  exact ⟨ψ, hψ_smooth, hψ_compact, hψ_x, f, hf⟩


/-- Restricting `u` by a conic cutoff `g` near `ω` can only shrink the spherical
conic singular support of `𝓕 u`. Concretely, `CSS_{sphere}(𝓕 (g·u)) ⊆ CSS_{sphere}(𝓕 u)`. -/
theorem cssSphere_fourier_conicCutoff_subset'
    {n : ℕ} (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (g : ConeSupport.E n → ℂ) (ω : ConeSupport.Sphere n)
    (hg : ConeSupport.IsConicCutoffNear g ω) :
    ConeSupport.ConicSingularSupportSphere
      (𝓕 (TemperedDistribution.smulLeftCLM ℂ g u)) ⊆
    ConeSupport.ConicSingularSupportSphere (𝓕 u) := by
  obtain ⟨f, hf⟩ := ConeSupport.fourier_conicCutoff_smulLeftCLM_eq_schwartzConvolution g ω hg u
  rw [hf]
  exact ConeSupport.css_schwartz_convolution _ f

/-- Conic cutoff variant for the ordinary singular support: applying a conic cutoff `g`
to `u` can only shrink the singular support of `𝓕 u`. -/
theorem singularSupport_fourier_conicCutoff_subset'
    {n : ℕ} (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (g : ConeSupport.E n → ℂ) (ω : ConeSupport.Sphere n)
    (hg : ConeSupport.IsConicCutoffNear g ω) :
    ConeSupport.singularSupport
      (𝓕 (TemperedDistribution.smulLeftCLM ℂ g u)) ⊆
    ConeSupport.singularSupport (𝓕 u) := by
  obtain ⟨f, hf⟩ := ConeSupport.fourier_conic_cutoff_eq_schwartz_convolution
    u g g ω hg hg (le_refl _)
  rw [hf]
  intro x hx
  simp only [ConeSupport.singularSupport, Set.mem_setOf_eq] at hx
  exact absurd (isSmoothNear_schwartzConvolution_local'
    (𝓕 (TemperedDistribution.smulLeftCLM ℂ g u)) f x) hx


/-- Auxiliary form of `not_mem_css_schwartz'`: a Schwartz function (viewed as a tempered
distribution via `schwEmbed`) has empty conic singular support on the closed-ball
compactification. -/
lemma not_mem_css_schwartz'_aux {n : ℕ} (f : SchwartzMap (ConeSupport.E n) ℂ)
    (p : ClosedBall n) :
    p ∉ Css (ConeSupport.schwEmbed f) := by
  simp only [Css, Set.mem_setOf]
  split_ifs with h
  ·
    simp only [ConeSupport.ConicSingularSupportSphere, Set.mem_setOf, not_not]
    obtain ⟨g, hg⟩ := ConeSupport.exists_conicCutoff (p.toSphere h)
    exact ⟨g, hg, SchwartzMap.smulLeftCLM ℂ g f,
      ConeSupport.smulLeftCLM_schwEmbed_eq_local g f⟩
  ·
    simp only [ConeSupport.singularSupport, Set.mem_setOf, not_not]
    have hp : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h
    let c := p.toEuclidean hp
    let b : ContDiffBump c := ⟨1, 2, one_pos, by norm_num⟩
    refine ⟨fun x => Complex.ofReal (b x), ?_, ?_, ?_,
      SchwartzMap.smulLeftCLM ℂ (fun x => Complex.ofReal (b x)) f,
      ConeSupport.smulLeftCLM_schwEmbed_eq_local _ f⟩
    · rw [contDiff_infty]; intro k
      exact_mod_cast Complex.ofRealCLM.contDiff.comp b.contDiff
    · exact b.hasCompactSupport.comp_left Complex.ofReal_zero
    · have hcenter : b.toFun (p.toEuclidean hp) = 1 :=
        b.one_of_mem_closedBall (Metric.mem_closedBall_self (le_of_lt one_pos))
      simp [hcenter]


/-- Decomposition criterion for the scattering wavefront set. If `u = a + b` with
`p ∉ Css a` and `q ∉ Css (𝓕 b)`, then `(p, q)` lies outside `WFsc u`. This is one of
the two main directions of the decomposition characterisation of `WFsc`. -/
theorem decomp_implies_not_mem_wfsc
    {n : ℕ}
    {u a b : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    (huab : u = a + b)
    {p q : ClosedBall n}
    (hpq : (p, q) ∈ BoundaryProd n)
    (hpa : p ∉ Css a) (hqfb : q ∉ Css (𝓕 b)) :
    (p, q) ∉ WFsc u := by

  simp only [WFsc, Set.mem_setOf_eq, not_not]
  simp only [Css, Set.mem_setOf] at hpa
  by_cases hp1 : ‖p.val‖ = 1
  ·
    rw [dif_pos hp1]
    rw [dif_pos hp1] at hpa
    simp only [ConeSupport.ConicSingularSupportSphere, Set.mem_setOf, not_not] at hpa
    obtain ⟨g, hg, f, hf⟩ := hpa

    refine ⟨g, hg, ?_⟩

    rw [huab, ConeSupport.smulLeftCLM_add_right]

    rw [FourierTransform.fourier_add]

    apply css_subadditive_not_mem'
    ·
      rw [hf, TemperedDistribution.fourier_toTemperedDistributionCLM_eq]
      exact not_mem_css_schwartz'_aux (𝓕 f) q
    ·
      simp only [Css, Set.mem_setOf]
      by_cases hq1 : ‖q.val‖ = 1
      · rw [dif_pos hq1]
        intro hmem_css
        simp only [Css, Set.mem_setOf, dif_pos hq1] at hqfb
        exact hqfb (cssSphere_fourier_conicCutoff_subset' b g (p.toSphere hp1) hg hmem_css)
      · rw [dif_neg hq1]
        intro hmem_ss
        simp only [Css, Set.mem_setOf, dif_neg hq1] at hqfb
        exact hqfb (singularSupport_fourier_conicCutoff_subset' b g (p.toSphere hp1) hg hmem_ss)
  ·
    rw [dif_neg hp1]
    have hp_lt : ‖p.val‖ < 1 := lt_of_le_of_ne p.property hp1
    rw [dif_neg hp1] at hpa
    simp only [ConeSupport.singularSupport, Set.mem_setOf, not_not] at hpa
    obtain ⟨φ, hφ_smooth, hφ_compact, hφ_ne, f, hf⟩ := hpa

    refine ⟨φ, hφ_smooth, hφ_compact, hφ_ne, ?_⟩

    rw [huab, ConeSupport.smulLeftCLM_add_right]

    rw [FourierTransform.fourier_add]

    apply css_subadditive_not_mem'
    ·
      rw [hf, TemperedDistribution.fourier_toTemperedDistributionCLM_eq]
      exact not_mem_css_schwartz'_aux (𝓕 f) q
    ·
      have hq1 : ‖q.val‖ = 1 := by
        simp only [BoundaryProd, Set.mem_setOf_eq] at hpq
        exact hpq.resolve_left hp1

      obtain ⟨f', hf'⟩ :=
        ConeSupport.fourier_smulLeftCLM_eq_schwartzConvolution φ hφ_smooth hφ_compact b
      rw [hf']
      simp only [Css, Set.mem_setOf, dif_pos hq1]
      intro hmem_css
      simp only [Css, Set.mem_setOf, dif_pos hq1] at hqfb
      exact hqfb (ConeSupport.css_schwartz_convolution (𝓕 b) f' hmem_css)


/-- Forward direction of the decomposition characterisation: if `(p, q) ∉ WFsc u`
then `u` can be written as `a + b` with `p ∉ Css a` and `q ∉ Css (𝓕 b)`. The
witnesses are built explicitly from the cutoff coming from `(p, q) ∉ WFsc u`. -/
theorem wfsc_forward_decomp
    {n : ℕ} {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)} {p q : ClosedBall n}
    (h : (p, q) ∉ WFsc u) :
    ∃ a b : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ),
      u = a + b ∧ p ∉ Css a ∧ q ∉ Css (𝓕 b) := by
  simp only [WFsc, Set.mem_setOf_eq, not_not] at h
  by_cases hp1 : ‖p.val‖ = 1
  · rw [dif_pos hp1] at h
    obtain ⟨g, hg_conic, hq_css⟩ := h
    exact ⟨u - TemperedDistribution.smulLeftCLM ℂ g u,
           TemperedDistribution.smulLeftCLM ℂ g u,
           (sub_add_cancel u _).symm,
           not_mem_css_sub_smulLeftCLM_boundary u g p hp1 hg_conic,
           hq_css⟩
  · have hp_lt : ‖p.val‖ < 1 := lt_of_le_of_ne p.property hp1
    rw [dif_neg hp1] at h
    obtain ⟨φ, hφ_smooth, hφ_compact, hφ_ne, hq_css⟩ := h
    exact ⟨u - TemperedDistribution.smulLeftCLM ℂ φ u,
           TemperedDistribution.smulLeftCLM ℂ φ u,
           (sub_add_cancel u _).symm,
           not_mem_css_sub_smulLeftCLM_interior u φ hφ_smooth hφ_compact p hp_lt hφ_ne,
           hq_css⟩


/-- Subadditivity of the scattering wavefront set: if `(p, q) ∉ WFsc u₁` and
`(p, q) ∉ WFsc u₂`, then `(p, q) ∉ WFsc (u₁ + u₂)`. Equivalently,
`WFsc (u₁ + u₂) ⊆ WFsc u₁ ∪ WFsc u₂`. -/
theorem wfsc_subadditive
    {n : ℕ}
    (u₁ u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (p q : ClosedBall n)
    (h₁ : (p, q) ∉ WFsc u₁) (h₂ : (p, q) ∉ WFsc u₂) :
    (p, q) ∉ WFsc (u₁ + u₂) := by

  by_cases hpq : (p, q) ∈ BoundaryProd n
  ·
    obtain ⟨a₁, b₁, hu₁, hp_a₁, hq_fb₁⟩ := wfsc_forward_decomp h₁
    obtain ⟨a₂, b₂, hu₂, hp_a₂, hq_fb₂⟩ := wfsc_forward_decomp h₂
    have hsum : u₁ + u₂ = (a₁ + a₂) + (b₁ + b₂) := by rw [hu₁, hu₂]; abel
    have hp_sum : p ∉ Css (a₁ + a₂) := css_subadditive_not_mem' hp_a₁ hp_a₂
    have hq_fsum : q ∉ Css (𝓕 (b₁ + b₂)) := by
      rw [FourierTransform.fourier_add]
      exact css_subadditive_not_mem' hq_fb₁ hq_fb₂
    exact decomp_implies_not_mem_wfsc hsum hpq hp_sum hq_fsum
  ·
    simp only [BoundaryProd, Set.mem_setOf_eq, not_or] at hpq
    obtain ⟨hp_ne, hq_ne⟩ := hpq
    simp only [WFsc, Set.mem_setOf_eq, not_not]
    rw [dif_neg hp_ne]
    simp only [WFsc, Set.mem_setOf_eq, not_not] at h₁
    rw [dif_neg hp_ne] at h₁
    obtain ⟨φ, hφ_smooth, hφ_compact, hφ_ne, hq_css⟩ := h₁
    refine ⟨φ, hφ_smooth, hφ_compact, hφ_ne, ?_⟩
    rw [ConeSupport.smulLeftCLM_add_right, FourierTransform.fourier_add]
    apply css_subadditive_not_mem' hq_css
    simp only [Css, Set.mem_setOf, dif_neg hq_ne, ConeSupport.singularSupport, not_not]
    obtain ⟨f, hf⟩ :=
      ConeSupport.fourier_smulLeftCLM_eq_schwartzConvolution φ hφ_smooth hφ_compact u₂
    rw [hf]
    exact isSmoothNear_schwartzConvolution_local' (𝓕 u₂) f _


/-- Every point of the closed-ball compactification lies outside the `Css` of an
embedded Schwartz function. This is the public form of `not_mem_css_schwartz'_aux`. -/
lemma not_mem_css_schwartz' {n : ℕ} (f : SchwartzMap (ConeSupport.E n) ℂ)
    (p : ClosedBall n) :
    p ∉ Css (ConeSupport.schwEmbed f) := by
  simp only [Css, Set.mem_setOf]
  split_ifs with h
  ·
    simp only [ConeSupport.ConicSingularSupportSphere, Set.mem_setOf, not_not]
    obtain ⟨g, hg⟩ := ConeSupport.exists_conicCutoff (p.toSphere h)
    exact ⟨g, hg, SchwartzMap.smulLeftCLM ℂ g f,
      ConeSupport.smulLeftCLM_schwEmbed_eq_local g f⟩
  ·
    simp only [ConeSupport.singularSupport, Set.mem_setOf, not_not]
    have hp : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h
    let c := p.toEuclidean hp
    let b : ContDiffBump c := ⟨1, 2, one_pos, by norm_num⟩
    refine ⟨fun x => Complex.ofReal (b x), ?_, ?_, ?_,
      SchwartzMap.smulLeftCLM ℂ (fun x => Complex.ofReal (b x)) f,
      ConeSupport.smulLeftCLM_schwEmbed_eq_local _ f⟩
    · rw [contDiff_infty]; intro k
      exact_mod_cast Complex.ofRealCLM.contDiff.comp b.contDiff
    · exact b.hasCompactSupport.comp_left Complex.ofReal_zero
    · have hcenter : b.toFun (p.toEuclidean hp) = 1 :=
        b.one_of_mem_closedBall (Metric.mem_closedBall_self (le_of_lt one_pos))
      simp [hcenter]


/-- If the first coordinate `p` lies outside the cone support `Css u`, then `(p, q)`
lies outside the scattering wavefront set `WFsc u` for any second coordinate `q`.
This is the "spatial" half of the projection bound `π₁ (WFsc u) ⊆ Css u`. -/
theorem not_mem_wfsc_of_not_mem_css
    {n : ℕ} {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    {p q : ClosedBall n} (_hpq : (p, q) ∈ BoundaryProd n)
    (hp : p ∉ Css u) :
    (p, q) ∉ WFsc u := by
  simp only [WFsc, Set.mem_setOf_eq, not_not]
  simp only [Css, Set.mem_setOf] at hp
  by_cases h : ‖p.val‖ = 1
  ·
    rw [dif_pos h]
    rw [dif_pos h] at hp
    simp only [ConeSupport.ConicSingularSupportSphere, Set.mem_setOf, not_not] at hp
    obtain ⟨g, hg, f, hf⟩ := hp
    refine ⟨g, hg, ?_⟩

    rw [hf, TemperedDistribution.fourier_toTemperedDistributionCLM_eq]
    exact not_mem_css_schwartz' (𝓕 f) q
  ·
    rw [dif_neg h]
    have hp_lt : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h
    rw [dif_neg h] at hp
    simp only [ConeSupport.singularSupport, Set.mem_setOf, not_not] at hp
    obtain ⟨φ, hφ_smooth, hφ_compact, hφ_ne, f, hf⟩ := hp
    refine ⟨φ, hφ_smooth, hφ_compact, hφ_ne, ?_⟩

    rw [hf, TemperedDistribution.fourier_toTemperedDistributionCLM_eq]
    exact not_mem_css_schwartz' (𝓕 f) q


/-- Conic-cutoff monotonicity for the spherical conic singular support of the Fourier
transform: multiplying `u` by a conic cutoff `g` near `ω` can only shrink
`CSS_{sphere}(𝓕 u)`. -/
theorem cssSphere_fourier_conicCutoff_subset
    {n : ℕ} (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (g : ConeSupport.E n → ℂ) (ω : ConeSupport.Sphere n)
    (hg : ConeSupport.IsConicCutoffNear g ω) :
    ConeSupport.ConicSingularSupportSphere
      (𝓕 (TemperedDistribution.smulLeftCLM ℂ g u)) ⊆
    ConeSupport.ConicSingularSupportSphere (𝓕 u) := by
  obtain ⟨f, hf⟩ := ConeSupport.fourier_conicCutoff_smulLeftCLM_eq_schwartzConvolution g ω hg u
  rw [hf]
  exact ConeSupport.css_schwartz_convolution _ f


/-- Conic-cutoff monotonicity for the ordinary singular support of the Fourier transform.
Multiplying `u` by a conic cutoff `g` near `ω` cannot enlarge `singularSupport (𝓕 u)`. -/
theorem singularSupport_fourier_conicCutoff_subset
    {n : ℕ} (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (g : ConeSupport.E n → ℂ) (ω : ConeSupport.Sphere n)
    (hg : ConeSupport.IsConicCutoffNear g ω) :
    ConeSupport.singularSupport
      (𝓕 (TemperedDistribution.smulLeftCLM ℂ g u)) ⊆
    ConeSupport.singularSupport (𝓕 u) := by


  obtain ⟨f, hf⟩ := ConeSupport.fourier_conic_cutoff_eq_schwartz_convolution
    u g g ω hg hg (le_refl _)

  rw [hf]


  intro x hx
  simp only [ConeSupport.singularSupport, Set.mem_setOf_eq] at hx
  exact absurd (isSmoothNear_schwartzConvolution_local'
    (𝓕 (TemperedDistribution.smulLeftCLM ℂ g u)) f x) hx

/-- If the second coordinate `q` lies outside `Css (𝓕 u)`, then `(p, q)` lies outside
`WFsc u`. This is the "frequency" half of the projection bound `π₂ (WFsc u) ⊆ Css (𝓕 u)`. -/
theorem not_mem_wfsc_of_not_mem_css_fourier
    {n : ℕ} {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    {p q : ClosedBall n} (hpq : (p, q) ∈ BoundaryProd n)
    (hq : q ∉ Css (𝓕 u)) :
    (p, q) ∉ WFsc u := by


  intro hmem
  simp only [WFsc, Set.mem_setOf_eq] at hmem
  apply hmem
  by_cases hp1 : ‖p.val‖ = 1
  ·
    rw [dif_pos hp1]
    obtain ⟨g, hg⟩ := ConeSupport.exists_conicCutoff (p.toSphere hp1)
    refine ⟨g, hg, ?_⟩
    simp only [Css, Set.mem_setOf_eq]
    by_cases hq1 : ‖q.val‖ = 1
    ·
      rw [dif_pos hq1]
      intro hmem_css
      simp only [Css, Set.mem_setOf_eq, dif_pos hq1] at hq
      exact hq (cssSphere_fourier_conicCutoff_subset u g (p.toSphere hp1) hg hmem_css)
    ·
      rw [dif_neg hq1]
      have hq_lt : ‖q.val‖ < 1 := lt_of_le_of_ne q.property hq1
      intro hmem_ss
      simp only [Css, Set.mem_setOf_eq, dif_neg hq1] at hq
      exact hq (singularSupport_fourier_conicCutoff_subset u g (p.toSphere hp1) hg hmem_ss)
  ·
    rw [dif_neg hp1]
    have hp_lt : ‖p.val‖ < 1 := lt_of_le_of_ne p.property hp1

    have hq1 : ‖q.val‖ = 1 := by
      simp only [BoundaryProd, Set.mem_setOf_eq] at hpq
      exact hpq.resolve_left hp1

    set x₀ := p.toEuclidean hp_lt
    set χ : ContDiffBump x₀ := ⟨1, 2, one_pos, by norm_num⟩
    set φ := fun x => Complex.ofReal (χ x)
    have hφ_smooth : ContDiff ℝ ↑(⊤ : ℕ∞) φ := by
      rw [contDiff_infty]; intro k
      exact_mod_cast Complex.ofRealCLM.contDiff.comp χ.contDiff
    have hφ_compact : HasCompactSupport φ :=
      χ.hasCompactSupport.comp_left Complex.ofReal_zero
    refine ⟨φ, hφ_smooth, hφ_compact, ?_, ?_⟩
    ·
      have h1 : χ x₀ = 1 :=
        χ.one_of_mem_closedBall (Metric.mem_closedBall_self (le_of_lt χ.rIn_pos))
      show φ x₀ ≠ 0
      simp only [φ, h1, Complex.ofReal_one]
      exact one_ne_zero
    ·
      obtain ⟨f, hf⟩ :=
        ConeSupport.fourier_smulLeftCLM_eq_schwartzConvolution φ hφ_smooth hφ_compact u
      rw [hf]
      simp only [Css, Set.mem_setOf_eq, dif_pos hq1]
      intro hmem_css
      simp only [Css, Set.mem_setOf_eq, dif_pos hq1] at hq
      exact hq (ConeSupport.css_schwartz_convolution (𝓕 u) f hmem_css)

/-- The zero distribution has empty closed-ball cone support: every `p : ClosedBall n`
lies outside `Css 0`. -/
lemma not_mem_css_zero' {n : ℕ} (p : ClosedBall n) :
    p ∉ Css (0 : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) := by
  simp only [Css, Set.mem_setOf]
  split_ifs with h
  ·
    simp only [ConeSupport.ConicSingularSupportSphere, Set.mem_setOf, not_not]
    obtain ⟨g, hg⟩ := ConeSupport.exists_conicCutoff (p.toSphere h)
    exact ⟨g, hg, 0, by simp [map_zero]⟩
  ·
    simp only [ConeSupport.singularSupport, Set.mem_setOf, not_not]
    have hp : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h
    let c := p.toEuclidean hp
    let b : ContDiffBump c := ⟨1, 2, one_pos, by norm_num⟩
    refine ⟨fun x => Complex.ofReal (b x), ?_, ?_, ?_, 0, by simp [map_zero]⟩
    · rw [contDiff_infty]; intro k
      exact_mod_cast Complex.ofRealCLM.contDiff.comp b.contDiff
    · exact b.hasCompactSupport.comp_left Complex.ofReal_zero
    · have hcenter : b.toFun (p.toEuclidean hp) = 1 :=
        b.one_of_mem_closedBall (Metric.mem_closedBall_self (le_of_lt one_pos))
      simp [hcenter]

/-- Decomposition characterisation of the scattering wavefront set: on the boundary
product, `(p, q) ∉ WFsc u` iff `u` decomposes as `u₁ + u₂` with `p ∉ Css u₁` and
`q ∉ Css (𝓕 u₂)`. This is one of the central structural results of Section 12. -/
theorem not_mem_wfsc_iff_exists_decomp
    {n : ℕ}
    {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    {p q : ClosedBall n} (hpq : (p, q) ∈ BoundaryProd n) :
    (p, q) ∉ WFsc u ↔
    ∃ u₁ u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ),
      u = u₁ + u₂ ∧ p ∉ Css u₁ ∧ q ∉ Css (𝓕 u₂) := by
  constructor
  ·
    intro hnotin
    simp only [WFsc, Set.mem_setOf_eq, not_not] at hnotin
    by_cases hp1 : ‖p.val‖ = 1
    ·
      rw [dif_pos hp1] at hnotin
      obtain ⟨g, hg_conic, hq_css⟩ := hnotin
      exact ⟨u - TemperedDistribution.smulLeftCLM ℂ g u,
             TemperedDistribution.smulLeftCLM ℂ g u,
             (sub_add_cancel u _).symm,
             not_mem_css_sub_smulLeftCLM_boundary u g p hp1 hg_conic,
             hq_css⟩
    ·
      have hp_lt : ‖p.val‖ < 1 := lt_of_le_of_ne p.property hp1
      rw [dif_neg hp1] at hnotin
      obtain ⟨φ, hφ_smooth, hφ_compact, hφ_ne, hq_css⟩ := hnotin
      exact ⟨u - TemperedDistribution.smulLeftCLM ℂ φ u,
             TemperedDistribution.smulLeftCLM ℂ φ u,
             (sub_add_cancel u _).symm,
             not_mem_css_sub_smulLeftCLM_interior u φ hφ_smooth hφ_compact p hp_lt hφ_ne,
             hq_css⟩
  ·
    rintro ⟨u₁, u₂, hudecomp, hp_u₁, hq_fu₂⟩
    have h₁ : (p, q) ∉ WFsc u₁ := not_mem_wfsc_of_not_mem_css hpq hp_u₁
    have h₂ : (p, q) ∉ WFsc u₂ := not_mem_wfsc_of_not_mem_css_fourier hpq hq_fu₂
    rw [hudecomp]
    exact wfsc_subadditive u₁ u₂ p q h₁ h₂


/-- Fourier inversion squared for Schwartz functions: applying the Fourier transform
twice equals reflection `x ↦ φ(-x)`, expressed via the Schwartz reflection CLM. -/
lemma schwartz_doubleFourier_eq_compNeg
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    𝓕 (𝓕 φ) = ConeSupport.schwartzReflectionCLM φ := by
  show 𝓕 (𝓕 φ) = (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.neg (R := ℝ) (M := EuclideanSpace ℝ (Fin n)))) φ
  have negCLE_eq : (LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv =
      ContinuousLinearEquiv.neg ℝ := by ext x; simp
  have key : φ = (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv) (𝓕 (𝓕 φ)) := by
    rw [← SchwartzMap.fourierInv_apply_eq (𝓕 φ)]
    exact (FourierTransform.fourierInv_fourier_eq φ).symm
  have negNeg : ∀ g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
        (LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv)
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv) g) = g := by
    intro g; ext x; simp [SchwartzMap.compCLMOfContinuousLinearEquiv]
  have step := congr_arg (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (LinearIsometryEquiv.neg ℝ (E := EuclideanSpace ℝ (Fin n))).toContinuousLinearEquiv) key
  rw [negNeg] at step
  rw [negCLE_eq] at step
  exact step.symm


/-- Distributional Fourier inversion squared: `𝓕 (𝓕 u) = u ∘ (-·)` (reflection)
for every tempered distribution `u`. Dual to `schwartz_doubleFourier_eq_compNeg`. -/
lemma doubleFourier_eq_reflection
    (u : TemperedDistribution (ConeSupport.E n) ℂ) :
    𝓕 (𝓕 u) = ConeSupport.reflection u := by
  ext φ
  simp only [TemperedDistribution.fourier_apply]
  show u (𝓕 (𝓕 φ)) = (u.comp ConeSupport.schwartzReflectionCLM) φ
  simp only [ContinuousLinearMap.comp_apply]
  congr 1
  exact schwartz_doubleFourier_eq_compNeg φ


/-- Singular support is equivariant under reflection: `x ∈ singularSupport (reflect v)`
iff `-x ∈ singularSupport v`. -/
theorem singularSupport_reflection
    (v : TemperedDistribution (ConeSupport.E n) ℂ) (x : ConeSupport.E n) :
    x ∈ ConeSupport.singularSupport (ConeSupport.reflection v) ↔
    (-x) ∈ ConeSupport.singularSupport v := by

  simp only [ConeSupport.singularSupport, mem_setOf_eq]

  constructor
  ·
    intro hx hcontra
    apply hx

    obtain ⟨φ, hsmooth, hcompact, hne, f, hf⟩ := hcontra

    refine ⟨φ ∘ Neg.neg,
      hsmooth.comp (ContinuousLinearEquiv.neg ℝ).contDiff,
      hcompact.comp_homeomorph (Homeomorph.neg (ConeSupport.E n)),
      by simp [Function.comp_apply, hne], ?_⟩


    have key : TemperedDistribution.smulLeftCLM ℂ (φ ∘ Neg.neg) (ConeSupport.reflection v) =
        (TemperedDistribution.smulLeftCLM ℂ ((φ ∘ Neg.neg) ∘ Neg.neg) v).comp
          ConeSupport.schwartzReflectionCLM := by
      ext ψ
      show v (ConeSupport.schwartzReflectionCLM ((SchwartzMap.smulLeftCLM ℂ (φ ∘ Neg.neg)) ψ)) =
           v ((SchwartzMap.smulLeftCLM ℂ ((φ ∘ Neg.neg) ∘ Neg.neg)) (ConeSupport.schwartzReflectionCLM ψ))
      congr 1
      ext y
      simp only [ConeSupport.schwartzReflectionCLM, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
        Function.comp, ContinuousLinearEquiv.coe_neg, SchwartzMap.smulLeftCLM]
      split_ifs with h1 h2 h2
      · simp only [SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.flip_apply,
          ContinuousLinearMap.lsmul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
          Function.comp, ContinuousLinearEquiv.coe_neg]
        simp [Pi.neg_apply, id]
      · exact absurd (ConeSupport.hasTemperateGrowth_comp_neg h1) h2
      · exact absurd (ConeSupport.hasTemperateGrowth_neg_iff.mpr h2) h1
      · simp
    have hgg : (φ ∘ Neg.neg) ∘ Neg.neg = φ := by ext; simp
    rw [key, hgg, hf]
    exact ⟨ConeSupport.schwartzReflectionCLM f, ConeSupport.reflection_schwartz_coercion f⟩
  ·
    intro hx hcontra
    apply hx
    obtain ⟨φ, hsmooth, hcompact, hne, f, hf⟩ := hcontra
    refine ⟨φ ∘ Neg.neg,
      hsmooth.comp (ContinuousLinearEquiv.neg ℝ).contDiff,
      hcompact.comp_homeomorph (Homeomorph.neg (ConeSupport.E n)),
      by simp [Function.comp_apply, hne], ?_⟩


    have key : TemperedDistribution.smulLeftCLM ℂ φ (ConeSupport.reflection v) =
        (TemperedDistribution.smulLeftCLM ℂ (φ ∘ Neg.neg) v).comp
          ConeSupport.schwartzReflectionCLM := by
      ext ψ
      show v (ConeSupport.schwartzReflectionCLM ((SchwartzMap.smulLeftCLM ℂ φ) ψ)) =
           v ((SchwartzMap.smulLeftCLM ℂ (φ ∘ Neg.neg)) (ConeSupport.schwartzReflectionCLM ψ))
      congr 1
      ext y
      simp only [ConeSupport.schwartzReflectionCLM, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
        Function.comp, ContinuousLinearEquiv.coe_neg, SchwartzMap.smulLeftCLM]
      split_ifs with h1 h2 h2
      · simp only [SchwartzMap.bilinLeftCLM_apply, ContinuousLinearMap.flip_apply,
          ContinuousLinearMap.lsmul_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
          Function.comp, ContinuousLinearEquiv.coe_neg]
        simp [Pi.neg_apply, id]
      · exact absurd (ConeSupport.hasTemperateGrowth_comp_neg h1) h2
      · exact absurd (ConeSupport.hasTemperateGrowth_neg_iff.mpr h2) h1
      · simp

    have h1 : ConeSupport.reflection (TemperedDistribution.smulLeftCLM ℂ (φ ∘ Neg.neg) v) = ↑f := by
      show (TemperedDistribution.smulLeftCLM ℂ (φ ∘ Neg.neg) v).comp
        ConeSupport.schwartzReflectionCLM = (f : 𝓢'(ConeSupport.E n, ℂ))
      rwa [← key]
    have h2 : TemperedDistribution.smulLeftCLM ℂ (φ ∘ Neg.neg) v =
        ConeSupport.reflection (↑f) := by
      have h3 := congr_arg ConeSupport.reflection h1
      rwa [ConeSupport.reflection_reflection] at h3
    rw [h2]
    exact ⟨ConeSupport.schwartzReflectionCLM f, ConeSupport.reflection_schwartz_coercion f⟩


/-- Negation commutes with the boundary embedding `ClosedBall → Sphere`. That is,
`(-p).toSphere = sphereNeg (p.toSphere)` when `‖p.val‖ = 1`. -/
lemma toSphere_neg (p : ClosedBall n) (hp : ‖p.val‖ = 1) :
    (-p).toSphere (by rw [ClosedBall.norm_neg_eq]; exact hp) =
    ConeSupport.sphereNeg (p.toSphere hp) := by
  apply Subtype.ext
  simp [ClosedBall.toSphere, ConeSupport.sphereNeg, ClosedBall.neg_val]


/-- Negation commutes with the interior embedding `ClosedBall → EuclideanSpace`.
Concretely, `(-p).toEuclidean = -(p.toEuclidean)` on the interior `‖p.val‖ < 1`. -/
lemma toEuclidean_neg (p : ClosedBall n) (hp : ‖p.val‖ < 1) :
    (-p).toEuclidean (by rw [ClosedBall.norm_neg_eq]; exact hp) =
    -(p.toEuclidean hp) := by
  simp [ClosedBall.toEuclidean, ClosedBall.neg_val, smul_neg]


/-- Equivariance of `Css` under the double Fourier transform: `p ∈ Css u` iff
`-p ∈ Css (𝓕 (𝓕 u))`. Follows from `doubleFourier_eq_reflection`. -/
theorem mem_css_iff_neg_mem_css_fourier_fourier
    {n : ℕ} (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (p : ClosedBall n) :
    p ∈ Css u ↔ (-p) ∈ Css (𝓕 (𝓕 u)) := by

  rw [doubleFourier_eq_reflection]

  simp only [Css, mem_setOf_eq]

  have hneg : ‖(-p).val‖ = ‖p.val‖ := by rw [ClosedBall.neg_val, norm_neg]
  constructor
  ·
    intro hp_css
    by_cases h_pos : ‖p.val‖ = 1
    ·
      have h_neg : ‖(-p).val‖ = 1 := by rwa [hneg]
      simp only [dif_pos h_pos] at hp_css
      simp only [dif_pos h_neg]
      rw [toSphere_neg p h_pos, ConeSupport.css_reflection]
      rw [ConeSupport.mem_negSet_iff]
      rwa [ConeSupport.sphereNeg_sphereNeg]
    ·
      have h_neg : ‖(-p).val‖ ≠ 1 := by rwa [hneg]
      have hp_lt : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h_pos
      simp only [dif_neg h_pos] at hp_css
      simp only [dif_neg h_neg]
      rw [toEuclidean_neg]
      rw [singularSupport_reflection]
      rwa [neg_neg]
  ·
    intro hnp_css
    by_cases h_pos : ‖p.val‖ = 1
    ·
      have h_neg : ‖(-p).val‖ = 1 := by rwa [hneg]
      simp only [dif_pos h_neg] at hnp_css
      simp only [dif_pos h_pos]
      rw [toSphere_neg p h_pos, ConeSupport.css_reflection, ConeSupport.mem_negSet_iff] at hnp_css
      rwa [ConeSupport.sphereNeg_sphereNeg] at hnp_css
    ·
      have h_neg : ‖(-p).val‖ ≠ 1 := by rwa [hneg]
      have hp_lt : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h_pos
      simp only [dif_neg h_neg] at hnp_css
      simp only [dif_neg h_pos]
      rw [toEuclidean_neg, singularSupport_reflection, neg_neg] at hnp_css
      exact hnp_css


/-- Negated form of `mem_css_iff_neg_mem_css_fourier_fourier`: `p ∉ Css u` iff
`-p ∉ Css (𝓕 (𝓕 u))`. -/
theorem not_mem_css_iff_neg_not_mem_css_fourier_fourier
    (u₁ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (p : ClosedBall n) :
    p ∉ Css u₁ ↔ (-p) ∉ Css (𝓕 (𝓕 u₁)) :=
  (mem_css_iff_neg_mem_css_fourier_fourier u₁ p).not


/-- Public restatement of `isSmoothNear_schwartzConvolution_local'`: the Schwartz
convolution `u * φ` is smooth near every point. -/
theorem isSmoothNear_schwartzConvolution_local
    (u : TemperedDistribution (ConeSupport.E n) ℂ)
    (φ : SchwartzMap (ConeSupport.E n) ℂ)
    (x₀ : ConeSupport.E n) :
    ConeSupport.IsSmoothNear (ConeSupport.schwartzConvolution u φ) x₀ :=
  isSmoothNear_schwartzConvolution_local' u φ x₀


/-- Double-Fourier equivariance for the scattering wavefront set:
`(a, b) ∈ WFsc (𝓕 (𝓕 u))` iff `(-a, -b) ∈ WFsc u`. This expresses how reflection
acts on `WFsc` through Fourier inversion squared. -/
theorem mem_wfsc_fourier_fourier_iff_neg_mem_wfsc
    {n : ℕ}
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (a b : ClosedBall n) :
    (a, b) ∈ WFsc (𝓕 (𝓕 u)) ↔ (-a, -b) ∈ WFsc u := by
  by_cases hab : (a, b) ∈ BoundaryProd n
  · have hnab : (-a, -b) ∈ BoundaryProd n := by
      simp only [BoundaryProd, Set.mem_setOf_eq, ClosedBall.norm_neg_eq] at hab ⊢
      exact hab
    rw [show ((a, b) ∈ WFsc (𝓕 (𝓕 u)) ↔ (-a, -b) ∈ WFsc u) ↔
      ((a, b) ∉ WFsc (𝓕 (𝓕 u)) ↔ (-a, -b) ∉ WFsc u) from not_iff_not.symm]
    rw [not_mem_wfsc_iff_exists_decomp hab,
        not_mem_wfsc_iff_exists_decomp hnab]
    constructor
    · rintro ⟨v₁, v₂, hdecomp, ha_v₁, hb_fv₂⟩
      refine ⟨𝓕⁻ (𝓕⁻ v₁), 𝓕⁻ (𝓕⁻ v₂), ?_, ?_, ?_⟩
      · have : 𝓕 (𝓕 u) = v₁ + v₂ := hdecomp
        have h1 : u = 𝓕⁻ (𝓕⁻ (𝓕 (𝓕 u))) := by simp
        rw [h1, this]
        simp
      · rw [show v₁ = 𝓕 (𝓕 (𝓕⁻ (𝓕⁻ v₁))) from by simp] at ha_v₁
        exact (not_mem_css_iff_neg_not_mem_css_fourier_fourier (𝓕⁻ (𝓕⁻ v₁)) (-a)).mpr
          (by simp only [ClosedBall.neg_neg]; exact ha_v₁)
      · rw [show 𝓕 (𝓕⁻ (𝓕⁻ v₂)) = 𝓕⁻ v₂ from by simp]
        exact (not_mem_css_iff_neg_not_mem_css_fourier_fourier (𝓕⁻ v₂) (-b)).mpr
          (by simp only [ClosedBall.neg_neg, show 𝓕 (𝓕 (𝓕⁻ v₂)) = 𝓕 v₂ from by simp]
              exact hb_fv₂)
    · rintro ⟨w₁, w₂, hdecomp, hna_w₁, hnb_fw₂⟩
      refine ⟨𝓕 (𝓕 w₁), 𝓕 (𝓕 w₂), ?_, ?_, ?_⟩
      · rw [hdecomp]
        simp [FourierTransform.fourier_add]
      · have := (not_mem_css_iff_neg_not_mem_css_fourier_fourier w₁ (-a)).mp hna_w₁
        simp only [ClosedBall.neg_neg] at this
        exact this
      · have := (not_mem_css_iff_neg_not_mem_css_fourier_fourier (𝓕 w₂) (-b)).mp hnb_fw₂
        simp only [ClosedBall.neg_neg] at this
        exact this
  ·

    have hnab : (-a, -b) ∉ BoundaryProd n := by
      simp only [BoundaryProd, Set.mem_setOf_eq, ClosedBall.norm_neg_eq] at hab ⊢
      exact hab
    simp only [BoundaryProd, Set.mem_setOf_eq, not_or] at hab hnab
    have ha_ne : ‖a.val‖ ≠ 1 := hab.1
    have hb_ne : ‖b.val‖ ≠ 1 := hab.2


    have not_in_css_fourier_interior :
        ∀ (v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
          (φ : ConeSupport.E n → ℂ)
          (hφ : ContDiff ℝ ↑(⊤ : ℕ∞) φ)
          (hφc : HasCompactSupport φ)
          (q : ClosedBall n) (hq : ‖q.val‖ ≠ 1),
        q ∉ Css (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ v)) := by
      intro v φ hφ hφc q hq_ne
      have hq_lt : ‖q.val‖ < 1 := lt_of_le_of_ne q.property hq_ne
      simp only [Css, Set.mem_setOf_eq, dif_neg hq_ne]
      simp only [ConeSupport.singularSupport, Set.mem_setOf_eq, not_not]

      obtain ⟨f, hf⟩ := ConeSupport.fourier_smulLeftCLM_eq_schwartzConvolution φ hφ hφc v
      rw [hf]
      exact isSmoothNear_schwartzConvolution_local (𝓕 v) f _

    have not_in_wfsc : ∀ (v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
        (p q : ClosedBall n) (hp : ‖p.val‖ ≠ 1) (hq : ‖q.val‖ ≠ 1),
        (p, q) ∉ WFsc v := by
      intro v p q hp_ne hq_ne hmem
      simp only [WFsc, Set.mem_setOf_eq] at hmem
      apply hmem
      rw [dif_neg hp_ne]
      set x₀ := p.toEuclidean (lt_of_le_of_ne p.property hp_ne)
      set χ : ContDiffBump x₀ := ⟨1, 2, one_pos, by norm_num⟩
      set φ := fun x => Complex.ofReal (χ x)
      have hφ_smooth : ContDiff ℝ ↑(⊤ : ℕ∞) φ := by
        rw [contDiff_infty]; intro k
        exact_mod_cast Complex.ofRealCLM.contDiff.comp χ.contDiff
      have hφ_compact : HasCompactSupport φ :=
        χ.hasCompactSupport.comp_left Complex.ofReal_zero
      refine ⟨φ, hφ_smooth, hφ_compact, ?_, not_in_css_fourier_interior _ φ hφ_smooth hφ_compact q hq_ne⟩
      have h1 : χ x₀ = 1 :=
        χ.one_of_mem_closedBall (Metric.mem_closedBall_self (le_of_lt χ.rIn_pos))
      show φ x₀ ≠ 0
      simp only [φ, h1, Complex.ofReal_one]
      exact one_ne_zero
    constructor
    · intro h; exact absurd h (not_in_wfsc (𝓕 (𝓕 u)) a b ha_ne hb_ne)
    · intro h; exact absurd h (not_in_wfsc u (-a) (-b)
        (by rw [ClosedBall.norm_neg_eq]; exact ha_ne)
        (by rw [ClosedBall.norm_neg_eq]; exact hb_ne))

/-- Stability of `BoundaryProd` under the swap-negate involution `(p, q) ↦ (q, -p)`. -/
theorem boundaryProd_swap_neg {p q : ClosedBall n}
    (hpq : (p, q) ∈ BoundaryProd n) : (q, -p) ∈ BoundaryProd n := by
  simp only [BoundaryProd, Set.mem_setOf_eq, ClosedBall.norm_neg_eq] at hpq ⊢
  exact hpq.symm

/-- Transport of `WFsc` under the Fourier transform: if `(p, q) ∉ WFsc u`, then
`(q, -p) ∉ WFsc (𝓕 u)`. -/
theorem not_mem_wfsc_of_not_mem_wfsc_fourier
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    {p q : ClosedBall n} (hpq : (p, q) ∈ BoundaryProd n)
    (h : (p, q) ∉ WFsc u) :
    (q, -p) ∉ WFsc (𝓕 u) := by
  rw [not_mem_wfsc_iff_exists_decomp hpq] at h
  obtain ⟨u₁, u₂, hudecomp, hp_u1, hq_fu2⟩ := h
  rw [not_mem_wfsc_iff_exists_decomp (boundaryProd_swap_neg hpq)]
  refine ⟨𝓕 u₂, 𝓕 u₁, ?_, hq_fu2,
    (not_mem_css_iff_neg_not_mem_css_fourier_fourier u₁ p).mp hp_u1⟩
  rw [hudecomp, FourierTransform.fourier_add]
  exact add_comm _ _

/-- Symmetry of `WFsc` under the Fourier transform: on the boundary product,
`(p, q) ∈ WFsc u ↔ (q, -p) ∈ WFsc (𝓕 u)`. This is the iff version of
`not_mem_wfsc_of_not_mem_wfsc_fourier`. -/
theorem mem_wfsc_iff_swap_neg_mem_wfsc_fourier
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    {p q : ClosedBall n} (hpq : (p, q) ∈ BoundaryProd n) :
    (p, q) ∈ WFsc u ↔ (q, -p) ∈ WFsc (𝓕 u) := by
  constructor
  · intro hmem
    by_contra habs
    have hbnd : (q, -p) ∈ BoundaryProd n := boundaryProd_swap_neg hpq
    have h1 : (-p, -q) ∉ WFsc (𝓕 (𝓕 u)) :=
      not_mem_wfsc_of_not_mem_wfsc_fourier (𝓕 u) hbnd habs
    have h2 : (-p, -q) ∈ WFsc (𝓕 (𝓕 u)) := by
      rw [mem_wfsc_fourier_fourier_iff_neg_mem_wfsc u (-p) (-q)]
      simp only [ClosedBall.neg_neg]
      exact hmem
    exact h1 h2
  · intro hmem
    by_contra habs
    exact absurd hmem (not_mem_wfsc_of_not_mem_wfsc_fourier u hpq habs)

/-- Monotonicity of `Css ∘ 𝓕` under shrinking the compactly supported cutoff:
if `tsupport φ' ⊆ supp φ`, then `Css (𝓕 (φ'·u)) ⊆ Css (𝓕 (φ·u))`. -/
theorem Css_mono_compact_cutoff
    {n : ℕ} (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (φ φ' : ConeSupport.E n → ℂ)
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ') (hφ'c : HasCompactSupport φ')
    (hsup : tsupport φ' ⊆ Function.support φ) :
    Css (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ' u)) ⊆
    Css (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ u)) := by
  intro q hq
  simp only [Css, Set.mem_setOf_eq] at hq ⊢
  by_cases hq1 : ‖q.val‖ = 1
  ·
    rw [dif_pos hq1] at hq ⊢
    exact ConeSupport.cssSphere_mono_compact_cutoff u φ φ' hφ hφc hφ' hφ'c hsup hq
  ·
    rw [dif_neg hq1] at hq
    have hq_lt : ‖q.val‖ < 1 := lt_of_le_of_ne q.property hq1
    rw [dif_neg hq1]

    obtain ⟨f, hf⟩ := ConeSupport.fourier_compact_cutoff_eq_schwartz_convolution
      u φ φ' hφ hφc hφ' hφ'c hsup

    exfalso
    simp only [ConeSupport.singularSupport, Set.mem_setOf_eq] at hq
    rw [hf] at hq
    exact hq (isSmoothNear_schwartzConvolution_local'
      (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ u)) f (q.toEuclidean hq_lt))

/-- Monotonicity of `Css ∘ 𝓕` under shrinking the conic cutoff. If `supp g' ⊆ supp g`,
both conic cutoffs near `ω`, then `Css (𝓕 (g'·u)) ⊆ Css (𝓕 (g·u))`. -/
theorem Css_mono_conic_cutoff
    {n : ℕ} (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (g g' : ConeSupport.E n → ℂ) (ω : ConeSupport.Sphere n)
    (hg : ConeSupport.IsConicCutoffNear g ω)
    (hg' : ConeSupport.IsConicCutoffNear g' ω)
    (hsup : Function.support g' ⊆ Function.support g) :
    Css (𝓕 (TemperedDistribution.smulLeftCLM ℂ g' u)) ⊆
    Css (𝓕 (TemperedDistribution.smulLeftCLM ℂ g u)) := by
  intro q hq
  simp only [Css, Set.mem_setOf_eq] at hq ⊢
  by_cases hq1 : ‖q.val‖ = 1
  ·
    rw [dif_pos hq1] at hq ⊢
    exact ConeSupport.cssSphere_mono_conic_cutoff u g g' ω hg hg' hsup hq
  ·
    rw [dif_neg hq1] at hq
    have hq_lt : ‖q.val‖ < 1 := lt_of_le_of_ne q.property hq1
    rw [dif_neg hq1]
    obtain ⟨f, hf⟩ := ConeSupport.fourier_conic_cutoff_eq_schwartz_convolution
      u g g' ω hg hg' hsup
    exfalso
    simp only [ConeSupport.singularSupport, Set.mem_setOf_eq] at hq
    rw [hf] at hq
    exact hq (isSmoothNear_schwartzConvolution_local'
      (𝓕 (TemperedDistribution.smulLeftCLM ℂ g u)) f (q.toEuclidean hq_lt))

/-- Neighbourhood-of-`q` form of `(p, q) ∉ WFsc u`. If `(p, q) ∉ WFsc u`, then there
is an open neighbourhood `V` of `q` together with a cutoff (conic on the boundary,
compactly supported in the interior) whose `Css (𝓕 (cutoff·u))` is disjoint from `V`,
and the same disjointness persists for any further shrinking of the cutoff. -/
theorem not_mem_wfsc_nhds_css (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    {p q : ClosedBall n} (_hpq : (p, q) ∈ BoundaryProd n)
    (hnotin : (p, q) ∉ WFsc u) :
    ∃ (V : Set (ClosedBall n)),
      IsOpen V ∧ q ∈ V ∧
      (if h : ‖p.val‖ = 1 then
        ∃ (g₀ : ConeSupport.E n → ℂ),
          ConeSupport.IsConicCutoffNear g₀ (p.toSphere h) ∧
          V ∩ Css (𝓕 (TemperedDistribution.smulLeftCLM ℂ g₀ u)) = ∅ ∧
          ∀ (g' : ConeSupport.E n → ℂ),
            ConeSupport.IsConicCutoffNear g' (p.toSphere h) →
            Function.support g' ⊆ Function.support g₀ →
            V ∩ Css (𝓕 (TemperedDistribution.smulLeftCLM ℂ g' u)) = ∅
      else
        have hp_lt : ‖p.val‖ < 1 := lt_of_le_of_ne p.property h
        ∃ (φ₀ : ConeSupport.E n → ℂ),
          ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ₀ ∧
          HasCompactSupport φ₀ ∧
          φ₀ (p.toEuclidean hp_lt) ≠ 0 ∧
          V ∩ Css (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ₀ u)) = ∅ ∧
          ∀ (φ' : ConeSupport.E n → ℂ),
            ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ' →
            HasCompactSupport φ' →
            tsupport φ' ⊆ Function.support φ₀ →
            V ∩ Css (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ' u)) = ∅) := by

  simp only [WFsc, Set.mem_setOf_eq, not_not] at hnotin
  by_cases hp1 : ‖p.val‖ = 1
  ·
    rw [dif_pos hp1] at hnotin
    obtain ⟨g₀, hg₀_conic, hq_notin_css⟩ := hnotin

    refine ⟨(Css (𝓕 (TemperedDistribution.smulLeftCLM ℂ g₀ u)))ᶜ,
            (isClosed_css _).isOpen_compl, Set.mem_compl hq_notin_css, ?_⟩
    rw [dif_pos hp1]
    refine ⟨g₀, hg₀_conic, Set.compl_inter_self _, ?_⟩

    intro g' hg'_conic hg'_supp

    have hmono : Css (𝓕 (TemperedDistribution.smulLeftCLM ℂ g' u)) ⊆
        Css (𝓕 (TemperedDistribution.smulLeftCLM ℂ g₀ u)) :=
      Css_mono_conic_cutoff u g₀ g' (p.toSphere hp1) hg₀_conic hg'_conic hg'_supp

    exact Set.eq_empty_of_subset_empty
      (Set.inter_subset_inter_right _ hmono |>.trans (Set.compl_inter_self _).subset)
  ·
    rw [dif_neg hp1] at hnotin
    have hp_lt : ‖p.val‖ < 1 := lt_of_le_of_ne p.property hp1
    obtain ⟨φ₀, hφ₀_smooth, hφ₀_compact, hφ₀_ne, hq_notin_css⟩ := hnotin

    refine ⟨(Css (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ₀ u)))ᶜ,
            (isClosed_css _).isOpen_compl, Set.mem_compl hq_notin_css, ?_⟩
    rw [dif_neg hp1]
    refine ⟨φ₀, hφ₀_smooth, hφ₀_compact, hφ₀_ne, Set.compl_inter_self _, ?_⟩

    intro φ' hφ'_smooth hφ'_compact hφ'_supp

    have hmono : Css (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ' u)) ⊆
        Css (𝓕 (TemperedDistribution.smulLeftCLM ℂ φ₀ u)) :=
      Css_mono_compact_cutoff u φ₀ φ' hφ₀_smooth hφ₀_compact hφ'_smooth hφ'_compact hφ'_supp

    exact Set.eq_empty_of_subset_empty
      (Set.inter_subset_inter_right _ hmono |>.trans (Set.compl_inter_self _).subset)

end WavefrontSet

end

set_option maxHeartbeats 1600000

open scoped Topology
open Set

namespace WavefrontSet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A function `f : E → F` is positively homogeneous of degree `d : ℤ` if
`f (a • x) = a^d • f x` for every `a > 0` and every nonzero `x`. -/
def IsPositivelyHomogeneous (d : ℤ) (f : E → F) : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ (x : E), x ≠ 0 → f (a • x) = (a : ℝ) ^ d • f x

/-- The scaling continuous linear equivalence `E ≃L[ℝ] E` corresponding to a nonzero
scalar `a`; the action is `x ↦ a • x`. -/
noncomputable def scaleCLE (a : ℝ) (ha : a ≠ 0) : E ≃L[ℝ] E :=
  Units.mk0 a ha • ContinuousLinearEquiv.refl ℝ E

/-- Evaluation lemma for `scaleCLE`: the underlying function is just scalar multiplication. -/
@[simp]
lemma scaleCLE_apply (a : ℝ) (ha : a ≠ 0) (x : E) : scaleCLE a ha x = a • x := by
  simp [scaleCLE]

omit [NormedSpace ℝ E] in
/-- The unit sphere is contained in the complement of the origin. -/
lemma sphere_subset_compl_zero :
    Metric.sphere (0 : E) 1 ⊆ ({(0 : E)}ᶜ : Set E) := by
  intro x hx h
  simp only [Metric.mem_sphere, dist_zero_right] at hx
  rw [h, norm_zero] at hx; exact zero_ne_one hx

/-- For a degree-`0` positively homogeneous function `ψ`, the `k`-th iterated derivative
satisfies the scaling bound `‖D^k ψ (x)‖ ≤ ‖D^k ψ (a • x)‖ * a^k` for any `a > 0`,
reflecting the fact that `D^k ψ` is positively homogeneous of degree `-k`. -/
lemma norm_iteratedFDeriv_le_scale
    {ψ : E → F}
    (hψ_hom : IsPositivelyHomogeneous 0 ψ)
    {a : ℝ} (ha : 0 < a) {x : E} (hx : x ≠ 0) (k : ℕ) :
    ‖iteratedFDeriv ℝ k ψ x‖ ≤ ‖iteratedFDeriv ℝ k ψ (a • x)‖ * a ^ k := by
  have ha' : a ≠ 0 := ne_of_gt ha
  have hax : a • x ≠ 0 := smul_ne_zero ha' hx
  have hopen : IsOpen ({(0 : E)}ᶜ : Set E) := isOpen_compl_singleton
  have : Nontrivial E := ⟨⟨x, 0, hx⟩⟩
  set s : Set E := {(0 : E)}ᶜ
  set g : E ≃L[ℝ] E := scaleCLE a ha'

  rw [← iteratedFDerivWithin_of_isOpen k hopen (show x ∈ s from hx),
      ← iteratedFDerivWithin_of_isOpen k hopen (show a • x ∈ s from hax)]

  have h_pre : (g : E → E) ⁻¹' s = s := by ext y; simp [g, s, ha']

  have h_eq : EqOn (ψ ∘ (g : E → E)) ψ s := fun y hy => by
    show ψ (g y) = ψ y; simp only [g, scaleCLE_apply]
    rw [hψ_hom a ha y hy]; simp

  have h_cle := g.iteratedFDerivWithin_comp_right ψ hopen.uniqueDiffOn
    (show g x ∈ s from show a • x ∈ s from hax) k
  rw [h_pre] at h_cle

  rw [← iteratedFDerivWithin_congr h_eq (show x ∈ s from hx) k, h_cle]

  set M := iteratedFDerivWithin ℝ k ψ s (g x)
  have h1 : ‖M.compContinuousLinearMap (fun _ => (g : E →L[ℝ] E))‖ ≤
      ‖M‖ * ∏ _ : Fin k, ‖(g : E →L[ℝ] E)‖ :=
    ContinuousMultilinearMap.norm_compContinuousLinearMap_le M _
  have h3 : ‖(g : E →L[ℝ] E)‖ = a := by
    have : ((g : E ≃L[ℝ] E) : E →L[ℝ] E) = a • ContinuousLinearMap.id ℝ E := by ext; simp [g]
    rw [this, norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_of_nonneg ha.le]
  rw [Finset.prod_const, Finset.card_fin, h3,
      show ‖M‖ = ‖iteratedFDerivWithin ℝ k ψ s (a • x)‖ from by simp [g, M]] at h1
  exact h1

/-- On the unit sphere of a nontrivial finite-dimensional space, the norm of every
iterated derivative of a smooth function on `E ∖ {0}` is uniformly bounded. -/
lemma exists_bound_iteratedFDeriv_sphere [FiniteDimensional ℝ E] [Nontrivial E]
    {ψ : E → F}
    (hψ_smooth : ContDiffOn ℝ ⊤ ψ ({(0 : E)}ᶜ))
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Metric.sphere (0 : E) 1,
      ‖iteratedFDeriv ℝ k ψ x‖ ≤ C := by
  have hopen : IsOpen ({(0 : E)}ᶜ : Set E) := isOpen_compl_singleton

  have h_cont : ContinuousOn (fun x => iteratedFDeriv ℝ k ψ x) ({(0 : E)}ᶜ) :=
    (hψ_smooth.continuousOn_iteratedFDerivWithin (m := k) le_top hopen.uniqueDiffOn).congr
      (fun x hx => (iteratedFDerivWithin_of_isOpen k hopen hx).symm)

  have h_norm_cont : ContinuousOn (fun x => ‖iteratedFDeriv ℝ k ψ x‖)
      (Metric.sphere (0 : E) 1) :=
    continuous_norm.comp_continuousOn (h_cont.mono sphere_subset_compl_zero)

  have h_nonempty : (Metric.sphere (0 : E) 1).Nonempty := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    exact ⟨‖x‖⁻¹ • x, by
      simp [norm_smul, norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

  obtain ⟨x₀, hx₀_mem, hx₀_max⟩ :=
    (isCompact_sphere (0 : E) 1).exists_isMaxOn h_nonempty h_norm_cont
  exact ⟨‖iteratedFDeriv ℝ k ψ x₀‖, norm_nonneg _, fun x hx => hx₀_max hx⟩

/-- For a smooth degree-`0` positively homogeneous function `ψ` on `E ∖ {0}`, the
`k`-th iterated derivative obeys the bound `‖D^k ψ (x)‖ ≤ C ‖x‖^{-k}` with a uniform
constant `C` (obtained from the spherical maximum of `‖D^k ψ‖`). -/
theorem norm_iteratedFDeriv_le_of_homogeneous_zero
    [FiniteDimensional ℝ E]
    {ψ : E → F}
    (hψ_smooth : ContDiffOn ℝ ⊤ ψ ({(0 : E)}ᶜ))
    (hψ_hom : IsPositivelyHomogeneous 0 ψ)
    (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, x ≠ 0 → ‖iteratedFDeriv ℝ k ψ x‖ ≤ C * ‖x‖⁻¹ ^ k := by

  by_cases hE : Subsingleton E
  · exact ⟨0, le_refl 0, fun x hx => absurd (Subsingleton.eq_zero x) hx⟩

  have hNT : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE

  obtain ⟨C, hC_nonneg, hC_bound⟩ := exists_bound_iteratedFDeriv_sphere hψ_smooth k
  refine ⟨C, hC_nonneg, fun x hx => ?_⟩
  have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hx_inv_pos : 0 < ‖x‖⁻¹ := inv_pos.mpr hx_norm_pos

  have h_scale := norm_iteratedFDeriv_le_scale hψ_hom hx_inv_pos hx k

  have h_on_sphere : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : E) 1 := by
    simp [norm_smul, inv_mul_cancel₀ (ne_of_gt hx_norm_pos)]

  calc ‖iteratedFDeriv ℝ k ψ x‖
      ≤ ‖iteratedFDeriv ℝ k ψ (‖x‖⁻¹ • x)‖ * ‖x‖⁻¹ ^ k := h_scale
    _ ≤ C * ‖x‖⁻¹ ^ k :=
        mul_le_mul_of_nonneg_right (hC_bound _ h_on_sphere)
          (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) k)

section Lemma12_5

open scoped SchwartzMap
open ConeSupport in

/-- Data structure packaging the inputs needed to define the `Css`-pairing
`⟨u₁, u₂⟩` used in Lemma 12.5: a notion of cone support `Css`, two cutoff
functions `ψ, ψ'` together with hypotheses that the relevant products have
empty `Css`, a recipe `toSchwartz` for upgrading such tempered distributions
to Schwartz functions, plus linearity and symmetry compatibilities. -/
structure CssPairingData {n : ℕ} (K₁ K₂ : Set (ConeSupport.E n)) where
  Css : 𝓢'(ConeSupport.E n, ℂ) → Set (ConeSupport.E n)
  ψ  : ConeSupport.E n → ℂ
  ψ' : ConeSupport.E n → ℂ
  toSchwartz : (u : 𝓢'(ConeSupport.E n, ℂ)) → Css u = ∅ →
    SchwartzMap (ConeSupport.E n) ℂ
  css_ψ_mul_empty : ∀ u : 𝓢'(ConeSupport.E n, ℂ), Css u ⊆ K₂ →
    Css (TemperedDistribution.smulLeftCLM ℂ ψ u) = ∅
  css_ψ_compl_mul_empty : ∀ u : 𝓢'(ConeSupport.E n, ℂ), Css u ⊆ K₁ →
    Css (TemperedDistribution.smulLeftCLM ℂ (1 - ψ) u) = ∅
  css_ψ'_mul_empty : ∀ u : 𝓢'(ConeSupport.E n, ℂ), Css u ⊆ K₂ →
    Css (TemperedDistribution.smulLeftCLM ℂ ψ' u) = ∅
  css_ψ'_compl_mul_empty : ∀ u : 𝓢'(ConeSupport.E n, ℂ), Css u ⊆ K₁ →
    Css (TemperedDistribution.smulLeftCLM ℂ (1 - ψ') u) = ∅
  css_diff_empty₂ : ∀ u : 𝓢'(ConeSupport.E n, ℂ), Css u ⊆ K₂ →
    Css (TemperedDistribution.smulLeftCLM ℂ (ψ - ψ') u) = ∅
  css_diff_empty₁ : ∀ u : 𝓢'(ConeSupport.E n, ℂ), Css u ⊆ K₁ →
    Css (TemperedDistribution.smulLeftCLM ℂ (ψ - ψ') u) = ∅
  linearity_mul : ∀ (u₂ : 𝓢'(ConeSupport.E n, ℂ)) (h₂ : Css u₂ ⊆ K₂)
    (u₁ : 𝓢'(ConeSupport.E n, ℂ)),
    u₁ (toSchwartz _ (css_ψ_mul_empty u₂ h₂)) -
      u₁ (toSchwartz _ (css_ψ'_mul_empty u₂ h₂)) =
    u₁ (toSchwartz _ (css_diff_empty₂ u₂ h₂))
  linearity_compl : ∀ (u₁ : 𝓢'(ConeSupport.E n, ℂ)) (h₁ : Css u₁ ⊆ K₁)
    (u₂ : 𝓢'(ConeSupport.E n, ℂ)),
    u₂ (toSchwartz _ (css_ψ'_compl_mul_empty u₁ h₁)) -
      u₂ (toSchwartz _ (css_ψ_compl_mul_empty u₁ h₁)) =
    u₂ (toSchwartz _ (css_diff_empty₁ u₁ h₁))
  symmetry_eval : ∀ (u₁ : 𝓢'(ConeSupport.E n, ℂ)) (h₁ : Css u₁ ⊆ K₁)
    (u₂ : 𝓢'(ConeSupport.E n, ℂ)) (h₂ : Css u₂ ⊆ K₂),
    u₁ (toSchwartz _ (css_diff_empty₂ u₂ h₂)) =
    u₂ (toSchwartz _ (css_diff_empty₁ u₁ h₁))

variable {n : ℕ} {K₁ K₂ : Set (ConeSupport.E n)} (D : CssPairingData K₁ K₂)

open scoped SchwartzMap

/-- The `ψ`-pairing of `u₁` and `u₂` defined from `CssPairingData`:
`u₁(ψ·u₂) + u₂((1-ψ)·u₁)`, evaluated using the Schwartz representatives
produced by `toSchwartz`. -/
noncomputable def CssPairingData.pairingψ
    (u₁ : 𝓢'(ConeSupport.E n, ℂ)) (h₁ : D.Css u₁ ⊆ K₁)
    (u₂ : 𝓢'(ConeSupport.E n, ℂ)) (h₂ : D.Css u₂ ⊆ K₂) : ℂ :=
  u₁ (D.toSchwartz _ (D.css_ψ_mul_empty u₂ h₂)) +
  u₂ (D.toSchwartz _ (D.css_ψ_compl_mul_empty u₁ h₁))

/-- The `ψ'`-pairing of `u₁` and `u₂` from `CssPairingData`: the variant of
`pairingψ` using `ψ'` in place of `ψ`. The symmetry axioms in
`CssPairingData` ensure `pairingψ = pairingψ'`. -/
noncomputable def CssPairingData.pairingψ'
    (u₁ : 𝓢'(ConeSupport.E n, ℂ)) (h₁ : D.Css u₁ ⊆ K₁)
    (u₂ : 𝓢'(ConeSupport.E n, ℂ)) (h₂ : D.Css u₂ ⊆ K₂) : ℂ :=
  u₁ (D.toSchwartz _ (D.css_ψ'_mul_empty u₂ h₂)) +
  u₂ (D.toSchwartz _ (D.css_ψ'_compl_mul_empty u₁ h₁))

end Lemma12_5

end WavefrontSet

open scoped SchwartzMap FourierTransform

namespace WavefrontSet

variable {n : ℕ}

/-- `ProductWFscCondition u v` is the wavefront-set compatibility condition
ensuring that the pointwise product `u · v` of tempered distributions is
well-defined: for every base point `p` and every boundary frequency `ω`,
if `(p, ω) ∈ WFsc u` then `(p, -ω) ∉ WFsc v`. -/
def ProductWFscCondition (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∀ (p ω : ClosedBall n), ‖ω.val‖ = 1 →
    (p, ω) ∈ WFsc u → (p, -ω) ∉ WFsc v

/-- `ConvolutionWFscCondition u v` is the wavefront-set compatibility condition
ensuring that the convolution `u * v` of tempered distributions is well-defined:
for every boundary base direction `θ` and every frequency `q`, if `(θ, q) ∈ WFsc u`
then `(-θ, q) ∉ WFsc v`. Fourier-dual to `ProductWFscCondition`. -/
def ConvolutionWFscCondition (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) : Prop :=
  ∀ (θ q : ClosedBall n), ‖θ.val‖ = 1 →
    (θ, q) ∈ WFsc u → (-θ, q) ∉ WFsc v

/-- Data witnessing that `u, v` can be convolved: a finite decomposition
`u = Σ uPart i + remainder`, `v = Σ vPart j` whose pairwise conic singular supports
satisfy the disjointness condition required for `ConeSupport.convolution_of_disjointCss`,
together with a remainder term `remainderConv` that handles the diagonal/leftover
contribution. -/
structure ConvolutionDecompData {n : ℕ}
    (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) where
  ι : Type
  [finι : Fintype ι]
  [decι : DecidableEq ι]
  uPart : ι → TemperedDistribution (ConeSupport.E n) ℂ
  vPart : ι → TemperedDistribution (ConeSupport.E n) ℂ
  disjCss : ∀ i j : ι, ConeSupport.DisjointCssCondition (uPart i) (vPart j)
  remainderConv : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)

attribute [instance] ConvolutionDecompData.finι ConvolutionDecompData.decι

/-- The total convolution coming from a `ConvolutionDecompData`: sum of the
pairwise convolutions `convolution_of_disjointCss (uPart i) (vPart j)` plus the
remainder term. -/
noncomputable def ConvolutionDecompData.totalConv {n : ℕ}
    {u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    (data : ConvolutionDecompData u v) :
    𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (Finset.univ.sum fun i =>
    Finset.univ.sum fun j =>
      ConeSupport.convolution_of_disjointCss (data.uPart i) (data.vPart j)
        (data.disjCss i j)) +
    data.remainderConv


/-- Refinement of `ConvolutionDecompData` recording an angular (conic) partition.
For each index `i`, the decomposition pieces `uPart i` and `vPart i` have spherical
conic singular supports contained in a closed angular region `angSupp i`, and the
regions are pairwise disjoint after negation. This packaging is what allows us to
verify the disjointness condition needed to define `ConeSupport.convolution_of_disjointCss`. -/
structure ConicPartitionData {n : ℕ}
    (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) where
  ι : Type
  [finι : Fintype ι]
  [decι : DecidableEq ι]
  uPart : ι → TemperedDistribution (ConeSupport.E n) ℂ
  vPart : ι → TemperedDistribution (ConeSupport.E n) ℂ
  angSupp : ι → Set (ConeSupport.Sphere n)
  angSupp_closed : ∀ i, IsClosed (angSupp i)
  css_uPart_sub : ∀ i, ConeSupport.ConicSingularSupportSphere (uPart i) ⊆ angSupp i
  css_vPart_sub : ∀ i, ConeSupport.ConicSingularSupportSphere (vPart i) ⊆ angSupp i
  angSupp_neg_disjoint : ∀ i j,
    Disjoint (angSupp i) (ConeSupport.negSet (angSupp j))
  remainderConv : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)

attribute [instance] ConicPartitionData.finι ConicPartitionData.decι


/-- The angular disjointness from a `ConicPartitionData` is enough to verify the
`DisjointCssCondition` between any pair of pieces `uPart i` and `vPart j`. -/
lemma disjointCss_of_conicPartitionData
    {n : ℕ} {u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    (P : ConicPartitionData u v) (i j : P.ι) :
    ConeSupport.DisjointCssCondition (P.uPart i) (P.vPart j) := by
  rw [ConeSupport.disjointCssCondition_iff_disjoint]
  exact (P.angSupp_neg_disjoint i j).mono (P.css_uPart_sub i)
    (Set.image_mono (P.css_vPart_sub j))


/-- From a `ConvolutionWFscCondition` between `u` and `v`, one can construct an
explicit conic partition (a `ConicPartitionData u v`) whose pieces have angularly
disjoint conic singular supports. This is Lemma 12.something — the technical input
behind defining convolution under the WFsc compatibility hypothesis. -/
noncomputable def conicPartitionData_of_convWFsc
    {n : ℕ}
    (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (h : ConvolutionWFscCondition u v) :
    ConicPartitionData u v := by sorry

/-- Convert a `ConicPartitionData` (built from a `ConvolutionWFscCondition`) into
a `ConvolutionDecompData` by using `disjointCss_of_conicPartitionData` to supply
the `DisjointCssCondition` field. -/
noncomputable def exists_convolutionDecompData
    {n : ℕ}
    (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (h : ConvolutionWFscCondition u v) :
    ConvolutionDecompData u v :=
  let P := conicPartitionData_of_convWFsc u v h
  { ι := P.ι
    finι := P.finι
    decι := P.decι
    uPart := P.uPart
    vPart := P.vPart
    disjCss := disjointCss_of_conicPartitionData P
    remainderConv := P.remainderConv }

/-- The convolution `u * v` of two tempered distributions whenever they satisfy the
`ConvolutionWFscCondition`. Built by combining `exists_convolutionDecompData` with
`ConvolutionDecompData.totalConv`. -/
noncomputable def convolution_exists_of_wfsc_condition
    (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (h : ConvolutionWFscCondition u v) :
    𝓢'(EuclideanSpace ℝ (Fin n), ℂ) :=
  (exists_convolutionDecompData u v h).totalConv

/-- The Fourier transform exchanges the product and convolution WFsc compatibility
conditions: if `ProductWFscCondition u v` holds, then `ConvolutionWFscCondition (𝓕 u) (𝓕 v)`
holds. This is the wavefront-set translation of the Fourier convolution theorem. -/
theorem product_wfsc_cond_implies_conv_wfsc_cond_fourier
    (u v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (h : ProductWFscCondition u v) :
    ConvolutionWFscCondition (𝓕 u) (𝓕 v) := by
  intro θ q hθ_sphere hθq_mem


  have hbnd : (-q, θ) ∈ BoundaryProd n := by
    simp only [BoundaryProd, Set.mem_setOf_eq]
    exact Or.inr hθ_sphere
  have h1 : (-q, θ) ∈ WFsc u := by
    rwa [mem_wfsc_iff_swap_neg_mem_wfsc_fourier u hbnd, ClosedBall.neg_neg]

  have h2 : (-q, -θ) ∉ WFsc v := h (-q) θ hθ_sphere h1

  have hbnd2 : (-q, -θ) ∈ BoundaryProd n := by
    simp only [BoundaryProd, Set.mem_setOf_eq, ClosedBall.norm_neg_eq]
    exact Or.inr hθ_sphere
  intro hcontra
  apply h2
  rwa [mem_wfsc_iff_swap_neg_mem_wfsc_fourier v hbnd2, ClosedBall.neg_neg]

end WavefrontSet
