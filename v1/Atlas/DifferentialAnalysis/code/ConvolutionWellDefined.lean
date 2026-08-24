/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.WavefrontSet

noncomputable section

open scoped SchwartzMap
open MeasureTheory Set ConeSupport

namespace ConeSupport

variable {n : ℕ}

/-- Direct, axiom-free version of Lemma 12.6 of Melrose: given a tempered
distribution `u` with empty conic singular support on the sphere, and two
linear-and-additive convolution operations `convSchwartz` (on Schwartz
functions) and `convCompact` (on compactly-supported distributions) that
agree on Schwartz functions whose embedding is compactly-supported, the sum
`convSchwartz d.schwartzPart + convCompact d.compactPart` does not depend on
the choice of decomposition `d` of `u` into a Schwartz and a
compactly-supported part. -/
theorem convolution_decomp_well_defined_direct
    {u : 𝓢'(E n, ℂ)}
    (hu : ConicSingularSupportSphere u = ∅)

    (convSchwartz : 𝓢(E n, ℂ) → 𝓢'(E n, ℂ))
    (convCompact : 𝓢'(E n, ℂ) → 𝓢'(E n, ℂ))

    (hSchwartz_add : ∀ φ₁ φ₂ : 𝓢(E n, ℂ),
      convSchwartz (φ₁ + φ₂) = convSchwartz φ₁ + convSchwartz φ₂)

    (hCompact_add : ∀ u₁ u₂ : 𝓢'(E n, ℂ),
      convCompact (u₁ + u₂) = convCompact u₁ + convCompact u₂)

    (hcompat : ∀ φ : 𝓢(E n, ℂ),
      IsCompactlySupportedDistribution (schwEmbed φ) →
      convSchwartz φ = convCompact (schwEmbed φ))

    (d₁ d₂ : SchwartzCompactDecomp u) :
    convSchwartz d₁.schwartzPart + convCompact d₁.compactPart =
    convSchwartz d₂.schwartzPart + convCompact d₂.compactPart := by

  set f₁ := d₁.schwartzPart
  set f₂ := d₂.schwartzPart
  set g₁ := d₁.compactPart
  set g₂ := d₂.compactPart


  have hdecomp : schwEmbed f₁ + g₁ = schwEmbed f₂ + g₂ := by
    rw [← d₁.sum_eq, ← d₂.sum_eq]


  have hCss := hasEmptyConicSingularSupportSphere_of_eq_empty u hu
  have hw : IsCompactlySupportedDistribution (schwEmbed (f₁ - f₂)) := by
    rw [map_sub]; exact hCss.diff_compactlySupported d₁ d₂

  have hg₂ : g₂ = schwEmbed (f₁ - f₂) + g₁ := by
    have h : schwEmbed f₁ + g₁ - schwEmbed f₂ = g₂ := by rw [hdecomp]; abel
    show g₂ = schwEmbed (f₁ - f₂) + g₁
    rw [map_sub, ← h]; abel


  have step1 : convSchwartz f₁ = convSchwartz f₂ + convSchwartz (f₁ - f₂) := by
    have h := hSchwartz_add f₂ (f₁ - f₂)
    simp only [add_sub_cancel] at h
    exact h


  have step2 : convSchwartz (f₁ - f₂) = convCompact (schwEmbed (f₁ - f₂)) :=
    hcompat _ hw


  have step3 : convCompact g₂ =
      convCompact (schwEmbed (f₁ - f₂)) + convCompact g₁ := by
    rw [hg₂, hCompact_add]


  calc convSchwartz f₁ + convCompact g₁
      = (convSchwartz f₂ + convSchwartz (f₁ - f₂)) + convCompact g₁ := by rw [step1]
    _ = (convSchwartz f₂ + convCompact (schwEmbed (f₁ - f₂))) + convCompact g₁ := by
        rw [step2]
    _ = convSchwartz f₂ + (convCompact (schwEmbed (f₁ - f₂)) + convCompact g₁) := by
        rw [add_assoc]
    _ = convSchwartz f₂ + convCompact g₂ := by rw [← step3]

end ConeSupport

end
