/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.WavefrontSet

noncomputable section

open scoped SchwartzMap FourierTransform
open MeasureTheory

namespace ConeSupport

variable {n : ℕ}


/-- Decomposition of a tempered distribution `u` away from a closed conic set `Γ` disjoint from the
conic singular support: `u` can be written as `u₁' + u₁'' + u₂` where `u₁'` is compactly supported,
`u₁''` vanishes on test functions supported far from the origin and supported in directions in `Γ`,
`u₂` is Schwartz, and the conic support of `u₁' + u₁''` is disjoint from `Γ`. -/
theorem exists_decomposition_disjoint_conicSingularSupport'
    (u : 𝓢'(E n, ℂ))
    (Γ : Set (Sphere n))
    (hΓ_closed : IsClosed Γ)
    (hΓ_disjoint : Disjoint (ConicSingularSupportSphere u) Γ) :
    ∃ (u₁' u₁'' : 𝓢'(E n, ℂ)) (u₂ : 𝓢(E n, ℂ)),
      u = u₁' + u₁'' + (u₂ : 𝓢'(E n, ℂ)) ∧
      IsCompactlySupportedDistribution u₁' ∧


      (∃ ε : ℝ, 0 < ε ∧ ∀ f : 𝓢(E n, ℂ),
        (∀ x : E n, ε ≤ ‖x‖ → f x = 0) → u₁'' f = 0) ∧


      (∀ f : 𝓢(E n, ℂ),
        (∀ x : E n, f x ≠ 0 → x ≠ 0 ∧ ∀ (hx : x ≠ 0), directionOf x hx ∈ Γ) →
        u₁'' f = 0) ∧
      Disjoint (ConicSupportSphere (u₁' + u₁'')) Γ := by sorry

end ConeSupport

end
