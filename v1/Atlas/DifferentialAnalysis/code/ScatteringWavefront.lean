/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.WavefrontSet

namespace WavefrontSet

open scoped SchwartzMap FourierTransform

variable {n : ℕ}

/-- Decomposition characterization of the scattering wavefront set on boundary pairs:
for `(p, q) ∈ BoundaryProd n`, the pair lies outside `WFsc u` iff `u` decomposes as
`u = u₁ + u₂` with `p` outside the scattering singular support of `u₁` and `q`
outside the scattering singular support of `𝓕 u₂`. -/
theorem wfsc_decomposition_iff
    {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    {p q : ClosedBall n} (hpq : (p, q) ∈ BoundaryProd n) :
    (p, q) ∉ WFsc u ↔
    ∃ u₁ u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ),
      u = u₁ + u₂ ∧ p ∉ Css u₁ ∧ q ∉ Css (𝓕 u₂) :=
  not_mem_wfsc_iff_exists_decomp hpq

end WavefrontSet
