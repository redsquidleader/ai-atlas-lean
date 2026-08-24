/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.SobolevDerivatives

open MeasureTheory SobolevSpace TemperedDistributions
open scoped FourierTransform SchwartzMap

noncomputable section

namespace SobolevRegularity

variable {n : ℕ}

/-- For nonnegative integer order `m`, membership in the Sobolev space `Hˢ(ℝⁿ)` with
`s = m` is equivalent to all distributional derivatives of order at most `m` being in
`L²`. -/
theorem sobolev_iff_derivatives_in_L2
    (m : ℕ) (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    MemHs n (m : ℝ) u ↔ AllDerivMemL2 n m u :=
  sobolev_integer_iff_deriv_memL2 m u

end SobolevRegularity

end
