/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
set_option maxHeartbeats 800000

namespace IsoperimetricEuclidean

open MeasureTheory Metric Set
/-- **Euclidean isoperimetric inequality** (Theorem 9.4.1). Among all measurable subsets of
$\mathbb{R}^n$ with a fixed Lebesgue volume, the closed ball minimizes the volume of the
$t$-thickening: if $\operatorname{vol}(A) = \operatorname{vol}(B(c, r))$, then for every
$t \ge 0$, $\operatorname{vol}(B(c, r)_t) \le \operatorname{vol}(A_t)$. -/
theorem isoperimetric_euclidean
    {n : ℕ} (A : Set (EuclideanSpace ℝ (Fin n)))
    (hA : MeasurableSet A)
    (c : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    (hvol : volume A = volume (closedBall c r))
    (t : ℝ) (ht : 0 ≤ t) :
    volume (cthickening t (closedBall c r)) ≤ volume (cthickening t A) := by sorry

end IsoperimetricEuclidean
