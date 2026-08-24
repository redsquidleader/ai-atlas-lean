/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter4.Background_Weyl

open Matrix Real Finset

noncomputable section

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

/-- **Hoffman-Wielandt inequality.** For matrices `A`, `B : Fin d × Fin T → ℝ` with
ordered singular value decompositions `S_A` and `S_B` of the same rank, the sum of squared
differences of corresponding singular values is bounded by the squared Frobenius norm of
`A - B`:  $\sum_k (\sigma_k(A) - \sigma_k(B))^2 \le \|A - B\|_F^2$. -/
theorem hoffman_wielandt_inequality {d T : ℕ}
    (A B : Matrix (Fin d) (Fin T) ℝ)
    (S_A : SVD d T) (hA : S_A.IsDecompOf A) (hA_ord : S_A.IsOrdered)
    (S_B : SVD d T) (hB : S_B.IsDecompOf B) (hB_ord : S_B.IsOrdered)
    (hr : S_A.r = S_B.r) :
    ∑ k : Fin S_A.r, |S_A.σval k - S_B.σval (Fin.cast hr k)| ^ 2 ≤
      ‖A - B‖ ^ 2 := by sorry

end
