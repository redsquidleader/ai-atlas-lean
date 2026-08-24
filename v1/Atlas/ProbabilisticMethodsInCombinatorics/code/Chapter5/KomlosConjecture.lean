/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

namespace Discrepancy


/-- **Komlós conjecture** (Conjecture 5.1.5). There exists an absolute constant $K > 0$
such that for any vectors $v_1, \dots, v_m \in \mathbb{R}^n$ with $\|v_i\| \leq 1$,
one can choose signs $\varepsilon_i \in \{\pm 1\}$ so that
$\left\|\sum_i \varepsilon_i v_i\right\|_\infty \leq K$. -/
theorem komlos_conjecture :
  ∃ K : ℝ, 0 < K ∧ ∀ (n m : ℕ) (v : Fin m → EuclideanSpace ℝ (Fin n)),
    (∀ i, ‖v i‖ ≤ 1) →
    ∃ ε : Fin m → ℝ, (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ j : Fin n, |∑ i : Fin m, ε i * (v i j)| ≤ K := by sorry

end Discrepancy
