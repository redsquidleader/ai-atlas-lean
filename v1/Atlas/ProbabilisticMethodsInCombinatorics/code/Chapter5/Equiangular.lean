/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Real Finset BigOperators

namespace Equiangular

/-- **Exponentially many approximately equiangular vectors** (Theorem 5.2.1).
For any target inner product $\alpha \in (0, 1)$ and tolerance $\varepsilon > 0$, there is
a constant $c > 0$ such that for every $n$ there exist $N \geq 2^{cn}$ unit vectors
$v_1, \dots, v_N \in \mathbb{R}^n$ with $|\langle v_i, v_j \rangle - \alpha| \leq \varepsilon$
for all $i \neq j$. -/
theorem exists_exp_many_approx_equiangular
    (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (c : ℝ), 0 < c ∧
      ∀ (n : ℕ), ∃ (N : ℕ) (v : Fin N → EuclideanSpace ℝ (Fin n)),
        (∀ i, ‖v i‖ = 1) ∧
        (∀ i j, i ≠ j → |@inner ℝ _ _ (v i) (v j) - α| ≤ ε) ∧
        (N : ℝ) ≥ 2 ^ (c * (n : ℝ)) := by sorry

/-- **Exponentially many approximately orthogonal vectors**. For any tolerance
$\varepsilon > 0$ there is a constant $c > 0$ such that for every dimension $d$ there exist
$N \geq \exp(c \varepsilon^2 d)$ unit vectors $v_1, \dots, v_N \in \mathbb{R}^d$ with
$|\langle v_i, v_j \rangle| \leq \varepsilon$ for all $i \neq j$. -/
theorem exists_exp_many_approx_orthogonal
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (c : ℝ), 0 < c ∧
      ∀ (d : ℕ), ∃ (N : ℕ) (v : Fin N → EuclideanSpace ℝ (Fin d)),
        (∀ i, ‖v i‖ = 1) ∧
        (∀ i j, i ≠ j → |@inner ℝ _ _ (v i) (v j)| ≤ ε) ∧
        (N : ℝ) ≥ exp (c * ε ^ 2 * (d : ℝ)) := by sorry

end Equiangular
