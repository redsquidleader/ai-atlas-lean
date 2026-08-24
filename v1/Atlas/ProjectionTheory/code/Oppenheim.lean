/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped Matrix

namespace Oppenheim

/-- A real quadratic form $Q$ is *indefinite* if it has mixed signature, i.e. it attains both
strictly positive and strictly negative values. -/
def IsIndefinite {n : ℕ} (Q : QuadraticForm ℝ (Fin n → ℝ)) : Prop :=
  (∃ v : Fin n → ℝ, Q v > 0) ∧ (∃ v : Fin n → ℝ, Q v < 0)

/-- A real quadratic form $Q$ is *proportional to an integer form* if there exist a scalar
$c \in \mathbb{R}$ and an integer matrix $M$ such that the Gram matrix of $Q$ equals
$c \cdot M$ (i.e. the coefficients of $Q$ all lie in $\mathbb{Z}\alpha$ for some $\alpha$). -/
def IsProportionalToIntegerForm {n : ℕ}
    (Q : QuadraticForm ℝ (Fin n → ℝ)) : Prop :=
  ∃ (c : ℝ) (M : Matrix (Fin n) (Fin n) ℤ),
    QuadraticMap.toMatrix' Q = c • (M.map (Int.cast : ℤ → ℝ))


/-- **Oppenheim conjecture** (Margulis): if $n \ge 3$, $Q$ is a nondegenerate indefinite real
quadratic form in $n$ variables whose coefficients are not all proportional to integers, then
the set of values $Q(\mathbb{Z}^n)$ is dense in $\mathbb{R}$. -/
theorem oppenheim_conjecture
    {n : ℕ} (hn : n ≥ 3) (Q : QuadraticForm ℝ (Fin n → ℝ))
    (hnd : QuadraticMap.Nondegenerate (Q := Q))
    (hind : IsIndefinite Q)
    (hrat : ¬ IsProportionalToIntegerForm Q) :
    Dense (Set.range (fun v : Fin n → ℤ => Q (fun i => (v i : ℝ)))) := by sorry

end Oppenheim
