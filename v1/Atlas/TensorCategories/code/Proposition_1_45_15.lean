/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.FrobeniusPerron

open Real FusionRing
open scoped Matrix

/-- Proposition 1.45.15 (Kronecker): Let `B` be a matrix with nonnegative integer entries
such that `λ(BBᵀ) = λ(B)²`. If `λ(B) < 2` then `λ(B) = 2 cos(π / n)` for some integer
`n ≥ 2`. -/
theorem proposition_1_45_15
    {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]
    (B : Matrix ι ι ℕ)
    (ev : ℝ) (v : ι → ℝ)
    (hv_pos : ∀ i, 0 < v i)
    (hv_eig : (B.map (Nat.cast : ℕ → ℝ)).mulVec v = ev • v)
    (w : ι → ℝ)
    (hw_pos : ∀ i, 0 < w i)
    (hw_eig : ((B.map (Nat.cast : ℕ → ℝ)) * (B.map (Nat.cast : ℕ → ℝ)).transpose).mulVec w
              = (ev ^ 2) • w)
    (hPF : ∀ μ : ℂ, IsComplexEigenvalue (B.map (Nat.cast : ℕ → ℝ)) μ → ‖μ‖ ≤ ev)
    (hev_lt : ev < 2) :
    ∃ n : ℕ, 2 ≤ n ∧ ev = 2 * cos (π / n) :=
  kronecker_eigenvalue_cos B ev v hv_pos hv_eig w hw_pos hw_eig hPF hev_lt
