/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.PerronFrobeniusProof
import Mathlib.Analysis.Normed.Field.Basic

open Matrix Finset BigOperators

namespace PerronFrobenius

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]

/-- Existence of a positive Perron-Frobenius eigenvector and eigenvalue for a strictly
positive matrix, packaged through the simplex fixed-point construction. -/
noncomputable def simplexFixedPoint_pos_matrix
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    Σ' (r : ℝ) (v : ι → ℝ), 0 < r ∧ (∀ i, 0 < v i) ∧ M.mulVec v = r • v :=
  perronFrobeniusExistence M hM

/-- A nonnegative matrix admits a nonnegative eigenvalue and a nonnegative eigenvector
with at least one strictly positive coordinate. -/
noncomputable def nonneg_matrix_has_nonneg_eigenvector
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 ≤ M i j) :
    Σ' (r : ℝ) (v : ι → ℝ), 0 ≤ r ∧ (∀ i, 0 ≤ v i) ∧ (∃ i, 0 < v i) ∧
      M.mulVec v = r • v := by sorry

/-- For a nonnegative matrix `M`, the modulus of any complex eigenvalue is bounded above
by the nonnegative Perron-Frobenius eigenvalue. -/
theorem nonneg_matrix_spectral_radius_dominates
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 ≤ M i j)
    (r : ℝ) (v : ι → ℝ)
    (hr : 0 ≤ r) (hv : ∀ i, 0 ≤ v i) (hv_ne : ∃ i, 0 < v i)
    (heig : M.mulVec v = r • v)
    (μ : ℂ) (w : ι → ℂ) (hw_ne : ∃ i, w i ≠ 0)
    (heig_c : ∀ i, (∑ j, (M i j : ℂ) * w j) = μ * w i) :
    ‖μ‖ ≤ r := by sorry

end PerronFrobenius
