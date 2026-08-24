/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProjectionTheory.code.KeyLemmaBSG
import Atlas.ProjectionTheory.code.BSGProposition

namespace ProjectionTheory

open Finset

/--
Balog–Szemerédi–Gowers (projection variant). For a commutative ring `G` and any
parameter `t ∈ G`, define the projection `πₜ(a, b) = a + t·b`. If
`X ⊆ A × B` with `|A|, |B| ≤ N`, `|X| ≥ K⁻¹ N²` and `|πₜ(X)| ≤ K N`, then there
exist refined subsets `A' ⊆ A`, `B' ⊆ B` such that `|X ∩ (A' × B')| ≳ K^{-O(1)} N²`
and `|πₜ(A' × B')| ≲ K^{O(1)} N`. This is the form of BSG used in the proof of
the Bourgain–Katz–Tao sum-product theorem.
-/
theorem bsg_projection_variant
    {G : Type*} [CommRing G] [DecidableEq G] :
    ∃ (c₁ c₂ : ℕ) (C₁ : ℝ) (C₂ : ℝ), C₁ > 0 ∧ C₂ > 0 ∧
    ∀ (A B : Finset G) (X : Finset (G × G)) (t : G) (N : ℕ) (K : ℝ),
      K ≥ 1 → A.card ≤ N → B.card ≤ N → X ⊆ A ×ˢ B →
      (X.card : ℝ) ≥ K⁻¹ * (N : ℝ) ^ 2 →
      ((X.image (fun p => p.1 + t * p.2)).card : ℝ) ≤ K * (N : ℝ) →
      ∃ A' : Finset G, ∃ B' : Finset G,
        A' ⊆ A ∧ B' ⊆ B ∧
        ((X.filter (fun p => p ∈ A' ×ˢ B')).card : ℝ) ≥ C₁ * K ^ (-(c₁ : ℤ)) * (N : ℝ) ^ 2 ∧
        (((A' ×ˢ B').image (fun p => p.1 + t * p.2)).card : ℝ) ≤ C₂ * K ^ (c₂ : ℤ) * (N : ℝ) := by sorry

end ProjectionTheory
