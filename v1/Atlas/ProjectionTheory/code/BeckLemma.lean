/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProjectionTheory.code.BourgainLemma

noncomputable section

open scoped NNReal ENNReal

namespace BeckLemma

open BourgainUniform

/-- **ε-bootstrap step for Continuum Beck's Theorem.** If `0 < s < min(u, 1)` then
there exist `ε > 0` and `η ∈ (0, 1)` such that the following holds: for any scale
`Δ ∈ (0, 1)`, any `m`, any planar set `E` with a uniform "good" subset `G ⊆ E` of
proportional `Δ^m`-mesh count at least `1 − η`, where each `Lx` (the line-set through
`x ∈ G`) is `(Δ^m, s, C)`-regular, one can produce a possibly smaller good set
`G' ⊆ E` of the same proportional size on which the line-set is `(Δ^m, s + ε, C')`-
regular. This is the bootstrap mechanism behind the lemma "if a typical `L_{x,E}` is
`(δ, s, C)` then a typical `L_{x,E}` is `(δ, s + ε, C')`". -/
theorem beck_bootstrap_epsilon_improvement
    (u s : ℝ)
    (hu : 0 < u) (hs : 0 < s) (hs_min : s < min u 1) :
    ∃ (ε : ℝ) (η : ℝ), ε > 0 ∧ 0 < η ∧ η < 1 ∧
      ∀ (Δ : ℝ) (m : ℕ) (C : ℝ≥0)
        (E : Set (EuclideanSpace ℝ (Fin 2)))
        (Lx : EuclideanSpace ℝ (Fin 2) → Set (EuclideanSpace ℝ (Fin 1)))
        (hΔ_pos : (0 : ℝ) < Δ) (hΔ_lt : Δ < 1)
        (G : Set (EuclideanSpace ℝ (Fin 2)))
        (hG_sub : G ⊆ E)
        (hG_large : ENNReal.ofReal (1 - η) * (meshCount (Δ ^ m) E : ℝ≥0∞)
                    ≤ (meshCount (Δ ^ m) G : ℝ≥0∞))
        (hUnif : ∀ x ∈ G, IsUniform Δ m (Lx x))
        (hReg : ∀ x ∈ G, IsRegularSet (Δ ^ m) s C (Lx x)),
        ∃ (C' : ℝ≥0) (G' : Set (EuclideanSpace ℝ (Fin 2))),
          G' ⊆ E ∧
          ENNReal.ofReal (1 - η) * (meshCount (Δ ^ m) E : ℝ≥0∞)
            ≤ (meshCount (Δ ^ m) G' : ℝ≥0∞) ∧
          ∀ x ∈ G', IsRegularSet (Δ ^ m) (s + ε) C' (Lx x) := by sorry

end BeckLemma

end
