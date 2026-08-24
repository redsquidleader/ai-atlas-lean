/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProjectionTheory.code.BKTLemma4

namespace BKT

open Finset

/-- Structured-subset version of BKT: assuming `X ⊆ A × A` for some `A ⊆ 𝔽_p` with
`|A|² ≥ |X|`, there exist `ε > 0` and a direction `t ∈ D` so that the projection
`π_t(X) = {x₁ + t · x₂ : x ∈ X}` satisfies `|π_t(X)| ≥ p^ε · |X|^{1/2}`. This is the
key step in deducing BKT from the abelian sum–product input. -/
theorem expansion_from_structured_subset
    (p : ℕ) [Fact (Nat.Prime p)]
    (X : Finset (ZMod p × ZMod p)) (D : Finset (ZMod p))
    (A : Finset (ZMod p))
    (hA_lower : 1 < A.card) (hA_upper : (A.card : ℝ) ≤ p)
    (hD_card : 1 < D.card)
    (hX_sub : ∀ x ∈ X, x.1 ∈ A ∧ x.2 ∈ A)
    (hX_lower : 1 < X.card)
    (hX_upper : (X.card : ℝ) < (p : ℝ) ^ 2)
    (hA_ge_sqrt : (A.card : ℝ) ^ 2 ≥ (X.card : ℝ)) :
    ∃ ε : ℝ, ε > 0 ∧ ∃ t ∈ D,
      ((Finset.image (fun x => x.1 + t * x.2) X).card : ℝ) ≥
        (p : ℝ) ^ ε * (X.card : ℝ) ^ ((1 : ℝ) / 2) := by sorry

/-- The Bourgain–Katz–Tao projection theorem (BKT) in `𝔽_p²`: for `X ⊆ 𝔽_p²` of size
`|X| = p^{s_X}` with `0 < s_X < 2` and a nontrivial set of directions `D ⊆ 𝔽_p`,
there exist `ε > 0` and `t ∈ D` such that the linear projection
`π_t(X) = {x₁ + t · x₂ : x ∈ X}` obeys `|π_t(X)| ≥ p^ε · |X|^{1/2}`.
The argument reduces to `expansion_from_structured_subset` applied to
`A = π_1(X) ∪ π_2(X)`. -/
theorem bkt_projection_bound (p : ℕ) [Fact (Nat.Prime p)]
    (X : Finset (ZMod p × ZMod p)) (D : Finset (ZMod p))
    (hX : 1 < X.card) (hD : 1 < D.card)
    (hX_upper : (X.card : ℝ) < (p : ℝ) ^ 2)
    (hD_upper : (D.card : ℝ) ≤ (p : ℝ)) :
    ∃ ε : ℝ, ε > 0 ∧ ∃ t ∈ D,
      ((Finset.image (fun x => x.1 + t * x.2) X).card : ℝ) ≥
        (p : ℝ) ^ ε * (X.card : ℝ) ^ ((1 : ℝ) / 2) := by

  set A := (X.image Prod.fst) ∪ (X.image Prod.snd)
  have hX_sub : ∀ x ∈ X, x.1 ∈ A ∧ x.2 ∈ A := fun x hx =>
    ⟨Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx),
     Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx)⟩

  have hA_card_ge : 1 < A.card := by
    obtain ⟨⟨a₁, b₁⟩, h1, ⟨a₂, b₂⟩, h2, hne⟩ := Finset.one_lt_card.mp hX
    have hne' : a₁ ≠ a₂ ∨ b₁ ≠ b₂ := by
      by_contra h
      simp only [not_or, not_not] at h
      exact hne (Prod.ext h.1 h.2)
    rcases hne' with ha | hb
    · exact Finset.one_lt_card.mpr ⟨a₁, (hX_sub _ h1).1, a₂, (hX_sub _ h2).1, ha⟩
    · exact Finset.one_lt_card.mpr ⟨b₁, (hX_sub _ h1).2, b₂, (hX_sub _ h2).2, hb⟩

  have hA_upper : (A.card : ℝ) ≤ (p : ℝ) := by
    have : A.card ≤ p := by
      calc A.card ≤ (Finset.univ : Finset (ZMod p)).card := Finset.card_le_univ A
        _ = p := by simp [ZMod.card]
    exact_mod_cast this

  have hA_ge_sqrt : (A.card : ℝ) ^ 2 ≥ (X.card : ℝ) := by
    have h : X.card ≤ A.card ^ 2 := by
      calc X.card ≤ (A ×ˢ A).card := Finset.card_le_card (fun x hx =>
            Finset.mem_product.mpr (hX_sub x hx))
        _ = A.card ^ 2 := by rw [Finset.card_product]; ring
    exact_mod_cast h

  exact expansion_from_structured_subset p X D A hA_card_ge hA_upper hD hX_sub hX hX_upper
    hA_ge_sqrt

end BKT
