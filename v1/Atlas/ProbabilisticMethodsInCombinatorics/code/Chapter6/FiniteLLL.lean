/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Tactic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Data.Fintype.Card
import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.LovaszLocalLemma

open MeasureTheory ProbabilityTheory Set Finset ENNReal

noncomputable section

set_option maxHeartbeats 800000

namespace Beck

variable {α ι : Type*}

/-- Restrict a Boolean function on `α` to the subtype of elements lying in a finset `C`. -/
def restrictToSubtype [DecidableEq α] (C : Finset α) (f : α → Bool) : {a // a ∈ C} → Bool :=
  fun ⟨a, _⟩ => f a

/-- General product-space LLL: in the uniform product probability space on `α → Bool`, if each
bad event $A_i$ depends only on the coordinates in `coords i`, and the dependency digraph $G$
together with weights $x_i \in [0,1)$ satisfies the LLL probability bound, then there exists a
Boolean assignment avoiding all bad events. -/
theorem product_space_lll_existence [Fintype α] [DecidableEq α]
    [Fintype ι] [DecidableEq ι]
    (G : Digraph ι) [DecidableRel G.Adj]
    (A : ι → Set (α → Bool))
    (hA_meas : ∀ i, MeasurableSet (A i))
    (coords : ι → Finset α)
    (hA_coords : ∀ i, ∀ f g : α → Bool, (∀ a ∈ coords i, f a = g a) → (f ∈ A i ↔ g ∈ A i))
    (hG_dep : ∀ i j, ¬G.Adj i j → j ≠ i → Disjoint (coords i) (coords j))
    (x : ι → ℝ) (hx01 : ∀ i, 0 ≤ x i ∧ x i < 1)
    (hbound : ∀ i, @Finset.card _ (@Finset.filter _ (· ∈ A i)
        (Classical.decPred _) Finset.univ) ≤
        ENNReal.toReal (ENNReal.ofReal (x i * ∏ j ∈ LovaszLocalLemma.neighbors G i, (1 - x j))) *
        (2 ^ Fintype.card α)) :
    ∃ f : α → Bool, ∀ i, f ∉ A i := by sorry

end Beck

end
