/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Atlas.ProbabilisticMethodsInCombinatorics.code.DecomposingCoveringsAxiom

open Set Metric

namespace DecomposingCoverings

noncomputable section

variable {ι : Type*}

/-- A family of unit balls with centres `center` is a covering of $\mathbb{R}^3$ when
every point is covered by at least one ball. -/
def IsCovering (center : ι → E3) : Prop :=
  ∀ x : E3, (coveringSet center x).Nonempty

/-- A family of unit balls is decomposable if its index set can be partitioned into two
classes $A$ and $A^c$ such that both subfamilies still cover $\mathbb{R}^3$. -/
def IsDecomposable (center : ι → E3) : Prop :=
  ∃ (A : Set ι), IsCovering (fun i : A => center i.val) ∧
                  IsCovering (fun i : ↥Aᶜ => center i.val)

/-- Theorem 6.2.12 (Mani-Levitska, Pach 1986). Any $k$-fold covering of $\mathbb{R}^3$ by
unit balls that cannot be split into two coverings must cover some point at least
$2^{k/3}$ times. -/
theorem theorem_6_2_12 (center : ι → E3) (k : ℕ) (hk : 2 ≤ k)
    (hcov : IsKFoldCovering center k)
    (hindec : ¬ IsDecomposable center) :
    ∃ x : E3, (2 : ℝ) ^ ((k : ℝ) / 3) ≤ ↑(mult center x) := by
  by_contra h_all_small
  push_neg at h_all_small

  apply hindec

  obtain ⟨A, hA_in, hAc_in⟩ := proper_2coloring_exists ι center k hk hcov h_all_small

  exact ⟨A, fun x => by
    obtain ⟨i, hi_cov, hi_A⟩ := hA_in x
    exact ⟨⟨i, hi_A⟩, by simpa [coveringSet] using hi_cov⟩,
    fun x => by
    obtain ⟨j, hj_cov, hj_notA⟩ := hAc_in x
    exact ⟨⟨j, hj_notA⟩, by simpa [coveringSet] using hj_cov⟩⟩

end

end DecomposingCoverings
