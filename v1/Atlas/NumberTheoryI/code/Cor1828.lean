/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.StieltjesIntegral

open scoped BigOperators

namespace RiemannStieltjes

variable {a b : ℝ}

noncomputable def summatoryFunction (g : ℝ → ℝ) (a : ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊x⌋, g (↑n)

noncomputable def discreteSum (f g : ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊a⌋ ⌊b⌋, f (↑n) * g (↑n)

def NotBothDiscAtIntegers (f g : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ n : ℤ, (↑n : ℝ) ∈ Set.Icc a b →
    (ContinuousWithinAt f (Set.Iio ↑n) ↑n ∨
      ContinuousWithinAt g (Set.Iio ↑n) ↑n) ∧
    (ContinuousWithinAt f (Set.Ioi ↑n) ↑n ∨
      ContinuousWithinAt g (Set.Ioi ↑n) ↑n)

theorem corollary_18_28 (f g : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hcont : NotBothDiscAtIntegers f g a b) :
    HasStieltjesIntegral f (summatoryFunction g a) a b (discreteSum f g a b) := by
  sorry

end RiemannStieltjes
