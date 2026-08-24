/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped ENNReal NNReal Pointwise
open Set Metric

namespace ABCSumProduct

/-- The `δ`-covering number `|X|_δ` of a subset `X ⊆ ℝ`: the minimum number of balls of
radius `δ` needed to cover `X`. Returned as an `ℕ∞` value. -/
noncomputable def deltaCoveringNumberR (δ : ℝ) (X : Set ℝ) : ℕ∞ :=
  Metric.coveringNumber δ.toNNReal X

/-- A set `X ⊆ B(0,1) ⊂ ℝ` is `(δ, s, C)`-regular if for every ball `B(x, r)` with
`δ ≤ r ≤ 1` we have `|X ∩ B(x, r)|_δ ≤ C r^s |X|_δ`. This is the one-dimensional
δ-discretised version of the `(δ, s, C)`-set condition used in projection theory. -/
def IsDeltaRegularSetR (δ s C : ℝ) (X : Set ℝ) : Prop :=
  X ⊆ ball (0 : ℝ) 1 ∧
  ∀ (x : ℝ) (r : ℝ), δ ≤ r → r ≤ 1 →
    (deltaCoveringNumberR δ (X ∩ ball x r) : ℝ≥0∞) ≤
      ENNReal.ofReal (C * r ^ s) * (deltaCoveringNumberR δ X : ℝ≥0∞)

/-- `X` has covering exponent `s` (up to a multiplicative constant `C`) at scale `δ`:
`C⁻¹ δ^{-s} ≤ |X|_δ ≤ C δ^{-s}`. This says `|X|_δ ∼ δ^{-s}`. -/
def HasCoveringExponent (δ s C : ℝ) (X : Set ℝ) : Prop :=
  ENNReal.ofReal (C⁻¹ * δ ^ (-s)) ≤ (deltaCoveringNumberR δ X : ℝ≥0∞) ∧
  (deltaCoveringNumberR δ X : ℝ≥0∞) ≤ ENNReal.ofReal (C * δ ^ (-s))

/-- **ABC sum-product theorem** (Orponen–Shmerkin). For exponents `0 < a, b, c ≤ 1`,
there exists `η > 0` such that if `A`, `B`, `C ⊆ ℝ` are `(δ, a, δ^{-η})`-,
`(δ, b, δ^{-η})`-, `(δ, c, δ^{-η})`-sets with covering numbers `≈ δ^{-a}`, `δ^{-b}`,
`δ^{-c}` respectively, and `|A + tB|_δ ≲ δ^{-η}|A|_δ` for every `t ∈ C`, then
`a ≥ b + c`. -/
theorem abc_sum_product_theorem
  (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (ha1 : a ≤ 1) (hb1 : b ≤ 1) (hc1 : c ≤ 1) :
  ∃ η : ℝ, η > 0 ∧
    ∀ δ : ℝ, 0 < δ → δ < 1 →
      ∀ A B C : Set ℝ,
        IsDeltaRegularSetR δ a (δ ^ (-η)) A →
        IsDeltaRegularSetR δ b (δ ^ (-η)) B →
        IsDeltaRegularSetR δ c (δ ^ (-η)) C →
        HasCoveringExponent δ a (δ ^ (-η)) A →
        HasCoveringExponent δ b (δ ^ (-η)) B →
        HasCoveringExponent δ c (δ ^ (-η)) C →
        (∀ t ∈ C, (deltaCoveringNumberR δ (A + t • B) : ℝ≥0∞) ≤
          ENNReal.ofReal (δ ^ (-η)) * (deltaCoveringNumberR δ A : ℝ≥0∞)) →
        a ≥ b + c := by sorry

end ABCSumProduct
