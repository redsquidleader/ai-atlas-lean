/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProjectionTheory.code.DeltaRegular

open Metric Set InnerProductSpace

namespace ProjectionTheory

/-- A `δ`-tube in $\mathbb{R}^2$, recorded by its midpoint, its direction angle, and its
width (intended to be the small parameter `δ`). The tube is a thin rectangle of length
roughly `1` and width `width`. -/
structure DeltaTube where
  midpoint : EuclideanSpace ℝ (Fin 2)
  direction : ℝ
  width : ℝ

/-- A point `p ∈ ℝ²` lies in the `δ`-tube `T` iff its components along the tube's axis
and along the normal direction satisfy $|⟨p - m, d⟩| \le 1/2$ and
$|⟨p - m, n⟩| \le \text{width}/2$, where `m` is the midpoint, `d` the unit direction,
and `n` the unit normal. -/
def DeltaTube.contains (T : DeltaTube) (p : EuclideanSpace ℝ (Fin 2)) : Prop :=
  let dir_vec := (EuclideanSpace.equiv (Fin 2) ℝ).symm
    ![Real.cos T.direction, Real.sin T.direction]
  let normal_vec := (EuclideanSpace.equiv (Fin 2) ℝ).symm
    ![-Real.sin T.direction, Real.cos T.direction]
  let diff := p - T.midpoint
  |⟪diff, dir_vec⟫_ℝ| ≤ (1 : ℝ) / 2 ∧ |⟪diff, normal_vec⟫_ℝ| ≤ T.width / 2

/-- A finite set of directions `Θ ⊂ ℝ` is `(δ, s, C)`-regular if for every centre `θ₀`
and every radius `r ∈ [δ, 1]`, the count of directions in the arc of radius `r` around
`θ₀` is bounded by `C r^s · |Θ|`. This is the standard Frostman/AD-regular type
condition for the set of tube directions in the OSRW setup. -/
def IsDeltaRegularDir (Θ : Finset ℝ) (δ s C : ℝ) : Prop :=
  0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧ 0 ≤ s ∧
  ∀ (θ₀ : ℝ) (r : ℝ), δ ≤ r → r ≤ 1 →
    ((Θ.filter (fun θ => |θ - θ₀| < r)).card : ℝ) ≤ C * r ^ s * Θ.card

/-- **Sharp Orponen–Shmerkin–Ren–Wang $\delta$-tube bound.** If $E \subset \mathbb{R}^2$
is a $(\delta, t, C)$-set, and for every $x \in E$ the family $\mathbb{T}_x$ of
$\delta$-tubes through $x$ has $(\delta, s, C)$-regular direction set with
$|\mathbb{T}_x| \sim \delta^{-s}$ (and $s > 0$), then the total number of tubes
satisfies
$$|\mathbb{T}| \ge c_\varepsilon\, \delta^\varepsilon\, C^{-O(1)}\,
   \min\!\left(\delta^{-s-t},\ \delta^{-t/2 - 3s/2},\ \delta^{-1-s}\right).$$ -/
theorem osrw_sharp_discretized_projection
    (δ t s C : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (ht : 0 < t) (hs : 0 < s)
    (hC : 0 < C)
    (E : Set (EuclideanSpace ℝ (Fin 2)))
    (hE_reg : DeltaRegular.IsDeltaSRegular δ t C E)
    (hE_size : ENNReal.ofReal (C⁻¹ * δ⁻¹ ^ t) ≤ (DeltaRegular.deltaCoveringNumber δ E : ENNReal))
    (𝕋 : Finset DeltaTube)
    (𝕋_x : EuclideanSpace ℝ (Fin 2) → Finset DeltaTube)
    (h𝕋_cover : ∀ T ∈ 𝕋, ∃ x, x ∈ E ∧ T ∈ 𝕋_x x)
    (h𝕋_support : ∀ x, (𝕋_x x).Nonempty → x ∈ E)
    (h𝕋_through : ∀ x, x ∈ E → ∀ T ∈ 𝕋_x x, T.contains x)
    (h𝕋_width : ∀ T ∈ 𝕋, T.width = δ)
    (h𝕋_dir_reg : ∀ x, x ∈ E →
      IsDeltaRegularDir (Finset.image DeltaTube.direction (𝕋_x x)) δ s C)
    (h𝕋_card : ∀ x, x ∈ E →
      C⁻¹ * δ⁻¹ ^ s ≤ ((𝕋_x x).card : ℝ) ∧ ((𝕋_x x).card : ℝ) ≤ C * δ⁻¹ ^ s)
    (h𝕋_dir_lower : ∀ x, x ∈ E → ∀ (θ₀ : ℝ) (r : ℝ), δ ≤ r → r ≤ 1 →
      C⁻¹ * r ^ s * (Finset.image DeltaTube.direction (𝕋_x x)).card ≤
        ((Finset.image DeltaTube.direction (𝕋_x x)).filter (fun θ => |θ - θ₀| < r)).card)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (c_ε : ℝ) (K : ℝ), 0 < c_ε ∧ 0 < K ∧
      (𝕋.card : ℝ) ≥ c_ε * δ ^ ε * C⁻¹ ^ K *
        min (min (δ⁻¹ ^ (s + t)) (δ⁻¹ ^ (t / 2 + 3 * s / 2))) (δ⁻¹ ^ (1 + s)) := by sorry

end ProjectionTheory
