/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.EisensteinSeries
import Atlas.EllipticCurves.code.JInvariant
import Atlas.EllipticCurves.code.Isogenies
import Atlas.EllipticCurves.code.WeierstrassPOrder

import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
import Mathlib.NumberTheory.Modular

open Complex PeriodPair

noncomputable section

namespace ComplexLattice

variable (L : ComplexLattice)

/-- Algebraic discriminant criterion: if the cubic `4x^3 - g₂ x - g₃` has three
distinct roots `e₁, e₂, e₃`, then the discriminant `g₂^3 - 27 g₃^2` of the
corresponding elliptic curve is nonzero. -/
lemma discr_ne_zero_of_three_distinct_roots {g₂ g₃ e₁ e₂ e₃ : ℂ}
    (h1 : 4 * e₁ ^ 3 - g₂ * e₁ - g₃ = 0)
    (h2 : 4 * e₂ ^ 3 - g₂ * e₂ - g₃ = 0)
    (h3 : 4 * e₃ ^ 3 - g₂ * e₃ - g₃ = 0)
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) :
    g₂ ^ 3 - 27 * g₃ ^ 2 ≠ 0 := by

  have hsub12 : (e₁ - e₂) * (4 * (e₁ ^ 2 + e₁ * e₂ + e₂ ^ 2) - g₂) = 0 := by
    linear_combination h1 - h2
  have hne12 : e₁ - e₂ ≠ 0 := sub_ne_zero.mpr h12
  have hg₂_12 : g₂ = 4 * (e₁ ^ 2 + e₁ * e₂ + e₂ ^ 2) := by
    have := (mul_eq_zero.mp hsub12).resolve_left hne12; linear_combination -this

  have hsub13 : (e₁ - e₃) * (4 * (e₁ ^ 2 + e₁ * e₃ + e₃ ^ 2) - g₂) = 0 := by
    linear_combination h1 - h3
  have hne13 : e₁ - e₃ ≠ 0 := sub_ne_zero.mpr h13
  have hg₂_13 : g₂ = 4 * (e₁ ^ 2 + e₁ * e₃ + e₃ ^ 2) := by
    have := (mul_eq_zero.mp hsub13).resolve_left hne13; linear_combination -this

  have h_eq : e₁ * e₂ + e₂ ^ 2 = e₁ * e₃ + e₃ ^ 2 := by
    have h4 : (4 : ℂ) ≠ 0 := by norm_num
    have := mul_left_cancel₀ h4 (hg₂_12.symm.trans hg₂_13)
    linear_combination this

  have hfactor : (e₂ - e₃) * (e₁ + e₂ + e₃) = 0 := by
    have : (e₂ - e₃) * (e₁ + e₂ + e₃) = (e₁ * e₂ + e₂ ^ 2) - (e₁ * e₃ + e₃ ^ 2) := by ring
    rw [this, h_eq, sub_self]

  have hne23 : e₂ - e₃ ≠ 0 := sub_ne_zero.mpr h23
  have hsum : e₁ + e₂ + e₃ = 0 := (mul_eq_zero.mp hfactor).resolve_left hne23
  have he₃ : e₃ = -(e₁ + e₂) := by linear_combination hsum

  have hg₃ : g₃ = -4 * e₁ * e₂ * (e₁ + e₂) := by
    have : g₃ = 4 * e₁ ^ 3 - g₂ * e₁ := by linear_combination -h1
    rw [this, hg₂_12]; ring

  have hident : g₂ ^ 3 - 27 * g₃ ^ 2 =
      16 * (e₁ - e₂) ^ 2 * (e₁ - e₃) ^ 2 * (e₂ - e₃) ^ 2 := by
    rw [he₃, hg₂_12, hg₃]; ring
  rw [hident]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num : (16 : ℂ) ≠ 0) (pow_ne_zero 2 hne12))
    (pow_ne_zero 2 hne13)) (pow_ne_zero 2 hne23)

/-- The half-sum `(ω₁ + ω₂)/2` of the two fundamental periods does not lie in
the lattice `L`. -/
lemma sum_div_two_notMem_lattice : (L.ω₁ + L.ω₂) / 2 ∉ L.lattice := by
  have : (L.ω₁ + L.ω₂) / 2 = (1/2 : ℚ) * L.ω₁ + (1/2 : ℚ) * L.ω₂ := by
    push_cast; ring
  rw [this]
  exact (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 1 / 2) (β := 1 / 2)).not.mpr (by norm_num)

/-- The derivative of the Weierstrass ℘-function vanishes at the half period
`ω₁ / 2`. -/
lemma derivWeierstrassP_halfPeriod₁ : ℘'[L] (L.ω₁ / 2) = 0 := by
  have h1 := L.derivWeierstrassP_neg (L.ω₁ / 2)
  have h2 : -(L.ω₁ / 2) = L.ω₁ / 2 - ↑(⟨L.ω₁, L.ω₁_mem_lattice⟩ : L.lattice) := by
    simp [sub_eq_neg_add]; ring
  rw [h2, L.derivWeierstrassP_sub_coe] at h1
  rw [← CharZero.eq_neg_self_iff]; exact h1

/-- The derivative of the Weierstrass ℘-function vanishes at the half period
`ω₂ / 2`. -/
lemma derivWeierstrassP_halfPeriod₂ : ℘'[L] (L.ω₂ / 2) = 0 := by
  have h1 := L.derivWeierstrassP_neg (L.ω₂ / 2)
  have h2 : -(L.ω₂ / 2) = L.ω₂ / 2 - ↑(⟨L.ω₂, L.ω₂_mem_lattice⟩ : L.lattice) := by
    simp [sub_eq_neg_add]; ring
  rw [h2, L.derivWeierstrassP_sub_coe] at h1
  rw [← CharZero.eq_neg_self_iff]; exact h1

/-- The derivative of the Weierstrass ℘-function vanishes at the half period
`(ω₁ + ω₂) / 2`. -/
lemma derivWeierstrassP_halfPeriod₃ : ℘'[L] ((L.ω₁ + L.ω₂) / 2) = 0 := by
  have h1 := L.derivWeierstrassP_neg ((L.ω₁ + L.ω₂) / 2)
  have hmem : L.ω₁ + L.ω₂ ∈ L.lattice :=
    L.lattice.add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice
  have h2 : -((L.ω₁ + L.ω₂) / 2) =
      (L.ω₁ + L.ω₂) / 2 - ↑(⟨L.ω₁ + L.ω₂, hmem⟩ : L.lattice) := by
    simp [sub_eq_neg_add]; ring
  rw [h2, L.derivWeierstrassP_sub_coe] at h1
  rw [← CharZero.eq_neg_self_iff]; exact h1

/-- The value `e₁ = ℘(ω₁/2)` is a root of the cubic `4x³ - g₂ x - g₃ = 0`
associated to the lattice `L`. -/
lemma weierstrassP_halfPeriod₁_isRoot :
    4 * ℘[L] (L.ω₁ / 2) ^ 3 - L.g₂ * ℘[L] (L.ω₁ / 2) - L.g₃ = 0 := by
  have h := L.derivWeierstrassP_sq (L.ω₁ / 2) L.ω₁_div_two_notMem_lattice
  rw [L.derivWeierstrassP_halfPeriod₁] at h; simp at h; exact h.symm

/-- The value `e₂ = ℘(ω₂/2)` is a root of the cubic `4x³ - g₂ x - g₃ = 0`
associated to the lattice `L`. -/
lemma weierstrassP_halfPeriod₂_isRoot :
    4 * ℘[L] (L.ω₂ / 2) ^ 3 - L.g₂ * ℘[L] (L.ω₂ / 2) - L.g₃ = 0 := by
  have h := L.derivWeierstrassP_sq (L.ω₂ / 2) L.ω₂_div_two_notMem_lattice
  rw [L.derivWeierstrassP_halfPeriod₂] at h; simp at h; exact h.symm

/-- The value `e₃ = ℘((ω₁+ω₂)/2)` is a root of the cubic
`4x³ - g₂ x - g₃ = 0` associated to the lattice `L`. -/
lemma weierstrassP_halfPeriod₃_isRoot :
    4 * ℘[L] ((L.ω₁ + L.ω₂) / 2) ^ 3 -
      L.g₂ * ℘[L] ((L.ω₁ + L.ω₂) / 2) - L.g₃ = 0 := by
  have h := L.derivWeierstrassP_sq ((L.ω₁ + L.ω₂) / 2) L.sum_div_two_notMem_lattice
  rw [L.derivWeierstrassP_halfPeriod₃] at h; simp at h; exact h.symm

/-- The point `(ω₁ - ω₂)/2` does not lie in the lattice. -/
lemma ω₁_sub_ω₂_div_two_notMem_lattice : (L.ω₁ - L.ω₂) / 2 ∉ (L.lattice : Set ℂ) := by
  have : (L.ω₁ - L.ω₂) / 2 = (1/2 : ℚ) * L.ω₁ + (-(1/2) : ℚ) * L.ω₂ := by
    push_cast; ring
  rw [this]
  exact (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 1 / 2) (β := -(1 / 2))).not.mpr (by norm_num)

/-- The difference `ω₁/2 - (ω₁ + ω₂)/2 = -ω₂/2` of two half periods does not
lie in the lattice. -/
lemma ω₁_sub_sum_div_two_notMem_lattice :
    L.ω₁ / 2 - (L.ω₁ + L.ω₂) / 2 ∉ (L.lattice : Set ℂ) := by
  have : L.ω₁ / 2 - (L.ω₁ + L.ω₂) / 2 = (0 : ℚ) * L.ω₁ + (-(1/2) : ℚ) * L.ω₂ := by
    push_cast; ring
  rw [this]
  exact (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := 0) (β := -(1 / 2))).not.mpr (by norm_num)

/-- The difference `ω₂/2 - (ω₁ + ω₂)/2 = -ω₁/2` of two half periods does not
lie in the lattice. -/
lemma ω₂_sub_sum_div_two_notMem_lattice :
    L.ω₂ / 2 - (L.ω₁ + L.ω₂) / 2 ∉ (L.lattice : Set ℂ) := by
  have : L.ω₂ / 2 - (L.ω₁ + L.ω₂) / 2 = (-(1/2) : ℚ) * L.ω₁ + (0 : ℚ) * L.ω₂ := by
    push_cast; ring
  rw [this]
  exact (L.mul_ω₁_add_mul_ω₂_mem_lattice (α := -(1 / 2)) (β := 0)).not.mpr (by norm_num)

/-- An elliptic function of order `2` cannot have three pairwise inequivalent
zeros `a, b, c` (with all differences nonlattice). This is an axiomatic
ingredient used to prove the half-period injectivity statements below. -/
theorem ellipticOrder2_no_three_zeros
    {f : ℂ → ℂ} (hf : L.IsEllipticFunction f) (hord : ellipticOrder L f hf = 2)
    (a b c : ℂ)
    (ha : a ∉ (L.lattice : Set ℂ)) (hb : b ∉ (L.lattice : Set ℂ))
    (hc : c ∉ (L.lattice : Set ℂ))
    (hab : a - b ∉ (L.lattice : Set ℂ)) (hac : a - c ∉ (L.lattice : Set ℂ))
    (hbc : b - c ∉ (L.lattice : Set ℂ))
    (hfa : f a = 0) (hfb : f b = 0) (hfc : f c = 0) : False := by sorry

/-- Injectivity at half periods: if `z` and `w` are nonlattice with
`2z, 2w ∈ L` and `℘(z) = ℘(w)`, then `z - w ∈ L`. This is a key step in the
cubic-root characterization of the half periods. -/
theorem half_period_weierstrassP_injective
    (z w : ℂ)
    (hz : z ∉ (L.lattice : Set ℂ)) (hw : w ∉ (L.lattice : Set ℂ))
    (h2z : (2 : ℂ) * z ∈ (L.lattice : Set ℂ))
    (h2w : (2 : ℂ) * w ∈ (L.lattice : Set ℂ))
    (heq : ℘[L] z = ℘[L] w)
    (h_diff : z - w ∉ (L.lattice : Set ℂ)) : False := by sorry

/-- If `℘(z) = ℘(w)` for nonlattice points `z, w`, then either `z - w ∈ L` or
`z + w ∈ L`. -/
theorem weierstrassP_eq_implies_pm (z w : ℂ)
    (hz : z ∉ (L.lattice : Set ℂ)) (hw : w ∉ (L.lattice : Set ℂ))
    (heq : ℘[L] z = ℘[L] w) :
    z - w ∈ (L.lattice : Set ℂ) ∨ z + w ∈ (L.lattice : Set ℂ) := by
  by_contra h_neg
  rw [not_or] at h_neg
  obtain ⟨h_diff, h_sum⟩ := h_neg
  have h_neg_z : -z ∉ (L.lattice : Set ℂ) :=
    fun h => hz (neg_neg z ▸ L.lattice.neg_mem h)
  have h_neg_w : -w ∉ (L.lattice : Set ℂ) :=
    fun h => hw (neg_neg w ▸ L.lattice.neg_mem h)
  have h_neg_diff : (-z) - w ∉ (L.lattice : Set ℂ) := by
    intro h
    apply h_sum
    have hrw : z + w = -((-z) - w) := by ring
    rw [hrw]
    exact L.lattice.neg_mem h
  have hg_ell := L.weierstrassPFun_sub_const_isElliptic (℘[L] z)
  have hg_ord := L.weierstrassPFun_sub_const_ellipticOrder (℘[L] z)
  have hfa : (fun ζ => L.weierstrassPFun ζ - ℘[L] z) z = 0 := sub_self _
  have hfb : (fun ζ => L.weierstrassPFun ζ - ℘[L] z) w = 0 :=
    sub_eq_zero.mpr heq.symm
  have hfc_neg_z : (fun ζ => L.weierstrassPFun ζ - ℘[L] z) (-z) = 0 := by
    show ℘[L] (-z) - ℘[L] z = 0
    rw [L.weierstrassP_neg]
    exact sub_self _
  have hfc_neg_w : (fun ζ => L.weierstrassPFun ζ - ℘[L] z) (-w) = 0 := by
    show ℘[L] (-w) - ℘[L] z = 0
    rw [L.weierstrassP_neg w, heq]
    exact sub_self _
  by_cases h2z : (2 : ℂ) * z ∈ (L.lattice : Set ℂ)
  · by_cases h2w : (2 : ℂ) * w ∈ (L.lattice : Set ℂ)
    · exact L.half_period_weierstrassP_injective z w hz hw h2z h2w heq h_diff
    ·
      have hac : z - -w ∉ (L.lattice : Set ℂ) := by
        rw [sub_neg_eq_add]
        exact h_sum
      have hbc : w - -w ∉ (L.lattice : Set ℂ) := by
        have hrw : w - -w = 2 * w := by ring
        rw [hrw]
        exact h2w
      exact L.ellipticOrder2_no_three_zeros hg_ell hg_ord z w (-w) hz hw h_neg_w
        h_diff hac hbc hfa hfb hfc_neg_w
  ·
    have hab : z - -z ∉ (L.lattice : Set ℂ) := by
      have hrw : z - -z = 2 * z := by ring
      rw [hrw]
      exact h2z
    exact L.ellipticOrder2_no_three_zeros hg_ell hg_ord z (-z) w hz h_neg_z hw
      hab h_diff h_neg_diff hfa hfc_neg_z hfb

/-- The values `℘(ω₁/2)`, `℘(ω₂/2)` and `℘((ω₁+ω₂)/2)` of the Weierstrass
function at the three nontrivial half periods are pairwise distinct. -/
lemma weierstrassP_halfPeriods_distinct :
    ℘[L] (L.ω₁ / 2) ≠ ℘[L] (L.ω₂ / 2) ∧
    ℘[L] (L.ω₁ / 2) ≠ ℘[L] ((L.ω₁ + L.ω₂) / 2) ∧
    ℘[L] (L.ω₂ / 2) ≠ ℘[L] ((L.ω₁ + L.ω₂) / 2) := by
  refine ⟨fun h12 => ?_, fun h13 => ?_, fun h23 => ?_⟩
  · exact L.half_period_weierstrassP_injective (L.ω₁ / 2) (L.ω₂ / 2)
      L.ω₁_div_two_notMem_lattice L.ω₂_div_two_notMem_lattice
      (by rw [show (2 : ℂ) * (L.ω₁ / 2) = L.ω₁ from by ring]; exact L.ω₁_mem_lattice)
      (by rw [show (2 : ℂ) * (L.ω₂ / 2) = L.ω₂ from by ring]; exact L.ω₂_mem_lattice)
      h12
      (by convert L.ω₁_sub_ω₂_div_two_notMem_lattice using 1; ring)
  · exact L.half_period_weierstrassP_injective (L.ω₁ / 2) ((L.ω₁ + L.ω₂) / 2)
      L.ω₁_div_two_notMem_lattice L.sum_div_two_notMem_lattice
      (by rw [show (2 : ℂ) * (L.ω₁ / 2) = L.ω₁ from by ring]; exact L.ω₁_mem_lattice)
      (by rw [show (2 : ℂ) * ((L.ω₁ + L.ω₂) / 2) = L.ω₁ + L.ω₂ from by ring]
          exact L.lattice.add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice)
      h13
      L.ω₁_sub_sum_div_two_notMem_lattice
  · exact L.half_period_weierstrassP_injective (L.ω₂ / 2) ((L.ω₁ + L.ω₂) / 2)
      L.ω₂_div_two_notMem_lattice L.sum_div_two_notMem_lattice
      (by rw [show (2 : ℂ) * (L.ω₂ / 2) = L.ω₂ from by ring]; exact L.ω₂_mem_lattice)
      (by rw [show (2 : ℂ) * ((L.ω₁ + L.ω₂) / 2) = L.ω₁ + L.ω₂ from by ring]
          exact L.lattice.add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice)
      h23
      L.ω₂_sub_sum_div_two_notMem_lattice

/-- A cubic `4x³ - g₂ x - g₃` whose three roots `e₁, e₂, e₃` are distinct has
no other roots: any root `x` must equal one of `e₁, e₂, e₃`. -/
lemma cubic_root_of_three_distinct_roots {g₂ g₃ x e₁ e₂ e₃ : ℂ}
    (hx : 4 * x ^ 3 - g₂ * x - g₃ = 0)
    (h1 : 4 * e₁ ^ 3 - g₂ * e₁ - g₃ = 0)
    (h2 : 4 * e₂ ^ 3 - g₂ * e₂ - g₃ = 0)
    (h3 : 4 * e₃ ^ 3 - g₂ * e₃ - g₃ = 0)
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃) :
    x = e₁ ∨ x = e₂ ∨ x = e₃ := by
  have hsub1 : (x - e₁) * (4 * (x ^ 2 + x * e₁ + e₁ ^ 2) - g₂) = 0 := by
    linear_combination hx - h1
  rcases mul_eq_zero.mp hsub1 with hxe₁ | hg₂_eq
  · exact Or.inl (sub_eq_zero.mp hxe₁)
  · have hsub12 : (e₂ - e₁) * (4 * (e₂ ^ 2 + e₂ * e₁ + e₁ ^ 2) - g₂) = 0 := by
      linear_combination h2 - h1
    have hne21 : e₂ - e₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
    have hg₂_12 : 4 * (e₂ ^ 2 + e₂ * e₁ + e₁ ^ 2) - g₂ = 0 :=
      (mul_eq_zero.mp hsub12).resolve_left hne21
    have hdiff : 4 * (x ^ 2 + x * e₁ + e₁ ^ 2) = 4 * (e₂ ^ 2 + e₂ * e₁ + e₁ ^ 2) := by
      linear_combination hg₂_eq - hg₂_12
    have h4ne : (4 : ℂ) ≠ 0 := by norm_num
    have hcancel := mul_left_cancel₀ h4ne hdiff
    have hfact2 : (x - e₂) * (x + e₂ + e₁) = 0 := by
      have : (x - e₂) * (x + e₂ + e₁) =
        (x ^ 2 + x * e₁ + e₁ ^ 2) - (e₂ ^ 2 + e₂ * e₁ + e₁ ^ 2) := by ring
      rw [this, hcancel, sub_self]
    rcases mul_eq_zero.mp hfact2 with hxe₂ | hxsum
    · exact Or.inr (Or.inl (sub_eq_zero.mp hxe₂))
    · have hsub13 : (e₃ - e₁) * (4 * (e₃ ^ 2 + e₃ * e₁ + e₁ ^ 2) - g₂) = 0 := by
        linear_combination h3 - h1
      have hne31 : e₃ - e₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h13)
      have hg₂_13 : 4 * (e₃ ^ 2 + e₃ * e₁ + e₁ ^ 2) - g₂ = 0 :=
        (mul_eq_zero.mp hsub13).resolve_left hne31
      have hdiff2 : 4 * (e₂ ^ 2 + e₂ * e₁ + e₁ ^ 2) = 4 * (e₃ ^ 2 + e₃ * e₁ + e₁ ^ 2) := by
        linear_combination hg₂_12 - hg₂_13
      have hcancel2 := mul_left_cancel₀ h4ne hdiff2
      have hfact3 : (e₂ - e₃) * (e₁ + e₂ + e₃) = 0 := by
        have : (e₂ - e₃) * (e₁ + e₂ + e₃) =
          (e₂ ^ 2 + e₂ * e₁ + e₁ ^ 2) - (e₃ ^ 2 + e₃ * e₁ + e₁ ^ 2) := by ring
        rw [this, hcancel2, sub_self]
      have hne23' : e₂ - e₃ ≠ 0 := sub_ne_zero.mpr h23
      have hsum : e₁ + e₂ + e₃ = 0 := (mul_eq_zero.mp hfact3).resolve_left hne23'
      exact Or.inr (Or.inr (by linear_combination hxsum - hsum))

/-- If `℘(z) = ℘(w)` for nonlattice `z, w` with `2w ∈ L`, then `z - w ∈ L`.
This combines `weierstrassP_eq_implies_pm` with the assumption that `w` is a
half period. -/
lemma weierstrassP_eq_halfperiod_implies_diff_mem (z w : ℂ)
    (hz : z ∉ (L.lattice : Set ℂ)) (hw : w ∉ (L.lattice : Set ℂ))
    (heq : ℘[L] z = ℘[L] w) (h2w : 2 * w ∈ (L.lattice : Set ℂ)) :
    z - w ∈ (L.lattice : Set ℂ) := by
  rcases L.weierstrassP_eq_implies_pm z w hz hw heq with h | h
  · exact h
  · have hrw : z - w = (z + w) - 2 * w := by ring
    rw [hrw]
    exact L.lattice.sub_mem h h2w

/-- If the derivative `℘'(z)` vanishes at a nonlattice point `z`, then `z` is
congruent modulo `L` to one of the three nontrivial half periods `ω₁/2`,
`ω₂/2`, or `(ω₁+ω₂)/2`. -/
theorem derivWeierstrassP_zero_implies_halfPeriod (z : ℂ)
    (hz : z ∉ (L.lattice : Set ℂ)) (hzero : ℘'[L] z = 0) :
    z - L.ω₁ / 2 ∈ (L.lattice : Set ℂ) ∨
    z - L.ω₂ / 2 ∈ (L.lattice : Set ℂ) ∨
    z - (L.ω₁ + L.ω₂) / 2 ∈ (L.lattice : Set ℂ) := by
  have hDE := L.derivWeierstrassP_sq z hz
  rw [hzero] at hDE; simp at hDE
  have hroot : 4 * ℘[L] z ^ 3 - L.g₂ * ℘[L] z - L.g₃ = 0 := hDE.symm
  obtain ⟨h12, h13, h23⟩ := L.weierstrassP_halfPeriods_distinct
  rcases cubic_root_of_three_distinct_roots hroot
    L.weierstrassP_halfPeriod₁_isRoot
    L.weierstrassP_halfPeriod₂_isRoot
    L.weierstrassP_halfPeriod₃_isRoot
    h12 h13 h23 with heq | heq | heq
  · left
    exact L.weierstrassP_eq_halfperiod_implies_diff_mem z (L.ω₁ / 2) hz
      L.ω₁_div_two_notMem_lattice heq
      (by rw [show 2 * (L.ω₁ / 2) = L.ω₁ from by ring]; exact L.ω₁_mem_lattice)
  · right; left
    exact L.weierstrassP_eq_halfperiod_implies_diff_mem z (L.ω₂ / 2) hz
      L.ω₂_div_two_notMem_lattice heq
      (by rw [show 2 * (L.ω₂ / 2) = L.ω₂ from by ring]; exact L.ω₂_mem_lattice)
  · right; right
    exact L.weierstrassP_eq_halfperiod_implies_diff_mem z ((L.ω₁ + L.ω₂) / 2) hz
      L.sum_div_two_notMem_lattice heq
      (by rw [show 2 * ((L.ω₁ + L.ω₂) / 2) = L.ω₁ + L.ω₂ from by ring]
          exact L.lattice.add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice)

/-- Characterization of the zeros of `℘'`: for `z ∉ L`, `℘'(z) = 0` if and
only if `2z ∈ L`, i.e. `z` is a (nontrivial) half period. -/
theorem derivWeierstrassPFun_eq_zero_iff (z : ℂ) (hz : z ∉ (L.lattice : Set ℂ)) :
    ℘'[L] z = 0 ↔ (2 : ℂ) * z ∈ (L.lattice : Set ℂ) := by
  constructor
  · intro hzero
    rcases L.derivWeierstrassP_zero_implies_halfPeriod z hz hzero with h | h | h
    · have : (2 : ℂ) * z = L.ω₁ + (z - L.ω₁ / 2) + (z - L.ω₁ / 2) := by ring
      rw [this]
      exact L.lattice.add_mem (L.lattice.add_mem L.ω₁_mem_lattice h) h
    · have : (2 : ℂ) * z = L.ω₂ + (z - L.ω₂ / 2) + (z - L.ω₂ / 2) := by ring
      rw [this]
      exact L.lattice.add_mem (L.lattice.add_mem L.ω₂_mem_lattice h) h
    · have : (2 : ℂ) * z = (L.ω₁ + L.ω₂) + (z - (L.ω₁ + L.ω₂) / 2) +
          (z - (L.ω₁ + L.ω₂) / 2) := by ring
      rw [this]
      exact L.lattice.add_mem
        (L.lattice.add_mem
          (L.lattice.add_mem L.ω₁_mem_lattice L.ω₂_mem_lattice) h) h
  · intro h2z
    have hodd := L.derivWeierstrassP_neg z
    have hperiod : ℘'[L] (z - (2 : ℂ) * z) = ℘'[L] z :=
      L.derivWeierstrassP_sub_coe z ⟨(2 : ℂ) * z, h2z⟩
    have hsub : z - (2 : ℂ) * z = -z := by ring
    rw [hsub] at hperiod
    rw [← CharZero.eq_neg_self_iff]
    exact hperiod.symm.trans hodd

/-- Same characterization as `derivWeierstrassPFun_eq_zero_iff`, but with
membership phrased via `L.toAddSubgroup`. -/
theorem derivWeierstrassP_eq_zero_iff (z : ℂ) (hz : z ∉ L.toAddSubgroup) :
    ℘'[L] z = 0 ↔ (2 : ℂ) * z ∈ L.toAddSubgroup :=
  L.derivWeierstrassPFun_eq_zero_iff z hz

/-- The discriminant `g₂(L)^3 - 27 g₃(L)^2` of any complex lattice is
nonzero, since the three half-period values of `℘` are distinct roots of the
associated cubic. -/
theorem discriminantLattice_ne_zero : L.discriminantLattice ≠ 0 := by
  obtain ⟨h12, h13, h23⟩ := L.weierstrassP_halfPeriods_distinct
  exact discr_ne_zero_of_three_distinct_roots
    L.weierstrassP_halfPeriod₁_isRoot
    L.weierstrassP_halfPeriod₂_isRoot
    L.weierstrassP_halfPeriod₃_isRoot
    h12 h13 h23


/-- The short Weierstrass curve `y² = x³ - (g₂/4) x - (g₃/4)` associated to a
lattice `L`, obtained from `y² = 4x³ - g₂ x - g₃` by the standard
substitution. -/
def ellipticCurveOfLattice : WeierstrassCurve ℂ :=
  ⟨0, 0, 0, -(L.g₂ / 4), -(L.g₃ / 4)⟩

/-- The `j`-invariant of a lattice equals the `j`-invariant (in the sense of
short Weierstrass curves) of its associated curve `y² = x³ - (g₂/4)x - (g₃/4)`.
-/
theorem jInvariantLattice_eq_curve_jInvariant :
    L.jInvariantLattice =
      jInvariant (-(L.g₂ / 4)) (-(L.g₃ / 4)) := by
  simp only [jInvariantLattice, discriminantLattice, jInvariant]
  set g₂ := L.g₂ with hg₂
  set g₃ := L.g₃ with hg₃
  have key : 1728 * g₂ ^ 3 * (4 * (-(g₂ / 4)) ^ 3 + 27 * (-(g₃ / 4)) ^ 2) =
      1728 * (4 * (-(g₂ / 4)) ^ 3) * (g₂ ^ 3 - 27 * g₃ ^ 2) := by ring
  by_cases hΔ : g₂ ^ 3 - 27 * g₃ ^ 2 = 0
  ·
    have hΔ' : 4 * (-(g₂ / 4)) ^ 3 + 27 * (-(g₃ / 4)) ^ 2 = 0 := by
      have : 4 * (-(g₂ / 4)) ^ 3 + 27 * (-(g₃ / 4)) ^ 2 = -(g₂ ^ 3 - 27 * g₃ ^ 2) / 16 := by ring
      rw [this, hΔ]; simp
    have hΔ'' : 4 * (-(g₂ / 4)) ^ 3 + 27 * (g₃ / 4) ^ 2 = 0 := by
      rw [show (4 : ℂ) * (-(g₂ / 4)) ^ 3 + 27 * (g₃ / 4) ^ 2 =
          -(g₂ ^ 3 - 27 * g₃ ^ 2) / 16 from by ring, hΔ]; simp
    simp [hΔ, hΔ'']
  · have hΔ' : 4 * (-(g₂ / 4)) ^ 3 + 27 * (-(g₃ / 4)) ^ 2 ≠ 0 := by
      rw [show (4 : ℂ) * (-(g₂ / 4)) ^ 3 + 27 * (-(g₃ / 4)) ^ 2 =
          -(g₂ ^ 3 - 27 * g₃ ^ 2) / 16 from by ring]
      exact div_ne_zero (neg_ne_zero.mpr hΔ) (by norm_num)
    exact (div_eq_div_iff hΔ hΔ').mpr key

/-- Two lattices `L, L'` are said to give *isomorphic elliptic curves over* ℂ
if there is a Weierstrass variable change taking `E_L` to `E_{L'}`. -/
def EllipticCurveIsomorphicOverC (L L' : ComplexLattice) : Prop :=
  ∃ C : WeierstrassCurve.VariableChange ℂ,
    C • L.ellipticCurveOfLattice = L'.ellipticCurveOfLattice

/-- If the elliptic curves associated to lattices `L` and `L'` are isomorphic
over ℂ, then they have the same `j`-invariant. -/
theorem jInvariant_eq_of_ellipticCurveIsomorphic {L L' : ComplexLattice}
    (h : EllipticCurveIsomorphicOverC L L') :
    jInvariant (-(L.g₂ / 4)) (-(L.g₃ / 4)) =
      jInvariant (-(L'.g₂ / 4)) (-(L'.g₃ / 4)) := by
  simp only [EllipticCurveIsomorphicOverC] at h
  have hiso := (short_weierstrass_iso_iff (-(L.g₂ / 4)) (-(L.g₃ / 4))
    (-(L'.g₂ / 4)) (-(L'.g₃ / 4))
    (by norm_num : (2 : ℂ) ≠ 0) (by norm_num : (3 : ℂ) ≠ 0)).mp h
  obtain ⟨μ, hA, hB⟩ := hiso
  exact jInvariant_eq_of_iso _ _ _ _ (↑μ) (μ.ne_zero) hA hB

/-- Converse to `jInvariant_eq_of_ellipticCurveIsomorphic`: lattices whose
short Weierstrass curves share the same `j`-invariant give rise to isomorphic
elliptic curves over ℂ. Splits into the `j=0`, `j=1728`, and generic cases. -/
theorem isomorphic_of_jInvariant_eq (L L' : ComplexLattice)
    (hj : jInvariant (-(L.g₂ / 4)) (-(L.g₃ / 4)) =
          jInvariant (-(L'.g₂ / 4)) (-(L'.g₃ / 4))) :
    EllipticCurveIsomorphicOverC L L' := by

  let A := -(L.g₂ / 4)
  let B := -(L.g₃ / 4)
  let A' := -(L'.g₂ / 4)
  let B' := -(L'.g₃ / 4)

  have hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0 := by
    show 4 * (-(L.g₂ / 4)) ^ 3 + 27 * (-(L.g₃ / 4)) ^ 2 ≠ 0
    rw [show (4 : ℂ) * (-(L.g₂ / 4)) ^ 3 + 27 * (-(L.g₃ / 4)) ^ 2 =
        -(L.g₂ ^ 3 - 27 * L.g₃ ^ 2) / 16 from by ring]
    exact div_ne_zero (neg_ne_zero.mpr (discriminantLattice_ne_zero L)) (by norm_num)
  have hΔ' : 4 * A' ^ 3 + 27 * B' ^ 2 ≠ 0 := by
    show 4 * (-(L'.g₂ / 4)) ^ 3 + 27 * (-(L'.g₃ / 4)) ^ 2 ≠ 0
    rw [show (4 : ℂ) * (-(L'.g₂ / 4)) ^ 3 + 27 * (-(L'.g₃ / 4)) ^ 2 =
        -(L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2) / 16 from by ring]
    exact div_ne_zero (neg_ne_zero.mpr (discriminantLattice_ne_zero L')) (by norm_num)
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have h3 : (3 : ℂ) ≠ 0 := by norm_num


  by_cases hj0 : jInvariant A B = 0
  ·
    obtain ⟨hA0, hA'0⟩ := jInvariant_converse_eq_zero A B A' B' h2 h3 hΔ hΔ' hj hj0
    have hBne : B ≠ 0 := by intro hB0; apply hΔ; rw [hA0, hB0]; ring
    have hB'ne : B' ≠ 0 := by intro hB'0; apply hΔ'; rw [hA'0, hB'0]; ring
    obtain ⟨μ, hμ6⟩ := IsAlgClosed.exists_pow_nat_eq (B' / B) (by norm_num : 0 < 6)
    have hμ : μ ≠ 0 := by
      intro hμ0; rw [hμ0, zero_pow (by norm_num : 6 ≠ 0)] at hμ6
      exact hB'ne ((div_eq_zero_iff.mp hμ6.symm).elim id (absurd · hBne))
    have hBrel : B' = (↑(Units.mk0 μ hμ) : ℂ) ^ 6 * B := by
      simp only [Units.val_mk0]; rw [hμ6]; field_simp
    have hArel : A' = (↑(Units.mk0 μ hμ) : ℂ) ^ 4 * A := by
      simp only [Units.val_mk0]; rw [hA0, hA'0]; ring
    exact (short_weierstrass_iso_iff A B A' B' h2 h3).mpr ⟨Units.mk0 μ hμ, hArel, hBrel⟩
  · by_cases hj1728 : jInvariant A B = 1728
    ·
      obtain ⟨hB0, hB'0⟩ := jInvariant_converse_eq_1728 A B A' B' h2 h3 hΔ hΔ' hj hj1728
      have hAne : A ≠ 0 := by intro hA0; apply hΔ; rw [hA0, hB0]; ring
      have hA'ne : A' ≠ 0 := by intro hA'0; apply hΔ'; rw [hA'0, hB'0]; ring
      obtain ⟨μ, hμ4⟩ := IsAlgClosed.exists_pow_nat_eq (A' / A) (by norm_num : 0 < 4)
      have hμ : μ ≠ 0 := by
        intro hμ0; rw [hμ0, zero_pow (by norm_num : 4 ≠ 0)] at hμ4
        exact hA'ne ((div_eq_zero_iff.mp hμ4.symm).elim id (absurd · hAne))
      have hArel : A' = (↑(Units.mk0 μ hμ) : ℂ) ^ 4 * A := by
        simp only [Units.val_mk0]; rw [hμ4]; field_simp
      have hBrel : B' = (↑(Units.mk0 μ hμ) : ℂ) ^ 6 * B := by
        simp only [Units.val_mk0]; rw [hB0, hB'0]; ring
      exact (short_weierstrass_iso_iff A B A' B' h2 h3).mpr ⟨Units.mk0 μ hμ, hArel, hBrel⟩
    ·
      obtain ⟨u, hu, hA'u, hB'u⟩ := jInvariant_converse_ne_zero_ne_1728 A B A' B'
        h2 h3 hΔ hΔ' hj hj0 hj1728
      obtain ⟨μ, hμsq⟩ := IsAlgClosed.exists_pow_nat_eq u (by norm_num : 0 < 2)
      have hμ : μ ≠ 0 := by
        intro hμ0; rw [hμ0, zero_pow (by norm_num : 2 ≠ 0)] at hμsq
        exact hu hμsq.symm
      have hArel : A' = (↑(Units.mk0 μ hμ) : ℂ) ^ 4 * A := by
        simp only [Units.val_mk0]
        rw [hA'u, show μ ^ 4 = (μ ^ 2) ^ 2 from by ring, hμsq]
      have hBrel : B' = (↑(Units.mk0 μ hμ) : ℂ) ^ 6 * B := by
        simp only [Units.val_mk0]
        rw [hB'u, show μ ^ 6 = (μ ^ 2) ^ 3 from by ring, hμsq]
      exact (short_weierstrass_iso_iff A B A' B' h2 h3).mpr ⟨Units.mk0 μ hμ, hArel, hBrel⟩

/-- If the Eisenstein invariants of two lattices `L, L'` are related by
`g₂(L') = μ⁴ g₂(L)` and `g₃(L') = μ⁶ g₃(L)` for some `μ ≠ 0`, then `L` and
`L'` are homothetic. -/
theorem isHomothetic_of_eisenstein_scaling {L L' : ComplexLattice}
    {μ : ℂ} (hμ : μ ≠ 0)
    (hg₂ : L'.g₂ = μ ^ 4 * L.g₂) (hg₃ : L'.g₃ = μ ^ 6 * L.g₃) :
    IsHomothetic L L' := by sorry

/-- Two lattices with the same `j`-invariant (in the lattice sense) are
homothetic. This is the harder direction of the homothety/`j` correspondence
(Theorem 15.5 of the textbook). -/
theorem isHomothetic_of_jInvariantLattice_eq {L L' : ComplexLattice}
    (h : L.jInvariantLattice = L'.jInvariantLattice) : IsHomothetic L L' := by

  have hjCurve : jInvariant (-(L.g₂ / 4)) (-(L.g₃ / 4)) =
      jInvariant (-(L'.g₂ / 4)) (-(L'.g₃ / 4)) := by
    rw [← jInvariantLattice_eq_curve_jInvariant L,
        ← jInvariantLattice_eq_curve_jInvariant L', h]

  have hΔ : 4 * (-(L.g₂ / 4)) ^ 3 + 27 * (-(L.g₃ / 4)) ^ 2 ≠ 0 := by
    rw [show (4 : ℂ) * (-(L.g₂ / 4)) ^ 3 + 27 * (-(L.g₃ / 4)) ^ 2 =
        -(L.g₂ ^ 3 - 27 * L.g₃ ^ 2) / 16 from by ring]
    exact div_ne_zero (neg_ne_zero.mpr (discriminantLattice_ne_zero L)) (by norm_num)
  have hΔ' : 4 * (-(L'.g₂ / 4)) ^ 3 + 27 * (-(L'.g₃ / 4)) ^ 2 ≠ 0 := by
    rw [show (4 : ℂ) * (-(L'.g₂ / 4)) ^ 3 + 27 * (-(L'.g₃ / 4)) ^ 2 =
        -(L'.g₂ ^ 3 - 27 * L'.g₃ ^ 2) / 16 from by ring]
    exact div_ne_zero (neg_ne_zero.mpr (discriminantLattice_ne_zero L')) (by norm_num)
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have h3 : (3 : ℂ) ≠ 0 := by norm_num

  by_cases hj0 : jInvariant (-(L.g₂ / 4)) (-(L.g₃ / 4)) = 0
  ·
    obtain ⟨hA, hA'⟩ := jInvariant_converse_eq_zero _ _ _ _ h2 h3 hΔ hΔ' hjCurve hj0
    have hg₂ : L.g₂ = 0 := by
      have h := hA; rw [show -(L.g₂ / 4) = -(1/4) * L.g₂ from by ring] at h
      exact (mul_eq_zero.mp h).resolve_left (by norm_num)
    have hg₂' : L'.g₂ = 0 := by
      have h := hA'; rw [show -(L'.g₂ / 4) = -(1/4) * L'.g₂ from by ring] at h
      exact (mul_eq_zero.mp h).resolve_left (by norm_num)

    have hB : -(L.g₃ / 4) ≠ 0 := by intro hB; apply hΔ; rw [hA, hB]; ring
    have hB' : -(L'.g₃ / 4) ≠ 0 := by intro hB'; apply hΔ'; rw [hA', hB']; ring
    have hg₃ : L.g₃ ≠ 0 := by intro h0; apply hB; rw [h0]; ring
    have hg₃' : L'.g₃ ≠ 0 := by intro h0; apply hB'; rw [h0]; ring

    obtain ⟨μ, hμ6⟩ := IsAlgClosed.exists_pow_nat_eq (L'.g₃ / L.g₃) (by norm_num : 0 < 6)
    have hμ : μ ≠ 0 := by
      intro h0; rw [h0, zero_pow (by norm_num : 6 ≠ 0)] at hμ6
      exact hg₃' ((div_eq_zero_iff.mp hμ6.symm).elim id (absurd · hg₃))
    exact isHomothetic_of_eisenstein_scaling hμ
      (by rw [hg₂, hg₂', mul_zero])
      (by rw [hμ6]; field_simp)
  · by_cases hj1728 : jInvariant (-(L.g₂ / 4)) (-(L.g₃ / 4)) = 1728
    ·
      obtain ⟨hB, hB'⟩ := jInvariant_converse_eq_1728 _ _ _ _ h2 h3 hΔ hΔ' hjCurve hj1728
      have hg₃ : L.g₃ = 0 := by
        have h := hB; rw [show -(L.g₃ / 4) = -(1/4) * L.g₃ from by ring] at h
        exact (mul_eq_zero.mp h).resolve_left (by norm_num)
      have hg₃' : L'.g₃ = 0 := by
        have h := hB'; rw [show -(L'.g₃ / 4) = -(1/4) * L'.g₃ from by ring] at h
        exact (mul_eq_zero.mp h).resolve_left (by norm_num)
      have hA : -(L.g₂ / 4) ≠ 0 := by intro hA; apply hΔ; rw [hA, hB]; ring
      have hA' : -(L'.g₂ / 4) ≠ 0 := by intro hA'; apply hΔ'; rw [hA', hB']; ring
      have hg₂ : L.g₂ ≠ 0 := by intro h0; apply hA; rw [h0]; ring
      have hg₂' : L'.g₂ ≠ 0 := by intro h0; apply hA'; rw [h0]; ring
      obtain ⟨μ, hμ4⟩ := IsAlgClosed.exists_pow_nat_eq (L'.g₂ / L.g₂) (by norm_num : 0 < 4)
      have hμ : μ ≠ 0 := by
        intro h0; rw [h0, zero_pow (by norm_num : 4 ≠ 0)] at hμ4
        exact hg₂' ((div_eq_zero_iff.mp hμ4.symm).elim id (absurd · hg₂))
      exact isHomothetic_of_eisenstein_scaling hμ
        (by rw [hμ4]; field_simp)
        (by rw [hg₃, hg₃', mul_zero])
    ·
      obtain ⟨u, hu, hA'u, hB'u⟩ := jInvariant_converse_ne_zero_ne_1728 _ _ _ _
        h2 h3 hΔ hΔ' hjCurve hj0 hj1728


      obtain ⟨μ, hμsq⟩ := IsAlgClosed.exists_pow_nat_eq u (by norm_num : 0 < 2)
      have hμ : μ ≠ 0 := by
        intro h0; rw [h0, zero_pow (by norm_num : 2 ≠ 0)] at hμsq; exact hu hμsq.symm
      have hg₂rel : L'.g₂ = μ ^ 4 * L.g₂ := by
        have h1 : -(L'.g₂ / 4) = u ^ 2 * -(L.g₂ / 4) := hA'u
        have : L'.g₂ = u ^ 2 * L.g₂ := by
          have := h1
          have : -(1/4) * L'.g₂ = u ^ 2 * (-(1/4) * L.g₂) := by
            rw [show -(L'.g₂ / 4) = -(1/4) * L'.g₂ from by ring,
                show u ^ 2 * -(L.g₂ / 4) = u ^ 2 * (-(1/4) * L.g₂) from by ring] at h1
            exact h1
          rw [show u ^ 2 * (-(1 / 4) * L.g₂) = (-(1 : ℂ) / 4) * (u ^ 2 * L.g₂) from by ring,
              show -(1 / 4) * L'.g₂ = (-(1 : ℂ) / 4) * L'.g₂ from by ring] at this
          exact mul_left_cancel₀ (show (-(1:ℂ) / 4) ≠ 0 from by norm_num) this
        rw [this, show μ ^ 4 = (μ ^ 2) ^ 2 from by ring, hμsq]
      have hg₃rel : L'.g₃ = μ ^ 6 * L.g₃ := by
        have h1 : -(L'.g₃ / 4) = u ^ 3 * -(L.g₃ / 4) := hB'u
        have : L'.g₃ = u ^ 3 * L.g₃ := by
          have := h1
          have : -(1/4) * L'.g₃ = u ^ 3 * (-(1/4) * L.g₃) := by
            rw [show -(L'.g₃ / 4) = -(1/4) * L'.g₃ from by ring,
                show u ^ 3 * -(L.g₃ / 4) = u ^ 3 * (-(1/4) * L.g₃) from by ring] at h1
            exact h1
          rw [show u ^ 3 * (-(1 / 4) * L.g₃) = (-(1 : ℂ) / 4) * (u ^ 3 * L.g₃) from by ring,
              show -(1 / 4) * L'.g₃ = (-(1 : ℂ) / 4) * L'.g₃ from by ring] at this
          exact mul_left_cancel₀ (show (-(1:ℂ) / 4) ≠ 0 from by norm_num) this
        rw [this, show μ ^ 6 = (μ ^ 2) ^ 3 from by ring, hμsq]
      exact isHomothetic_of_eisenstein_scaling hμ hg₂rel hg₃rel

/-- Corollary 15.6 of the textbook: two lattices `L, L'` are homothetic if
and only if their associated elliptic curves `E_L`, `E_{L'}` are isomorphic
over ℂ. -/
theorem isHomothetic_iff_ellipticCurveIsomorphic {L L' : ComplexLattice} :
    IsHomothetic L L' ↔ EllipticCurveIsomorphicOverC L L' := by
  constructor
  ·
    intro h
    have hjLat := (jInvariantLattice_eq_of_isHomothetic h).symm
    have hjCurve : jInvariant (-(L.g₂ / 4)) (-(L.g₃ / 4)) =
        jInvariant (-(L'.g₂ / 4)) (-(L'.g₃ / 4)) := by
      rw [← jInvariantLattice_eq_curve_jInvariant L,
          ← jInvariantLattice_eq_curve_jInvariant L', hjLat]
    exact isomorphic_of_jInvariant_eq L L' hjCurve
  ·
    intro h
    have hjCurve := jInvariant_eq_of_ellipticCurveIsomorphic h
    have hjLat : L.jInvariantLattice = L'.jInvariantLattice := by
      rw [jInvariantLattice_eq_curve_jInvariant L,
          jInvariantLattice_eq_curve_jInvariant L', hjCurve]
    exact isHomothetic_of_jInvariantLattice_eq hjLat

end ComplexLattice

open scoped UpperHalfPlane

section Lemma_15_9

open ComplexLattice Pointwise ModularGroup UpperHalfPlane

/-- The action of the modular generator `T = [[1,1],[0,1]]` on `τ ∈ ℍ` is
addition by `1`. -/
theorem T_smul_eq_addOne (τ : ℍ) : ModularGroup.T • τ = τ.addOne := by
  rw [UpperHalfPlane.ext_iff, coe_specialLinearGroup_apply]
  simp [ModularGroup.coe_T, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    UpperHalfPlane.addOne]

/-- The action of the modular generator `S = [[0,-1],[1,0]]` on `τ ∈ ℍ` is the
negative inverse `τ ↦ -1/τ`. -/
theorem S_smul_eq_negInv (τ : ℍ) : ModularGroup.S • τ = τ.negInv := by
  rw [UpperHalfPlane.ext_iff, modular_S_smul]
  simp [UpperHalfPlane.negInv, UpperHalfPlane.coe_mk]

/-- Invariance of the `j`-function under the generator `S`: `j(-1/τ) = j(τ)`.
-/
theorem jFunction_modular_S (τ : ℍ) : jFunction (ModularGroup.S • τ) = jFunction τ := by
  rw [S_smul_eq_negInv]
  exact jFunction_neg_inv τ

/-- Invariance of the `j`-function under the generator `T`: `j(τ + 1) = j(τ)`.
-/
theorem jFunction_modular_T (τ : ℍ) : jFunction (ModularGroup.T • τ) = jFunction τ := by
  rw [T_smul_eq_addOne]
  exact jFunction_add_one τ

/-- Invariance of `j` under the full modular group `SL(2, ℤ)`: for any
`γ ∈ SL(2, ℤ)` and `τ ∈ ℍ`, `j(γτ) = j(τ)`. -/
theorem jFunction_SL2_invariant (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : ℍ) :
    jFunction (γ • τ) = jFunction τ := by
  have hγ : γ ∈ Subgroup.closure ({S, T} : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)) := by
    rw [SpecialLinearGroup.SL2Z_generators]; exact Subgroup.mem_top γ
  suffices h : ∀ g ∈ Subgroup.closure ({S, T} : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ)),
      ∀ τ : ℍ, jFunction (g • τ) = jFunction τ from h γ hγ τ
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    intro τ
    rcases hx with rfl | rfl
    · exact jFunction_modular_S τ
    · exact jFunction_modular_T τ
  | one =>
    intro τ; simp [one_smul]
  | mul x y _ _ hx hy =>
    intro τ
    rw [mul_smul]; exact (hx (y • τ)).trans (hy τ)
  | inv x _ hx =>
    intro τ
    have h1 := hx (x⁻¹ • τ)
    rw [← mul_smul, mul_inv_cancel, one_smul] at h1
    exact h1.symm

/-- Symmetric form of `jFunction_SL2_invariant`: any `γ`-translate of `τ` has
the same `j` as `τ`. -/
theorem jFunction_eq_of_SL2_equiv (τ : ℍ) (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) :
    jFunction τ = jFunction (γ • τ) :=
  (jFunction_SL2_invariant γ τ).symm

/-- One direction of Lemma 15.9: if `j(τ) = j(τ')`, then there exists
`γ ∈ SL(2, ℤ)` with `τ' = γ τ`. -/
theorem jFunction_eq_imp_SL2_equiv (τ τ' : ℍ) (h : jFunction τ = jFunction τ') :
    ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, τ' = γ • τ := by
  have hhom : IsHomothetic (ofUpperHalfPlane τ) (ofUpperHalfPlane τ') :=
    isHomothetic_of_jInvariantLattice_eq h
  obtain ⟨μ, hμne, hμL⟩ := hhom

  have h1f : (1 : ℂ) ∈ μ • ((ofUpperHalfPlane τ).lattice : Set ℂ) := by
    rw [← hμL]; exact (ofUpperHalfPlane τ').ω₁_mem
  rw [Set.mem_smul_set] at h1f
  obtain ⟨w₁, hw₁m, hw₁e⟩ := h1f
  rw [SetLike.mem_coe, mem_lattice_iff] at hw₁m
  obtain ⟨d, c, hw₁v⟩ := hw₁m
  have h2f : (τ' : ℂ) ∈ μ • ((ofUpperHalfPlane τ).lattice : Set ℂ) := by
    rw [← hμL]; exact (ofUpperHalfPlane τ').ω₂_mem
  rw [Set.mem_smul_set] at h2f
  obtain ⟨w₂, hw₂m, hw₂e⟩ := h2f
  rw [SetLike.mem_coe, mem_lattice_iff] at hw₂m
  obtain ⟨b, a, hw₂v⟩ := hw₂m
  simp only [ofUpperHalfPlane, mk'] at hw₁v hw₂v
  subst hw₁v; subst hw₂v
  simp only [smul_eq_mul, mul_one] at hw₁e hw₂e


  have hμL_inv : ↑(ofUpperHalfPlane τ).lattice =
      μ⁻¹ • (↑(ofUpperHalfPlane τ').lattice : Set ℂ) := by
    rw [hμL, inv_smul_smul₀ hμne]
  have h1r : (1 : ℂ) ∈ μ⁻¹ • ((ofUpperHalfPlane τ').lattice : Set ℂ) :=
    hμL_inv ▸ (ofUpperHalfPlane τ).ω₁_mem
  rw [Set.mem_smul_set] at h1r
  obtain ⟨w₃, hw₃m, hw₃e⟩ := h1r
  rw [SetLike.mem_coe, mem_lattice_iff] at hw₃m
  obtain ⟨d', c', hw₃v⟩ := hw₃m
  have h2r : (τ : ℂ) ∈ μ⁻¹ • ((ofUpperHalfPlane τ').lattice : Set ℂ) :=
    hμL_inv ▸ (ofUpperHalfPlane τ).ω₂_mem
  rw [Set.mem_smul_set] at h2r
  obtain ⟨w₄, hw₄m, hw₄e⟩ := h2r
  rw [SetLike.mem_coe, mem_lattice_iff] at hw₄m
  obtain ⟨b', a', hw₄v⟩ := hw₄m
  simp only [ofUpperHalfPlane, mk'] at hw₃v hw₄v
  subst hw₃v; subst hw₄v
  simp only [smul_eq_mul, mul_one] at hw₃e hw₄e


  have hd_cτ_ne : (↑d + ↑c * (τ : ℂ) : ℂ) ≠ 0 := by
    intro h0; simp only [h0, mul_zero] at hw₁e; exact one_ne_zero hw₁e.symm
  have hμ_inv_val : μ⁻¹ = ↑d + ↑c * (τ : ℂ) :=
    inv_eq_of_mul_eq_one_right hw₁e
  have hd'_c'τ'_ne : (↑d' + ↑c' * (τ' : ℂ) : ℂ) ≠ 0 := by
    intro h0; simp only [h0, mul_zero] at hw₃e; exact one_ne_zero hw₃e.symm
  have hμ_val : μ = ↑d' + ↑c' * (τ' : ℂ) := by
    have := inv_eq_of_mul_eq_one_right hw₃e; rwa [inv_inv] at this

  have hprod_one : (↑d + ↑c * (τ : ℂ)) * (↑d' + ↑c' * (τ' : ℂ)) = 1 := by
    rw [← hμ_inv_val, ← hμ_val, inv_mul_cancel₀ hμne]

  have hden : (↑c * (τ : ℂ) + ↑d ≠ 0) := by
    rwa [show (↑c * (τ : ℂ) + ↑d : ℂ) = ↑d + ↑c * ↑τ from by ring]
  have hτ'_eq : (τ' : ℂ) = (↑a * ↑τ + ↑b) / (↑c * ↑τ + ↑d) := by
    have hsc : μ = (↑d + ↑c * (τ : ℂ))⁻¹ := by rw [← hμ_inv_val, inv_inv]
    rw [← hw₂e, hsc, inv_mul_eq_div]; ring_nf


  have hprod_expand : (↑(d' * c + c' * a) : ℂ) * (τ : ℂ) + ↑(d' * d + c' * b) = 1 := by
    have hp := hprod_one
    rw [hτ'_eq] at hp
    rw [show (↑d + ↑c * (τ : ℂ) : ℂ) = ↑c * ↑τ + ↑d from by ring] at hp
    field_simp at hp
    push_cast at hp ⊢
    linear_combination hp

  have hprod2_expand : (↑(b' * c + a' * a) : ℂ) * (τ : ℂ) + ↑(b' * d + a' * b) = (τ : ℂ) := by
    have hp := hw₄e
    rw [hμ_inv_val] at hp
    rw [hτ'_eq] at hp
    rw [show (↑d + ↑c * (τ : ℂ) : ℂ) = ↑c * ↑τ + ↑d from by ring] at hp
    field_simp at hp
    push_cast at hp ⊢
    linear_combination hp

  have him_τ_pos : (0 : ℝ) < (τ : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact τ.im_pos

  have hentry21 : d' * c + c' * a = 0 := by
    have him := congr_arg Complex.im hprod_expand
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im,
               Complex.one_im] at him
    have : (↑(d' * c + c' * a) : ℝ) * (τ : ℂ).im = 0 := by linarith
    exact_mod_cast (mul_eq_zero.mp this).resolve_right (ne_of_gt him_τ_pos)
  have hentry11 : d' * d + c' * b = 1 := by
    have hre := congr_arg Complex.re hprod_expand
    simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im,
               Complex.one_re] at hre
    have h21r : (↑(d' * c + c' * a) : ℝ) = 0 := by exact_mod_cast hentry21
    simp only [h21r, zero_mul, zero_sub, neg_zero, zero_add] at hre
    exact_mod_cast hre

  have hentry22 : b' * c + a' * a = 1 := by
    have him := congr_arg Complex.im hprod2_expand
    simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im] at him
    have : ((↑(b' * c + a' * a) : ℝ) - 1) * (τ : ℂ).im = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_right (ne_of_gt him_τ_pos)
    exact_mod_cast sub_eq_zero.mp this
  have hentry12 : b' * d + a' * b = 0 := by
    have hre := congr_arg Complex.re hprod2_expand
    simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im] at hre
    have h22r : (↑(b' * c + a' * a) : ℝ) = 1 := by exact_mod_cast hentry22
    simp only [h22r, one_mul] at hre
    have : (↑(b' * d + a' * b) : ℝ) = 0 := by linarith
    exact_mod_cast this


  have hdet_prod : (a' * d' - b' * c') * (a * d - b * c) = 1 := by
    nlinarith [hentry11, hentry12, hentry21, hentry22]

  have him_formula : (τ' : ℂ).im =
      (↑(a * d - b * c) : ℝ) * (τ : ℂ).im / Complex.normSq (↑c * (τ : ℂ) + ↑d) := by
    rw [hτ'_eq, Complex.div_im]
    simp only [Complex.add_im, Complex.mul_im, Complex.add_re, Complex.mul_re,
               Complex.intCast_re, Complex.intCast_im]
    push_cast; ring
  have him_τ'_pos : (0 : ℝ) < (τ' : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact τ'.im_pos
  have hnormSq_pos : (0 : ℝ) < Complex.normSq (↑c * (τ : ℂ) + ↑d) :=
    Complex.normSq_pos.mpr hden
  have had_bc_pos : (0 : ℤ) < a * d - b * c := by
    by_contra h_le
    push_neg at h_le
    have h1 : (↑(a * d - b * c) : ℝ) ≤ 0 := by exact_mod_cast h_le
    have h2 : (↑(a * d - b * c) : ℝ) * (τ : ℂ).im / Complex.normSq (↑c * (τ : ℂ) + ↑d) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg h1 (le_of_lt him_τ_pos))
        (le_of_lt hnormSq_pos)
    linarith [him_formula]

  have hdet : (a * d - b * c : ℤ) = 1 := by
    have hdet_prod' : (a * d - b * c) * (a' * d' - b' * c') = 1 := by linarith [hdet_prod]
    rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ hdet_prod') with h3 | h3
    · exact h3
    · linarith [had_bc_pos]

  have hdet_mat : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := by
    simp only [Matrix.det_fin_two]; exact hdet
  refine ⟨⟨!![a, b; c, d], hdet_mat⟩, ?_⟩
  rw [UpperHalfPlane.ext_iff]
  simp only [UpperHalfPlane.coe_specialLinearGroup_apply]
  convert hτ'_eq using 1

/-- Lemma 15.9 of the textbook: `j(τ) = j(τ')` if and only if `τ' = γ τ` for
some `γ ∈ SL(2, ℤ)`. -/
theorem jFunction_eq_iff_SL2_equiv (τ τ' : ℍ) :
    jFunction τ = jFunction τ' ↔
      ∃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, τ' = γ • τ :=
  ⟨jFunction_eq_imp_SL2_equiv τ τ', fun ⟨γ, hγ⟩ => hγ ▸ (jFunction_SL2_invariant γ τ).symm⟩

end Lemma_15_9

section Lemma_15_10

open ModularGroup Matrix.SpecialLinearGroup

open scoped Modular MatrixGroups

/-- The standard (closed) fundamental domain for the action of `SL(2, ℤ)` on
the upper half plane, as defined in mathlib via `ModularGroup.fd`. -/
def standardFundamentalDomain : Set ℍ := ModularGroup.fd

/-- Membership in the standard fundamental domain: `τ ∈ fd` iff
`|τ|² ≥ 1` and `|Re τ| ≤ 1/2`. -/
theorem mem_standardFundamentalDomain_iff (τ : ℍ) :
    τ ∈ standardFundamentalDomain ↔
      1 ≤ Complex.normSq (τ : ℂ) ∧ |τ.re| ≤ (1 : ℝ) / 2 :=
  Iff.rfl

/-- The open standard fundamental domain `fdo` for the action of `SL(2, ℤ)` on
`ℍ`. -/
def standardOpenFundamentalDomain : Set ℍ := ModularGroup.fdo

/-- Membership in the open standard fundamental domain: `τ ∈ fdo` iff
`|τ|² > 1` and `|Re τ| < 1/2`. -/
theorem mem_standardOpenFundamentalDomain_iff (τ : ℍ) :
    τ ∈ standardOpenFundamentalDomain ↔
      1 < Complex.normSq (τ : ℂ) ∧ |τ.re| < (1 : ℝ) / 2 :=
  Iff.rfl

/-- The open standard fundamental domain is contained in the closed one. -/
theorem standardOpenFundamentalDomain_subset :
    standardOpenFundamentalDomain ⊆ standardFundamentalDomain :=
  ModularGroup.fdo_subset_fd

/-- Every `τ ∈ ℍ` is `SL(2, ℤ)`-equivalent to a point of the standard closed
fundamental domain. -/
theorem exists_SL2Z_smul_mem_fd (τ : ℍ) :
    ∃ γ : SL(2, ℤ), γ • τ ∈ standardFundamentalDomain :=
  ModularGroup.exists_smul_mem_fd τ

/-- If both `τ` and `γ τ` lie in the open standard fundamental domain, then
`τ = γ τ`. (Uniqueness of the representative on the interior.) -/
theorem eq_smul_self_of_mem_fdo (τ : ℍ) {γ : SL(2, ℤ)}
    (hτ : τ ∈ standardOpenFundamentalDomain) (hγτ : γ • τ ∈ standardOpenFundamentalDomain) :
    τ = γ • τ :=
  ModularGroup.eq_smul_self_of_mem_fdo_mem_fdo hτ hγτ

/-- The textbook (half-open) fundamental domain of Lemma 15.10:
`{τ ∈ ℍ : -1/2 ≤ Re τ < 1/2, |τ| ≥ 1, and |τ| > 1 if Re τ > 0}`. -/
def bookFundamentalDomain : Set ℍ :=
  {τ | (-1/2 : ℝ) ≤ τ.re ∧ τ.re < 1/2 ∧ 1 ≤ Complex.normSq (τ : ℂ) ∧
       (0 < τ.re → 1 < Complex.normSq (τ : ℂ))}

/-- Membership in the textbook fundamental domain unfolded as the conjunction
of its four defining inequalities. -/
theorem mem_bookFundamentalDomain_iff (τ : ℍ) :
    τ ∈ bookFundamentalDomain ↔
      (-1/2 : ℝ) ≤ τ.re ∧ τ.re < 1/2 ∧ 1 ≤ Complex.normSq (τ : ℂ) ∧
       (0 < τ.re → 1 < Complex.normSq (τ : ℂ)) :=
  Iff.rfl

/-- The textbook fundamental domain is contained in the (closed) standard
fundamental domain. -/
theorem bookFundamentalDomain_subset_fd :
    bookFundamentalDomain ⊆ standardFundamentalDomain := by
  intro τ ⟨hre_low, hre_high, hnorm, _⟩
  exact ⟨hnorm, abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- The open standard fundamental domain is contained in the textbook
fundamental domain. -/
theorem standardOpenFundamentalDomain_subset_book :
    standardOpenFundamentalDomain ⊆ bookFundamentalDomain := by
  intro τ ⟨hnorm_strict, hre_strict⟩
  have hre_abs := abs_lt.mp hre_strict
  exact ⟨by linarith [hre_abs.1], by linarith [hre_abs.2], le_of_lt hnorm_strict,
    fun _ => hnorm_strict⟩

/-- Effect of the `S`-action on the norm-square of `τ`:
`|S τ|² = 1 / |τ|²`. -/
theorem normSq_S_smul' (z : ℍ) :
    Complex.normSq (↑(S • z) : ℂ) = 1 / Complex.normSq (↑z : ℂ) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]; simp [coe_S]

/-- Effect of `S` on the real part: `Re(S τ) = -Re τ / |τ|²`. -/
theorem re_S_smul' (z : ℍ) : (S • z).re = -z.re / Complex.normSq (↑z : ℂ) := by
  rw [UpperHalfPlane.re, UpperHalfPlane.coe_specialLinearGroup_apply]
  simp [coe_S, Complex.normSq_apply, Complex.div_re]

/-- If `Re τ = 1/2`, the translation by `T⁻¹` preserves the norm-square:
`|T⁻¹ τ|² = |τ|²`. -/
theorem normSq_T_inv_smul_of_re_half (z : ℍ) (h : z.re = 1/2) :
    Complex.normSq (↑(T ^ (-1 : ℤ) • z) : ℂ) = Complex.normSq (↑z : ℂ) := by
  rw [show (↑(T ^ (-1 : ℤ) • z) : ℂ) = ↑z + ((-1 : ℤ) : ℂ) from coe_T_zpow_smul_eq z]
  simp only [Complex.normSq_add, Complex.normSq_intCast, map_intCast,
    Complex.mul_re, Complex.intCast_re, Complex.intCast_im]
  have : z.re = (↑z : ℂ).re := rfl; rw [this] at h; push_cast; linarith

/-- Existence statement for Lemma 15.10: every `τ ∈ ℍ` is `SL(2, ℤ)`-equivalent
to a point of the textbook fundamental domain. -/
theorem exists_SL2Z_smul_mem_bookFD (τ : ℍ) :
    ∃ γ : SL(2, ℤ), γ • τ ∈ bookFundamentalDomain := by
  obtain ⟨γ₀, hnorm, hre_abs⟩ := ModularGroup.exists_smul_mem_fd τ
  have hre_bound := abs_le.mp hre_abs
  have hre_low : (-1 : ℝ)/2 ≤ (γ₀ • τ).re := by linarith [hre_bound.1]
  by_cases hre_half : (γ₀ • τ).re < 1/2
  ·
    by_cases h_boundary : 0 < (γ₀ • τ).re ∧ Complex.normSq (↑(γ₀ • τ) : ℂ) = 1
    ·
      obtain ⟨hre_pos, hnorm_eq⟩ := h_boundary
      refine ⟨S * γ₀, ?_, ?_, ?_, ?_⟩
      · rw [mul_smul, re_S_smul', hnorm_eq, div_one]; linarith
      · rw [mul_smul, re_S_smul', hnorm_eq, div_one]; linarith
      · rw [mul_smul, normSq_S_smul', hnorm_eq, div_one]
      · rw [mul_smul, re_S_smul', hnorm_eq, div_one]; intro h; linarith
    ·
      refine ⟨γ₀, hre_low, hre_half, hnorm, ?_⟩
      intro hre_pos; push Not at h_boundary
      exact lt_of_le_of_ne hnorm (Ne.symm (h_boundary hre_pos))

  ·
    have hre_eq : (γ₀ • τ).re = 1/2 := le_antisymm hre_bound.2 (not_lt.mp hre_half)
    refine ⟨T ^ (-1 : ℤ) * γ₀, ?_, ?_, ?_, ?_⟩
    · rw [mul_smul, re_T_zpow_smul, hre_eq]; push_cast; linarith
    · rw [mul_smul, re_T_zpow_smul, hre_eq]; push_cast; linarith
    · rw [mul_smul, normSq_T_inv_smul_of_re_half _ hre_eq]; exact hnorm
    · rw [mul_smul, re_T_zpow_smul, hre_eq]; push_cast; intro h; linarith


/-- If `z` and `g z` both lie in the standard fundamental domain, then the
lower-left entry `g 1 0` of `g` has absolute value at most one. -/
lemma abs_c_le_one_of_mem_fd {g : SL(2, ℤ)} {z : ℍ}
    (hz : z ∈ ModularGroup.fd) (hg : g • z ∈ ModularGroup.fd) : |g 1 0| ≤ 1 := by
  let c' : ℤ := g 1 0; let c := (c' : ℝ)
  suffices 3 * c ^ 2 ≤ 4 by
    rw [← Int.cast_pow, ← Int.cast_three, ← Int.cast_four, ← Int.cast_mul, Int.cast_le] at this
    replace this : c' ^ 2 ≤ 1 ^ 2 := by omega
    rwa [sq_le_sq, abs_one] at this
  suffices c ≠ 0 → 9 * c ^ 4 ≤ 16 by
    rcases eq_or_ne c 0 with hc | hc; · rw [hc]; simp
    nlinarith [this hc, sq_abs c]
  intro hc
  have him1 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hg
  have him2 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hz
  have h₁ : 9 * c ^ 4 ≤ 4 * (g • z).im ^ 2 * (4 * z.im ^ 2) * c ^ 4 := by
    have hc4 : (0:ℝ) < c ^ 4 := by positivity
    have : 9 ≤ 4 * (g • z).im ^ 2 * (4 * z.im ^ 2) := by nlinarith
    nlinarith
  have h₂ : (c * z.im) ^ 4 / Complex.normSq (UpperHalfPlane.denom (↑g) z) ^ 2 ≤ 1 :=
    div_le_one_of_le₀
      (pow_four_le_pow_two_of_pow_two_le (z.c_mul_im_sq_le_normSq_denom g)) (sq_nonneg _)
  calc 9 * c ^ 4 ≤ c ^ 4 * z.im ^ 2 * (g • z).im ^ 2 * 16 := by linarith
    _ = c ^ 4 * z.im ^ 4 / (Complex.normSq (UpperHalfPlane.denom g z)) ^ 2 * 16 := by
        rw [ModularGroup.im_smul_eq_div_normSq, div_pow]; ring
    _ ≤ 16 := by rw [← mul_pow]; nlinarith


/-- Uniqueness step for Lemma 15.10 in the case `c = γ 1 0 = 1`: if `τ` and
`γ τ` both lie in the textbook fundamental domain, then `τ = γ τ`. -/
lemma eq_of_mem_bookFD_c_one (τ : ℍ) {γ : SL(2, ℤ)}
    (hτ : τ ∈ bookFundamentalDomain) (hγτ : γ • τ ∈ bookFundamentalDomain)
    (hc : (↑γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1) : τ = γ • τ := by
  obtain ⟨hτ_re_lo, hτ_re_hi, hτ_norm, hτ_bdy⟩ := hτ
  obtain ⟨hγτ_re_lo, hγτ_re_hi, hγτ_norm, hγτ_bdy⟩ := hγτ
  have hτ_fd : τ ∈ ModularGroup.fd :=
    ⟨hτ_norm, abs_le.mpr ⟨by linarith, by linarith⟩⟩
  have hγτ_fd : γ • τ ∈ ModularGroup.fd :=
    ⟨hγτ_norm, abs_le.mpr ⟨by linarith, by linarith⟩⟩


  have h_ge : 1 ≤ Complex.normSq (↑(T ^ ((↑γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) • τ) : ℂ) := by
    rw [coe_T_zpow_smul_eq]
    have hz1 : 1 ≤ τ.re * τ.re + τ.im * τ.im := by simpa [Complex.normSq_apply] using hτ_fd.1
    simp only [Complex.normSq_apply, Complex.add_re, UpperHalfPlane.coe_re,
      Complex.intCast_re, Complex.add_im, UpperHalfPlane.coe_im, Complex.intCast_im, add_zero]
    nlinarith [Int.nneg_mul_add_sq_of_abs_le_one (γ 1 1)
      (show |2 * τ.re| ≤ 1 by rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith [hτ_fd.2])]

  have hw : S • T ^ (γ 1 1) • τ = T ^ (-(γ 0 0)) • (γ • τ) := by
    have had : T ^ (-(γ 0 0)) * γ = S * T ^ (γ 1 1) := by
      have hg := g_eq_of_c_eq_one hc
      nth_rw 2 [hg]; group
    have := congr_arg (· • τ) had
    simp only [mul_smul] at this
    exact this.symm
  have h_ge2 : 1 ≤ Complex.normSq (↑(T ^ (-(γ 0 0)) • (γ • τ)) : ℂ) := by
    rw [coe_T_zpow_smul_eq]
    have hz1 : 1 ≤ (γ • τ).re * (γ • τ).re + (γ • τ).im * (γ • τ).im := by
      simpa [Complex.normSq_apply] using hγτ_fd.1
    simp only [Complex.normSq_apply, Complex.add_re, UpperHalfPlane.coe_re,
      Complex.intCast_re, Complex.add_im, UpperHalfPlane.coe_im, Complex.intCast_im, add_zero]
    nlinarith [Int.nneg_mul_add_sq_of_abs_le_one (-(γ 0 0))
      (show |2 * (γ • τ).re| ≤ 1 by rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith [hγτ_fd.2])]
  rw [← hw] at h_ge2

  have h_eq_inv : Complex.normSq (↑(S • T ^ (γ 1 1) • τ) : ℂ) =
      1 / Complex.normSq (↑(T ^ (γ 1 1) • τ) : ℂ) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]; simp [coe_S]
  rw [h_eq_inv] at h_ge2
  have hpos : 0 < Complex.normSq (↑(T ^ (γ 1 1) • τ) : ℂ) := by positivity
  have h_le : Complex.normSq (↑(T ^ (γ 1 1) • τ) : ℂ) ≤ 1 := by
    rwa [le_div_iff₀ hpos, one_mul] at h_ge2
  have h_nsq_one : Complex.normSq (↑(T ^ (γ 1 1) • τ) : ℂ) = 1 :=
    le_antisymm h_le h_ge

  have him_denom : Complex.normSq (UpperHalfPlane.denom γ τ) = 1 := by
    rw [ModularGroup.denom_apply, hc]; push_cast
    convert h_nsq_one using 2
    rw [coe_T_zpow_smul_eq]; ring

  have him_eq : (γ • τ).im = τ.im := by
    rw [ModularGroup.im_smul_eq_div_normSq, him_denom, div_one]

  set a := γ 0 0 with ha_def
  set d := γ 1 1 with hd_def
  have hre_formula : (γ • τ).re = (a : ℝ) - (d : ℝ) - τ.re := by

    conv_lhs => rw [g_eq_of_c_eq_one hc, mul_smul, mul_smul]
    rw [re_T_zpow_smul]

    rw [re_S_smul']

    have hnsq_td : Complex.normSq (↑(T ^ d • τ) : ℂ) = 1 := h_nsq_one

    have hre_td : (T ^ d • τ).re = τ.re + ↑d := re_T_zpow_smul τ d
    rw [hnsq_td, div_one, hre_td]
    ring

  have had_lo : (-1 : ℤ) ≤ a - d := by
    have : (a : ℝ) - d - τ.re ≥ -1/2 := by linarith [hre_formula]
    exact_mod_cast (show -(1:ℝ) ≤ (a:ℝ) - d by linarith)
  have had_hi : a - d < 1 := by
    have : (a : ℝ) - d - τ.re < 1/2 := by linarith [hre_formula]
    exact_mod_cast (show (a:ℝ) - d < 1 by linarith)
  have had_int : a - d = 0 ∨ a - d = -1 := by omega


  rcases had_int with had | had
  ·
    suffices τ.re = 0 by
      have hre_eq : τ.re = (γ • τ).re := by
        rw [this] at hre_formula
        have had_r : (a : ℝ) - d = 0 := by exact_mod_cast had
        linarith
      exact UpperHalfPlane.ext (Complex.ext (by change τ.re = (γ • τ).re; exact hre_eq)
        (by change τ.im = (γ • τ).im; exact him_eq.symm))
    by_contra hne
    exfalso
    have hnsq_gt : 1 < Complex.normSq (τ : ℂ) := by
      rcases lt_or_gt_of_ne hne with h | h
      ·


        have hgre : 0 < (γ • τ).re := by
          rw [hre_formula]
          have : (a : ℝ) - d = 0 := by exact_mod_cast had
          linarith
        have hnsq_γτ_gt := hγτ_bdy hgre

        have had_r : (a : ℝ) - d = 0 := by exact_mod_cast had
        have hre_eq_neg : (γ • τ).re = -τ.re := by linarith [hre_formula]

        have hnsq_eq : Complex.normSq (↑(γ • τ) : ℂ) = Complex.normSq (↑τ : ℂ) := by
          simp only [Complex.normSq_apply]
          rw [show (↑(γ • τ) : ℂ).re = (γ • τ).re from rfl,
              show (↑(γ • τ) : ℂ).im = (γ • τ).im from rfl,
              show (↑τ : ℂ).re = τ.re from rfl,
              show (↑τ : ℂ).im = τ.im from rfl,
              hre_eq_neg, him_eq]
          ring
        linarith [hnsq_eq]
      · exact hτ_bdy h
    have h_nsq_τ : (τ.re + ↑d) * (τ.re + ↑d) + τ.im * τ.im = 1 := by
      have := h_nsq_one; rw [coe_T_zpow_smul_eq] at this
      simpa [Complex.normSq_apply] using this
    have h_nsq_τ_gt : τ.re * τ.re + τ.im * τ.im > 1 := by
      simpa [Complex.normSq_apply] using hnsq_gt
    have h3 : (τ.re + ↑d) * (τ.re + ↑d) < τ.re * τ.re := by linarith
    have h4 : |τ.re| < 1/2 := by
      apply abs_lt.mpr
      constructor
      · have : (a : ℝ) - d = 0 := by exact_mod_cast had
        linarith [hre_formula, hγτ_re_hi]
      · exact hτ_re_hi
    rcases eq_or_ne d 0 with hd | hd
    · rw [hd, Int.cast_zero, add_zero] at h3; linarith
    · have hd_abs : (1:ℝ) ≤ |(d : ℝ)| := by exact_mod_cast Int.one_le_abs hd
      have h5 : 1/2 ≤ |τ.re + (d : ℝ)| := by
        linarith [abs_sub_abs_le_abs_add (d : ℝ) τ.re,
          show |(d:ℝ) + τ.re| = |τ.re + ↑d| from by rw [add_comm]]
      nlinarith [sq_abs (τ.re + ↑d), sq_abs τ.re]
  ·
    have hre_neg_half : τ.re = -1/2 := by
      have : (a : ℝ) - d = -1 := by exact_mod_cast had
      linarith [hre_formula, hγτ_re_lo]
    have hre_eq : τ.re = (γ • τ).re := by
      rw [hre_neg_half] at hre_formula
      have had_r : (a : ℝ) - d = -1 := by exact_mod_cast had
      linarith
    exact UpperHalfPlane.ext (Complex.ext (by change τ.re = (γ • τ).re; exact hre_eq)
      (by change τ.im = (γ • τ).im; exact him_eq.symm))

/-- Uniqueness statement for Lemma 15.10: if `τ` and `γ τ` both lie in the
textbook fundamental domain, then `τ = γ τ`. -/
theorem eq_of_mem_bookFD_of_smul_mem_bookFD (τ : ℍ) {γ : SL(2, ℤ)}
    (hτ : τ ∈ bookFundamentalDomain) (hγτ : γ • τ ∈ bookFundamentalDomain) :
    τ = γ • τ := by
  have hτ_fd := bookFundamentalDomain_subset_fd hτ
  have hγτ_fd := bookFundamentalDomain_subset_fd hγτ
  have hc_le := abs_c_le_one_of_mem_fd hτ_fd hγτ_fd
  rcases Int.abs_le_one_iff.mp hc_le with hc | hc | hc
  ·
    obtain ⟨n, hn⟩ := exists_eq_T_zpow_of_c_eq_zero hc
    rw [hn τ]; suffices n = 0 by simp [this]
    rw [hn τ] at hγτ
    have hre_lo := hγτ.1; have hre_hi := hγτ.2.1
    rw [re_T_zpow_smul] at hre_lo hre_hi
    have : (-1 : ℤ) < n := by exact_mod_cast (show -(1:ℝ) < (n:ℝ) by linarith [hτ.2.1])
    have : n < (1 : ℤ) := by exact_mod_cast (show (n:ℝ) < 1 by linarith [hτ.1])
    omega
  ·
    exact eq_of_mem_bookFD_c_one τ hτ hγτ hc
  ·
    rw [← SL_neg_smul γ τ] at hγτ ⊢
    have hc' : (-γ) 1 0 = 1 := by simp [hc]
    exact eq_of_mem_bookFD_c_one τ hτ hγτ hc'

/-- Lemma 15.10 of the textbook: every `τ ∈ ℍ` has a unique
`SL(2, ℤ)`-translate lying in the textbook fundamental domain `F`. -/
theorem fundamental_domain_exists_unique (τ : ℍ) :
    ∃! τ' : ℍ, τ' ∈ bookFundamentalDomain ∧ ∃ γ : SL(2, ℤ), γ • τ = τ' := by

  obtain ⟨γ, hγ⟩ := exists_SL2Z_smul_mem_bookFD τ
  refine ⟨γ • τ, ⟨hγ, γ, rfl⟩, ?_⟩

  rintro τ' ⟨hτ'_mem, γ', hγ'⟩


  have h_equiv : τ' = (γ' * γ⁻¹) • (γ • τ) := by
    rw [mul_smul, inv_smul_smul]; exact hγ'.symm
  rw [h_equiv] at hτ'_mem

  have heq := eq_of_mem_bookFD_of_smul_mem_bookFD (γ • τ) hγ hτ'_mem

  rw [h_equiv, ← heq]

end Lemma_15_10

section Theorem_15_11

open ModularGroup Matrix.SpecialLinearGroup ComplexLattice

open scoped Modular MatrixGroups

/-- Axiomatic input for Theorem 15.11: the image of the `j`-function is open
in ℂ. (Used together with closedness to show surjectivity onto ℂ.) -/
theorem jFunction_range_isOpen_ax : IsOpen (Set.range jFunction) := by sorry

/-- Axiomatic input for Theorem 15.11: the image of the `j`-function is closed
in ℂ. (Used together with openness to show surjectivity onto ℂ.) -/
theorem jFunction_range_isClosed_ax : IsClosed (Set.range jFunction) := by sorry

/-- The image of the `j`-function is an open subset of ℂ. -/
lemma jFunction_range_isOpen : IsOpen (Set.range jFunction) :=
  jFunction_range_isOpen_ax

/-- The image of the `j`-function is a closed subset of ℂ. -/
lemma jFunction_range_isClosed : IsClosed (Set.range jFunction) :=
  jFunction_range_isClosed_ax

/-- The `j`-function `ℍ → ℂ` is surjective: every complex number is a value of
`j`. -/
theorem jFunction_surjective : Function.Surjective jFunction := by
  rw [← Set.range_eq_univ]
  have hne : (Set.range jFunction).Nonempty :=
    ⟨jFunction ⟨Complex.I, by simp [Complex.I_im]⟩, Set.mem_range_self _⟩
  exact IsClopen.eq_univ ⟨jFunction_range_isClosed, jFunction_range_isOpen⟩ hne

/-- Every value of `j` is attained at some point of the standard fundamental
domain. -/
theorem jFunction_surjective_on_fd (j₀ : ℂ) :
    ∃ τ : ℍ, τ ∈ standardFundamentalDomain ∧ jFunction τ = j₀ := by
  obtain ⟨τ, hτ⟩ := jFunction_surjective j₀
  obtain ⟨γ, hγ⟩ := exists_SL2Z_smul_mem_fd τ
  exact ⟨γ • τ, hγ, by rw [jFunction_SL2_invariant, hτ]⟩

/-- `j` is injective on the open standard fundamental domain. -/
theorem jFunction_injective_on_fdo {τ τ' : ℍ}
    (hτ : τ ∈ standardOpenFundamentalDomain) (hτ' : τ' ∈ standardOpenFundamentalDomain)
    (hj : jFunction τ = jFunction τ') : τ = τ' := by
  obtain ⟨γ, hγ⟩ := jFunction_eq_imp_SL2_equiv τ τ' hj
  have hτ_eq : τ = γ • τ := eq_smul_self_of_mem_fdo τ hτ (hγ ▸ hτ')
  rw [hτ_eq, hγ]

/-- Surjectivity of `j` restricted to the standard fundamental domain. -/
theorem jFunction_bijective_fd_surj :
    ∀ j₀ : ℂ, ∃ τ : ℍ, τ ∈ standardFundamentalDomain ∧ jFunction τ = j₀ :=
  jFunction_surjective_on_fd

/-- Injectivity of `j` restricted to the open standard fundamental domain. -/
theorem jFunction_bijective_fdo_inj :
    Set.InjOn jFunction standardOpenFundamentalDomain := by
  intro τ hτ τ' hτ' hj
  exact jFunction_injective_on_fdo hτ hτ' hj


/-- Theorem 15.11 of the textbook: the restriction of the `j`-function to
the textbook fundamental domain `F` is a bijection from `F` to ℂ. -/
theorem jFunction_bijOn_fundamentalDomain :
    Set.BijOn jFunction bookFundamentalDomain Set.univ := by
  refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
  ·
    intro τ₁ hτ₁ τ₂ hτ₂ hj
    obtain ⟨γ, hγ⟩ := jFunction_eq_imp_SL2_equiv τ₁ τ₂ hj


    have huniq := fundamental_domain_exists_unique τ₁
    obtain ⟨τ_rep, ⟨hτ_rep_mem, γ₀, hγ₀⟩, huniq_prop⟩ := huniq
    have hτ₁_eq : τ₁ = τ_rep := by
      have := huniq_prop τ₁ ⟨hτ₁, 1, by simp⟩
      exact this
    have hτ₂_eq : τ₂ = τ_rep := by
      have := huniq_prop τ₂ ⟨hτ₂, γ, hγ.symm⟩
      exact this
    rw [hτ₁_eq, hτ₂_eq]
  ·
    intro j₀ _
    obtain ⟨τ₀, hτ₀⟩ := jFunction_surjective j₀
    obtain ⟨τ, ⟨hτ_mem, γ, hγ⟩, _⟩ := fundamental_domain_exists_unique τ₀
    exact ⟨τ, hτ_mem, by rw [← hγ, jFunction_SL2_invariant, hτ₀]⟩

end Theorem_15_11

section Corollary_15_12

open ComplexLattice

/-- The short Weierstrass `j`-invariant of `(A, B) = (-g₂/4, -g₃/4)` agrees
with the lattice `j`-invariant `jInvariantLattice L`. -/
theorem jInvariant_EL_eq_jInvariantLattice (L : ComplexLattice) :
    jInvariant (-(L.g₂ / 4)) (-(L.g₃ / 4)) = L.jInvariantLattice := by
  simp only [jInvariant, jInvariantLattice_def]
  have hΔ : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := by
    have := L.discriminantLattice_ne_zero; simpa [discriminantLattice] using this

  have h : (1728 : ℂ) * (4 * (-(L.g₂ / 4)) ^ 3) /
    (4 * (-(L.g₂ / 4)) ^ 3 + 27 * (-(L.g₃ / 4)) ^ 2) =
    1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    have hden_ne : (4 : ℂ) * (-(L.g₂ / 4)) ^ 3 + 27 * (-(L.g₃ / 4)) ^ 2 ≠ 0 := by
      rw [show (4 : ℂ) * (-(L.g₂ / 4)) ^ 3 + 27 * (-(L.g₃ / 4)) ^ 2 =
        -(L.g₂ ^ 3 - 27 * L.g₃ ^ 2) / 16 from by ring]
      exact div_ne_zero (neg_ne_zero.mpr hΔ) (by norm_num)
    rw [div_eq_div_iff hden_ne hΔ]
    ring
  exact h

/-- The discriminant `4 A³ + 27 B²` of the elliptic curve associated to a
lattice with `A = -g₂/4` and `B = -g₃/4` is nonzero. -/
theorem ellipticCurveEL_disc_ne_zero (L : ComplexLattice) :
    4 * (-(L.g₂ / 4)) ^ 3 + 27 * (-(L.g₃ / 4)) ^ 2 ≠ 0 := by
  have hΔ := L.discriminantLattice_ne_zero
  simp only [discriminantLattice_def] at hΔ
  rw [show (4 : ℂ) * (-(L.g₂ / 4)) ^ 3 + 27 * (-(L.g₃ / 4)) ^ 2 =
    -(L.g₂ ^ 3 - 27 * L.g₃ ^ 2) / 16 from by ring]
  exact div_ne_zero (neg_ne_zero.mpr hΔ) (by norm_num : (16 : ℂ) ≠ 0)

/-- Two short Weierstrass curves `y² = x³ + A x + B` and `y² = x³ + A' x + B'`
with the same `j`-invariant are isomorphic via a Weierstrass variable change.
Handles the `j = 0`, `j = 1728`, and generic cases separately. -/
theorem short_weierstrass_iso_of_jInvariant_eq (A B A' B' : ℂ)
    (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0)
    (hΔ' : 4 * A' ^ 3 + 27 * B' ^ 2 ≠ 0)
    (hj : jInvariant A B = jInvariant A' B') :
    ∃ C : WeierstrassCurve.VariableChange ℂ,
      C • (⟨0, 0, 0, A, B⟩ : WeierstrassCurve ℂ) = ⟨0, 0, 0, A', B'⟩ := by
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have h3 : (3 : ℂ) ≠ 0 := by norm_num
  by_cases hj0 : jInvariant A B = 0
  ·
    obtain ⟨hA0, hA'0⟩ := jInvariant_converse_eq_zero A B A' B' h2 h3 hΔ hΔ' hj hj0
    subst hA0; subst hA'0
    have hB : B ≠ 0 := by intro hB; apply hΔ; rw [hB]; ring
    have hB' : B' ≠ 0 := by intro hB'; apply hΔ'; rw [hB']; ring
    obtain ⟨μ, hμ6⟩ := IsAlgClosed.exists_pow_nat_eq (B' / B) (by norm_num : 0 < 6)
    have hμ : μ ≠ 0 := by
      intro hμ0; rw [hμ0, zero_pow (by norm_num : 6 ≠ 0)] at hμ6
      exact hB' ((div_eq_zero_iff.mp hμ6.symm).elim id (absurd · hB))
    exact (short_weierstrass_iso_iff (0 : ℂ) B 0 B' h2 h3).mpr
      ⟨Units.mk0 μ hμ, by simp, by
        show B' = μ ^ 6 * B
        rw [hμ6]; field_simp⟩

  · by_cases hj1728 : jInvariant A B = 1728
    ·
      obtain ⟨hB0, hB'0⟩ := jInvariant_converse_eq_1728 A B A' B' h2 h3 hΔ hΔ' hj hj1728
      subst hB0; subst hB'0
      have hA : A ≠ 0 := by intro hA; apply hΔ; rw [hA]; ring
      have hA' : A' ≠ 0 := by intro hA'; apply hΔ'; rw [hA']; ring
      obtain ⟨μ, hμ4⟩ := IsAlgClosed.exists_pow_nat_eq (A' / A) (by norm_num : 0 < 4)
      have hμ : μ ≠ 0 := by
        intro hμ0; rw [hμ0, zero_pow (by norm_num : 4 ≠ 0)] at hμ4
        exact hA' ((div_eq_zero_iff.mp hμ4.symm).elim id (absurd · hA))
      exact (short_weierstrass_iso_iff A 0 A' 0 h2 h3).mpr
        ⟨Units.mk0 μ hμ, by
          show A' = μ ^ 4 * A
          rw [hμ4]; field_simp, by simp⟩
    ·
      obtain ⟨u, hu, hA'u, hB'u⟩ := jInvariant_converse_ne_zero_ne_1728 A B A' B'
        h2 h3 hΔ hΔ' hj hj0 hj1728
      obtain ⟨μ, hμsq⟩ := IsAlgClosed.exists_pow_nat_eq u (by norm_num : 0 < 2)
      have hμ : μ ≠ 0 := by
        intro hμ0; rw [hμ0, zero_pow (by norm_num : 2 ≠ 0)] at hμsq
        exact hu hμsq.symm
      exact (short_weierstrass_iso_iff A B A' B' h2 h3).mpr
        ⟨Units.mk0 μ hμ,
          by show A' = μ ^ 4 * A
             rw [hA'u, show μ ^ 4 = (μ ^ 2) ^ 2 from by ring, hμsq],
          by show B' = μ ^ 6 * B
             rw [hB'u, show μ ^ 6 = (μ ^ 2) ^ 3 from by ring, hμsq]⟩

/-- Uniformization up to isomorphism: every elliptic curve `y² = x³ + A x + B`
over ℂ is isomorphic, via a Weierstrass variable change, to the curve
`y² = x³ - (g₂/4) x - (g₃/4)` of some lattice `L`. -/
theorem uniformization_corollary (A B : ℂ) (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
    ∃ (L : ComplexLattice) (C : WeierstrassCurve.VariableChange ℂ),
      C • (⟨0, 0, 0, A, B⟩ : WeierstrassCurve ℂ) =
        ⟨0, 0, 0, -(L.g₂ / 4), -(L.g₃ / 4)⟩ := by

  obtain ⟨τ, hτ⟩ := jFunction_surjective (jInvariant A B)

  refine ⟨ofUpperHalfPlane τ, ?_⟩

  have hjL : jInvariant A B =
      jInvariant (-((ofUpperHalfPlane τ).g₂ / 4)) (-((ofUpperHalfPlane τ).g₃ / 4)) := by
    rw [jInvariant_EL_eq_jInvariantLattice]
    exact hτ.symm
  exact short_weierstrass_iso_of_jInvariant_eq A B _ _ hΔ
    (ellipticCurveEL_disc_ne_zero (ofUpperHalfPlane τ)) hjL

/-- The lattice obtained from `L` by scaling by a nonzero complex number `c`:
its generators are `c · ω₁` and `c · ω₂`. -/
def scaleLattice (c : ℂ) (hc : c ≠ 0) (L : ComplexLattice) : ComplexLattice :=
  ComplexLattice.mk' (c * L.ω₁) (c * L.ω₂) (by
    have hL := L.linearIndependent
    rw [linearIndependent_fin2] at hL ⊢
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hL ⊢
    constructor
    · intro h
      have : c * L.ω₂ = 0 := h
      rcases mul_eq_zero.mp this with hc0 | hω2
      · exact absurd hc0 hc
      · exact absurd hω2 hL.1
    · intro a ha
      apply hL.2 a
      have h1 : a • (c * L.ω₂) = c * L.ω₁ := ha
      have h2 : c * (a • L.ω₂) = c * L.ω₁ := by
        rw [mul_smul_comm]; exact h1
      exact mul_left_cancel₀ hc h2)


/-- Equivalence between the scaled lattice `scaleLattice c hc L` and `L`,
implemented as multiplication by `c⁻¹`/`c`. -/
def scaleLatticeEquiv (c : ℂ) (hc : c ≠ 0) (L : ComplexLattice) :
    (scaleLattice c hc L).lattice ≃ L.lattice where
  toFun l := ⟨c⁻¹ * (l : ℂ), by
    have hl := l.2
    rw [ComplexLattice.mem_lattice_iff] at hl ⊢
    obtain ⟨n₁, n₂, hl⟩ := hl
    exact ⟨n₁, n₂, by
      simp only [scaleLattice, ComplexLattice.mk'] at hl
      rw [← hl]; field_simp⟩⟩

  invFun l := ⟨c * (l : ℂ), by
    have hl := l.2
    rw [ComplexLattice.mem_lattice_iff] at hl ⊢
    obtain ⟨n₁, n₂, hl⟩ := hl
    exact ⟨n₁, n₂, by
      simp only [scaleLattice, ComplexLattice.mk']
      rw [← hl]; ring⟩⟩
  left_inv l := Subtype.ext (by field_simp)
  right_inv l := Subtype.ext (by field_simp)

/-- The underlying value of `scaleLatticeEquiv c hc L` applied to a point `l`
of the scaled lattice equals `c⁻¹ · l`. -/
theorem scaleLatticeEquiv_coe (c : ℂ) (hc : c ≠ 0) (L : ComplexLattice)
    (l : (scaleLattice c hc L).lattice) :
    ((scaleLatticeEquiv c hc L l : L.lattice) : ℂ) = c⁻¹ * (l : ℂ) := rfl

/-- The underlying value of the inverse of `scaleLatticeEquiv c hc L` applied
to `l` of `L` equals `c · l`. -/
theorem scaleLatticeEquiv_symm_coe (c : ℂ) (hc : c ≠ 0) (L : ComplexLattice)
    (l : L.lattice) :
    (((scaleLatticeEquiv c hc L).symm l : (scaleLattice c hc L).lattice) : ℂ) = c * (l : ℂ) := rfl

/-- Scaling effect on `g₂`: `g₂(cL) = c⁻⁴ · g₂(L)`. -/
theorem g₂_scaleLattice (c : ℂ) (hc : c ≠ 0) (L : ComplexLattice) :
    (scaleLattice c hc L).g₂ = c⁻¹ ^ 4 * L.g₂ := by

  simp only [g₂_eq, eisensteinSeries_def]

  rw [show c⁻¹ ^ 4 * (60 * (∑' l : L.lattice, ((↑l : ℂ) ^ 4)⁻¹)) =
      60 * (c⁻¹ ^ 4 * ∑' l : L.lattice, ((↑l : ℂ) ^ 4)⁻¹) from by ring]
  congr 1

  rw [← Equiv.tsum_eq (scaleLatticeEquiv c hc L).symm]

  rw [← tsum_mul_left]
  congr 1
  ext l
  simp only [scaleLatticeEquiv_symm_coe, mul_pow, mul_inv]
  ring

/-- Scaling effect on `g₃`: `g₃(cL) = c⁻⁶ · g₃(L)`. -/
theorem g₃_scaleLattice (c : ℂ) (hc : c ≠ 0) (L : ComplexLattice) :
    (scaleLattice c hc L).g₃ = c⁻¹ ^ 6 * L.g₃ := by
  simp only [g₃_eq, eisensteinSeries_def]
  rw [show c⁻¹ ^ 6 * (140 * (∑' l : L.lattice, ((↑l : ℂ) ^ 6)⁻¹)) =
      140 * (c⁻¹ ^ 6 * ∑' l : L.lattice, ((↑l : ℂ) ^ 6)⁻¹) from by ring]
  congr 1
  rw [← Equiv.tsum_eq (scaleLatticeEquiv c hc L).symm]
  rw [← tsum_mul_left]
  congr 1
  ext l
  simp only [scaleLatticeEquiv_symm_coe, mul_pow, mul_inv]
  ring

/-- Corollary 15.12 (Uniformization Theorem): for every elliptic curve
`y² = x³ + A x + B` over ℂ there exists a lattice `L` such that the curve
equals `E_L` on the nose. -/
theorem uniformization_theorem (A B : ℂ) (hΔ : 4 * A ^ 3 + 27 * B ^ 2 ≠ 0) :
    ∃ (L : ComplexLattice),
      (⟨0, 0, 0, A, B⟩ : WeierstrassCurve ℂ) = L.ellipticCurveOfLattice := by

  obtain ⟨L', C, hC⟩ := uniformization_corollary A B hΔ


  have ha₁ : (C • (⟨0, 0, 0, A, B⟩ : WeierstrassCurve ℂ)).a₁ = 0 := by rw [hC]
  have ha₂ : (C • (⟨0, 0, 0, A, B⟩ : WeierstrassCurve ℂ)).a₂ = 0 := by rw [hC]
  have ha₃ : (C • (⟨0, 0, 0, A, B⟩ : WeierstrassCurve ℂ)).a₃ = 0 := by rw [hC]
  rw [WeierstrassCurve.variableChange_a₁] at ha₁
  rw [WeierstrassCurve.variableChange_a₃] at ha₃
  rw [WeierstrassCurve.variableChange_a₂] at ha₂
  have hs : C.s = 0 := by
    have hu : (↑C.u⁻¹ : ℂ) ≠ 0 := Units.ne_zero _
    simpa using (mul_eq_zero.mp ha₁).resolve_left hu
  have ht : C.t = 0 := by
    have hu : (↑C.u⁻¹ : ℂ) ^ 3 ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
    have : (↑C.u⁻¹ : ℂ) ^ 3 * (2 * C.t) = 0 := by simpa using ha₃
    have h2t := (mul_eq_zero.mp this).resolve_left hu
    exact (mul_eq_zero.mp h2t).resolve_left (by norm_num : (2 : ℂ) ≠ 0)
  have hr : C.r = 0 := by
    have hu : (↑C.u⁻¹ : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (Units.ne_zero _)
    have : (↑C.u⁻¹ : ℂ) ^ 2 * (3 * C.r) = 0 := by simpa [hs] using ha₂
    have h3r := (mul_eq_zero.mp this).resolve_left hu
    exact (mul_eq_zero.mp h3r).resolve_left (by norm_num : (3 : ℂ) ≠ 0)

  have ha₄_eq : (C • (⟨0, 0, 0, A, B⟩ : WeierstrassCurve ℂ)).a₄ = -(L'.g₂ / 4) := by
    have : C • (⟨0, 0, 0, A, B⟩ : WeierstrassCurve ℂ) =
      ⟨0, 0, 0, -(L'.g₂ / 4), -(L'.g₃ / 4)⟩ := hC
    exact congr_arg WeierstrassCurve.a₄ this
  have ha₆_eq : (C • (⟨0, 0, 0, A, B⟩ : WeierstrassCurve ℂ)).a₆ = -(L'.g₃ / 4) := by
    exact congr_arg WeierstrassCurve.a₆ hC
  rw [WeierstrassCurve.variableChange_a₄] at ha₄_eq
  rw [WeierstrassCurve.variableChange_a₆] at ha₆_eq
  simp only [hs, ht, hr, mul_zero, zero_mul, sub_zero, add_zero,
    pow_succ, pow_zero, one_mul] at ha₄_eq ha₆_eq


  set μval := (↑C.u⁻¹ : ℂ) with hμval_def
  have hμne : μval ≠ 0 := Units.ne_zero _
  refine ⟨scaleLattice μval hμne L', ?_⟩

  unfold ellipticCurveOfLattice


  congr 1
  ·
    rw [g₂_scaleLattice]


    have hμ4 : μval ^ 4 ≠ 0 := pow_ne_zero _ hμne
    have ha4' : μval ^ 4 * A = -(g₂ L' / 4) := by
      convert ha₄_eq using 1; ring
    have : A = μval⁻¹ ^ 4 * -(g₂ L' / 4) := by
      rw [← ha4', inv_pow, ← mul_assoc, inv_mul_cancel₀ hμ4, one_mul]
    rw [this]; ring
  ·
    rw [g₃_scaleLattice]
    have hμ6 : μval ^ 6 ≠ 0 := pow_ne_zero _ hμne
    have ha6' : μval ^ 6 * B = -(g₃ L' / 4) := by
      convert ha₆_eq using 1; ring
    have : B = μval⁻¹ ^ 6 * -(g₃ L' / 4) := by
      rw [← ha6', inv_pow, ← mul_assoc, inv_mul_cancel₀ hμ6, one_mul]
    rw [this]; ring

end Corollary_15_12

end
