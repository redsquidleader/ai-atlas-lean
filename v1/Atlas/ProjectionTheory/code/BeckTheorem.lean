/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open scoped Classical
open Finset AffineSubspace

namespace BeckTheorem

/-- An affine subspace `L ⊆ ℝ²` is a line iff its direction has dimension 1. -/
def IsLine (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : Prop :=
  Module.finrank ℝ L.direction = 1

/-- The number of points of the finite set `E ⊂ ℝ²` lying on the line `L`. -/
noncomputable def pointsOnLine (E : Finset (EuclideanSpace ℝ (Fin 2)))
    (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (E.filter (· ∈ (L : Set (EuclideanSpace ℝ (Fin 2))))).card

/-- The set of lines determined by `E`: lines that contain at least two points of `E`. -/
def determinedLines (E : Finset (EuclideanSpace ℝ (Fin 2))) :
    Set (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) :=
  {L | IsLine L ∧ 2 ≤ pointsOnLine E L}

/-- The set of lines through `x ∈ ℝ²` which are determined by `E`, i.e. pass through
`x` and at least one other point of `E`. -/
noncomputable def linesThrough (E : Finset (EuclideanSpace ℝ (Fin 2)))
    (x : EuclideanSpace ℝ (Fin 2)) :
    Set (AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2))) :=
  {L | IsLine L ∧ x ∈ (L : Set (EuclideanSpace ℝ (Fin 2))) ∧ 2 ≤ pointsOnLine E L}


/-- **Beck's theorem (1982).** There exists `c > 0` such that for every finite point
set `E ⊂ ℝ²`, either some line contains at least `|E|/100` points of `E`, or `E`
determines at least `c · |E|²` distinct lines. -/
theorem beck_theorem :
    ∃ c : ℝ, 0 < c ∧ ∀ (E : Finset (EuclideanSpace ℝ (Fin 2))),
      (∃ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
        IsLine L ∧ (E.card : ℝ) / 100 ≤ (pointsOnLine E L : ℝ)) ∨
      (c * (E.card : ℝ) ^ 2 ≤ (Set.ncard (determinedLines E) : ℝ)) := by sorry


/-- Per-point uniformization of the Szemerédi–Trotter consequence of Beck: if no
line contains more than `|E|/2` points and `E` determines `≥ c |E|²` lines, then
through every point of `E` there pass `≳ |E|` determined lines. -/
theorem st_uniformization_per_point (c : ℝ) (hc : 0 < c) :
    ∃ c' : ℝ, 0 < c' ∧ ∀ (E : Finset (EuclideanSpace ℝ (Fin 2))),
      (∀ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
        IsLine L → (pointsOnLine E L : ℝ) ≤ E.card / 2) →
      c * (E.card : ℝ) ^ 2 ≤ (Set.ncard (determinedLines E) : ℝ) →
      ∀ x ∈ E, c' * (E.card : ℝ) ≤ (Set.ncard (linesThrough E x) : ℝ) := by sorry


/-- If no line contains more than `|E|/2` points yet some line `L` contains at least
`|E|/100` points, then every `x ∈ E` has at least `|E|/100` lines through it
determined by `E` (using the rich line `L` to construct many such lines through `x`). -/
theorem lines_per_point_from_rich_line
    (E : Finset (EuclideanSpace ℝ (Fin 2)))
    (hconc : ∀ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
      IsLine L → (pointsOnLine E L : ℝ) ≤ E.card / 2)
    (L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)))
    (hL_line : IsLine L)
    (hL_rich : (E.card : ℝ) / 100 ≤ (pointsOnLine E L : ℝ))
    (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ E) :
    (1 : ℝ) / 100 * (E.card : ℝ) ≤ (Set.ncard (linesThrough E x) : ℝ) := by sorry

/-- **Beck's theorem, per-point form.** There is `c > 0` such that for any finite
`E ⊂ ℝ²` with no line containing more than `|E|/2` points, every point `x ∈ E` has
at least `c · |E|` lines through it that are determined by `E` (i.e. pass through `x`
and another point of `E`). -/
theorem beck_theorem_lines_per_point :
    ∃ c : ℝ, 0 < c ∧ ∀ (E : Finset (EuclideanSpace ℝ (Fin 2))),
      (∀ L : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 2)),
        IsLine L → (pointsOnLine E L : ℝ) ≤ E.card / 2) →
      ∀ x ∈ E, c * (E.card : ℝ) ≤ (Set.ncard (linesThrough E x) : ℝ) := by

  obtain ⟨c₁, hc₁_pos, hbeck⟩ := beck_theorem

  obtain ⟨c₂, hc₂_pos, hunif⟩ := st_uniformization_per_point c₁ hc₁_pos

  refine ⟨min (1 / 100) c₂, lt_min (by norm_num : (0:ℝ) < 1/100) hc₂_pos,
    fun E hconc x hx => ?_⟩

  rcases hbeck E with ⟨L, hL_line, hL_rich⟩ | hL_many
  ·

    have h := lines_per_point_from_rich_line E hconc L hL_line hL_rich x hx

    have hmin : min (1 / 100 : ℝ) c₂ ≤ 1 / 100 := min_le_left _ _
    have hE_nn : (0 : ℝ) ≤ (E.card : ℝ) := Nat.cast_nonneg' _
    linarith [mul_le_mul_of_nonneg_right hmin hE_nn]
  ·

    have h := hunif E hconc hL_many x hx

    have hmin : min (1 / 100 : ℝ) c₂ ≤ c₂ := min_le_right _ _
    have hE_nn : (0 : ℝ) ≤ (E.card : ℝ) := Nat.cast_nonneg' _
    linarith [mul_le_mul_of_nonneg_right hmin hE_nn]

end BeckTheorem
