/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Combinatorics.Enumerative.DoubleCounting

noncomputable section

open Classical Finset BigOperators

namespace TwoEnds

/-- A point in the Euclidean plane `ℝ²`, modelled as `EuclideanSpace ℝ (Fin 2)`. -/
abbrev Point := EuclideanSpace ℝ (Fin 2)

/-- The `δ`-tube around the unit-length segment `{c + t v : |t| ≤ 1/2}`:
the set of points within Euclidean distance `δ` of some point on that segment. -/
def deltaTube (c v : Point) (δ : ℝ) : Set Point :=
  { x | ∃ t : ℝ, |t| ≤ 1/2 ∧ ‖x - (c + t • v)‖ ≤ δ }

/-- `IsDeltaTube T δ` says that `T` is a `δ`-tube, i.e. it is of the form
`deltaTube c v δ` for some centre `c` and unit-length direction `v`. -/
def IsDeltaTube (T : Set Point) (δ : ℝ) : Prop :=
  ∃ (c v : Point), ‖v‖ = 1 ∧ T = deltaTube c v δ

/-- A finite set `E ⊂ B(0,1)` of `N` points is "well-spaced" (with constant
`C`) in the sense of Sharp Projection Theorems III: it lies in the unit
ball, has cardinality comparable to `N`, and every ball of radius `N^{-1/2}`
contains at most `C` points of `E`. -/
structure WellSpaced (E : Finset Point) (N : ℕ) (C : ℝ) : Prop where
  subset_unitBall : ∀ x ∈ E, ‖x‖ ≤ 1
  card_lower : (N : ℝ) ≤ C * E.card
  card_upper : (E.card : ℝ) ≤ C * N
  spacing : ∀ x : Point,
    ((E.filter (fun y => ‖y - x‖ ≤ (N : ℝ) ^ (-(1 : ℝ) / 2))).card : ℝ) ≤ C

/-- Geometric incidence fact: a pair of points `x₁, x₂` separated by at
least `δ` can lie in at most one `δ`-tube. (Two distinct `δ`-tubes through
the same `δ`-separated pair would force their directions to coincide.) -/
theorem pair_determines_tube_geometric
    (δ : ℝ) (hδ : 0 < δ)
    (tubes : Finset (Set Point))
    (h_tubes : ∀ T ∈ tubes, IsDeltaTube T δ)
    (x₁ x₂ : Point) (hsep : ‖x₁ - x₂‖ ≥ δ)
    (hx₁ : ∀ T ∈ tubes, x₁ ∈ T) (hx₂ : ∀ T ∈ tubes, x₂ ∈ T) :
    (tubes.card : ℝ) ≤ 1 := by sorry

/-- A family of `δ`-tubes `𝕋` contained in a fixed `ρ`-tube `Tρ`, each of
which contains many points of `E` and additionally satisfies the
**two-ends condition**: for each `T ∈ 𝕋` one can split its `≳ R` points
of `E ∩ T` into two clusters `H₁ T`, `H₂ T`, both of cardinality at least
`C⁻¹ R`, separated by Euclidean distance at least `δ`. This is exactly
the hypothesis of the two-ends lemma. -/
structure TubeFamily (E : Finset Point) (Tρ : Set Point) (ρ δ : ℝ) (R : ℕ) (C : ℝ) where
  hTρ_tube : IsDeltaTube Tρ ρ
  hδ_le_ρ : δ ≤ ρ
  tubes : Finset (Set Point)
  is_tube : ∀ T ∈ tubes, IsDeltaTube T δ
  subset_Tρ : ∀ T ∈ tubes, T ⊆ Tρ
  H₁ : Set Point → Finset Point
  H₂ : Set Point → Finset Point
  H₁_sub : ∀ T ∈ tubes, H₁ T ⊆ E.filter (fun x => x ∈ Tρ)
  H₂_sub : ∀ T ∈ tubes, H₂ T ⊆ E.filter (fun x => x ∈ Tρ)
  H₁_in_tube : ∀ T ∈ tubes, ∀ x ∈ H₁ T, (x : Point) ∈ T
  H₂_in_tube : ∀ T ∈ tubes, ∀ x ∈ H₂ T, (x : Point) ∈ T
  separation : ∀ T ∈ tubes,
    ∀ x ∈ H₁ T, ∀ y ∈ H₂ T, ‖(x : Point) - y‖ ≥ δ
  H₁_card : ∀ T ∈ tubes, C⁻¹ * (R : ℝ) ≤ (H₁ T).card
  H₂_card : ∀ T ∈ tubes, C⁻¹ * (R : ℝ) ≤ (H₂ T).card

/-- Combinatorial consequence of `pair_determines_tube_geometric`: a fixed
ordered pair `(x₁, x₂)` can play the role of `(H₁, H₂)` representatives for
at most one tube in the family. This is the pointwise upper bound on the
double-counting sum used in the proof of the two-ends lemma. -/
lemma pair_determines_tube_from_geometry
    (δ : ℝ) (hδ : 0 < δ)
    (tubes : Finset (Set Point))
    (is_tube : ∀ T ∈ tubes, IsDeltaTube T δ)
    (H₁ H₂ : Set Point → Finset Point)
    (H₁_in_tube : ∀ T ∈ tubes, ∀ x ∈ H₁ T, (x : Point) ∈ T)
    (H₂_in_tube : ∀ T ∈ tubes, ∀ x ∈ H₂ T, (x : Point) ∈ T)
    (separation : ∀ T ∈ tubes, ∀ x ∈ H₁ T, ∀ y ∈ H₂ T, ‖(x : Point) - y‖ ≥ δ)
    (x₁ x₂ : Point) :
    ((tubes.filter (fun T => x₁ ∈ H₁ T ∧ x₂ ∈ H₂ T)).card : ℝ) ≤ 1 := by
  set F := tubes.filter (fun T => x₁ ∈ H₁ T ∧ x₂ ∈ H₂ T)
  by_cases hF : F.Nonempty
  · obtain ⟨T₀, hT₀⟩ := hF
    have hT₀_mem : T₀ ∈ tubes := (Finset.mem_filter.mp hT₀).1
    have hT₀_prop := (Finset.mem_filter.mp hT₀).2
    have hsep : ‖x₁ - x₂‖ ≥ δ :=
      separation T₀ hT₀_mem x₁ hT₀_prop.1 x₂ hT₀_prop.2
    have h_is_tube : ∀ T ∈ F, IsDeltaTube T δ := by
      intro T hT; exact is_tube T (Finset.mem_filter.mp hT).1
    have hx₁_in : ∀ T ∈ F, x₁ ∈ T := by
      intro T hT
      exact H₁_in_tube T (Finset.mem_filter.mp hT).1 x₁ (Finset.mem_filter.mp hT).2.1
    have hx₂_in : ∀ T ∈ F, x₂ ∈ T := by
      intro T hT
      exact H₂_in_tube T (Finset.mem_filter.mp hT).1 x₂ (Finset.mem_filter.mp hT).2.2
    exact pair_determines_tube_geometric δ hδ F h_is_tube x₁ x₂ hsep hx₁_in hx₂_in
  · simp only [Finset.not_nonempty_iff_eq_empty] at hF
    rw [hF]; simp

/-- **Lemma (two ends).** Let `E` be a well-spaced set in `B¹ ⊂ ℝ²` with
`|E| ∼ N` and `|E ∩ B(x, N^{-1/2})| ≲ 1`, let `δ ≤ ρ ≤ N^{-1/2}`, and let
`Tρ` be a `ρ`-tube with `|Tρ ∩ E|_ρ ∼ R̃`. If every `δ`-tube
`T ∈ 𝕋_R(E, Tρ)` obeys the two-ends condition, then
$$\big|\mathbb{T}_R(E, T_\rho)\big| \;\lesssim\; \frac{\tilde R^{\,2}}{R^{\,2}}.$$
The proof double-counts triples `(T, x, y)` with `x ∈ H₁ T, y ∈ H₂ T`,
using `pair_determines_tube_from_geometry` for the upper bound. -/
theorem two_ends_lemma
    (E : Finset Point)
    (C : ℝ) (ρ δ : ℝ) (R R_tilde : ℕ)
    (Tρ : Set Point)
    (hC : C ≥ 1)
    (hδ : 0 < δ)
    (hR : 0 < R)
    (hTρ_upper : ((E.filter (fun x => x ∈ Tρ)).card : ℝ) ≤ C * R_tilde)
    (𝕋 : TubeFamily E Tρ ρ δ R C)
    : (𝕋.tubes.card : ℝ) ≤ C ^ 4 * (R_tilde : ℝ) ^ 2 / (R : ℝ) ^ 2 := by
  set S := E.filter (fun x => x ∈ Tρ)


  have lower : (𝕋.tubes.card : ℝ) * (C⁻¹ * R) ^ 2 ≤
      ∑ T ∈ 𝕋.tubes, ((𝕋.H₁ T).card : ℝ) * (𝕋.H₂ T).card := by
    have h_each : ∀ T ∈ 𝕋.tubes, (C⁻¹ * (R : ℝ)) ^ 2 ≤
        ((𝕋.H₁ T).card : ℝ) * (𝕋.H₂ T).card := by
      intro T hT
      have hH₁ := 𝕋.H₁_card T hT
      have hH₂ := 𝕋.H₂_card T hT
      have h_nn : (0 : ℝ) ≤ C⁻¹ * R := by positivity
      calc (C⁻¹ * (R : ℝ)) ^ 2 = (C⁻¹ * R) * (C⁻¹ * R) := by ring
        _ ≤ ((𝕋.H₁ T).card : ℝ) * (𝕋.H₂ T).card :=
            mul_le_mul hH₁ hH₂ h_nn (le_trans h_nn (by exact_mod_cast hH₁))
    calc (𝕋.tubes.card : ℝ) * (C⁻¹ * R) ^ 2
        = ∑ _T ∈ 𝕋.tubes, (C⁻¹ * (R : ℝ)) ^ 2 := by
            simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ T ∈ 𝕋.tubes, ((𝕋.H₁ T).card : ℝ) * (𝕋.H₂ T).card :=
            Finset.sum_le_sum h_each


  have upper : (∑ T ∈ 𝕋.tubes, ((𝕋.H₁ T).card : ℝ) * (𝕋.H₂ T).card) ≤
      (S.card : ℝ) ^ 2 := by

    have dc : (∑ T ∈ 𝕋.tubes, (𝕋.H₁ T ×ˢ 𝕋.H₂ T).card) =
        ∑ p ∈ S ×ˢ S, (𝕋.tubes.filter (fun T => p.1 ∈ 𝕋.H₁ T ∧ p.2 ∈ 𝕋.H₂ T)).card := by
      have key := @Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (Set Point) (Point × Point)
        (fun T p => p.1 ∈ 𝕋.H₁ T ∧ p.2 ∈ 𝕋.H₂ T) 𝕋.tubes (S ×ˢ S) _
      simp only [Finset.bipartiteAbove, Finset.bipartiteBelow] at key
      rw [← key]
      apply Finset.sum_congr rfl
      intro T hT
      congr 1
      ext ⟨x, y⟩
      simp only [Finset.mem_product, Finset.mem_filter]
      exact ⟨fun ⟨hx, hy⟩ => ⟨⟨𝕋.H₁_sub T hT hx, 𝕋.H₂_sub T hT hy⟩, hx, hy⟩,
             fun ⟨_, hx, hy⟩ => ⟨hx, hy⟩⟩

    have h_sum_eq : (∑ T ∈ 𝕋.tubes, ((𝕋.H₁ T).card : ℝ) * (𝕋.H₂ T).card) =
        ↑(∑ T ∈ 𝕋.tubes, (𝕋.H₁ T ×ˢ 𝕋.H₂ T).card) := by
      push_cast
      apply Finset.sum_congr rfl
      intro T _; rw [Finset.card_product]; push_cast; ring

    have h_pair_bound : ∀ (x₁ x₂ : Point),
        ((𝕋.tubes.filter (fun T => x₁ ∈ 𝕋.H₁ T ∧ x₂ ∈ 𝕋.H₂ T)).card : ℝ) ≤ 1 :=
      pair_determines_tube_from_geometry δ hδ 𝕋.tubes 𝕋.is_tube 𝕋.H₁ 𝕋.H₂
        𝕋.H₁_in_tube 𝕋.H₂_in_tube 𝕋.separation
    rw [h_sum_eq, dc]; push_cast
    calc (∑ p ∈ S ×ˢ S,
          ((𝕋.tubes.filter (fun T => p.1 ∈ 𝕋.H₁ T ∧ p.2 ∈ 𝕋.H₂ T)).card : ℝ))
        ≤ ∑ _p ∈ S ×ˢ S, (1 : ℝ) :=
          Finset.sum_le_sum (fun p _ => h_pair_bound p.1 p.2)
      _ = (S ×ˢ S).card := by simp [Finset.sum_const]
      _ = (S.card : ℝ) ^ 2 := by rw [Finset.card_product]; push_cast; ring


  have hR2 : (0 : ℝ) < (R : ℝ) ^ 2 := by positivity
  have hC_pos : (0 : ℝ) < C := by linarith
  have combined : (𝕋.tubes.card : ℝ) * (C⁻¹ * R) ^ 2 ≤ C ^ 2 * (R_tilde : ℝ) ^ 2 := by
    calc (𝕋.tubes.card : ℝ) * (C⁻¹ * R) ^ 2
        ≤ (S.card : ℝ) ^ 2 := le_trans lower upper
      _ ≤ (C * R_tilde) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hTρ_upper 2
      _ = C ^ 2 * (R_tilde : ℝ) ^ 2 := by ring
  have hC2_pos : (0 : ℝ) < C ^ 2 := by positivity
  have h_final : (𝕋.tubes.card : ℝ) * (R : ℝ) ^ 2 ≤ C ^ 4 * (R_tilde : ℝ) ^ 2 := by
    have key : (𝕋.tubes.card : ℝ) * (C⁻¹ * (R : ℝ)) ^ 2 * C ^ 2 ≤
        C ^ 2 * (R_tilde : ℝ) ^ 2 * C ^ 2 :=
      mul_le_mul_of_nonneg_right combined (le_of_lt hC2_pos)
    have expand : (𝕋.tubes.card : ℝ) * (C⁻¹ * (R : ℝ)) ^ 2 * C ^ 2 =
        (𝕋.tubes.card : ℝ) * (R : ℝ) ^ 2 := by field_simp
    linarith [show C ^ 2 * (↑R_tilde : ℝ) ^ 2 * C ^ 2 =
      C ^ 4 * (↑R_tilde : ℝ) ^ 2 from by ring]
  exact (le_div_iff₀ hR2).mpr h_final

end TwoEnds
