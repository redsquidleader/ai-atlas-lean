/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic

set_option maxHeartbeats 800000

noncomputable section

open Real Finset

/-- **Probabilistic core of the Johnson–Lindenstrauss lemma.** There exists $c > 0$ such that
whenever the union-bound quantity $N^{2}\,(2\,e^{-c\varepsilon^{2}d})$ is strictly less than
$1$, any $N$-point subset $X \subseteq \mathbb{R}^m$ admits a map $f : \mathbb{R}^m \to
\mathbb{R}^d$ that preserves all pairwise distances up to a factor of $1 \pm \varepsilon$. -/
theorem jl_probabilistic_existence :
    ∃ c : ℝ, c > 0 ∧
      ∀ (m d : ℕ), 1 ≤ d →
        ∀ (ε : ℝ), ε > 0 → ε ≤ 1 →
          ∀ (N : ℕ), N ≥ 2 →
            (N : ℝ) ^ 2 * (2 * exp (-c * ε ^ 2 * ↑d)) < 1 →
              ∀ (X : Finset (EuclideanSpace ℝ (Fin m))), X.card = N →
                ∃ f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d),
                  ∀ x ∈ X, ∀ y ∈ X,
                    (1 - ε) * ‖x - y‖ ≤ ‖f x - f y‖ ∧
                    ‖f x - f y‖ ≤ (1 + ε) * ‖x - y‖ := by sorry

/-- **Johnson–Lindenstrauss map existence (intermediate form).** There exists a constant $C > 0$
such that for any $\varepsilon \in (0, 1]$, dimension $d$ with $d > C\varepsilon^{-2}\log N$, and
any $N$-point set $X \subseteq \mathbb{R}^m$, there is a map $f : \mathbb{R}^m \to \mathbb{R}^d$
with $(1 - \varepsilon)\|x - y\| \le \|f(x) - f(y)\| \le (1 + \varepsilon)\|x - y\|$ for all
$x, y \in X$. -/
theorem jl_map_existence :
    ∃ C : ℝ, C > 0 ∧
      ∀ (ε : ℝ), ε > 0 → ε ≤ 1 →
        ∀ (m d : ℕ), 1 ≤ d →
          ∀ (N : ℕ), N ≥ 2 →
            (d : ℝ) > C * ε⁻¹ ^ 2 * Real.log (N : ℝ) →
              ∀ (X : Finset (EuclideanSpace ℝ (Fin m))), X.card = N →
                ∃ f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d),
                  ∀ x ∈ X, ∀ y ∈ X,
                    (1 - ε) * ‖x - y‖ ≤ ‖f x - f y‖ ∧
                    ‖f x - f y‖ ≤ (1 + ε) * ‖x - y‖ := by
  obtain ⟨c, hc_pos, hPM⟩ := jl_probabilistic_existence


  refine ⟨4 / c, by positivity, ?_⟩
  intro ε hε hε1 m d hd N hN hd_bound X hX
  apply hPM m d hd ε hε hε1 N hN _ X hX

  have hN_pos : (0 : ℝ) < (N : ℝ) := by positivity
  have hN_ge_2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlog_pos : (0 : ℝ) < Real.log (N : ℝ) :=
    Real.log_pos (by linarith : (1 : ℝ) < (N : ℝ))

  have h_ced : c * ε ^ 2 * (d : ℝ) > 3 * Real.log (N : ℝ) := by
    have h1 : c * ε ^ 2 * (d : ℝ) > c * ε ^ 2 * (4 / c * ε⁻¹ ^ 2 * Real.log (N : ℝ)) :=
      mul_lt_mul_of_pos_left hd_bound (by positivity)
    have h2 : c * ε ^ 2 * (4 / c * ε⁻¹ ^ 2 * Real.log (N : ℝ)) = 4 * Real.log (N : ℝ) := by
      rw [inv_pow]
      rw [show c * ε ^ 2 * (4 / c * (ε ^ 2)⁻¹ * Real.log ↑N) =
          (c / c) * (ε ^ 2 * (ε ^ 2)⁻¹) * (4 * Real.log ↑N) from by ring]
      rw [div_self (ne_of_gt hc_pos), mul_inv_cancel₀ (pow_ne_zero 2 (ne_of_gt hε))]
      ring
    linarith

  have hexp3 : Real.exp (3 * Real.log (N : ℝ)) = (N : ℝ) ^ 3 := by
    have h1 : (3 : ℝ) * Real.log (N : ℝ) = ↑(3 : ℕ) * Real.log (N : ℝ) := by norm_num
    rw [h1, Real.exp_nat_mul, Real.exp_log hN_pos]
  have hexp_a_gt : Real.exp (c * ε ^ 2 * (d : ℝ)) > 2 * (N : ℝ) ^ 2 := by
    have hN3 : (N : ℝ) ^ 3 ≥ 2 * (N : ℝ) ^ 2 := by nlinarith
    have : Real.exp (c * ε ^ 2 * (d : ℝ)) > (N : ℝ) ^ 3 := by
      calc Real.exp (c * ε ^ 2 * (d : ℝ)) > Real.exp (3 * Real.log (N : ℝ)) :=
            Real.exp_strictMono h_ced
        _ = (N : ℝ) ^ 3 := hexp3
    linarith

  have hexp_neg_bound : Real.exp (-(c * ε ^ 2 * (d : ℝ))) < (2 * (N : ℝ) ^ 2)⁻¹ := by
    rw [Real.exp_neg]; exact inv_strictAnti₀ (by positivity) hexp_a_gt

  have h_neg_eq : -c * ε ^ 2 * (d : ℝ) = -(c * ε ^ 2 * (d : ℝ)) := by ring
  rw [h_neg_eq]
  have hN2_pos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have key : (N : ℝ) ^ 2 * (2 * (2 * (N : ℝ) ^ 2)⁻¹) = 1 := by
    have h : 2 * (2 * (N : ℝ) ^ 2)⁻¹ = ((N : ℝ) ^ 2)⁻¹ := by
      rw [mul_inv]; ring_nf
    rw [h, mul_inv_cancel₀ (ne_of_gt hN2_pos)]
  linarith [mul_lt_mul_of_pos_left (show 2 * Real.exp (-(c * ε ^ 2 * ↑d)) <
    2 * (2 * (N : ℝ) ^ 2)⁻¹ from by linarith) hN2_pos]

namespace JohnsonLindenstrauss

/-- **Johnson–Lindenstrauss lemma** (Theorem 9.4.22, Johnson–Lindenstrauss 1982). There exists a
constant $C > 0$ such that for every $\varepsilon > 0$, every finite set
$X \subseteq \mathbb{R}^m$ of size $N \ge 2$, and every target dimension
$d > C\varepsilon^{-2}\log N$, there is a map $f : \mathbb{R}^m \to \mathbb{R}^d$ preserving
all pairwise distances within a factor of $1 \pm \varepsilon$. -/
theorem johnson_lindenstrauss :
    ∃ C : ℝ, C > 0 ∧
      ∀ (ε : ℝ), ε > 0 →
        ∀ (m : ℕ) (N : ℕ), N ≥ 2 →
          ∀ (X : Finset (EuclideanSpace ℝ (Fin m))), X.card = N →
            ∀ (d : ℕ), (d : ℝ) > C * ε⁻¹ ^ 2 * Real.log (N : ℝ) →
              ∃ f : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d),
                ∀ x ∈ X, ∀ y ∈ X,
                  (1 - ε) * ‖x - y‖ ≤ ‖f x - f y‖ ∧
                  ‖f x - f y‖ ≤ (1 + ε) * ‖x - y‖ := by
  obtain ⟨C₀, hC₀_pos, hExist⟩ := jl_map_existence
  refine ⟨C₀, hC₀_pos, ?_⟩
  intro ε hε m N hN X hX d hd
  by_cases hε1 : ε ≤ 1
  ·


    have hd1 : 1 ≤ d := by
      by_contra h
      simp only [not_le] at h
      have hd0 : d = 0 := by omega
      subst hd0; simp at hd
      have hN_pos : (1 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hN
      have hlog_pos := Real.log_pos hN_pos
      linarith [mul_pos (mul_pos hC₀_pos (show (0:ℝ) < (ε ^ 2)⁻¹ from by positivity)) hlog_pos]
    exact hExist ε hε hε1 m d hd1 N hN hd X hX
  ·
    simp only [not_le] at hε1
    refine ⟨fun _ => 0, ?_⟩
    intro x _ y _
    simp only [sub_self, norm_zero]
    constructor
    · nlinarith [norm_nonneg (x - y)]
    · nlinarith [norm_nonneg (x - y)]

end JohnsonLindenstrauss

end
