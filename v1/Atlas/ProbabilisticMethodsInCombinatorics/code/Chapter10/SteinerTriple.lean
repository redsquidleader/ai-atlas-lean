/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open MeasureTheory Filter Topology Real Set

noncomputable section

/-- A Steiner triple system on $\alpha$ (Definition 10.2.8): a collection of 3-element subsets
("triples") such that every pair of distinct elements is contained in exactly one triple. -/
structure SteinerTripleSystem (α : Type*) [DecidableEq α] where
  triples : Set (Finset α)
  triple_card : ∀ t ∈ triples, t.card = 3
  pair_in_unique_triple : ∀ (a b : α), a ≠ b →
    ∃! t, t ∈ triples ∧ a ∈ t ∧ b ∈ t

/-- Finiteness of the type of Steiner triple systems on $\{0,\dots,n-1\}$. -/
instance (n : ℕ) : Finite (SteinerTripleSystem (Fin n)) :=
  Finite.of_injective (fun s => s.triples) (fun s1 s2 h => by cases s1; cases s2; congr)

/-- The number of Steiner triple systems on $\{0,\dots,n-1\}$, denoted $\mathrm{STS}(n)$. -/
noncomputable def numSTS (n : ℕ) : ℕ :=
  Nat.card (SteinerTripleSystem (Fin n))

/-- The integral $\int_0^1 \log(t^2) \, dt = -2$. -/
lemma integral_log_sq : ∫ (t : ℝ) in (0:ℝ)..1, Real.log (t ^ 2) = -2 := by
  have h1 : ∫ (t : ℝ) in (0:ℝ)..1, Real.log (t ^ 2) =
    ∫ (t : ℝ) in (0:ℝ)..1, 2 * Real.log t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith : (0:ℝ) ≤ 1)] at ht
    simp only; rw [Real.log_pow]; norm_cast
  rw [h1, intervalIntegral.integral_const_mul, integral_log_from_zero]
  simp [Real.log_one]

/-- The sequence $n \mapsto \log\bigl(\tfrac{1}{n+4} + t^2\bigr)$ is antitone in $n$. -/
lemma antitone_log_inv_add_sq (t : ℝ) :
    Antitone (fun n : ℕ => Real.log (1/(↑n + 4 : ℝ) + t ^ 2)) := by
  intro m n hmn
  apply Real.log_le_log (by positivity)
  have h : (↑m : ℝ) + 4 ≤ (↑n : ℝ) + 4 := by exact_mod_cast Nat.add_le_add_right hmn 4
  have hm_pos : (0 : ℝ) < ↑m + 4 := by positivity
  linarith [div_le_div_of_nonneg_left (by linarith : (0:ℝ) ≤ 1) hm_pos h]

/-- Pointwise convergence: $\log\bigl(\tfrac{1}{n+4} + t^2\bigr) \to \log(t^2)$ as
$n \to \infty$, for any $t \neq 0$. -/
lemma tendsto_log_inv_add_sq {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun n : ℕ => Real.log (1/(↑n + 4 : ℝ) + t ^ 2))
    atTop (nhds (Real.log (t ^ 2))) := by
  apply Tendsto.log
  · have h1 : Tendsto (fun n : ℕ => (↑n : ℝ) + 4) atTop atTop :=
      Filter.tendsto_atTop_add_const_right _ 4 tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => 1/(↑n + 4 : ℝ)) atTop (nhds 0) := by
      simp_rw [one_div]
      exact tendsto_inv_atTop_zero.comp h1
    simpa using h2.add (tendsto_const_nhds (x := t^2))
  · exact pow_ne_zero 2 ht

/-- Integrability of $t \mapsto \log(t^2)$ on $(0,1]$. -/
lemma integrableOn_log_sq :
    IntegrableOn (fun t : ℝ => Real.log (t ^ 2)) (Ioc 0 1) volume := by
  rw [show (fun t : ℝ => Real.log (t ^ 2)) = (fun t => (2 : ℕ) * Real.log t) from by
    ext x; rw [Real.log_pow]]
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith : (0:ℝ) ≤ 1)]
  exact intervalIntegral.intervalIntegrable_of_integral_ne_zero (by
    rw [show ∫ (t : ℝ) in (0:ℝ)..1, (2 : ℕ) * Real.log t =
        (2 : ℕ) * ∫ (t : ℝ) in (0:ℝ)..1, Real.log t from
      intervalIntegral.integral_const_mul _ _]
    rw [integral_log_from_zero]; simp [Real.log_one])

/-- Integrability of $t \mapsto \log\bigl(\tfrac{1}{n+4} + t^2\bigr)$ on $(0,1]$. -/
lemma integrableOn_log_inv_add_sq (n : ℕ) :
    IntegrableOn (fun t => Real.log (1/(↑n + 4 : ℝ) + t ^ 2)) (Ioc 0 1) volume := by
  apply IntegrableOn.mono_set _ Ioc_subset_Icc_self
  apply ContinuousOn.integrableOn_compact isCompact_Icc
  apply ContinuousOn.log
  · exact continuousOn_const.add (continuous_pow 2).continuousOn
  · intro x _; positivity

/-- Convergence of integrals: $\int_0^1 \log\bigl(\tfrac{1}{n+4} + t^2\bigr) \, dt \to -2$ as
$n \to \infty$, by the monotone convergence theorem. -/
theorem tendsto_integral_log_inv_add_sq :
    Tendsto (fun n : ℕ => ∫ (t : ℝ) in (0:ℝ)..1, Real.log (1/(↑n + 4 : ℝ) + t ^ 2))
    atTop (nhds (-2)) := by
  rw [← integral_log_sq]
  simp_rw [intervalIntegral.integral_of_le (by linarith : (0:ℝ) ≤ 1)]
  apply integral_tendsto_of_tendsto_of_antitone
  · exact fun n => (integrableOn_log_inv_add_sq n).integrable
  · exact integrableOn_log_sq.integrable
  · exact ae_of_all _ (fun t => antitone_log_inv_add_sq t)
  · rw [ae_restrict_iff' measurableSet_Ioc]
    exact ae_of_all _ (fun t ht => tendsto_log_inv_add_sq (ne_of_gt ht.1))

/-- Algebraic identity: $\int_0^1 \log(1 + c t^2) \, dt = \log c + \int_0^1 \log(1/c + t^2) \, dt$
for any $c > 0$. -/
lemma integral_log_one_add_mul_sq (c : ℝ) (hc : 0 < c) :
    ∫ (t : ℝ) in (0:ℝ)..1, Real.log (1 + c * t ^ 2) =
    Real.log c + ∫ (t : ℝ) in (0:ℝ)..1, Real.log (1/c + t ^ 2) := by
  have heq : (fun t : ℝ => Real.log (1 + c * t ^ 2)) =
      (fun t => Real.log c + Real.log (1/c + t ^ 2)) := by
    ext t
    have hpos : (0 : ℝ) < 1/c + t^2 := by positivity
    rw [← Real.log_mul (ne_of_gt hc) (ne_of_gt hpos)]
    congr 1; field_simp
  rw [heq, intervalIntegral.integral_add]
  · simp [intervalIntegral.integral_const]
  · exact intervalIntegrable_const
  · apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.log
    · exact continuousOn_const.add (continuous_pow 2).continuousOn
    · intro x _; positivity

end

/-- Entropy upper bound on Steiner triple systems: for $n \ge 4$,
$\log |\mathrm{STS}(n)| \le \tfrac{n(n-1)}{6} \int_0^1 \log(1 + (n-3) t^2) \, dt$. -/
theorem entropy_bound_sts (n : ℕ) (hn : 4 ≤ n) :
    Real.log (numSTS n : ℝ) ≤
    (↑n * (↑n - 1) / 6) * ∫ (t : ℝ) in (0:ℝ)..1, Real.log (1 + (↑n - 3) * t ^ 2) := by sorry

noncomputable section

open MeasureTheory Filter Topology Real Set

/-- The Linial-Luria upper bound (Theorem 10.2.10): for every $\varepsilon > 0$, eventually
$\log |\mathrm{STS}(n)| \le \tfrac{n(n-1)}{6}(\log n - 2 + \varepsilon)$. -/
theorem sts_count_upper_bound :
    ∀ ε > 0, ∀ᶠ (n : ℕ) in atTop,
      Real.log (numSTS n : ℝ) ≤ (↑n * (↑n - 1) / 6) * (Real.log ↑n - 2 + ε) := by
  intro ε hε


  have h_conv := tendsto_integral_log_inv_add_sq
  rw [Metric.tendsto_atTop] at h_conv
  obtain ⟨N₁, hN₁⟩ := h_conv (ε / 2) (by linarith)

  filter_upwards [Filter.Ici_mem_atTop (max 7 (N₁ + 7))] with n hn
  have hn7 : 7 ≤ n := le_of_max_le_left hn
  have hnN : N₁ + 7 ≤ n := le_of_max_le_right hn
  have hn4 : 4 ≤ n := le_trans (by norm_num : 4 ≤ 7) hn7

  have h_entropy := entropy_bound_sts n hn4

  suffices h_int : ∫ (t : ℝ) in (0:ℝ)..1, Real.log (1 + (↑n - 3) * t ^ 2) ≤
      Real.log ↑n - 2 + ε by
    calc Real.log (numSTS n : ℝ)
        ≤ (↑n * (↑n - 1) / 6) * ∫ (t : ℝ) in (0:ℝ)..1, Real.log (1 + (↑n - 3) * t ^ 2) :=
          h_entropy
      _ ≤ (↑n * (↑n - 1) / 6) * (Real.log ↑n - 2 + ε) := by
          apply mul_le_mul_of_nonneg_left h_int
          apply div_nonneg _ (by norm_num : (0:ℝ) ≤ 6)
          have : (1 : ℝ) ≤ (↑n : ℝ) := by exact_mod_cast le_trans (by norm_num : 1 ≤ 4) hn4
          nlinarith [Nat.cast_nonneg (α := ℝ) n]

  have hn3_pos : (0 : ℝ) < (↑n : ℝ) - 3 := by
    have : (3 : ℝ) < ↑n := by exact_mod_cast Nat.lt_of_lt_of_le (by norm_num : 3 < 7) hn7
    linarith
  rw [integral_log_one_add_mul_sq (↑n - 3) hn3_pos]


  have h_log_bound : Real.log ((↑n : ℝ) - 3) ≤ Real.log ↑n := by
    apply Real.log_le_log (by linarith)
    linarith


  have h_reindex : (1 : ℝ) / ((↑n : ℝ) - 3) = 1 / (↑(n - 7) + 4 : ℝ) := by
    congr 1
    rw [Nat.cast_sub (by omega : 7 ≤ n)]
    ring
  have h_int_eq : ∫ (t : ℝ) in (0:ℝ)..1, Real.log (1/((↑n : ℝ) - 3) + t ^ 2) =
      ∫ (t : ℝ) in (0:ℝ)..1, Real.log (1/(↑(n - 7) + 4 : ℝ) + t ^ 2) := by
    congr 1; ext t; rw [h_reindex]
  have hm_ge : N₁ ≤ n - 7 := by omega
  have h_dist := hN₁ (n - 7) hm_ge

  rw [Real.dist_eq] at h_dist
  have h_int_bound : ∫ (t : ℝ) in (0:ℝ)..1, Real.log (1/((↑n : ℝ) - 3) + t ^ 2) ≤
      -2 + ε / 2 := by
    rw [h_int_eq]

    have := (abs_lt.mp h_dist).2
    linarith
  linarith

end
