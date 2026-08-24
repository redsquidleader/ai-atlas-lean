/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProbabilisticMethodsInCombinatorics.code.Janson

set_option maxHeartbeats 800000

noncomputable section

open Real

namespace Janson

/-- The expectation parameter $\mu = \mathbb{E}[X]$ in a Janson setup is nonnegative. -/
lemma JansonSetup.mu_nonneg (J : JansonSetup) : 0 ≤ J.mu :=
  Finset.sum_nonneg fun i _ => Finset.prod_nonneg fun j _ => J.prob_nonneg j

/-- The dependency parameter $\Delta = \sum_{i \sim j} \Pr(A_i \cap A_j)$ in a Janson setup
is nonnegative. -/
lemma JansonSetup.delta_nonneg (J : JansonSetup) : 0 ≤ J.delta := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact Finset.prod_nonneg fun l _ => J.prob_nonneg l
  · exact le_refl 0

/-- The probability of any particular subset $T \subseteq [N]$ being the realized set of
indicators is nonnegative. -/
lemma JansonSetup.probSubset_nonneg (J : JansonSetup) (T : Finset (Fin J.N)) :
    0 ≤ J.probSubset T := by
  unfold JansonSetup.probSubset
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun i _ => J.prob_nonneg i)
  · exact Finset.prod_nonneg (fun i _ => by linarith [J.prob_le_one i])

/-- The product-measure probabilities `J.probSubset T` form a probability distribution:
they sum to $1$ over all subsets $T \subseteq [N]$. -/
lemma JansonSetup.sum_probSubset_eq_one (J : JansonSetup) :
    ∑ T ∈ Finset.powerset Finset.univ, J.probSubset T = 1 := by
  unfold JansonSetup.probSubset
  have key := Finset.prod_add (fun i : Fin J.N => J.prob i) (fun i : Fin J.N => 1 - J.prob i)
    (Finset.univ : Finset (Fin J.N))
  simp only [add_sub_cancel] at key
  rw [Finset.prod_const_one] at key
  exact key.symm

end Janson

namespace JansonInequality

open Janson

/-- Linear upper bound: $1 - e^{-l} \leq l$. -/
lemma one_sub_exp_neg_le {l : ℝ} (_hl : 0 ≤ l) : 1 - Real.exp (-l) ≤ l := by
  linarith [add_one_le_exp (x := -l)]

/-- Nonnegativity of $1 - e^{-l}$ for $l \geq 0$. -/
lemma one_sub_exp_neg_nonneg {l : ℝ} (hl : 0 ≤ l) : 0 ≤ 1 - Real.exp (-l) := by
  linarith [Real.exp_le_one_iff.mpr (neg_nonpos.mpr hl)]

/-- Quadratic lower bound: $l - l^2/2 \leq 1 - e^{-l}$ for $l \geq 0$. -/
lemma le_one_sub_exp_neg {l : ℝ} (hl : 0 ≤ l) :
    l - l ^ 2 / 2 ≤ 1 - Real.exp (-l) := by
  suffices h : Real.exp (-l) ≤ 1 - l + l ^ 2 / 2 by linarith
  have hquad : 1 + l + l ^ 2 / 2 ≤ Real.exp l := Real.quadratic_le_exp_of_nonneg hl
  rw [Real.exp_neg]
  have hpos : 0 < 1 + l + l ^ 2 / 2 := by positivity
  have hinv_le : (Real.exp l)⁻¹ ≤ (1 + l + l ^ 2 / 2)⁻¹ := inv_anti₀ hpos hquad
  have hrhs_pos : 0 < 1 - l + l ^ 2 / 2 := by nlinarith [sq_nonneg l]
  have hfinal : (1 + l + l ^ 2 / 2)⁻¹ ≤ 1 - l + l ^ 2 / 2 := by
    rw [inv_le_comm₀ hpos hrhs_pos]
    calc (1 - l + l ^ 2 / 2)⁻¹
        = 1 / (1 - l + l ^ 2 / 2) := (one_div _).symm
      _ ≤ (1 + l + l ^ 2 / 2) := by
          rw [div_le_iff₀ hrhs_pos]
          nlinarith [sq_nonneg (l ^ 2)]
  linarith

/-- Algebraic simplification at the optimal $\lambda_0 = t/(\mu + \Delta)$:
$-\lambda_0 t + \lambda_0^2 (\mu + \Delta)/2 = -t^2/(2(\mu + \Delta))$. -/
lemma optimal_lambda_value {mu Delta t : ℝ} (hpos : 0 < mu + Delta) :
    -(t / (mu + Delta)) * t + (t / (mu + Delta)) ^ 2 * (mu + Delta) / 2 =
    -(t ^ 2 / (2 * (mu + Delta))) := by
  field_simp
  ring

/-- Intermediate Markov/MGF-style bound used in the proof of Janson III: for every
$\lambda \geq 0$,
$\Pr(X \leq \mu - t) \leq e^{\lambda(\mu - t)} \exp\!\big(-(1 - e^{-\lambda})\mu
+ (1 - e^{-\lambda})^2 \Delta / 2\big)$. -/
theorem janson_III_intermediate_bound (J : JansonSetup) (t : ℝ)
    (ht_nonneg : 0 ≤ t) (ht_le : t ≤ J.mu) :
    ∀ (l : ℝ), 0 ≤ l →
      J.probLowerTail t ≤
        Real.exp (l * (J.mu - t)) *
        Real.exp (-(1 - Real.exp (-l)) * J.mu + (1 - Real.exp (-l)) ^ 2 * J.delta / 2) := by sorry

/-- The lower-tail probability $\Pr(X \leq \mu - t)$ is bounded above by $1$, as a
probability must be. -/
theorem janson_III_prob_le_one (J : JansonSetup) (t : ℝ) :
    J.probLowerTail t ≤ 1 := by
  suffices h : J.probLowerTail t ≤ ∑ T ∈ Finset.powerset Finset.univ, J.probSubset T by
    linarith [J.sum_probSubset_eq_one]
  unfold JansonSetup.probLowerTail
  apply Finset.sum_le_sum
  intro T _
  split_ifs
  · exact le_refl _
  · exact J.probSubset_nonneg T

/-- **Janson inequality III** (Theorem 8.2.2, lower tail). For any $0 \leq t \leq \mu$,
$\Pr(X \leq \mu - t) \leq \exp\!\left(-\dfrac{t^2}{2(\mu + \Delta)}\right)$. -/
theorem janson_inequality_III (J : JansonSetup)
    (t : ℝ) (ht_nonneg : 0 ≤ t) (ht_le : t ≤ J.mu) :
    J.probLowerTail t ≤ Real.exp (-(t ^ 2 / (2 * (J.mu + J.delta)))) := by
  have h_markov_janson := janson_III_intermediate_bound J t ht_nonneg ht_le
  have hprob_le_one := janson_III_prob_le_one J t

  by_cases hmuDelta : J.mu + J.delta = 0
  ·
    have hmu0 : J.mu = 0 := by linarith [J.mu_nonneg, J.delta_nonneg]
    have ht0 : t = 0 := by linarith
    subst ht0
    simp only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_div, neg_zero, Real.exp_zero]
    exact hprob_le_one
  ·
    have hmuDelta_pos : 0 < J.mu + J.delta :=
      lt_of_le_of_ne (by linarith [J.mu_nonneg, J.delta_nonneg]) (Ne.symm hmuDelta)

    set l₀ := t / (J.mu + J.delta) with hl₀_def
    have hl₀_nonneg : 0 ≤ l₀ := div_nonneg ht_nonneg (le_of_lt hmuDelta_pos)

    have h1 := h_markov_janson l₀ hl₀_nonneg

    have h2 : J.probLowerTail t ≤
        Real.exp (l₀ * (J.mu - t) - (1 - Real.exp (-l₀)) * J.mu +
          (1 - Real.exp (-l₀)) ^ 2 * J.delta / 2) := by
      calc J.probLowerTail t
          ≤ Real.exp (l₀ * (J.mu - t)) *
            Real.exp (-(1 - Real.exp (-l₀)) * J.mu +
              (1 - Real.exp (-l₀)) ^ 2 * J.delta / 2) := h1
        _ = Real.exp (l₀ * (J.mu - t) + (-(1 - Real.exp (-l₀)) * J.mu +
            (1 - Real.exp (-l₀)) ^ 2 * J.delta / 2)) := by rw [← Real.exp_add]
        _ = Real.exp (l₀ * (J.mu - t) - (1 - Real.exp (-l₀)) * J.mu +
            (1 - Real.exp (-l₀)) ^ 2 * J.delta / 2) := by ring_nf

    suffices h_exp_le : l₀ * (J.mu - t) - (1 - Real.exp (-l₀)) * J.mu +
        (1 - Real.exp (-l₀)) ^ 2 * J.delta / 2 ≤ -(t ^ 2 / (2 * (J.mu + J.delta))) by
      calc J.probLowerTail t ≤ _ := h2
        _ ≤ Real.exp (-(t ^ 2 / (2 * (J.mu + J.delta)))) := Real.exp_le_exp.mpr h_exp_le
    set q := 1 - Real.exp (-l₀)
    have hq_le : q ≤ l₀ := one_sub_exp_neg_le hl₀_nonneg
    have hq_ge : l₀ - l₀ ^ 2 / 2 ≤ q := le_one_sub_exp_neg hl₀_nonneg
    have hq_nonneg : 0 ≤ q := one_sub_exp_neg_nonneg hl₀_nonneg

    have h_neg_q_mu : -q * J.mu ≤ -(l₀ - l₀ ^ 2 / 2) * J.mu := by
      linarith [mul_le_mul_of_nonneg_right hq_ge J.mu_nonneg]

    have h_q_sq_delta : q ^ 2 * J.delta / 2 ≤ l₀ ^ 2 * J.delta / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) < 2).le
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq_nonneg hq_le 2) J.delta_nonneg

    calc l₀ * (J.mu - t) - q * J.mu + q ^ 2 * J.delta / 2
        ≤ l₀ * (J.mu - t) - (l₀ - l₀ ^ 2 / 2) * J.mu + l₀ ^ 2 * J.delta / 2 := by linarith
      _ = -l₀ * t + l₀ ^ 2 * (J.mu + J.delta) / 2 := by ring
      _ = -(t ^ 2 / (2 * (J.mu + J.delta))) := by
          rw [hl₀_def]; exact optimal_lambda_value hmuDelta_pos

end JansonInequality
