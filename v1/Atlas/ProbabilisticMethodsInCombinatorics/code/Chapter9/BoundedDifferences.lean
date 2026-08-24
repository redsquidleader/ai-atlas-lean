/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Martingale.Basic
set_option maxHeartbeats 800000

namespace BoundedDifferences

open MeasureTheory ProbabilityTheory Real Finset Function
open scoped NNReal ENNReal

/-- The function $f$ has bounded differences with coefficients $c_i$: changing the $i$-th
coordinate of the input changes $f$ by at most $c_i$ in absolute value. -/
def HasBoundedDifferences {n : ℕ} {α : Fin n → Type*} [∀ i, DecidableEq (α i)]
    (f : (∀ i, α i) → ℝ) (c : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, ∀ x : (∀ i, α i), ∀ y : α i,
    |f x - f (Function.update x i y)| ≤ c i

/-- Lift a function `Fin n → ℝ` to a function `ℕ → ℝ` by extending with zeros for indices ≥ $n$. -/
noncomputable def liftToNat {n : ℕ} (c : Fin n → ℝ) : ℕ → ℝ :=
  fun i => if h : i < n then c ⟨i, h⟩ else 0

/-- The nat-lifted version of a nonnegative `Fin n`-indexed function is nonnegative. -/
lemma liftToNat_nonneg {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) :
    ∀ i, 0 ≤ liftToNat c i := by
  intro i; simp only [liftToNat]; split_ifs with h
  · exact hc ⟨i, h⟩
  · linarith

/-- The Hoeffding sub-Gaussian parameter $c^2/4$ associated with a bounded random variable
of range $c$, packaged as a nonnegative real. -/
noncomputable def hoeffdingParam (c : ℝ) (_hc : 0 ≤ c) : ℝ≥0 :=
  ⟨c ^ 2 / 4, by positivity⟩

/-- The sum of Hoeffding parameters $\sum_{i<n} c_i^2/4$ equals $(\sum_i c_i^2)/4$. -/
lemma sum_hoeffdingParam_eq {n : ℕ} (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i) :
    (↑(∑ i ∈ range n,
      hoeffdingParam (liftToNat c i) (liftToNat_nonneg c hc i)) : ℝ) =
    (∑ i : Fin n, c i ^ 2) / 4 := by
  rw [NNReal.coe_sum]
  simp only [hoeffdingParam, NNReal.coe_mk]
  rw [Finset.sum_div, ← Fin.sum_univ_eq_sum_range]
  congr 1; ext ⟨i, hi⟩; simp [liftToNat, hi]

/-- The Doob martingale construction for a bounded-differences function: given independent
$X_i$ and $f$ with bounded differences $c_i$, the martingale differences $Y_i$ satisfy
$\sum_i Y_i = f(X) - \mathbb{E}[f(X)]$ and each $Y_{i+1}$ is conditionally sub-Gaussian
with parameter $c_{i+1}^2/4$ given $\mathcal{F}_i$. -/
theorem doob_martingale_from_bounded_differences
    {n : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [StandardBorelSpace Ω]
    {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)] [∀ i, DecidableEq (α i)]
    (X : ∀ i, Ω → α i) (hX_indep : iIndepFun X μ)
    (f : (∀ i, α i) → ℝ) (hf_meas : Measurable (fun ω => f (fun i => X i ω)))
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hbd : HasBoundedDifferences f c) :
    ∃ (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ),
      (∀ ω, ∑ i ∈ range n, Y i ω = f (fun i => X i ω) - ∫ ω', f (fun i => X i ω') ∂μ) ∧
      StronglyAdapted ℱ Y ∧
      HasSubgaussianMGF (Y 0) (hoeffdingParam (liftToNat c 0) (liftToNat_nonneg c hc 0)) μ ∧
      (∀ i, i < n - 1 →
        HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1))
          (hoeffdingParam (liftToNat c (i + 1)) (liftToNat_nonneg c hc (i + 1))) μ) := by sorry

/-- Upper-tail bounded differences inequality (Theorem 9.1.3): if $f$ has bounded differences
$c_i$ on independent coordinates $X_1, \dots, X_n$, then
$\mathbb{P}(f(X) - \mathbb{E}f(X) \geq t) \leq \exp(-2t^2 / \sum_i c_i^2)$. -/
theorem bounded_differences_upper_tail
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [StandardBorelSpace Ω]
    {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)] [∀ i, DecidableEq (α i)]
    (X : ∀ i, Ω → α i) (hX_indep : iIndepFun X μ)
    (f : (∀ i, α i) → ℝ) (hf_meas : Measurable (fun ω => f (fun i => X i ω)))
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hbd : HasBoundedDifferences f c)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ f (fun i => X i ω) - μ[fun ω => f (fun i => X i ω)]} ≤
      exp (-2 * t ^ 2 / ∑ i : Fin n, c i ^ 2) := by

  obtain ⟨ℱ, Y, hsum, h_adapted, h0, h_subG⟩ :=
    doob_martingale_from_bounded_differences X hX_indep f hf_meas c hc hbd

  have heq : {ω | t ≤ f (fun i => X i ω) - μ[fun ω => f (fun i => X i ω)]} =
      {ω | t ≤ ∑ i ∈ range n, Y i ω} := by
    ext ω; simp only [Set.mem_setOf_eq]; rw [hsum ω]
  rw [heq]

  set cY : ℕ → ℝ≥0 := fun i => hoeffdingParam (liftToNat c i) (liftToNat_nonneg c hc i)
  have hmain := measure_sum_ge_le_of_hasCondSubgaussianMGF
    (ℱ := ℱ) (cY := cY) h_adapted h0 n h_subG ht

  refine hmain.trans (exp_le_exp.mpr ?_)
  rw [sum_hoeffdingParam_eq c hc]
  by_cases hS : ∑ i : Fin n, c i ^ 2 = 0
  · simp [hS]
  · rw [show (2 : ℝ) * ((∑ i : Fin n, c i ^ 2) / 4) =
        (∑ i : Fin n, c i ^ 2) / 2 by ring]
    rw [show -t ^ 2 / ((∑ i : Fin n, c i ^ 2) / 2) =
        -2 * t ^ 2 / ∑ i : Fin n, c i ^ 2 by field_simp]

/-- Lower-tail bounded differences inequality (Theorem 9.1.3): if $f$ has bounded differences
$c_i$, then $\mathbb{P}(f(X) - \mathbb{E}f(X) \leq -t) \leq \exp(-2t^2 / \sum_i c_i^2)$. -/
theorem bounded_differences_lower_tail
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [StandardBorelSpace Ω]
    {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)] [∀ i, DecidableEq (α i)]
    (X : ∀ i, Ω → α i) (hX_indep : iIndepFun X μ)
    (f : (∀ i, α i) → ℝ) (hf_meas : Measurable (fun ω => f (fun i => X i ω)))
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hbd : HasBoundedDifferences f c)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | f (fun i => X i ω) - μ[fun ω => f (fun i => X i ω)] ≤ -t} ≤
      exp (-2 * t ^ 2 / ∑ i : Fin n, c i ^ 2) := by

  have hf_neg_meas : Measurable (fun ω => (-f) (fun i => X i ω)) :=
    hf_meas.neg
  have hbd_neg : HasBoundedDifferences (-f) c := by
    intro i x y
    simp only [Pi.neg_apply, neg_sub_neg]
    rw [abs_sub_comm]
    exact hbd i x y
  have h := bounded_differences_upper_tail X hX_indep (-f) hf_neg_meas c hc hbd_neg ht

  have heq : {ω | t ≤ (-f) (fun i => X i ω) - μ[fun ω => (-f) (fun i => X i ω)]} =
      {ω | f (fun i => X i ω) - μ[fun ω => f (fun i => X i ω)] ≤ -t} := by
    ext ω
    simp only [Set.mem_setOf_eq, Pi.neg_apply, integral_neg]
    constructor
    · intro h'; linarith
    · intro h'; linarith
  rw [heq] at h
  exact h

/-- The two-sided bounded differences inequality (Theorem 9.1.3, McDiarmid):
both tails $\mathbb{P}(|f(X) - \mathbb{E}f(X)| \geq t)$ are bounded by
$\exp(-2t^2 / \sum_i c_i^2)$. -/
theorem bounded_differences_inequality
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [StandardBorelSpace Ω]
    {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)] [∀ i, DecidableEq (α i)]
    (X : ∀ i, Ω → α i) (hX_indep : iIndepFun X μ)
    (f : (∀ i, α i) → ℝ) (hf_meas : Measurable (fun ω => f (fun i => X i ω)))
    (c : Fin n → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hbd : HasBoundedDifferences f c)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ f (fun i => X i ω) - μ[fun ω => f (fun i => X i ω)]} ≤
      exp (-2 * t ^ 2 / ∑ i : Fin n, c i ^ 2) ∧
    μ.real {ω | f (fun i => X i ω) - μ[fun ω => f (fun i => X i ω)] ≤ -t} ≤
      exp (-2 * t ^ 2 / ∑ i : Fin n, c i ^ 2) :=
  ⟨bounded_differences_upper_tail X hX_indep f hf_meas c hc hbd ht,
   bounded_differences_lower_tail X hX_indep f hf_meas c hc hbd ht⟩

/-- Bounded differences inequality with uniform constant $c_i = 1$ (Theorem 9.1.1):
if $f$ is $1$-Lipschitz per coordinate, then
$\mathbb{P}(f(X) - \mathbb{E}f(X) \geq t) \leq \exp(-2t^2/n)$. -/
theorem bounded_differences_uniform_upper_tail
    {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    [StandardBorelSpace Ω]
    {α : Fin n → Type*} [∀ i, MeasurableSpace (α i)] [∀ i, DecidableEq (α i)]
    (X : ∀ i, Ω → α i) (hX_indep : iIndepFun X μ)
    (f : (∀ i, α i) → ℝ) (hf_meas : Measurable (fun ω => f (fun i => X i ω)))
    (hbd : HasBoundedDifferences f (fun _ => (1 : ℝ)))
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ f (fun i => X i ω) - μ[fun ω => f (fun i => X i ω)]} ≤
      exp (-2 * t ^ 2 / ↑n) := by
  have h := bounded_differences_upper_tail X hX_indep f hf_meas (fun _ => (1 : ℝ))
    (fun _ => zero_le_one) hbd ht
  simp only [one_pow, sum_const, card_univ, Fintype.card_fin, Nat.smul_one_eq_cast] at h
  exact h

end BoundedDifferences
