/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Exp
set_option maxHeartbeats 800000

open MeasureTheory Real Finset

noncomputable section

namespace TalagrandWeightedCertificates

variable {n : ℕ} {Ω : Fin n → Type*}

/-- The weighted Hamming distance between $x$ and $y$ with weights $α$:
$d_α(x, y) = \sum_{i : x_i \neq y_i} α_i$. -/
def weightedHammingDist [∀ i, DecidableEq (Ω i)]
    (α : Fin n → ℝ) (x y : (i : Fin n) → Ω i) : ℝ :=
  ∑ i : Fin n, if x i = y i then 0 else α i

/-- The Euclidean ($ℓ^2$) norm of the weight vector $α$:
$\|α\|_2 = \sqrt{\sum_i α_i^2}$. -/
def eucNorm (α : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, α i ^ 2)

/-- The weighted Hamming distance from $x$ to a set $A$:
$d_α(x, A) = \inf_{y \in A} d_α(x, y)$. -/
def weightedDistToSet [∀ i, DecidableEq (Ω i)]
    (α : Fin n → ℝ) (x : (i : Fin n) → Ω i)
    (A : Set ((i : Fin n) → Ω i)) : ℝ :=
  sInf (Set.image (weightedHammingDist α x) A)

/-- Talagrand's convex distance from $x$ to $A$, defined as the supremum of the
weighted distances $d_α(x, A)$ over all unit-norm weight vectors:
$d_T(x, A) = \sup_{\|α\|_2 = 1} d_α(x, A)$. -/
def convexDist [∀ i, DecidableEq (Ω i)]
    (x : (i : Fin n) → Ω i) (A : Set ((i : Fin n) → Ω i)) : ℝ :=
  sSup (Set.image (fun α => weightedDistToSet α x A) {α | eucNorm α = 1})

/-- The function $f$ admits weighted certificates with constant $K$: for every $x$
there exist nonnegative weights $α(x)$ with $\|α(x)\|_2 \leq K/2$ such that for all
$y$, $f(y) \geq f(x) - \sum_{i : x_i \neq y_i} α_i(x)$. -/
def HasWeightedCertificates [∀ i, DecidableEq (Ω i)]
    (f : ((i : Fin n) → Ω i) → ℝ) (K : ℝ) : Prop :=
  ∀ x, ∃ α : Fin n → ℝ,
    (∀ i, 0 ≤ α i) ∧
    eucNorm α ≤ K / 2 ∧
    ∀ y, f y ≥ f x - weightedHammingDist α x y


/-- Talagrand's convex-distance inequality (Theorem 9.5.11): for any product
probability measure on $\prod_i Ω_i$ and any set $A$,
$\mu(A) \cdot \mu(\{x : d_T(x, A) \geq t\}) \leq e^{-t^2 / 4}$. -/
theorem talagrand_convex_distance_inequality
    {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, DecidableEq (Ω i)]
    [∀ i, MeasurableSpace (Ω i)]
    (μ : (i : Fin n) → Measure (Ω i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (A : Set ((i : Fin n) → Ω i))
    (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi μ A).toReal * (Measure.pi μ {x | convexDist x A ≥ t}).toReal
      ≤ Real.exp (-(t ^ 2) / 4) := by sorry
/-- If $f$ has weighted certificates with constant $K$ and $f(x) \geq r$, then the
convex distance from $x$ to the sublevel set $\{f \leq r - t\}$ is at least
$2t/K$. -/
theorem certificate_convexDist_bound
    {n : ℕ} {Ω : Fin n → Type*} [∀ i, DecidableEq (Ω i)]
    (f : ((i : Fin n) → Ω i) → ℝ) (K : ℝ) (hK : 0 < K)
    (hcert : HasWeightedCertificates f K)
    (x : (i : Fin n) → Ω i) (r t : ℝ) (hfx : f x ≥ r) :
    convexDist x {y | f y ≤ r - t} ≥ 2 * t / K := by sorry

/-- Combining the two one-sided product bounds with the median property
$\mathbb{P}(f \leq m), \mathbb{P}(f \geq m) \geq 1/2$ yields the two-sided
tail bound $\mathbb{P}(f \geq m+t) + \mathbb{P}(f \leq m-t) \leq 4 e^{-t^2 / K^2}$. -/
theorem median_argument
    (prob_le_m prob_ge_mt prob_le_mt prob_ge_m : ℝ)
    (K t : ℝ)
    (hprod1 : prob_le_m * prob_ge_mt ≤ Real.exp (-(t ^ 2) / K ^ 2))
    (hprod2 : prob_le_mt * prob_ge_m ≤ Real.exp (-(t ^ 2) / K ^ 2))
    (hmed_le : prob_le_m ≥ 1 / 2)
    (hmed_ge : prob_ge_m ≥ 1 / 2) :
    prob_ge_mt + prob_le_mt ≤ 4 * Real.exp (-(t ^ 2) / K ^ 2) := by
  have hexp_pos := Real.exp_pos (-(t ^ 2) / K ^ 2)
  have h2 : prob_ge_mt ≤ 2 * Real.exp (-(t ^ 2) / K ^ 2) := by nlinarith
  have h4 : prob_le_mt ≤ 2 * Real.exp (-(t ^ 2) / K ^ 2) := by nlinarith
  linarith

/-- Theorem 9.5.14 (Talagrand's inequality with weighted certificates): if $f$ has
weighted certificates with constant $K$ and $m$ is a median of $f$, then
$\mu(\{x : |f(x) - m| \geq t\}) \leq 4 e^{-t^2 / K^2}$. -/
theorem talagrand_weighted_certificates
    {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, DecidableEq (Ω i)]
    [∀ i, MeasurableSpace (Ω i)]
    (μ : (i : Fin n) → Measure (Ω i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : ((i : Fin n) → Ω i) → ℝ)
    (K : ℝ) (hK : 0 < K)
    (hcert : HasWeightedCertificates f K)
    (m : ℝ)
    (hmed_le : (Measure.pi μ {x | f x ≤ m}).toReal ≥ 1 / 2)
    (hmed_ge : (Measure.pi μ {x | f x ≥ m}).toReal ≥ 1 / 2)
    (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi μ {x | |f x - m| ≥ t}).toReal ≤ 4 * Real.exp (-(t ^ 2) / K ^ 2) := by


  have hprod : ∀ r, (Measure.pi μ {x | f x ≤ r - t}).toReal *
      (Measure.pi μ {x | f x ≥ r}).toReal ≤ Real.exp (-(t ^ 2) / K ^ 2) := by
    intro r


    have h_tal := talagrand_convex_distance_inequality μ
      {y | f y ≤ r - t} (2 * t / K) (by positivity)

    have hK_ne : K ≠ 0 := ne_of_gt hK
    have h_exp_eq : Real.exp (-((2 * t / K) ^ 2) / 4) = Real.exp (-(t ^ 2) / K ^ 2) := by
      congr 1; field_simp; ring
    rw [h_exp_eq] at h_tal


    have h_mono : (Measure.pi μ {x | f x ≥ r}) ≤
        (Measure.pi μ {x | convexDist x {y | f y ≤ r - t} ≥ 2 * t / K}) := by
      apply MeasureTheory.measure_mono
      intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      exact certificate_convexDist_bound f K hK hcert x r t hx
    have hnn := ENNReal.toReal_nonneg (a := Measure.pi μ {x | f x ≤ r - t})
    have h_mono_real : (Measure.pi μ {x | f x ≥ r}).toReal ≤
        (Measure.pi μ {x | convexDist x {y | f y ≤ r - t} ≥ 2 * t / K}).toReal := by
      exact ENNReal.toReal_mono (measure_ne_top _ _) h_mono
    nlinarith


  have hsub : (Measure.pi μ {x | |f x - m| ≥ t}) ≤
      (Measure.pi μ {x | f x ≥ m + t}) + (Measure.pi μ {x | f x ≤ m - t}) := by
    apply le_trans (MeasureTheory.measure_mono _) (measure_union_le _ _)
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_union] at hx ⊢
    by_cases h : f x ≥ m
    · left
      have : |f x - m| = f x - m := abs_of_nonneg (by linarith)
      linarith
    · right
      push_neg at h
      have : |f x - m| = -(f x - m) := abs_of_neg (by linarith)
      linarith

  have h1 : (Measure.pi μ {x | f x ≤ m}).toReal *
      (Measure.pi μ {x | f x ≥ m + t}).toReal ≤ Real.exp (-(t ^ 2) / K ^ 2) := by
    have := hprod (m + t)
    simp only [add_sub_cancel_right] at this
    exact this

  have h3 : (Measure.pi μ {x | f x ≤ m - t}).toReal *
      (Measure.pi μ {x | f x ≥ m}).toReal ≤ Real.exp (-(t ^ 2) / K ^ 2) := hprod m

  have h_tail := median_argument
    (Measure.pi μ {x | f x ≤ m}).toReal
    (Measure.pi μ {x | f x ≥ m + t}).toReal
    (Measure.pi μ {x | f x ≤ m - t}).toReal
    (Measure.pi μ {x | f x ≥ m}).toReal
    K t h1 h3 hmed_le hmed_ge

  have hsub_real : (Measure.pi μ {x | |f x - m| ≥ t}).toReal ≤
      (Measure.pi μ {x | f x ≥ m + t}).toReal + (Measure.pi μ {x | f x ≤ m - t}).toReal := by
    have hne : (Measure.pi μ {x | f x ≥ m + t}) + (Measure.pi μ {x | f x ≤ m - t}) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩
    have h1 := ENNReal.toReal_mono hne hsub
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h1
    exact h1
  linarith

end TalagrandWeightedCertificates
