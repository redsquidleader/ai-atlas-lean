/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Moments.SubGaussian
set_option maxHeartbeats 800000

open MeasureTheory Real Set Metric

namespace Talagrand

variable {n : ℕ}

/-- The Boolean cube $\{0, 1\}^n$ embedded in $\mathbb{R}^n$. -/
def cube01 (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, x i = 0 ∨ x i = 1}

/-- The signed cube $\{-1, +1\}^n$ embedded in $\mathbb{R}^n$. -/
def cubePM (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, x i = -1 ∨ x i = 1}

/-- The continuous cube $[0,1]^n$ in $\mathbb{R}^n$. -/
def continuousCube01 (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc 0 1)

/-- Talagrand's inequality for convex sets (Theorem 9.5.3) on the Boolean cube
$\{0,1\}^n$: if $A$ is convex, then
$\mu(A) \cdot \mu(\{x : \operatorname{dist}(x, A) \geq t\}) \leq e^{-t^2/4}$. -/
theorem talagrand_convex_concentration
    {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (cube01 n)ᶜ = 0)
    (A : Set (Fin n → ℝ)) (hA : Convex ℝ A) (t : ℝ) (ht : 0 ≤ t) :
    (μ A).toReal * (μ {x | t ≤ Metric.infDist x A}).toReal ≤
      Real.exp (-(t ^ 2) / 4) := by sorry

/-- Talagrand's convex-set inequality on the signed cube $\{-1,+1\}^n$:
$\mu(A) \cdot \mu(\{x : \operatorname{dist}(x, A) \geq t\}) \leq e^{-t^2/4}$. -/
theorem talagrand_convex_concentration_cubePM
    {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (cubePM n)ᶜ = 0)
    (A : Set (Fin n → ℝ)) (hA : Convex ℝ A) (t : ℝ) (ht : 0 ≤ t) :
    (μ A).toReal * (μ {x | t ≤ Metric.infDist x A}).toReal ≤
      Real.exp (-(t ^ 2) / 4) := by sorry

/-- Corollary 9.5.6 (concentration for convex $1$-Lipschitz functions on the Boolean cube):
$\mu(\{f \leq r\}) \cdot \mu(\{f \geq r + t\}) \leq e^{-t^2/4}$. -/
theorem talagrand_convex_lipschitz
    {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (cube01 n)ᶜ = 0)
    (f : (Fin n → ℝ) → ℝ)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_lip : LipschitzWith 1 f)
    (r : ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hne : ({x : Fin n → ℝ | f x ≤ r}).Nonempty) :
    (μ {x | f x ≤ r}).toReal * (μ {x | r + t ≤ f x}).toReal ≤
      Real.exp (-(t ^ 2) / 4) := by
  set A := {x : Fin n → ℝ | f x ≤ r}
  have hA : Convex ℝ A := by
    intro x hx y hy a b ha hb hab
    simp only [A, mem_setOf_eq] at *
    calc f (a • x + b • y) ≤ a • f x + b • f y :=
          hf_convex.2 (mem_univ x) (mem_univ y) ha hb hab
      _ ≤ a • r + b • r := by gcongr
      _ = r := by rw [← add_smul, hab, one_smul]
  have key := talagrand_convex_concentration μ hμ A hA t ht
  have hsub : {x | r + t ≤ f x} ⊆ {x | t ≤ Metric.infDist x A} := by
    intro x hx
    simp only [A, mem_setOf_eq] at *
    rw [Metric.le_infDist hne]
    intro y hy
    simp only [mem_setOf_eq] at hy
    have h1 := hf_lip.dist_le_mul x y
    simp only [NNReal.coe_one, one_mul] at h1
    have h2 : t ≤ f x - f y := by linarith
    have h3 : f x - f y ≤ |f x - f y| := le_abs_self _
    rw [← Real.dist_eq] at h3
    linarith
  have hmono : μ {x | r + t ≤ f x} ≤ μ {x | t ≤ Metric.infDist x A} :=
    measure_mono hsub
  have h_toReal : (μ {x | r + t ≤ f x}).toReal ≤ (μ {x | t ≤ Metric.infDist x A}).toReal :=
    (ENNReal.toReal_le_toReal (measure_ne_top μ _) (measure_ne_top μ _)).mpr hmono
  calc (μ {x | f x ≤ r}).toReal * (μ {x | r + t ≤ f x}).toReal
      ≤ (μ A).toReal * (μ {x | t ≤ Metric.infDist x A}).toReal := by
        apply mul_le_mul_of_nonneg_left h_toReal ENNReal.toReal_nonneg
    _ ≤ Real.exp (-(t ^ 2) / 4) := key

/-- $m$ is a median of $f$ under $\mu$ if both $\mu(\{f \leq m\}) \geq 1/2$
and $\mu(\{f \geq m\}) \geq 1/2$. -/
def IsMedian (μ : Measure (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ) (m : ℝ) : Prop :=
  (1 : ℝ) / 2 ≤ (μ {x | f x ≤ m}).toReal ∧ (1 : ℝ) / 2 ≤ (μ {x | m ≤ f x}).toReal

/-- Upper-tail concentration about the median for convex $1$-Lipschitz $f$:
$\mu(\{f \geq m + t\}) \leq 2 e^{-t^2/4}$. -/
theorem talagrand_upper_tail
    {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (cube01 n)ᶜ = 0)
    (f : (Fin n → ℝ) → ℝ)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_lip : LipschitzWith 1 f)
    (m : ℝ) (hm : IsMedian μ f m)
    (t : ℝ) (ht : 0 ≤ t)
    (hne : ({x : Fin n → ℝ | f x ≤ m}).Nonempty) :
    (μ {x | m + t ≤ f x}).toReal ≤ 2 * Real.exp (-(t ^ 2) / 4) := by
  have h956 := talagrand_convex_lipschitz μ hμ f hf_convex hf_lip m t ht hne
  have hmed := hm.1
  nlinarith [ENNReal.toReal_nonneg (a := μ {x | m + t ≤ f x})]

/-- Lower-tail concentration about the median for convex $1$-Lipschitz $f$:
$\mu(\{f \leq m - t\}) \leq 2 e^{-t^2/4}$. -/
theorem talagrand_lower_tail
    {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (cube01 n)ᶜ = 0)
    (f : (Fin n → ℝ) → ℝ)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_lip : LipschitzWith 1 f)
    (m : ℝ) (hm : IsMedian μ f m)
    (t : ℝ) (ht : 0 ≤ t)
    (hne : ({x : Fin n → ℝ | f x ≤ m - t}).Nonempty) :
    (μ {x | f x ≤ m - t}).toReal ≤ 2 * Real.exp (-(t ^ 2) / 4) := by
  have h956 := talagrand_convex_lipschitz μ hμ f hf_convex hf_lip (m - t) t ht hne
  have hset : {x : Fin n → ℝ | m - t + t ≤ f x} = {x | m ≤ f x} := by
    ext x; simp only [mem_setOf_eq]; constructor <;> intro h <;> linarith
  rw [hset] at h956
  nlinarith [hm.2, ENNReal.toReal_nonneg (a := μ {x | f x ≤ m - t})]

/-- Corollary 9.5.8 (two-sided median concentration on the Boolean cube):
for convex $1$-Lipschitz $f$ with median $m$,
$\mu(\{|f - m| \geq t\}) \leq 4 e^{-t^2/4}$. -/
theorem talagrand_median_concentration
    {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (cube01 n)ᶜ = 0)
    (f : (Fin n → ℝ) → ℝ)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_lip : LipschitzWith 1 f)
    (m : ℝ) (hm : IsMedian μ f m)
    (t : ℝ) (ht : 0 ≤ t)
    (hne_m : ({x : Fin n → ℝ | f x ≤ m}).Nonempty)
    (hne_mt : ({x : Fin n → ℝ | f x ≤ m - t}).Nonempty) :
    (μ {x | t ≤ |f x - m|}).toReal ≤ 4 * Real.exp (-(t ^ 2) / 4) := by

  have hsub : {x : Fin n → ℝ | t ≤ |f x - m|} ⊆
      {x | m + t ≤ f x} ∪ {x | f x ≤ m - t} := by
    intro x hx
    simp only [mem_setOf_eq, mem_union] at *
    cases le_or_gt m (f x) with
    | inl h =>
      left
      have : |f x - m| = f x - m := abs_of_nonneg (sub_nonneg.mpr h)
      linarith [this ▸ hx]
    | inr h =>
      right
      have : |f x - m| = -(f x - m) := abs_of_neg (sub_neg.mpr h)
      linarith [this ▸ hx]

  have hmono : μ {x | t ≤ |f x - m|} ≤
      μ {x | m + t ≤ f x} + μ {x | f x ≤ m - t} :=
    le_trans (measure_mono hsub) (measure_union_le _ _)
  have h_toReal : (μ {x | t ≤ |f x - m|}).toReal ≤
      (μ {x | m + t ≤ f x}).toReal + (μ {x | f x ≤ m - t}).toReal := by
    have h1 := (ENNReal.toReal_le_toReal (measure_ne_top μ _)
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, measure_ne_top μ _⟩)).mpr hmono
    rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at h1
    exact h1
  have h_upper := talagrand_upper_tail μ hμ f hf_convex hf_lip m hm t ht hne_m
  have h_lower := talagrand_lower_tail μ hμ f hf_convex hf_lip m hm t ht hne_mt
  linarith

/-- Talagrand's convex-set inequality on the continuous cube $[0,1]^n$. -/
theorem talagrand_convex_concentration_continuousCube01
    {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (continuousCube01 n)ᶜ = 0)
    (A : Set (Fin n → ℝ)) (hA : Convex ℝ A) (t : ℝ) (ht : 0 ≤ t) :
    (μ A).toReal * (μ {x | t ≤ Metric.infDist x A}).toReal ≤
      Real.exp (-(t ^ 2) / 4) := by sorry

/-- Concentration for convex $1$-Lipschitz $f$ on the continuous cube $[0,1]^n$:
$\mu(\{f \leq r\}) \cdot \mu(\{f \geq r + t\}) \leq e^{-t^2/4}$. -/
theorem talagrand_convex_lipschitz_continuousCube01
    {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (continuousCube01 n)ᶜ = 0)
    (f : (Fin n → ℝ) → ℝ)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_lip : LipschitzWith 1 f)
    (r : ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hne : ({x : Fin n → ℝ | f x ≤ r}).Nonempty) :
    (μ {x | f x ≤ r}).toReal * (μ {x | r + t ≤ f x}).toReal ≤
      Real.exp (-(t ^ 2) / 4) := by
  set A := {x : Fin n → ℝ | f x ≤ r}
  have hA : Convex ℝ A := by
    intro x hx y hy a b ha hb hab
    simp only [A, mem_setOf_eq] at *
    calc f (a • x + b • y) ≤ a • f x + b • f y :=
          hf_convex.2 (mem_univ x) (mem_univ y) ha hb hab
      _ ≤ a • r + b • r := by gcongr
      _ = r := by rw [← add_smul, hab, one_smul]
  have key := talagrand_convex_concentration_continuousCube01 μ hμ A hA t ht
  have hsub : {x | r + t ≤ f x} ⊆ {x | t ≤ Metric.infDist x A} := by
    intro x hx
    simp only [A, mem_setOf_eq] at *
    rw [Metric.le_infDist hne]
    intro y hy
    simp only [mem_setOf_eq] at hy
    have h1 := hf_lip.dist_le_mul x y
    simp only [NNReal.coe_one, one_mul] at h1
    have h2 : t ≤ f x - f y := by linarith
    have h3 : f x - f y ≤ |f x - f y| := le_abs_self _
    rw [← Real.dist_eq] at h3
    linarith
  have hmono : μ {x | r + t ≤ f x} ≤ μ {x | t ≤ Metric.infDist x A} :=
    measure_mono hsub
  have h_toReal : (μ {x | r + t ≤ f x}).toReal ≤ (μ {x | t ≤ Metric.infDist x A}).toReal :=
    (ENNReal.toReal_le_toReal (measure_ne_top μ _) (measure_ne_top μ _)).mpr hmono
  calc (μ {x | f x ≤ r}).toReal * (μ {x | r + t ≤ f x}).toReal
      ≤ (μ A).toReal * (μ {x | t ≤ Metric.infDist x A}).toReal := by
        apply mul_le_mul_of_nonneg_left h_toReal ENNReal.toReal_nonneg
    _ ≤ Real.exp (-(t ^ 2) / 4) := key

/-- Concentration for convex $1$-Lipschitz $f$ on the signed cube $\{-1,+1\}^n$:
$\mu(\{f \leq r\}) \cdot \mu(\{f \geq r + t\}) \leq e^{-t^2/4}$. -/
theorem talagrand_convex_lipschitz_cubePM
    {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (cubePM n)ᶜ = 0)
    (f : (Fin n → ℝ) → ℝ)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_lip : LipschitzWith 1 f)
    (r : ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hne : ({x : Fin n → ℝ | f x ≤ r}).Nonempty) :
    (μ {x | f x ≤ r}).toReal * (μ {x | r + t ≤ f x}).toReal ≤
      Real.exp (-(t ^ 2) / 4) := by
  set A := {x : Fin n → ℝ | f x ≤ r}
  have hA : Convex ℝ A := by
    intro x hx y hy a b ha hb hab
    simp only [A, mem_setOf_eq] at *
    calc f (a • x + b • y) ≤ a • f x + b • f y :=
          hf_convex.2 (mem_univ x) (mem_univ y) ha hb hab
      _ ≤ a • r + b • r := by gcongr
      _ = r := by rw [← add_smul, hab, one_smul]
  have key := talagrand_convex_concentration_cubePM μ hμ A hA t ht

  have hsub : {x | r + t ≤ f x} ⊆ {x | t ≤ Metric.infDist x A} := by
    intro x hx
    simp only [A, mem_setOf_eq] at *
    rw [Metric.le_infDist hne]
    intro y hy
    simp only [mem_setOf_eq] at hy
    have h1 := hf_lip.dist_le_mul x y
    simp only [NNReal.coe_one, one_mul] at h1
    have h2 : t ≤ f x - f y := by linarith
    have h3 : f x - f y ≤ |f x - f y| := le_abs_self _
    rw [← Real.dist_eq] at h3
    linarith
  have hmono : μ {x | r + t ≤ f x} ≤ μ {x | t ≤ Metric.infDist x A} :=
    measure_mono hsub
  have h_toReal : (μ {x | r + t ≤ f x}).toReal ≤ (μ {x | t ≤ Metric.infDist x A}).toReal :=
    (ENNReal.toReal_le_toReal (measure_ne_top μ _) (measure_ne_top μ _)).mpr hmono
  calc (μ {x | f x ≤ r}).toReal * (μ {x | r + t ≤ f x}).toReal
      ≤ (μ A).toReal * (μ {x | t ≤ Metric.infDist x A}).toReal := by
        apply mul_le_mul_of_nonneg_left h_toReal ENNReal.toReal_nonneg
    _ ≤ Real.exp (-(t ^ 2) / 4) := key

/-- Two-sided median concentration on the signed cube $\{-1,+1\}^n$:
for convex $1$-Lipschitz $f$ with median $m$,
$\mu(\{|f - m| \geq t\}) \leq 4 e^{-t^2/4}$. -/
theorem talagrand_median_concentration_cubePM
    {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (cubePM n)ᶜ = 0)
    (f : (Fin n → ℝ) → ℝ)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_lip : LipschitzWith 1 f)
    (m : ℝ) (hm : IsMedian μ f m)
    (t : ℝ) (ht : 0 ≤ t)
    (hne_m : ({x : Fin n → ℝ | f x ≤ m}).Nonempty)
    (hne_mt : ({x : Fin n → ℝ | f x ≤ m - t}).Nonempty) :
    (μ {x | t ≤ |f x - m|}).toReal ≤ 4 * Real.exp (-(t ^ 2) / 4) := by

  have hsub : {x : Fin n → ℝ | t ≤ |f x - m|} ⊆
      {x | m + t ≤ f x} ∪ {x | f x ≤ m - t} := by
    intro x hx
    simp only [mem_setOf_eq, mem_union] at *
    cases le_or_gt m (f x) with
    | inl h =>
      left
      have : |f x - m| = f x - m := abs_of_nonneg (sub_nonneg.mpr h)
      linarith [this ▸ hx]
    | inr h =>
      right
      have : |f x - m| = -(f x - m) := abs_of_neg (sub_neg.mpr h)
      linarith [this ▸ hx]

  have hmono : μ {x | t ≤ |f x - m|} ≤
      μ {x | m + t ≤ f x} + μ {x | f x ≤ m - t} :=
    le_trans (measure_mono hsub) (measure_union_le _ _)
  have h_toReal : (μ {x | t ≤ |f x - m|}).toReal ≤
      (μ {x | m + t ≤ f x}).toReal + (μ {x | f x ≤ m - t}).toReal := by
    have h1 := (ENNReal.toReal_le_toReal (measure_ne_top μ _)
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, measure_ne_top μ _⟩)).mpr hmono
    rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at h1
    exact h1

  have h_upper : (μ {x | m + t ≤ f x}).toReal ≤ 2 * Real.exp (-(t ^ 2) / 4) := by
    have h956 := talagrand_convex_lipschitz_cubePM μ hμ f hf_convex hf_lip m t ht hne_m
    nlinarith [hm.1, ENNReal.toReal_nonneg (a := μ {x | m + t ≤ f x})]

  have h_lower : (μ {x | f x ≤ m - t}).toReal ≤ 2 * Real.exp (-(t ^ 2) / 4) := by
    have h956 := talagrand_convex_lipschitz_cubePM μ hμ f hf_convex hf_lip (m - t) t ht hne_mt
    have hset : {x : Fin n → ℝ | m - t + t ≤ f x} = {x | m ≤ f x} := by
      ext x; simp only [mem_setOf_eq]; constructor <;> intro h <;> linarith
    rw [hset] at h956
    nlinarith [hm.2, ENNReal.toReal_nonneg (a := μ {x | f x ≤ m - t})]
  linarith

/-- Elementary inequality: $t^2/2 - K^2 \leq (t - K)^2$ for all real $t, K$. -/
lemma sq_sub_le_half_sq (t K : ℝ) : t ^ 2 / 2 - K ^ 2 ≤ (t - K) ^ 2 := by
  nlinarith [sq_nonneg (t - 2 * K)]

/-- Shifting the centering point of a sub-Gaussian tail bound: if $X$ concentrates
about $m$ with constants $(C_1, c_1)$ and $|m - a| \leq K$, then $X$ concentrates
about $a$ with adjusted constants, gaining a factor $e^{c_1 K^2}$. -/
lemma subgaussian_shift_center
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (m a K : ℝ) (hK : |m - a| ≤ K)
    (C₁ c₁ : ℝ) (hC₁ : 1 ≤ C₁) (hc₁ : 0 < c₁)
    (hbound : ∀ s : ℝ, 0 ≤ s →
      (μ {ω | s ≤ |X ω - m|}).toReal ≤ C₁ * Real.exp (-(c₁ * s ^ 2)))
    (t : ℝ) (ht : 0 ≤ t) :
    (μ {ω | t ≤ |X ω - a|}).toReal ≤
      C₁ * Real.exp (c₁ * K ^ 2) * Real.exp (-(c₁ / 2 * t ^ 2)) := by
  have hK_pos : 0 ≤ K := le_trans (abs_nonneg _) hK
  have hsub : {ω | t ≤ |X ω - a|} ⊆ {ω | t - K ≤ |X ω - m|} := by
    intro ω hω
    simp only [mem_setOf_eq] at *
    linarith [abs_sub_le (X ω) m a]
  by_cases htK : K ≤ t
  ·
    have hs : 0 ≤ t - K := by linarith
    have hb := hbound (t - K) hs
    have hmeas_mono : μ {ω | t ≤ |X ω - a|} ≤ μ {ω | t - K ≤ |X ω - m|} :=
      measure_mono hsub
    have h_tr : (μ {ω | t ≤ |X ω - a|}).toReal ≤ (μ {ω | t - K ≤ |X ω - m|}).toReal :=
      (ENNReal.toReal_le_toReal (measure_ne_top μ _) (measure_ne_top μ _)).mpr hmeas_mono
    calc (μ {ω | t ≤ |X ω - a|}).toReal
        ≤ C₁ * Real.exp (-(c₁ * (t - K) ^ 2)) := le_trans h_tr hb
      _ ≤ C₁ * Real.exp (-(c₁ * (t ^ 2 / 2 - K ^ 2))) := by
          gcongr; linarith [sq_sub_le_half_sq t K]
      _ = C₁ * Real.exp (c₁ * K ^ 2 + (-(c₁ / 2 * t ^ 2))) := by
          congr 1; ring_nf
      _ = C₁ * (Real.exp (c₁ * K ^ 2) * Real.exp (-(c₁ / 2 * t ^ 2))) := by
          rw [Real.exp_add]
      _ = C₁ * Real.exp (c₁ * K ^ 2) * Real.exp (-(c₁ / 2 * t ^ 2)) := by ring
  ·
    simp only [not_le] at htK
    have hprob_le_one : (μ {ω | t ≤ |X ω - a|}).toReal ≤ 1 := by
      have hle : μ {ω | t ≤ |X ω - a|} ≤ 1 := by
        calc μ {ω | t ≤ |X ω - a|} ≤ μ Set.univ := measure_mono (subset_univ _)
          _ = 1 := measure_univ
      exact ENNReal.toReal_le_of_le_ofReal one_pos.le (by rwa [ENNReal.ofReal_one])
    suffices h : (1 : ℝ) ≤ C₁ * Real.exp (c₁ * K ^ 2) * Real.exp (-(c₁ / 2 * t ^ 2)) from
      le_trans hprob_le_one h
    have htK2 : t ^ 2 < K ^ 2 := by nlinarith
    have h3 : (0 : ℝ) ≤ c₁ * K ^ 2 + (-(c₁ / 2 * t ^ 2)) := by nlinarith
    have h4 : (1 : ℝ) ≤ Real.exp (c₁ * K ^ 2 + (-(c₁ / 2 * t ^ 2))) :=
      Real.one_le_exp h3
    have h5 : Real.exp (c₁ * K ^ 2 + (-(c₁ / 2 * t ^ 2))) =
        Real.exp (c₁ * K ^ 2) * Real.exp (-(c₁ / 2 * t ^ 2)) :=
      Real.exp_add _ _
    nlinarith [Real.exp_pos (c₁ * K ^ 2), Real.exp_pos (-(c₁ / 2 * t ^ 2))]

/-- The distance function $x \mapsto \operatorname{dist}(x, V)$ to a linear subspace $V$
is convex and $1$-Lipschitz. -/
theorem dist_subspace_convex_lipschitz
    {n : ℕ} (V : Submodule ℝ (Fin n → ℝ)) :
    ConvexOn ℝ Set.univ (fun x => Metric.infDist x (V : Set (Fin n → ℝ))) ∧
    LipschitzWith 1 (fun x => Metric.infDist x (V : Set (Fin n → ℝ))) := by sorry

/-- For a $d$-dimensional subspace $V$ with $d < n$, the median $m$ of
$x \mapsto \operatorname{dist}(x, V)$ on the signed cube satisfies
$|m - \sqrt{n - d}| \leq 1$. -/
theorem dist_subspace_median_bound
    {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (cubePM n)ᶜ = 0)
    (V : Submodule ℝ (Fin n → ℝ))
    (d : ℕ) (hd : Module.finrank ℝ V = d) (hdn : d < n) :
    ∃ m : ℝ, IsMedian μ (fun x => Metric.infDist x (V : Set (Fin n → ℝ))) m ∧
      |m - Real.sqrt (↑(n - d) : ℝ)| ≤ 1 := by sorry

/-- Any sublevel set $\{x : \operatorname{dist}(x, V) \leq r\}$ of the distance-to-subspace
function is nonempty (it contains $0 \in V$). -/
theorem dist_subspace_sublevel_nonempty
    {n : ℕ} (V : Submodule ℝ (Fin n → ℝ)) (r : ℝ) :
    ({x : Fin n → ℝ | (fun x => Metric.infDist x (V : Set (Fin n → ℝ))) x ≤ r}).Nonempty := by sorry

/-- Sub-Gaussian concentration of $\operatorname{dist}(x, V)$ about $\sqrt{n-d}$
on the signed cube $\{-1,+1\}^n$, for any $d$-dimensional subspace $V$ with $d < n$. -/
theorem dist_subspace_concentration
    {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (cubePM n)ᶜ = 0)
    (V : Submodule ℝ (Fin n → ℝ))
    (d : ℕ) (hd : Module.finrank ℝ V = d) (hdn : d < n) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ t : ℝ, 0 ≤ t →
      (μ {x | t ≤ |Metric.infDist x (V : Set (Fin n → ℝ)) -
        Real.sqrt (↑(n - d) : ℝ)|}).toReal ≤
        C * Real.exp (-(c * t ^ 2)) := by

  obtain ⟨hf_convex, hf_lip⟩ := dist_subspace_convex_lipschitz V

  obtain ⟨m, hm_median, hK_bound⟩ := dist_subspace_median_bound μ hμ V d hd hdn
  set f := fun x => Metric.infDist x (V : Set (Fin n → ℝ))

  have hbound : ∀ s : ℝ, 0 ≤ s →
      (μ {x | s ≤ |f x - m|}).toReal ≤ 4 * Real.exp (-(1 / 4 * s ^ 2)) := by
    intro s hs
    have h := talagrand_median_concentration_cubePM μ hμ f hf_convex hf_lip m hm_median s hs
      (dist_subspace_sublevel_nonempty V m)
      (dist_subspace_sublevel_nonempty V (m - s))
    convert h using 2
    ring_nf

  have hshift := fun t (ht : 0 ≤ t) =>
    subgaussian_shift_center μ f m (Real.sqrt (↑(n - d) : ℝ)) 1 hK_bound
      4 (1 / 4) (by norm_num) (by norm_num) hbound t ht
  refine ⟨4 * Real.exp (1 / 4 * 1 ^ 2), 1 / 8, ?_, by norm_num, fun t ht => ?_⟩
  · positivity
  · have h := hshift t ht
    convert h using 2
    ring_nf

/-- Talagrand's convex-set inequality on the continuous cube $[0,1]^n$
(alias of `talagrand_convex_concentration_continuousCube01`). -/
theorem talagrand_convex_set_concentration
    {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (continuousCube01 n)ᶜ = 0)
    (A : Set (Fin n → ℝ)) (hA : Convex ℝ A) (t : ℝ) (ht : 0 ≤ t) :
    (μ A).toReal * (μ {x | t ≤ Metric.infDist x A}).toReal ≤
      Real.exp (-(t ^ 2) / 4) :=
  talagrand_convex_concentration_continuousCube01 μ hμ A hA t ht

/-- Two-sided median concentration for convex $1$-Lipschitz $f$ on the continuous
cube $[0,1]^n$: $\mu(\{|f - m| \geq t\}) \leq 4 e^{-t^2/4}$. -/
theorem talagrand_convex_lipschitz_concentration
    {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (continuousCube01 n)ᶜ = 0)
    (f : (Fin n → ℝ) → ℝ)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_lip : LipschitzWith 1 f)
    (m : ℝ) (hm : IsMedian μ f m)
    (t : ℝ) (ht : 0 ≤ t) :
    (μ {x | t ≤ |f x - m|}).toReal ≤ 4 * Real.exp (-(t ^ 2) / 4) := by

  have hne_m : ({x : Fin n → ℝ | f x ≤ m}).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have : (μ {x | f x ≤ m}).toReal = 0 := by
      simp only [show {x : Fin n → ℝ | f x ≤ m} = ∅ from h, measure_empty,
                  ENNReal.toReal_zero]
    linarith [hm.1]

  have hsub : {x : Fin n → ℝ | t ≤ |f x - m|} ⊆
      {x | m + t ≤ f x} ∪ {x | f x ≤ m - t} := by
    intro x hx
    simp only [mem_setOf_eq, mem_union] at *
    cases le_or_gt m (f x) with
    | inl h =>
      left
      have : |f x - m| = f x - m := abs_of_nonneg (sub_nonneg.mpr h)
      linarith [this ▸ hx]
    | inr h =>
      right
      have : |f x - m| = -(f x - m) := abs_of_neg (sub_neg.mpr h)
      linarith [this ▸ hx]

  have h_upper : (μ {x | m + t ≤ f x}).toReal ≤ 2 * Real.exp (-(t ^ 2) / 4) := by
    have h956 := talagrand_convex_lipschitz_continuousCube01 μ hμ f hf_convex hf_lip m t ht hne_m
    nlinarith [hm.1, ENNReal.toReal_nonneg (a := μ {x | m + t ≤ f x})]

  have h_lower : (μ {x | f x ≤ m - t}).toReal ≤ 2 * Real.exp (-(t ^ 2) / 4) := by
    by_cases hne_mt : ({x : Fin n → ℝ | f x ≤ m - t}).Nonempty
    ·
      have h956 := talagrand_convex_lipschitz_continuousCube01 μ hμ f hf_convex hf_lip (m - t) t ht hne_mt
      have hset : {x : Fin n → ℝ | m - t + t ≤ f x} = {x | m ≤ f x} := by
        ext x; simp only [mem_setOf_eq]; constructor <;> intro h <;> linarith
      rw [hset] at h956
      nlinarith [hm.2, ENNReal.toReal_nonneg (a := μ {x | f x ≤ m - t})]
    ·
      rw [Set.not_nonempty_iff_eq_empty] at hne_mt
      have : (μ {x | f x ≤ m - t}).toReal = 0 := by
        simp only [show {x : Fin n → ℝ | f x ≤ m - t} = ∅ from hne_mt, measure_empty,
                    ENNReal.toReal_zero]
      rw [this]
      positivity

  have hmono : μ {x | t ≤ |f x - m|} ≤
      μ {x | m + t ≤ f x} + μ {x | f x ≤ m - t} :=
    le_trans (measure_mono hsub) (measure_union_le _ _)
  have h_toReal : (μ {x | t ≤ |f x - m|}).toReal ≤
      (μ {x | m + t ≤ f x}).toReal + (μ {x | f x ≤ m - t}).toReal := by
    have h1 := (ENNReal.toReal_le_toReal (measure_ne_top μ _)
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ _, measure_ne_top μ _⟩)).mpr hmono
    rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at h1
    exact h1
  linarith

/-- Combined Talagrand inequality on $[0,1]^n$: the convex-set bound together
with the median concentration for convex $1$-Lipschitz functions. -/
theorem talagrand_convex_lipschitz_combined
    {n : ℕ} (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : μ (continuousCube01 n)ᶜ = 0)
    (A : Set (Fin n → ℝ)) (hA : Convex ℝ A) (t : ℝ) (ht : 0 ≤ t)
    (f : (Fin n → ℝ) → ℝ)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_lip : LipschitzWith 1 f)
    (m : ℝ) (hm : IsMedian μ f m) :
    ((μ A).toReal * (μ {x | t ≤ Metric.infDist x A}).toReal ≤
      Real.exp (-(t ^ 2) / 4)) ∧
    ((μ {x | t ≤ |f x - m|}).toReal ≤ 4 * Real.exp (-(t ^ 2) / 4)) :=
  And.intro
    (talagrand_convex_set_concentration μ hμ A hA t ht)
    (talagrand_convex_lipschitz_concentration μ hμ f hf_convex hf_lip m hm t ht)

end Talagrand
