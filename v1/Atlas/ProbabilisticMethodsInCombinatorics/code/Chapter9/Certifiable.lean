/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.WeightedCertificates
import Atlas.ProbabilisticMethodsInCombinatorics.code.Certifiable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option maxHeartbeats 800000

open MeasureTheory Real Finset Set

noncomputable section

namespace TalagrandCertifiable

variable {n : ℕ} {Ω : Fin n → Type*}

/-- A function $f$ is Hamming-Lipschitz if $|f(x) - f(y)|$ is at most the Hamming distance
between $x$ and $y$ (the number of coordinates where they differ). -/
def IsHammingLipschitz [∀ i, DecidableEq (Ω i)]
    (f : ((i : Fin n) → Ω i) → ℝ) : Prop :=
  ∀ x y : (i : Fin n) → Ω i,
    |f x - f y| ≤ (Finset.univ.filter fun i => x i ≠ y i).card

/-- The upper level set $\{x : f(x) \geq r\}$ is $s$-certifiable (Definition 9.5.20). -/
def UpperLevelCertifiable [∀ i, DecidableEq (Ω i)]
    (f : ((i : Fin n) → Ω i) → ℝ) (r : ℝ) (s : ℕ) : Prop :=
  Certifiable.IsCertifiable (Ω := Ω) s {x | f x ≥ r}

/-- Key lemma for Talagrand's certifiable functions inequality: if $\{f \geq r\}$ is
$s$-certifiable, $f$ is Hamming-Lipschitz, and $f(y) \geq r$, then the convex distance from
$y$ to $\{f \leq r - t\}$ is at least $t / \sqrt{s}$. -/
theorem certifiable_convexDist_bound [∀ i, DecidableEq (Ω i)]
    (f : ((i : Fin n) → Ω i) → ℝ) (s : ℕ) (hs : 0 < s)
    (hf_lip : IsHammingLipschitz f)
    (r t : ℝ) (ht : 0 ≤ t)
    (hcert : UpperLevelCertifiable f r s)
    (y : (i : Fin n) → Ω i) (hfy : f y ≥ r) :
    TalagrandWeightedCertificates.convexDist (Ω := Ω) y {x | f x ≤ r - t} ≥
      t / Real.sqrt (s : ℝ) := by sorry

/-- Talagrand's inequality for $s$-certifiable Hamming-Lipschitz functions (Theorem 9.5.21):
$\mathbb{P}(f \leq r - t) \cdot \mathbb{P}(f \geq r) \leq \exp(-t^2 / (4s))$. -/
theorem talagrand_certifiable
    {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, DecidableEq (Ω i)]
    [∀ i, MeasurableSpace (Ω i)]
    (μ : (i : Fin n) → Measure (Ω i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : ((i : Fin n) → Ω i) → ℝ)
    (hf_lip : IsHammingLipschitz f)
    (r : ℝ) (s : ℕ) (hs : 0 < s)
    (hcert : UpperLevelCertifiable f r s)
    (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi μ {x | f x ≤ r - t}).toReal *
      (Measure.pi μ {x | f x ≥ r}).toReal ≤
        Real.exp (-(t ^ 2) / (4 * ↑s)) := by
  set A := {x : (i : Fin n) → Ω i | f x ≤ r - t}
  have h_inclusion : {x | f x ≥ r} ⊆
      {x | TalagrandWeightedCertificates.convexDist x A ≥ t / Real.sqrt (↑s)} := by
    intro y hy
    simp only [mem_setOf_eq] at hy ⊢
    exact certifiable_convexDist_bound f s hs hf_lip r t ht hcert y hy
  have h_mono : Measure.pi μ {x | f x ≥ r} ≤
      Measure.pi μ {x | TalagrandWeightedCertificates.convexDist x A ≥
        t / Real.sqrt (↑s)} :=
    MeasureTheory.measure_mono h_inclusion
  have h_mono_real : (Measure.pi μ {x | f x ≥ r}).toReal ≤
      (Measure.pi μ {x | TalagrandWeightedCertificates.convexDist x A ≥
        t / Real.sqrt (↑s)}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) h_mono
  have h_sqrt_nonneg : (0 : ℝ) ≤ t / Real.sqrt (↑s) :=
    div_nonneg ht (Real.sqrt_nonneg _)
  have h_tal := TalagrandWeightedCertificates.talagrand_convex_distance_inequality μ
    A (t / Real.sqrt (↑s)) h_sqrt_nonneg
  have hs_pos : (0 : ℝ) < ↑s := Nat.cast_pos.mpr hs
  have h_exp_eq : Real.exp (-((t / Real.sqrt ↑s) ^ 2) / 4) =
      Real.exp (-(t ^ 2) / (4 * ↑s)) := by
    congr 1
    rw [div_pow, Real.sq_sqrt (le_of_lt hs_pos)]
    ring
  rw [h_exp_eq] at h_tal
  have hnn := ENNReal.toReal_nonneg (a := Measure.pi μ A)
  nlinarith

/-- $m$ is a median of $f$ under the product measure $\prod_i \mu_i$:
both $\{f \leq m\}$ and $\{f \geq m\}$ have probability at least $1/2$. -/
def IsMedianPi
    {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, MeasurableSpace (Ω i)]
    (μ : (i : Fin n) → Measure (Ω i))
    (f : ((i : Fin n) → Ω i) → ℝ)
    (m : ℝ) : Prop :=
  (1 : ℝ) / 2 ≤ (Measure.pi μ {x | f x ≤ m}).toReal ∧
  (1 : ℝ) / 2 ≤ (Measure.pi μ {x | f x ≥ m}).toReal

/-- Corollary 9.5.22: two-sided concentration around the median for Hamming-Lipschitz
functions whose upper level sets are $\lfloor r \rfloor$-certifiable:
$\mathbb{P}(f \leq m - t) \leq 2\exp(-t^2/(4m))$ and
$\mathbb{P}(f \geq m + t) \leq 2\exp(-t^2/(4(m+t)))$. -/
theorem talagrand_certifiable_corollary
    {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, DecidableEq (Ω i)]
    [∀ i, MeasurableSpace (Ω i)]
    (μ : (i : Fin n) → Measure (Ω i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : ((i : Fin n) → Ω i) → ℝ)
    (hf_lip : IsHammingLipschitz f)
    (m : ℝ) (hm : IsMedianPi μ f m) (hm_pos : 1 ≤ m)
    (hcert : ∀ r : ℝ, 0 < r → UpperLevelCertifiable f r ⌊r⌋₊)
    (t : ℝ) (ht : 0 ≤ t) :
    (Measure.pi μ {x | f x ≤ m - t}).toReal ≤ 2 * Real.exp (-(t ^ 2) / (4 * m)) ∧
    (Measure.pi μ {x | f x ≥ m + t}).toReal ≤ 2 * Real.exp (-(t ^ 2) / (4 * (m + t))) := by
  have hm_nonneg : (0 : ℝ) ≤ m := le_trans zero_le_one hm_pos
  have hm_pos_real : (0 : ℝ) < m := lt_of_lt_of_le one_pos hm_pos
  have hmt_pos : (0 : ℝ) < m + t := by linarith
  have hmt_ge_one : (1 : ℝ) ≤ m + t := by linarith

  have hs_m_pos : 0 < ⌊m⌋₊ := Nat.floor_pos.mpr hm_pos
  have hs_mt_pos : 0 < ⌊m + t⌋₊ := Nat.floor_pos.mpr hmt_ge_one
  have hcert_m : UpperLevelCertifiable f m ⌊m⌋₊ := hcert m hm_pos_real
  have hcert_mt : UpperLevelCertifiable f (m + t) ⌊m + t⌋₊ := hcert (m + t) hmt_pos
  constructor
  ·
    have h921 := talagrand_certifiable μ f hf_lip m ⌊m⌋₊ hs_m_pos hcert_m t ht
    have hmed_ge : (1 : ℝ) / 2 ≤ (Measure.pi μ {x | f x ≥ m}).toReal := hm.2
    have hfloor_le : (⌊m⌋₊ : ℝ) ≤ m := Nat.floor_le hm_nonneg
    have hfloor_pos : (0 : ℝ) < (⌊m⌋₊ : ℝ) := Nat.cast_pos.mpr hs_m_pos
    have h_exp_mono : Real.exp (-(t ^ 2) / (4 * (⌊m⌋₊ : ℝ))) ≤
        Real.exp (-(t ^ 2) / (4 * m)) := by
      apply Real.exp_le_exp.mpr
      have h1 : t ^ 2 / (4 * m) ≤ t ^ 2 / (4 * (⌊m⌋₊ : ℝ)) :=
        div_le_div_of_nonneg_left (sq_nonneg t) (by positivity) (by linarith)
      have h2 : -(t ^ 2 / (4 * (⌊m⌋₊ : ℝ))) ≤ -(t ^ 2 / (4 * m)) := neg_le_neg h1
      simp only [neg_div] at h2 ⊢
      exact h2
    have hP_le := ENNReal.toReal_nonneg (a := Measure.pi μ {x | f x ≤ m - t})
    nlinarith
  ·
    have h921 := talagrand_certifiable μ f hf_lip (m + t) ⌊m + t⌋₊ hs_mt_pos hcert_mt t ht
    have hset_eq : {x : (i : Fin n) → Ω i | f x ≤ m + t - t} = {x | f x ≤ m} := by
      ext x; simp only [Set.mem_setOf_eq]; constructor <;> intro h <;> linarith
    rw [hset_eq] at h921
    have hmed_le : (1 : ℝ) / 2 ≤ (Measure.pi μ {x | f x ≤ m}).toReal := hm.1
    have hfloor_le : (⌊m + t⌋₊ : ℝ) ≤ m + t := Nat.floor_le (by linarith : (0 : ℝ) ≤ m + t)
    have hfloor_pos : (0 : ℝ) < (⌊m + t⌋₊ : ℝ) := Nat.cast_pos.mpr hs_mt_pos
    have h_exp_mono : Real.exp (-(t ^ 2) / (4 * (⌊m + t⌋₊ : ℝ))) ≤
        Real.exp (-(t ^ 2) / (4 * (m + t))) := by
      apply Real.exp_le_exp.mpr
      have h1 : t ^ 2 / (4 * (m + t)) ≤ t ^ 2 / (4 * (⌊m + t⌋₊ : ℝ)) :=
        div_le_div_of_nonneg_left (sq_nonneg t) (by positivity) (by linarith)
      have h2 : -(t ^ 2 / (4 * (⌊m + t⌋₊ : ℝ))) ≤ -(t ^ 2 / (4 * (m + t))) := neg_le_neg h1
      simp only [neg_div] at h2 ⊢
      exact h2
    have hP_le := ENNReal.toReal_nonneg (a := Measure.pi μ {x | f x ≥ m + t})
    nlinarith

/-- Technical lemma: for any $K > 0$ and $\varepsilon > 0$, one can choose $C$ large enough
that $2\exp(-C^2/(4K)) + 2\exp(-C^2/(4(K+C))) \leq \varepsilon$. -/
lemma tail_sum_small (K : ℝ) (hK : 0 < K) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      2 * Real.exp (-(C ^ 2) / (4 * K)) +
      2 * Real.exp (-(C ^ 2) / (4 * (K + C))) ≤ ε := by
  set C := max (2 * K + 1) (8 * Real.log (4 / ε) + 1) with hC_def
  use C
  refine ⟨lt_of_lt_of_le (by linarith : (0:ℝ) < 2 * K + 1) (le_max_left _ _), ?_⟩
  have hC_ge_2K : 2 * K < C := lt_of_lt_of_le (by linarith : 2*K < 2*K+1) (le_max_left _ _)
  have hC_pos : (0 : ℝ) < C := by linarith
  have hKC_le : K + C ≤ 2 * C := by linarith
  have h_exp_lower : C ^ 2 / (4 * (K + C)) ≥ C / 8 := by
    rw [ge_iff_le, div_le_div_iff₀ (by positivity : (0:ℝ) < 8)
      (by positivity : (0:ℝ) < 4 * (K+C))]
    nlinarith [sq_nonneg C]
  have hexp1 : Real.exp (-(C ^ 2) / (4 * K)) ≤ Real.exp (-C / 8) := by
    apply Real.exp_le_exp.mpr
    have h_CK : C ^ 2 / (4 * K) ≥ C / 8 := le_trans h_exp_lower.le
      (div_le_div_of_nonneg_left (by positivity : 0 ≤ C ^ 2)
        (by positivity : 0 < 4 * K) (by linarith))
    linarith [neg_le_neg h_CK.le,
      show -(C ^ 2) / (4 * K) = -(C ^ 2 / (4 * K)) from by ring,
      show -C / 8 = -(C / 8) from by ring]
  have hexp2 : Real.exp (-(C ^ 2) / (4 * (K + C))) ≤ Real.exp (-C / 8) := by
    apply Real.exp_le_exp.mpr
    linarith [neg_le_neg h_exp_lower.le,
      show -(C ^ 2) / (4 * (K + C)) = -(C ^ 2 / (4 * (K + C))) from by ring,
      show -C / 8 = -(C / 8) from by ring]
  have htotal : 2 * Real.exp (-(C ^ 2) / (4 * K)) +
      2 * Real.exp (-(C ^ 2) / (4 * (K + C))) ≤ 4 * Real.exp (-C / 8) := by
    nlinarith [Real.exp_pos (-(C ^ 2) / (4 * K)), Real.exp_pos (-C / 8)]
  suffices h : 4 * Real.exp (-C / 8) ≤ ε from le_trans htotal h
  have hC_ge_log : C ≥ 8 * Real.log (4 / ε) := by
    linarith [le_max_right (2 * K + 1) (8 * Real.log (4 / ε) + 1)]
  have hexp_bound : Real.exp (-C / 8) ≤ ε / 4 := by
    calc Real.exp (-C / 8)
        = Real.exp (-(C / 8)) := by ring_nf
      _ ≤ Real.exp (-(Real.log (4 / ε))) := by
          apply Real.exp_le_exp.mpr; linarith
      _ = (4 / ε)⁻¹ := by
          rw [Real.exp_neg, Real.exp_log (by positivity : (0:ℝ) < 4 / ε)]
      _ = ε / 4 := by field_simp
  linarith [Real.exp_pos (-C / 8)]

/-- Concentration of the longest-increasing-subsequence-type statistic: if the median $m$ of
$f$ satisfies $m \leq K\sqrt{n}$ and the Talagrand tail bounds hold, then for every
$\varepsilon > 0$ there exists $C$ such that $\mathbb{P}(|f - m| > C n^{1/4}) \leq \varepsilon$. -/
theorem lis_concentration
    {n : ℕ} (hn : 1 ≤ n)
    {Ω : Fin n → Type*}
    [∀ i, MeasurableSpace (Ω i)]
    (μ : (i : Fin n) → Measure (Ω i))
    [∀ i, IsProbabilityMeasure (μ i)]
    (f : ((i : Fin n) → Ω i) → ℝ)
    (m : ℝ) (hm_pos : 1 ≤ m)

    (K : ℝ) (hK : 0 < K) (hm_bound : m ≤ K * Real.sqrt n)

    (h_lower : ∀ t : ℝ, 0 ≤ t →
      (Measure.pi μ {x | f x ≤ m - t}).toReal ≤
        2 * Real.exp (-(t ^ 2) / (4 * m)))

    (h_upper : ∀ t : ℝ, 0 ≤ t →
      (Measure.pi μ {x | f x ≥ m + t}).toReal ≤
        2 * Real.exp (-(t ^ 2) / (4 * (m + t))))

    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      (Measure.pi μ {x | |f x - m| > C * (n : ℝ) ^ ((1:ℝ)/4)}).toReal ≤ ε := by
  obtain ⟨C₀, hC₀_pos, hC₀_bound⟩ := tail_sum_small K hK ε hε
  use C₀
  refine ⟨hC₀_pos, ?_⟩
  set t := C₀ * (n : ℝ) ^ ((1:ℝ)/4)
  have ht_pos : (0 : ℝ) ≤ t := by positivity

  have h_subset : {x | |f x - m| > t} ⊆
      {x | f x ≤ m - t} ∪ {x | f x ≥ m + t} := by
    intro x hx
    simp only [Set.mem_setOf_eq, gt_iff_lt] at hx
    have habs := hx
    rw [lt_abs] at habs
    cases habs with
    | inl h =>
      right
      show f x ≥ m + t
      linarith
    | inr h =>
      left
      show f x ≤ m - t
      linarith

  have h_meas_le : (Measure.pi μ {x | |f x - m| > t}).toReal ≤
      (Measure.pi μ {x | f x ≤ m - t}).toReal +
        (Measure.pi μ {x | f x ≥ m + t}).toReal := by
    calc (Measure.pi μ {x | |f x - m| > t}).toReal
        ≤ (Measure.pi μ ({x | f x ≤ m - t} ∪ {x | f x ≥ m + t})).toReal := by
          apply ENNReal.toReal_mono (measure_ne_top _ _)
          exact measure_mono h_subset
      _ ≤ (Measure.pi μ {x | f x ≤ m - t} +
            Measure.pi μ {x | f x ≥ m + t}).toReal := by
          apply ENNReal.toReal_mono
          · exact ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩
          · exact measure_union_le _ _
      _ = (Measure.pi μ {x | f x ≤ m - t}).toReal +
            (Measure.pi μ {x | f x ≥ m + t}).toReal :=
          ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)

  have h_low := h_lower t ht_pos
  have h_up := h_upper t ht_pos

  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hsqrt_pos : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have h_t_sq : t ^ 2 = C₀ ^ 2 * Real.sqrt n := by
    show (C₀ * (n : ℝ) ^ ((1:ℝ)/4)) ^ 2 = C₀ ^ 2 * Real.sqrt n
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast ((n : ℝ) ^ ((1:ℝ)/4)) 2,
        ← Real.rpow_mul (le_of_lt hn_pos)]
    norm_num
    rw [← Real.sqrt_eq_rpow]

  have h_exp_lower : Real.exp (-(t ^ 2) / (4 * m)) ≤
      Real.exp (-(C₀ ^ 2) / (4 * K)) := by
    apply Real.exp_le_exp.mpr
    rw [h_t_sq]
    have h1 : C₀ ^ 2 * Real.sqrt n / (4 * m) ≥ C₀ ^ 2 / (4 * K) := by
      rw [ge_iff_le, div_le_div_iff₀ (by positivity : (0:ℝ) < 4 * K)
        (by positivity : (0:ℝ) < 4 * m)]
      nlinarith [sq_nonneg C₀]
    linarith [neg_le_neg h1.le,
      show -(C₀ ^ 2 * Real.sqrt n) / (4 * m) =
        -(C₀ ^ 2 * Real.sqrt n / (4 * m)) from by ring,
      show -(C₀ ^ 2) / (4 * K) = -(C₀ ^ 2 / (4 * K)) from by ring]


  have h_n14_le_sqrt : (n : ℝ) ^ ((1:ℝ)/4) ≤ Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hn) (by norm_num)
  have h_mt_bound : m + t ≤ (K + C₀) * Real.sqrt n := by
    calc m + t = m + C₀ * (n : ℝ) ^ ((1:ℝ)/4) := rfl
      _ ≤ K * Real.sqrt n + C₀ * Real.sqrt n := by
          linarith [mul_le_mul_of_nonneg_left h_n14_le_sqrt (le_of_lt hC₀_pos)]
      _ = (K + C₀) * Real.sqrt n := by ring
  have h_exp_upper : Real.exp (-(t ^ 2) / (4 * (m + t))) ≤
      Real.exp (-(C₀ ^ 2) / (4 * (K + C₀))) := by
    apply Real.exp_le_exp.mpr
    rw [h_t_sq]
    have hmt_pos : (0 : ℝ) < m + t := by linarith [ht_pos]
    have h1 : C₀ ^ 2 * Real.sqrt n / (4 * (m + t)) ≥
        C₀ ^ 2 / (4 * (K + C₀)) := by
      rw [ge_iff_le, div_le_div_iff₀ (by positivity : (0:ℝ) < 4 * (K + C₀))
        (by positivity : (0:ℝ) < 4 * (m + t))]
      nlinarith [sq_nonneg C₀]
    linarith [neg_le_neg h1.le,
      show -(C₀ ^ 2 * Real.sqrt n) / (4 * (m + t)) =
        -(C₀ ^ 2 * Real.sqrt n / (4 * (m + t))) from by ring,
      show -(C₀ ^ 2) / (4 * (K + C₀)) =
        -(C₀ ^ 2 / (4 * (K + C₀))) from by ring]

  calc (Measure.pi μ {x | |f x - m| > t}).toReal
      ≤ (Measure.pi μ {x | f x ≤ m - t}).toReal +
          (Measure.pi μ {x | f x ≥ m + t}).toReal := h_meas_le
    _ ≤ 2 * Real.exp (-(t ^ 2) / (4 * m)) +
          2 * Real.exp (-(t ^ 2) / (4 * (m + t))) := by linarith
    _ ≤ 2 * Real.exp (-(C₀ ^ 2) / (4 * K)) +
          2 * Real.exp (-(C₀ ^ 2) / (4 * (K + C₀))) := by
        nlinarith [Real.exp_pos (-(t ^ 2) / (4 * m)),
          Real.exp_pos (-(t ^ 2) / (4 * (m + t)))]
    _ ≤ ε := hC₀_bound

end TalagrandCertifiable
