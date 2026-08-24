/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Moments.SubGaussian

set_option maxHeartbeats 800000

open MeasureTheory Filter Set SimpleGraph

noncomputable section

namespace ShamirSpencer

/-- The discrete $\sigma$-algebra (every subset is measurable) on the finite set of simple
graphs on $\{0, 1, \dots, n-1\}$. -/
scoped instance instMeasurableSpaceSimpleGraph (n : ℕ) : MeasurableSpace (SimpleGraph (Fin n)) := ⊤

/-- The Erdős–Rényi random graph measure $G(n, p)$ on simple graphs over $\{0, \dots, n-1\}$,
where each edge is included independently with probability $p \in [0, 1]$. -/
noncomputable def erdosRenyiMeasure (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
  Measure (SimpleGraph (Fin n)) := by sorry

/-- The Erdős–Rényi measure $G(n, p)$ is a probability measure on simple graphs. -/
theorem erdosRenyiMeasure_isProbability (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
  IsProbabilityMeasure (erdosRenyiMeasure n p hp hp1) := by sorry

/-- The chromatic number $\chi(G)$ of a finite simple graph $G$ on $\{0, \dots, n-1\}$ as a
natural number (converted from the `ℕ∞`-valued chromatic number in Mathlib via `ENat.toNat`). -/
noncomputable def chromaticNumberNat (n : ℕ) (G : SimpleGraph (Fin n)) : ℕ :=
  G.chromaticNumber.toNat

/-- The probability $\mathbb{P}_{G(n,p)}(E)$ of an event $E$ under the Erdős–Rényi measure
$G(n, p)$, returned as a real number via `ENNReal.toReal`. -/
noncomputable def probEvent (n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (E : Set (SimpleGraph (Fin n))) : ℝ :=
  ((erdosRenyiMeasure n p hp hp1) E).toReal

/-- If $G[\bar S]$ is $u$-colourable and $G[S]$ is $3$-colourable, then $G$ itself is
$(u + 3)$-colourable: combine the two colourings using disjoint palettes. -/
lemma colorable_of_induce_compl_colorable {n : ℕ} (G : SimpleGraph (Fin n))
    (u : ℕ) (S : Finset (Fin n))
    (h1 : (G.induce (↑Sᶜ : Set (Fin n))).Colorable u)
    (h2 : (G.induce (↑S : Set (Fin n))).Colorable 3) :
    G.Colorable (u + 3) := by
  obtain ⟨c1⟩ := h1
  obtain ⟨c2⟩ := h2
  constructor
  refine ⟨fun v => ?_, ?_⟩
  · by_cases hv : (v : Fin n) ∈ S
    · exact ⟨u + (c2 ⟨v, hv⟩).val, by omega⟩
    · have hv' : v ∈ (↑Sᶜ : Set (Fin n)) := by simp [hv]
      exact ⟨(c1 ⟨v, hv'⟩).val, by omega⟩
  · intro v w hvw
    simp only
    by_cases hv : v ∈ S <;> by_cases hw : w ∈ S
    · simp [hv, hw]
      have hadj : (G.induce (↑S : Set (Fin n))).Adj ⟨v, hv⟩ ⟨w, hw⟩ := by
        rw [induce_adj]; exact hvw
      have := c2.valid hadj
      simp [Ne, Fin.ext_iff] at this
      omega
    · simp [hv, hw]
      omega
    · simp [hv, hw]
      omega
    · simp [hv, hw]
      have hv' : v ∈ (↑Sᶜ : Set (Fin n)) := by simp [hv]
      have hw' : w ∈ (↑Sᶜ : Set (Fin n)) := by simp [hw]
      have hadj : (G.induce (↑Sᶜ : Set (Fin n))).Adj ⟨v, hv'⟩ ⟨w, hw'⟩ := by
        rw [induce_adj]; exact hvw
      have := c1.valid hadj
      simp [Ne, Fin.ext_iff] at this
      omega

/-- Corollary of `colorable_of_induce_compl_colorable`: under the same hypotheses,
$\chi(G) \le u + 3$. -/
lemma chromaticNumberNat_le_of_deletion {n : ℕ} (G : SimpleGraph (Fin n))
    (u : ℕ) (S : Finset (Fin n))
    (h1 : (G.induce (↑Sᶜ : Set (Fin n))).Colorable u)
    (h2 : (G.induce (↑S : Set (Fin n))).Colorable 3) :
    chromaticNumberNat n G ≤ u + 3 :=
  ENat.toNat_le_of_le_coe (colorable_of_induce_compl_colorable G u S h1 h2).chromaticNumber_le

/-- Set-level lemma underlying the Shamir–Spencer concentration argument: the intersection of
the three events (existence of a small "deletion set" $S$ making $G[\bar S]$ $u$-colourable,
all small $S$ make $G[S]$ $3$-colourable, and $\chi(G) \ge u$) is contained in the event
$\{u \le \chi(G) \le u + 3\}$. -/
lemma three_events_subset (n : ℕ) (u : ℕ) (C : ℝ) :
    ({G : SimpleGraph (Fin n) | ∃ S : Finset (Fin n), (S.card : ℝ) ≤ C * Real.sqrt (↑n) ∧
        (G.induce (↑Sᶜ : Set (Fin n))).Colorable u} ∩
     {G | ∀ S : Finset (Fin n), (S.card : ℝ) ≤ C * Real.sqrt (↑n) →
        (G.induce (↑S : Set (Fin n))).Colorable 3} ∩
     {G | u ≤ chromaticNumberNat n G}) ⊆
    {G | u ≤ chromaticNumberNat n G ∧ chromaticNumberNat n G ≤ u + 3} := by
  intro G hG
  obtain ⟨⟨hG1, hG2⟩, hG3⟩ := hG
  obtain ⟨S, hS_card, hS_col⟩ := hG1
  exact ⟨hG3, chromaticNumberNat_le_of_deletion G u S hS_col (hG2 S hS_card)⟩

/-- **Shamir–Spencer four-value concentration of the chromatic number.** For sparse Erdős–Rényi
graphs $G(n, p)$ with $p < n^{-\alpha}$ and $\alpha > 5/6$, there exists a sequence $u(n)$ such
that with probability at least $1 - 3\varepsilon$, $u(n) \le \chi(G) \le u(n) + 3$ for all
sufficiently large $n$. The proof combines the Azuma-type bounded-difference inequality with
a $3$-colourability property of small induced subgraphs. -/
theorem shamir_spencer_chromatic_four_concentration
    (_α : ℝ) (_hα : _α > 5/6)
    (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n) (hp1 : ∀ n, p n ≤ 1)
    (_hpn : ∀ᶠ n in atTop, p n < (n : ℝ) ^ (-_α))
    (ε : ℝ) (_hε : 0 < ε) (_hε1 : ε < 1)

    (h_bounded_diff : ∀ n₀ : ℕ, ∀ u : ℕ,
      probEvent n₀ (p n₀) (hp n₀) (hp1 n₀) {G | chromaticNumberNat n₀ G ≤ u} > ε →
      probEvent n₀ (p n₀) (hp n₀) (hp1 n₀)
        {G | ∃ S : Finset (Fin n₀),
          (S.card : ℝ) ≤ 2 * Real.sqrt (-Real.log ε / 2) * Real.sqrt (↑n₀) ∧
          (G.induce (↑Sᶜ : Set (Fin n₀))).Colorable u} ≥ 1 - ε)

    (h_three_col : ∀ᶠ n₀ in atTop,
      probEvent n₀ (p n₀) (hp n₀) (hp1 n₀)
        {G | ∀ S : Finset (Fin n₀),
          (S.card : ℝ) ≤ 2 * Real.sqrt (-Real.log ε / 2) * Real.sqrt (↑n₀) →
          (G.induce (↑S : Set (Fin n₀))).Colorable 3} ≥ 1 - ε)

    (h_exists_u : ∀ n₀ : ℕ, ∃ u : ℕ,
      probEvent n₀ (p n₀) (hp n₀) (hp1 n₀) {G | chromaticNumberNat n₀ G ≤ u} > ε ∧
      probEvent n₀ (p n₀) (hp n₀) (hp1 n₀) {G | u ≤ chromaticNumberNat n₀ G} ≥ 1 - ε) :
    ∃ u : ℕ → ℕ, ∀ᶠ n in atTop,
      probEvent n (p n) (hp n) (hp1 n)
        {G | u n ≤ chromaticNumberNat n G ∧ chromaticNumberNat n G ≤ u n + 3} ≥ 1 - 3 * ε := by

  choose u hu using h_exists_u
  use u

  apply h_three_col.mono
  intro n₀ h_3col_n
  obtain ⟨hu_prob, hu_ge⟩ := hu n₀

  have hev1 := h_bounded_diff n₀ (u n₀) hu_prob

  set C := 2 * Real.sqrt (-Real.log ε / 2)
  set A := {G : SimpleGraph (Fin n₀) | ∃ S : Finset (Fin n₀),
    (S.card : ℝ) ≤ C * Real.sqrt (↑n₀) ∧
    (G.induce (↑Sᶜ : Set (Fin n₀))).Colorable (u n₀)}
  set B := {G : SimpleGraph (Fin n₀) | ∀ S : Finset (Fin n₀),
    (S.card : ℝ) ≤ C * Real.sqrt (↑n₀) →
    (G.induce (↑S : Set (Fin n₀))).Colorable 3}
  set D := {G : SimpleGraph (Fin n₀) | u n₀ ≤ chromaticNumberNat n₀ G}
  have hsubset := three_events_subset n₀ (u n₀) C

  unfold probEvent at *
  have hμ := erdosRenyiMeasure_isProbability n₀ (p n₀) (hp n₀) (hp1 n₀)
  set μ := erdosRenyiMeasure n₀ (p n₀) (hp n₀) (hp1 n₀)

  have hT_mono : (μ (A ∩ B ∩ D)).toReal ≤
      (μ {G | u n₀ ≤ chromaticNumberNat n₀ G ∧ chromaticNumberNat n₀ G ≤ u n₀ + 3}).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset)

  have hApC : (μ A).toReal + (μ Aᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top μ A) (measure_ne_top μ Aᶜ)]
    rw [prob_add_prob_compl (MeasurableSpace.measurableSet_top)]; simp
  have hBpC : (μ B).toReal + (μ Bᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top μ B) (measure_ne_top μ Bᶜ)]
    rw [prob_add_prob_compl (MeasurableSpace.measurableSet_top)]; simp
  have hDpC : (μ D).toReal + (μ Dᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top μ D) (measure_ne_top μ Dᶜ)]
    rw [prob_add_prob_compl (MeasurableSpace.measurableSet_top)]; simp
  have hABDpC : (μ (A ∩ B ∩ D)).toReal + (μ (A ∩ B ∩ D)ᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
    rw [prob_add_prob_compl (MeasurableSpace.measurableSet_top)]; simp
  have hAc : (μ Aᶜ).toReal ≤ ε := by linarith
  have hBc : (μ Bᶜ).toReal ≤ ε := by linarith
  have hDc : (μ Dᶜ).toReal ≤ ε := by linarith
  have hsubset_compl : (A ∩ B ∩ D)ᶜ ⊆ Aᶜ ∪ Bᶜ ∪ Dᶜ := by
    intro x hx; simp at hx ⊢; tauto
  have h_compl : μ (A ∩ B ∩ D)ᶜ ≤ μ Aᶜ + μ Bᶜ + μ Dᶜ := by
    calc μ (A ∩ B ∩ D)ᶜ ≤ μ (Aᶜ ∪ Bᶜ ∪ Dᶜ) := measure_mono hsubset_compl
      _ ≤ μ (Aᶜ ∪ Bᶜ) + μ Dᶜ := measure_union_le _ _
      _ ≤ (μ Aᶜ + μ Bᶜ) + μ Dᶜ := by gcongr; exact measure_union_le _ _
  have hfin : μ Aᶜ + μ Bᶜ + μ Dᶜ ≠ ⊤ := by
    simp [measure_ne_top]
  have h_compl_real : (μ (A ∩ B ∩ D)ᶜ).toReal ≤ (μ Aᶜ + μ Bᶜ + μ Dᶜ).toReal :=
    ENNReal.toReal_le_toReal (measure_ne_top μ _) hfin |>.mpr h_compl
  have h_sum : (μ Aᶜ + μ Bᶜ + μ Dᶜ).toReal =
      (μ Aᶜ).toReal + (μ Bᶜ).toReal + (μ Dᶜ).toReal := by
    rw [ENNReal.toReal_add (by simp [measure_ne_top]) (measure_ne_top μ _)]
    rw [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)]
  linarith

end ShamirSpencer

namespace Martingales

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

/-- **Definition 9.2.1** (Martingale). A sequence $(Z_n)_{n \ge 0}$ is a martingale with respect
to a filtration $(\mathcal F_n)$ and probability measure $\mu$ if each $Z_n$ is
$\mathcal F_n$-measurable, integrable, and $\mathbb{E}[Z_{n+1} \mid \mathcal F_n] = Z_n$.
This is a thin wrapper around Mathlib's `MeasureTheory.Martingale`. -/
def IsMartingale {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : MeasureTheory.Measure Ω) (ℱ : MeasureTheory.Filtration ℕ m0)
    (Z : ℕ → Ω → ℝ) : Prop :=
  MeasureTheory.Martingale Z ℱ μ

/-- Helper for Azuma's inequality: the martingale-difference process
$i \mapsto Z_{i+1} - Z_i$ is strongly adapted to the filtration $\mathcal F$. -/
theorem azuma_inequality_adapted
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [StandardBorelSpace Ω]
    {ℱ : MeasureTheory.Filtration ℕ mΩ}
    {Z : ℕ → Ω → ℝ}
    (hmart : MeasureTheory.Martingale Z ℱ μ)
    (n : ℕ) (hbdd : ∀ i, i < n → ∀ᵐ ω ∂μ, |Z (i + 1) ω - Z i ω| ≤ 1) :
    MeasureTheory.StronglyAdapted ℱ (fun i ω => Z (i + 1) ω - Z i ω) := by sorry

/-- Helper for Azuma's inequality: the first martingale increment $Z_1 - Z_0$ is sub-Gaussian
with parameter $1$ when the increments satisfy $|Z_{i+1} - Z_i| \le 1$. -/
theorem azuma_inequality_hasSubgaussianMGF
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [StandardBorelSpace Ω]
    {ℱ : MeasureTheory.Filtration ℕ mΩ}
    {Z : ℕ → Ω → ℝ}
    (hmart : MeasureTheory.Martingale Z ℱ μ)
    (n : ℕ) (hbdd : ∀ i, i < n → ∀ᵐ ω ∂μ, |Z (i + 1) ω - Z i ω| ≤ 1) :
    ProbabilityTheory.HasSubgaussianMGF (fun ω => Z 1 ω - Z 0 ω) 1 μ := by sorry

/-- Helper for Azuma's inequality: each subsequent martingale increment
$Z_{i+2} - Z_{i+1}$ is conditionally sub-Gaussian (parameter $1$) given $\mathcal F_i$. -/
theorem azuma_inequality_hasCondSubgaussianMGF
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [StandardBorelSpace Ω]
    {ℱ : MeasureTheory.Filtration ℕ mΩ}
    {Z : ℕ → Ω → ℝ}
    (hmart : MeasureTheory.Martingale Z ℱ μ)
    (n : ℕ) (hbdd : ∀ i, i < n → ∀ᵐ ω ∂μ, |Z (i + 1) ω - Z i ω| ≤ 1) :
    ∀ i, i < n - 1 →
      ProbabilityTheory.HasCondSubgaussianMGF (↑(ℱ i)) (ℱ.le i)
        (fun ω => Z (i + 2) ω - Z (i + 1) ω) 1 μ := by sorry

/-- **Azuma's inequality** (Theorem 9.2.7 / 9.2.8). For a martingale $(Z_n)$ with bounded
increments $|Z_{i+1} - Z_i| \le 1$, the upper tail satisfies
$\mathbb{P}(Z_n - Z_0 \ge t\sqrt{n}) \le \exp(-t^{2}/2)$ for every $t > 0$. -/
theorem azuma_inequality
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [StandardBorelSpace Ω]
    {ℱ : MeasureTheory.Filtration ℕ mΩ}
    {Z : ℕ → Ω → ℝ}
    (hmart : MeasureTheory.Martingale Z ℱ μ)
    (n : ℕ) (hn : 0 < n)
    (hbdd : ∀ i, i < n → ∀ᵐ ω ∂μ, |Z (i + 1) ω - Z i ω| ≤ 1)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | Z n ω - Z 0 ω ≥ t * Real.sqrt n} ≤ Real.exp (-t ^ 2 / 2) := by
  have h_adapted := azuma_inequality_adapted hmart n hbdd
  have h0 := azuma_inequality_hasSubgaussianMGF hmart n hbdd
  have h_subG := azuma_inequality_hasCondSubgaussianMGF hmart n hbdd
  set Y : ℕ → Ω → ℝ := fun i ω => Z (i + 1) ω - Z i ω
  have htelescope : ∀ ω, Z n ω - Z 0 ω = ∑ i ∈ Finset.range n, Y i ω :=
    fun ω => (Finset.sum_range_sub (fun i => Z i ω) n).symm
  have hset_eq : {ω | Z n ω - Z 0 ω ≥ t * Real.sqrt n} =
      {ω | t * Real.sqrt n ≤ ∑ i ∈ Finset.range n, Y i ω} := by
    ext ω; simp only [Set.mem_setOf_eq, ge_iff_le, htelescope ω]
  rw [hset_eq]
  have hε : (0 : ℝ) ≤ t * Real.sqrt n := by positivity
  have hmain := ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF
    (cY := fun _ => 1) h_adapted h0 n h_subG hε
  refine hmain.trans (Real.exp_le_exp.mpr ?_)
  have hsum_c : (∑ i ∈ Finset.range n, (1 : ℝ≥0)) = (n : ℝ≥0) := by
    simp [Finset.sum_const, Finset.card_range]
  rw [hsum_c]; simp only [NNReal.coe_natCast]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn)
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg' n)]
  rw [show -(t ^ 2 * ↑n) = -t ^ 2 * ↑n from by ring]
  rw [mul_div_mul_right _ _ hn']

/-- **Azuma's inequality, weighted form.** With increments bounded by $|Z_{i+1} - Z_i| \le c_i$
and sub-Gaussian parameters $\sigma_i = c_i^{2}$, one has
$\mathbb{P}(Z_n - Z_0 \ge t) \le \exp\!\big({-t^{2} / (2\sum_i c_i^{2})}\big)$ for $t > 0$. -/
theorem azuma_inequality_alt
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [StandardBorelSpace Ω]
    {ℱ : MeasureTheory.Filtration ℕ mΩ}
    {Z : ℕ → Ω → ℝ}
    (hmart : MeasureTheory.Martingale Z ℱ μ)
    (n : ℕ)
    (c : Fin n → ℝ)
    (hc_pos : ∀ i, 0 ≤ c i)
    (hbdd : ∀ i : Fin n, ∀ᵐ ω ∂μ, |Z (↑i + 1) ω - Z ↑i ω| ≤ c i)
    (h_adapted : MeasureTheory.StronglyAdapted ℱ (fun i ω => Z (i + 1) ω - Z i ω))

    (σ : ℕ → ℝ≥0)
    (hσ : ∀ i (hi : i < n), (σ i : ℝ) = c ⟨i, hi⟩ ^ 2)

    (h0 : ProbabilityTheory.HasSubgaussianMGF (fun ω => Z 1 ω - Z 0 ω) (σ 0) μ)
    (h_subG : ∀ i, i < n - 1 →
      ProbabilityTheory.HasCondSubgaussianMGF (↑(ℱ i)) (ℱ.le i)
        (fun ω => Z (i + 2) ω - Z (i + 1) ω) (σ (i + 1)) μ)
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | Z n ω - Z 0 ω ≥ t} ≤
      Real.exp (-t ^ 2 / (2 * ∑ i : Fin n, c i ^ 2)) := by
  set Y : ℕ → Ω → ℝ := fun i ω => Z (i + 1) ω - Z i ω
  have htelescope : ∀ ω, Z n ω - Z 0 ω = ∑ i ∈ Finset.range n, Y i ω :=
    fun ω => (Finset.sum_range_sub (fun i => Z i ω) n).symm
  have hset_eq : {ω | Z n ω - Z 0 ω ≥ t} =
      {ω | t ≤ ∑ i ∈ Finset.range n, Y i ω} := by
    ext ω; simp only [Set.mem_setOf_eq, ge_iff_le, htelescope ω]
  rw [hset_eq]
  have hε : (0 : ℝ) ≤ t := le_of_lt ht
  have hmain := ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF
    (cY := σ) h_adapted h0 n h_subG hε
  refine hmain.trans (Real.exp_le_exp.mpr ?_)


  suffices h : (↑(∑ i ∈ Finset.range n, σ i) : ℝ) = ∑ i : Fin n, c i ^ 2 by rw [h]
  rw [NNReal.coe_sum]
  have hfin : ∑ i : Fin n, c i ^ 2 = ∑ i ∈ Finset.range n,
      (if h : i < n then c ⟨i, h⟩ ^ 2 else 0) := Finset.sum_fin_eq_sum_range ..
  rw [hfin]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dif_pos (Finset.mem_range.mp hi)]
  exact hσ i (Finset.mem_range.mp hi)

open Finset in

/-- The Hoeffding sub-Gaussian parameter $c^{2}/4$ for a centred random variable bounded in an
interval of length $c$, packaged as a non-negative real. -/
noncomputable def hoeffdingSubGParam (c : ℝ) (_ : 0 ≤ c) : ℝ≥0 :=
  ⟨c ^ 2 / 4, by positivity⟩

open Set in
/-- **Hoeffding's lemma** (Lemma 9.2.12). If $X$ is a centred random variable taking values in
$[a, a + \ell]$, then its moment generating function satisfies
$\mathbb{E}[e^{tX}] \le \exp(t^{2} \ell^{2} / 8)$ for all $t \in \mathbb{R}$. -/
theorem hoeffding_lemma {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (hE : ∫ ω, X ω ∂μ = 0)
    (a ℓ : ℝ) (hℓ : 0 ≤ ℓ) (hbnd : ∀ᵐ ω ∂μ, a ≤ X ω ∧ X ω ≤ a + ℓ)
    (t : ℝ) : ∫ ω, Real.exp (t * X ω) ∂μ ≤ Real.exp (t ^ 2 * ℓ ^ 2 / 8) := by

  have hIcc : ∀ᵐ ω ∂μ, X ω ∈ Icc a (a + ℓ) := by
    filter_upwards [hbnd] with ω ⟨h1, h2⟩; exact ⟨h1, h2⟩


  have hSubG := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hX hIcc hE

  have hmgf := hSubG.mgf_le t
  simp only [mgf] at hmgf


  refine hmgf.trans (Real.exp_le_exp.mpr ?_)
  have hab : (a + ℓ) - a = ℓ := by ring
  rw [hab]
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat]
  rw [Real.nnnorm_of_nonneg hℓ]
  push_cast
  linarith

open MeasureTheory.Measure in

/-- **Azuma–Doob martingale concentration (sub-Gaussian form).** For an adapted sequence $(Y_i)$
with sub-Gaussian (resp. conditionally sub-Gaussian given $\mathcal F_i$) MGFs of Hoeffding
parameter $c_i^{2}/4$, the partial sum satisfies
$\mathbb{P}\!\big(\sum_i Y_i \ge \varepsilon\big) \le \exp\!\big({-2\varepsilon^{2} / \sum_i c_i^{2}}\big)$
for every $\varepsilon \ge 0$. -/
theorem azuma_doob_martingale_subG
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {ℱ : MeasureTheory.Filtration ℕ mΩ}
    {Y : ℕ → Ω → ℝ} {c : ℕ → ℝ}
    (hc : ∀ i, 0 ≤ c i)
    (h_adapted : MeasureTheory.StronglyAdapted ℱ Y)
    (h0 : ProbabilityTheory.HasSubgaussianMGF (Y 0) (hoeffdingSubGParam (c 0) (hc 0)) μ)
    (n : ℕ)
    (h_subG : ∀ i, i < n - 1 →
      ProbabilityTheory.HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1))
        (hoeffdingSubGParam (c (i + 1)) (hc (i + 1))) μ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω} ≤
      Real.exp (-2 * ε ^ 2 / ∑ i ∈ Finset.range n, c i ^ 2) := by


  set cY : ℕ → ℝ≥0 := fun i => hoeffdingSubGParam (c i) (hc i) with hcY_def
  have hmain := ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF
    (ℱ := ℱ) (cY := cY) h_adapted h0 n h_subG hε


  refine hmain.trans (Real.exp_le_exp.mpr ?_)


  have hcY_eq : (↑(∑ i ∈ Finset.range n, cY i) : ℝ) = (∑ i ∈ Finset.range n, c i ^ 2) / 4 := by
    rw [NNReal.coe_sum]
    simp only [hcY_def, hoeffdingSubGParam, NNReal.coe_mk]
    rw [Finset.sum_div]
  rw [hcY_eq]
  by_cases hS : ∑ x ∈ Finset.range n, c x ^ 2 = 0
  · simp [hS]
  · rw [show (2 : ℝ) * ((∑ x ∈ Finset.range n, c x ^ 2) / 4) =
        (∑ x ∈ Finset.range n, c x ^ 2) / 2 by ring]
    rw [show -ε ^ 2 / ((∑ x ∈ Finset.range n, c x ^ 2) / 2) =
        -2 * ε ^ 2 / ∑ x ∈ Finset.range n, c x ^ 2 by field_simp]

/-- A centred random variable supported in an interval $[a_0, a_0 + c]$ has a sub-Gaussian MGF
with the Hoeffding parameter $c^{2}/4$. -/
theorem hasSubgaussianMGF_of_bounded
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h_mean : ∫ ω, X ω ∂μ = 0)
    (h_meas : AEMeasurable X μ)
    (h_bnd : ∃ a₀ : ℝ, ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a₀ (a₀ + c)) :
    HasSubgaussianMGF X (hoeffdingSubGParam c hc) μ := by
  obtain ⟨a₀, ha₀⟩ := h_bnd
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero h_meas ha₀ h_mean
  rw [show a₀ + c - a₀ = c from by ring] at h
  have hparam : (‖c‖₊ / 2) ^ 2 = hoeffdingSubGParam c hc := by
    unfold hoeffdingSubGParam
    rw [Real.nnnorm_of_nonneg hc]
    ext
    push_cast
    ring
  rwa [hparam] at h

/-- Conditional version of `hasSubgaussianMGF_of_bounded`: a variable with vanishing conditional
mean given $m$ and contained in an interval $[a(\omega), a(\omega) + c]$ (with $a$ being
$m$-measurable) has a conditionally sub-Gaussian MGF with the Hoeffding parameter $c^{2}/4$. -/
theorem hasCondSubgaussianMGF_of_condBounded
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {X : Ω → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h_condMean : μ[X|m] =ᵐ[μ] 0)
    (h_bnd : ∃ a : Ω → ℝ, @Measurable Ω ℝ m _ a ∧
      ∀ᵐ ω ∂μ, X ω ∈ Set.Icc (a ω) (a ω + c)) :
    HasCondSubgaussianMGF m hm X (hoeffdingSubGParam c hc) μ := by sorry

/-- **Azuma's inequality for a Doob martingale** (Theorem 9.2.9). If the increments
$Y_i$ are centred (conditionally on $\mathcal F_{i-1}$) and lie in intervals of length $c_i$,
then $\mathbb{P}\!\big(\sum_i Y_i \ge \varepsilon\big) \le
\exp\!\big({-2\varepsilon^{2} / \sum_i c_i^{2}}\big)$. -/
theorem azuma_doob_martingale
    {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {ℱ : MeasureTheory.Filtration ℕ mΩ}
    {Y : ℕ → Ω → ℝ} {c : ℕ → ℝ}
    (hc : ∀ i, 0 ≤ c i)
    (h_adapted : MeasureTheory.StronglyAdapted ℱ Y)
    (h_mean0 : ∫ ω, Y 0 ω ∂μ = 0)
    (h_meas0 : AEMeasurable (Y 0) μ)
    (h_bnd0 : ∃ a₀ : ℝ, ∀ᵐ ω ∂μ, Y 0 ω ∈ Set.Icc a₀ (a₀ + c 0))
    (n : ℕ)
    (h_condMean : ∀ i, i < n - 1 → μ[Y (i + 1)|ℱ i] =ᵐ[μ] 0)
    (h_bnd : ∀ i, i < n - 1 → ∃ a : Ω → ℝ, @Measurable Ω ℝ (ℱ i) _ a ∧
      ∀ᵐ ω ∂μ, Y (i + 1) ω ∈ Set.Icc (a ω) (a ω + c (i + 1)))
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω} ≤
      Real.exp (-2 * ε ^ 2 / ∑ i ∈ Finset.range n, c i ^ 2) := by

  have h0 : HasSubgaussianMGF (Y 0) (hoeffdingSubGParam (c 0) (hc 0)) μ :=
    hasSubgaussianMGF_of_bounded (hc 0) h_mean0 h_meas0 h_bnd0
  have h_subG : ∀ i, i < n - 1 →
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1))
        (hoeffdingSubGParam (c (i + 1)) (hc (i + 1))) μ :=
    fun i hi => hasCondSubgaussianMGF_of_condBounded (ℱ i) (ℱ.le i) (hc (i + 1))
      (h_condMean i hi) (h_bnd i hi)
  exact azuma_doob_martingale_subG hc h_adapted h0 n h_subG hε

end Martingales
