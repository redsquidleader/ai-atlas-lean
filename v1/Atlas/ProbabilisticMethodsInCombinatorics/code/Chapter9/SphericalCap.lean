/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.LevyIsoperimetric
set_option maxHeartbeats 400000

noncomputable section

open Real Set MeasureTheory

namespace SphericalCap

/-- The $(n-1)$-dimensional Hausdorff measure on the unit sphere $S^{n-1}$, serving as the
unnormalized surface-area measure used to define `normalizedSphereMeasure`. -/
def sphereVolume (n : ℕ) :
    Measure (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) :=
  Measure.hausdorffMeasure (↑(n - 1) : ℝ)

/-- The total $(n-1)$-Hausdorff surface measure of the sphere $S^{n-1}$ is finite. -/
theorem sphereVolume_univ_ne_top (n : ℕ) : sphereVolume n Set.univ ≠ ⊤ := by sorry

/-- The **uniform probability measure** on $S^{n-1}$, defined by normalizing the
$(n-1)$-Hausdorff surface measure: $\mu(A) = \operatorname{vol}(A) / \operatorname{vol}(S^{n-1})$. -/
def normalizedSphereMeasure {n : ℕ}
    (A : Set (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))) : ℝ :=
  (sphereVolume n A).toReal / (sphereVolume n Set.univ).toReal

/-- The normalized sphere measure is monotone with respect to set inclusion. -/
theorem normalizedSphereMeasure_subset_mono {n : ℕ}
    {A B : Set (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))}
    (h : A ⊆ B) : normalizedSphereMeasure A ≤ normalizedSphereMeasure B := by
  unfold normalizedSphereMeasure
  exact div_le_div_of_nonneg_right
    (ENNReal.toReal_mono (ne_top_of_le_ne_top (sphereVolume_univ_ne_top n)
      (measure_mono (subset_univ B))) (measure_mono h)) ENNReal.toReal_nonneg

/-- Subadditivity (union bound) of the normalized sphere measure:
$\mu(A \cup B) \le \mu(A) + \mu(B)$. -/
theorem normalizedSphereMeasure_union_le {n : ℕ}
    (A B : Set (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))) :
    normalizedSphereMeasure (A ∪ B) ≤ normalizedSphereMeasure A + normalizedSphereMeasure B := by
  unfold normalizedSphereMeasure
  rw [show ∀ (a b c : ℝ), a / c + b / c = (a + b) / c from fun a b c => (add_div a b c).symm]
  apply div_le_div_of_nonneg_right _ ENNReal.toReal_nonneg
  have hA_fin : sphereVolume n A ≠ ⊤ :=
    ne_top_of_le_ne_top (sphereVolume_univ_ne_top n) (measure_mono (subset_univ A))
  have hB_fin : sphereVolume n B ≠ ⊤ :=
    ne_top_of_le_ne_top (sphereVolume_univ_ne_top n) (measure_mono (subset_univ B))
  rw [← ENNReal.toReal_add hA_fin hB_fin]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hA_fin, hB_fin⟩)
    (measure_union_le A B)

/-- The normalized measure of the spherical cap $\{x \in S^{n-1} \mid x_1 \ge \varepsilon\}$,
i.e. $\mathbb{P}_{x \sim S^{n-1}}(x_1 \ge \varepsilon)$ (with the convention that the value is
$0$ when $n = 0$). -/
def sphericalCapMeasure (n : ℕ) (ε : ℝ) : ℝ :=
  if h : 0 < n then
    normalizedSphereMeasure
      {x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) |
        (x : EuclideanSpace ℝ (Fin n)) ⟨0, h⟩ ≥ ε}
  else 0

set_option maxHeartbeats 800000 in
/-- For $\varepsilon > 1$ the cap $\{x \in S^{n-1} \mid x_1 \ge \varepsilon\}$ is empty,
hence has measure $0$. -/
theorem sphericalCapMeasure_eq_zero_of_gt_one (n : ℕ) (ε : ℝ) (hε : ε > 1) :
    sphericalCapMeasure n ε = 0 := by
  unfold sphericalCapMeasure
  split
  case isTrue h =>
    unfold normalizedSphereMeasure
    have h_empty : {x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) |
        (x : EuclideanSpace ℝ (Fin n)) ⟨0, h⟩ ≥ ε} = ∅ := by
      ext ⟨x, hx_mem⟩
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_le]
      rw [Metric.mem_sphere, dist_zero_right] at hx_mem
      have hx_norm : ‖x‖ = 1 := hx_mem
      have h_norm_sq : ‖x‖ ^ 2 = ∑ i : Fin n, ‖x i‖ ^ 2 :=
        EuclideanSpace.norm_sq_eq x
      have h1 : ‖x ⟨0, h⟩‖ ^ 2 ≤ ∑ i : Fin n, ‖x i‖ ^ 2 :=
        Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2) (fun i _ => sq_nonneg _)
          (Finset.mem_univ (⟨0, h⟩ : Fin n))
      have h2 : ∑ i : Fin n, ‖x i‖ ^ 2 = 1 := by
        rw [← h_norm_sq, hx_norm]; norm_num
      have h3 : ‖x ⟨0, h⟩‖ ^ 2 ≤ 1 := by linarith
      have h4 : ‖x ⟨0, h⟩‖ ≤ 1 := by
        nlinarith [norm_nonneg (x ⟨0, h⟩)]
      have h5 : |x ⟨0, h⟩| ≤ 1 := by rwa [Real.norm_eq_abs] at h4
      linarith [le_abs_self (x ⟨0, h⟩)]
    rw [h_empty, show sphereVolume n ∅ = 0 from measure_empty]
    simp
  case isFalse => rfl

/-- **Spherical cap bound, small-$\varepsilon$ regime** ($0 \le \varepsilon \le 1/\sqrt{2}$):
$\mathbb{P}(x_1 \ge \varepsilon) \le (1 - \varepsilon^{2})^{n/2}$. -/
theorem sphericalCapMeasure_le_case1 (n : ℕ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / Real.sqrt 2) :
    sphericalCapMeasure n ε ≤ (Real.sqrt (1 - ε ^ 2)) ^ n := by sorry

/-- **Spherical cap bound, large-$\varepsilon$ regime** ($1/\sqrt{2} \le \varepsilon \le 1$):
$\mathbb{P}(x_1 \ge \varepsilon) \le \big(1/(2\varepsilon)\big)^{n}$. -/
theorem sphericalCapMeasure_le_case2 (n : ℕ) (ε : ℝ)
    (hε_lb : 1 / Real.sqrt 2 ≤ ε) (hε_ub : ε ≤ 1) :
    sphericalCapMeasure n ε ≤ (1 / (2 * ε)) ^ n := by sorry

/-- Real analysis lemma: $\sqrt{1 - \varepsilon^{2}} \le \exp(-\varepsilon^{2}/2)$,
obtained from $1 - x \le e^{-x}$ and the identity $\sqrt{e^{-t}} = e^{-t/2}$. -/
theorem sqrt_one_sub_sq_le_exp (ε : ℝ) :
    Real.sqrt (1 - ε ^ 2) ≤ Real.exp (-(ε ^ 2 / 2)) := by
  have h_key : 1 - ε ^ 2 ≤ Real.exp (-(ε ^ 2)) := by
    have h := Real.add_one_le_exp (-(ε ^ 2))
    linarith
  have h_sqrt_exp : Real.sqrt (Real.exp (-(ε ^ 2))) = Real.exp (-(ε ^ 2 / 2)) := by
    rw [← Real.exp_half (-(ε ^ 2))]
    ring_nf
  calc Real.sqrt (1 - ε ^ 2)
      ≤ Real.sqrt (Real.exp (-(ε ^ 2))) := Real.sqrt_le_sqrt h_key
    _ = Real.exp (-(ε ^ 2 / 2)) := h_sqrt_exp

/-- Real analysis lemma: for $1/\sqrt{2} \le \varepsilon \le 1$,
$1/(2\varepsilon) \le \exp(-\varepsilon^{2}/2)$. -/
theorem inv_two_mul_le_exp (ε : ℝ) (hε_lb : 1 / Real.sqrt 2 ≤ ε) (hε_ub : ε ≤ 1) :
    1 / (2 * ε) ≤ Real.exp (-(ε ^ 2 / 2)) := by
  have hε_pos : (0 : ℝ) < ε := by
    have : (0 : ℝ) < 1 / Real.sqrt 2 := by positivity
    linarith
  have hsqrt2_sq : Real.sqrt 2 ^ 2 = 2 :=
    Real.sq_sqrt (show (0:ℝ) ≤ 2 from by norm_num)
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 2)
  have hε_sq_lb : (1 : ℝ) / 2 ≤ ε ^ 2 := by
    have h1 : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) ≤ ε * ε :=
      mul_le_mul hε_lb hε_lb (by positivity) (le_of_lt hε_pos)
    have h2 : (1 / Real.sqrt 2) * (1 / Real.sqrt 2) = 1 / 2 := by
      rw [← sq, div_pow, one_pow, hsqrt2_sq]
    nlinarith
  suffices h_main : Real.exp (ε ^ 2 / 2) ≤ 2 * ε by
    have h_exp_inv : Real.exp (-(ε ^ 2 / 2)) = (Real.exp (ε ^ 2 / 2))⁻¹ := by
      rw [Real.exp_neg]
    rw [h_exp_inv, show (1 : ℝ) / (2 * ε) = (2 * ε)⁻¹ from one_div _]
    exact inv_anti₀ (Real.exp_pos _) h_main
  have hε2_half_nonneg : (0 : ℝ) ≤ ε ^ 2 / 2 := by positivity
  have hε2_half_lt_one : ε ^ 2 / 2 < 1 := by nlinarith
  have h_exp_bound : Real.exp (ε ^ 2 / 2) ≤ 1 / (1 - ε ^ 2 / 2) :=
    Real.exp_bound_div_one_sub_of_interval hε2_half_nonneg hε2_half_lt_one
  suffices h2 : 1 / (1 - ε ^ 2 / 2) ≤ 2 * ε from le_trans h_exp_bound h2
  have h_denom_pos : (0 : ℝ) < 1 - ε ^ 2 / 2 := by nlinarith
  rw [div_le_iff₀ h_denom_pos]
  nlinarith [sq_nonneg (1 - ε)]

/-- Raising the bound $r \le e^{-\varepsilon^{2}/2}$ to the $n$-th power yields
$r^{n} \le \exp(-n \varepsilon^{2}/2)$. -/
theorem pow_le_exp_of_le {r ε : ℝ} {n : ℕ} (hr : 0 ≤ r)
    (h : r ≤ Real.exp (-(ε ^ 2 / 2))) :
    r ^ n ≤ Real.exp (-(↑n * ε ^ 2 / 2)) := by
  calc r ^ n
      ≤ (Real.exp (-(ε ^ 2 / 2))) ^ n := pow_le_pow_left₀ hr h n
    _ = Real.exp (↑n * (-(ε ^ 2 / 2))) := by rw [← Real.exp_nat_mul]
    _ = Real.exp (-(↑n * ε ^ 2 / 2)) := by congr 1; ring

/-- **Spherical cap concentration** (Theorem 9.4.11). For a uniformly random unit vector
$x \sim S^{n-1}$ and $\varepsilon \ge 0$,
$\mathbb{P}(x_1 \ge \varepsilon) \le \exp(-n \varepsilon^{2}/2)$. -/
theorem spherical_cap_bound (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε) :
    sphericalCapMeasure n ε ≤ Real.exp (-(↑n * ε ^ 2 / 2)) := by
  by_cases h1 : ε > 1
  ·
    rw [sphericalCapMeasure_eq_zero_of_gt_one n ε h1]
    exact le_of_lt (Real.exp_pos _)
  · simp only [not_lt] at h1
    by_cases h2 : ε ≤ 1 / Real.sqrt 2
    ·
      calc sphericalCapMeasure n ε
          ≤ (Real.sqrt (1 - ε ^ 2)) ^ n :=
            sphericalCapMeasure_le_case1 n ε hε h2
        _ ≤ Real.exp (-(↑n * ε ^ 2 / 2)) :=
            pow_le_exp_of_le (Real.sqrt_nonneg _) (sqrt_one_sub_sq_le_exp ε)
    ·
      simp only [not_le] at h2
      have hε_pos : (0 : ℝ) < ε :=
        lt_of_lt_of_le (by positivity : (0:ℝ) < 1 / Real.sqrt 2) (le_of_lt h2)
      calc sphericalCapMeasure n ε
          ≤ (1 / (2 * ε)) ^ n :=
            sphericalCapMeasure_le_case2 n ε (le_of_lt h2) h1
        _ ≤ Real.exp (-(↑n * ε ^ 2 / 2)) :=
            pow_le_exp_of_le (by positivity) (inv_two_mul_le_exp ε (le_of_lt h2) h1)

end SphericalCap

namespace SphericalCap

/-- Contrapositive helper: if the normalized measure of some set $A$ is positive, then the
total surface volume of $S^{n-1}$ is nonzero (i.e. the sphere is genuinely $(n-1)$-dimensional). -/
theorem sphereVolume_pos_of_normalizedSphereMeasure_pos {n : ℕ}
    {A : Set (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))}
    (h : normalizedSphereMeasure A > 0) : sphereVolume n Set.univ ≠ 0 := by
  intro h0
  have : normalizedSphereMeasure A = 0 := by
    unfold normalizedSphereMeasure
    have : (sphereVolume n Set.univ).toReal = 0 :=
      (ENNReal.toReal_eq_zero_iff _).mpr (Or.inl h0)
    rw [this, div_zero]
  linarith

/-- Probability complement: $\mu(A^c) = 1 - \mu(A)$ for the normalized sphere measure,
provided the total surface volume is nonzero. -/
theorem normalizedSphereMeasure_compl {n : ℕ}
    (A : Set (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)))
    (hA : MeasurableSet A) (hpos : sphereVolume n Set.univ ≠ 0) :
    normalizedSphereMeasure Aᶜ = 1 - normalizedSphereMeasure A := by
  unfold normalizedSphereMeasure
  have huniv_ne_top := sphereVolume_univ_ne_top n
  have huniv_pos := ENNReal.toReal_pos hpos huniv_ne_top
  have hA_fin : sphereVolume n A ≠ ⊤ :=
    ne_top_of_le_ne_top huniv_ne_top (measure_mono (subset_univ A))
  rw [measure_compl hA hA_fin]
  rw [ENNReal.toReal_sub_of_le (measure_mono (subset_univ A)) huniv_ne_top]
  rw [sub_div, div_self huniv_pos.ne']

/-- A set of positive normalized sphere measure is nonempty. -/
theorem normalizedSphereMeasure_nonempty_of_pos {n : ℕ}
    (A : Set (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)))
    (h : normalizedSphereMeasure A > 0) : A.Nonempty := by
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  have : normalizedSphereMeasure A = 0 := by
    unfold normalizedSphereMeasure
    rw [hempty, measure_empty, ENNReal.toReal_zero, zero_div]
  linarith

/-- Key intermediate step in the concentration of measure on $S^{n-1}$: if $\mu(A) \ge 1/2$,
then $1 - \mu(A_t) \le \mathbb{P}\!\big(x_1 \ge t/\sqrt{2}\big)$ for every $t \ge 0$,
obtained from Lévy's isoperimetric inequality. -/
theorem sphere_thickening_complement_bound {n : ℕ}
    (A : Set (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)))
    (hA : normalizedSphereMeasure A ≥ 1/2) (t : ℝ) (ht : 0 ≤ t) :
    1 - normalizedSphereMeasure (Metric.cthickening t A) ≤
      sphericalCapMeasure n (t / Real.sqrt 2) := by sorry

/-- **Concentration of measure on the sphere** (Corollary 9.4.12). If $\mu(A) \ge 1/2$ then
$\mu(A_t) \ge 1 - \exp(-n t^{2}/4)$ for every $t \ge 0$. -/
theorem sphere_concentration {n : ℕ}
    (A : Set (↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)))
    (hA : normalizedSphereMeasure A ≥ 1/2) (t : ℝ) (ht : 0 ≤ t) :
    normalizedSphereMeasure (Metric.cthickening t A) ≥
      1 - Real.exp (-(↑n * t ^ 2 / 4)) := by
  have h_comp := sphere_thickening_complement_bound A hA t ht
  have ht_sqrt : (0 : ℝ) ≤ t / Real.sqrt 2 := div_nonneg ht (Real.sqrt_nonneg 2)
  have h_cap := spherical_cap_bound n (t / Real.sqrt 2) ht_sqrt
  have h_sq : (t / Real.sqrt 2) ^ 2 = t ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt (show (0:ℝ) ≤ 2 from by norm_num)]
  have h_exp_eq : -(↑n * (t / Real.sqrt 2) ^ 2 / 2) = -(↑n * t ^ 2 / 4) := by
    rw [h_sq]; ring
  rw [h_exp_eq] at h_cap
  linarith

/-- Existence of a **median** for any function $f : S^{n-1} \to \mathbb{R}$: there is some
$m \in \mathbb{R}$ such that both $\{f \le m\}$ and $\{f \ge m\}$ have normalized sphere
measure at least $1/2$. -/
theorem sphere_median_exists {n : ℕ}
    (f : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) → ℝ) :
    ∃ m : ℝ, normalizedSphereMeasure {x | f x ≤ m} ≥ 1/2 ∧
             normalizedSphereMeasure {x | f x ≥ m} ≥ 1/2 := by sorry

/-- For a $1$-Lipschitz function $f : S^{n-1} \to \mathbb{R}$ with median bound $\mu(f \le m)
\ge 1/2$, the upper tail $\{f > m + t\}$ has measure at most
$1 - \mu(\text{thickening}_t \{f \le m\})$. This is the geometric link between
Lipschitz tails and isoperimetric thickening. -/
theorem sphere_lipschitz_sublevel_bound {n : ℕ}
    (f : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) → ℝ)
    (hf_lip : LipschitzWith 1 f)
    (m t : ℝ) (ht : 0 ≤ t)
    (hm : normalizedSphereMeasure {x | f x ≤ m} ≥ 1/2) :
    normalizedSphereMeasure {x | f x > m + t} ≤
      1 - normalizedSphereMeasure (Metric.cthickening t {x | f x ≤ m}) := by

  have hA_ne : ({x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) | f x ≤ m}).Nonempty :=
    normalizedSphereMeasure_nonempty_of_pos _ (by linarith)

  have h_incl : Metric.cthickening t
      {x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) | f x ≤ m} ⊆
      {x | f x ≤ m + t} := by
    intro x hx
    simp only [Set.mem_setOf_eq]
    rw [Metric.mem_cthickening_iff] at hx
    have h_infDist : Metric.infDist x {y | f y ≤ m} ≤ t := by
      have h1 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hx
      rwa [ENNReal.toReal_ofReal ht, ← Metric.infDist] at h1
    by_contra h_neg
    push Not at h_neg
    have h_lt : Metric.infDist x {y | f y ≤ m} < f x - m := by linarith
    obtain ⟨y, hy_mem, hy_dist⟩ := (Metric.infDist_lt_iff hA_ne).mp h_lt
    simp only [Set.mem_setOf_eq] at hy_mem
    have h_lip := hf_lip.dist_le_mul x y
    simp only [NNReal.coe_one, one_mul] at h_lip
    have h_dist_eq : dist (f x) (f y) = |f x - f y| := Real.dist_eq (f x) (f y)
    linarith [le_abs_self (f x - f y)]

  have h_compl : {x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) | f x > m + t} ⊆
      (Metric.cthickening t {x | f x ≤ m})ᶜ := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    simp only [Set.mem_compl_iff]
    intro hx_mem
    have := h_incl hx_mem
    simp only [Set.mem_setOf_eq] at this
    linarith

  calc normalizedSphereMeasure {x | f x > m + t}
      ≤ normalizedSphereMeasure (Metric.cthickening t {x | f x ≤ m})ᶜ :=
        normalizedSphereMeasure_subset_mono h_compl
    _ = 1 - normalizedSphereMeasure (Metric.cthickening t {x | f x ≤ m}) :=
        normalizedSphereMeasure_compl _ Metric.isClosed_cthickening.measurableSet
          (sphereVolume_pos_of_normalizedSphereMeasure_pos
            (show normalizedSphereMeasure {x | f x ≤ m} > 0 by linarith))

/-- One-sided concentration for $1$-Lipschitz functions on the sphere: if $m$ is a median of
$f$ then $\mu(f > m + t) \le \exp(-n t^{2}/4)$ for all $t \ge 0$. -/
theorem sphere_lipschitz_upper_tail {n : ℕ}
    (f : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) → ℝ)
    (hf_lip : LipschitzWith 1 f)
    (m : ℝ)
    (hm : normalizedSphereMeasure {x | f x ≤ m} ≥ 1/2)
    (t : ℝ) (ht : 0 ≤ t) :
    normalizedSphereMeasure {x | f x > m + t} ≤ Real.exp (-(↑n * t ^ 2 / 4)) := by
  have h_sublevel := sphere_lipschitz_sublevel_bound f hf_lip m t ht hm
  have h_conc := sphere_concentration {x | f x ≤ m} hm t ht
  linarith

/-- **Concentration of $1$-Lipschitz functions on the sphere** (Corollary 9.4.14). For any
$1$-Lipschitz $f : S^{n-1} \to \mathbb{R}$ there exists a median $m \in \mathbb{R}$ such that
$\mu(|f - m| > t) \le 2 \exp(-n t^{2}/4)$ for every $t \ge 0$. -/
theorem sphere_lipschitz_concentration {n : ℕ}
    (f : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) → ℝ)
    (hf_lip : LipschitzWith 1 f) :
    ∃ m : ℝ, ∀ t : ℝ, 0 ≤ t →
      normalizedSphereMeasure {x | |f x - m| > t} ≤
        2 * Real.exp (-(↑n * t ^ 2 / 4)) := by
  obtain ⟨m, hm_le, hm_ge⟩ := sphere_median_exists f
  use m
  intro t ht

  have h_decomp : {x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) | |f x - m| > t} ⊆
      {x | f x > m + t} ∪ {x | f x < m - t} := by
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_union] at *
    by_cases h : f x ≤ m
    · right
      have hab : |f x - m| = -(f x - m) := abs_of_nonpos (sub_nonpos.mpr h)
      linarith
    · left
      simp only [not_le] at h
      have hab : |f x - m| = f x - m := abs_of_pos (sub_pos.mpr h)
      linarith

  have h_upper := sphere_lipschitz_upper_tail f hf_lip m hm_le t ht


  have h_neg_lip : LipschitzWith 1 (-f) := hf_lip.neg
  have hm_neg : normalizedSphereMeasure
      {x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) | (-f) x ≤ -m} ≥ 1/2 := by
    have : {x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) | (-f) x ≤ -m} =
           {x | f x ≥ m} := by
      ext x; simp only [Pi.neg_apply, Set.mem_setOf_eq, neg_le_neg_iff]
    rw [this]; exact hm_ge
  have h_lower_neg := sphere_lipschitz_upper_tail (-f) h_neg_lip (-m) hm_neg t ht

  have h_lower_eq : {x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) |
      (-f) x > -m + t} = {x | f x < m - t} := by
    ext x; simp only [Pi.neg_apply, Set.mem_setOf_eq]; constructor
    · intro h; linarith
    · intro h; linarith
  rw [h_lower_eq] at h_lower_neg

  calc normalizedSphereMeasure {x | |f x - m| > t}
      ≤ normalizedSphereMeasure ({x | f x > m + t} ∪ {x | f x < m - t}) :=
        normalizedSphereMeasure_subset_mono h_decomp
    _ ≤ normalizedSphereMeasure {x | f x > m + t} +
        normalizedSphereMeasure {x | f x < m - t} :=
        normalizedSphereMeasure_union_le _ _
    _ ≤ Real.exp (-(↑n * t ^ 2 / 4)) + Real.exp (-(↑n * t ^ 2 / 4)) := by
        linarith [h_upper, h_lower_neg]
    _ = 2 * Real.exp (-(↑n * t ^ 2 / 4)) := by ring

end SphericalCap
