/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Atlas.AnAlgorithmistsToolkit.code.HighDimensional

open MeasureTheory ProbabilityTheory Real InnerProductSpace

namespace Concentration

theorem chernoff_bound
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (X : Fin n → Ω → ℝ)
    (hIndep : iIndepFun X μ)
    (hRange : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hProb : ∀ i, μ.real {ω | X i ω = 1} = p)
    (ε : ℝ) (hε : 0 ≤ ε) :
    μ.real {ω | |∑ i, X i ω - ↑n * p| ≥ ε * (↑n * p)} ≤
      2 * exp (-(↑n * p * ε ^ 2 / 12)) := by sorry

theorem hoeffding_bound
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (X : Fin n → Ω → ℝ) (a : Fin n → ℝ)
    (hIndep : iIndepFun X μ)
    (hRange : ∀ i ω, X i ω = 1 ∨ X i ω = -1)
    (hProb : ∀ i, μ.real {ω | X i ω = 1} = 1 / 2)
    (ha : ∑ i, a i ^ 2 = 1)
    (t : ℝ) (ht : 0 < t) :
    μ.real {ω | |∑ i, a i * X i ω| > t} ≤ 2 * exp (-t ^ 2 / 2) := by sorry

theorem inner_product_eq_dist_hyperplane {n : ℕ}
    (a x : EuclideanSpace ℝ (Fin n)) (ha : ‖a‖ = 1) :
    Metric.infDist x {y | @inner ℝ _ _ a y = (0 : ℝ)} = |@inner ℝ _ _ a x| := by
  set H := {y : EuclideanSpace ℝ (Fin n) | @inner ℝ _ _ a y = (0 : ℝ)}
  set c : ℝ := @inner ℝ _ _ a x
  set p := x - c • a
  have hp : p ∈ H := by
    simp only [H, Set.mem_setOf_eq, p, inner_sub_right, inner_smul_right,
      inner_self_eq_norm_sq_to_K, ha]
    simp [c]
  have hdist : dist x p = |c| := by
    simp only [p, dist_eq_norm, sub_sub_cancel]
    rw [norm_smul, ha, mul_one, Real.norm_eq_abs]
  have hne : H.Nonempty := ⟨p, hp⟩
  apply le_antisymm
  · rw [← hdist]
    exact Metric.infDist_le_dist_of_mem hp
  · rw [Metric.le_infDist hne]
    intro y hy
    rw [dist_eq_norm]
    have hinner : @inner ℝ _ _ a y = (0 : ℝ) := hy
    calc |c| = |@inner ℝ _ _ a (x - y)| := by
          simp only [c, inner_sub_right, hinner, sub_zero]
      _ ≤ ‖a‖ * ‖x - y‖ := abs_real_inner_le_norm a (x - y)
      _ = ‖x - y‖ := by rw [ha, one_mul]

open HighDimensional in
theorem levy_concentration_lipschitz
    (n : ℕ) (f : UnitSphere n → ℝ)
    (hf : LipschitzWith 1 f) (M : ℝ)
    (hM : IsMedian (uniformSphereMeasure n) f M)
    (ε : ℝ) (hε : 0 < ε)
    (hne_low : {x : UnitSphere n | f x ≤ M}.Nonempty)
    (hne_high : {x : UnitSphere n | f x ≥ M}.Nonempty) :
    uniformSphereMeasure n {x | ε < |f x - M|} ≤
      ENNReal.ofReal (2 * exp (-(↑n * ε ^ 2 / 2))) :=
  concentration_lipschitz_sphere n f hf M hM ε hε hne_low hne_high

end Concentration

namespace VolumeHardness

open MeasureTheory Real Set Finset BigOperators

theorem convexHull_subset_iUnion_closedBalls {n : ℕ} {m : ℕ} (hm : 0 < m)
    (P : Fin m → (Fin n → ℝ)) (hP : ∀ i, ‖P i‖ ≤ 1) :
    convexHull ℝ (Set.range P) ⊆ ⋃ i : Fin m, Metric.closedBall ((2⁻¹ : ℝ) • P i) (2⁻¹) := by sorry

theorem volume_convex_hull_points_bound (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    (P : Fin m → (Fin n → ℝ))
    (hP : ∀ i, ‖P i‖ ≤ 1) :
    (Measure.addHaar : Measure (Fin n → ℝ)) (convexHull ℝ (Set.range P)) ≤
      ENNReal.ofReal ((m : ℝ) / 2 ^ n) *
        (Measure.addHaar : Measure (Fin n → ℝ)) (Metric.ball (0 : Fin n → ℝ) 1) := by
  set μ := (Measure.addHaar : Measure (Fin n → ℝ))
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nontrivial (Fin n → ℝ) := Function.nontrivial

  have hcover := convexHull_subset_iUnion_closedBalls hm P hP


  have h1 : μ (convexHull ℝ (Set.range P)) ≤
      μ (⋃ i : Fin m, Metric.closedBall ((2⁻¹ : ℝ) • P i) (2⁻¹)) :=
    measure_mono hcover

  have h2 : μ (⋃ i : Fin m, Metric.closedBall ((2⁻¹ : ℝ) • P i) (2⁻¹)) ≤
      ∑' i : Fin m, μ (Metric.closedBall ((2⁻¹ : ℝ) • P i) (2⁻¹)) :=
    measure_iUnion_le _

  have h3 : ∀ i : Fin m, μ (Metric.closedBall ((2⁻¹ : ℝ) • P i) (2⁻¹)) =
      ENNReal.ofReal ((2⁻¹ : ℝ) ^ n) * μ (Metric.ball 0 1) := by
    intro i
    rw [Measure.addHaar_closedBall μ ((2⁻¹ : ℝ) • P i) (by positivity : (0 : ℝ) ≤ 2⁻¹)]
    congr 1
    rw [Module.finrank_fin_fun]

  calc μ (convexHull ℝ (Set.range P))
      ≤ ∑' i : Fin m, μ (Metric.closedBall ((2⁻¹ : ℝ) • P i) (2⁻¹)) := le_trans h1 h2
    _ = ∑' _ : Fin m, ENNReal.ofReal ((2⁻¹ : ℝ) ^ n) * μ (Metric.ball 0 1) := by
        congr 1
        ext i
        exact h3 i
    _ = ENat.card (Fin m) * (ENNReal.ofReal ((2⁻¹ : ℝ) ^ n) * μ (Metric.ball 0 1)) :=
        ENNReal.tsum_const _
    _ = ENNReal.ofReal ((m : ℝ) / 2 ^ n) * μ (Metric.ball 0 1) := by
        rw [ENat.card_eq_coe_fintype_card, Fintype.card_fin, ENat.toENNReal_coe]
        rw [show (↑m : ENNReal) * (ENNReal.ofReal ((2⁻¹ : ℝ) ^ n) * μ (Metric.ball 0 1)) =
          ((↑m : ENNReal) * ENNReal.ofReal ((2⁻¹ : ℝ) ^ n)) * μ (Metric.ball 0 1) from
          by ring]
        congr 1
        rw [← ENNReal.ofReal_natCast m, ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
        congr 1
        rw [inv_pow]
        field_simp

theorem volume_computation_hardness (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    (P : Fin m → (Fin n → ℝ))
    (hP : ∀ i, ‖P i‖ ≤ 1) :
    (Measure.addHaar : Measure (Fin n → ℝ)) (Metric.ball (0 : Fin n → ℝ) 1) ≥
      ENNReal.ofReal (2 ^ n / (m : ℝ)) *
        (Measure.addHaar : Measure (Fin n → ℝ)) (convexHull ℝ (Set.range P)) := by
  have bound := volume_convex_hull_points_bound n hn m hm P hP
  have hm_pos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have h2n_pos : (0 : ℝ) < 2 ^ n := pow_pos (by norm_num : (0:ℝ) < 2) n
  set μ := (Measure.addHaar : Measure (Fin n → ℝ))
  have hcd : ENNReal.ofReal (2 ^ n / (m : ℝ)) * ENNReal.ofReal ((m : ℝ) / 2 ^ n) = 1 := by
    rw [← ENNReal.ofReal_mul (div_nonneg (le_of_lt h2n_pos) (le_of_lt hm_pos))]
    have h : 2 ^ n / (m : ℝ) * ((m : ℝ) / 2 ^ n) = 1 := by field_simp
    rw [h, ENNReal.ofReal_one]
  calc ENNReal.ofReal (2 ^ n / (m : ℝ)) * μ (convexHull ℝ (Set.range P))
      ≤ ENNReal.ofReal (2 ^ n / (m : ℝ)) *
        (ENNReal.ofReal ((m : ℝ) / 2 ^ n) * μ (Metric.ball 0 1)) := by gcongr
    _ = (ENNReal.ofReal (2 ^ n / (m : ℝ)) * ENNReal.ofReal ((m : ℝ) / 2 ^ n)) *
        μ (Metric.ball 0 1) := by ring
    _ = 1 * μ (Metric.ball 0 1) := by rw [hcd]
    _ = μ (Metric.ball 0 1) := one_mul _

end VolumeHardness
