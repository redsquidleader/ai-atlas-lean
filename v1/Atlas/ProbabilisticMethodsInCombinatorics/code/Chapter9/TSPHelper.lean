/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Metric Set Real Filter

namespace TSPHelper

/-- The unit square $[0,1]^2 \subseteq \mathbb{R}^2$ as a subset of Euclidean space. -/
def unitSquare : Set (EuclideanSpace ℝ (Fin 2)) :=
  { p | ∀ i : Fin 2, 0 ≤ p i ∧ p i ≤ 1 }

/-- The uniform probability measure on the unit square, obtained by restricting
Lebesgue measure on $\mathbb{R}^2$ to $[0,1]^2$. -/
def uniformOnSquare : Measure (EuclideanSpace ℝ (Fin 2)) :=
  volume.restrict unitSquare

/-- The product measure on $(\mathbb{R}^2)^k$ corresponding to $k$ i.i.d.\ uniform
points in the unit square. -/
def iidUniformOnSquare (k : ℕ) : Measure (Fin k → EuclideanSpace ℝ (Fin 2)) :=
  Measure.pi (fun _ => uniformOnSquare)

/-- The Lebesgue volume of the unit square $[0,1]^2$ is $1$. -/
lemma volume_unitSquare : (volume : Measure (EuclideanSpace ℝ (Fin 2))) unitSquare = 1 := by
  have heq : unitSquare = WithLp.ofLp ⁻¹' (Set.pi Set.univ (fun _ : Fin 2 => Icc (0:ℝ) 1)) := by
    ext p; simp only [unitSquare, mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Icc]
  rw [heq, (PiLp.volume_preserving_ofLp (ι := Fin 2)).measure_preimage
    ((MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)).nullMeasurableSet),
    volume_pi_pi]
  simp [Real.volume_Icc]

/-- The uniform measure on the unit square is a probability measure. -/
instance uniformOnSquare_isProbabilityMeasure : IsProbabilityMeasure uniformOnSquare :=
  ⟨by rw [show uniformOnSquare = volume.restrict unitSquare from rfl,
          Measure.restrict_apply_univ]; exact volume_unitSquare⟩

/-- The product measure of $k$ i.i.d.\ uniform points in the unit square is a
probability measure. -/
instance iidUniformOnSquare_isProbabilityMeasure (k : ℕ) :
    IsProbabilityMeasure (iidUniformOnSquare k) :=
  Measure.pi.instIsProbabilityMeasure (μ := fun _ => uniformOnSquare)

/-- Tail bound for the distance from a fixed $y \in [0,1]^2$ to a uniform sample
of $k$ points: for $t > 0$, the probability that $\operatorname{dist}(y, S) > t$
is at most $e^{-(k/4) t^2}$. -/
theorem tail_bound_infDist (k : ℕ) (hk : 0 < k) (y : EuclideanSpace ℝ (Fin 2))
    (hy : y ∈ unitSquare) (t : ℝ) (ht : 0 < t) :
    (iidUniformOnSquare k).real {S | t < Metric.infDist y (Set.range S)} ≤
      Real.exp (-(1/4 * ↑k) * t ^ 2) := by sorry

/-- The map $S \mapsto \operatorname{dist}(y, S)$ is integrable with respect to the
uniform i.i.d.\ measure on $k$-tuples of points in the unit square. -/
theorem infDist_integrable (k : ℕ) (hk : 0 < k) (y : EuclideanSpace ℝ (Fin 2))
    (hy : y ∈ unitSquare) :
    Integrable (fun S => Metric.infDist y (Set.range S)) (iidUniformOnSquare k) := by sorry

/-- The tail function $t \mapsto \mathbb{P}(\operatorname{dist}(y, S) > t)$
is integrable on $(0, \infty)$, which justifies the layer-cake representation
of $\mathbb{E}[\operatorname{dist}(y, S)]$. -/
theorem tail_integrableOn (k : ℕ) (hk : 0 < k) (y : EuclideanSpace ℝ (Fin 2))
    (hy : y ∈ unitSquare) :
    IntegrableOn (fun t => (iidUniformOnSquare k).real
      {a | t < Metric.infDist y (Set.range a)}) (Ioi 0) volume := by sorry

/-- Lemma 9.6.2: there is a constant $C > 0$ such that for all $k \geq 1$ and
any $y \in [0,1]^2$, the expected distance from $y$ to a uniform sample of $k$
i.i.d.\ points in the unit square satisfies
$\mathbb{E}[\operatorname{dist}(y, S)] \leq C / \sqrt{k}$. -/
theorem expected_infDist_le_div_sqrt :
    ∃ C : ℝ, 0 < C ∧ ∀ (k : ℕ) (_ : 0 < k) (y : EuclideanSpace ℝ (Fin 2)) (_ : y ∈ unitSquare),
      ∫ S, Metric.infDist y (Set.range S) ∂(iidUniformOnSquare k) ≤ C / Real.sqrt (↑k) := by
  refine ⟨Real.sqrt (Real.pi / (1/4)) / 2, by positivity, fun k hk y hy => ?_⟩
  have hck_pos : (0 : ℝ) < 1/4 * ↑k := by positivity
  have hD_int := infDist_integrable k hk y hy
  have hD_nn : 0 ≤ᵐ[iidUniformOnSquare k] (fun S => Metric.infDist y (Set.range S)) :=
    Filter.Eventually.of_forall (fun _ => Metric.infDist_nonneg)
  rw [hD_int.integral_eq_integral_meas_lt hD_nn]
  calc ∫ t in Ioi (0 : ℝ), (iidUniformOnSquare k).real
        {a | t < Metric.infDist y (Set.range a)}
      ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-(1/4 * ↑k) * t ^ 2) := by
        apply setIntegral_mono_on (tail_integrableOn k hk y hy)
          (integrable_exp_neg_mul_sq hck_pos).integrableOn measurableSet_Ioi
        intro t ht
        exact tail_bound_infDist k hk y hy t (mem_Ioi.mp ht)
    _ = Real.sqrt (Real.pi / (1/4)) / 2 / Real.sqrt ↑k := by
        rw [integral_gaussian_Ioi]
        rw [show Real.pi / (1/4 * ↑k) = (Real.pi / (1/4)) / ↑k from by ring]
        rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ Real.pi / (1/4))]
        ring

end TSPHelper
