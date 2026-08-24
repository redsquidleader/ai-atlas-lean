/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.WeightedCertificates

set_option maxHeartbeats 400000
set_option linter.unusedVariables false

namespace RheeTalagrand

open Real MeasureTheory Set

/-- A point in the plane $\mathbb{R}^2$, represented as a function $\mathrm{Fin}\,2 \to \mathbb{R}$. -/
abbrev Point := Fin 2 → ℝ

/-- The unit square $[0,1]^2 \subseteq \mathbb{R}^2$. -/
def unitSquare : Set Point :=
  { p : Point | ∀ i : Fin 2, 0 ≤ p i ∧ p i ≤ 1 }

/-- The TSP tour length $L_n$: the infimum over permutations $σ$ of $\mathrm{Fin}\,n$
of $\sum_i \mathrm{dist}(\mathit{points}_{σ(i)}, \mathit{points}_{σ(i+1 \bmod n)})$.
Returns $0$ when $n = 0$. -/
noncomputable def tspTourLength (n : ℕ) (points : Fin n → Point) : ℝ :=
  if h : n = 0 then 0
  else ⨅ σ : Equiv.Perm (Fin n), ∑ i : Fin n,
    dist (points (σ i)) (points (σ ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.pos_of_ne_zero h)⟩))

/-- The measure $μ$ on $(\mathbb{R}^2)^n$ corresponds to $n$ i.i.d.\ uniformly random
points in the unit square. -/
def IsIIDUniformUnitSquare (n : ℕ) (μ : Measure (Fin n → Point)) : Prop :=
  μ = Measure.pi (fun _ => volume.restrict unitSquare)

/-- TSP tour length specialized to points in the unit square, viewed as a function
of the subtype-valued configuration $x : \mathrm{Fin}\,n \to \mathit{unitSquare}$. -/
noncomputable def tspTourLengthOnUnitSquare (n : ℕ) (x : Fin n → unitSquare) : ℝ :=
  tspTourLength n (fun i => (x i).val)

/-- Lemma 9.6.11: the TSP tour length on the unit square admits weighted
certificates with a uniform constant $K > 0$, allowing Talagrand's weighted
certificates inequality to be applied to $L_n$. -/
theorem tsp_has_weighted_certificates :
    ∃ K : ℝ, 0 < K ∧ ∀ (n : ℕ) (_ : 1 ≤ n),
      TalagrandWeightedCertificates.HasWeightedCertificates
        (Ω := fun _ : Fin n => unitSquare)
        (tspTourLengthOnUnitSquare n) K := by sorry

/-- Theorem 9.6.3 (Rhee–Talagrand 1989): for $n$ i.i.d.\ uniform points in the unit
square, the TSP tour length $L_n$ is $O(1)$-sub-Gaussian about its mean, i.e.\ there
exists $c > 0$ such that for all $t > 0$,
$\mu(\{x : |L_n(x) - \mathbb{E} L_n| \geq t\}) \leq e^{-c t^2}$. -/
theorem rhee_talagrand_1989 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n : ℕ) (_ : 1 ≤ n)
        (μ : Measure (Fin n → Point))
        (_ : IsIIDUniformUnitSquare n μ)
        (_ : IsProbabilityMeasure μ),
        ∀ t : ℝ, 0 < t →
          μ {x : Fin n → Point | t ≤ |tspTourLength n x -
            ∫ y, tspTourLength n y ∂μ|} ≤
            ENNReal.ofReal (exp (-c * t ^ 2)) := by sorry

end RheeTalagrand
