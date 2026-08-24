/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AnAlgorithmistsToolkit.code.ConvexGeometry
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Probability.Independence.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.PosDef

open Set

open scoped Matrix.Norms.Frobenius

noncomputable section

open MeasureTheory Real Finset

namespace RudelsonVershynin

def vecOuterProduct {n : ℕ} (v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => v i * v j

def euclideanNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i : Fin n, v i ^ 2)

theorem rv_theorem
  (n : ℕ) (hn : 0 < n)
  {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
  (Y : Ω → Fin n → ℝ)
  (hY_meas : Measurable Y)
  (t : ℝ) (ht : 0 < t)
  (hY_bound : ∀ᵐ ω ∂μ, euclideanNorm (Y ω) ≤ t)
  (hY_cov : ‖∫ ω, vecOuterProduct (Y ω) ∂μ‖ ≤ 1)
  (q : ℕ) (hq : 1 < q)
  {Ω' : Type*} [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]
  (Ys : Fin q → Ω' → Fin n → ℝ)
  (hYs_iid : ∀ i : Fin q, Measure.map (Ys i) ν = Measure.map Y μ)
  (hYs_indep : ProbabilityTheory.iIndepFun Ys ν)
  : ∃ (k : ℝ), 0 < k ∧
    ∫ ω', ‖(∫ ω, vecOuterProduct (Y ω) ∂μ) -
       (1 / (q : ℝ)) • ∑ i : Fin q, vecOuterProduct (Ys i ω')‖ ∂ν ≤
    k * t * Real.sqrt (Real.log (q : ℝ) / (q : ℝ)) := by sorry

end RudelsonVershynin

open Matrix

end
