/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Matrix.Spectrum
import Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.WeightedCertificates

open MeasureTheory Matrix Real BigOperators Finset

noncomputable section

namespace EigenvalueConcentration

end EigenvalueConcentration

namespace EigenvalueConcentration

variable {n : ℕ} [NeZero n]

/-- Number of entries on or above the diagonal of an $n \times n$ matrix: $n(n+1)/2$. -/
def numUpperTriEntries (n : ℕ) : ℕ := n * (n + 1) / 2

/-- The largest eigenvalue $\lambda_1(A)$ of a Hermitian matrix $A$, defined as the first
entry of its eigenvalue list. -/
def largestEigenvalue (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) : ℝ :=
  hA.eigenvalues₀ ⟨0, by rw [Fintype.card_fin]; exact NeZero.pos n⟩

end EigenvalueConcentration

/-- The largest-eigenvalue functional $\lambda_1$ on the space of Hermitian matrices with
entries bounded by $1$ admits weighted Talagrand certificates with constant $4\sqrt{2}$. -/
theorem EigenvalueConcentration.eigenvalue_has_weighted_certificates
    {n : ℕ} [NeZero n]
    (s : ℕ) (hs : s = EigenvalueConcentration.numUpperTriEntries n)
    (Ω : Fin s → Type*) [∀ i, DecidableEq (Ω i)]
    (toMatrix : ((i : Fin s) → Ω i) → Matrix (Fin n) (Fin n) ℝ)
    (hSymm : ∀ x, (toMatrix x).IsHermitian)
    (hBdd : ∀ x i j, |toMatrix x i j| ≤ 1) :
    TalagrandWeightedCertificates.HasWeightedCertificates
      (n := s) (Ω := Ω)
      (fun x => EigenvalueConcentration.largestEigenvalue (toMatrix x) (hSymm x))
      (4 * Real.sqrt 2) := by sorry

namespace EigenvalueConcentration

variable {n : ℕ} [NeZero n]

/-- Concentration of the largest eigenvalue around its median (Theorem 9.5.17): for a random
Hermitian matrix with independent bounded entries,
$\mathbb{P}(|\lambda_1(A) - M\lambda_1(A)| \geq t) \leq 4\exp(-t^2/32)$. -/
theorem largest_eigenvalue_concentration
    (s : ℕ) (hs : s = numUpperTriEntries n)
    (Ω : Fin s → Type*) [∀ i, DecidableEq (Ω i)] [∀ i, MeasurableSpace (Ω i)]
    (μ : (i : Fin s) → MeasureTheory.Measure (Ω i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (toMatrix : ((i : Fin s) → Ω i) → Matrix (Fin n) (Fin n) ℝ)
    (hSymm : ∀ x, (toMatrix x).IsHermitian)
    (hBdd : ∀ x i j, |toMatrix x i j| ≤ 1)
    (M : ℝ)
    (h_median_upper : (MeasureTheory.Measure.pi μ
      {x | (fun ω => largestEigenvalue (toMatrix ω) (hSymm ω)) x ≤ M}).toReal ≥ 1/2)
    (h_median_lower : (MeasureTheory.Measure.pi μ
      {x | (fun ω => largestEigenvalue (toMatrix ω) (hSymm ω)) x ≥ M}).toReal ≥ 1/2) :
    ∀ t : ℝ, 0 ≤ t →
      (MeasureTheory.Measure.pi μ
        {x | |(fun ω => largestEigenvalue (toMatrix ω) (hSymm ω)) x - M| ≥ t}).toReal ≤
          4 * exp (-(t ^ 2) / 32) := by
  intro t ht

  have hcert := eigenvalue_has_weighted_certificates s hs Ω toMatrix hSymm hBdd

  have hK : (0 : ℝ) < 4 * Real.sqrt 2 := by positivity
  have h := TalagrandWeightedCertificates.talagrand_weighted_certificates μ
    (fun ω => largestEigenvalue (toMatrix ω) (hSymm ω))
    (4 * Real.sqrt 2) hK hcert M h_median_upper h_median_lower t ht

  have heq : -(t ^ 2) / (4 * Real.sqrt 2) ^ 2 = -(t ^ 2) / 32 := by
    congr 1
    rw [mul_pow, Real.sq_sqrt (by norm_num : (2:ℝ) ≥ 0)]
    norm_num
  rw [heq] at h
  exact h

end EigenvalueConcentration
