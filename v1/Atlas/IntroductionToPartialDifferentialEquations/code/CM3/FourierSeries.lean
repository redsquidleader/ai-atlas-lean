/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.IntroductionToPartialDifferentialEquations.code.CM2.HeatEquationSetup
open MeasureTheory Real Filter Topology Set

noncomputable section

namespace FourierFacts

open HeatEquation

/-- Basic facts about the Fourier sine series on $[0, 1]$ (Theorem 4.1):
for $f \in L^2([0, 1])$, the Fourier sine partial sums converge to $f$ in $L^2$,
the Parseval identity $\|f\|_{L^2}^2 = \sum_m \tfrac{1}{2} A_m^2$ holds, and if $f$
is continuous on $[0, 1]$ then the convergence is uniform on any closed subinterval
$[a, b] \subset (0, 1)$. -/
theorem fourier_sine_theorem (f : ℝ → ℝ)
    (hf : Integrable (fun x => (f x) ^ 2) (volume.restrict (Icc 0 1))) :

    (Tendsto (fun N => L2ErrorSq f N) atTop (nhds 0)) ∧

    (L2NormSq f = ∑' m, (1 / 2 : ℝ) * (fourierSineCoeff f (m + 1)) ^ 2) ∧

    (ContinuousOn f (Icc 0 1) →
      ∀ (a b : ℝ), 0 < a → a ≤ b → b < 1 →
        Tendsto (fun N => ⨆ x ∈ Icc a b, |f x - fourierSinePartialSum f N x|)
          atTop (nhds 0)) := by sorry

/-- Uniform convergence statement from Theorem 4.1: if $f$ is continuous on $[0, 1]$,
then the Fourier sine partial sums converge uniformly to $f$ on any closed subinterval
$[a, b] \subset (0, 1)$. -/
theorem fourier_sine_uniform_convergence (f : ℝ → ℝ)
    (hf_cont : ContinuousOn f (Icc 0 1))
    (a b : ℝ) (hab : 0 < a) (hba : a ≤ b) (hb1 : b < 1) :
    Tendsto
      (fun N => ⨆ x ∈ Icc a b,
        |f x - fourierSinePartialSum f N x|)
      atTop (nhds 0) := by sorry

end FourierFacts
