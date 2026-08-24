/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.Basic

open Set MeasureTheory Filter Topology Real

noncomputable section

namespace Duhamel

/-- The squared Euclidean norm $|x|^2 = \sum_{i=1}^n (x^i)^2$ for $x \in \mathbb{R}^n$. -/
def euclidNormSq {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 2

/-- The heat kernel (fundamental solution) on $\mathbb{R}^n$:
$\Gamma_D(t, x) = \frac{1}{(4 \pi D t)^{n/2}} \exp\!\left(-\frac{|x|^2}{4 D t}\right)$. -/
def heatKernel {n : ℕ} (D : ℝ) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  1 / (4 * π * D * t) ^ ((n : ℝ) / 2) * exp (-(euclidNormSq x) / (4 * D * t))

/-- The spatial Laplacian $\Delta f(x) = \sum_{i=1}^n \partial_i^2 f(x)$. -/
def laplacian {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, fderiv ℝ (fun y => fderiv ℝ f y (Pi.single i 1)) x (Pi.single i 1)

/-- The heat operator $\partial_t u - D \Delta u$ applied to $u$ at $(t, x)$. -/
def heatOperator {n : ℕ} (D : ℝ) (u : ℝ → (Fin n → ℝ) → ℝ) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  deriv (fun s => u s x) t - D * laplacian (u t) x

/-- Spatial convolution $(f * g)(x) = \int_{\mathbb{R}^n} f(x - y) g(y)\, d^n y$. -/
def spatialConvolution {n : ℕ} (f g : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∫ y, f (x - y) * g y

/-- Duhamel's formula: the candidate solution to the inhomogeneous heat equation
$u_t - D \Delta u = f$ with initial data $g$ is
$u(t, x) = (\Gamma_D(t, \cdot) * g)(x) + \int_0^t (\Gamma_D(t - s, \cdot) * f(s, \cdot))(x)\, ds$. -/
def duhamelSolution {n : ℕ} (D : ℝ) (g : (Fin n → ℝ) → ℝ)
    (f : ℝ → (Fin n → ℝ) → ℝ) (t : ℝ) (x : Fin n → ℝ) : ℝ :=
  spatialConvolution (heatKernel D t) g x +
    ∫ s in Icc 0 t, spatialConvolution (heatKernel D (t - s)) (f s) x

/-- Duhamel's principle (Theorem 1.2): for continuous initial data $g$ satisfying
$|g(x)| \leq a\,e^{b|x|^2}$ and a continuous, bounded forcing $f$ with bounded first
and second spatial derivatives, the inhomogeneous heat equation
$u_t - D \Delta u = f$, $u(0, x) = g(x)$ has a unique solution
$u \in C([0, T) \times \mathbb{R}^n) \cap C^{1,2}((0, T) \times \mathbb{R}^n)$ on
$[0, T) \times \mathbb{R}^n$ with $T = \tfrac{1}{4 D b}$, given on $(0, T)$ by
the Duhamel formula. -/
theorem theorem_1_2_duhamel
    {n : ℕ} (D : ℝ) (hD : D > 0)
    (g : (Fin n → ℝ) → ℝ) (hg_cont : Continuous g)
    {a : ℝ} (ha : 0 < a) {b : ℝ} (hb : 0 < b)
    (hg_bound : ∀ x, |g x| ≤ a * exp (b * euclidNormSq x))
    (f : ℝ → (Fin n → ℝ) → ℝ)
    (hf_cont : Continuous (fun p : ℝ × (Fin n → ℝ) => f p.1 p.2))
    (hf_bdd : ∃ M : ℝ, ∀ t x, 0 ≤ t → t < 1 / (4 * D * b) → |f t x| ≤ M)
    (hf_deriv_bdd : ∀ i : Fin n, ∃ M : ℝ,
      ∀ t x, 0 ≤ t → t < 1 / (4 * D * b) →
        ‖fderiv ℝ (f t) x (Pi.single i 1)‖ ≤ M)
    (hf_deriv2_bdd : ∀ i j : Fin n, ∃ M : ℝ,
      ∀ t x, 0 ≤ t → t < 1 / (4 * D * b) →
        ‖fderiv ℝ (fun y => fderiv ℝ (f t) y (Pi.single i 1)) x (Pi.single j 1)‖ ≤ M) :
    ∃ u : ℝ → (Fin n → ℝ) → ℝ,

      (∀ t x, 0 < t → t < 1 / (4 * D * b) →
        u t x = duhamelSolution D g f t x) ∧

      (∀ t x, 0 < t → t < 1 / (4 * D * b) →
        heatOperator D u t x = f t x) ∧

      (∀ x, Tendsto (fun t => u t x) (nhdsWithin 0 (Ioi 0)) (nhds (g x))) ∧

      (ContinuousOn (fun (p : ℝ × (Fin n → ℝ)) => u p.1 p.2)
        (Ico 0 (1 / (4 * D * b)) ×ˢ univ)) ∧

      (∀ x, ContDiffOn ℝ 1 (fun t => u t x) (Ioo 0 (1 / (4 * D * b)))) ∧

      (∀ t, t ∈ Ioo 0 (1 / (4 * D * b)) → ContDiff ℝ 2 (u t)) ∧

      (∀ v : ℝ → (Fin n → ℝ) → ℝ,
        (∀ t x, 0 < t → t < 1 / (4 * D * b) → heatOperator D v t x = f t x) →
        (∀ x, Tendsto (fun t => v t x) (nhdsWithin 0 (Ioi 0)) (nhds (g x))) →
        (∃ A B : ℝ, 0 < A ∧ 0 < B ∧
          ∀ t x, 0 ≤ t → t < 1 / (4 * D * b) → |v t x| ≤ A * exp (B * euclidNormSq x)) →
        ∀ t x, 0 < t → t < 1 / (4 * D * b) → v t x = u t x) := by sorry

end Duhamel

end
