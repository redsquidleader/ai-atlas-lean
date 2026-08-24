/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProjectionTheory.code.DeltaRegular

open scoped ENNReal NNReal
open Metric Set Finset Classical

namespace BourgainProjection

/-- Projection of $v \in \mathbb{R}^2$ onto the line with affine parameter $\theta$:
$\pi_\theta(v) = v_0 + \theta v_1$. -/
noncomputable def projLine (θ : ℝ) (v : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  v 0 + θ * v 1

/-- The $1$-scale covering number of a subset $S \subseteq \mathbb{R}$. -/
noncomputable def coveringNumber1 (S : Set ℝ) : ℕ∞ :=
  Metric.externalCoveringNumber 1 S


/-- **Bourgain's projection theorem (real case)**: for any $t \in (0,2)$ and $s \in (0,1]$
there exist $\varepsilon, \eta > 0$ such that for every $R \geq 1$ and every pair $(X, D)$
with $|X| = R^t$, $|D| = R^s$, both Frostman-regular with exponents $t$ and $s$ up to an
$R^\eta$ loss, there exists a direction $\theta \in D$ for which every robust subset
$Y \subseteq X$ (i.e.\ $|Y| \geq R^{-\eta} |X|$) satisfies
$|\pi_\theta(Y)|_1 \geq R^{t/2 + \varepsilon}$. -/
theorem bourgain_projection
  (t s : ℝ) (ht : 0 < t) (ht2 : t < 2) (hs : 0 < s) (hs1 : s ≤ 1) :
  ∃ ε > (0 : ℝ), ∃ η > (0 : ℝ),
    ∀ (R : ℝ) (_ : 1 ≤ R)
      (X : Finset (EuclideanSpace ℝ (Fin 2)))
      (D : Finset ℝ),
      (X.card : ℝ) = R ^ t →
      (D.card : ℝ) = R ^ s →

      (∀ (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ), r ≤ R →
        ((X.filter (fun p => dist p x ≤ r)).card : ℝ) ≤
          R ^ η * (r / R) ^ t * (X.card : ℝ)) →

      (∀ (θ₀ : ℝ) (ρ : ℝ), ρ ≤ 1 →
        ((D.filter (fun d => |d - θ₀| ≤ ρ)).card : ℝ) ≤
          R ^ η * ρ ^ s * (D.card : ℝ)) →

      ∃ θ ∈ D,
        ∀ (Y : Finset (EuclideanSpace ℝ (Fin 2))),
          Y ⊆ X →
          (Y.card : ℝ) ≥ R ^ ((-1 : ℝ) * η) * (X.card : ℝ) →
          (coveringNumber1 (projLine θ '' (Y : Set (EuclideanSpace ℝ (Fin 2)))) : ℝ≥0∞) ≥
            ENNReal.ofReal (R ^ (t / 2 + ε)) := by sorry

end BourgainProjection
