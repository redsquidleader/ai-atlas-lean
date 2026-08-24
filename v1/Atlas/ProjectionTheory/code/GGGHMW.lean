/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProjectionTheory.code.DeltaRegular

open MeasureTheory Metric Set DeltaRegular
open scoped ENNReal NNReal

namespace RestrictedProjection

/-- The unit sphere $S^2 \subset \mathbb{R}^3$. -/
noncomputable abbrev S2 : Set (EuclideanSpace ℝ (Fin 3)) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

/-- Orthogonal projection $\pi_\theta : \mathbb{R}^3 \to \mathbb{R}^3$ onto the plane
perpendicular to a direction $\theta$, given by $v \mapsto v - \langle v, \theta\rangle\,\theta$. -/
noncomputable def orthogonalProjectionTo (θ : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) :=
  fun v => v - (inner (𝕜 := ℝ) v θ) • θ

/-- A spherical curve $\gamma : \mathbb{R} \to S^2$ is **non-degenerate** if it is $C^2$
and, at every parameter $t$, the second derivative $\gamma''(t)$ is not contained in the
linear span of $\gamma(t)$ and $\gamma'(t)$; equivalently $\gamma, \gamma', \gamma''$ are
pointwise linearly independent. -/
def IsNonDegenerate (γ : ℝ → EuclideanSpace ℝ (Fin 3)) : Prop :=
  (∀ t, γ t ∈ S2) ∧
  ContDiff ℝ 2 γ ∧
  ∀ t, ¬ ∃ (a b : ℝ),
    (iteratedFDeriv ℝ 2 γ t) (fun _ => 1) = a • γ t + b • ((fderiv ℝ γ t) 1)

/-- The image $\pi_\theta(X)$ of $X \subset \mathbb{R}^3$ under orthogonal projection
perpendicular to the direction $\theta$. -/
def projImage (θ : EuclideanSpace ℝ (Fin 3)) (X : Set (EuclideanSpace ℝ (Fin 3))) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  orthogonalProjectionTo θ '' X

/-- The arc-length average of $f$ along the curve $\gamma$ on $[a,b]$, i.e.
$\bigl(\int_a^b \|\gamma'\|\bigr)^{-1} \int_a^b f(\gamma(t))\,\|\gamma'(t)\|\,dt$. -/
noncomputable def arcLengthAverage (γ : ℝ → EuclideanSpace ℝ (Fin 3))
    (f : EuclideanSpace ℝ (Fin 3) → ℝ) (a b : ℝ) : ℝ :=
  (∫ t in a..b, ‖deriv γ t‖)⁻¹ * ∫ t in a..b, f (γ t) * ‖deriv γ t‖

/-- **Gan–Guo–Guth–Harris–Maldague–Wang theorem.** If $X \subset B^3$ is a
$(\delta, 2, C)$-set and $\gamma$ is a non-degenerate spherical curve, then for every
$\varepsilon > 0$,
$\operatorname{Avg}_{\theta \in \gamma} |\pi_\theta(X)|_\delta \ge C_\varepsilon \, \delta^{-2 + \varepsilon}$,
i.e. averaging the $\delta$-covering number of the projection along the curve recovers
nearly the full upper bound. -/
theorem gan_guo_guth_harris_maldague_wang
    (X : Set (EuclideanSpace ℝ (Fin 3)))
    (γ : ℝ → EuclideanSpace ℝ (Fin 3))
    (δ C : ℝ) (hδ : 0 < δ) (hC : 0 < C)
    (hX : IsDeltaSRegular δ 2 C X)
    (hγ : IsNonDegenerate γ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C_ε : ℝ, 0 < C_ε ∧
      ∀ (a b : ℝ), a < b →
        arcLengthAverage γ
          (fun θ => (deltaCoveringNumber δ (projImage θ X) : ℝ≥0∞).toReal) a b ≥
        C_ε * δ ^ (-2 + ε) := by sorry

end RestrictedProjection
