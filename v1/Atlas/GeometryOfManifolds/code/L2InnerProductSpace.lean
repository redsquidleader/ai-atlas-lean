/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.GeometryOfManifolds.code.HodgeStarMathlib
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped Manifold ComplexConjugate
open MeasureTheory HodgeStarMathlib

set_option autoImplicit false

noncomputable section

namespace L2InnerProductSpace

/-- $L^2$ seminorm structure on smooth $k$-forms on a compact complex $n$-manifold,
induced by the pointwise Hermitian inner product and the volume form. -/
noncomputable instance instSeminormedAddCommGroupSmoothForm (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M]
    [CompactSpace M] [MeasurableSpace M] (k : ℕ) :
    SeminormedAddCommGroup (SmoothForm n M k) := by sorry

/-- $L^2$ inner product structure on smooth $k$-forms,
$\langle \alpha, \beta \rangle = \int_M \alpha \wedge \star \bar\beta$,
used to define the formal adjoints $\bar\partial^*$ and $\partial^*$. -/
noncomputable instance instInnerProductSpaceSmoothForm (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℂ (Fin n)) M]
    [IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin n)) ⊤ M]
    [CompactSpace M] [MeasurableSpace M] (k : ℕ) :
    @InnerProductSpace ℝ (SmoothForm n M k) _
      (instSeminormedAddCommGroupSmoothForm n M k) := by sorry

end L2InnerProductSpace

end
