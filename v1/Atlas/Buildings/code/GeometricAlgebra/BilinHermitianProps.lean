/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.Buildings.code.GeometricAlgebra.HyperbolicCancellation
import Atlas.Buildings.code.GeometricAlgebra.KernelDecomposition

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace Formalization.GeometricAlgebra

open Garrett

variable {k : Type*} [Field k] [Invertible (2 : k)]


section Prop2

variable {V : Type*} [AddCommGroup V] [Module k V]

end Prop2


section Prop3

/-- Two hyperbolic formed spaces of the same finite dimension are isometric. NOTE:
the proof of this statement is currently `sorry`. -/
theorem hyperbolic_spaces_of_same_dim_isometric
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
    (B₁ : LinearMap.BilinForm k V₁) (B₂ : LinearMap.BilinForm k V₂)
    (hHyp₁ : BilinForm.IsHyperbolic B₁) (hHyp₂ : BilinForm.IsHyperbolic B₂)
    (hdim : Module.finrank k V₁ = Module.finrank k V₂) :
    FormedSpacesIsometric B₁ B₂ := by sorry

end Prop3


section Prop4

variable {V : Type*} [AddCommGroup V] [Module k V]

/-- An alternating bilinear form is skew-symmetric: `B x y = -(B y x)`. -/
lemma isAlt_skew (B : LinearMap.BilinForm k V) (hAlt : B.IsAlt) (x y : V) :
    B x y = -(B y x) := by
  have h1 := hAlt (x + y)
  simp only [map_add, LinearMap.add_apply] at h1
  rw [hAlt x, hAlt y, zero_add, add_zero] at h1

  rw [add_comm] at h1
  exact add_eq_zero_iff_eq_neg.mp h1

end Prop4

end Formalization.GeometricAlgebra
