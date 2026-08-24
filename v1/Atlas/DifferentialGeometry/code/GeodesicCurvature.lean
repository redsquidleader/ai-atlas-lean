/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialGeometry.code.Intrinsic

noncomputable section

open Matrix Finset BigOperators

namespace MovingFrame

def firstFundamentalFormBilinear (patch : HypersurfacePatch 2)
    (x : Fin 2 → ℝ) (v w : Fin 2 → ℝ) : ℝ :=
  v ⬝ᵥ ((firstFundamentalForm patch x).mulVec w)

def geodesicCurvature (patch : HypersurfacePatch 2)
    (c : ℝ → Fin 2 → ℝ) (t : ℝ) : ℝ :=
  let γ := patch.f ∘ c
  let γ' := deriv γ t
  let γ'' := deriv (deriv γ) t
  let ν := gaussNormal patch (c t)
  let M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j =>
    match j with
    | 0 => γ' i
    | 1 => γ'' i
    | 2 => ν i
  let speed := Real.sqrt (∑ i : Fin 3, γ' i ^ 2)
  M.det / (speed ^ 3)


theorem geodesicCurvature_eq_connection_formula
    (patch : HypersurfacePatch 2)
    (X : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℝ)
    (c : ℝ → Fin 2 → ℝ)
    (hF : IsMovingFrame patch X)
    (hpos : ∀ x ∈ patch.domain, 0 < (X x).det)
    (hsmooth : ContDiff ℝ ⊤ c)
    (hdom : ∀ t, c t ∈ patch.domain)
    (hspeed : ∀ t, firstFundamentalFormBilinear patch (c t) (deriv c t) (deriv c t) > 0)
    (hX1 : ∀ t, ∀ k : Fin 2, (X (c t)) k 0 =
      (deriv c t) k /
        Real.sqrt (firstFundamentalFormBilinear patch (c t) (deriv c t) (deriv c t)))
    (t : ℝ) :
    geodesicCurvature patch c t =
      (connectionMatrix patch X (c t) 0 0 1 * (deriv c t) 0 +
       connectionMatrix patch X (c t) 1 0 1 * (deriv c t) 1) /
      Real.sqrt (firstFundamentalFormBilinear patch (c t) (deriv c t) (deriv c t)) := by sorry

end MovingFrame

end
