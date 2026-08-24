/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.Lec18KahlerSmoothness

noncomputable section

open IsLocalRing

/-- Corollary 23 / Proposition 31 (Lecture 19), restated. For a complete intersection
`V(f_1,…,f_m)` of expected dimension `n - m`, the local ring at `x` is regular iff the
Jacobian matrix has full rank `m` at `x`. -/
theorem corollary23_jacobian_rank {k : Type*} [Field k] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k)
    (x : Fin n → k)
    (hx : ∀ i, MvPolynomial.eval x (f i) = 0)
    (hI : Ideal.span (Set.range f) ≤ maxIdealOfPoint x)
    (hdim : ringKrullDim (localRingAtPoint (Ideal.span (Set.range f)) x hI) = (n - m : ℕ)) :
    (jacobianMatrix f x).rank = m ↔
      IsRegularLocalRing (localRingAtPoint (Ideal.span (Set.range f)) x hI) :=
  Corollary23_jacobian_criterion f x hx hI hdim

/-- Hypersurface case of the Jacobian criterion: for `V(P) ⊂ 𝔸ⁿ` of dimension `n-1`, the
point `x` is smooth iff some partial derivative `∂P/∂x_i(x)` is nonzero. -/
theorem corollary23_jacobian_hypersurface {k : Type*} [Field k] {n : ℕ}
    (P : MvPolynomial (Fin n) k) (x : Fin n → k)
    (hx : MvPolynomial.eval x P = 0)
    (hI : Ideal.span (Set.range (fun _ : Fin 1 => P)) ≤ maxIdealOfPoint x)
    (hdim : ringKrullDim
      (localRingAtPoint (Ideal.span (Set.range (fun _ : Fin 1 => P))) x hI) = (n - 1 : ℕ)) :
    (∃ i, MvPolynomial.eval x (MvPolynomial.pderiv i P) ≠ 0) ↔
      IsRegularLocalRing
        (localRingAtPoint (Ideal.span (Set.range (fun _ : Fin 1 => P))) x hI) := by

  rw [Corollary23_hypersurface_criterion P x hx]

  have hx' : ∀ i : Fin 1, MvPolynomial.eval x ((fun _ : Fin 1 => P) i) = 0 :=
    fun _ => hx
  exact corollary23_jacobian_rank (fun _ : Fin 1 => P) x hx' hI hdim

end
