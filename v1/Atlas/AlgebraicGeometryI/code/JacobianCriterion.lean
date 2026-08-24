/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.Lec18KahlerSmoothness

noncomputable section

open IsLocalRing

/-- Proposition 31 (Lec 19): smoothness of an ideal `I` at a point `x` is equivalent
to the existence of polynomials `f₁, …, f_m ∈ I` with linearly independent gradients at
`x` that locally generate `I` (after multiplying by a unit at `x`). -/
theorem proposition31_smooth_iff_locally_generated
    {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k)
    (hI : I ≤ maxIdealOfPoint x) :

    IsRegularLocalRing (localRingAtPoint I x hI) ↔


    (∃ (m : ℕ) (f : Fin m → MvPolynomial (Fin n) k),

      (∀ i, f i ∈ I) ∧

      LinearIndependent k
        (fun i : Fin m => (fun j : Fin n =>
          MvPolynomial.eval x (MvPolynomial.pderiv j (f i)))) ∧


      ∃ (u : MvPolynomial (Fin n) k),
        MvPolynomial.eval x u ≠ 0 ∧
        ∀ g ∈ I, u * g ∈ Ideal.span (Set.range f)) :=
  Proposition31_smooth_point_characterization I x hI

/-- Jacobian criterion (Cor 23, Lec 19): for a system `f₁, …, f_m` vanishing at `x`
that cuts out a local ring of expected dimension `n − m`, smoothness at `x` is
equivalent to the Jacobian matrix `(∂f_i / ∂x_j)(x)` having full rank `m`. -/
theorem proposition31_jacobian_criterion
    {k : Type*} [Field k] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k)
    (x : Fin n → k)
    (hx : ∀ i, MvPolynomial.eval x (f i) = 0)
    (hI : Ideal.span (Set.range f) ≤ maxIdealOfPoint x)
    (hdim : ringKrullDim (localRingAtPoint (Ideal.span (Set.range f)) x hI) = (n - m : ℕ)) :
    IsRegularLocalRing (localRingAtPoint (Ideal.span (Set.range f)) x hI) ↔
      (jacobianMatrix f x).rank = m :=
  (Corollary23_jacobian_criterion f x hx hI hdim).symm

/-- Helper: linear independence of the gradient vectors `(∂f_i/∂x_j(x))_j` implies
the Jacobian matrix has full row rank `m`. -/
theorem jacobian_rank_eq_of_linearIndependent
    {k : Type*} [Field k] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k)
    (x : Fin n → k)
    (hf_indep : LinearIndependent k
      (fun i : Fin m => (fun j : Fin n =>
        MvPolynomial.eval x (MvPolynomial.pderiv j (f i))))) :
    (jacobianMatrix f x).rank = m := by
  have h : LinearIndependent k (jacobianMatrix f x).row := by
    simp only [Matrix.row]
    exact hf_indep
  rw [LinearIndependent.rank_matrix h, Fintype.card_fin]

end
