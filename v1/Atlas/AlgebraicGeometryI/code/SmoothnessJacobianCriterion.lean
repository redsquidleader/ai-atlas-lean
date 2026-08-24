/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Maps

noncomputable section

/-- The maximal ideal of `k[x₁,…,xₙ]` corresponding to a `k`-rational point `x`:
the kernel of evaluation at `x`. -/
def maxIdealOfPoint_SJC {k : Type*} [Field k] {n : ℕ}
    (x : Fin n → k) : Ideal (MvPolynomial (Fin n) k) :=
  RingHom.ker (MvPolynomial.eval x)

/-- `maxIdealOfPoint_SJC x` is maximal: evaluation at a rational point gives a
ring homomorphism onto the field `k`. -/
instance maxIdealOfPoint_SJC_isMaximal {k : Type*} [Field k] {n : ℕ}
    (x : Fin n → k) : (maxIdealOfPoint_SJC x).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _
    (fun c => ⟨MvPolynomial.C c, MvPolynomial.eval_C c⟩)

/-- Image of the point-maximal-ideal in the quotient `k[x]/I`: the maximal ideal
of the closed point `x` in the affine variety `V(I)`. -/
def maxIdealInQuotient_SJC {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (_ : I ≤ maxIdealOfPoint_SJC x) :
    Ideal (MvPolynomial (Fin n) k ⧸ I) :=
  Ideal.map (Ideal.Quotient.mk I) (maxIdealOfPoint_SJC x)

/-- The image of the point ideal in the quotient is maximal. -/
instance maxIdealInQuotient_SJC_isMaximal {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint_SJC x) :
    (maxIdealInQuotient_SJC I x hI).IsMaximal := by
  apply Ideal.IsMaximal.map_of_surjective_of_ker_le
  · exact Ideal.Quotient.mk_surjective
  · rwa [Ideal.mk_ker]

/-- The image of the point ideal in the quotient is prime (follows from maximal). -/
instance maxIdealInQuotient_SJC_isPrime {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint_SJC x) :
    (maxIdealInQuotient_SJC I x hI).IsPrime :=
  (maxIdealInQuotient_SJC_isMaximal I x hI).isPrime

/-- The **local ring at a `k`-rational point** `x` of an affine variety `V(I)`:
the localization of `k[x]/I` at the maximal ideal of `x`. -/
abbrev localRingAtPoint_SJC {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint_SJC x) :=
  Localization.AtPrime (maxIdealInQuotient_SJC I x hI)

/-- **Jacobian matrix** of a finite system `f₁,…,fₘ` of polynomials in
`x₁,…,xₙ` evaluated at the point `x`. -/
def jacobianMatrix_SJC {k : Type*} [Field k] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k) (x : Fin n → k) :
    Matrix (Fin m) (Fin n) k :=
  fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (f i))

/-- **Cotangent dimension formula**: at a rational point `x` of `V(f₁,…,fₘ)`, the
dimension of the cotangent space `𝔪/𝔪²` equals `n − rank J(x)`, where `J` is the
Jacobian matrix. -/
theorem cotangentSpace_finrank_eq_n_sub_jacobianRank_SJC
    {k : Type*} [Field k] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k)
    (x : Fin n → k)
    (hx : ∀ i, MvPolynomial.eval x (f i) = 0)
    (hI : Ideal.span (Set.range f) ≤ maxIdealOfPoint_SJC x) :
    Module.finrank
      (IsLocalRing.ResidueField (localRingAtPoint_SJC (Ideal.span (Set.range f)) x hI))
      (IsLocalRing.CotangentSpace (localRingAtPoint_SJC (Ideal.span (Set.range f)) x hI)) =
    n - (jacobianMatrix_SJC f x).rank := by sorry

/-- **Corollary 23 (Jacobian Criterion for Smoothness)**: when the Krull dimension
of the local ring at `x` equals `n - m`, the Jacobian rank is `m` (full rank)
iff the local ring at `x` is regular, i.e., the variety is smooth at `x`. -/
theorem corollary23_jacobian_rank_SJC {k : Type*} [Field k] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k)
    (x : Fin n → k)
    (hx : ∀ i, MvPolynomial.eval x (f i) = 0)
    (hI : Ideal.span (Set.range f) ≤ maxIdealOfPoint_SJC x)
    (hdim : ringKrullDim
      (localRingAtPoint_SJC (Ideal.span (Set.range f)) x hI) = (n - m : ℕ))
    (hmn : m ≤ n) :
    (jacobianMatrix_SJC f x).rank = m ↔
      IsRegularLocalRing
        (localRingAtPoint_SJC (Ideal.span (Set.range f)) x hI) := by


  have hcot : Module.finrank
      (IsLocalRing.ResidueField (localRingAtPoint_SJC (Ideal.span (Set.range f)) x hI))
      (IsLocalRing.CotangentSpace (localRingAtPoint_SJC (Ideal.span (Set.range f)) x hI)) =
    n - (jacobianMatrix_SJC f x).rank :=
    cotangentSpace_finrank_eq_n_sub_jacobianRank_SJC f x hx hI

  rw [IsRegularLocalRing.iff_finrank_cotangentSpace]

  rw [hcot, hdim]

  have hrank_le_n : (jacobianMatrix_SJC f x).rank ≤ n :=
    le_trans (Matrix.rank_le_card_width _) (by simp)
  constructor
  · intro h; rw [h]
  · intro h
    have h' : n - (jacobianMatrix_SJC f x).rank = n - m := by exact_mod_cast h
    omega

/-- A `1 × n` matrix over a field has rank one iff it is non-zero
(equivalently, has a non-zero entry). -/
lemma matrix_fin1_rank_eq_one_iff_SJC {k : Type*} [Field k] {n : ℕ}
    (M : Matrix (Fin 1) (Fin n) k) : M.rank = 1 ↔ ∃ j, M 0 j ≠ 0 := by
  constructor
  · intro h
    by_contra h_all
    push Not at h_all
    have hM : M = 0 := by ext i j; fin_cases i; exact h_all j
    have : M.rank = 0 := by rw [hM]; simp [Matrix.rank]
    omega
  · intro ⟨j, hj⟩
    have hne : M ≠ 0 := by
      intro heq; apply hj; have := congr_fun (congr_fun heq 0) j; exact this
    have hle : M.rank ≤ 1 := by
      calc M.rank ≤ Fintype.card (Fin 1) := Matrix.rank_le_card_height M
        _ = 1 := by simp
    have hpos : 0 < M.rank := by
      rw [Nat.pos_iff_ne_zero]
      intro h0
      apply hne
      unfold Matrix.rank at h0
      rw [Submodule.finrank_eq_zero] at h0
      rw [LinearMap.range_eq_bot] at h0
      ext i j
      have hcol := congr_fun (LinearMap.ext_iff.mp h0 (Pi.single j 1)) i
      simp [Matrix.mulVecLin, Matrix.mulVec_single] at hcol
      exact hcol
    omega

/-- **Hypersurface Jacobian rank criterion**: for a single polynomial `P`
vanishing at `x`, the Jacobian has full rank `1` iff some partial derivative
`∂P/∂xᵢ` is non-zero at `x`. -/
theorem corollary23_hypersurface_criterion_SJC {k : Type*} [Field k] {n : ℕ}
    (P : MvPolynomial (Fin n) k) (x : Fin n → k)
    (_hx : MvPolynomial.eval x P = 0) :
    (∃ i : Fin n, MvPolynomial.eval x (MvPolynomial.pderiv i P) ≠ 0) ↔
    (jacobianMatrix_SJC (fun _ : Fin 1 => P) x).rank = 1 := by
  rw [matrix_fin1_rank_eq_one_iff_SJC]
  simp only [jacobianMatrix_SJC]

/-- **Smoothness criterion for hypersurfaces (Corollary 23)**: a hypersurface
`V(P)` of dimension `n - 1` is smooth at `x` iff some partial derivative of `P`
is non-zero at `x` — the classical "gradient is non-zero" criterion. -/
theorem corollary23_jacobian_hypersurface_SJC {k : Type*} [Field k] {n : ℕ}
    (P : MvPolynomial (Fin n) k) (x : Fin n → k)
    (hx : MvPolynomial.eval x P = 0)
    (hI : Ideal.span (Set.range (fun _ : Fin 1 => P)) ≤ maxIdealOfPoint_SJC x)
    (hdim : ringKrullDim
      (localRingAtPoint_SJC (Ideal.span (Set.range (fun _ : Fin 1 => P))) x hI) =
        (n - 1 : ℕ))
    (hn : 1 ≤ n) :
    (∃ i, MvPolynomial.eval x (MvPolynomial.pderiv i P) ≠ 0) ↔
      IsRegularLocalRing
        (localRingAtPoint_SJC
          (Ideal.span (Set.range (fun _ : Fin 1 => P))) x hI) := by

  rw [corollary23_hypersurface_criterion_SJC P x hx]

  have hx' : ∀ i : Fin 1, MvPolynomial.eval x ((fun _ : Fin 1 => P) i) = 0 :=
    fun _ => hx
  exact corollary23_jacobian_rank_SJC (fun _ : Fin 1 => P) x hx' hI hdim hn

end
