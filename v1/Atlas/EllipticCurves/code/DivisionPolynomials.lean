/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.FieldTheory.SeparableDegree
import Atlas.EllipticCurves.code.IsogenyKernels
import Atlas.EllipticCurves.code.Isogenies
import Atlas.EllipticCurves.code.Lemma53
import Atlas.EllipticCurves.code.TorsionEndomorphism

open Polynomial
open scoped Polynomial.Bivariate

/-- A short Weierstrass curve $y^2 = x^3 + A x + B$ over a commutative ring $R$, parameterised
by the coefficients $A$ and $B$. -/
structure ShortWeierstrassCurve (R : Type*) where
  A : R
  B : R

namespace ShortWeierstrassCurve

variable {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R)

/-- The underlying Mathlib `WeierstrassCurve` of a short Weierstrass curve, with
$a_1 = a_2 = a_3 = 0$, $a_4 = A$, $a_6 = B$. -/
noncomputable def toWeierstrassCurve : WeierstrassCurve R :=
  ⟨0, 0, 0, E.A, E.B⟩

/-- The first Weierstrass coefficient $a_1$ of a short Weierstrass curve vanishes. -/
@[simp] lemma toWeierstrassCurve_a₁ : E.toWeierstrassCurve.a₁ = 0 := rfl
/-- The second Weierstrass coefficient $a_2$ of a short Weierstrass curve vanishes. -/
@[simp] lemma toWeierstrassCurve_a₂ : E.toWeierstrassCurve.a₂ = 0 := rfl
/-- The third Weierstrass coefficient $a_3$ of a short Weierstrass curve vanishes. -/
@[simp] lemma toWeierstrassCurve_a₃ : E.toWeierstrassCurve.a₃ = 0 := rfl
/-- The fourth Weierstrass coefficient $a_4$ of a short Weierstrass curve equals $A$. -/
@[simp] lemma toWeierstrassCurve_a₄ : E.toWeierstrassCurve.a₄ = E.A := rfl
/-- The sixth Weierstrass coefficient $a_6$ of a short Weierstrass curve equals $B$. -/
@[simp] lemma toWeierstrassCurve_a₆ : E.toWeierstrassCurve.a₆ = E.B := rfl

/-- The auxiliary invariant $b_2 = a_1^2 + 4 a_2$ of a short Weierstrass curve vanishes. -/
@[simp] lemma b₂_eq : E.toWeierstrassCurve.b₂ = 0 := by
  simp [WeierstrassCurve.b₂, toWeierstrassCurve]

/-- The auxiliary invariant $b_4 = 2 a_4 + a_1 a_3$ of a short Weierstrass curve equals $2A$. -/
@[simp] lemma b₄_eq : E.toWeierstrassCurve.b₄ = 2 * E.A := by
  simp [WeierstrassCurve.b₄, toWeierstrassCurve]

/-- The auxiliary invariant $b_6 = a_3^2 + 4 a_6$ of a short Weierstrass curve equals $4B$. -/
@[simp] lemma b₆_eq : E.toWeierstrassCurve.b₆ = 4 * E.B := by
  simp [WeierstrassCurve.b₆, toWeierstrassCurve]

/-- The auxiliary invariant $b_8$ of a short Weierstrass curve equals $-A^2$. -/
@[simp] lemma b₈_eq : E.toWeierstrassCurve.b₈ = -(E.A ^ 2) := by
  simp [WeierstrassCurve.b₈, toWeierstrassCurve]

/-- The $n$-th division polynomial $\psi_n \in R[X][Y]$ of a short Weierstrass curve, as a
bivariate polynomial. Computed from Mathlib's `WeierstrassCurve.ψ`. -/
noncomputable def divisionPoly (n : ℤ) : R[X][Y] :=
  E.toWeierstrassCurve.ψ n

/-- The zeroth division polynomial vanishes, $\psi_0 = 0$. -/
@[simp] lemma divisionPoly_zero : E.divisionPoly 0 = 0 :=
  E.toWeierstrassCurve.ψ_zero

/-- The first division polynomial is $\psi_1 = 1$. -/
@[simp] lemma divisionPoly_one : E.divisionPoly 1 = 1 :=
  E.toWeierstrassCurve.ψ_one

/-- The second division polynomial is $\psi_2$, equal to the Mathlib helper `ψ₂`. -/
@[simp] lemma divisionPoly_two : E.divisionPoly 2 = E.toWeierstrassCurve.ψ₂ :=
  E.toWeierstrassCurve.ψ_two

/-- For a short Weierstrass curve, $\psi_2 = 2 Y$ (since $a_1 = a_3 = 0$). -/
lemma ψ₂_eq : E.toWeierstrassCurve.ψ₂ = C (C 2) * Y := by
  unfold WeierstrassCurve.ψ₂ WeierstrassCurve.Affine.polynomialY
  simp [toWeierstrassCurve, WeierstrassCurve.toAffine]

/-- The third division polynomial $\psi_3$ depends only on $X$ (it equals $C \, \Psi_3$). -/
@[simp] lemma divisionPoly_three :
    E.divisionPoly 3 = C E.toWeierstrassCurve.Ψ₃ :=
  E.toWeierstrassCurve.ψ_three

/-- The fourth division polynomial factors as $\psi_4 = C \, \mathrm{pre}\Psi_4 \cdot \psi_2$. -/
@[simp] lemma divisionPoly_four :
    E.divisionPoly 4 = C E.toWeierstrassCurve.preΨ₄ * E.toWeierstrassCurve.ψ₂ :=
  E.toWeierstrassCurve.ψ_four

/-- Negating the index negates the division polynomial: $\psi_{-n} = -\psi_n$. -/
@[simp] lemma divisionPoly_neg (n : ℤ) :
    E.divisionPoly (-n) = -E.divisionPoly n :=
  E.toWeierstrassCurve.ψ_neg n

/-- Odd-index recurrence (Theorem 5.21): $\psi_{2m+1} = \psi_{m+2}\psi_m^3 -
\psi_{m-1}\psi_{m+1}^3$. -/
lemma divisionPoly_odd (m : ℤ) : E.divisionPoly (2 * m + 1) =
    E.divisionPoly (m + 2) * E.divisionPoly m ^ 3 -
    E.divisionPoly (m - 1) * E.divisionPoly (m + 1) ^ 3 :=
  E.toWeierstrassCurve.ψ_odd m

/-- Even-index recurrence (Theorem 5.21): $\psi_{2m} \psi_2 = \psi_{m-1}^2 \psi_m \psi_{m+2}
- \psi_{m-2}\psi_m \psi_{m+1}^2$. -/
lemma divisionPoly_even (m : ℤ) :
    E.divisionPoly (2 * m) * E.toWeierstrassCurve.ψ₂ =
    E.divisionPoly (m - 1) ^ 2 * E.divisionPoly m * E.divisionPoly (m + 2) -
    E.divisionPoly (m - 2) * E.divisionPoly m * E.divisionPoly (m + 1) ^ 2 :=
  E.toWeierstrassCurve.ψ_even m

/-- The $x$-coordinate numerator polynomial $\phi_n \in R[X][Y]$ used in the multiplication-by-$n$
map: $\phi_n = X \psi_n^2 - \psi_{n+1} \psi_{n-1}$. -/
noncomputable def phiPoly (n : ℤ) : R[X][Y] :=
  E.toWeierstrassCurve.φ n

/-- Defining identity: $\phi_n = C X \cdot \psi_n^2 - \psi_{n+1} \cdot \psi_{n-1}$. -/
lemma phiPoly_eq (n : ℤ) : E.phiPoly n =
    C X * E.divisionPoly n ^ 2 - E.divisionPoly (n + 1) * E.divisionPoly (n - 1) := rfl

/-- The zeroth $\phi$-polynomial is $\phi_0 = 1$. -/
@[simp] lemma phiPoly_zero : E.phiPoly 0 = 1 :=
  E.toWeierstrassCurve.φ_zero

/-- The first $\phi$-polynomial is $\phi_1 = X$. -/
@[simp] lemma phiPoly_one : E.phiPoly 1 = C X :=
  E.toWeierstrassCurve.φ_one

/-- The $\phi$-polynomial is invariant under negation of the index: $\phi_{-n} = \phi_n$. -/
@[simp] lemma phiPoly_neg (n : ℤ) : E.phiPoly (-n) = E.phiPoly n :=
  E.toWeierstrassCurve.φ_neg n

/-- The numerator polynomial of $\omega_n$ (the $y$-coordinate piece of $[n]$), defined as
$\psi_{n+2}\psi_{n-1}^2 - \psi_{n-2}\psi_{n+1}^2$. -/
noncomputable def omegaPolyNumer (n : ℤ) : R[X][Y] :=
  E.divisionPoly (n + 2) * E.divisionPoly (n - 1) ^ 2 -
  E.divisionPoly (n - 2) * E.divisionPoly (n + 1) ^ 2

/-- For odd $n$, Mathlib's $\Psi_n$ collapses to $C(\mathrm{pre}\Psi_n)$ (no $\psi_2$ factor). -/
lemma Psi_odd (n : ℤ) (hn : ¬Even n) :
    E.toWeierstrassCurve.Ψ n = C (E.toWeierstrassCurve.preΨ n) := by
  unfold WeierstrassCurve.Ψ
  rw [if_neg hn, mul_one]

/-- For even $n$, Mathlib's $\Psi_n$ equals $C(\mathrm{pre}\Psi_n) \cdot \psi_2$. -/
lemma Psi_even (n : ℤ) (hn : Even n) :
    E.toWeierstrassCurve.Ψ n = C (E.toWeierstrassCurve.preΨ n) * E.toWeierstrassCurve.ψ₂ := by
  unfold WeierstrassCurve.Ψ
  rw [if_pos hn]

/-- For even $n$, the image of `omegaPolyNumer n` in the coordinate ring equals
$\psi_2 \cdot C(\text{pre}\Psi\text{-combination})$. -/
lemma omegaPolyNumer_mk_even (n : ℤ) (hn : Even n) :
    WeierstrassCurve.Affine.CoordinateRing.mk E.toWeierstrassCurve (E.omegaPolyNumer n) =
    WeierstrassCurve.Affine.CoordinateRing.mk E.toWeierstrassCurve
      (E.toWeierstrassCurve.ψ₂ * C (E.toWeierstrassCurve.preΨ (n + 2) *
        E.toWeierstrassCurve.preΨ (n - 1) ^ 2 -
        E.toWeierstrassCurve.preΨ (n - 2) *
        E.toWeierstrassCurve.preΨ (n + 1) ^ 2)) := by
  simp only [omegaPolyNumer, divisionPoly, map_sub, map_mul, map_pow,
    WeierstrassCurve.Affine.CoordinateRing.mk_ψ]
  have hn2 : Even (n + 2) := by obtain ⟨k, hk⟩ := hn; exact ⟨k + 1, by omega⟩
  have hno1 : ¬Even (n - 1) := by intro ⟨k, hk⟩; obtain ⟨m, hm⟩ := hn; omega
  have hn_2 : Even (n - 2) := by obtain ⟨k, hk⟩ := hn; exact ⟨k - 1, by omega⟩
  have hno2 : ¬Even (n + 1) := by intro ⟨k, hk⟩; obtain ⟨m, hm⟩ := hn; omega
  simp only [WeierstrassCurve.Ψ, if_pos hn2, if_neg hno1, if_pos hn_2, if_neg hno2, mul_one]
  simp only [map_mul]
  ring

/-- For odd $n$, the image of `omegaPolyNumer n` in the coordinate ring equals
$\psi_2^2 \cdot C(\text{pre}\Psi\text{-combination})$. -/
lemma omegaPolyNumer_mk_odd (n : ℤ) (hn : ¬Even n) :
    WeierstrassCurve.Affine.CoordinateRing.mk E.toWeierstrassCurve (E.omegaPolyNumer n) =
    WeierstrassCurve.Affine.CoordinateRing.mk E.toWeierstrassCurve
      (E.toWeierstrassCurve.ψ₂ ^ 2 * C (E.toWeierstrassCurve.preΨ (n + 2) *
        E.toWeierstrassCurve.preΨ (n - 1) ^ 2 -
        E.toWeierstrassCurve.preΨ (n - 2) *
        E.toWeierstrassCurve.preΨ (n + 1) ^ 2)) := by
  simp only [omegaPolyNumer, divisionPoly, map_sub, map_mul, map_pow,
    WeierstrassCurve.Affine.CoordinateRing.mk_ψ]
  have hno2 : ¬Even (n + 2) := by intro ⟨k, hk⟩; exact hn ⟨k - 1, by omega⟩
  have hn1 : Even (n - 1) := by
    rw [Int.not_even_iff_odd] at hn; obtain ⟨k, hk⟩ := hn; exact ⟨k, by omega⟩
  have hno_2 : ¬Even (n - 2) := by intro ⟨k, hk⟩; exact hn ⟨k + 1, by omega⟩
  have hn_1 : Even (n + 1) := by
    rw [Int.not_even_iff_odd] at hn; obtain ⟨k, hk⟩ := hn; exact ⟨k + 1, by omega⟩

  simp only [WeierstrassCurve.Ψ, if_neg hno2, if_pos hn1, if_neg hno_2, if_pos hn_1, mul_one]
  simp only [map_mul]
  ring

/-- For even $n$, the polynomial combination of `preΨ` is divisible by $2$, witnessed by
some half $h \in R[X]$. -/
theorem preΨ_omega_comb_even_div2 {R : Type*} [CommRing R]
  (W : WeierstrassCurve R) (n : ℤ) (hn : Even n) :
  ∃ h : R[X], W.preΨ (n + 2) * W.preΨ (n - 1) ^ 2 -
    W.preΨ (n - 2) * W.preΨ (n + 1) ^ 2 = C 2 * h := by sorry

/-- Squaring is invariant under negation of the index: $\psi_{-n}^2 = \psi_n^2$. -/
lemma divisionPoly_neg_sq (n : ℤ) :
    E.divisionPoly (-n) ^ 2 = E.divisionPoly n ^ 2 := by
  rw [divisionPoly_neg]; ring

/-- The $x$-coordinate of $[n]P$ is unchanged by $n \mapsto -n$: both $\phi_n$ and $\psi_n^2$ are
invariant under $n \mapsto -n$. -/
theorem x_coord_neg_invariant (n : ℤ) :
    E.phiPoly (-n) = E.phiPoly n ∧
    E.divisionPoly (-n) ^ 2 = E.divisionPoly n ^ 2 :=
  ⟨E.phiPoly_neg n, E.divisionPoly_neg_sq n⟩

/-- Odd-index addition identity (Theorem 5.21): the difference of cross terms
$\phi_m \psi_{m+1}^2 - \phi_{m+1}\psi_m^2$ equals $\psi_{2m+1}$. -/
theorem psi_odd_verification (m : ℤ) :
    E.phiPoly m * E.divisionPoly (m + 1) ^ 2 -
    E.phiPoly (m + 1) * E.divisionPoly m ^ 2 =
    E.divisionPoly (2 * m + 1) := by

  have key : E.phiPoly m * E.divisionPoly (m + 1) ^ 2 -
      E.phiPoly (m + 1) * E.divisionPoly m ^ 2 =
      E.divisionPoly (m + 1 + 1) * E.divisionPoly m ^ 3 -
      E.divisionPoly (m - 1) * E.divisionPoly (m + 1) ^ 3 := by

    change (C X * E.divisionPoly m ^ 2 - E.divisionPoly (m + 1) * E.divisionPoly (m - 1)) *
        E.divisionPoly (m + 1) ^ 2 -
      (C X * E.divisionPoly (m + 1) ^ 2 -
        E.divisionPoly (m + 1 + 1) * E.divisionPoly (m + 1 - 1)) *
        E.divisionPoly m ^ 2 =
      E.divisionPoly (m + 1 + 1) * E.divisionPoly m ^ 3 -
      E.divisionPoly (m - 1) * E.divisionPoly (m + 1) ^ 3
    have h : (m + 1 - 1 : ℤ) = m := by omega
    rw [h]
    ring

  rw [key, show (m + 1 + 1 : ℤ) = m + 2 by omega]
  exact (E.divisionPoly_odd m).symm

/-- Even-index verification (Theorem 5.21): $\psi_m \cdot \omega_n^{\mathrm{num}} = \psi_{2m}
\cdot \psi_2$. -/
theorem psi_even_verification (m : ℤ) :
    E.divisionPoly m * E.omegaPolyNumer m =
    E.divisionPoly (2 * m) * E.toWeierstrassCurve.ψ₂ := by

  unfold omegaPolyNumer

  rw [E.divisionPoly_even m]

  ring

/-- Degree of $\Phi_n$: the natural degree of Mathlib's $\Phi_n$ equals $n^2$ (in absolute
value). -/
theorem Phi_natDegree [Nontrivial R] (n : ℤ) :
    (E.toWeierstrassCurve.Φ n).natDegree = n.natAbs ^ 2 :=
  E.toWeierstrassCurve.natDegree_Φ n

/-- Leading coefficient of $\Phi_n$ is $1$ (the polynomial is monic). -/
theorem Phi_leadingCoeff [Nontrivial R] (n : ℤ) :
    (E.toWeierstrassCurve.Φ n).leadingCoeff = 1 :=
  E.toWeierstrassCurve.leadingCoeff_Φ n

/-- Degree of $\mathrm{pre}\Psi_n$: when $n \neq 0$ in $R$, its $\mathrm{natDegree}$ equals
$(n^2 - 4)/2$ for even $n$ and $(n^2 - 1)/2$ for odd $n$. -/
theorem preΨ_natDegree {n : ℤ} (h : (n : R) ≠ 0) :
    (E.toWeierstrassCurve.preΨ n).natDegree =
      (n.natAbs ^ 2 - if Even n then 4 else 1) / 2 :=
  E.toWeierstrassCurve.natDegree_preΨ h

/-- Leading coefficient of $\mathrm{pre}\Psi_n$: it equals $n/2$ for even $n$ and $n$ for odd $n$
(when $n \neq 0$ in $R$). -/
theorem preΨ_leadingCoeff {n : ℤ} (h : (n : R) ≠ 0) :
    (E.toWeierstrassCurve.preΨ n).leadingCoeff =
      ↑(if Even n then n / 2 else n) :=
  E.toWeierstrassCurve.leadingCoeff_preΨ h

/-- Degree of $\Psi_n^2$: when $n \neq 0$ in $R$, $\mathrm{natDegree}(\Psi_n^2) = n^2 - 1$. -/
theorem ΨSq_natDegree [NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) :
    (E.toWeierstrassCurve.ΨSq n).natDegree = n.natAbs ^ 2 - 1 :=
  E.toWeierstrassCurve.natDegree_ΨSq h

/-- Leading coefficient of $\Psi_n^2$ equals $n^2$. -/
theorem ΨSq_leadingCoeff [NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) :
    (E.toWeierstrassCurve.ΨSq n).leadingCoeff = ↑n ^ 2 :=
  E.toWeierstrassCurve.leadingCoeff_ΨSq h

/-- Combined statement of degree and leading coefficient of $\Psi_n^2$. -/
theorem ΨSq_leading_term [NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) :
    (E.toWeierstrassCurve.ΨSq n).natDegree = n.natAbs ^ 2 - 1 ∧
    (E.toWeierstrassCurve.ΨSq n).leadingCoeff = ↑n ^ 2 :=
  ⟨E.ΨSq_natDegree h, E.ΨSq_leadingCoeff h⟩

/-- A short Weierstrass curve has $a_1 = a_2 = a_3 = 0$. -/
lemma toWeierstrassCurve_short_form :
    E.toWeierstrassCurve.a₁ = 0 ∧ E.toWeierstrassCurve.a₂ = 0 ∧
    E.toWeierstrassCurve.a₃ = 0 :=
  ⟨rfl, rfl, rfl⟩

end ShortWeierstrassCurve

noncomputable section PointEval

open Polynomial WeierstrassCurve.Affine

/-- Evaluate a bivariate polynomial $p \in S[X][Y]$ at a point $(x_0, y_0) \in S \times S$
by first specialising $Y \mapsto y_0$ then $X \mapsto x_0$. -/
def Polynomial.evalBivariate {S : Type*} [CommRing S]
    (p : Polynomial (Polynomial S)) (x₀ y₀ : S) : S :=
  (p.eval (Polynomial.C y₀)).eval x₀

namespace ShortWeierstrassCurve

variable {F : Type*} [Field F] [DecidableEq F] (E : ShortWeierstrassCurve F)

/-- Numeric evaluation of $\psi_n$ at the affine point $(x_0, y_0)$. -/
def evalDivisionPoly (n : ℤ) (x₀ y₀ : F) : F :=
  (E.divisionPoly n).evalBivariate x₀ y₀

/-- Numeric evaluation of $\phi_n$ at the affine point $(x_0, y_0)$. -/
def evalPhiPoly (n : ℤ) (x₀ y₀ : F) : F :=
  (E.phiPoly n).evalBivariate x₀ y₀

/-- Numeric evaluation of the $\omega_n$-numerator polynomial at $(x_0, y_0)$. -/
def evalOmegaNumer (n : ℤ) (x₀ y₀ : F) : F :=
  (E.omegaPolyNumer n).evalBivariate x₀ y₀

/-- The $x$-coordinate of $[n] P$ for $P = (x_0, y_0)$, given by $\phi_n / \psi_n^2$. -/
def mulByN_x (n : ℤ) (x₀ y₀ : F) : F :=
  E.evalPhiPoly n x₀ y₀ / (E.evalDivisionPoly n x₀ y₀) ^ 2

/-- Numeric value of $\omega_n(P) = \omega_n^{\mathrm{num}}/(4y_0)$ at the affine point
$P = (x_0, y_0)$. -/
def evalOmega (n : ℤ) (x₀ y₀ : F) : F :=
  E.evalOmegaNumer n x₀ y₀ / (4 * y₀)

/-- The $y$-coordinate of $[n] P$ for $P = (x_0, y_0)$, given by $\omega_n / \psi_n^3$. -/
def mulByN_y (n : ℤ) (x₀ y₀ : F) : F :=
  E.evalOmega n x₀ y₀ / (E.evalDivisionPoly n x₀ y₀) ^ 3

omit [DecidableEq F] in
/-- Base case: $\psi_1$ evaluates to $1$ at any point. -/
@[simp] lemma evalDivisionPoly_one (x₀ y₀ : F) :
    E.evalDivisionPoly 1 x₀ y₀ = 1 := by
  simp [evalDivisionPoly, divisionPoly, Polynomial.evalBivariate]

omit [DecidableEq F] in
/-- Base case: $\phi_1(x_0, y_0) = x_0$. -/
@[simp] lemma evalPhiPoly_one (x₀ y₀ : F) :
    E.evalPhiPoly 1 x₀ y₀ = x₀ := by
  simp [evalPhiPoly, phiPoly, Polynomial.evalBivariate, eval_C, eval_X]

omit [DecidableEq F] in
/-- Base case: $[1] P$ has $x$-coordinate $x_0$. -/
lemma mulByN_x_one (x₀ y₀ : F) : E.mulByN_x 1 x₀ y₀ = x₀ := by
  simp [mulByN_x]

omit [DecidableEq F] in
/-- Over an elliptic short Weierstrass curve, $4 \neq 0$ in the base field $F$ (otherwise
$\Delta = 0$). -/
lemma four_ne_zero_of_isElliptic [hE : E.toWeierstrassCurve.IsElliptic] : (4 : F) ≠ 0 := by
  intro h4
  have h2 : (2 : F) = 0 :=
    pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp (by linear_combination h4)
  have hΔ : E.toWeierstrassCurve.Δ = 0 := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈, toWeierstrassCurve]
    have h64 : (64 : F) = 0 := by linear_combination 32 * h2
    have h432 : (432 : F) = 0 := by linear_combination 216 * h2
    ring_nf
    rw [h432, h64]
    ring
  exact absurd hΔ (isUnit_iff_ne_zero.mp hE.isUnit)

omit [DecidableEq F] in
/-- Base case: $\omega_1^{\mathrm{num}}(x_0, y_0) = 4 y_0^2$. -/
lemma evalOmegaNumer_one (x₀ y₀ : F) :
    E.evalOmegaNumer 1 x₀ y₀ = 4 * y₀ ^ 2 := by
  simp only [evalOmegaNumer, omegaPolyNumer, Polynomial.evalBivariate, divisionPoly]
  show ((E.toWeierstrassCurve.ψ 3 * (E.toWeierstrassCurve.ψ 0) ^ 2 -
    E.toWeierstrassCurve.ψ (-1) * (E.toWeierstrassCurve.ψ 2) ^ 2).eval (C y₀)).eval x₀ =
    4 * y₀ ^ 2
  simp only [WeierstrassCurve.ψ_zero, WeierstrassCurve.ψ_neg, WeierstrassCurve.ψ_one,
    WeierstrassCurve.ψ_two]

  unfold WeierstrassCurve.ψ₂ WeierstrassCurve.Affine.polynomialY


  simp [toWeierstrassCurve, WeierstrassCurve.toAffine]
  ring

omit [DecidableEq F] in
/-- Base case: $[1] P$ has $y$-coordinate $y_0$. -/
lemma mulByN_y_one [E.toWeierstrassCurve.IsElliptic] (x₀ y₀ : F) :
    E.mulByN_y 1 x₀ y₀ = y₀ := by
  simp only [mulByN_y, evalOmega, evalOmegaNumer_one, evalDivisionPoly_one, one_pow, div_one]
  by_cases hy : y₀ = 0
  · simp [hy]
  · rw [div_eq_iff (mul_ne_zero (E.four_ne_zero_of_isElliptic) hy)]
    ring

/-- Theorem 5.21 (algebraic form): when $\psi_n$ does not vanish at $P$, the affine point
$(x_0, y_0)$ is sent under $[n]$ to the point $(\mathrm{mulByN}_x, \mathrm{mulByN}_y)$. -/
theorem mul_eq_divisionPoly_coords
    {F : Type*} [Field F] [DecidableEq F] (E : ShortWeierstrassCurve F)
    [E.toWeierstrassCurve.IsElliptic]
    {x₀ y₀ : F}
    (hP : E.toWeierstrassCurve.toAffine.Nonsingular x₀ y₀)
    {n : ℤ} (hn : n ≠ 0)
    (hψ : E.evalDivisionPoly n x₀ y₀ ≠ 0) :
    ∃ h : E.toWeierstrassCurve.toAffine.Nonsingular
        (E.mulByN_x n x₀ y₀) (E.mulByN_y n x₀ y₀),
      n • (Point.some x₀ y₀ hP) =
      Point.some (E.mulByN_x n x₀ y₀) (E.mulByN_y n x₀ y₀) h := by sorry

/-- Theorem 5.21 (algebraic form): when $\psi_n$ vanishes at $P$, the affine point is an
$n$-torsion point ($[n] P = O$). -/
theorem mul_eq_zero_of_divisionPoly_eq_zero
    {F : Type*} [Field F] [DecidableEq F] (E : ShortWeierstrassCurve F)
    [E.toWeierstrassCurve.IsElliptic]
    {x₀ y₀ : F}
    (hP : E.toWeierstrassCurve.toAffine.Nonsingular x₀ y₀)
    {n : ℤ} (hn : n ≠ 0)
    (hψ : E.evalDivisionPoly n x₀ y₀ = 0) :
    n • (Point.some x₀ y₀ hP) = Point.zero := by sorry

/-- Theorem 5.21 (purely algebraic): three identities characterising the division polynomials.
The first asserts $n \mapsto -n$ symmetry; the second is the odd recurrence; the third is the
even recurrence. -/
theorem theorem_5_21_algebraic {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R) :

    (∀ n : ℤ, E.phiPoly (-n) = E.phiPoly n ∧
              E.divisionPoly (-n) ^ 2 = E.divisionPoly n ^ 2) ∧

    (∀ m : ℤ, E.phiPoly m * E.divisionPoly (m + 1) ^ 2 -
              E.phiPoly (m + 1) * E.divisionPoly m ^ 2 =
              E.divisionPoly (2 * m + 1)) ∧

    (∀ m : ℤ, E.divisionPoly m * E.omegaPolyNumer m =
              E.divisionPoly (2 * m) * E.toWeierstrassCurve.ψ₂) :=
  ⟨E.x_coord_neg_invariant, E.psi_odd_verification, E.psi_even_verification⟩

/-- Theorem 5.21: case split on whether $\psi_n(P)$ vanishes, returning either the affine
formulae for $[n] P$ or that $[n] P = O$. -/
theorem smul_eq_divisionPoly_cases
    {F : Type*} [Field F] [DecidableEq F] (E : ShortWeierstrassCurve F)
    [E.toWeierstrassCurve.IsElliptic]
    {x₀ y₀ : F}
    (hP : E.toWeierstrassCurve.toAffine.Nonsingular x₀ y₀)
    {n : ℤ} (hn : n ≠ 0) :
    (E.evalDivisionPoly n x₀ y₀ ≠ 0 →
      ∃ h : E.toWeierstrassCurve.toAffine.Nonsingular
          (E.mulByN_x n x₀ y₀) (E.mulByN_y n x₀ y₀),
        n • (Point.some x₀ y₀ hP) =
        Point.some (E.mulByN_x n x₀ y₀) (E.mulByN_y n x₀ y₀) h) ∧
    (E.evalDivisionPoly n x₀ y₀ = 0 →
      n • (Point.some x₀ y₀ hP) = Point.zero) :=
  ⟨mul_eq_divisionPoly_coords E hP hn, mul_eq_zero_of_divisionPoly_eq_zero E hP hn⟩

end ShortWeierstrassCurve

end PointEval

universe uSWC

/-- Auxiliary lemma for the coprimality of $\Phi_n$ and $\Psi_n^2$: a common root would
witness an affine $n$-torsion point that is also $(n \pm 1)$-torsion, contradicting
nontriviality. -/
theorem ShortWeierstrassCurve.common_root_torsion_contradiction_aux
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
    (E : ShortWeierstrassCurve F)
    [E.toWeierstrassCurve.IsElliptic]
    {x₀ : F} {n : ℤ} (hn : n ≠ 0)
    (hΦ : Polynomial.aeval x₀ (E.toWeierstrassCurve.Φ n) = 0)
    (hΨ : Polynomial.aeval x₀ (E.toWeierstrassCurve.ΨSq n) = 0) :
    ∃ y₀ : F, ∃ hP : E.toWeierstrassCurve.toAffine.Nonsingular x₀ y₀,
      n • (WeierstrassCurve.Affine.Point.some x₀ y₀ hP) =
        (WeierstrassCurve.Affine.Point.zero : E.toWeierstrassCurve.toAffine.Point) ∧
      ((n - 1) • (WeierstrassCurve.Affine.Point.some x₀ y₀ hP) =
        (WeierstrassCurve.Affine.Point.zero : E.toWeierstrassCurve.toAffine.Point) ∨
       (n + 1) • (WeierstrassCurve.Affine.Point.some x₀ y₀ hP) =
        (WeierstrassCurve.Affine.Point.zero : E.toWeierstrassCurve.toAffine.Point)) := by sorry

namespace ShortWeierstrassCurve

variable {k : Type uSWC} [Field k] (E : ShortWeierstrassCurve k)

open WeierstrassCurve.Affine in
/-- The polynomials $\Phi_n$ and $\Psi_n^2$ are coprime over an elliptic short Weierstrass
curve, used to extract the multiplication-by-$n$ map as a standard-form isogeny. -/
theorem Phi_ΨSq_isCoprime [E.toWeierstrassCurve.IsElliptic] (n : ℤ) :
    IsCoprime (E.toWeierstrassCurve.Φ n) (E.toWeierstrassCurve.ΨSq n) := by
  rcases eq_or_ne n 0 with rfl | hn
  ·
    rw [E.toWeierstrassCurve.Φ_zero]
    exact isCoprime_one_left
  ·
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed k (AlgebraicClosure k)]
    obtain ⟨ha₁, ha₂, ha₃⟩ := E.toWeierstrassCurve_short_form
    let Ek : ShortWeierstrassCurve (AlgebraicClosure k) :=
      ⟨algebraMap k _ E.toWeierstrassCurve.a₄, algebraMap k _ E.toWeierstrassCurve.a₆⟩
    have hWmap : Ek.toWeierstrassCurve =
        E.toWeierstrassCurve.map (algebraMap k (AlgebraicClosure k)) := by
      ext <;> simp only [ShortWeierstrassCurve.toWeierstrassCurve, WeierstrassCurve.map,
        ha₁, ha₂, ha₃, map_zero] <;> rfl
    haveI hEk : Ek.toWeierstrassCurve.IsElliptic := hWmap ▸ inferInstance

    classical
    intro x₀
    by_contra h_both
    push_neg at h_both
    obtain ⟨hΦ, hΨ⟩ := h_both

    have hΦ' : Polynomial.aeval x₀ (Ek.toWeierstrassCurve.Φ n) = 0 := by
      rwa [hWmap, WeierstrassCurve.map_Φ, Polynomial.aeval_map_algebraMap]
    have hΨ' : Polynomial.aeval x₀ (Ek.toWeierstrassCurve.ΨSq n) = 0 := by
      rwa [hWmap, WeierstrassCurve.map_ΨSq, Polynomial.aeval_map_algebraMap]
    obtain ⟨y₀, hP, hnP, hadj⟩ :=
      Ek.common_root_torsion_contradiction_aux hn hΦ' hΨ'

    have hPzero : (Point.some x₀ y₀ hP : Ek.toWeierstrassCurve.toAffine.Point) =
        Point.zero := by
      rcases hadj with h_minus | h_plus
      ·
        by_cases hn1 : n - 1 = 0
        ·
          rw [show n = 1 from by omega, one_zsmul] at hnP
          exact hnP
        · have key : (-1 : ℤ) • (Point.some x₀ y₀ hP :
              Ek.toWeierstrassCurve.toAffine.Point) = Point.zero := by
            have eq : (-1 : ℤ) = (n - 1) - n := by ring
            rw [eq, sub_zsmul, hnP, h_minus]; simp [← Point.zero_def]
          exact neg_eq_zero.mp (by simpa using key)
      ·
        by_cases hn1 : n + 1 = 0
        ·
          rw [show n = -1 from by omega] at hnP
          exact neg_eq_zero.mp (by simpa using hnP)
        · have key : (1 : ℤ) • (Point.some x₀ y₀ hP :
              Ek.toWeierstrassCurve.toAffine.Point) = Point.zero := by
            have eq : (1 : ℤ) = (n + 1) - n := by ring
            rw [eq, sub_zsmul, hnP, h_plus]; simp [← Point.zero_def]
          simpa using key

    exact Point.some_ne_zero hP hPzero

end ShortWeierstrassCurve

namespace ShortWeierstrassCurve

variable {k : Type*} [CommRing k]

/-- Data for the degree-$2$ Vélu isogeny: a $2$-torsion $x$-coordinate $x_0$ satisfying
$x_0^3 + A x_0 + B = 0$. -/
structure VeluDeg2Data (E : ShortWeierstrassCurve k) where
  x₀ : k
  root_eq : x₀ ^ 3 + E.A * x₀ + E.B = 0

namespace VeluDeg2Data

variable {E : ShortWeierstrassCurve k} (d : VeluDeg2Data E)

/-- Vélu parameter $t = 3 x_0^2 + A$. -/
def t : k := 3 * d.x₀ ^ 2 + E.A

/-- Vélu parameter $w = x_0 t = x_0 (3 x_0^2 + A)$. -/
def w : k := d.x₀ * d.t

/-- Vélu image parameter $A' = A - 5 t$ for the codomain curve. -/
def A' : k := E.A - 5 * d.t

/-- Vélu image parameter $B' = B - 7 w$ for the codomain curve. -/
def B' : k := E.B - 7 * d.w

/-- The image curve $E' : y^2 = x^3 + A' x + B'$ of the Vélu degree-$2$ isogeny. -/
def imageCurve : ShortWeierstrassCurve k := ⟨d.A', d.B'⟩

/-- Unfolding the $A$-coefficient of the image curve. -/
@[simp] lemma imageCurve_A : d.imageCurve.A = d.A' := rfl
/-- Unfolding the $B$-coefficient of the image curve. -/
@[simp] lemma imageCurve_B : d.imageCurve.B = d.B' := rfl

/-- Defining identity for $t$. -/
lemma t_eq : d.t = 3 * d.x₀ ^ 2 + E.A := rfl

/-- Defining identity for $w$. -/
lemma w_eq : d.w = d.x₀ * (3 * d.x₀ ^ 2 + E.A) := rfl

/-- The $2$-torsion point $(x_0, 0)$ lies on $E$ since $x_0^3 + A x_0 + B = 0$. -/
theorem kernel_point_on_curve : d.x₀ ^ 3 + E.A * d.x₀ + E.B = 0 := d.root_eq

/-- The key algebraic identity for the Vélu degree-$2$ map: the cubic in the numerator
factors compatibly with the image curve equation. -/
theorem velu_image_identity (x : k) :
    (x ^ 2 - d.x₀ * x + d.t) ^ 3 +
      d.A' * (x ^ 2 - d.x₀ * x + d.t) * (x - d.x₀) ^ 2 +
      d.B' * (x - d.x₀) ^ 3 =
    ((x - d.x₀) ^ 2 - d.t) ^ 2 * (x ^ 2 + d.x₀ * x + d.x₀ ^ 2 + E.A) := by
  simp only [t, w, A', B']
  linear_combination (x - d.x₀) ^ 3 * d.root_eq

/-- Numerator of the $x$-coordinate component $\phi_x(x) = x^2 - x_0 x + t$. -/
def phi_x_numer (x : k) : k := x ^ 2 - d.x₀ * x + d.t

/-- Denominator of the $x$-coordinate component $\phi_x$, namely $x - x_0$. -/
def phi_x_denom (x : k) : k := x - d.x₀

/-- Factor appearing in the $y$-coordinate numerator: $(x - x_0)^2 - t$. -/
def phi_y_numer_factor (x : k) : k := (x - d.x₀) ^ 2 - d.t

/-- Denominator of the $y$-coordinate component: $(x - x_0)^2$. -/
def phi_y_denom (x : k) : k := (x - d.x₀) ^ 2

section FieldTheorems

variable {F : Type*} [Field F] {E : ShortWeierstrassCurve F} (d : VeluDeg2Data E)

open Polynomial in
/-- Natural degree of the Vélu $u$-polynomial $X^2 - x_0 X + t$ over a field is $2$. -/
lemma velu_u_natDegree :
    (X ^ 2 - C d.x₀ * X + C d.t : F[X]).natDegree = 2 := by
  have h1 : (C d.x₀ * X : F[X]).natDegree ≤ 1 := by
    calc (C d.x₀ * X : F[X]).natDegree
        ≤ (C d.x₀ : F[X]).natDegree + X.natDegree := natDegree_mul_le
      _ = 0 + 1 := by simp [natDegree_C, natDegree_X]
      _ = 1 := by omega
  have h2 : (X ^ 2 - C d.x₀ * X : F[X]).natDegree = 2 := by
    rw [natDegree_sub_eq_left_of_natDegree_lt]
    · rw [natDegree_pow, natDegree_X]
    · rw [natDegree_pow, natDegree_X]; omega
  conv_lhs =>
    rw [show X ^ 2 - C d.x₀ * X + C d.t = (X ^ 2 - C d.x₀ * X) + C d.t from by ring]
  rw [natDegree_add_eq_left_of_natDegree_lt (by rw [natDegree_C, h2]; omega)]
  exact h2

open Polynomial in
/-- The Wronskian of the Vélu degree-$2$ pair simplifies to $(X - x_0)^2 - t$. -/
theorem velu_wronskian_eq :
    Polynomial.derivative (X ^ 2 - C d.x₀ * X + C d.t : F[X]) * (X - C d.x₀) -
    (X ^ 2 - C d.x₀ * X + C d.t) * Polynomial.derivative (X - C d.x₀) =
    (X - C d.x₀) ^ 2 - C d.t := by
  simp only [derivative_sub, derivative_add, derivative_pow, derivative_mul, derivative_C,
    derivative_X, map_ofNat, Nat.cast_ofNat, mul_one, zero_mul, sub_zero, zero_add]
  ring

open Polynomial in
/-- Separability of the Vélu degree-$2$ map: the Wronskian is nonzero. -/
theorem velu_deg2_is_separable :
    Polynomial.derivative (X ^ 2 - C d.x₀ * X + C d.t : F[X]) * (X - C d.x₀) -
    (X ^ 2 - C d.x₀ * X + C d.t) * Polynomial.derivative (X - C d.x₀) ≠ 0 := by
  rw [d.velu_wronskian_eq]
  have h2 : ((X - C d.x₀ : F[X]) ^ 2).natDegree = 2 := by
    rw [natDegree_pow, natDegree_X_sub_C]
  have h4 : (C d.t : F[X]).natDegree < ((X - C d.x₀ : F[X]) ^ 2).natDegree := by
    rw [h2, natDegree_C]; omega
  have h6 : ((X - C d.x₀ : F[X]) ^ 2 - C d.t).natDegree = 2 :=
    (natDegree_sub_eq_left_of_natDegree_lt h4).trans h2
  intro h
  rw [h] at h6; simp at h6

open Polynomial in
/-- The Vélu degree-$2$ map has degree $2$: $\max(\deg u, \deg v) = 2$. -/
theorem velu_deg2_degree_eq_two :
    max (X ^ 2 - C d.x₀ * X + C d.t : F[X]).natDegree
        (X - C d.x₀ : F[X]).natDegree = 2 := by
  rw [d.velu_u_natDegree, natDegree_X_sub_C]; omega

/-- The $2$-torsion kernel point $(x_0, 0)$ lies on the curve: $0^2 = x_0^3 + A x_0 + B$. -/
theorem velu_deg2_kernel_on_curve :
    (0 : F) ^ 2 = d.x₀ ^ 3 + E.A * d.x₀ + E.B := by
  rw [d.root_eq]; ring

/-- The denominators of $\phi_x$ and $\phi_y$ vanish at the kernel point $x_0$. -/
theorem velu_deg2_kernel_denom_vanish :
    d.phi_x_denom d.x₀ = 0 ∧ d.phi_y_denom d.x₀ = 0 := by
  constructor
  · exact sub_self d.x₀
  · simp [phi_y_denom, sub_self]

/-- The kernel of $\phi_x$ is exactly $\{x_0\}$: the denominator does not vanish elsewhere. -/
theorem velu_deg2_kernel_unique {x : F} (hx : x ≠ d.x₀) :
    d.phi_x_denom x ≠ 0 := sub_ne_zero.mpr hx

/-- On the curve, $y^2$ factors as $(x - x_0)(x^2 + x_0 x + x_0^2 + A)$. -/
theorem velu_y_sq_factor {x y : F} (hcurve : y ^ 2 = x ^ 3 + E.A * x + E.B) :
    y ^ 2 = (x - d.x₀) * (x ^ 2 + d.x₀ * x + d.x₀ ^ 2 + E.A) := by
  rw [hcurve]; linear_combination d.root_eq

/-- The Vélu degree-$2$ map sends an on-curve point $(x, y)$ to a point on the image curve. -/
theorem velu_phi_maps_points {x y : F} (hcurve : y ^ 2 = x ^ 3 + E.A * x + E.B) :
    ((x - d.x₀) ^ 2 - d.t) ^ 2 * y ^ 2 =
      (x - d.x₀) * ((x ^ 2 - d.x₀ * x + d.t) ^ 3 +
        d.A' * (x ^ 2 - d.x₀ * x + d.t) * (x - d.x₀) ^ 2 +
        d.B' * (x - d.x₀) ^ 3) := by
  rw [d.velu_y_sq_factor hcurve]
  rw [mul_left_comm]
  congr 1
  exact (d.velu_image_identity x).symm

/-- The Vélu degree-$2$ map is a standard-form separable isogeny of degree $2$. -/
theorem velu_deg2_is_standard_form_separable_deg2 :
    (max (Polynomial.X ^ 2 - Polynomial.C d.x₀ * Polynomial.X +
      Polynomial.C d.t : F[X]).natDegree
      (Polynomial.X - Polynomial.C d.x₀ : F[X]).natDegree = 2) ∧
    (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C d.x₀ *
      Polynomial.X + Polynomial.C d.t : F[X]) * (Polynomial.X - Polynomial.C d.x₀) -
      (Polynomial.X ^ 2 - Polynomial.C d.x₀ * Polynomial.X + Polynomial.C d.t) *
      Polynomial.derivative (Polynomial.X - Polynomial.C d.x₀) ≠ 0) :=
  ⟨d.velu_deg2_degree_eq_two, d.velu_deg2_is_separable⟩

/-- Bundled kernel data for the Vélu degree-$2$ isogeny: the kernel point is on $E$, the
denominators vanish at it, are nonzero elsewhere, and the kernel has order $2$. -/
structure VeluDeg2Kernel (E : ShortWeierstrassCurve F) (d : VeluDeg2Data E) where
  kernel_point_on_E : (0 : F) ^ 2 = d.x₀ ^ 3 + E.A * d.x₀ + E.B
  kernel_point_maps_to_zero : d.phi_x_denom d.x₀ = 0
  nonkernel_welldefined : ∀ x : F, x ≠ d.x₀ → d.phi_x_denom x ≠ 0
  kernel_order : ({(d.x₀, (0 : F))} : Finset (F × F)).card + 1 = 2

/-- The Vélu degree-$2$ kernel data associated to a Vélu degree-$2$ datum. -/
def velu_deg2_kernel : VeluDeg2Kernel E d where
  kernel_point_on_E := d.velu_deg2_kernel_on_curve
  kernel_point_maps_to_zero := (d.velu_deg2_kernel_denom_vanish).1
  nonkernel_welldefined := fun x hx => d.velu_deg2_kernel_unique hx
  kernel_order := by simp [Finset.card_singleton]

/-- Bundled Vélu degree-$2$ isogeny: a standard-form separable degree-$2$ isogeny together with
its kernel datum. -/
structure VeluDeg2Isogeny (E : ShortWeierstrassCurve F) (d : VeluDeg2Data E) where
  phi_maps_points : ∀ (x y : F), y ^ 2 = x ^ 3 + E.A * x + E.B →
    ((x - d.x₀) ^ 2 - d.t) ^ 2 * y ^ 2 =
      (x - d.x₀) * ((x ^ 2 - d.x₀ * x + d.t) ^ 3 +
        d.A' * (x ^ 2 - d.x₀ * x + d.t) * (x - d.x₀) ^ 2 +
        d.B' * (x - d.x₀) ^ 3)
  degree_eq_two : max (Polynomial.X ^ 2 - Polynomial.C d.x₀ * Polynomial.X +
    Polynomial.C d.t : F[X]).natDegree (Polynomial.X - Polynomial.C d.x₀ : F[X]).natDegree = 2
  is_separable : Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C d.x₀ *
    Polynomial.X + Polynomial.C d.t : F[X]) * (Polynomial.X - Polynomial.C d.x₀) -
    (Polynomial.X ^ 2 - Polynomial.C d.x₀ * Polynomial.X + Polynomial.C d.t) *
    Polynomial.derivative (Polynomial.X - Polynomial.C d.x₀) ≠ 0
  kernel : VeluDeg2Kernel E d

/-- The Vélu degree-$2$ isogeny constructed from a Vélu datum. -/
def velu_deg2_isogeny : VeluDeg2Isogeny E d where
  phi_maps_points := fun x y hcurve => d.velu_phi_maps_points hcurve
  degree_eq_two := d.velu_deg2_degree_eq_two
  is_separable := d.velu_deg2_is_separable
  kernel := d.velu_deg2_kernel

end FieldTheorems

end VeluDeg2Data

section VeluOdd

variable {k : Type*} [Field k]

/-- An affine point on a short Weierstrass curve: a pair $(x, y)$ together with a proof that
$y^2 = x^3 + A x + B$. -/
structure AffinePoint (E : ShortWeierstrassCurve k) where
  x : k
  y : k
  on_curve : y ^ 2 = x ^ 3 + E.A * x + E.B

variable {E : ShortWeierstrassCurve k}

/-- Vélu parameter $t_Q = 3 x_Q^2 + A$ associated with an affine point $Q$. -/
def AffinePoint.tQ (Q : AffinePoint E) : k := 3 * Q.x ^ 2 + E.A

/-- Vélu parameter $u_Q = 2 y_Q^2$ associated with an affine point $Q$. -/
def AffinePoint.uQ (Q : AffinePoint E) : k := 2 * Q.y ^ 2

/-- Vélu parameter $w_Q = u_Q + t_Q x_Q$ associated with an affine point $Q$. -/
def AffinePoint.wQ (Q : AffinePoint E) : k := Q.uQ + Q.tQ * Q.x

/-- Unfolds $t_Q$ to its defining formula. -/
@[simp] lemma AffinePoint.tQ_val (Q : AffinePoint E) :
    Q.tQ = 3 * Q.x ^ 2 + E.A := rfl

/-- Unfolds $u_Q$ to its defining formula. -/
@[simp] lemma AffinePoint.uQ_val (Q : AffinePoint E) :
    Q.uQ = 2 * Q.y ^ 2 := rfl

/-- Unfolds $w_Q$ to its defining formula $u_Q + t_Q x_Q$. -/
@[simp] lemma AffinePoint.wQ_val (Q : AffinePoint E) :
    Q.wQ = Q.uQ + Q.tQ * Q.x := rfl

/-- Expanded form $w_Q = 2 y_Q^2 + (3 x_Q^2 + A) x_Q$. -/
lemma AffinePoint.wQ_expanded (Q : AffinePoint E) :
    Q.wQ = 2 * Q.y ^ 2 + (3 * Q.x ^ 2 + E.A) * Q.x := rfl

/-- Using the curve equation, $u_Q = 2(x_Q^3 + A x_Q + B)$. -/
lemma AffinePoint.uQ_eq_curve (Q : AffinePoint E) :
    Q.uQ = 2 * (Q.x ^ 3 + E.A * Q.x + E.B) := by
  simp only [AffinePoint.uQ]
  linear_combination 2 * Q.on_curve

/-- Using the curve equation, $w_Q = 5 x_Q^3 + 3 A x_Q + 2 B$. -/
lemma AffinePoint.wQ_eq_curve (Q : AffinePoint E) :
    Q.wQ = 5 * Q.x ^ 3 + 3 * E.A * Q.x + 2 * E.B := by
  simp only [AffinePoint.wQ, AffinePoint.uQ, AffinePoint.tQ]
  linear_combination 2 * Q.on_curve

/-- Data for the odd-degree Vélu isogeny: a finite set of nonidentity affine points such that
the kernel order $|S| + 1$ is odd. -/
structure VeluOddData (E : ShortWeierstrassCurve k) where
  pts : Finset (AffinePoint E)
  odd_order : Odd (pts.card + 1)

namespace VeluOddData

variable (d : VeluOddData E)

/-- Vélu sum $t = \sum_Q t_Q$ over the kernel points. -/
def t : k := d.pts.sum (fun Q => Q.tQ)

/-- Vélu sum $w = \sum_Q w_Q$ over the kernel points. -/
def w : k := d.pts.sum (fun Q => Q.wQ)

/-- Vélu image coefficient $A' = A - 5 t$. -/
def A' : k := E.A - 5 * d.t

/-- Vélu image coefficient $B' = B - 7 w$. -/
def B' : k := E.B - 7 * d.w

/-- The image curve $E' : y^2 = x^3 + A' x + B'$ of the odd-degree Vélu isogeny. -/
def imageCurve : ShortWeierstrassCurve k := ⟨d.A', d.B'⟩

/-- Unfolding the $A$-coefficient of the image curve. -/
@[simp] lemma imageCurve_A : d.imageCurve.A = d.A' := rfl
/-- Unfolding the $B$-coefficient of the image curve. -/
@[simp] lemma imageCurve_B : d.imageCurve.B = d.B' := rfl

/-- The rational function $r(x) = x + \sum_Q \left(\tfrac{t_Q}{x - x_Q} + \tfrac{u_Q}{(x - x_Q)^2}\right)$
defining the $x$-coordinate component of the Vélu isogeny. -/
noncomputable def r (x : k) : k :=
  x + d.pts.sum (fun Q => Q.tQ / (x - Q.x) + Q.uQ / (x - Q.x) ^ 2)

/-- The derivative $r'(x) = 1 - \sum_Q \left(\tfrac{t_Q}{(x - x_Q)^2} + \tfrac{2 u_Q}{(x - x_Q)^3}\right)$
used in the $y$-coordinate component. -/
noncomputable def r' (x : k) : k :=
  1 + d.pts.sum (fun Q => -(Q.tQ / (x - Q.x) ^ 2) - 2 * Q.uQ / (x - Q.x) ^ 3)

/-- The Vélu odd-degree map sends an on-curve point not in the kernel to a point on the
image curve. -/
theorem velu_odd_maps_to_image (P : AffinePoint E)
    (hP : ∀ Q ∈ d.pts, P.x ≠ Q.x) :
    (d.r' P.x * P.y) ^ 2 =
      (d.r P.x) ^ 3 + d.A' * (d.r P.x) + d.B' := by sorry

/-- The Vélu odd-degree map is a separable isogeny of degree $|S| + 1$. -/
theorem velu_odd_is_separable_isogeny :
    ∃ (α : IsogenyStandardForm k),
      α.IsSeparable ∧ α.degree = d.pts.card + 1 := by sorry

/-- The kernel of the Vélu odd-degree map is precisely the $x$-coordinate set
$\{x_Q : Q \in S\}$. -/
theorem velu_odd_kernel_eq :
    ∃ (α : IsogenyStandardForm k),
      α.degree = d.pts.card + 1 ∧
      ∀ (x : k), Polynomial.eval x α.v = 0 ↔ ∃ Q ∈ d.pts, x = Q.x := by sorry

end VeluOddData

end VeluOdd

end ShortWeierstrassCurve

open Polynomial

/-- Corollary 5.2: in characteristic zero, every isogeny of positive degree is separable. -/
theorem corollary_5_2 {F : Type*} [Field F] [CharZero F]
    (α : IsogenyStandardForm F) (hdeg : 0 < α.degree) : α.IsSeparable := by
  rw [IsogenyStandardForm.IsSeparable]
  intro h


  have hwronskian : α.u.wronskian α.v = 0 := by
    simp only [Polynomial.wronskian]
    linear_combination -h

  have ⟨hu', hv'⟩ := (lemma_5_1_first_iff α.coprime_uv).mp hwronskian

  have hu_const : α.u.natDegree = 0 := natDegree_eq_zero_of_derivative_eq_zero hu'
  have hv_const : α.v.natDegree = 0 := natDegree_eq_zero_of_derivative_eq_zero hv'

  have hdeg_zero : α.degree = 0 := by
    simp [IsogenyStandardForm.degree, hu_const, hv_const]

  omega

/-- An isogeny $\alpha$ over a field of characteristic $p$ has a Frobenius factorisation if it
factors as $\mathrm{Frob}^n \circ \alpha_{\mathrm{sep}}$ for a separable $\alpha_{\mathrm{sep}}$. -/
def IsogenyStandardForm.HasFrobeniusFactorization {F : Type*} [Field F]
    {p : ℕ} [CharP F p] (α : IsogenyStandardForm F) : Prop :=
  ∃ (α_sep : IsogenyStandardForm F) (n : ℕ),
    α_sep.IsSeparable ∧
    α.u = Polynomial.expand F (p ^ n) α_sep.u ∧
    α.v = Polynomial.expand F (p ^ n) α_sep.v ∧
    α.degree = p ^ n * α_sep.degree

namespace IsogenyStandardForm

/-- Frobenius factorisation: over a field of characteristic $p$, every positive-degree isogeny
factors as $\alpha_{\mathrm{sep}}$ composed with $\mathrm{Frob}^n$. -/
theorem frobeniusFactorization {F : Type*} [Field F] {p : ℕ} [CharP F p]
    (hp : Nat.Prime p) (α : IsogenyStandardForm F) (hdeg : 0 < α.degree) :
    ∃ (α_sep : IsogenyStandardForm F) (n : ℕ),
      α_sep.IsSeparable ∧
      α.u = Polynomial.expand F (p ^ n) α_sep.u ∧
      α.v = Polynomial.expand F (p ^ n) α_sep.v ∧
      α.degree = p ^ n * α_sep.degree := by

  have hfact : Fact (Nat.Prime p) := ⟨hp⟩
  have hp_ne : p ≠ 0 := hp.ne_zero
  suffices ∀ (d : ℕ) (α : IsogenyStandardForm F),
      α.degree = d → 0 < d →
      ∃ (α_sep : IsogenyStandardForm F) (n : ℕ),
        α_sep.IsSeparable ∧
        α.u = Polynomial.expand F (p ^ n) α_sep.u ∧
        α.v = Polynomial.expand F (p ^ n) α_sep.v ∧
        α.degree = p ^ n * α_sep.degree by
    exact this α.degree α rfl hdeg
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
  intro α hd hdeg_pos

  by_cases hsep : α.IsSeparable
  · exact ⟨α, 0, hsep,
      by simp [Polynomial.expand_one],
      by simp [Polynomial.expand_one],
      by simp⟩
  ·
    rw [IsogenyStandardForm.IsSeparable] at hsep
    push Not at hsep
    have hinsep : Polynomial.derivative α.u * α.v - α.u * Polynomial.derivative α.v = 0 := hsep
    obtain ⟨u₁, v₁, hu₁, hv₁⟩ := lemma_5_3_x (show p ≠ 0 from hp_ne) α.coprime_uv hinsep
    have hcop₁ : IsCoprime u₁ v₁ := by
      rw [← (Polynomial.isCoprime_expand hp_ne (f := u₁) (g := v₁)), hu₁, hv₁]
      exact α.coprime_uv
    have hv₁_ne : v₁ ≠ 0 := by
      intro habs; rw [habs, map_zero] at hv₁; exact α.v_ne_zero hv₁.symm
    have hdeg_u₁ : α.u.natDegree = u₁.natDegree * p := by
      rw [← hu₁, Polynomial.natDegree_expand]
    have hdeg_v₁ : α.v.natDegree = v₁.natDegree * p := by
      rw [← hv₁, Polynomial.natDegree_expand]

    let α₁ : IsogenyStandardForm F :=
      ⟨u₁, v₁, α.s, α.t, hv₁_ne, α.t_ne_zero, hcop₁, α.coprime_st⟩
    have hdeg_α₁ : α₁.degree * p = α.degree := by
      unfold IsogenyStandardForm.degree
      simp only [α₁]
      rw [hdeg_u₁, hdeg_v₁]
      rcases le_or_gt u₁.natDegree v₁.natDegree with h | h
      · rw [max_eq_right (Nat.mul_le_mul_right p h), max_eq_right h]
      · rw [max_eq_left (Nat.mul_le_mul_right p (Nat.le_of_lt_succ (Nat.lt_succ_of_lt h))),
             max_eq_left (Nat.le_of_lt_succ (Nat.lt_succ_of_lt h))]
    have hdeg_α₁_pos : 0 < α₁.degree := by
      by_contra h
      push Not at h
      interval_cases α₁.degree
      simp at hdeg_α₁; omega
    have hdeg_lt : α₁.degree < d := by
      have heq : α₁.degree * p = d := by omega
      nlinarith [hp.one_lt]
    obtain ⟨α_sep, m, hsep_m, hu_m, hv_m, hdeg_m⟩ :=
      ih α₁.degree hdeg_lt α₁ rfl hdeg_α₁_pos

    have hu₁_eq : u₁ = (Polynomial.expand F (p ^ m)) α_sep.u := hu_m
    have hv₁_eq : v₁ = (Polynomial.expand F (p ^ m)) α_sep.v := hv_m
    refine ⟨α_sep, m + 1, hsep_m, ?_, ?_, ?_⟩
    ·
      rw [show p ^ (m + 1) = p ^ m * p from pow_succ p m]
      rw [← hu₁, hu₁_eq, Polynomial.expand_expand, Nat.mul_comm]
    · rw [show p ^ (m + 1) = p ^ m * p from pow_succ p m]
      rw [← hv₁, hv₁_eq, Polynomial.expand_expand, Nat.mul_comm]
    ·
      rw [show p ^ (m + 1) = p ^ m * p from pow_succ p m,
          show p ^ m * p * α_sep.degree = α₁.degree * p by rw [hdeg_m]; ring,
          hdeg_α₁]

end IsogenyStandardForm

namespace ShortWeierstrassCurve

variable {k : Type uSWC} [Field k] (E : ShortWeierstrassCurve k)

/-- Over an elliptic curve, the derivative of $\Phi_n$ is nonzero whenever $n \neq 0$ in $k$.
This is the key separability ingredient for $[n]$. -/
lemma derivative_Phi_ne_zero {n : ℤ} (hn : (n : k) ≠ 0) :
    Polynomial.derivative (E.toWeierstrassCurve.Φ n) ≠ 0 := by
  intro hd
  have h_deg := E.toWeierstrassCurve.natDegree_Φ n
  have h_lc := E.toWeierstrassCurve.leadingCoeff_Φ n
  have h_nabs : n.natAbs ≠ 0 := by
    intro h; exact hn (by simp [Int.natAbs_eq_zero.mp h])
  have h_pos : 1 ≤ n.natAbs ^ 2 := Nat.one_le_pow 2 n.natAbs (Nat.pos_of_ne_zero h_nabs)
  have h_coeff : Polynomial.coeff (Polynomial.derivative (E.toWeierstrassCurve.Φ n))
      ((E.toWeierstrassCurve.Φ n).natDegree - 1) = 0 := by
    rw [hd]; simp
  rw [Polynomial.coeff_derivative] at h_coeff
  have hsub1 : (E.toWeierstrassCurve.Φ n).natDegree - 1 + 1 =
      (E.toWeierstrassCurve.Φ n).natDegree := by rw [h_deg]; omega
  rw [hsub1, Polynomial.coeff_natDegree, h_lc, one_mul, h_deg] at h_coeff
  set m := n.natAbs ^ 2 - 1 with hm_def
  have hm_succ : m + 1 = n.natAbs ^ 2 := by omega
  have h_zero : (↑(n.natAbs ^ 2) : k) = 0 := by
    rw [← hm_succ, Nat.cast_add, Nat.cast_one]; exact h_coeff
  have h_sq : (n : k) ^ 2 = (↑(n.natAbs) : k) ^ 2 := by
    have h : (n : ℤ) ^ 2 = (↑(n.natAbs) : ℤ) ^ 2 := by simp
    have h2 := congr_arg (Int.cast : ℤ → k) h
    push_cast at h2; rw [Int.abs_eq_natAbs] at h2; norm_cast at h2 ⊢
  have : (n : k) ^ 2 = 0 := by rw [h_sq, ← Nat.cast_pow]; exact h_zero
  exact pow_ne_zero 2 hn this

/-- The multiplication-by-$n$ map packaged as an `IsogenyStandardForm`: numerator $\Phi_n$,
denominator $\Psi_n^2$, on the elliptic short Weierstrass curve. -/
noncomputable def mulByNStandardForm [E.toWeierstrassCurve.IsElliptic] {n : ℤ} (hn : (n : k) ≠ 0) :
    IsogenyStandardForm k where
  u := E.toWeierstrassCurve.Φ n
  v := E.toWeierstrassCurve.ΨSq n
  s := 1
  t := 1
  v_ne_zero := E.toWeierstrassCurve.ΨSq_ne_zero hn
  t_ne_zero := one_ne_zero
  coprime_uv := E.Phi_ΨSq_isCoprime n
  coprime_st := isCoprime_one_right

/-- Degree part of Theorem 5.25: $\deg[n] = n^2$ (when $n \neq 0$ in $k$). -/
theorem theorem_5_25_degree [E.toWeierstrassCurve.IsElliptic] {n : ℤ} (hn : (n : k) ≠ 0) :
    (E.mulByNStandardForm hn).degree = n.natAbs ^ 2 := by
  simp only [mulByNStandardForm, IsogenyStandardForm.degree]
  rw [E.toWeierstrassCurve.natDegree_Φ n, E.toWeierstrassCurve.natDegree_ΨSq hn]
  have : 1 ≤ n.natAbs ^ 2 := by
    have : n.natAbs ≠ 0 := by intro h; exact hn (by simp [Int.natAbs_eq_zero.mp h])
    exact Nat.one_le_pow 2 n.natAbs (Nat.pos_of_ne_zero this)
  omega

/-- Separability part of Theorem 5.25: $[n]$ is separable when $n \neq 0$ in $k$. -/
theorem theorem_5_25_separable [E.toWeierstrassCurve.IsElliptic] {n : ℤ} (hn : (n : k) ≠ 0) :
    (E.mulByNStandardForm hn).IsSeparable := by
  simp only [IsogenyStandardForm.IsSeparable, mulByNStandardForm]
  intro h_insep
  have h_wron : (E.toWeierstrassCurve.Φ n).wronskian (E.toWeierstrassCurve.ΨSq n) = 0 := by
    simp only [Polynomial.wronskian]; linear_combination -h_insep
  have ⟨hd_Phi, _⟩ := (lemma_5_1_first_iff (E.Phi_ΨSq_isCoprime n)).mp h_wron
  exact E.derivative_Phi_ne_zero hn hd_Phi

/-- When $n$ vanishes in $k$ (char $p \mid n$), both $\Phi_n$ and $\Psi_n^2$ are images of
the Frobenius expansion: there exist polynomials $f, g$ with
$\mathrm{expand}_p f = \Phi_n$, $\mathrm{expand}_p g = \Psi_n^2$. -/
theorem divpoly_frobenius_structure {k : Type uSWC} [Field k]
    (E : ShortWeierstrassCurve k) {n : ℤ} (hn : n ≠ 0) (hc : (n : k) = 0) :
    ∃ (f g : k[X]),
      Polynomial.expand k (ringChar k) f = E.toWeierstrassCurve.Φ n ∧
      Polynomial.expand k (ringChar k) g = E.toWeierstrassCurve.ΨSq n := by sorry

/-- Inseparability case of Theorem 5.25: when $n$ vanishes in $k$, the Wronskian of $\Phi_n$
and $\Psi_n^2$ is zero, so $[n]$ is inseparable. -/
theorem theorem_5_25_inseparable {n : ℤ} (hn_ne_zero : n ≠ 0) (hn_char : (n : k) = 0) :
    Polynomial.derivative (E.toWeierstrassCurve.Φ n) * E.toWeierstrassCurve.ΨSq n -
    E.toWeierstrassCurve.Φ n * Polynomial.derivative (E.toWeierstrassCurve.ΨSq n) = 0 := by
  obtain ⟨f, g, hf, hg⟩ := divpoly_frobenius_structure E hn_ne_zero hn_char
  have hΦ' : Polynomial.derivative (E.toWeierstrassCurve.Φ n) = 0 := by
    rw [← hf, Polynomial.derivative_expand]; simp
  have hΨ' : Polynomial.derivative (E.toWeierstrassCurve.ΨSq n) = 0 := by
    rw [← hg, Polynomial.derivative_expand]; simp
  rw [hΦ', hΨ']; simp

/-- Theorem 5.25 (separability $\iff$ $n$-nonvanishing): $[n]$ is separable iff $n \neq 0$ in $k$. -/
theorem theorem_5_25_separable_iff [E.toWeierstrassCurve.IsElliptic] {n : ℤ} (hn : n ≠ 0) :
    (Polynomial.derivative (E.toWeierstrassCurve.Φ n) * E.toWeierstrassCurve.ΨSq n -
     E.toWeierstrassCurve.Φ n * Polynomial.derivative (E.toWeierstrassCurve.ΨSq n) ≠ 0) ↔
    (n : k) ≠ 0 := by
  constructor
  ·
    intro hwron hn_char
    exact hwron (E.theorem_5_25_inseparable hn hn_char)
  ·
    intro hne
    have hsep := E.theorem_5_25_separable hne
    simp only [IsogenyStandardForm.IsSeparable, mulByNStandardForm] at hsep
    exact hsep

/-- General degree formula: for any nonzero $n$, $\max(\deg \Phi_n, \deg \Psi_n^2) = n^2$. -/
theorem theorem_5_25_degree_general (n : ℤ) (hn : n ≠ 0) :
    max (E.toWeierstrassCurve.Φ n).natDegree
        (E.toWeierstrassCurve.ΨSq n).natDegree = n.natAbs ^ 2 := by
  rw [E.toWeierstrassCurve.natDegree_Φ n]
  have hle : (E.toWeierstrassCurve.ΨSq n).natDegree ≤ n.natAbs ^ 2 - 1 :=
    E.toWeierstrassCurve.natDegree_ΨSq_le n
  have h1 : 1 ≤ n.natAbs ^ 2 := by
    have : 1 ≤ n.natAbs := Int.natAbs_pos.mpr hn
    calc 1 = 1 ^ 2 := by ring
    _ ≤ n.natAbs ^ 2 := Nat.pow_le_pow_left this 2
  omega

/-- Theorem 5.25 (combined): for nonzero $n$, $[n]$ has degree $n^2$ and is separable iff
$n \neq 0$ in $k$. -/
theorem theorem_5_25 [E.toWeierstrassCurve.IsElliptic] {n : ℤ} (hn : n ≠ 0) :
    max (E.toWeierstrassCurve.Φ n).natDegree
        (E.toWeierstrassCurve.ΨSq n).natDegree = n.natAbs ^ 2 ∧
    ((Polynomial.derivative (E.toWeierstrassCurve.Φ n) * E.toWeierstrassCurve.ΨSq n -
      E.toWeierstrassCurve.Φ n * Polynomial.derivative (E.toWeierstrassCurve.ΨSq n) ≠ 0) ↔
     (n : k) ≠ 0) :=
  ⟨E.theorem_5_25_degree_general n hn, E.theorem_5_25_separable_iff hn⟩

end ShortWeierstrassCurve

namespace IsogenyStandardForm

variable {F : Type*} [Field F]

/-- An isogeny $\alpha$ has separable degree $d$ if it factors as
$\mathrm{Frob}^n \circ \alpha_{\mathrm{sep}}$ with $\deg \alpha_{\mathrm{sep}} = d$. -/
def HasSeparableDegree {p : ℕ} (_hp : Nat.Prime p) [CharP F p]
    (α : IsogenyStandardForm F) (d : ℕ) : Prop :=
  ∃ (α_sep : IsogenyStandardForm F) (n : ℕ),
    α_sep.IsSeparable ∧
    α.u = Polynomial.expand F (p ^ n) α_sep.u ∧
    α.v = Polynomial.expand F (p ^ n) α_sep.v ∧
    α_sep.degree = d

/-- An isogeny $\alpha$ has inseparable degree $d = p^n$ if its Frobenius factorisation has
exponent $n$. -/
def HasInseparableDegree {p : ℕ} (_hp : Nat.Prime p) [CharP F p]
    (α : IsogenyStandardForm F) (d : ℕ) : Prop :=
  ∃ (α_sep : IsogenyStandardForm F) (n : ℕ),
    α_sep.IsSeparable ∧
    α.u = Polynomial.expand F (p ^ n) α_sep.u ∧
    α.v = Polynomial.expand F (p ^ n) α_sep.v ∧
    d = p ^ n

/-- An isogeny is purely inseparable if its separable degree is $1$. -/
def IsPurelyInseparable' {p : ℕ} (hp : Nat.Prime p) [CharP F p]
    (α : IsogenyStandardForm F) : Prop :=
  α.HasSeparableDegree hp 1

/-- The separable degree of a standard-form isogeny: the maximum of the separable degrees of
its numerator and denominator. -/
noncomputable def separableDegree (α : IsogenyStandardForm F) : ℕ :=
  max α.u.natSepDegree α.v.natSepDegree

/-- The inseparable degree of a standard-form isogeny: total degree divided by separable
degree. -/
noncomputable def inseparableDegree (α : IsogenyStandardForm F) : ℕ :=
  α.degree / α.separableDegree

/-- An isogeny is purely inseparable if its separable degree equals $1$. -/
def IsPurelyInseparable (α : IsogenyStandardForm F) : Prop :=
  α.separableDegree = 1

/-- Existence of separable degree: every positive-degree isogeny over a positive-characteristic
field has a separable degree. -/
theorem exists_separableDegree {p : ℕ} (hp : Nat.Prime p) [CharP F p]
    (α : IsogenyStandardForm F) (hdeg : 0 < α.degree) :
    ∃ d, α.HasSeparableDegree hp d := by
  obtain ⟨α_sep, n, hsep, hu, hv, _⟩ := frobeniusFactorization hp α hdeg
  exact ⟨α_sep.degree, α_sep, n, hsep, hu, hv, rfl⟩

/-- The total degree of $\alpha$ equals $p^n$ times its separable degree, witnessing the
$\deg = \deg_{\mathrm{insep}} \cdot \deg_{\mathrm{sep}}$ decomposition. -/
theorem degree_eq_insep_mul_sep {p : ℕ} (_hp : Nat.Prime p) [CharP F p]
    (α : IsogenyStandardForm F) (_hdeg : 0 < α.degree)
    {d : ℕ} (hs : α.HasSeparableDegree _hp d) :
    ∃ n, α.degree = p ^ n * d := by
  obtain ⟨α_sep, n, _, hu, hv, hd⟩ := hs
  refine ⟨n, ?_⟩
  subst hd
  unfold degree
  rw [hu, hv, Polynomial.natDegree_expand, Polynomial.natDegree_expand]
  rcases le_or_gt α_sep.u.natDegree α_sep.v.natDegree with h | h
  · rw [max_eq_right h, max_eq_right (Nat.mul_le_mul_right _ h), Nat.mul_comm]
  · rw [max_eq_left (Nat.le_of_lt_succ (Nat.lt_succ_of_lt h)),
         max_eq_left (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ (Nat.lt_succ_of_lt h))),
         Nat.mul_comm]

end IsogenyStandardForm

namespace IsogenyStandardForm

/-- The size of the kernel of $\alpha$, computed as $\max(\mathrm{natSepDegree}(u),
\mathrm{natSepDegree}(v))$. -/
noncomputable def kernelSize {F : Type*} [Field F]
    (α : IsogenyStandardForm F) : ℕ := max α.u.natSepDegree α.v.natSepDegree

/-- The size of the kernel of $\alpha$ as an abstract group; this agrees with
`kernelSize` (cf. `groupKernelSize_eq_separableDegree`). -/
noncomputable def groupKernelSize {F : Type*} [Field F]
    (α : IsogenyStandardForm F) : ℕ := by sorry

/-- The group-theoretic kernel size equals the separable degree. -/
theorem groupKernelSize_eq_separableDegree {F : Type*} [Field F]
    (α : IsogenyStandardForm F) (hdeg : 0 < α.degree) :
    α.groupKernelSize = α.separableDegree := by sorry

/-- The polynomial kernel size equals the separable degree (for a Frobenius factorisation
witness). -/
theorem kernelSize_eq_separableDegree {F : Type*} [Field F] {p : ℕ} [CharP F p]
    (hp : Nat.Prime p)
    (α : IsogenyStandardForm F) (hdeg : 0 < α.degree)
    (d : ℕ) (hd : α.HasSeparableDegree hp d) :
    α.kernelSize = d := by sorry

end IsogenyStandardForm

/-- Corollary 5.9: a purely inseparable Frobenius factorisation (separable degree $1$) implies
the isogeny has kernel size $1$. -/
theorem corollary_5_9 {F : Type*} [Field F] {p : ℕ} [CharP F p]
    (hp : Nat.Prime p)
    (α : IsogenyStandardForm F) (_hdeg : 0 < α.degree)
    (α_sep : IsogenyStandardForm F) (n : ℕ)
    (_hsep : α_sep.IsSeparable)
    (hu : α.u = Polynomial.expand F (p ^ n) α_sep.u)
    (hv : α.v = Polynomial.expand F (p ^ n) α_sep.v)
    (hpure : α_sep.degree = 1) :
    α.kernelSize = 1 := by
  haveI : ExpChar F p := ExpChar.prime hp
  show max α.u.natSepDegree α.v.natSepDegree = 1
  rw [hu, hv, Polynomial.natSepDegree_expand _ p, Polynomial.natSepDegree_expand _ p]
  have hu_le := Polynomial.natSepDegree_le_natDegree α_sep.u
  have hv_le := Polynomial.natSepDegree_le_natDegree α_sep.v
  unfold IsogenyStandardForm.degree at hpure
  rcases le_or_gt α_sep.u.natDegree α_sep.v.natDegree with huv | huv
  · rw [max_eq_right huv] at hpure
    have := Polynomial.natSepDegree_ne_zero α_sep.v (by omega)
    omega
  · rw [max_eq_left (le_of_lt huv)] at hpure
    have := Polynomial.natSepDegree_ne_zero α_sep.u (by omega)
    omega

/-- Corollary 5.9' (packaged form): if $\alpha$ is purely inseparable then its kernel size
is $1$. -/
theorem corollary_5_9' {F : Type*} [Field F] {p : ℕ} [CharP F p]
    (hp : Nat.Prime p)
    (α : IsogenyStandardForm F) (hdeg : 0 < α.degree)
    (hpure : α.IsPurelyInseparable' hp) :
    α.kernelSize = 1 := by
  obtain ⟨α_sep, n, hsep, hu, hv, hd⟩ := hpure
  exact corollary_5_9 hp α hdeg α_sep n hsep hu hv hd

/-- Converse direction: if $\alpha$ has kernel size $1$ then it is purely inseparable. -/
theorem purelyInseparable_of_kernelSize_eq_one {F : Type*} [Field F] {p : ℕ} [CharP F p]
    (hp : Nat.Prime p)
    (α : IsogenyStandardForm F) (hdeg : 0 < α.degree)
    (hker : α.kernelSize = 1) :
    α.IsPurelyInseparable' hp := by
  obtain ⟨d, hsd⟩ := α.exists_separableDegree hp hdeg
  have hkd : α.kernelSize = d := IsogenyStandardForm.kernelSize_eq_separableDegree hp α hdeg d hsd
  rw [hker] at hkd
  subst hkd
  exact hsd

namespace IsogenyStandardForm

variable {F : Type*} [Field F]

open Polynomial

/-- The rational function $u/v \in K(F[X])$ representing the $x$-coordinate of a standard-form
isogeny in the fraction field. -/
noncomputable def xCoordRatFun (α : IsogenyStandardForm F) : FractionRing (Polynomial F) :=
  IsLocalization.mk' _ α.u ⟨α.v, mem_nonZeroDivisors_of_ne_zero α.v_ne_zero⟩

/-- Evaluate a polynomial $p \in F[X]$ at a rational function $r \in K$ by substitution. -/
noncomputable def evalAtRatFun (p : Polynomial F) (r : FractionRing (Polynomial F)) :
    FractionRing (Polynomial F) :=
  Polynomial.eval₂ (algebraMap _ (FractionRing (Polynomial F))) r p

/-- The composition of two $x$-coordinate rational functions $\beta \circ \gamma$ in the
fraction field. -/
noncomputable def compXCoord (β γ : IsogenyStandardForm F) : FractionRing (Polynomial F) :=
  evalAtRatFun β.u γ.xCoordRatFun / evalAtRatFun β.v γ.xCoordRatFun

/-- $\alpha = \beta \circ \gamma$ as rational $x$-coordinate maps: the $x$-coordinate rational
function of $\alpha$ equals the composition of those of $\beta$ and $\gamma$. -/
def IsCompOf (α β γ : IsogenyStandardForm F) : Prop :=
  α.xCoordRatFun = compXCoord β γ

/-- A separable-degree witness gives an inseparable-degree witness $p^n$ and a degree
factorisation $\deg \alpha = p^n \cdot d$. -/
lemma HasSeparableDegree.insepDegree_and_factorization {p : ℕ} (hp : Nat.Prime p) [CharP F p]
    {α : IsogenyStandardForm F} {d : ℕ} (hs : α.HasSeparableDegree hp d) :
    ∃ n, α.HasInseparableDegree hp (p ^ n) ∧ α.degree = p ^ n * d := by
  obtain ⟨α_sep, n, hsep, hu, hv, hd⟩ := hs
  refine ⟨n, ⟨α_sep, n, hsep, hu, hv, rfl⟩, ?_⟩
  subst hd
  unfold degree
  rw [hu, hv, Polynomial.natDegree_expand, Polynomial.natDegree_expand]
  rcases le_or_gt α_sep.u.natDegree α_sep.v.natDegree with h | h
  · rw [max_eq_right h, max_eq_right (Nat.mul_le_mul_right _ h), Nat.mul_comm]
  · rw [max_eq_left (Nat.le_of_lt_succ (Nat.lt_succ_of_lt h)),
         max_eq_left (Nat.mul_le_mul_right _ (Nat.le_of_lt_succ (Nat.lt_succ_of_lt h))),
         Nat.mul_comm]

end IsogenyStandardForm

/-- Multiplicativity of separable degree under composition: $d_\alpha = d_\beta \cdot d_\gamma$
when $\alpha = \beta \circ \gamma$. -/
theorem separableDegree_comp_mul {F : Type*} [Field F] {p : ℕ} [CharP F p]
    (hp : Nat.Prime p)
    (α β γ : IsogenyStandardForm F)
    (hcomp : α.IsCompOf β γ)
    (hdα : 0 < α.degree) (hdβ : 0 < β.degree) (hdγ : 0 < γ.degree)
    {dα dβ dγ : ℕ}
    (hsα : α.HasSeparableDegree hp dα)
    (hsβ : β.HasSeparableDegree hp dβ)
    (hsγ : γ.HasSeparableDegree hp dγ) :
    dα = dβ * dγ := by sorry

/-- Multiplicativity of inseparable degree under composition: $i_\alpha = i_\beta \cdot i_\gamma$
when $\alpha = \beta \circ \gamma$. -/
theorem inseparableDegree_comp_mul {F : Type*} [Field F] {p : ℕ} [CharP F p]
    (hp : Nat.Prime p)
    (α β γ : IsogenyStandardForm F)
    (hcomp : α.IsCompOf β γ)
    (hdα : 0 < α.degree) (hdβ : 0 < β.degree) (hdγ : 0 < γ.degree)
    {iα iβ iγ : ℕ}
    (hiα : α.HasInseparableDegree hp iα)
    (hiβ : β.HasInseparableDegree hp iβ)
    (hiγ : γ.HasInseparableDegree hp iγ) :
    iα = iβ * iγ := by sorry

/-- Multiplicativity of total degree under composition: $\deg \alpha = \deg \beta \cdot \deg
\gamma$ when $\alpha = \beta \circ \gamma$, obtained by combining separable and inseparable
multiplicativity. -/
theorem degree_comp_mul {F : Type*} [Field F] {p : ℕ} [CharP F p]
    (hp : Nat.Prime p)
    (α β γ : IsogenyStandardForm F)
    (hcomp : α.IsCompOf β γ)
    (hdα : 0 < α.degree) (hdβ : 0 < β.degree) (hdγ : 0 < γ.degree)
    {dα dβ dγ : ℕ}
    (hsα : α.HasSeparableDegree hp dα)
    (hsβ : β.HasSeparableDegree hp dβ)
    (hsγ : γ.HasSeparableDegree hp dγ) :
    α.degree = β.degree * γ.degree := by

  obtain ⟨nα, hiα, hdegα⟩ := hsα.insepDegree_and_factorization hp
  obtain ⟨nβ, hiβ, hdegβ⟩ := hsβ.insepDegree_and_factorization hp
  obtain ⟨nγ, hiγ, hdegγ⟩ := hsγ.insepDegree_and_factorization hp

  have h_sep := separableDegree_comp_mul hp α β γ hcomp hdα hdβ hdγ hsα hsβ hsγ

  have h_insep := inseparableDegree_comp_mul hp α β γ hcomp hdα hdβ hdγ hiα hiβ hiγ


  rw [hdegα, hdegβ, hdegγ, h_sep, h_insep]
  ring

/-- Corollary 5.10 (combined): for a composition $\alpha = \beta \circ \gamma$, the total,
separable, and inseparable degrees are all multiplicative. -/
theorem corollary_5_10 {F : Type*} [Field F] {p : ℕ} [CharP F p]
    (hp : Nat.Prime p)
    (α β γ : IsogenyStandardForm F)
    (hcomp : α.IsCompOf β γ)
    (hdα : 0 < α.degree) (hdβ : 0 < β.degree) (hdγ : 0 < γ.degree)
    {dα dβ dγ iα iβ iγ : ℕ}
    (hsα : α.HasSeparableDegree hp dα)
    (hsβ : β.HasSeparableDegree hp dβ)
    (hsγ : γ.HasSeparableDegree hp dγ)
    (hiα : α.HasInseparableDegree hp iα)
    (hiβ : β.HasInseparableDegree hp iβ)
    (hiγ : γ.HasInseparableDegree hp iγ) :
    α.degree = β.degree * γ.degree ∧ dα = dβ * dγ ∧ iα = iβ * iγ :=
  ⟨degree_comp_mul hp α β γ hcomp hdα hdβ hdγ hsα hsβ hsγ,
   separableDegree_comp_mul hp α β γ hcomp hdα hdβ hdγ hsα hsβ hsγ,
   inseparableDegree_comp_mul hp α β γ hcomp hdα hdβ hdγ hiα hiβ hiγ⟩

/-- Quotient existence: for any finite subgroup $G \subseteq E(F)$, there exists a quotient
isogeny $\phi : E \to E/G$ realising $G$ as $\ker \phi$ and with $\deg \phi = |G|$. -/
theorem quotient_curve_exists {F : Type uSWC} [Field F] [DecidableEq F]
    (E : WeierstrassCurve.Affine F)
    (G : AddSubgroup E.Point) [Finite G] :
    ∃ (E' : WeierstrassCurve.Affine F) (φ : Isogeny E E'),
      φ.toAddMonoidHom.ker = G ∧ φ.degree = Nat.card G := by sorry

/-- Every isogeny admits an `IsogenyRepresentation` (a rational standard-form representation
of its action on coordinates). -/
noncomputable def isogeny_has_representation {F : Type uSWC} [Field F] [DecidableEq F]
    {E E' : WeierstrassCurve.Affine F}
    (φ : Isogeny E E') :
    Isogeny.IsogenyRepresentation E E' φ := by sorry

/-- The standard-form representation of a quotient isogeny is separable. -/
theorem quotient_isogeny_rep_is_separable {F : Type uSWC} [Field F] [DecidableEq F]
    {E E' : WeierstrassCurve.Affine F}
    (φ : Isogeny E E')
    (G : AddSubgroup E.Point) [Finite G]
    (hker : φ.toAddMonoidHom.ker = G)
    (rep : Isogeny.IsogenyRepresentation E E' φ) :
    rep.toIsogenyStandardForm.IsSeparable := by sorry

/-- Packaging: a quotient isogeny admits a separable standard-form representation. -/
theorem quotient_isogeny_separable_rep {F : Type uSWC} [Field F] [DecidableEq F]
    {E E' : WeierstrassCurve.Affine F}
    (φ : Isogeny E E')
    (G : AddSubgroup E.Point) [Finite G]
    (hker : φ.toAddMonoidHom.ker = G) :
    ∃ (rep : Isogeny.IsogenyRepresentation E E' φ),
      rep.toIsogenyStandardForm.IsSeparable :=
  ⟨isogeny_has_representation φ, quotient_isogeny_rep_is_separable φ G hker _⟩

/-- For every finite subgroup $G$ of $E$, there is an isogeny $\phi : E \to E'$ with kernel
$G$, degree $|G|$, and admitting a separable standard-form representation. -/
theorem Isogeny.exists_separable_of_finite_subgroup {F : Type uSWC} [Field F] [DecidableEq F]
    (E : WeierstrassCurve.Affine F)
    (G : AddSubgroup E.Point) [Finite G] :
    ∃ (E' : WeierstrassCurve.Affine F) (φ : Isogeny E E')
      (rep : Isogeny.IsogenyRepresentation E E' φ),
      φ.toAddMonoidHom.ker = G ∧
      φ.degree = Nat.card G ∧
      rep.toIsogenyStandardForm.IsSeparable := by
  obtain ⟨E', φ, hker, hdeg⟩ := quotient_curve_exists E G
  obtain ⟨rep, hsep⟩ := quotient_isogeny_separable_rep φ G hker
  exact ⟨E', φ, rep, hker, hdeg, hsep⟩

/-- Uniqueness up to isomorphism: any two quotient isogenies with the same kernel $G$ differ
by a degree-$1$ isogeny. -/
theorem Isogeny.exists_separable_of_finite_subgroup_unique {F : Type uSWC} [Field F] [DecidableEq F]
    (E : WeierstrassCurve.Affine F)
    (G : AddSubgroup E.Point) [Finite G]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (φ : Isogeny E E₁) (ψ : Isogeny E E₂)
    (hφ : φ.toAddMonoidHom.ker = G)
    (hψ : ψ.toAddMonoidHom.ker = G) :
    ∃ (ι : Isogeny E₁ E₂), ι.degree = 1 ∧ ∀ P, ψ P = ι (φ P) := by

  have hle : φ.toAddMonoidHom.ker ≤ ψ.toAddMonoidHom.ker := by rw [hφ, hψ]

  let ι_hom := AddMonoidHom.liftOfSurjective φ.toAddMonoidHom φ.surjective
    ⟨ψ.toAddMonoidHom, hle⟩

  have ι_surj : Function.Surjective ι_hom := by
    intro Q
    obtain ⟨P, hP⟩ := ψ.surjective Q
    exact ⟨φ P, by simp [ι_hom, AddMonoidHom.liftOfSurjective, hP]⟩

  refine ⟨⟨ι_hom, ι_surj, 1, Nat.one_pos⟩, rfl, ?_⟩

  intro P
  show ψ.toAddMonoidHom P = ι_hom (φ.toAddMonoidHom P)
  simp [ι_hom, AddMonoidHom.liftOfSurjective]

/-- Auxiliary statement for prime-degree factorisation: any divisor $d$ of $\alpha$.degree
admits a length-$2$ decomposition with degrees $p$ and $d/p$. -/
theorem isogeny_prime_degree_factor_aux {F : Type*} [Field F]
    (d k p : ℕ) (hp : Nat.Prime p) (hdvd : p ∣ d) (hd : 1 < d)
    (hk_pos : 0 < k) (hk_le : k ≤ d) :
    ∃ (β γ : IsogenyStandardForm F),
      β.degree = p ∧ γ.degree = d / p ∧
      β.kernelSize * γ.kernelSize = k := by sorry

/-- Prime-degree factorisation: an isogeny of degree $> 1$ factors as $\beta \circ \gamma$
with $\deg \beta = p$ for any prime $p$ dividing $\deg \alpha$. -/
theorem isogeny_prime_degree_factor {F : Type*} [Field F]
    (α : IsogenyStandardForm F) (hdeg : 1 < α.degree)
    (p : ℕ) (hp : Nat.Prime p) (hdvd : p ∣ α.degree) :
    ∃ (β γ : IsogenyStandardForm F),
      0 < β.degree ∧ 0 < γ.degree ∧
      β.degree = p ∧
      α.degree = β.degree * γ.degree ∧
      α.kernelSize = β.kernelSize * γ.kernelSize := by
  have hk_pos : 0 < α.kernelSize := by
    show 0 < max α.u.natSepDegree α.v.natSepDegree
    have hdeg' : 1 < max α.u.natDegree α.v.natDegree := hdeg
    by_cases h : α.u.natDegree ≤ α.v.natDegree
    · have hv : α.v.natDegree ≠ 0 := by
        have := max_eq_right h ▸ hdeg'; omega
      exact lt_of_lt_of_le (Nat.pos_of_ne_zero (α.v.natSepDegree_ne_zero hv))
        (le_max_right _ _)
    · have hu : α.u.natDegree ≠ 0 := by omega
      exact lt_of_lt_of_le (Nat.pos_of_ne_zero (α.u.natSepDegree_ne_zero hu))
        (le_max_left _ _)
  have hk_le : α.kernelSize ≤ α.degree :=
    max_le_max α.u.natSepDegree_le_natDegree α.v.natSepDegree_le_natDegree
  obtain ⟨β, γ, hβ_deg, hγ_deg, hker⟩ :=
    isogeny_prime_degree_factor_aux (F := F) α.degree α.kernelSize p hp hdvd hdeg hk_pos hk_le
  refine ⟨β, γ, ?_, ?_, hβ_deg, ?_, hker.symm⟩
  · rw [hβ_deg]; exact hp.pos
  · rw [hγ_deg]; exact Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hp.pos
  · rw [hβ_deg, hγ_deg]; exact (Nat.mul_div_cancel' hdvd).symm

open WeierstrassCurve.Affine in
/-- A chain of isogenies between Weierstrass curves: either a single isogeny or one followed
by a further chain. -/
inductive IsogenyChain {F : Type*} [Field F] [DecidableEq F] :
    WeierstrassCurve.Affine F → WeierstrassCurve.Affine F → Type _ where
  | single {E₁ E₂ : WeierstrassCurve.Affine F} (φ : Isogeny E₁ E₂) :
      IsogenyChain E₁ E₂
  | cons {E₁ E₂ E₃ : WeierstrassCurve.Affine F} (φ : Isogeny E₁ E₂)
      (rest : IsogenyChain E₂ E₃) : IsogenyChain E₁ E₃

open WeierstrassCurve.Affine in
/-- The compose of an `IsogenyChain` as an additive group homomorphism on point groups. -/
def IsogenyChain.compose {F : Type*} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F} :
    IsogenyChain E₁ E₂ → (E₁.Point →+ E₂.Point)
  | .single φ => φ.toAddMonoidHom
  | .cons φ rest => rest.compose.comp φ.toAddMonoidHom

open WeierstrassCurve.Affine in
/-- Predicate asserting that every link in an `IsogenyChain` has prime degree. -/
def IsogenyChain.allPrimeDegree {F : Type*} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F} :
    IsogenyChain E₁ E₂ → Prop
  | .single φ => Nat.Prime φ.degree
  | .cons φ rest => Nat.Prime φ.degree ∧ rest.allPrimeDegree

open WeierstrassCurve.Affine in
/-- Prime-degree factorisation of a single isogeny: an isogeny of degree $> 1$ factors as
$\gamma \circ \beta$ with $\deg \beta = p$ for any prime $p \mid \deg \alpha$. -/
theorem isogeny_prime_factor {F : Type*} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) (hdeg : 1 < α.degree)
    (p : ℕ) (hp : Nat.Prime p) (hdvd : p ∣ α.degree) :
    ∃ (E_mid : WeierstrassCurve.Affine F)
      (β : Isogeny E₁ E_mid) (γ : Isogeny E_mid E₂),
      β.degree = p ∧
      0 < γ.degree ∧
      γ.degree * β.degree = α.degree ∧
      γ.toAddMonoidHom.comp β.toAddMonoidHom = α.toAddMonoidHom :=
  Isogeny.prime_factor_aux α hdeg p hp hdvd

open WeierstrassCurve.Affine in
/-- Prime-degree decomposition: every isogeny of degree $> 1$ decomposes as a chain of
prime-degree isogenies whose composition is the original isogeny. -/
theorem isogeny_prime_degree_decomposition {F : Type*} [Field F] [DecidableEq F]
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (α : Isogeny E₁ E₂) (hdeg : 1 < α.degree) :
    ∃ (chain : IsogenyChain E₁ E₂),
      chain.allPrimeDegree ∧
      chain.compose = α.toAddMonoidHom := by
  suffices ∀ (d : ℕ) {E₁ E₂ : WeierstrassCurve.Affine F} (α : Isogeny E₁ E₂),
      α.degree = d → 1 < d →
      ∃ (chain : IsogenyChain E₁ E₂),
        chain.allPrimeDegree ∧
        chain.compose = α.toAddMonoidHom by
    exact this α.degree α rfl hdeg
  intro d
  induction d using Nat.strongRecOn with
  | _ d ih =>
  intro E₁' E₂' α' hαd hd
  have ⟨p, hp, hdvd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
  rw [← hαd] at hdvd
  have hα_gt1 : 1 < α'.degree := by omega
  obtain ⟨E_mid, β, γ, hβ_deg, hγ_pos, hcomp_deg, hcomp_eq⟩ :=
    isogeny_prime_factor α' hα_gt1 p hp hdvd
  by_cases hγ1 : γ.degree ≤ 1
  · have hγ_deg_one : γ.degree = 1 := by omega
    have hα_is_p : α'.degree = p := by
      have : γ.degree * β.degree = α'.degree := hcomp_deg
      rw [hγ_deg_one, one_mul, hβ_deg] at this; exact this.symm
    exact ⟨.single α',
      by rw [IsogenyChain.allPrimeDegree, hα_is_p]; exact hp,
      by simp [IsogenyChain.compose]⟩
  · push_neg at hγ1
    have hγ_lt : γ.degree < d := by
      rw [← hαd]; have : γ.degree * β.degree = α'.degree := hcomp_deg
      rw [← this, hβ_deg]; nlinarith [hp.two_le]
    obtain ⟨chain_γ, hchain_γ, hcompose_γ⟩ := ih γ.degree hγ_lt γ rfl hγ1
    exact ⟨.cons β chain_γ,
      ⟨by rw [hβ_deg]; exact hp, hchain_γ⟩,
      by simp [IsogenyChain.compose, hcompose_γ, hcomp_eq]⟩

namespace DivisionPolynomial

open Polynomial WeierstrassCurve.Affine

/-- Public alias for the $n$-th division polynomial of a short Weierstrass curve. -/
noncomputable def psi {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R) (n : ℤ) :
    R[X][Y] :=
  E.divisionPoly n

/-- Public alias for the $n$-th $\phi$-polynomial of a short Weierstrass curve. -/
noncomputable def phi {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R) (n : ℤ) :
    R[X][Y] :=
  E.phiPoly n

/-- Public alias for the numerator of the $n$-th $\omega$-polynomial. -/
noncomputable def omegaNumer {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R) (n : ℤ) :
    R[X][Y] :=
  E.omegaPolyNumer n

section BaseCases

variable {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R)

/-- $\psi_0 = 0$. -/
@[simp] lemma psi_zero : psi E 0 = 0 := E.divisionPoly_zero
/-- $\psi_1 = 1$. -/
@[simp] lemma psi_one : psi E 1 = 1 := E.divisionPoly_one
/-- $\psi_{-n} = -\psi_n$. -/
@[simp] lemma psi_neg (n : ℤ) : psi E (-n) = -psi E n := E.divisionPoly_neg n

/-- Defining identity: $\phi_n = X \psi_n^2 - \psi_{n+1} \psi_{n-1}$. -/
lemma phi_eq (n : ℤ) : phi E n =
    C X * psi E n ^ 2 - psi E (n + 1) * psi E (n - 1) :=
  E.phiPoly_eq n

/-- $\phi_0 = 1$. -/
@[simp] lemma phi_zero : phi E 0 = 1 := E.phiPoly_zero
/-- $\phi_1 = X$. -/
@[simp] lemma phi_one : phi E 1 = C X := E.phiPoly_one
/-- $\phi_{-n} = \phi_n$. -/
@[simp] lemma phi_neg (n : ℤ) : phi E (-n) = phi E n := E.phiPoly_neg n

/-- Odd recurrence: $\psi_{2m+1} = \psi_{m+2}\psi_m^3 - \psi_{m-1}\psi_{m+1}^3$. -/
lemma psi_odd_recurrence (m : ℤ) : psi E (2 * m + 1) =
    psi E (m + 2) * psi E m ^ 3 -
    psi E (m - 1) * psi E (m + 1) ^ 3 :=
  E.divisionPoly_odd m

/-- Even recurrence: $\psi_{2m} \psi_2 = \psi_{m-1}^2 \psi_m \psi_{m+2} -
\psi_{m-2} \psi_m \psi_{m+1}^2$. -/
lemma psi_even_recurrence (m : ℤ) :
    psi E (2 * m) * E.toWeierstrassCurve.ψ₂ =
    psi E (m - 1) ^ 2 * psi E m * psi E (m + 2) -
    psi E (m - 2) * psi E m * psi E (m + 1) ^ 2 :=
  E.divisionPoly_even m

end BaseCases

section AlgebraicIdentities

variable {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R)

/-- Odd identity (Theorem 5.21): $\phi_m \psi_{m+1}^2 - \phi_{m+1}\psi_m^2 = \psi_{2m+1}$. -/
theorem psi_odd_identity (m : ℤ) :
    phi E m * psi E (m + 1) ^ 2 -
    phi E (m + 1) * psi E m ^ 2 =
    psi E (2 * m + 1) :=
  E.psi_odd_verification m

/-- Even identity (Theorem 5.21): $\psi_m \cdot \omega^{\mathrm{num}}_m = \psi_{2m} \cdot
\psi_2$. -/
theorem psi_even_identity (m : ℤ) :
    psi E m * omegaNumer E m =
    psi E (2 * m) * E.toWeierstrassCurve.ψ₂ :=
  E.psi_even_verification m

/-- Symmetry under negation: $\phi_{-n} = \phi_n$ and $\psi_{-n}^2 = \psi_n^2$. -/
theorem x_coord_neg_symmetry (n : ℤ) :
    phi E (-n) = phi E n ∧
    psi E (-n) ^ 2 = psi E n ^ 2 :=
  E.x_coord_neg_invariant n

end AlgebraicIdentities

noncomputable section PointEvaluation

variable {F : Type*} [Field F] [DecidableEq F] (E : ShortWeierstrassCurve F)

/-- Numerical evaluation of $\psi_n$ at the affine point $(x_0, y_0)$. -/
def evalPsi (n : ℤ) (x₀ y₀ : F) : F := E.evalDivisionPoly n x₀ y₀

/-- Numerical evaluation of $\phi_n$ at the affine point $(x_0, y_0)$. -/
def evalPhi (n : ℤ) (x₀ y₀ : F) : F := E.evalPhiPoly n x₀ y₀

/-- Numerical evaluation of $\omega_n$ at the affine point $(x_0, y_0)$. -/
def evalOmega (n : ℤ) (x₀ y₀ : F) : F := E.evalOmega n x₀ y₀

/-- $x$-coordinate of $[n] P$ for $P = (x_0, y_0)$, as $\phi_n(P) / \psi_n(P)^2$. -/
def mulByN_x (n : ℤ) (x₀ y₀ : F) : F := E.mulByN_x n x₀ y₀

/-- $y$-coordinate of $[n] P$ for $P = (x_0, y_0)$, as $\omega_n(P) / \psi_n(P)^3$. -/
def mulByN_y (n : ℤ) (x₀ y₀ : F) : F := E.mulByN_y n x₀ y₀

/-- Theorem 5.21 (textbook statement): the three division polynomial identities — symmetry
under negation, odd recurrence, and even recurrence — hold over any commutative ring. -/
theorem theorem_5_21 {R : Type*} [CommRing R] (E : ShortWeierstrassCurve R) :

    (∀ n : ℤ, phi E (-n) = phi E n ∧
              psi E (-n) ^ 2 = psi E n ^ 2) ∧

    (∀ m : ℤ, phi E m * psi E (m + 1) ^ 2 -
              phi E (m + 1) * psi E m ^ 2 =
              psi E (2 * m + 1)) ∧

    (∀ m : ℤ, psi E m * omegaNumer E m =
              psi E (2 * m) * E.toWeierstrassCurve.ψ₂) :=
  E.theorem_5_21_algebraic

/-- Combined point-multiplication theorem: either $\psi_n(P) \neq 0$ and $[n]P$ is given by
the division polynomial formulae, or $\psi_n(P) = 0$ and $[n] P = O$. -/
theorem nsmul_eq_divisionPoly
    [E.toWeierstrassCurve.IsElliptic]
    {x₀ y₀ : F}
    (hP : E.toWeierstrassCurve.toAffine.Nonsingular x₀ y₀)
    {n : ℤ} (hn : n ≠ 0) :
    (evalPsi E n x₀ y₀ ≠ 0 →
      ∃ h : E.toWeierstrassCurve.toAffine.Nonsingular
          (mulByN_x E n x₀ y₀) (mulByN_y E n x₀ y₀),
        n • (Point.some x₀ y₀ hP) =
        Point.some (mulByN_x E n x₀ y₀) (mulByN_y E n x₀ y₀) h) ∧
    (evalPsi E n x₀ y₀ = 0 →
      n • (Point.some x₀ y₀ hP) = Point.zero) :=
  ShortWeierstrassCurve.smul_eq_divisionPoly_cases E hP hn

end PointEvaluation

end DivisionPolynomial
