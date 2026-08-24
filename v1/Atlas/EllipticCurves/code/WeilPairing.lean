/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.SMulWithZero
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Fintype.Units
import Mathlib.Algebra.Ring.GeomSum
import Atlas.EllipticCurves.code.Divisors
import Atlas.EllipticCurves.code.TorsionEndomorphism

noncomputable section

open WeierstrassCurve.Affine

namespace WeilPairing

/-- Evaluation of a function `f : P → k` at a divisor `D = ∑ nₚ [P]`, producing the product
`∏ f(p) ^ nₚ` (Definition 23.18 in Sutherland's notes). -/
def functionEvalAtDivisor {P : Type*} [DecidableEq P] {k : Type*} [CommGroup k]
    (f : P → k) (D : P →₀ ℤ) : k :=
  D.prod (fun p n => f p ^ n)

/-- Evaluation at a divisor is multiplicative in the divisor:
`f(D₁ + D₂) = f(D₁) · f(D₂)`. -/
theorem functionEvalAtDivisor_mul
    {P : Type*} [DecidableEq P] {k : Type*} [CommGroup k]
    (f : P → k) (D₁ D₂ : P →₀ ℤ) :
    functionEvalAtDivisor f (D₁ + D₂) =
      functionEvalAtDivisor f D₁ * functionEvalAtDivisor f D₂ := by
  unfold functionEvalAtDivisor
  exact Finsupp.prod_add_index (fun a _ => zpow_zero (f a))
    (fun a _ b₁ b₂ => zpow_add (f a) b₁ b₂)

/-- Weil reciprocity (Theorem 23.20): for functions `f, g` on a smooth projective curve whose
divisors have disjoint support, we have `f(div g) = g(div f)`. -/
theorem weilReciprocity
    {P : Type*} [DecidableEq P] {k : Type*} [CommGroup k]
    (Φ : CurveDiv.FunctionFieldDiv P)
    (evalAt : Φ.F → P → k)
    (f g : Additive Φ.F)
    (hdisjoint : Disjoint (Φ.divMap f).support (Φ.divMap g).support) :
    functionEvalAtDivisor (evalAt (Additive.toMul f)) (Φ.divMap g) =
      functionEvalAtDivisor (evalAt (Additive.toMul g)) (Φ.divMap f) := by sorry

/-- The numerator `L_{P,Q}` of the line function from Definition 23.16, evaluated at a third point
`R`. Returns the value of the line through `P` and `Q` (or the tangent at `P` if `P = Q`). -/
noncomputable def lineFunction
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F)
    (P Q : W.Point) (R : W.Point) : F :=
  match P, Q, R with

  | .zero, _, _ => 1
  | _, .zero, _ => 1
  | _, _, .zero => 1

  | .some x₁ y₁ _, .some x₂ y₂ _, .some xR yR _ =>
    if x₁ = x₂ then
      if y₁ = y₂ then


        let denom := 2 * y₁ + W.a₁ * x₁ + W.a₃
        if denom = 0 then
          xR - x₁
        else
          let slope := (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) / denom
          (yR - y₁) - slope * (xR - x₁)
      else

        xR - x₁
    else

      (yR - y₁) * (x₂ - x₁) - (xR - x₁) * (y₂ - y₁)

/-- The function `G_{P,Q} := L_{P,Q} / L_{P+Q, -(P+Q)}` from Definition 23.16, packaged as a
function into `Fˣ` and forced to `1` when the denominator/value vanishes. -/
noncomputable def lineFunctionG
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) :
    W.Point → W.Point → (W.Point → Fˣ) :=
  fun P Q R =>
    let num := lineFunction W P Q R
    let den := lineFunction W (P + Q) (-(P + Q)) R


    if hd : den = 0 then 1
    else
      let val := num / den
      if hv : val = 0 then 1
      else Units.mk0 val hv

variable {F₀ : Type*} [Field F₀] [DecidableEq F₀]

/-- The divisor of the line `L_{P,Q}`, namely `[P] + [Q] + [-(P+Q)] - 3[0]`. -/
def divLine {W : WeierstrassCurve.Affine F₀} (P Q : W.Point) : W.Point →₀ ℤ :=
  Finsupp.single P 1 + Finsupp.single Q 1 + Finsupp.single (-(P + Q)) 1
    - 3 • Finsupp.single (0 : W.Point) 1

/-- The divisor of `G_{P,Q}`, namely `[P] + [Q] - [P+Q] - [0]`. -/
def divG {W : WeierstrassCurve.Affine F₀} (P Q : W.Point) : W.Point →₀ ℤ :=
  Finsupp.single P 1 + Finsupp.single Q 1 - Finsupp.single (P + Q) 1
    - Finsupp.single (0 : W.Point) 1

/-- Axiomatized "divisor of a function" map sending a function `W.Point → Fˣ` to its formal
divisor. Used as a placeholder for the algebraic-geometric `div` operator. -/
noncomputable def divFunG_ax
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) :
    (W.Point → Fˣ) → (W.Point →₀ ℤ) := by sorry

/-- The "divisor of a function" map for `lineFunctionG`-style functions, defined via
`divFunG_ax`. -/
noncomputable def divFunG
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) :
    (W.Point → Fˣ) → (W.Point →₀ ℤ) := divFunG_ax W

/-- The divisor of the function `G_{P,Q}` is `[P] + [Q] - [P+Q] - [0]`, as expected from
Definition 23.16. -/
theorem lineFunctionG_divisor
    {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve.Affine F}
    (P Q : W.Point) :
    divFunG W (lineFunctionG W P Q) = divG P Q := by sorry

/-- Two divisors `D₁, D₂` are linearly equivalent (with respect to a subgroup of principal
divisors `PrincE`) when `D₁ - D₂ ∈ PrincE`. -/
def LinearlyEquivalent {W : WeierstrassCurve.Affine F₀}
    (PrincE : AddSubgroup (W.Point →₀ ℤ))
    (D₁ D₂ : W.Point →₀ ℤ) : Prop :=
  D₁ - D₂ ∈ PrincE

section MillerFunction

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve.Affine F)

/-- The Miller function `f_{n,P}` for natural `n`, defined recursively (Definition 23.23):
`f_{0,P} = f_{1,P} = 1` and `f_{n+2,P} = f_{n+1,P} · G_{P, (n+1)P}`. -/
def millerFunctionNat (P : W.Point) : ℕ → (W.Point → Fˣ)
  | 0 => fun _ => 1
  | 1 => fun _ => 1
  | (n + 2) => fun R =>
    millerFunctionNat P (n + 1) R * lineFunctionG W P ((↑(n + 1) : ℤ) • P) R

/-- The Miller function `f_{n,P}` extended to all integers (Definition 23.23):
for `n < 0`, `f_{-n,P} := (f_{n,P} · G_{nP, -nP})⁻¹`. -/
def millerFunction (P : W.Point) (n : ℤ) : W.Point → Fˣ :=
  match n with
  | (m : ℕ) => millerFunctionNat W P m
  | Int.negSucc m =>
    fun R => (millerFunctionNat W P (m + 1) R *
              lineFunctionG W ((↑(m + 1) : ℤ) • P) (-(↑(m + 1) : ℤ) • P) R)⁻¹

/-- The Miller function at index `0` is the constant function `1`. -/
@[simp]
theorem millerFunction_zero (P : W.Point) :
    millerFunction W P 0 = fun _ => 1 :=
  rfl

/-- The Miller function at index `1` is the constant function `1`. -/
@[simp]
theorem millerFunction_one (P : W.Point) :
    millerFunction W P 1 = fun _ => 1 :=
  rfl

/-- Recursive step for the natural-index Miller function:
`f_{n+1,P}(R) = f_{n,P}(R) · G_{P, nP}(R)` for `n ≥ 1`. -/
theorem millerFunctionNat_succ (P : W.Point) (n : ℕ) (hn : 1 ≤ n) (R : W.Point) :
    millerFunctionNat W P (n + 1) R =
      millerFunctionNat W P n R * lineFunctionG W P ((↑n : ℤ) • P) R := by
  cases n with
  | zero => omega
  | succ m => simp only [millerFunctionNat]

/-- Relation between the Miller function at `-n` and at `n`, for positive natural `n`. -/
theorem millerFunction_neg (P : W.Point) (n : ℕ) (hn : 0 < n) (R : W.Point) :
    millerFunction W P (-(↑n : ℤ)) R =
      (millerFunction W P (↑n : ℤ) R *
       lineFunctionG W ((↑n : ℤ) • P) (-(↑n : ℤ) • P) R)⁻¹ := by
  cases n with
  | zero => omega
  | succ m =>
    have hkey : -(↑(m + 1) : ℤ) = Int.negSucc m := by omega
    simp only [millerFunction, hkey]

end MillerFunction

section MillerProperties

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve.Affine F)

/-- The divisor of `f_{n,P}`, namely `n[P] - (n-1)[0] - [nP]` (Lemma 23.24(i)). -/
def millerFunctionDivisor
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) :
    W.Point → ℤ → (W.Point →₀ ℤ) :=
  fun P n =>
    n • Finsupp.single P 1 - (n - 1) • Finsupp.single (0 : W.Point) 1
      - Finsupp.single ((n : ℤ) • P) 1

/-- Expands the definition of `millerFunctionDivisor` as
`n[P] - (n-1)[0] - [nP]` (Lemma 23.24(i)). -/
theorem millerFunction_divisor (P : W.Point) (n : ℤ) :
    millerFunctionDivisor W P n =
      n • Finsupp.single P 1 - (n - 1) • Finsupp.single (0 : W.Point) 1
        - Finsupp.single ((n : ℤ) • P) 1 := rfl

/-- Additivity in the index (Lemma 23.24(ii)):
`f_{m+n,P} = f_{m,P} · f_{n,P} · G_{mP, nP}`. -/
theorem millerFunction_add (P : W.Point) (m n : ℤ) (R : W.Point) :
    millerFunction W P (m + n) R =
      millerFunction W P m R * millerFunction W P n R *
        lineFunctionG W ((m : ℤ) • P) ((n : ℤ) • P) R := by sorry

/-- Multiplicativity in the index (Lemma 23.24(iii)):
`f_{mn,P} = f_{m,P}^n · f_{n, mP}`. -/
theorem millerFunction_mul (P : W.Point) (m n : ℤ) (R : W.Point) :
    millerFunction W P (m * n) R =
      millerFunction W P m R ^ n * millerFunction W ((m : ℤ) • P) n R := by sorry

/-- The symmetric form of Lemma 23.24(iii):
`f_{mn,P} = f_{n,P}^m · f_{m, nP}`. -/
theorem millerFunction_mul' (P : W.Point) (m n : ℤ) (R : W.Point) :
    millerFunction W P (m * n) R =
      millerFunction W P n R ^ m * millerFunction W ((n : ℤ) • P) m R := by sorry

end MillerProperties

section MillerDerived

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve.Affine F)

/-- The divisor `n[P] - (n-1)[0] - [nP]` has degree zero. -/
theorem millerFunction_divisor_deg_zero (P : W.Point) (n : ℤ) :
    (millerFunctionDivisor W P n).sum (fun _ k => k) = 0 := by
  rw [millerFunction_divisor]
  simp [Finsupp.sum_sub_index, Finsupp.sum_single_index]

/-- Doubling formula for the Miller function:
`f_{2n,P} = f_{n,P}² · G_{nP, nP}`. Specialization of `millerFunction_add`. -/
theorem millerFunction_double (P : W.Point) (n : ℤ) (R : W.Point) :
    millerFunction W P (n + n) R =
      millerFunction W P n R * millerFunction W P n R *
        lineFunctionG W ((n : ℤ) • P) ((n : ℤ) • P) R :=
  millerFunction_add W P n n R

/-- Adding one to the integer index of the Miller function:
`f_{n+1,P} = f_{n,P} · f_{1,P} · G_{nP, P}`. -/
theorem millerFunction_succ_int (P : W.Point) (n : ℤ) (R : W.Point) :
    millerFunction W P (n + 1) R =
      millerFunction W P n R * millerFunction W P 1 R *
        lineFunctionG W ((n : ℤ) • P) ((1 : ℤ) • P) R :=
  millerFunction_add W P n 1 R

/-- Squaring formula for the Miller function:
`f_{n²,P} = f_{n,P}^n · f_{n, nP}`. Specialization of `millerFunction_mul`. -/
theorem millerFunction_sq (P : W.Point) (n : ℤ) (R : W.Point) :
    millerFunction W P (n * n) R =
      millerFunction W P n R ^ n * millerFunction W ((n : ℤ) • P) n R :=
  millerFunction_mul W P n n R

end MillerDerived

/-- The group `μ_N(F)` of `N`-th roots of unity inside `Fˣ`. -/
def muN (N : ℕ) (F : Type*) [CommMonoid F] : Subgroup Fˣ :=
  rootsOfUnity N F

variable {F : Type*} [Field F] [DecidableEq F]

/-- The raw Weil pairing value (Lemma 23.26):
`e_n(P, Q) = f_{n,Q}(T) · f_{n,P}(Q - T) / (f_{n,P}(-T) · f_{n,Q}(P + T))`
for an auxiliary point `T`. -/
def weilPairingVal
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F)
    (N : ℕ) (P Q : W.Point) (T : W.Point) : Fˣ :=
  millerFunction W Q (N : ℤ) T *
    millerFunction W P (N : ℤ) (Q - T) *
  (millerFunction W P (N : ℤ) (-T) *
    millerFunction W Q (N : ℤ) (P + T))⁻¹

/-- The raw Weil pairing value `weilPairingVal W N P Q T` lies in `μ_N(F)` for `P, Q ∈ E[N]`
when `T` avoids the forbidden points `{0, Q, -P, Q - P}` (consequence of Lemma 23.21). -/
theorem weilPairingVal_mem_muN
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (P Q : ↥(torsionSubgroup W (N : ℤ)))
    (T : W.Point)
    (hT_ne_zero : T ≠ 0)
    (hT_ne_Q : T ≠ (Q : W.Point))
    (hT_ne_negP : T ≠ -(P : W.Point))
    (hT_ne_QsubP : T ≠ (Q : W.Point) - (P : W.Point)) :
    weilPairingVal W N (P : W.Point) (Q : W.Point) T ∈ muN N F := by sorry

/-- The Weil pairing value `weilPairingVal W N P Q T` does not depend on the choice of valid
auxiliary point `T` (Lemma 23.21). -/
theorem weilPairingVal_indep_T
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (P Q : ↥(torsionSubgroup W (N : ℤ)))
    (T₁ T₂ : W.Point)
    (hT₁_ne_zero : T₁ ≠ 0) (hT₁_ne_Q : T₁ ≠ (Q : W.Point))
    (hT₁_ne_negP : T₁ ≠ -(P : W.Point)) (hT₁_ne_QsubP : T₁ ≠ (Q : W.Point) - (P : W.Point))
    (hT₂_ne_zero : T₂ ≠ 0) (hT₂_ne_Q : T₂ ≠ (Q : W.Point))
    (hT₂_ne_negP : T₂ ≠ -(P : W.Point)) (hT₂_ne_QsubP : T₂ ≠ (Q : W.Point) - (P : W.Point)) :
    weilPairingVal W N (P : W.Point) (Q : W.Point) T₁ =
      weilPairingVal W N (P : W.Point) (Q : W.Point) T₂ := by sorry

/-- Existence of a valid auxiliary point `T` for the Weil pairing: there is some `T` avoiding
the four forbidden points `{0, Q, -P, Q - P}`. -/
theorem exists_valid_T
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (P Q : ↥(torsionSubgroup W (N : ℤ))) :
    ∃ T : W.Point, T ≠ 0 ∧ T ≠ (Q : W.Point) ∧
      T ≠ -(P : W.Point) ∧ T ≠ (Q : W.Point) - (P : W.Point) := by sorry

/-- The Weil pairing `e_N : E[N] × E[N] → μ_N(F)` as a function valued in `μ_N(F)`, obtained
by choosing a valid auxiliary `T` and packaging the resulting unit. -/
noncomputable def weilPairing
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N)) :
    ↥(torsionSubgroup W (N : ℤ)) → ↥(torsionSubgroup W (N : ℤ)) → ↥(muN N F) :=
  fun P Q =>
    ⟨weilPairingVal W N (P : W.Point) (Q : W.Point)
        (exists_valid_T W N hN hchar P Q).choose,
     weilPairingVal_mem_muN W N hN hchar P Q
        (exists_valid_T W N hN hchar P Q).choose
        (exists_valid_T W N hN hchar P Q).choose_spec.1
        (exists_valid_T W N hN hchar P Q).choose_spec.2.1
        (exists_valid_T W N hN hchar P Q).choose_spec.2.2.1
        (exists_valid_T W N hN hchar P Q).choose_spec.2.2.2⟩

/-- For an `N`-torsion point `P`, the ratio `f_{n,P}(Q - T) / f_{n,P}(-T)` equals the evaluation
of `R ↦ f_{n,P}(R - T)` at the divisor `[Q] - [0]`. -/
theorem millerFunction_compose_translate
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F)
    (P : W.Point) (n : ℤ) (hn : n • P = 0)
    (T Q : W.Point) :
    millerFunction W P n (Q - T) *
      (millerFunction W P n (-T))⁻¹ =
    functionEvalAtDivisor (fun R => millerFunction W P n (R - T))
      (Finsupp.single Q 1 - Finsupp.single (0 : W.Point) 1) := by sorry

/-- The value of `weilPairing W N hN hchar P Q` as a unit `Fˣ` equals the explicit
Miller-function formula for any valid auxiliary point `T` (Lemma 23.26). -/
theorem weilPairing_millerFunction
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (P Q : ↥(torsionSubgroup W (N : ℤ)))
    (T : W.Point)
    (hT_ne_zero : T ≠ 0)
    (hT_ne_Q : T ≠ (Q : W.Point))
    (hT_ne_negP : T ≠ -(P : W.Point))
    (hT_ne_QsubP : T ≠ (Q : W.Point) - (P : W.Point)) :
    (↑(weilPairing W N hN hchar P Q) : Fˣ) =
      millerFunction W (Q : W.Point) (N : ℤ) T *
        millerFunction W (P : W.Point) (N : ℤ) ((Q : W.Point) - T) *
      (millerFunction W (P : W.Point) (N : ℤ) (-T) *
        millerFunction W (Q : W.Point) (N : ℤ) ((P : W.Point) + T))⁻¹ := by

  change (↑(weilPairing W N hN hchar P Q) : Fˣ) = weilPairingVal W N (P : W.Point) (Q : W.Point) T


  have h_def : (↑(weilPairing W N hN hchar P Q) : Fˣ) =
    weilPairingVal W N ↑P ↑Q (exists_valid_T W N hN hchar P Q).choose := by
    unfold weilPairing weilPairingVal
    rfl
  rw [h_def]
  exact weilPairingVal_indep_T W N hN hchar P Q
    (exists_valid_T W N hN hchar P Q).choose T
    (exists_valid_T W N hN hchar P Q).choose_spec.1
    (exists_valid_T W N hN hchar P Q).choose_spec.2.1
    (exists_valid_T W N hN hchar P Q).choose_spec.2.2.1
    (exists_valid_T W N hN hchar P Q).choose_spec.2.2.2
    hT_ne_zero hT_ne_Q hT_ne_negP hT_ne_QsubP

/-- Existence of an auxiliary point `T` realizing the simplification of the Weil pairing to
the Corollary 23.27 form `(-1)^N · f_{N,P}(Q) / f_{N,Q}(P)` for distinct `N`-torsion points
`P ≠ Q`. -/
theorem millerFunction_simplification_identity
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 1 < N) (hchar : ¬ (ringChar F ∣ N))
    (P Q : ↥(torsionSubgroup W (N : ℤ)))
    (hPQ : (P : W.Point) ≠ (Q : W.Point)) :
    ∃ (T : W.Point),
      T ≠ 0 ∧
      T ≠ (Q : W.Point) ∧
      T ≠ -(P : W.Point) ∧
      T ≠ (Q : W.Point) - (P : W.Point) ∧
      millerFunction W (Q : W.Point) (N : ℤ) T *
        millerFunction W (P : W.Point) (N : ℤ) ((Q : W.Point) - T) *
      (millerFunction W (P : W.Point) (N : ℤ) (-T) *
        millerFunction W (Q : W.Point) (N : ℤ) ((P : W.Point) + T))⁻¹ =
      ((-1 : Fˣ) ^ N) *
      (millerFunction W (P : W.Point) (N : ℤ) (Q : W.Point) *
        (millerFunction W (Q : W.Point) (N : ℤ) (P : W.Point))⁻¹) := by sorry

/-- Corollary 23.27: for distinct `N`-torsion points `P ≠ Q`,
`e_N(P, Q) = (-1)^N · f_{N,P}(Q) / f_{N,Q}(P)`. -/
theorem weilPairing_millerFunction_simplified
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 1 < N) (hchar : ¬ (ringChar F ∣ N))
    (P Q : ↥(torsionSubgroup W (N : ℤ)))
    (hPQ : (P : W.Point) ≠ (Q : W.Point)) :
    (↑(weilPairing W N (by omega) hchar P Q) : Fˣ) =
      ((-1 : Fˣ) ^ N) *
      (millerFunction W (P : W.Point) (N : ℤ) (Q : W.Point) *
        (millerFunction W (Q : W.Point) (N : ℤ) (P : W.Point))⁻¹) := by
  obtain ⟨T, hT0, hTQ, hTnP, hTQP, hTeq⟩ :=
    millerFunction_simplification_identity W N hN hchar P Q hPQ
  rw [weilPairing_millerFunction W N (by omega) hchar P Q T hT0 hTQ hTnP hTQP]
  exact hTeq

section Definition_23_19

variable {P : Type*} [DecidableEq P] {k : Type*} [CommGroup k]

/-- Divisor-level Weil pairing (Definition 23.19): given functions `f₁, f₂` representing the
`n`-torsion of the divisors `D₁, D₂` (i.e., `div fᵢ = n · Dᵢ`), define
`e_n(D₁, D₂) := f₁(D₂) / f₂(D₁)`. -/
def weilPairingDiv (f₁ f₂ : P → k) (D₁ D₂ : P →₀ ℤ) : k :=
  functionEvalAtDivisor f₁ D₂ * (functionEvalAtDivisor f₂ D₁)⁻¹

end Definition_23_19

section Lemma_23_21

variable {P : Type*} [DecidableEq P] {k : Type*} [CommGroup k]

/-- Invariance of the divisor-level Weil pairing under adding a principal divisor on the left:
modifying `f₁` by a function `g` and adjusting `D₁` by `div g` does not change the value
(Lemma 23.21). -/
theorem weilPairingDiv_add_div_left
    (Φ : CurveDiv.FunctionFieldDiv P) (evalAt : Φ.F → P → k)
    (n : ℤ) (f₁ f₂ : P → k) (D₁ D₂ : P →₀ ℤ) (g : Additive Φ.F)
    (hD₁_D₂_disjoint : Disjoint D₁.support D₂.support)
    (hg_D₁_disjoint : Disjoint (Φ.divMap g).support D₁.support)
    (hg_D₂_disjoint : Disjoint (Φ.divMap g).support D₂.support) :
    weilPairingDiv (fun p => f₁ p * (evalAt (Additive.toMul g) p) ^ n)
      f₂ (D₁ + Φ.divMap g) D₂ =
    weilPairingDiv f₁ f₂ D₁ D₂ := by sorry

/-- Invariance of the divisor-level Weil pairing under adding a principal divisor on the right
(Lemma 23.21). -/
theorem weilPairingDiv_add_div_right
    (Φ : CurveDiv.FunctionFieldDiv P) (evalAt : Φ.F → P → k)
    (n : ℤ) (f₁ f₂ : P → k) (D₁ D₂ : P →₀ ℤ) (g : Additive Φ.F)
    (hD₁_D₂_disjoint : Disjoint D₁.support D₂.support)
    (hg_D₁_disjoint : Disjoint (Φ.divMap g).support D₁.support)
    (hg_D₂_disjoint : Disjoint (Φ.divMap g).support D₂.support) :
    weilPairingDiv f₁
      (fun p => f₂ p * (evalAt (Additive.toMul g) p) ^ n)
      D₁ (D₂ + Φ.divMap g) =
    weilPairingDiv f₁ f₂ D₁ D₂ := by sorry

/-- Scaling a divisor by an integer `n` exponentiates the evaluation:
`f(n • D) = f(D)^n`. -/
theorem functionEvalAtDivisor_zsmul
    (f : P → k) (n : ℤ) (D : P →₀ ℤ) :
    functionEvalAtDivisor f (n • D) = functionEvalAtDivisor f D ^ n := by

  change (n • D).support.prod (fun a => f a ^ ((n • D) a)) =
    (D.support.prod (fun a => f a ^ (D a))) ^ n
  rw [Finset.prod_subset (s₁ := (n • D).support) Finsupp.support_smul
    (fun x _ hx => by
      rw [Finsupp.notMem_support_iff.mp hx, zpow_zero]),
    ← Finset.prod_zpow]
  exact Finset.prod_congr rfl (fun p _ => by
    rw [Finsupp.smul_apply, smul_eq_mul, zpow_mul'])

/-- The divisor-level Weil pairing raised to the power `n` is trivial when `div fᵢ = n · Dᵢ`,
i.e., it lies in `μ_n` (key step in Lemma 23.21). -/
theorem weilPairingDiv_pow_eq_one
    (Φ : CurveDiv.FunctionFieldDiv P) (evalAt : Φ.F → P → k)
    (n : ℤ) (f₁ f₂ : Additive Φ.F) (D₁ D₂ : P →₀ ℤ)
    (hf₁ : Φ.divMap f₁ = n • D₁) (hf₂ : Φ.divMap f₂ = n • D₂)
    (hdisjoint : Disjoint D₁.support D₂.support)
    (hf₁_D₂ : Disjoint (Φ.divMap f₁).support D₂.support)
    (hf₂_D₁ : Disjoint (Φ.divMap f₂).support D₁.support) :
    weilPairingDiv (evalAt (Additive.toMul f₁)) (evalAt (Additive.toMul f₂))
      D₁ D₂ ^ n = 1 := by

  unfold weilPairingDiv
  rw [mul_zpow, inv_zpow]

  rw [← functionEvalAtDivisor_zsmul, ← functionEvalAtDivisor_zsmul]

  rw [← hf₂, ← hf₁]

  have hdisjoint_divs : Disjoint (Φ.divMap f₁).support (Φ.divMap f₂).support := by
    rw [hf₁, hf₂]
    exact Disjoint.mono Finsupp.support_smul Finsupp.support_smul hdisjoint
  rw [weilReciprocity Φ evalAt f₁ f₂ hdisjoint_divs]

  exact mul_inv_cancel _

/-- The divisor-level Weil pairing is alternating: `e_n(D₁, D₂) · e_n(D₂, D₁) = 1`. -/
theorem weilPairingDiv_alternating
    (f₁ f₂ : P → k) (D₁ D₂ : P →₀ ℤ) :
    weilPairingDiv f₁ f₂ D₁ D₂ * weilPairingDiv f₂ f₁ D₂ D₁ = 1 := by
  unfold weilPairingDiv
  group

/-- Inverse form of the alternating property:
`e_n(D₁, D₂) = e_n(D₂, D₁)⁻¹`. -/
theorem weilPairingDiv_alternating_inv
    (f₁ f₂ : P → k) (D₁ D₂ : P →₀ ℤ) :
    weilPairingDiv f₁ f₂ D₁ D₂ = (weilPairingDiv f₂ f₁ D₂ D₁)⁻¹ :=
  mul_eq_one_iff_eq_inv.mp (weilPairingDiv_alternating f₁ f₂ D₁ D₂)

end Lemma_23_21

/-- Bilinearity of the Weil pairing in the first argument (Theorem 23.29):
`e_N(P + Q, R) = e_N(P, R) · e_N(Q, R)`. -/
theorem weilPairing_bilinear_left
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (P Q R : ↥(torsionSubgroup W (N : ℤ))) :
    weilPairing W N hN hchar (P + Q) R =
      weilPairing W N hN hchar P R * weilPairing W N hN hchar Q R := by sorry

/-- The Weil pairing is alternating (Theorem 23.29):
`e_N(P, Q) · e_N(Q, P) = 1`. -/
theorem weilPairing_alternating
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (P Q : ↥(torsionSubgroup W (N : ℤ))) :
    weilPairing W N hN hchar P Q * weilPairing W N hN hchar Q P = 1 := by sorry

/-- Inverse form of the alternating property:
`e_N(P, Q) = e_N(Q, P)⁻¹`. -/
theorem weilPairing_alternating_inv
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (P Q : ↥(torsionSubgroup W (N : ℤ))) :
    weilPairing W N hN hchar P Q = (weilPairing W N hN hchar Q P)⁻¹ :=
  mul_eq_one_iff_eq_inv.mp (weilPairing_alternating W N hN hchar P Q)

/-- Bilinearity of the Weil pairing in the second argument (Theorem 23.29):
`e_N(P, Q + R) = e_N(P, Q) · e_N(P, R)`. Derived from `weilPairing_bilinear_left` via
the alternating property. -/
theorem weilPairing_bilinear_right
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (P Q R : ↥(torsionSubgroup W (N : ℤ))) :
    weilPairing W N hN hchar P (Q + R) =
      weilPairing W N hN hchar P Q * weilPairing W N hN hchar P R := by
  have h1 : weilPairing W N hN hchar P (Q + R) =
      (weilPairing W N hN hchar (Q + R) P)⁻¹ :=
    weilPairing_alternating_inv W N hN hchar P (Q + R)
  have h2 : weilPairing W N hN hchar (Q + R) P =
      weilPairing W N hN hchar Q P * weilPairing W N hN hchar R P :=
    weilPairing_bilinear_left W N hN hchar Q R P
  have h3 : (weilPairing W N hN hchar Q P)⁻¹ =
      weilPairing W N hN hchar P Q :=
    (weilPairing_alternating_inv W N hN hchar P Q).symm
  have h4 : (weilPairing W N hN hchar R P)⁻¹ =
      weilPairing W N hN hchar P R :=
    (weilPairing_alternating_inv W N hN hchar P R).symm
  rw [h1, h2, mul_inv_rev, ← h3, ← h4]
  exact mul_comm _ _

/-- The Weil pairing is trivial on the diagonal (Theorem 23.29):
`e_N(P, P) = 1`. -/
theorem weilPairing_self
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (P : ↥(torsionSubgroup W (N : ℤ))) :
    weilPairing W N hN hchar P P = 1 := by sorry

/-- Non-degeneracy of the Weil pairing (Theorem 23.29):
if `P ≠ 0` then there exists `Q ∈ E[N]` with `e_N(P, Q) ≠ 1`. -/
theorem weilPairing_nondegenerate
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (P : ↥(torsionSubgroup W (N : ℤ))) (hP : P ≠ 0) :
    ∃ Q : ↥(torsionSubgroup W (N : ℤ)), weilPairing W N hN hchar P Q ≠ 1 := by sorry

/-- Compatibility of the Weil pairing across different `N` (Theorem 23.29):
`e_{MN}(P, Q) = e_N(M·P, Q)` for `P ∈ E[MN]` and `Q ∈ E[N]`. -/
theorem weilPairing_compatibility
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (M N : ℕ) (hMN : 0 < M * N) (hN : 0 < N)
    (hcharMN : ¬ (ringChar F ∣ M * N)) (hcharN : ¬ (ringChar F ∣ N))
    (P : ↥(torsionSubgroup W (↑(M * N) : ℤ)))
    (Q : ↥(torsionSubgroup W (↑N : ℤ)))
    (hQ_MN : (Q : W.Point) ∈ torsionSubgroup W (↑(M * N) : ℤ))
    (hMP : (M : ℤ) • (P : W.Point) ∈ torsionSubgroup W (↑N : ℤ)) :
    (↑(weilPairing W (M * N) hMN hcharMN P ⟨(Q : W.Point), hQ_MN⟩) : Fˣ) =
      (↑(weilPairing W N hN hcharN ⟨(M : ℤ) • (P : W.Point), hMP⟩ Q) : Fˣ) := by sorry

/-- A Galois automorphism `σ : F ≃+* F` induces an additive automorphism of the `N`-torsion
subgroup `E[N]`. -/
noncomputable def galoisActionOnTorsion
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (σ : F ≃+* F) :
    ↥(torsionSubgroup W (N : ℤ)) →+ ↥(torsionSubgroup W (N : ℤ)) := by sorry

/-- A Galois automorphism `σ : F ≃+* F` induces a multiplicative automorphism of
`μ_N(F) ⊆ Fˣ`. -/
noncomputable def galoisActionOnMuN
    {F : Type*} [Field F] [DecidableEq F]
    (N : ℕ) (_hN : 0 < N) (_hchar : ¬ (ringChar F ∣ N))
    (σ : F ≃+* F) :
    ↥(muN N F) →* ↥(muN N F) where
  toFun := fun ⟨x, hx⟩ =>
    ⟨Units.map σ.toRingHom.toMonoidHom x, by
      simp only [muN, rootsOfUnity, Subgroup.mem_mk, Submonoid.mem_mk] at hx ⊢
      show (Units.map σ.toRingHom.toMonoidHom x) ^ N = 1
      rw [← map_pow, hx, map_one]⟩
  map_one' := by ext; simp [map_one]
  map_mul' := by intro a b; ext; simp [map_mul]

/-- Galois-equivariance of the Weil pairing (Theorem 23.29):
`e_N(σ·P, σ·Q) = σ·e_N(P, Q)` for every `σ ∈ Gal(F̄/F)`. -/
theorem weilPairing_galois_equivariant
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (σ : F ≃+* F)
    (P Q : ↥(torsionSubgroup W (N : ℤ))) :
    weilPairing W N hN hchar
      (galoisActionOnTorsion W N hN hchar σ P)
      (galoisActionOnTorsion W N hN hchar σ Q) =
    galoisActionOnMuN N hN hchar σ (weilPairing W N hN hchar P Q) := by sorry

/-- Behavior of the Weil pairing under endomorphisms (Theorem 23.29):
`e_N(α(P), α(Q)) = e_N(P, Q)^{deg α}` for every isogeny/endomorphism `α`. -/
theorem weilPairing_endomorphism
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (α : Isogeny W W)
    (P Q : ↥(torsionSubgroup W (N : ℤ)))
    (hαP : α (P : W.Point) ∈ torsionSubgroup W (N : ℤ))
    (hαQ : α (Q : W.Point) ∈ torsionSubgroup W (N : ℤ)) :
    weilPairing W N hN hchar ⟨α (P : W.Point), hαP⟩ ⟨α (Q : W.Point), hαQ⟩ =
      weilPairing W N hN hchar P Q ^ (α.degree : ℤ) := by sorry

/-- Surjectivity of the Weil pairing onto `μ_r ⊆ μ_N` for `r = |P|` (Theorem 23.29):
every root of unity `ζ` whose order divides `|P|` is hit by some `Q ∈ E[N]`. -/
theorem weilPairing_surjective
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (P : ↥(torsionSubgroup W (N : ℤ)))
    (ζ : ↥(muN N F))
    (hζ : orderOf (ζ : Fˣ) ∣ addOrderOf (P : W.Point)) :
    ∃ Q : ↥(torsionSubgroup W (N : ℤ)),
      (↑(weilPairing W N hN hchar P Q) : Fˣ) = (↑ζ : Fˣ) := by sorry

/-- The order of `e_N(P, Q)` divides the additive order of `P`. -/
theorem weilPairing_order_dvd
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (P Q : ↥(torsionSubgroup W (N : ℤ))) :
    orderOf (↑(weilPairing W N hN hchar P Q) : Fˣ) ∣ addOrderOf (P : W.Point) := by sorry

/-- The Weil pairing vanishes when the first argument is `0`:
`e_N(0, Q) = 1`. Consequence of bilinearity. -/
theorem weilPairing_zero_left
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (Q : ↥(torsionSubgroup W (N : ℤ))) :
    weilPairing W N hN hchar 0 Q = 1 := by
  have h := weilPairing_bilinear_left W N hN hchar 0 0 Q
  simp only [add_zero] at h

  have : weilPairing W N hN hchar 0 Q * 1 = weilPairing W N hN hchar 0 Q * weilPairing W N hN hchar 0 Q := by
    rw [mul_one]
    exact h
  exact (mul_left_cancel this).symm

/-- The Weil pairing vanishes when the second argument is `0`:
`e_N(P, 0) = 1`. -/
theorem weilPairing_zero_right
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (P : ↥(torsionSubgroup W (N : ℤ))) :
    weilPairing W N hN hchar P 0 = 1 := by
  rw [weilPairing_alternating_inv W N hN hchar P 0,
      weilPairing_zero_left W N hN hchar P, inv_one]

section EmbeddingDegree

variable {K : Type*} [Field K]

/-- The predicate "the `n`-torsion `E[n]` is contained in `E(L)`" for a field extension `L/K`
(used to define the embedding degree, Definition 23.32). -/
noncomputable def NTorsionContainedIn
    (W : WeierstrassCurve.Affine K) (n : ℕ)
    (L : Type*) [Field L] [Algebra K L] : Prop := by sorry

/-- `k` is the embedding degree of `W` with respect to `n` (Definition 23.32):
there exists a field extension `L/K` of degree `k` containing `E[n]`, and `k` is the minimal
such degree. -/
def IsEmbeddingDegree (W : WeierstrassCurve.Affine K) (n : ℕ) (k : ℕ) : Prop :=
  (∃ (L : Type*) (_ : Field L) (_ : Algebra K L),
    NTorsionContainedIn W n L ∧ Module.finrank K L = k) ∧
  (∀ (L : Type*) [Field L] [Algebra K L],
    NTorsionContainedIn W n L → k ≤ Module.finrank K L)

end EmbeddingDegree

section PairingFriendly

variable {K : Type*} [Field K]

/-- `W` is pairing-friendly for parameters `(n, k, bound)` if `k` is its embedding degree
with respect to `n` and `k ≤ bound` (small embedding degree makes the Tate pairing efficiently
computable in cryptographic applications). -/
def IsPairingFriendly (W : WeierstrassCurve.Affine K) (n : ℕ) (k : ℕ) (bound : ℕ) : Prop :=
  IsEmbeddingDegree.{_, 0, 0} W n k ∧ k ≤ bound

end PairingFriendly

section TatePairing

/-- For any element `u` of a finite commutative group `G` and any divisor `n` of `|G|`,
the power `(u ^ (|G| / n))^n = 1`. -/
lemma pow_div_mem_rootsOfUnity
    {G : Type*} [CommGroup G] [Fintype G] (u : G) (n : ℕ) (hn : n ∣ Fintype.card G) :
    (u ^ (Fintype.card G / n)) ^ n = 1 := by
  rw [← pow_mul, Nat.div_mul_cancel hn, pow_card_eq_one]

/-- The (modified) Tate pairing `t_n : E[n] × E[n] → μ_n` (Definition 23.34), defined on a
finite field `F` with embedding degree `k`: `t_n(P, Q) := (f_{n,P}(Q) / f_{n,P}(0))^{(|F|^k - 1)/n}`.
-/
def tatePairing
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (n : ℕ) (hn : 2 < n) (hchar : ¬ (ringChar F ∣ n))
    (k : ℕ) (hk : IsEmbeddingDegree W n k)
    (hdvd : n ∣ Fintype.card F ^ k - 1) :
    ↥(torsionSubgroup W (n : ℤ)) → ↥(torsionSubgroup W (n : ℤ)) → ↥(muN n F) :=
  fun P Q =>

    let ratio : Fˣ := millerFunction W (P : W.Point) (n : ℤ) (Q : W.Point) /
                       millerFunction W (P : W.Point) (n : ℤ) 0

    let e : ℕ := (Fintype.card F ^ k - 1) / n

    ⟨ratio ^ e, by
      show ratio ^ e ∈ rootsOfUnity n F
      rw [mem_rootsOfUnity, ← pow_mul, Nat.div_mul_cancel hdvd]
      have h_one : ratio ^ (Fintype.card F - 1) = 1 := by
        rw [← Fintype.card_units]; exact pow_card_eq_one
      obtain ⟨c, hc⟩ := Nat.sub_one_dvd_pow_sub_one (Fintype.card F) k
      rw [hc, pow_mul, h_one, one_pow]⟩

end TatePairing

section Lemma2333

open WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- The Frobenius endomorphism `π_E : E(F̄) → E(F̄)` on a finite-field elliptic curve, packaged
as an additive group homomorphism on `W.Point`. -/
noncomputable def frobeniusIsogeny_toAddMonoidHom
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] :
    W.Point →+ W.Point := by sorry

/-- The Frobenius endomorphism is surjective on the group of points. -/
theorem frobeniusIsogeny_surjective
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] :
    Function.Surjective (frobeniusIsogeny_toAddMonoidHom W) := by sorry

/-- The Frobenius endomorphism as an `Isogeny W W` of degree `|F|`. -/
noncomputable def frobeniusIsogeny
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] :
    Isogeny W W where
  toAddMonoidHom := frobeniusIsogeny_toAddMonoidHom W
  surjective := frobeniusIsogeny_surjective W
  degree := Fintype.card F
  degree_pos := Fintype.card_pos (α := F)

/-- The degree of the Frobenius isogeny equals `|F|`. -/
theorem frobeniusIsogeny_degree
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] :
    (frobeniusIsogeny W).degree = Fintype.card F := rfl

/-- The trace of Frobenius `a_q := q + 1 - #E(F_q)` for an elliptic curve over a finite field. -/
noncomputable def frobeniusTrace
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] : ℤ := by sorry

/-- Counting formula: `#E(F_q) = q + 1 - tr(π_E)`. -/
theorem cardPoints_eq_card_sub_trace
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    [Fintype W.Point] :
    (Fintype.card W.Point : ℤ) =
      (Fintype.card F : ℤ) + 1 - frobeniusTrace W := by sorry

/-- The characteristic polynomial of Frobenius `(π - 1)(π - q) = 0` factors on the
`n`-torsion when `n` is prime and divides `#E(F_q)` (key input to Lemma 23.33). -/
theorem frobenius_charPoly_factors_on_torsion
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    [Fintype W.Point]
    (n : ℕ) (hn_prime : Nat.Prime n)
    (hn_cop : Nat.Coprime n (Fintype.card F))
    (hn_dvd : (n : ℤ) ∣ (Fintype.card W.Point : ℤ))
    (P : W.Point) (hP : P ∈ torsionSubgroup W (n : ℤ)) :
    let π := frobeniusIsogeny W
    let q := (Fintype.card F : ℤ)

    (π.toAddMonoidHom - AddMonoidHom.id W.Point)
      ((π.toAddMonoidHom - q • (AddMonoidHom.id W.Point)) P) = 0 := by sorry

/-- If `q ≡ 1 (mod n)` then Frobenius acts trivially on every `n`-torsion point — equivalently,
`E[n] ⊆ E(F_q)` (case of Lemma 23.33). -/
theorem torsion_contained_if_q_cong_one
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    [Fintype W.Point]
    (n : ℕ) (hn_prime : Nat.Prime n)
    (hn_cop : Nat.Coprime n (Fintype.card F))
    (hn_dvd : (n : ℤ) ∣ (Fintype.card W.Point : ℤ))
    (hq_cong : (Fintype.card F : ℤ) ≡ 1 [ZMOD (n : ℤ)])
    (P : W.Point) (hP : P ∈ torsionSubgroup W (n : ℤ)) :
    (frobeniusIsogeny W).toAddMonoidHom P = P := by sorry

/-- Eigenspace decomposition of `E[n]` under Frobenius when `q ≢ 1 (mod n)`:
every `n`-torsion point `P` writes as `P = P₁ + P_q` with `π(P₁) = P₁` and `π(P_q) = q · P_q`
(Lemma 23.33: `E[n] ≅ ker(π_n - 1) ⊕ ker(π_n - q)`). -/
theorem torsion_eigenspace_decomposition
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    [Fintype W.Point]
    (n : ℕ) (hn_prime : Nat.Prime n)
    (hn_cop : Nat.Coprime n (Fintype.card F))
    (hn_dvd : (n : ℤ) ∣ (Fintype.card W.Point : ℤ))
    (hq_not_cong : ¬ ((Fintype.card F : ℤ) ≡ 1 [ZMOD (n : ℤ)]))
    (P : W.Point) (hP : P ∈ torsionSubgroup W (n : ℤ)) :
    ∃ (P₁ Pq : W.Point),
      P₁ ∈ torsionSubgroup W (n : ℤ) ∧
      Pq ∈ torsionSubgroup W (n : ℤ) ∧
      P = P₁ + Pq ∧
      (frobeniusIsogeny W).toAddMonoidHom P₁ = P₁ ∧
      (frobeniusIsogeny W).toAddMonoidHom Pq =
        (Fintype.card F : ℤ) • Pq := by sorry

/-- If `E[n] ⊆ E(L)` for a finite extension `L/F`, then `[L : F] > 0` and `n ∣ |F|^[L:F] - 1`
(forward direction of Lemma 23.33). -/
theorem nTorsionContainedIn_implies_dvd
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    [Fintype W.Point]
    (n : ℕ) (hn_prime : Nat.Prime n)
    (hn_cop : Nat.Coprime n (Fintype.card F))
    (hn_dvd : (n : ℤ) ∣ (Fintype.card W.Point : ℤ))
    (L : Type*) [Field L] [Algebra F L]
    (hL : NTorsionContainedIn W n L) :
    0 < Module.finrank F L ∧ n ∣ (Fintype.card F) ^ (Module.finrank F L) - 1 := by sorry

/-- Converse: if `n ∣ |F|^k - 1` then there exists a degree-`k` extension `L/F` containing
`E[n]` (reverse direction of Lemma 23.33). -/
theorem dvd_implies_nTorsionContainedIn
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    [Fintype W.Point]
    (n : ℕ) (hn_prime : Nat.Prime n)
    (hn_cop : Nat.Coprime n (Fintype.card F))
    (hn_dvd : (n : ℤ) ∣ (Fintype.card W.Point : ℤ))
    (k : ℕ) (hk_pos : 0 < k)
    (hk_dvd : n ∣ (Fintype.card F) ^ k - 1) :
    ∃ (L : Type*) (_ : Field L) (_ : Algebra F L),
      NTorsionContainedIn W n L ∧ Module.finrank F L = k := by sorry

/-- Lemma 23.33: the embedding degree of `E/F_q` with respect to a prime `n` dividing `#E(F_q)`
(coprime to `q`) equals the multiplicative order of `q` modulo `n`. -/
theorem embeddingDegree_is_multiplicativeOrder_of_q_mod_n
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    [Fintype W.Point]
    (n : ℕ) (hn_prime : Nat.Prime n)
    (hn_cop : Nat.Coprime n (Fintype.card F))
    (hn_dvd : (n : ℤ) ∣ (Fintype.card W.Point : ℤ))
    (k : ℕ) (hk_pos : 0 < k)
    (hk_dvd : n ∣ (Fintype.card F) ^ k - 1)
    (hk_least : ∀ j : ℕ, 0 < j → j < k → ¬ (n ∣ (Fintype.card F) ^ j - 1)) :
    IsEmbeddingDegree W n k := by
  constructor
  ·
    exact dvd_implies_nTorsionContainedIn W n hn_prime hn_cop hn_dvd k hk_pos hk_dvd
  ·
    intro L _ _ hL
    have ⟨h_pos, h_dvd⟩ := nTorsionContainedIn_implies_dvd W n hn_prime hn_cop hn_dvd L hL
    by_contra h_lt
    push Not at h_lt
    exact absurd h_dvd (hk_least (Module.finrank F L) h_pos h_lt)

end Lemma2333

section Corollary_23_25

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve.Affine F)

/-- The Miller "double-and-add" algorithm: efficient evaluation of `f_{n,P}(Q)` using
`O(log n)` field operations (Corollary 23.25). At each step we either square the accumulator
(via the line `G_{mP, mP}`) or square and multiply by `G_{2mP, P}`. -/
def millerDoubleAndAdd (P : W.Point) (Q : W.Point) : ℕ → Fˣ
  | 0 => 1
  | 1 => 1
  | n + 2 =>
    let m := (n + 2) / 2
    let acc := millerDoubleAndAdd P Q m

    let doubled := acc * acc * lineFunctionG W ((m : ℤ) • P) ((m : ℤ) • P) Q
    if (n + 2) % 2 = 0 then
      doubled
    else

      doubled * lineFunctionG W ((2 * m : ℤ) • P) ((1 : ℤ) • P) Q
  termination_by n => n

/-- Correctness of the Miller double-and-add algorithm:
`millerDoubleAndAdd W P Q n = f_{n,P}(Q)`. -/
theorem millerDoubleAndAdd_eq_millerFunction (P Q : W.Point) (n : ℕ) :
    millerDoubleAndAdd W P Q n = millerFunction W P (n : ℤ) Q := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 =>
      simp [millerDoubleAndAdd, millerFunction_zero]
    | 1 =>
      simp [millerDoubleAndAdd, millerFunction_one]
    | n + 2 =>
      simp only [millerDoubleAndAdd]
      have hm_lt : (n + 2) / 2 < n + 2 := Nat.div_lt_self (by omega) (by omega)
      have h_ih := ih ((n + 2) / 2) hm_lt
      set m := (n + 2) / 2
      have h_doubled : millerDoubleAndAdd W P Q m * millerDoubleAndAdd W P Q m *
          lineFunctionG W ((↑m : ℤ) • P) ((↑m : ℤ) • P) Q =
          millerFunction W P ((↑m : ℤ) + (↑m : ℤ)) Q := by
        rw [h_ih]
        exact (millerFunction_double W P (↑m : ℤ) Q).symm
      split_ifs with h
      ·
        rw [h_doubled]
        congr 1
        push_cast
        omega
      ·
        have h_doubled' : millerDoubleAndAdd W P Q m * millerDoubleAndAdd W P Q m *
            lineFunctionG W ((↑m : ℤ) • P) ((↑m : ℤ) • P) Q =
            millerFunction W P ((2 : ℤ) * (↑m : ℤ)) Q := by
          rw [h_doubled]; congr 1; ring
        have h_succ := millerFunction_succ_int W P ((2 : ℤ) * (↑m : ℤ)) Q
        have h_one : millerFunction W P 1 Q = 1 := by
          have := millerFunction_one W P; simp [this]
        rw [h_one, mul_one] at h_succ
        have h_cast : (↑(n + 2) : ℤ) = 2 * (↑m : ℤ) + 1 := by push_cast; omega
        rw [h_doubled', h_cast, h_succ]

/-- Operation cost of the Miller double-and-add algorithm: roughly `log₂ n` doublings plus a few
extra operations per "add" step. -/
def millerEvalCost : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 =>
    let m := (n + 2) / 2
    let sub_cost := millerEvalCost m
    if (n + 2) % 2 = 0 then
      sub_cost + 1
    else
      sub_cost + 2
  termination_by n => n

/-- Logarithmic bound on the Miller evaluation cost:
`millerEvalCost n ≤ 2 log₂ n + 2`, giving the `O(log n)` complexity of Corollary 23.25. -/
theorem millerEvalCost_le_log (n : ℕ) :
    millerEvalCost n ≤ 2 * Nat.log 2 n + 2 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp [millerEvalCost]
    | 1 => simp [millerEvalCost]
    | n + 2 =>
      simp only [millerEvalCost]
      have hm : (n + 2) / 2 < n + 2 := Nat.div_lt_self (by omega) (by omega)
      have h_ih := ih ((n + 2) / 2) hm
      have h_log : Nat.log 2 (n + 2) = Nat.log 2 ((n + 2) / 2) + 1 :=
        Nat.log_of_one_lt_of_le (by omega) (by omega)
      split_ifs with h
      ·
        omega
      ·
        omega

end Corollary_23_25

section Corollary_23_30

/-- Galois-equivariance refinement (Corollary 23.30): if `E[n] ⊆ E(L)` then every `n`-th root
of unity in `L` actually lies in (the image of) `K`. -/
theorem muN_contained_if_torsion_contained
    {K : Type*} [Field K]
    (W : WeierstrassCurve.Affine K)
    (n : ℕ) (hn : 0 < n) (hchar : ¬ (ringChar K ∣ n))
    (L : Type*) [Field L] [Algebra K L]
    (hL : NTorsionContainedIn W n L) :
    ∀ (ζ : Lˣ), ζ ∈ rootsOfUnity n L → ζ.val ∈ (algebraMap K L).range := by sorry

/-- Corollary 23.30 over finite fields: if `E[n] ⊆ E(F_q)` then `n ∣ q - 1`. -/
theorem corollary_23_30_finite_field
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    [Fintype W.Point]
    (n : ℕ) (hn_prime : Nat.Prime n)
    (hn_cop : Nat.Coprime n (Fintype.card F))
    (hn_dvd : (n : ℤ) ∣ (Fintype.card W.Point : ℤ))
    (hcontained : NTorsionContainedIn W n F) :
    n ∣ Fintype.card F - 1 := by
  have ⟨_, h_dvd⟩ := nTorsionContainedIn_implies_dvd W n hn_prime hn_cop hn_dvd F hcontained
  simp only [Module.finrank_self, pow_one] at h_dvd
  exact h_dvd

/-- Congruence form of Corollary 23.30: if `E[n] ⊆ E(F_q)` then `q ≡ 1 (mod n)`. -/
theorem corollary_23_30_finite_field_cong
    {F : Type*} [Field F] [DecidableEq F] [Fintype F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    [Fintype W.Point]
    (n : ℕ) (hn_prime : Nat.Prime n)
    (hn_cop : Nat.Coprime n (Fintype.card F))
    (hn_dvd : (n : ℤ) ∣ (Fintype.card W.Point : ℤ))
    (hcontained : NTorsionContainedIn W n F) :
    Fintype.card F ≡ 1 [MOD n] := by
  have h := corollary_23_30_finite_field W n hn_prime hn_cop hn_dvd hcontained
  have hle : 1 ≤ Fintype.card F := Fintype.card_pos
  exact ((Nat.modEq_iff_dvd' hle).mpr h).symm

end Corollary_23_30

section Corollary_23_31

variable {F : Type*} [Field F] [DecidableEq F]

/-- Corollary 23.31, full-torsion case: if `P` has additive order `N` and together with `Q`
generates `E[N]`, then the Weil pairing `e_N(P, Q)` has order exactly `N` (so it is a primitive
`N`-th root of unity). -/
theorem corollary_23_31_full_torsion
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (P Q : ↥(torsionSubgroup W (N : ℤ)))
    (hP_order : addOrderOf (P : W.Point) = N)
    (hPQ_generate : ∀ R : W.Point, R ∈ torsionSubgroup W (N : ℤ) →
      R ∈ AddSubgroup.closure ({(P : W.Point), (Q : W.Point)} : Set W.Point)) :
    orderOf (↑(weilPairing W N hN hchar P Q) : Fˣ) = N := by sorry

/-- Corollary 23.31 (one direction): if `m · Q ∈ ⟨P⟩` then the order of `e_N(P, Q)` divides `m`. -/
theorem corollary_23_31_order_dvd_of_mem_zmultiples
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (P Q : ↥(torsionSubgroup W (N : ℤ)))
    (hP_order : addOrderOf (P : W.Point) = N)
    (m : ℕ) (hm : 0 < m)
    (hQ_in_P : (m : ℤ) • (Q : W.Point) ∈ AddSubgroup.zmultiples (P : W.Point)) :
    orderOf (↑(weilPairing W N hN hchar P Q) : Fˣ) ∣ m := by sorry

/-- Corollary 23.31 (other direction): if the order of `e_N(P, Q)` divides `m`, then
`m · Q ∈ ⟨P⟩`. -/
theorem corollary_23_31_mem_zmultiples_of_order_dvd
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (P Q : ↥(torsionSubgroup W (N : ℤ)))
    (hP_order : addOrderOf (P : W.Point) = N)
    (m : ℕ) (hm : 0 < m)
    (h_dvd : orderOf (↑(weilPairing W N hN hchar P Q) : Fˣ) ∣ m) :
    (m : ℤ) • (Q : W.Point) ∈ AddSubgroup.zmultiples (P : W.Point) := by sorry

/-- Corollary 23.31 (equivalent form): `orderOf e_N(P, Q) ∣ m` iff `m · Q ∈ ⟨P⟩`. The order of
`e_N(P, Q)` equals the least integer `m` for which `m · Q ∈ ⟨P⟩`. -/
theorem corollary_23_31_order_eq_least_m
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (P Q : ↥(torsionSubgroup W (N : ℤ)))
    (hP_order : addOrderOf (P : W.Point) = N)
    (m : ℕ) (hm : 0 < m) :
    orderOf (↑(weilPairing W N hN hchar P Q) : Fˣ) ∣ m ↔
      (m : ℤ) • (Q : W.Point) ∈ AddSubgroup.zmultiples (P : W.Point) := by
  constructor
  · exact corollary_23_31_mem_zmultiples_of_order_dvd W N hN hchar P Q hP_order m hm
  · exact corollary_23_31_order_dvd_of_mem_zmultiples W N hN hchar P Q hP_order m hm

/-- Corollary 23.31 specialized to `m = 1`: `e_N(P, Q) = 1` iff `Q ∈ ⟨P⟩`. -/
theorem corollary_23_31_weilPairing_eq_one_iff_mem_zmultiples
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (P Q : ↥(torsionSubgroup W (N : ℤ)))
    (hP_order : addOrderOf (P : W.Point) = N) :
    (↑(weilPairing W N hN hchar P Q) : Fˣ) = 1 ↔
      (Q : W.Point) ∈ AddSubgroup.zmultiples (P : W.Point) := by
  constructor
  ·
    intro h_eq_one
    have h_order_one : orderOf (↑(weilPairing W N hN hchar P Q) : Fˣ) ∣ 1 := by
      rw [Nat.dvd_one]
      exact orderOf_eq_one_iff.mpr h_eq_one
    have h_mem := corollary_23_31_mem_zmultiples_of_order_dvd W N hN hchar P Q hP_order 1
      Nat.one_pos h_order_one
    simpa using h_mem
  ·
    intro hQ_mem
    have h_dvd : orderOf (↑(weilPairing W N hN hchar P Q) : Fˣ) ∣ 1 := by
      apply corollary_23_31_order_dvd_of_mem_zmultiples W N hN hchar P Q hP_order 1 Nat.one_pos
      simpa using hQ_mem
    rw [Nat.dvd_one] at h_dvd
    exact orderOf_eq_one_iff.mp h_dvd

/-- The predicate "the subgroup generated by `P` and `Q` is cyclic": there exists a single
generator `R` whose multiples coincide with `⟨P, Q⟩`. -/
def IsSubgroupCyclicPair
    {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve.Affine F}
    (P Q : W.Point) : Prop :=
  ∃ R : W.Point,
    AddSubgroup.closure ({P, Q} : Set W.Point) = AddSubgroup.zmultiples R

/-- Corollary 23.31 (one direction of the cyclic characterization):
if `e_N(P, Q) = 1` then `⟨P, Q⟩` is cyclic. -/
theorem corollary_23_31_cyclic_of_weilPairing_eq_one
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (P Q : ↥(torsionSubgroup W (N : ℤ)))
    (hP_order : addOrderOf (P : W.Point) = N)
    (h_eq_one : (↑(weilPairing W N hN hchar P Q) : Fˣ) = 1) :
    IsSubgroupCyclicPair (P : W.Point) (Q : W.Point) := by
  have hQ_mem := (corollary_23_31_weilPairing_eq_one_iff_mem_zmultiples
    W N hN hchar P Q hP_order).mp h_eq_one

  use (P : W.Point)
  apply le_antisymm
  ·
    rw [AddSubgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    cases hx with
    | inl h => rw [h]; exact AddSubgroup.mem_zmultiples _
    | inr h => rw [h]; exact hQ_mem
  ·
    rw [AddSubgroup.zmultiples_le]
    exact AddSubgroup.subset_closure (Set.mem_insert _ _)

/-- Corollary 23.31 (other direction): if `⟨P, Q⟩` is cyclic then `e_N(P, Q) = 1`. -/
theorem corollary_23_31_weilPairing_eq_one_of_cyclic
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (P Q : ↥(torsionSubgroup W (N : ℤ)))
    (hP_order : addOrderOf (P : W.Point) = N)
    (hcyclic : IsSubgroupCyclicPair (P : W.Point) (Q : W.Point)) :
    (↑(weilPairing W N hN hchar P Q) : Fˣ) = 1 := by
  apply (corollary_23_31_weilPairing_eq_one_iff_mem_zmultiples
    W N hN hchar P Q hP_order).mpr
  obtain ⟨R, hR⟩ := hcyclic
  have hQ_cl : (Q : W.Point) ∈ AddSubgroup.closure ({(P : W.Point), (Q : W.Point)} : Set W.Point) :=
    AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hP_cl : (P : W.Point) ∈ AddSubgroup.closure ({(P : W.Point), (Q : W.Point)} : Set W.Point) :=
    AddSubgroup.subset_closure (Set.mem_insert _ _)
  rw [hR] at hQ_cl hP_cl

  have hR_tor : (N : ℤ) • R = 0 := by
    have : R ∈ AddSubgroup.closure ({(P : W.Point), (Q : W.Point)} : Set W.Point) := by
      rw [hR]; exact AddSubgroup.mem_zmultiples R
    have hle : AddSubgroup.closure ({(P : W.Point), (Q : W.Point)} : Set W.Point) ≤
        torsionSubgroup W (N : ℤ) := by
      rw [AddSubgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;> [exact P.2; exact Q.2]
    exact (mem_torsionSubgroup W (N : ℤ) R).mp (hle this)

  have hR_ord_dvd : addOrderOf R ∣ N := by
    rw [← Int.natCast_dvd_natCast]
    exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr hR_tor
  have hP_ord_dvd : addOrderOf (P : W.Point) ∣ addOrderOf R :=
    addOrderOf_dvd_of_mem_zmultiples hP_cl
  have hR_ord : addOrderOf R = N :=
    Nat.dvd_antisymm hR_ord_dvd (hP_order ▸ hP_ord_dvd)

  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hP_cl

  have h_gcd : Int.gcd k (N : ℤ) = 1 := by
    by_contra h_ne
    have hg : 1 < Int.gcd k (N : ℤ) := by
      have hg_pos : 0 < Int.gcd k (N : ℤ) := by
        rw [Int.gcd_pos_iff]; right; exact_mod_cast hN.ne'
      omega
    set g := Int.gcd k (N : ℤ)
    have hg_dvd_N : g ∣ N := by exact_mod_cast Int.gcd_dvd_right (a := k) (b := (N : ℤ))
    obtain ⟨k', hk'⟩ : (g : ℤ) ∣ k := Int.gcd_dvd_left (a := k) (b := (N : ℤ))
    have hsmul_zero : ((N / g : ℕ) : ℤ) • (P : W.Point) = 0 := by
      have step1 : ((N / g : ℕ) : ℤ) • (P : W.Point) = (((N / g : ℕ) : ℤ) * k) • R := by
        rw [← hk, mul_smul]
      have step2 : (((N / g : ℕ) : ℤ) * k) • R = (((N : ℤ)) * k') • R := by
        congr 1
        have hdmc : (N / g * g : ℕ) = N := Nat.div_mul_cancel hg_dvd_N
        calc ((N / g : ℕ) : ℤ) * k = ((N / g : ℕ) : ℤ) * (↑g * k') := by rw [hk']
          _ = (((N / g : ℕ) : ℤ) * ↑g) * k' := by ring
          _ = ((N / g * g : ℕ) : ℤ) * k' := by push_cast; ring
          _ = (N : ℤ) * k' := by rw [hdmc]
      rw [step1, step2, mul_comm (↑N) k', mul_smul, hR_tor, smul_zero]
    have hord : addOrderOf (P : W.Point) ∣ N / g := by
      rw [← Int.natCast_dvd_natCast]
      exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr hsmul_zero
    rw [hP_order] at hord
    have hlt : N / g < N := Nat.div_lt_self hN hg
    exact absurd hlt (Nat.not_lt.mpr (Nat.le_of_dvd
      (Nat.div_pos (Nat.le_of_dvd hN hg_dvd_N) (by omega)) hord))

  have hab := Int.gcd_eq_gcd_ab k (N : ℤ)
  rw [h_gcd, Nat.cast_one] at hab

  have hR_in_P : R ∈ AddSubgroup.zmultiples (P : W.Point) := by
    rw [AddSubgroup.mem_zmultiples_iff]
    refine ⟨Int.gcdA k (N : ℤ), ?_⟩
    have h1 : (1 : ℤ) • R = R := one_zsmul R
    have step : (k * Int.gcdA k ↑N + ↑N * Int.gcdB k ↑N) • R =
        Int.gcdA k ↑N • (k • R) + Int.gcdB k ↑N • ((N : ℤ) • R) := by
      rw [add_smul, mul_comm k, mul_smul]
      congr 1
      rw [mul_comm, mul_smul]
    rw [← h1, hab, step, hk, hR_tor, smul_zero, add_zero]
  exact (AddSubgroup.zmultiples_le.mpr hR_in_P) hQ_cl

/-- Corollary 23.31, equivalence form: `e_N(P, Q) = 1` iff the subgroup `⟨P, Q⟩` is cyclic. -/
theorem corollary_23_31_weilPairing_eq_one_iff_cyclic
    {F : Type*} [Field F] [DecidableEq F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic]
    (N : ℕ) (hN : 0 < N) (hchar : ¬ (ringChar F ∣ N))
    (P Q : ↥(torsionSubgroup W (N : ℤ)))
    (hP_order : addOrderOf (P : W.Point) = N) :
    (↑(weilPairing W N hN hchar P Q) : Fˣ) = 1 ↔
      IsSubgroupCyclicPair (P : W.Point) (Q : W.Point) := by
  constructor
  · exact corollary_23_31_cyclic_of_weilPairing_eq_one W N hN hchar P Q hP_order
  · exact corollary_23_31_weilPairing_eq_one_of_cyclic W N hN hchar P Q hP_order

end Corollary_23_31

end WeilPairing
