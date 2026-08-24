/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.EraseLead
import Mathlib.Algebra.CharP.Defs
import Atlas.EllipticCurves.code.ModularCurves
import Atlas.EllipticCurves.code.Uniformization

open scoped MatrixGroups UpperHalfPlane
open CongruenceSubgroup Complex

noncomputable section

namespace ModularFunction

/-- The upper half-plane as a subset of `ℂ`: complex numbers with strictly positive
imaginary part. -/
def upperHalfPlaneSet : Set ℂ := {z : ℂ | 0 < z.im}

/-- The local uniformizer `q_N(τ) = exp(2πiτ/N)` at the cusp `i∞` for level `N`. -/
def qMapN (N : ℕ) (τ : ℍ) : ℂ :=
  Complex.exp (2 * ↑Real.pi * Complex.I * (τ : ℂ) / (N : ℂ))

/-- `f : ℍ → ℂ` is meromorphic at the cusp `i∞` if, after the substitution
`q = q_N(τ)`, it agrees near `0` with a meromorphic function in `q`. -/
def IsMeromorphicAtInfty (f : ℍ → ℂ) : Prop :=
  ∃ (N : ℕ) (_ : 0 < N) (g : ℂ → ℂ), MeromorphicAt g 0 ∧
    ∀ᶠ τ : ℍ in UpperHalfPlane.atImInfty, f τ = g (qMapN N τ)

/-- `f : ℍ → ℂ` is meromorphic at every cusp (= every `SL₂(ℤ)`-translate of `i∞`). -/
def IsMeromorphicAtCusps (f : ℍ → ℂ) : Prop :=
  ∀ γ : SL(2, ℤ), IsMeromorphicAtInfty (fun τ => f (γ • τ))

/-- `f : ℍ → ℂ` is meromorphic on the upper half-plane if it extends to a meromorphic
function on the open set `{Im z > 0} ⊆ ℂ`. -/
def IsMeromorphicOnH (f : ℍ → ℂ) : Prop :=
  ∃ g : ℂ → ℂ, MeromorphicOn g upperHalfPlaneSet ∧
    ∀ τ : ℍ, g (τ : ℂ) = f τ

/-- `f` is invariant under the subgroup `Γ ≤ SL₂(ℤ)`, i.e. `f(γ τ) = f(τ)` for
all `γ ∈ Γ` and `τ ∈ ℍ`. -/
def IsInvariantUnder (f : ℍ → ℂ) (Γ : Subgroup SL(2, ℤ)) : Prop :=
  ∀ (γ : SL(2, ℤ)), γ ∈ Γ → ∀ (τ : ℍ), f (γ • τ) = f τ

/-- `f : ℍ → ℂ` is holomorphic on the upper half-plane if it extends to an analytic
function on the open set `{Im z > 0} ⊆ ℂ`. -/
def IsHolomorphicOnH (f : ℍ → ℂ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g upperHalfPlaneSet ∧
    ∀ τ : ℍ, g (τ : ℂ) = f τ

/-- The modular `j`-function `j : ℍ → ℂ`. -/
def jModular : ℍ → ℂ := jFunction

/-- The `j`-function is surjective from `ℍ` to `ℂ`. -/
theorem jModular_surjective : Function.Surjective jModular := jFunction_surjective

/-- The `j`-function is meromorphic on the upper half-plane (in fact holomorphic). -/
theorem jModular_meromorphicOnH : IsMeromorphicOnH jModular := by sorry

/-- The `j`-function is invariant under the full modular group `SL₂(ℤ)`. -/
theorem jModular_invariant_SL2 : IsInvariantUnder jModular ⊤ := by sorry

/-- The `j`-function is meromorphic at every cusp. -/
theorem jModular_meromorphicAtCusps : IsMeromorphicAtCusps jModular := by sorry

/-- Scaling of the upper half-plane by a positive integer `N`: sends `τ ∈ ℍ` to
`N τ ∈ ℍ`. -/
def scaleUHP (N : ℕ) (hN : 0 < N) (τ : ℍ) : ℍ :=
  ⟨(N : ℂ) * (τ : ℂ), by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im]
    simp [mul_pos (Nat.cast_pos.mpr hN) τ.im_pos]⟩

/-- The level-`N` `j`-function `j_N(τ) := j(N τ)` (cf. Theorem 19.13). -/
def jModularN (N : ℕ) (hN : 0 < N) (τ : ℍ) : ℂ :=
  jModular (scaleUHP N hN τ)

end ModularFunction

open ModularFunction

/-- A modular function for the congruence subgroup `Γ` (Definition 19.2): a function
`f : ℍ → ℂ` that is meromorphic on `ℍ`, `Γ`-invariant, and meromorphic at the cusps. -/
structure IsModularFunction (f : ℍ → ℂ) (Γ : Subgroup SL(2, ℤ)) : Prop where
  meromorphicOnH : IsMeromorphicOnH f
  invariant : IsInvariantUnder f Γ
  meromorphicAtCusps : IsMeromorphicAtCusps f

namespace ModularFunction

/-- Auxiliary version of Theorem 19.8: every modular function for `Γ(1) = SL₂(ℤ)` is
a rational function of `j(τ)`, witnessed by a pair `(P, Q)` of polynomials. -/
theorem is_rational_in_j_aux (f : ℍ → ℂ)
    (hmod : IsModularFunction f ⊤) :
    ∃ (P Q : Polynomial ℂ), Q ≠ 0 ∧
      ∀ τ : ℍ, f τ * Q.eval (jModular τ) = P.eval (jModular τ) := by sorry

/-- Theorem 19.8: every modular function for `Γ(1)` is a rational function of `j(τ)`;
equivalently `ℂ(Γ(1)) = ℂ(j)`. -/
theorem is_rational_in_j (f : ℍ → ℂ)
    (hmod : IsModularFunction f ⊤) :
    ∃ (P Q : Polynomial ℂ), Q ≠ 0 ∧
      ∀ τ : ℍ, f τ * Q.eval (jModular τ) = P.eval (jModular τ) :=
  is_rational_in_j_aux f hmod

/-- If `f = P(j)/Q(j)` is holomorphic on `ℍ`, then `Q(j(τ))` is never zero on `ℍ`. -/
theorem holomorphic_rational_no_poles (f : ℍ → ℂ) (P Q : Polynomial ℂ)
    (hQ : Q ≠ 0) (hhol : IsHolomorphicOnH f)
    (hfQ : ∀ τ : ℍ, f τ * Q.eval (jModular τ) = P.eval (jModular τ)) :
    ∀ τ : ℍ, Q.eval (jModular τ) ≠ 0 := by sorry

end ModularFunction

/-- The level-`N` `j`-function `j_N` is meromorphic on `ℍ`: it is the composition of
`j` with the (holomorphic) scaling `τ ↦ N τ`. -/
theorem jModularN_meromorphicOnH (N : ℕ) (hN : 0 < N) :
    IsMeromorphicOnH (jModularN N hN) := by
  obtain ⟨g, hg_mero, hg_eq⟩ := jModular_meromorphicOnH
  refine ⟨g ∘ ((N : ℂ) * ·), ?_, ?_⟩
  · intro z hz
    apply MeromorphicAt.comp_analyticAt
    · apply hg_mero
      simp only [upperHalfPlaneSet, Set.mem_setOf_eq] at hz ⊢
      simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im]
      linarith [mul_pos (Nat.cast_pos.mpr hN : (0 : ℝ) < (N : ℝ)) hz]
    · exact analyticAt_const.mul analyticAt_id
  · intro τ
    simp only [Function.comp, jModularN]
    have h := hg_eq (scaleUHP N hN τ)
    simp only [scaleUHP, UpperHalfPlane.coe_mk] at h
    exact h

/-- The level-`N` `j`-function `j_N(τ) = j(N τ)` is invariant under `Γ₀(N)`
(Theorem 19.13). -/
theorem jModularN_invariant_Gamma0 (N : ℕ) (hN : 0 < N) :
    IsInvariantUnder (jModularN N hN) (Gamma0 N) := by sorry

/-- The level-`N` `j`-function is meromorphic at every cusp. -/
theorem jModularN_meromorphicAtCusps (N : ℕ) (hN : 0 < N) :
    IsMeromorphicAtCusps (jModularN N hN) := by sorry

/-- Theorem 19.13: `j_N(τ) := j(Nτ)` is a modular function for `Γ₀(N)`. -/
theorem jModularN_isModularFunction (N : ℕ) (hN : 0 < N) :
    IsModularFunction (jModularN N hN) (Gamma0 N) :=
  ⟨jModularN_meromorphicOnH N hN,
   jModularN_invariant_Gamma0 N hN,
   jModularN_meromorphicAtCusps N hN⟩

open MvPolynomial

namespace ModularPolynomial

/-- The (classical) modular polynomial `Φ_N(X, Y) ∈ ℤ[X, Y]` as a `MvPolynomial`
indexed by `Fin 2`, characterized in Definition 19.15 as the minimal polynomial of
`j_N` over `ℂ(j)`. -/
noncomputable def Phi (N : ℕ) : MvPolynomial (Fin 2) ℤ := by sorry

/-- The modular polynomial `Φ_N`, repackaged for positive `N : ℕ+`. -/
def modularPolynomial (N : ℕ+) : MvPolynomial (Fin 2) ℤ := Phi N

/-- `modularPolynomial N = Phi N` (definitional unfolding for `simp`). -/
@[simp] theorem modularPolynomial_eq (N : ℕ+) : modularPolynomial N = Phi N := rfl

/-- Evaluate `Φ_N(j₁, j₂)` in an arbitrary commutative ring `R` via the integer
casts. -/
def eval {R : Type*} [CommRing R] (N : ℕ) (j₁ j₂ : R) : R :=
  eval₂ (Int.castRingHom R) (![j₁, j₂]) (Phi N)

open Classical in
/-- Two `j`-invariants `j₁, j₂ ∈ F` admit a cyclic `N`-isogeny over `F`: there are
elliptic curves `E₁, E₂` with those `j`-invariants and a surjective group
homomorphism `E₁ → E₂` whose kernel is cyclic of order `N`. -/
def HasCyclicNIsogeny (F : Type*) [Field F] (N : ℕ) (j₁ j₂ : F) : Prop :=
  ∃ (E₁ E₂ : WeierstrassCurve.Affine F) (_ : E₁.IsElliptic) (_ : E₂.IsElliptic),
    E₁.j = j₁ ∧ E₂.j = j₂ ∧
    ∃ (φ : E₁.Point →+ E₂.Point), Function.Surjective φ ∧
      ∃ (P : E₁.Point), addOrderOf P = N ∧
        ∀ Q : E₁.Point, φ Q = 0 → ∃ k : ℤ, Q = k • P

/-- Theorem 20.7: the modular polynomial is symmetric, `Φ_N(X, Y) = Φ_N(Y, X)`. -/
theorem phi_symmetric (N : ℕ) (hN : 1 < N) :
    (rename (Equiv.swap (0 : Fin 2) 1)) (Phi N) = Phi N := by sorry

/-- Symmetry of the evaluation `Φ_N(j₁, j₂) = Φ_N(j₂, j₁)`, derived from `phi_symmetric`. -/
theorem eval_swap {R : Type*} [CommRing R] (N : ℕ) (hN : 1 < N) (j₁ j₂ : R) :
    eval N j₁ j₂ = eval N j₂ j₁ := by
  unfold eval
  conv_rhs => rw [← phi_symmetric N hN]
  rw [eval₂_rename]
  congr 1
  funext i
  fin_cases i <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- Dedekind's `ψ` function `ψ(N) = N ∏_{p | N}(1 + 1/p)`, equal to the index
`[Γ(1) : Γ₀(N)]` and the degree of `Φ_N` in each variable. -/
def dedekindPsi (N : ℕ) : ℕ :=
  if N = 0 then 0
  else ∏ p ∈ N.primeFactors, p ^ (N.factorization p - 1) * (p + 1)

/-- Theorem 19.14: the degree of `Φ_N` in the variable `Y` equals
`[Γ(1) : Γ₀(N)] = ψ(N)`. -/
theorem phi_degreeOf_Y (N : ℕ) (hN : 0 < N) :
    degreeOf (1 : Fin 2) (Phi N) = dedekindPsi N := by sorry

/-- The two variable-degrees of `Φ_N` agree, by the symmetry `Φ_N(X, Y) = Φ_N(Y, X)`. -/
theorem phi_degreeOf_X_eq_Y (N : ℕ) (hN : 1 < N) :
    degreeOf (0 : Fin 2) (Phi N) = degreeOf (1 : Fin 2) (Phi N) := by
  have h := phi_symmetric N hN
  have hinj : Function.Injective (Equiv.swap (0 : Fin 2) 1) :=
    (Equiv.swap (0 : Fin 2) 1).injective
  have h1 := degreeOf_rename_of_injective hinj (0 : Fin 2) (p := Phi N)
  simp only [Equiv.swap_apply_left] at h1
  rw [h] at h1
  exact h1.symm

/-- Consequently, the degree of `Φ_N` in the variable `X` also equals `ψ(N)`. -/
theorem phi_degreeOf_X (N : ℕ) (hN : 1 < N) :
    degreeOf (0 : Fin 2) (Phi N) = dedekindPsi N := by
  rw [phi_degreeOf_X_eq_Y N hN, phi_degreeOf_Y N (by omega)]

/-- Theorem 20.4: over any field of characteristic not dividing `N`,
`Φ_N(j₁, j₂) = 0` iff `j₁, j₂` are the `j`-invariants of elliptic curves related by a
cyclic isogeny of degree `N`. -/
theorem eval_eq_zero_iff {F : Type*} [Field F]
    (N : ℕ) (hN : 1 < N) (hchar : ¬(ringChar F ∣ N)) (j₁ j₂ : F) :
    eval N j₁ j₂ = 0 ↔ HasCyclicNIsogeny F N j₁ j₂ := by sorry

/-- Specialization of Theorem 20.4 to fields of characteristic `0` (where the
character/divisibility hypothesis is automatic). -/
theorem eval_eq_zero_iff_of_charZero {F : Type*} [Field F] [CharZero F]
    (N : ℕ) (hN : 1 < N) (j₁ j₂ : F) :
    eval N j₁ j₂ = 0 ↔ HasCyclicNIsogeny F N j₁ j₂ := by
  apply eval_eq_zero_iff N hN
  rw [ringChar.eq_zero]; omega

/-- The diagonal modular polynomial `Φ_N(X, X) ∈ ℤ[X]`, obtained by specializing both
variables of `Φ_N` to the same indeterminate. -/
def diagPhi (N : ℕ) : Polynomial ℤ :=
  MvPolynomial.aeval (fun _ : Fin 2 => (Polynomial.X : Polynomial ℤ)) (Phi N)

/-- For prime `N`, `Φ_N(X, X) = -X^{2N} + r(X)` with `deg r < 2N`; in particular the
leading term is `-X^{2N}` (a strengthening of Lemma 20.7's tail). -/
theorem diagPhi_eq_neg_X_pow_add_lower (N : ℕ) (hN : Nat.Prime N) :
    ∃ r : Polynomial ℤ, diagPhi N = -(Polynomial.X ^ (2 * N)) + r ∧
      r.natDegree < 2 * N := by sorry

/-- For prime `N`, the leading coefficient of `Φ_N(X, X)` is `-1`. -/
theorem diagPhi_leadingCoeff (N : ℕ) (hN : Nat.Prime N) :
    (diagPhi N).leadingCoeff = -1 := by
  obtain ⟨r, hdecomp, hdeg⟩ := diagPhi_eq_neg_X_pow_add_lower N hN
  rw [hdecomp]
  set p := -((Polynomial.X : Polynomial ℤ) ^ (2 * N)) with hp_def
  have hp_ndeg : p.natDegree = 2 * N := by
    simp [hp_def, Polynomial.natDegree_neg, Polynomial.natDegree_X_pow]
  have hr_lt : r.natDegree < p.natDegree := hp_ndeg ▸ hdeg
  have hdeg_lt : r.degree < p.degree := Polynomial.degree_lt_degree hr_lt
  calc (p + r).leadingCoeff
      = p.leadingCoeff := Polynomial.leadingCoeff_add_of_degree_lt' hdeg_lt
    _ = -(((Polynomial.X : Polynomial ℤ) ^ (2 * N)).leadingCoeff) := by
        simp [hp_def, Polynomial.leadingCoeff_neg]
    _ = -1 := by rw [Polynomial.leadingCoeff_X_pow]

end ModularPolynomial

namespace ModularFunction

/-- Corollary 19.10: every modular function for `Γ(1)` that is holomorphic on `ℍ` is a
polynomial in `j(τ)`. The witness `P` is constructed from a rational-function
representation by checking that the denominator polynomial has degree `0`. -/
theorem exists_polynomial_eval_eq
    (f : ℍ → ℂ)
    (hmod : IsModularFunction f ⊤)
    (hhol : IsHolomorphicOnH f) :
    ∃ P : Polynomial ℂ, ∀ τ : ℍ, f τ = P.eval (jModular τ) := by
  obtain ⟨P, Q, hQ, hfQ⟩ := is_rational_in_j f hmod

  have hQeval := holomorphic_rational_no_poles f P Q hQ hhol hfQ

  have hQnoroot : ∀ c : ℂ, ¬Q.IsRoot c := by
    intro c hroot
    obtain ⟨τ, hτ⟩ := jModular_surjective c
    exact hQeval τ (hτ ▸ Polynomial.IsRoot.def.mp hroot)

  have hQdeg : Q.degree = 0 := by
    by_contra h
    exact absurd (IsAlgClosed.exists_root Q h) (not_exists.mpr hQnoroot)

  have hQC := Polynomial.eq_C_of_degree_eq_zero hQdeg
  have hc0 : Q.coeff 0 ≠ 0 := by
    intro h0
    exact hQ (by rw [hQC, h0, map_zero])

  refine ⟨Polynomial.C (Q.coeff 0)⁻¹ * P, fun τ => ?_⟩
  have heval : Q.eval (jModular τ) = Q.coeff 0 := by
    conv_lhs => rw [hQC]; simp only [Polynomial.eval_C]
  have hmul := hfQ τ
  rw [heval] at hmul
  rw [Polynomial.eval_mul, Polynomial.eval_C,
      ← hmul, mul_comm (f τ) _, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]

end ModularFunction

section ModularCurveX0Defs

open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup Matrix
open scoped MatrixGroups UpperHalfPlane

/-- The `(i, j)`-entry of an `SL₂(ℤ)`-matrix, coerced to `ℚ`. -/
def sl2zEntry (γ : SL(2, ℤ)) (i j : Fin 2) : ℚ :=
  ((↑γ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ)

/-- The determinant identity `ad - bc = 1` rewritten in terms of `sl2zEntry`. -/
lemma sl2zEntry_det (γ : SL(2, ℤ)) :
    sl2zEntry γ 0 0 * sl2zEntry γ 1 1 - sl2zEntry γ 0 1 * sl2zEntry γ 1 0 = 1 := by
  simp only [sl2zEntry]
  have hd := γ.det_coe
  rw [det_fin_two] at hd
  exact_mod_cast hd

/-- The matrix-product entry formula `(g₁ g₂)_{ij} = g₁_{i0} g₂_{0j} + g₁_{i1} g₂_{1j}`
for `SL₂(ℤ)`-matrices, expressed via `sl2zEntry`. -/
lemma sl2zEntry_mul (g₁ g₂ : SL(2, ℤ)) (i j : Fin 2) :
    sl2zEntry (g₁ * g₂) i j =
    sl2zEntry g₁ i 0 * sl2zEntry g₂ 0 j + sl2zEntry g₁ i 1 * sl2zEntry g₂ 1 j := by
  simp only [sl2zEntry]
  simp [mul_apply, Fin.sum_univ_two]

/-- The extended upper half-plane `ℍ*` = `ℍ ⊔ ℚ ∪ {∞}`, obtained by adjoining the
rational cusps and the cusp at infinity to `ℍ`. -/
def ExtendedUpperHalfPlane := ℍ ⊕ (WithTop ℚ)

namespace ExtendedUpperHalfPlane

/-- Inclusion `ℍ ↪ ℍ*`. -/
def ofUHP (τ : ℍ) : ExtendedUpperHalfPlane := Sum.inl τ

/-- Inclusion of a rational cusp `r ∈ ℚ ↪ ℍ*`. -/
def ofRat (r : ℚ) : ExtendedUpperHalfPlane := Sum.inr (↑r)

/-- The cusp at infinity in `ℍ*`. -/
def cuspInfty : ExtendedUpperHalfPlane := Sum.inr ⊤

/-- The action of `SL₂(ℤ)` on the cusps `ℚ ∪ {∞}`, given by the linear-fractional
formula `γ · r = (ar + b)/(cr + d)` and `γ · ∞ = a/c` (with `c = 0` mapping to `∞`). -/
def cuspAction (γ : SL(2, ℤ)) : WithTop ℚ → WithTop ℚ
  | ⊤ => if sl2zEntry γ 1 0 = 0 then ⊤ else ↑(sl2zEntry γ 0 0 / sl2zEntry γ 1 0)
  | (r : ℚ) => if sl2zEntry γ 1 0 * r + sl2zEntry γ 1 1 = 0 then ⊤
      else ↑((sl2zEntry γ 0 0 * r + sl2zEntry γ 0 1) / (sl2zEntry γ 1 0 * r + sl2zEntry γ 1 1))

/-- The identity matrix acts trivially on the cusps. -/
theorem cuspAction_one : ∀ x, cuspAction 1 x = x := by
  intro x
  cases x with
  | top => simp [cuspAction, sl2zEntry]
  | coe r => simp [cuspAction, sl2zEntry]

/-- Auxiliary algebraic identity used in proving the multiplicative law for
`cuspAction`: handles the case where the denominator vanishes for `g₂`. -/
lemma cuspAction_factor_denom_zero (g₁ g₂ : SL(2, ℤ)) (r : ℚ)
    (hd₂ : sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1 = 0) :
    sl2zEntry (g₁ * g₂) 1 0 * r + sl2zEntry (g₁ * g₂) 1 1 =
    sl2zEntry g₁ 1 0 * (sl2zEntry g₂ 0 0 * r + sl2zEntry g₂ 0 1) := by
  rw [sl2zEntry_mul, sl2zEntry_mul]
  have : sl2zEntry g₁ 1 1 * (sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1) = 0 := by
    rw [hd₂, mul_zero]
  linarith

/-- Companion identity to `cuspAction_factor_denom_zero` for the numerator. -/
lemma cuspAction_factor_numer_zero (g₁ g₂ : SL(2, ℤ)) (r : ℚ)
    (hd₂ : sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1 = 0) :
    sl2zEntry (g₁ * g₂) 0 0 * r + sl2zEntry (g₁ * g₂) 0 1 =
    sl2zEntry g₁ 0 0 * (sl2zEntry g₂ 0 0 * r + sl2zEntry g₂ 0 1) := by
  rw [sl2zEntry_mul, sl2zEntry_mul]
  have : sl2zEntry g₁ 0 1 * (sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1) = 0 := by
    rw [hd₂, mul_zero]
  linarith

/-- If the denominator of the linear-fractional action of `g₂` on `r` vanishes, then
the numerator cannot also vanish (consequence of `det g₂ = 1`). -/
lemma cuspAction_numer_ne_zero_of_denom_zero (g₂ : SL(2, ℤ)) (r : ℚ)
    (hd₂ : sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1 = 0) :
    sl2zEntry g₂ 0 0 * r + sl2zEntry g₂ 0 1 ≠ 0 := by
  intro heq
  have hdet := sl2zEntry_det g₂
  have : sl2zEntry g₂ 0 0 * (sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1) -
    sl2zEntry g₂ 1 0 * (sl2zEntry g₂ 0 0 * r + sl2zEntry g₂ 0 1) = 1 := by linarith
  rw [hd₂, heq, mul_zero, mul_zero, sub_zero] at this
  exact zero_ne_one this

set_option maxHeartbeats 400000 in
/-- The cusp action at `∞` is compatible with multiplication in `SL₂(ℤ)`:
`(g₁ g₂) · ∞ = g₁ · (g₂ · ∞)`. -/
theorem cuspAction_mul_top (g₁ g₂ : SL(2, ℤ)) :
    cuspAction (g₁ * g₂) ⊤ = cuspAction g₁ (cuspAction g₂ ⊤) := by
  simp only [cuspAction]
  by_cases hc₂ : sl2zEntry g₂ 1 0 = 0
  · simp only [hc₂, ite_true]
    rw [sl2zEntry_mul]
    simp only [hc₂, mul_zero, add_zero]
    have ha₂ : sl2zEntry g₂ 0 0 ≠ 0 := by
      intro heq
      have := sl2zEntry_det g₂
      rw [hc₂, mul_zero, sub_zero, heq, zero_mul] at this
      exact zero_ne_one this
    by_cases hc₁ : sl2zEntry g₁ 1 0 = 0
    · simp [hc₁]
    · simp only [mul_ne_zero hc₁ ha₂, ite_false, hc₁]
      rw [sl2zEntry_mul]
      simp only [hc₂, mul_zero, add_zero]
      congr 1
      field_simp
  · simp only [hc₂, ite_false]
    rw [sl2zEntry_mul, sl2zEntry_mul]
    by_cases hdenom : sl2zEntry g₁ 1 0 * (sl2zEntry g₂ 0 0 / sl2zEntry g₂ 1 0) +
        sl2zEntry g₁ 1 1 = 0
    · have : sl2zEntry g₁ 1 0 * sl2zEntry g₂ 0 0 +
          sl2zEntry g₁ 1 1 * sl2zEntry g₂ 1 0 = 0 := by
        field_simp at hdenom
        linarith
      simp [this, hdenom]
    · have hne : sl2zEntry g₁ 1 0 * sl2zEntry g₂ 0 0 +
          sl2zEntry g₁ 1 1 * sl2zEntry g₂ 1 0 ≠ 0 := by
        intro heq
        apply hdenom
        field_simp
        linarith
      simp only [hne, hdenom, ite_false]
      congr 1
      field_simp

set_option maxHeartbeats 800000 in
/-- The cusp action at a rational cusp `r` is compatible with multiplication in
`SL₂(ℤ)`: `(g₁ g₂) · r = g₁ · (g₂ · r)`. -/
theorem cuspAction_mul_coe (g₁ g₂ : SL(2, ℤ)) (r : ℚ) :
    cuspAction (g₁ * g₂) ↑r = cuspAction g₁ (cuspAction g₂ ↑r) := by
  simp only [cuspAction]
  by_cases hd₂ : sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1 = 0
  · simp only [hd₂, ite_true]
    have hc₂_ne : sl2zEntry g₂ 1 0 ≠ 0 := by
      intro heq
      rw [heq, zero_mul, zero_add] at hd₂
      have := sl2zEntry_det g₂
      rw [hd₂, heq] at this
      simp at this
    have hnum₂_ne := cuspAction_numer_ne_zero_of_denom_zero g₂ r hd₂
    rw [cuspAction_factor_denom_zero g₁ g₂ r hd₂,
        cuspAction_factor_numer_zero g₁ g₂ r hd₂]
    by_cases hc₁ : sl2zEntry g₁ 1 0 = 0
    · simp [hc₁]
    · simp only [mul_ne_zero hc₁ hnum₂_ne, ite_false, hc₁]
      congr 1
      field_simp
  · simp only [hd₂, ite_false]
    set s := (sl2zEntry g₂ 0 0 * r + sl2zEntry g₂ 0 1) /
             (sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1) with hs_def
    have hdenom_rel : sl2zEntry g₁ 1 0 * s + sl2zEntry g₁ 1 1 =
        (sl2zEntry (g₁ * g₂) 1 0 * r + sl2zEntry (g₁ * g₂) 1 1) /
        (sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1) := by
      rw [hs_def, sl2zEntry_mul, sl2zEntry_mul]
      have hd₂' : r * sl2zEntry g₂ 1 0 + sl2zEntry g₂ 1 1 ≠ 0 := by
        rwa [show r * sl2zEntry g₂ 1 0 + sl2zEntry g₂ 1 1 =
             sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1 from by ring]
      field_simp
      ring
    have zero_iff : sl2zEntry g₁ 1 0 * s + sl2zEntry g₁ 1 1 = 0 ↔
        sl2zEntry (g₁ * g₂) 1 0 * r + sl2zEntry (g₁ * g₂) 1 1 = 0 := by
      rw [hdenom_rel, div_eq_zero_iff]
      exact ⟨fun h => h.resolve_right hd₂, fun h => Or.inl h⟩
    by_cases hprod : sl2zEntry (g₁ * g₂) 1 0 * r + sl2zEntry (g₁ * g₂) 1 1 = 0
    · have : sl2zEntry g₁ 1 0 * s + sl2zEntry g₁ 1 1 = 0 := zero_iff.mpr hprod
      simp [hprod, this]
    · have hne : sl2zEntry g₁ 1 0 * s + sl2zEntry g₁ 1 1 ≠ 0 :=
        fun h => hprod (zero_iff.mp h)
      simp only [hprod, hne, ite_false]
      congr 1
      rw [hs_def, sl2zEntry_mul, sl2zEntry_mul, sl2zEntry_mul, sl2zEntry_mul]
      have hd₂' : r * sl2zEntry g₂ 1 0 + sl2zEntry g₂ 1 1 ≠ 0 := by
        rwa [show r * sl2zEntry g₂ 1 0 + sl2zEntry g₂ 1 1 =
             sl2zEntry g₂ 1 0 * r + sl2zEntry g₂ 1 1 from by ring]
      field_simp
      ring

/-- Multiplicativity of the cusp action on all of `WithTop ℚ`, combining the cases
for the cusp at infinity and the finite rational cusps. -/
theorem cuspAction_mul (g₁ g₂ : SL(2, ℤ)) :
    ∀ x, cuspAction (g₁ * g₂) x = cuspAction g₁ (cuspAction g₂ x) := by
  intro x
  cases x with
  | top => exact cuspAction_mul_top g₁ g₂
  | coe r => exact cuspAction_mul_coe g₁ g₂ r

/-- The `SL₂(ℤ)`-action on `ℍ*`, defined cases-wise: the Möbius action on the upper
half-plane component, and `cuspAction` on the cusp component. -/
def smulExt (γ : SL(2, ℤ)) (x : ExtendedUpperHalfPlane) : ExtendedUpperHalfPlane :=
  match x with
  | Sum.inl τ => Sum.inl (γ • τ)
  | Sum.inr c => Sum.inr (cuspAction γ c)

/-- Register `smulExt` as the scalar multiplication of `SL₂(ℤ)` on `ℍ*`. -/
instance : SMul SL(2, ℤ) ExtendedUpperHalfPlane where
  smul := smulExt

/-- The `SL₂(ℤ)`-action on `ℍ*` is a `MulAction`, with `1 · x = x` and
`(g₁ g₂) · x = g₁ · (g₂ · x)`. -/
instance : MulAction SL(2, ℤ) ExtendedUpperHalfPlane where
  one_smul x := by
    show smulExt 1 x = x
    cases x with
    | inl τ =>
      show Sum.inl ((1 : SL(2, ℤ)) • τ) = Sum.inl τ
      simp [one_smul]
    | inr c =>
      show Sum.inr (cuspAction 1 c) = Sum.inr c
      simp [cuspAction_one]
  mul_smul g₁ g₂ x := by
    show smulExt (g₁ * g₂) x = smulExt g₁ (smulExt g₂ x)
    cases x with
    | inl τ =>
      show Sum.inl ((g₁ * g₂) • τ) = Sum.inl (g₁ • (g₂ • τ))
      congr 1
      exact SemigroupAction.mul_smul g₁ g₂ τ
    | inr c =>
      show Sum.inr (cuspAction (g₁ * g₂) c) = Sum.inr (cuspAction g₁ (cuspAction g₂ c))
      congr 1
      exact cuspAction_mul g₁ g₂ c

/-- Restriction of the `SL₂(ℤ)`-action on `ℍ*` to the congruence subgroup `Γ₀(N)`. -/
instance gamma0Action (N : ℕ) :
    MulAction (CongruenceSubgroup.Gamma0 N) ExtendedUpperHalfPlane :=
  MulAction.compHom ExtendedUpperHalfPlane (CongruenceSubgroup.Gamma0 N).subtype

end ExtendedUpperHalfPlane

/-- The modular curve `X₀(N) = Γ₀(N) \ ℍ*` as the orbit space of `Γ₀(N)` acting on
the extended upper half-plane. -/
def ModularCurveX0 (N : ℕ) : Type :=
  MulAction.orbitRel.Quotient (CongruenceSubgroup.Gamma0 N) ExtendedUpperHalfPlane

/-- Canonical projection `ℍ* → X₀(N)`, sending a point to its `Γ₀(N)`-orbit. -/
def ModularCurveX0.mk (N : ℕ) : ExtendedUpperHalfPlane → ModularCurveX0 N :=
  Quotient.mk (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ExtendedUpperHalfPlane)

end ModularCurveX0Defs

namespace ModularFunctionField

open Polynomial hiding C X coeff_zero

/-- The modular `j`-function `ℍ → ℂ`, accessed inside the `ModularFunctionField`
namespace. -/
def jFunction : ℍ → ℂ := _root_.jFunction

/-- `f : ℍ → ℂ` is a rational function of `j(τ)` if there exist polynomials `p, q`
with `q ≠ 0` such that `q(j(τ)) · f(τ) = p(j(τ))` for all `τ ∈ ℍ`. -/
def IsRationalFunctionOfJ (f : ℍ → ℂ) : Prop :=
  ∃ (p q : Polynomial ℂ), q ≠ 0 ∧
    ∀ τ : ℍ, Polynomial.eval (jFunction τ) q * f τ = Polynomial.eval (jFunction τ) p

/-- The `q`-expansion of a polynomial in `j`, viewed as a Laurent series in `q`. -/
noncomputable def qExpJ : ℂ[X] → LaurentSeries ℂ := by sorry

/-- The leading-order coefficient of the `q`-expansion of `P(j)` at order
`-deg P` is the leading coefficient of `P` (since `j = 1/q + O(1)`). -/
theorem qExpJ_leadingCoeff (P : ℂ[X]) (hP : P ≠ 0) :
    (qExpJ P).coeff (-(P.natDegree : ℤ)) = P.leadingCoeff := by sorry

/-- The map `qExpJ` is additive: `qExpJ (P - Q) = qExpJ P - qExpJ Q`. -/
theorem qExpJ_sub (P Q : ℂ[X]) : qExpJ (P - Q) = qExpJ P - qExpJ Q := by sorry

/-- Each coefficient of the `q`-expansion of a monomial `a · X^d` in `j` is an
integer multiple of `a`. -/
theorem qExpJ_monomial_coeffs (a : ℂ) (d : ℕ) (n : ℤ) :
    ∃ (k : ℤ), (qExpJ (Polynomial.C a * Polynomial.X ^ d)).coeff n = k * a := by sorry

/-- The `q`-expansion of an arbitrary function `f : ℍ → ℂ` as a Laurent series. -/
noncomputable def qExpansion : (ℍ → ℂ) → LaurentSeries ℂ := by sorry

/-- For a polynomial `P`, the `q`-expansion of `τ ↦ P(j(τ))` equals `qExpJ P`. -/
theorem qExpansion_eq_qExpJ (P : ℂ[X]) :
    qExpansion (fun τ => P.eval (jFunction τ)) = qExpJ P := by sorry

/-- Corollary 19.10 in this namespace: every holomorphic modular function for `Γ(1)`
is a polynomial in `j(τ)`. -/
theorem holomorphic_modular_is_polynomial_in_j (f : ℍ → ℂ)
    (hmod : IsModularFunction f ⊤)
    (hhol : ModularFunction.IsHolomorphicOnH f) :
    ∃ P : ℂ[X], ∀ τ : ℍ, f τ = P.eval (jFunction τ) := by

  obtain ⟨P, hP⟩ := ModularFunction.exists_polynomial_eval_eq f hmod hhol
  exact ⟨P, fun τ => by rw [hP τ]; rfl⟩

/-- Deprecated name for `holomorphic_modular_is_polynomial_in_j` (Corollary 19.10). -/
@[deprecated (since := "2025-04-30")]
alias corollary_19_10 := holomorphic_modular_is_polynomial_in_j

/-- A Laurent series `f` has coefficients in an additive subgroup `A ⊆ ℂ` if every
coefficient `f.coeff n` belongs to `A`. -/
def HasCoeffsIn (f : LaurentSeries ℂ) (A : AddSubgroup ℂ) : Prop :=
  ∀ n : ℤ, f.coeff n ∈ A

/-- A function `f : ℍ → ℂ` has `q`-expansion coefficients in the additive subgroup
`A ⊆ ℂ`. -/
def HasQExpCoeffsIn (f : ℍ → ℂ) (A : AddSubgroup ℂ) : Prop :=
  HasCoeffsIn (qExpansion f) A

/-- A polynomial `P : ℂ[X]` has all its coefficients in the additive subgroup
`A ⊆ ℂ`. -/
def PolynomialHasCoeffsIn (P : ℂ[X]) (A : AddSubgroup ℂ) : Prop :=
  ∀ k : ℕ, P.coeff k ∈ A

/-- If the `q`-expansion of `P(j)` has all coefficients in `A`, then so does `P`
itself. Proved by induction on the degree, peeling off leading terms. -/
theorem poly_coeffs_of_qExpJ_coeffs (A : AddSubgroup ℂ) (P : ℂ[X])
    (hcoeff : HasCoeffsIn (qExpJ P) A) :
    PolynomialHasCoeffsIn P A := by
  suffices h : ∀ d : ℕ, ∀ Q : ℂ[X], Q.natDegree ≤ d →
      HasCoeffsIn (qExpJ Q) A → PolynomialHasCoeffsIn Q A from
    h P.natDegree P le_rfl hcoeff
  intro d
  induction d with
  | zero =>
    intro Q hd hqcoeff k
    by_cases hQ : Q = 0
    · subst hQ; simp only [Polynomial.coeff_zero]; exact A.zero_mem
    · have hnd : Q.natDegree = 0 := Nat.eq_zero_of_le_zero hd
      by_cases hk : k = 0
      · subst hk
        have hlc := qExpJ_leadingCoeff Q hQ
        rw [hnd, Int.ofNat_zero, neg_zero, leadingCoeff, hnd] at hlc
        rw [← hlc]; exact hqcoeff 0
      · rw [coeff_eq_zero_of_natDegree_lt (by omega)]; exact A.zero_mem
  | succ d ih =>
    intro Q hd hqcoeff k
    by_cases hQ : Q = 0
    · subst hQ; simp only [Polynomial.coeff_zero]; exact A.zero_mem
    ·
      have hlc_mem : Q.leadingCoeff ∈ A :=
        qExpJ_leadingCoeff Q hQ ▸ hqcoeff _

      have hel_deg : Q.eraseLead.natDegree ≤ d := by
        rcases eraseLead_natDegree_lt_or_eraseLead_eq_zero Q with h | h
        · omega
        · rw [h, natDegree_zero]; omega

      have hel_coeff : HasCoeffsIn (qExpJ Q.eraseLead) A := by
        intro n
        rw [← self_sub_C_mul_X_pow, qExpJ_sub]
        apply A.sub_mem (hqcoeff n)
        obtain ⟨m, hm⟩ := qExpJ_monomial_coeffs Q.leadingCoeff Q.natDegree n
        rw [hm, ← zsmul_eq_mul]
        exact A.zsmul_mem hlc_mem m

      have hel_poly : PolynomialHasCoeffsIn Q.eraseLead A :=
        ih Q.eraseLead hel_deg hel_coeff

      have hdecomp : Q.coeff k = Q.eraseLead.coeff k +
          if k = Q.natDegree then Q.leadingCoeff else 0 := by
        rw [eraseLead_coeff]
        split_ifs with h <;> simp only [zero_add, add_zero, leadingCoeff]
        rw [h]
      rw [hdecomp]
      apply A.add_mem (hel_poly k)
      split_ifs
      · exact hlc_mem
      · exact A.zero_mem

/-- Lemma 19.18 (Hasse `q`-expansion principle): if a holomorphic modular function
`f` for `Γ(1)` has `q`-expansion coefficients in an additive subgroup `A ⊆ ℂ`, then
`f(τ) = P(j(τ))` for some polynomial `P ∈ A[X]`. -/
theorem hasse_q_expansion_principle
    (f : ℍ → ℂ) (A : AddSubgroup ℂ)
    (hmod : IsModularFunction f ⊤)
    (hhol : ModularFunction.IsHolomorphicOnH f)
    (hqcoeff : HasQExpCoeffsIn f A) :
    ∃ P : ℂ[X], PolynomialHasCoeffsIn P A ∧ ∀ τ : ℍ, f τ = P.eval (jFunction τ) := by

  obtain ⟨P, hP⟩ := holomorphic_modular_is_polynomial_in_j f hmod hhol
  refine ⟨P, ?_, hP⟩

  have hq : HasCoeffsIn (qExpJ P) A := by
    intro n
    have : qExpansion f = qExpansion (fun τ => P.eval (jFunction τ)) := by
      congr 1; ext τ; exact hP τ
    rw [qExpansion_eq_qExpJ] at this
    rw [← this]
    exact hqcoeff n

  exact poly_coeffs_of_qExpJ_coeffs A P hq

end ModularFunctionField

namespace ModularPolynomial

open ModularFunctionField

/-- Scaling of the upper half-plane `τ ↦ N τ` (the level-`N` version inside the
`ModularPolynomial` namespace). -/
def scaleUHP (N : ℕ) (hN : 0 < N) (τ : ℍ) : ℍ :=
  ⟨(N : ℂ) * (τ : ℂ), by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, UpperHalfPlane.coe_im,
      UpperHalfPlane.coe_re, zero_mul, add_zero]
    exact mul_pos (Nat.cast_pos.mpr hN) τ.im_pos⟩

/-- The translate-and-scale map `τ ↦ (τ + k)/N`, used to describe the `Γ₀(N)`-orbit
representatives appearing in Lemma 19.16 and the conjugates of `j_N`. -/
def translateScaleUHP (N : ℕ) (hN : 0 < N) (k : ℤ) (τ : ℍ) : ℍ :=
  ⟨((τ : ℂ) + (k : ℂ)) / (N : ℂ), by
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
    have hNc : ((N : ℂ) : ℂ) = ((N : ℝ) : ℂ) := by push_cast; ring
    rw [hNc, Complex.div_ofReal]
    show 0 < _ / _
    have him : (↑τ + ↑k : ℂ).im = τ.im := by
      simp [Complex.add_im, Complex.intCast_im]
    rw [him]
    exact div_pos τ.im_pos hN'⟩

/-- `j_N(τ) := j(N τ)`, the level-`N` `j`-function, here defined inside the
`ModularPolynomial` namespace. -/
def jFunc_N (N : ℕ) (hN : 0 < N) (τ : ℍ) : ℂ :=
  ModularFunctionField.jFunction (scaleUHP N hN τ)

/-- The conjugate `j_N`-value `j((τ + k)/N)`; these conjugates are the roots of
`Φ_N(j(τ), Y)` for `N` prime. -/
def jFunc_N_conjugate (N : ℕ) (hN : 0 < N) (k : ℤ) (τ : ℍ) : ℂ :=
  ModularFunctionField.jFunction (translateScaleUHP N hN k τ)

/-- The modular polynomial `Φ_N` viewed with complex coefficients, before checking
integrality (used to bootstrap Theorem 19.17). -/
noncomputable def PhiComplex (N : ℕ) : MvPolynomial (Fin 2) ℂ := by sorry

/-- The polynomial `Φ_N^ℂ(j(τ), j_N(τ))` vanishes identically on `ℍ`: this is the
defining property of `Φ_N` as a minimal polynomial of `j_N` over `ℂ(j)`. -/
theorem phiComplex_vanishes_at_jN (N : ℕ) (hN : 0 < N) (τ : ℍ) :
    MvPolynomial.eval (![ModularFunctionField.jFunction τ, jFunc_N N hN τ]) (PhiComplex N) = 0 := by sorry

/-- For prime `N`, each conjugate `j_N`-value also satisfies `Φ_N^ℂ(j(τ), ·) = 0`,
exhibiting the `N + 1` roots of the modular polynomial. -/
theorem phiComplex_root_conjugate (N : ℕ) (hN : Nat.Prime N) (k : Fin N) (τ : ℍ) :
    MvPolynomial.eval (![ModularFunctionField.jFunction τ, jFunc_N_conjugate N hN.pos (k : ℤ) τ])
      (PhiComplex N) = 0 := by sorry

/-- The integer modular polynomial `Phi N`, mapped to `ℂ`, recovers the complex
modular polynomial `PhiComplex N`. -/
theorem phi_map_eq_phiComplex (N : ℕ) (hN : 0 < N) :
    MvPolynomial.map (Int.castRingHom ℂ) (Phi N) = PhiComplex N := by sorry

/-- Theorem 19.17: `Φ_N` has integer coefficients, i.e. `Φ_N ∈ ℤ[X, Y]`. The witness
is `Phi N`, which maps via integers to `PhiComplex N`. -/
theorem phi_has_integer_coefficients (N : ℕ) (hN : 0 < N) :
    ∃ P : MvPolynomial (Fin 2) ℤ,
      MvPolynomial.map (Int.castRingHom ℂ) P = PhiComplex N :=
  ⟨Phi N, phi_map_eq_phiComplex N hN⟩

end ModularPolynomial

section Lemma19_16

open ModularGroup

/-- Matrix-entry computation: `S · T^k = !![0, -1; 1, k]` in `SL₂(ℤ)`. -/
lemma coe_S_mul_T_zpow (k : ℤ) :
    ((S * T ^ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, k] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [coe_S, coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two]

/-- Matrix-entry computation: `S · T^m · S⁻¹ = !![1, 0; -m, 1]` in `SL₂(ℤ)`. -/
lemma coe_S_T_zpow_S_inv (m : ℤ) :
    ((S * T ^ m * S⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -m, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [coe_S, coe_T_zpow, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

/-- Auxiliary algebraic identity used to factor a general matrix `!![a, b; c, d]` as a
product of a `Γ₀(N)`-matrix with `S · T^k`. -/
lemma product_matrix_eq (a b c d k : ℤ) :
    !![(k * a - b : ℤ), a; (k * c - d : ℤ), c] *
    (!![(0 : ℤ), -1; 1, k] : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- For prime `N`, every `γ ∈ SL₂(ℤ)` lies in `Γ₀(N)` or in one of the `N` right
cosets `Γ₀(N) · S · T^k` for `0 ≤ k < N` (the "cover" half of Lemma 19.16). -/
theorem gamma0_right_coset_cover (N : ℕ) (hN : Nat.Prime N) (γ : SL(2, ℤ)) :
    γ ∈ CongruenceSubgroup.Gamma0 N ∨
    ∃ (k : ℕ) (_ : k < N) (γ₀ : SL(2, ℤ)),
      γ₀ ∈ CongruenceSubgroup.Gamma0 N ∧ γ = γ₀ * (S * T ^ (k : ℤ)) := by
  haveI : Fact (Nat.Prime N) := ⟨hN⟩
  haveI : NeZero N := ⟨hN.ne_zero⟩
  set c := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0
  set d := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1
  set a := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0
  set b := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1
  have hdet : a * d - b * c = 1 := by
    have := γ.det_coe; rw [Matrix.det_fin_two] at this; exact this
  by_cases hc : (↑c : ZMod N) = 0
  · left; rwa [CongruenceSubgroup.Gamma0_mem]
  · right
    set k := ZMod.val ((↑d : ZMod N) * (↑c : ZMod N)⁻¹)
    have hk_lt : k < N := ZMod.val_lt _
    have hkc : (↑k : ZMod N) * (↑c : ZMod N) = (↑d : ZMod N) := by
      show (↑(ZMod.val ((↑d : ZMod N) * (↑c : ZMod N)⁻¹)) : ZMod N) * _ = _
      rw [ZMod.natCast_val, ZMod.cast_id']
      show (↑d : ZMod N) * (↑c : ZMod N)⁻¹ * (↑c : ZMod N) = (↑d : ZMod N)
      rw [mul_assoc, inv_mul_cancel₀ hc, mul_one]
    have hkcd : (↑((↑k : ℤ) * c - d) : ZMod N) = 0 := by
      push_cast; exact sub_eq_zero.mpr hkc
    have hdet₀ : ((↑k : ℤ) * a - b) * c - a * ((↑k : ℤ) * c - d) = 1 := by linarith
    set γ₀ : SL(2, ℤ) := ⟨!![(↑k : ℤ) * a - b, a; (↑k : ℤ) * c - d, c],
      by rw [Matrix.det_fin_two]; simpa using hdet₀⟩
    refine ⟨k, hk_lt, γ₀, ?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma0_mem]; exact hkcd
    · apply Subtype.ext
      show (γ : Matrix (Fin 2) (Fin 2) ℤ) =
        (γ₀ : Matrix (Fin 2) (Fin 2) ℤ) *
        ((S * T ^ (↑k : ℤ) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      rw [coe_S_mul_T_zpow]
      have hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] := by
        ext i j; fin_cases i <;> fin_cases j <;> rfl
      rw [hγ, show (γ₀ : Matrix _ _ ℤ) =
        !![(↑k : ℤ) * a - b, a; (↑k : ℤ) * c - d, c] from rfl]
      exact (product_matrix_eq a b c d ↑k).symm

/-- Part of Lemma 19.16: the coset representative `S · T^k` itself never lies in
`Γ₀(N)` for prime `N`. -/
lemma S_mul_T_zpow_not_mem_gamma0 (N : ℕ) (hN : Nat.Prime N) (k : ℤ) :
    S * T ^ k ∉ CongruenceSubgroup.Gamma0 N := by
  haveI : Fact (Nat.Prime N) := ⟨hN⟩
  intro hmem; rw [CongruenceSubgroup.Gamma0_mem] at hmem
  have : ((S * T ^ k : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    rw [coe_S_mul_T_zpow]; simp
  rw [this] at hmem; simp at hmem

/-- The remaining part of Lemma 19.16: distinct coset representatives `S · T^k`,
`S · T^j` (with `j, k < N` and `j ≠ k`) give genuinely distinct cosets. -/
lemma gamma0_coset_distinct_neq (N : ℕ) (hN : Nat.Prime N)
    (j k : ℕ) (hj : j < N) (hk : k < N) (hjk : j ≠ k) :
    (S * T ^ (k : ℤ)) * (S * T ^ (j : ℤ))⁻¹ ∉ CongruenceSubgroup.Gamma0 N := by
  haveI : Fact (Nat.Prime N) := ⟨hN⟩
  haveI : NeZero N := ⟨hN.ne_zero⟩
  rw [show (S * T ^ (k : ℤ)) * (S * T ^ (j : ℤ))⁻¹ =
    S * T ^ ((k : ℤ) - j) * S⁻¹ from by group]
  intro hmem; rw [CongruenceSubgroup.Gamma0_mem] at hmem
  have : ((S * T ^ ((k : ℤ) - j) * S⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 =
      -((k : ℤ) - j) := by rw [coe_S_T_zpow_S_inv]; simp
  rw [this] at hmem
  simp only [Int.cast_neg, neg_eq_zero, Int.cast_sub, Int.cast_natCast] at hmem
  exact hjk (by
    have := congr_arg ZMod.val (sub_eq_zero.mp hmem)
    rw [ZMod.val_natCast_of_lt hk, ZMod.val_natCast_of_lt hj] at this
    omega)

/-- Lemma 19.16: for prime `N`, the right cosets of `Γ₀(N)` in `Γ(1)` are exactly
`{Γ₀(N)} ∪ {Γ₀(N) · S · T^k : 0 ≤ k < N}`. This is packaged as three conjuncts:
covering, non-membership of representatives, and pairwise distinctness. -/
theorem lemma_19_16 (N : ℕ) (hN : Nat.Prime N) :

    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N ∨
      ∃ (k : ℕ) (_ : k < N) (γ₀ : SL(2, ℤ)),
        γ₀ ∈ CongruenceSubgroup.Gamma0 N ∧ γ = γ₀ * (S * T ^ (k : ℤ))) ∧

    (∀ k : ℤ, S * T ^ k ∉ CongruenceSubgroup.Gamma0 N) ∧

    (∀ j k : ℕ, j < N → k < N → j ≠ k →
      (S * T ^ (k : ℤ)) * (S * T ^ (j : ℤ))⁻¹ ∉ CongruenceSubgroup.Gamma0 N) :=
  ⟨gamma0_right_coset_cover N hN,
   S_mul_T_zpow_not_mem_gamma0 N hN,
   gamma0_coset_distinct_neq N hN⟩

end Lemma19_16

namespace ModularPolynomial

/-- Theorem 19.14 (restated): the degree of `Φ_N` in `Y` equals the Dedekind `ψ`
function, which is the index `[Γ(1) : Γ₀(N)]`. -/
theorem theorem_19_14 (N : ℕ) (hN : 0 < N) :
    degreeOf (1 : Fin 2) (Phi N) = dedekindPsi N :=
  phi_degreeOf_Y N hN

/-- `E` has a cyclic endomorphism of degree `N` (Definition 19.15 / Section 20.1):
a cyclic `N`-isogeny from `E` to itself. -/
def HasCyclicEndomorphism (F : Type*) [Field F] (N : ℕ) (j₀ : F) : Prop :=
  HasCyclicNIsogeny F N j₀ j₀

/-- The diagonal of Theorem 20.4: `Φ_N(j₀, j₀) = 0` iff the elliptic curve with
`j`-invariant `j₀` admits a cyclic endomorphism of degree `N`. -/
theorem eval_diag_eq_zero_iff {F : Type*} [Field F]
    (N : ℕ) (hN : 1 < N) (hchar : ¬(ringChar F ∣ N)) (j₀ : F) :
    eval N j₀ j₀ = 0 ↔ HasCyclicEndomorphism F N j₀ :=
  eval_eq_zero_iff N hN hchar j₀ j₀

/-- The diagonal evaluation `Φ_N(j₀, j₀)` agrees with evaluating the univariate
diagonal polynomial `diagPhi N` at `j₀`. -/
theorem eval_diag_eq_diagPhi_eval {R : Type*} [CommRing R] (N : ℕ) (j₀ : R) :
    eval N j₀ j₀ = Polynomial.eval₂ (Int.castRingHom R) j₀ (diagPhi N) := by
  unfold eval diagPhi
  symm
  have key : ((Polynomial.eval₂RingHom (Int.castRingHom R) j₀).comp
    (MvPolynomial.aeval (fun _ : Fin 2 => (Polynomial.X : Polynomial ℤ))).toRingHom) =
    MvPolynomial.eval₂Hom (Int.castRingHom R) (![j₀, j₀]) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [Polynomial.eval₂RingHom]
    · intro i; simp [Polynomial.eval₂RingHom]
      fin_cases i <;> simp
  exact DFunLike.congr_fun key (Phi N)

end ModularPolynomial

/-- A Laurent series `f : LaurentSeries ℂ` has integer coefficients: every
`f.coeff n` is in the image of `ℤ → ℂ`. -/
def HasIntCoeffs (f : LaurentSeries ℂ) : Prop :=
  ∀ n : ℤ, ∃ m : ℤ, f.coeff n = (m : ℂ)


/-- Corollary 19.6 (integrality part): the `q`-expansion of `j(τ)` has all integer
coefficients. -/
theorem corollary_19_6_int_coeffs :
  HasIntCoeffs (ModularFunctionField.qExpansion ModularFunctionField.jFunction) := by sorry

/-- Corollary 19.6 (leading-term): the `q⁻¹`-coefficient of `j(τ)` is `1`. -/
theorem corollary_19_6_leading :
  (ModularFunctionField.qExpansion ModularFunctionField.jFunction).coeff (-1 : ℤ) = (1 : ℂ) := by sorry

/-- Corollary 19.6 (constant term): the `q⁰`-coefficient of `j(τ)` is `744`. -/
theorem corollary_19_6_constant :
  (ModularFunctionField.qExpansion ModularFunctionField.jFunction).coeff (0 : ℤ) = (744 : ℂ) := by sorry

/-- Corollary 19.6 (order at the cusp): all coefficients of `j(τ)` below `q⁻¹`
vanish, i.e. `j` has a simple pole of residue `1` at `i∞`. -/
theorem corollary_19_6_order :
  ∀ n : ℤ, n < -1 → (ModularFunctionField.qExpansion ModularFunctionField.jFunction).coeff n = 0 := by sorry

/-- Corollary 19.6: with `q = e^{2πiτ}` we have
`j(τ) = 1/q + 744 + ∑_{n ≥ 1} aₙ qⁿ` with `aₙ ∈ ℤ`. -/
theorem corollary_19_6 :
    let f := ModularFunctionField.qExpansion ModularFunctionField.jFunction
    (f.coeff (-1 : ℤ) = (1 : ℂ)) ∧
    (f.coeff (0 : ℤ) = (744 : ℂ)) ∧
    (∀ n : ℤ, ∃ m : ℤ, f.coeff n = (m : ℂ)) ∧
    (∀ n : ℤ, n < -1 → f.coeff n = 0) :=
  ⟨corollary_19_6_leading, corollary_19_6_constant,
   corollary_19_6_int_coeffs, corollary_19_6_order⟩

end
