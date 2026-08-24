/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.EllipticCurves.code.PointCounting
import Atlas.EllipticCurves.code.OrdinarySupersingular
import Atlas.EllipticCurves.code.HilbertClassPolynomial
import Atlas.EllipticCurves.code.CMTorsor

namespace Elliptic_Curves

/-- An integer `D` is the discriminant of an imaginary quadratic order if it
is negative and congruent to `0` or `1` modulo `4`. -/
def IsImagQuadDiscriminant (D : ℤ) : Prop :=
  D < 0 ∧ (D % 4 = 0 ∨ D % 4 = 1)

/-- The ideal class group of the imaginary quadratic order of discriminant `D`,
abstractly defined as a type (concrete construction left unspecified). -/
noncomputable def IdealClassGroup' (D : ℤ) (_ : IsImagQuadDiscriminant D) : Type := by sorry

/-- The ideal class group `IdealClassGroup' D hD` is a commutative group. -/
noncomputable instance IdealClassGroup'.instCommGroup (D : ℤ) (hD : IsImagQuadDiscriminant D) :
    CommGroup (IdealClassGroup' D hD) := by sorry

attribute [instance] IdealClassGroup'.instCommGroup

/-- The ideal class group `IdealClassGroup' D hD` is finite (so admits a
`Fintype` structure), reflecting the classical finiteness of class number. -/
noncomputable instance IdealClassGroup'.instFintype (D : ℤ) (hD : IsImagQuadDiscriminant D) :
    Fintype (IdealClassGroup' D hD) := by sorry

attribute [instance] IdealClassGroup'.instFintype

/-- The class number `h(D)` of the imaginary quadratic order of discriminant
`D`, defined as the cardinality of its ideal class group. -/
noncomputable def classNumber (D : ℤ) (hD : IsImagQuadDiscriminant D) : ℕ :=
  Fintype.card (IdealClassGroup' D hD)

/-- The class number of an imaginary quadratic discriminant is positive. -/
theorem classNumber_pos (D : ℤ) (hD : IsImagQuadDiscriminant D) : 0 < classNumber D hD := by
  unfold classNumber
  haveI : Nonempty (IdealClassGroup' D hD) := ⟨1⟩
  exact Fintype.card_pos

/-- A bundle of data witnessing the existence of the ring class field of
discriminant `D`: the imaginary quadratic field `K = ℚ(√D)`, an abelian
extension `K_D / K` whose degree equals the class number, and the requisite
algebra/number field/Galois structures. -/
structure RingClassField (D : ℤ) (hD : IsImagQuadDiscriminant D) where
  K : Type*
  K_D : Type*
  [instFieldK : Field K]
  [instFieldKD : Field K_D]
  [instAlgebraQK : Algebra ℚ K]
  [instNumberFieldK : NumberField K]
  [instAlgebraKKD : Algebra K K_D]
  [instAlgebraQKD : Algebra ℚ K_D]
  [instIsScalarTower : IsScalarTower ℚ K K_D]
  [instNumberFieldKD : NumberField K_D]
  [instFiniteDimKKD : FiniteDimensional K K_D]
  [instIsGalois : IsGalois K K_D]
  finrankK : Module.finrank ℚ K = 2
  degree_eq_classNumber : Module.finrank K K_D = classNumber D hD
  galoisGroupComm : ∀ (σ τ : K_D ≃ₐ[K] K_D), σ.trans τ = τ.trans σ

attribute [instance] RingClassField.instFieldK RingClassField.instFieldKD
  RingClassField.instAlgebraQK RingClassField.instNumberFieldK
  RingClassField.instAlgebraKKD RingClassField.instAlgebraQKD
  RingClassField.instIsScalarTower RingClassField.instNumberFieldKD
  RingClassField.instFiniteDimKKD RingClassField.instIsGalois

/-- The ring class field of an imaginary quadratic discriminant exists. -/
theorem RingClassField.nonempty (D : ℤ) (hD : IsImagQuadDiscriminant D) :
    Nonempty (RingClassField D hD) := by sorry

/-- The Cornacchia-type norm equation `4p = t^2 - v^2 D` with `t, v` integers,
underlying Theorem 21.5(iv). -/
def NormEquation (D : ℤ) (p : ℕ) (t v : ℤ) : Prop :=
  4 * (p : ℤ) = t ^ 2 - v ^ 2 * D

/-- The prime `p` satisfies the Cornacchia norm equation for discriminant `D`
if there exist integers `t, v` with `4p = t^2 - v^2 D` and `p ∤ t`. -/
def SatisfiesNormEquation (D : ℤ) (p : ℕ) : Prop :=
  ∃ t v : ℤ, NormEquation D p t v ∧ ¬((p : ℤ) ∣ t)

/-- The Hilbert class polynomial `H_D(X)` of discriminant `D` realized over
`ℤ` (`1` outside the imaginary quadratic discriminant range). -/
noncomputable def hilbertClassPolynomialZ (D : ℤ) : Polynomial ℤ := by
  classical
  exact if h : _root_.IsImaginaryQuadraticDiscriminant D then
    ((Polynomial.mem_lifts _).mp (_root_.hilbertClassPoly_int_coeffs D h)).choose
  else 1

/-- `p` is the norm of a principal ideal in the order of discriminant `D` iff
there exist integers `t, v` with `4p = t^2 - v^2 D` and `2 ∣ t - vD`. This is
condition (i) in Theorem 21.5 of Sutherland. -/
def IsNormOfPrincipalIdeal (D : ℤ) (p : ℕ) : Prop :=
  ∃ t v : ℤ, 4 * (p : ℤ) = t ^ 2 - v ^ 2 * D ∧ 2 ∣ (t - v * D)

/-- Condition (ii) of Theorem 21.5: the Legendre symbol `(D/p) = 1` and the
Hilbert class polynomial `H_D` splits into linear factors over `𝔽_p`. -/
def LegendreOneAndHDSplits (D : ℤ) (p : ℕ) : Prop :=
  jacobiSym D p = 1 ∧ ((hilbertClassPolynomialZ D).map (Int.castRingHom (ZMod p))).Splits

/-- Condition (iii) of Theorem 21.5: `p` splits completely in the ring class
field of discriminant `D`, expressed as: there is a number field `L` over
which `H_D` splits and all maximal ideals above `p` have absolute norm `p`. -/
def SplitsCompletelyInRCF (D : ℤ) (p : ℕ) : Prop :=
  ∃ (L : Type) (hF : Field L) (hNF : @NumberField L hF),
    letI := hF
    letI := hNF

    ((hilbertClassPolynomialZ D).map (algebraMap ℤ L)).Splits ∧

    (∀ (P : Ideal (NumberField.RingOfIntegers L)),
      P.IsMaximal →
      (p : NumberField.RingOfIntegers L) ∈ P →
      Ideal.absNorm P = p)


/-- Theorem 21.5, equivalence (i) ↔ (ii) of Sutherland: for `p ∤ D` odd prime,
`p` is the norm of a principal `𝒪`-ideal iff `(D/p) = 1` and `H_D(X)` splits
over `𝔽_p`. -/
theorem theorem_21_5_i_iff_ii (D : ℤ) (p : ℕ)
    (hD : IsImagQuadDiscriminant D)
    (hp : Nat.Prime p)
    (hp_odd : p ≠ 2)
    (hp_ndvd : ¬((p : ℤ) ∣ D)) :
    IsNormOfPrincipalIdeal D p ↔ LegendreOneAndHDSplits D p := by sorry

/-- Theorem 21.5, equivalence (ii) ↔ (iii) of Sutherland: `(D/p) = 1` with
`H_D` splitting over `𝔽_p` iff `p` splits completely in the ring class field. -/
theorem theorem_21_5_ii_iff_iii (D : ℤ) (p : ℕ)
    (hD : IsImagQuadDiscriminant D)
    (hp : Nat.Prime p)
    (hp_odd : p ≠ 2)
    (hp_ndvd : ¬((p : ℤ) ∣ D)) :
    LegendreOneAndHDSplits D p ↔ SplitsCompletelyInRCF D p := by sorry

/-- Theorem 21.5, equivalence (iii) ↔ (iv) of Sutherland: complete splitting
of `p` in the ring class field iff `4p = t^2 - v^2 D` for some `t, v` with
`p ∤ t`. -/
theorem theorem_21_5_iii_iff_iv (D : ℤ) (p : ℕ)
    (hD : IsImagQuadDiscriminant D)
    (hp : Nat.Prime p)
    (hp_odd : p ≠ 2)
    (hp_ndvd : ¬((p : ℤ) ∣ D)) :
    SplitsCompletelyInRCF D p ↔ SatisfiesNormEquation D p := by sorry

/-- Theorem 21.5, equivalence (iv) ↔ (i) of Sutherland: `4p = t^2 - v^2 D`
with `p ∤ t` iff `p` is the norm of a principal `𝒪`-ideal. -/
theorem theorem_21_5_iv_iff_i (D : ℤ) (p : ℕ)
    (hD : IsImagQuadDiscriminant D)
    (hp : Nat.Prime p)
    (hp_odd : p ≠ 2)
    (hp_ndvd : ¬((p : ℤ) ∣ D)) :
    SatisfiesNormEquation D p ↔ IsNormOfPrincipalIdeal D p := by sorry

/-- Theorem 21.5 (Sutherland): for an imaginary quadratic discriminant `D` and
an odd prime `p` with `p ∤ D` unramified in the ring class field `L`, the
four conditions (i)-(iv) are pairwise equivalent. -/
theorem theorem_21_5 (D : ℤ) (p : ℕ)
    (hD : IsImagQuadDiscriminant D)
    (hp : Nat.Prime p)
    (hp_odd : p ≠ 2)
    (hp_ndvd : ¬((p : ℤ) ∣ D)) :
    (IsNormOfPrincipalIdeal D p ↔ LegendreOneAndHDSplits D p) ∧
    (LegendreOneAndHDSplits D p ↔ SplitsCompletelyInRCF D p) ∧
    (SplitsCompletelyInRCF D p ↔ SatisfiesNormEquation D p) ∧
    (SatisfiesNormEquation D p ↔ IsNormOfPrincipalIdeal D p) :=
  ⟨theorem_21_5_i_iff_ii D p hD hp hp_odd hp_ndvd,
   theorem_21_5_ii_iff_iii D p hD hp hp_odd hp_ndvd,
   theorem_21_5_iii_iff_iv D p hD hp hp_odd hp_ndvd,
   theorem_21_5_iv_iff_i D p hD hp hp_odd hp_ndvd⟩

/-- Definitional unfolding of `NormEquation D p t v`. -/
@[simp]
theorem normEquation_iff (D : ℤ) (p : ℕ) (t v : ℤ) :
    NormEquation D p t v ↔ 4 * (p : ℤ) = t ^ 2 - v ^ 2 * D :=
  Iff.rfl

/-- The norm equation is symmetric under sign change of `t, v`. -/
theorem normEquation_neg (D : ℤ) (p : ℕ) (t v : ℤ) :
    NormEquation D p t v ↔ NormEquation D p (-t) (-v) := by
  simp only [NormEquation, neg_sq]

/-- If `D < 0` and `NormEquation D p t v` holds, then `t^2 ≤ 4p`. -/
theorem normEquation_sq_le {D : ℤ} {p : ℕ} {t v : ℤ}
    (hD : D < 0) (hne : NormEquation D p t v) :
    t ^ 2 ≤ 4 * (p : ℤ) := by
  unfold NormEquation at hne
  nlinarith [sq_nonneg v]

/-- Definition 21.4 (Sutherland): the Kronecker symbol `(D/p)`. For odd primes
it agrees with the Legendre symbol; for `p = 2` it is `0` if `2 ∣ D`, `+1`
if `D ≡ ±1 mod 8`, and `-1` if `D ≡ ±3 mod 8`. -/
noncomputable def kroneckerSymbol (p : ℕ) [hp : Fact (Nat.Prime p)] (D : ℤ) : ℤ :=
  if p = 2 then
    if D % 2 = 0 then 0
    else if D % 8 = 1 ∨ D % 8 = 7 then 1
    else -1
  else
    legendreSym p D

/-- The Kronecker symbol `(D/p)` always takes values in `{-1, 0, 1}`. -/
theorem kroneckerSymbol_values {p : ℕ} [hp : Fact (Nat.Prime p)] (D : ℤ) :
    kroneckerSymbol p D = -1 ∨ kroneckerSymbol p D = 0 ∨ kroneckerSymbol p D = 1 := by
  unfold kroneckerSymbol
  split_ifs
  · right; left; rfl
  · right; right; rfl
  · left; rfl
  · have hq := quadraticChar_isQuadratic (ZMod p) (D : ZMod p)
    simp only [legendreSym]
    rcases hq with h | h | h
    · right; left; exact_mod_cast h
    · right; right; exact_mod_cast h
    · left; exact_mod_cast h

/-- For an odd prime, the Kronecker symbol coincides with the Legendre symbol. -/
theorem kroneckerSymbol_odd_prime {p : ℕ} [hp : Fact (Nat.Prime p)] (hodd : p ≠ 2) (D : ℤ) :
    kroneckerSymbol p D = legendreSym p D := by
  simp [kroneckerSymbol, hodd]

namespace Deuring

open Polynomial

/-- A "ring class field prime" for Theorem 21.12 (Deuring): a positive integer
`q > 1` that is coprime to the discriminant `D`, intended to represent a
prime power norm of a prime in the ring class field. -/
structure RingClassFieldPrime (D : ℤ) where
  q : ℕ
  q_pos : 1 < q
  coprime_q_D : Nat.Coprime q D.natAbs

/-- The Hilbert class polynomial of discriminant `D` viewed as a polynomial
over an arbitrary field `F`, obtained by base change from the integral form. -/
noncomputable def hilbertClassPolynomial (D : ℤ) (F : Type*) [Field F] : Polynomial F :=
  (Elliptic_Curves.hilbertClassPolynomialZ D).map (Int.castRingHom F)

/-- `Ell_𝒪(F)`: the set of `j`-invariants of elliptic curves over the finite
field `F` whose endomorphism ring is the order of discriminant `D`. -/
noncomputable def ellCMSet (D : ℤ) (F : Type*) [Field F] [Fintype F] : Set F := by sorry

/-- Theorem 21.12 (Deuring, Sutherland): for an imaginary quadratic order of
discriminant `D` with ring class field `L`, and `q` the norm of a prime ideal
of `𝒪_L` with `q ⊥ D`, the Hilbert class polynomial `H_D(X)` splits into
distinct linear factors over `𝔽_q`, with roots equal to `Ell_𝒪(𝔽_q)`. -/
theorem theorem_21_12
    (D : ℤ) (hD : IsImagQuadDiscriminant D)
    (𝔮 : RingClassFieldPrime D)
    (F : Type*) [Field F] [Fintype F]
    (hcard : Fintype.card F = 𝔮.q) :

    (hilbertClassPolynomial D F).Splits ∧
    (hilbertClassPolynomial D F).Separable ∧

    (∀ x : F, (hilbertClassPolynomial D F).IsRoot x ↔ x ∈ ellCMSet D F) := by sorry

end Deuring

end Elliptic_Curves

open NumberField

noncomputable section

namespace DeuringLifting

/-- `IsReductionOfCurve E E_star 𝔮 e` is the predicate stating that the curve
`E_star` over the number field `L` has good reduction modulo the prime `𝔮`
identifying with `E` via the ring isomorphism `e : F ≃+* 𝒪_L/𝔮`. -/
opaque IsReductionOfCurve
    {F : Type} [Field F] [DecidableEq F] [Fintype F]
    {L : Type} [Field L] [DecidableEq L] [NumberField L]
    (E : WeierstrassCurve.Affine F)
    (E_star : WeierstrassCurve.Affine L)
    (𝔮 : Ideal (𝓞 L)) [𝔮.IsMaximal]
    (e : F ≃+* (𝓞 L ⧸ 𝔮)) : Prop

/-- `IsReductionOfEndomorphism` states that the endomorphism `φ_star` of the
lift `E_star` reduces to the endomorphism `φ` of `E` modulo `𝔮`, given that
`E_star` is a good reduction lift of `E`. -/
opaque IsReductionOfEndomorphism
    {F : Type} [Field F] [DecidableEq F] [Fintype F]
    {L : Type} [Field L] [DecidableEq L] [NumberField L]
    (E : WeierstrassCurve.Affine F)
    (E_star : WeierstrassCurve.Affine L)
    (φ : AddMonoid.End E.Point)
    (φ_star : AddMonoid.End E_star.Point)
    (𝔮 : Ideal (𝓞 L)) [𝔮.IsMaximal]
    (e : F ≃+* (𝓞 L ⧸ 𝔮))
    (hcurve : IsReductionOfCurve E E_star 𝔮 e) : Prop

/-- Theorem 21.13 (Deuring lifting theorem, Sutherland): every nonzero
endomorphism `φ` of an elliptic curve `E/𝔽_q` lifts to a characteristic-zero
endomorphism `φ_star` of an elliptic curve `E_star` over a number field `L`
with good reduction at a prime `𝔮` of residue field `𝔽_q`. -/
theorem deuring_lifting_theorem
    {F : Type} [Field F] [DecidableEq F] [Fintype F]
    (E : WeierstrassCurve.Affine F)
    (φ : AddMonoid.End E.Point)
    (hφ : φ ≠ 0) :
    ∃ (L : Type) (_ : Field L) (_ : DecidableEq L) (_ : NumberField L)
      (E_star : WeierstrassCurve.Affine L)
      (φ_star : AddMonoid.End E_star.Point)
      (𝔮 : Ideal (𝓞 L)) (_ : 𝔮.IsMaximal)
      (e : F ≃+* (𝓞 L ⧸ 𝔮))
      (hcurve : IsReductionOfCurve E E_star 𝔮 e),
      IsReductionOfEndomorphism E E_star φ φ_star 𝔮 e hcurve := by sorry

end DeuringLifting

namespace RingClassField

/-- Predicate (in `Prop`) form of "`D` is the discriminant of an imaginary
quadratic order": `D < 0` and `D ≡ 0` or `1 mod 4`. -/
structure IsImagQuadDisc (D : ℤ) : Prop where
  neg : D < 0
  cong : D % 4 = 0 ∨ D % 4 = 1

/-- The imaginary quadratic field `K = ℚ(√D)`, abstractly defined as a type. -/
noncomputable def ImagQuadField (D : ℤ) : Type := by sorry

/-- The imaginary quadratic field `ImagQuadField D` has a `Field` structure. -/
noncomputable instance ImagQuadField.instField (D : ℤ) : Field (ImagQuadField D) := by sorry
attribute [instance] ImagQuadField.instField

/-- `ImagQuadField D` is a `ℚ`-algebra. -/
noncomputable instance ImagQuadField.instAlgebra (D : ℤ) : Algebra ℚ (ImagQuadField D) := by sorry
attribute [instance] ImagQuadField.instAlgebra

/-- For an imaginary quadratic discriminant `D`, `ImagQuadField D` is a number
field. -/
theorem ImagQuadField.instNumberField (D : ℤ) (hD : IsImagQuadDisc D) :
  NumberField (ImagQuadField D) := by sorry

/-- The imaginary quadratic field has degree `2` over `ℚ`. -/
theorem ImagQuadField.finrank_eq_two (D : ℤ) (hD : IsImagQuadDisc D) :
  Module.finrank ℚ (ImagQuadField D) = 2 := by sorry

/-- The order `𝒪 = ℤ[(D + √D)/2]` (or `ℤ[√D]`) of discriminant `D`, abstractly
defined as a type. -/
noncomputable def ImagQuadOrder (D : ℤ) : Type := by sorry

/-- The imaginary quadratic order is a commutative ring. -/
noncomputable instance ImagQuadOrder.instCommRing (D : ℤ) : CommRing (ImagQuadOrder D) := by sorry
attribute [instance] ImagQuadOrder.instCommRing

/-- The ideal class group `cl(𝒪)` of the order of discriminant `D`. -/
noncomputable def IdealClassGroup (D : ℤ) : Type := by sorry

/-- The ideal class group is a commutative group. -/
noncomputable instance IdealClassGroup.instCommGroup (D : ℤ) : CommGroup (IdealClassGroup D) := by sorry
attribute [instance] IdealClassGroup.instCommGroup

/-- For an imaginary quadratic discriminant `D`, the ideal class group is
finite. -/
noncomputable instance IdealClassGroup.instFintype (D : ℤ) (hD : IsImagQuadDisc D) :
  Fintype (IdealClassGroup D) := by sorry

/-- The class number `h(D) = #cl(𝒪)`. -/
def classNumber (D : ℤ) (hD : IsImagQuadDisc D) : ℕ :=
  @Fintype.card (IdealClassGroup D) (IdealClassGroup.instFintype D hD)

/-- The class number of an imaginary quadratic discriminant is positive. -/
theorem classNumber_pos (D : ℤ) (hD : IsImagQuadDisc D) : 0 < classNumber D hD := by
  unfold classNumber
  haveI : Nonempty (IdealClassGroup D) := ⟨1⟩
  exact @Fintype.card_pos _ (IdealClassGroup.instFintype D hD) ⟨1⟩

/-- The Hilbert class polynomial `H_D(X)` viewed as a polynomial over the
imaginary quadratic field `K = ℚ(√D)`. -/
noncomputable def hilbertClassPoly (D : ℤ) : Polynomial (ImagQuadField D) := by sorry

/-- The Hilbert class polynomial is monic. -/
theorem hilbertClassPoly_monic (D : ℤ) (hD : IsImagQuadDisc D) :
  (hilbertClassPoly D).Monic := by sorry

/-- The Hilbert class polynomial has degree equal to the class number. -/
theorem hilbertClassPoly_natDegree (D : ℤ) (hD : IsImagQuadDisc D) :
  (hilbertClassPoly D).natDegree = classNumber D hD := by sorry

/-- The Hilbert class polynomial is nonzero. -/
theorem hilbertClassPoly_ne_zero (D : ℤ) (hD : IsImagQuadDisc D) :
  hilbertClassPoly D ≠ 0 := by sorry

/-- The Hilbert class polynomial is in the image of `ℤ`-coefficient
polynomials: it has integer coefficients. -/
theorem hilbertClassPoly_lifts_int (D : ℤ) (hD : IsImagQuadDisc D) :
    hilbertClassPoly D ∈ Polynomial.lifts (algebraMap ℤ (ImagQuadField D)) := by sorry

/-- Definition 21.3 (Sutherland): the ring class field of discriminant `D`,
defined as the splitting field of the Hilbert class polynomial `H_D` over
`K = ℚ(√D)`. -/
abbrev RingClassFieldType (D : ℤ) : Type :=
  Polynomial.SplittingField (hilbertClassPoly D)

/-- The ring class field is a field. -/
instance (D : ℤ) : Field (RingClassFieldType D) :=
  Polynomial.SplittingField.instField _

/-- The ring class field is an algebra over the imaginary quadratic base
field. -/
instance (D : ℤ) : Algebra (ImagQuadField D) (RingClassFieldType D) :=
  Polynomial.SplittingField.instAlgebra _

/-- The ring class field is Galois over the imaginary quadratic base field. -/
theorem ringClassField_isGalois (D : ℤ) (hD : IsImagQuadDisc D) :
  IsGalois (ImagQuadField D) (RingClassFieldType D) := by sorry

/-- `Ell_𝒪`: the set of `j`-invariants in the ring class field corresponding
to elliptic curves with CM by the order of discriminant `D`. -/
noncomputable def EllO (D : ℤ) : Set (RingClassFieldType D) := by sorry

/-- Every `j ∈ Ell_𝒪(D)` is a root of the Hilbert class polynomial. -/
theorem EllO_subset_roots (D : ℤ) (j : RingClassFieldType D) (hj : j ∈ EllO D) :
  Polynomial.aeval j (hilbertClassPoly D) = 0 := by sorry

/-- Every root of the Hilbert class polynomial in the ring class field belongs
to `Ell_𝒪(D)`. -/
theorem roots_subset_EllO (D : ℤ) (j : RingClassFieldType D)
    (hj : j ∈ (hilbertClassPoly D).rootSet (RingClassFieldType D)) : j ∈ EllO D := by sorry

/-- The set `Ell_𝒪(D)` is nonempty for an imaginary quadratic discriminant. -/
theorem EllO_nonempty (D : ℤ) (hD : IsImagQuadDisc D) : (EllO D).Nonempty := by sorry

/-- The action of the ideal class group on `Ell_𝒪(D)`: given a class
`α ∈ cl(𝒪)` and `j ∈ Ell_𝒪(D)`, we produce `α · j ∈ Ell_𝒪(D)`. -/
noncomputable def cmAction (D : ℤ) : IdealClassGroup D → (EllO D) → (EllO D) := by sorry

/-- The ideal class group action on `Ell_𝒪(D)` is transitive. -/
theorem cmAction_transitive (D : ℤ) (hD : IsImagQuadDisc D)
    (j₁ j₂ : EllO D) : ∃ α : IdealClassGroup D, cmAction D α j₁ = j₂ := by sorry

/-- The ideal class group action on `Ell_𝒪(D)` is free: only the identity
class fixes a point. -/
theorem cmAction_free (D : ℤ) (hD : IsImagQuadDisc D)
    (α : IdealClassGroup D) (j : EllO D)
    (h : cmAction D α j = j) : α = 1 := by sorry

/-- The Galois action on the ring class field preserves the subset `Ell_𝒪(D)`. -/
theorem galAction_preserves_EllO (D : ℤ)
    (σ : RingClassFieldType D ≃ₐ[ImagQuadField D] RingClassFieldType D)
    (j : RingClassFieldType D) (hj : j ∈ EllO D) :
    σ j ∈ EllO D := by sorry

/-- Compatibility of the Galois action with the ideal class group action: if
`σ` sends `j₁` to `α₁ · j₁` and `j₂` to `α₂ · j₂`, then `α₁ = α₂`, i.e. `σ`
acts uniformly through a single ideal class. -/
theorem galAction_cmAction_compat (D : ℤ) (hD : IsImagQuadDisc D)
    (σ : RingClassFieldType D ≃ₐ[ImagQuadField D] RingClassFieldType D)
    (j₁ j₂ : EllO D)
    (α₁ : IdealClassGroup D) (hα₁ : cmAction D α₁ j₁ = ⟨σ j₁, galAction_preserves_EllO D σ j₁ j₁.2⟩)
    (α₂ : IdealClassGroup D) (hα₂ : cmAction D α₂ j₂ = ⟨σ j₂, galAction_preserves_EllO D σ j₂ j₂.2⟩) :
    α₁ = α₂ := by sorry

/-- Auxiliary construction: from a Galois automorphism `σ` and a base point
`j₀ ∈ Ell_𝒪(D)`, pick the ideal class taking `j₀` to `σ(j₀)`. -/
noncomputable def galToClassGroupAux (D : ℤ) (hD : IsImagQuadDisc D)
    (σ : RingClassFieldType D ≃ₐ[ImagQuadField D] RingClassFieldType D)
    (j₀ : EllO D) : IdealClassGroup D := by
  classical
  exact (cmAction_transitive D hD j₀
    ⟨σ j₀, galAction_preserves_EllO D σ j₀ j₀.2⟩).choose

/-- The group homomorphism `Gal(L/K) → cl(𝒪)` underlying Corollary 21.2. -/
noncomputable def galToClassGroupHom (D : ℤ) (hD : IsImagQuadDisc D) :
    (RingClassFieldType D ≃ₐ[ImagQuadField D] RingClassFieldType D) →* IdealClassGroup D := by sorry

/-- Characterizing property of `galToClassGroupHom`: it sends `σ` to the
ideal class `α` such that `α · j₀ = σ(j₀)`. -/
theorem galToClassGroupHom_spec (D : ℤ) (hD : IsImagQuadDisc D)
    (σ : RingClassFieldType D ≃ₐ[ImagQuadField D] RingClassFieldType D)
    (j₀ : EllO D) :
    cmAction D (galToClassGroupHom D hD σ) j₀ =
      ⟨σ j₀, galAction_preserves_EllO D σ j₀ j₀.2⟩ := by sorry

/-- The natural map `Gal(L/K) → cl(𝒪)` is injective. -/
theorem galToClassGroupHom_injective (D : ℤ) (hD : IsImagQuadDisc D) :
    Function.Injective (galToClassGroupHom D hD) := by
  intro σ τ h

  have agree_on_EllO : ∀ (j₀ : EllO D), σ (j₀ : RingClassFieldType D) =
      τ (j₀ : RingClassFieldType D) := by
    intro j₀
    have hσ := galToClassGroupHom_spec D hD σ j₀
    have hτ := galToClassGroupHom_spec D hD τ j₀
    rw [h] at hσ
    exact congrArg Subtype.val (hσ.symm.trans hτ)


  apply Polynomial.Gal.ext
  intro x hx

  exact agree_on_EllO ⟨x, roots_subset_EllO D x hx⟩

/-- The natural map `Gal(L/K) → cl(𝒪)` is surjective. -/
theorem galToClassGroupHom_surjective (D : ℤ) (hD : IsImagQuadDisc D) :
    Function.Surjective (galToClassGroupHom D hD) := by sorry

/-- The group isomorphism `Gal(L/K) ≃* cl(𝒪)` from Corollary 21.2,
constructed via the bijective hom `galToClassGroupHom`. -/
noncomputable def galToClassGroup_mulEquiv (D : ℤ) (hD : IsImagQuadDisc D) :
    (RingClassFieldType D ≃ₐ[ImagQuadField D] RingClassFieldType D) ≃*
      IdealClassGroup D :=
  MulEquiv.ofBijective (galToClassGroupHom D hD)
    ⟨galToClassGroupHom_injective D hD, galToClassGroupHom_surjective D hD⟩

/-- Corollary 21.2 (irreducibility part, Sutherland): the Hilbert class
polynomial `H_D(X)` is irreducible over `K = ℚ(√D)`. -/
theorem corollary_21_2_irreducible (D : ℤ) (hD : IsImagQuadDisc D) :
    Irreducible (hilbertClassPoly D) := by sorry

/-- Corollary 21.2 (degree part, Sutherland): the ring class field
`K(j(E))/K` has degree equal to the class number `h(D)`. -/
theorem corollary_21_2_degree (D : ℤ) (hD : IsImagQuadDisc D) :
    Module.finrank (ImagQuadField D) (RingClassFieldType D) = classNumber D hD := by
  letI := ringClassField_isGalois D hD
  letI := IdealClassGroup.instFintype D hD
  have h1 := IsGalois.card_aut_eq_finrank (ImagQuadField D) (RingClassFieldType D)
  have h2 := Nat.card_congr (galToClassGroup_mulEquiv D hD).toEquiv
  rw [← h1, h2]
  exact @Nat.card_eq_fintype_card _ (IdealClassGroup.instFintype D hD)

/-- Corollary 21.2 (Galois isomorphism part, Sutherland): the Galois group
`Gal(K(j(E))/K)` is isomorphic to the ideal class group `cl(𝒪)`. -/
noncomputable def corollary_21_2_galois_iso (D : ℤ) (hD : IsImagQuadDisc D) :
    (RingClassFieldType D ≃ₐ[ImagQuadField D] RingClassFieldType D) ≃*
      IdealClassGroup D :=
  galToClassGroup_mulEquiv D hD

end RingClassField

end

open Elliptic_Curves

namespace CMMethod

/-- Predicate saying that the elliptic curve `E/F` has prescribed
`j`-invariant `j₀ ∈ F`. -/
noncomputable def HasJInvariant {F : Type*} [Field F]
    (E : WeierstrassCurve.Affine F) (j₀ : F) : Prop := by sorry

/-- Corollary 21.9 (Sutherland): for an imaginary quadratic discriminant `D`,
an odd prime `p ∤ D` with `4p = t^2 - v^2 D` and `p ∤ t`, and an elliptic
curve `E/𝔽_p` whose `j`-invariant `j₀ ∉ {0, 1728}` is a root of `H_D(X)` mod
`p`, the trace of Frobenius of `E` equals `±t`. -/
theorem corollary_21_9
    (D : ℤ) (p : ℕ) (t v : ℤ)
    (hD : IsImagQuadDiscriminant D)
    (hp : Nat.Prime p)
    (hp_odd : p ≠ 2)
    (hp_ndvd : ¬((p : ℤ) ∣ D))
    (hne : NormEquation D p t v)
    (ht : ¬((p : ℤ) ∣ t))
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hcard : Fintype.card F = p)
    (E : WeierstrassCurve.Affine F)
    (j₀ : F) (hj₀_ne0 : j₀ ≠ 0) (hj₀_ne1728 : j₀ ≠ 1728)
    (hj₀_root : (Deuring.hilbertClassPolynomial D F).IsRoot j₀)
    (hj_E : HasJInvariant E j₀) :
    Hasse.traceFrobenius E = t ∨ Hasse.traceFrobenius E = -t := by sorry

/-- Companion to Corollary 21.9: under the same hypotheses, the Frobenius
trace of `E` is not divisible by `p` (equivalently, `E` is ordinary). -/
theorem corollary_21_9_trace_not_dvd
    (D : ℤ) (p : ℕ) (t v : ℤ)
    (hD : IsImagQuadDiscriminant D)
    (hp : Nat.Prime p)
    (hp_odd : p ≠ 2)
    (hp_ndvd : ¬((p : ℤ) ∣ D))
    (hne : NormEquation D p t v)
    (ht : ¬((p : ℤ) ∣ t))
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hcard : Fintype.card F = p)
    (E : WeierstrassCurve.Affine F)
    (j₀ : F) (hj₀_ne0 : j₀ ≠ 0) (hj₀_ne1728 : j₀ ≠ 1728)
    (hj₀_root : (Deuring.hilbertClassPolynomial D F).IsRoot j₀)
    (hj_E : HasJInvariant E j₀) :
    ¬((p : ℤ) ∣ Hasse.traceFrobenius E) := by
  have hfrob := corollary_21_9 D p t v hD hp hp_odd hp_ndvd hne ht F hcard E
    j₀ hj₀_ne0 hj₀_ne1728 hj₀_root hj_E
  rcases hfrob with h | h <;> rw [h]
  · exact ht
  · rwa [Int.dvd_neg]

/-- The output of the CM method: a curve over a finite field `F` together with
its Frobenius trace witnessing the relation `trace = ±t`. -/
structure CMOutput (F : Type*) [Field F] [Fintype F] [DecidableEq F] where
  curve : WeierstrassCurve.Affine F
  trace : ℤ
  frob_trace_eq : Hasse.traceFrobenius curve = trace ∨
                  Hasse.traceFrobenius curve = -trace

end CMMethod

namespace ProperIdealNormCount

open Elliptic_Curves

/-- The conductor `[𝒪_K : 𝒪]` of the order of discriminant `D` in its
maximal order, as a natural number. -/
noncomputable def conductor (D : ℤ) (_ : IsImagQuadDiscriminant D) : ℕ := by sorry

/-- The conductor of an imaginary quadratic order is positive. -/
theorem conductor_pos (D : ℤ) (hD : IsImagQuadDiscriminant D) : 0 < conductor D hD := by sorry

/-- The number of proper `𝒪`-ideals of norm `p`. -/
noncomputable def numProperIdealsOfNorm (D : ℤ) (p : ℕ) : ℕ := by sorry

/-- Corollary 21.7 (Sutherland), case `p ∣ conductor`: if the prime `p`
divides the conductor of the order `𝒪`, there are no proper `𝒪`-ideals of
norm `p`. -/
theorem corollary_21_7_conductor_divides
    (D : ℤ) (p : ℕ)
    (hD : IsImagQuadDiscriminant D)
    [hp : Fact (Nat.Prime p)]
    (hdvd : (p : ℤ) ∣ (conductor D hD : ℤ)) :
    numProperIdealsOfNorm D p = 0 := by sorry

/-- Corollary 21.7 (Sutherland), case `p` coprime to the conductor: when `p`
does not divide the conductor of `𝒪`, the number of proper `𝒪`-ideals of
norm `p` is `1 + (D/p)`. -/
theorem corollary_21_7_conductor_coprime
    (D : ℤ) (p : ℕ)
    (hD : IsImagQuadDiscriminant D)
    [hp : Fact (Nat.Prime p)]
    (hndvd : ¬((p : ℤ) ∣ (conductor D hD : ℤ))) :
    (numProperIdealsOfNorm D p : ℤ) = 1 + kroneckerSymbol p D := by sorry

end ProperIdealNormCount

namespace RingClassFieldRamification

open Elliptic_Curves

/-- Predicate: the rational prime `p` is unramified in the ring class field
of discriminant `D`. -/
noncomputable def IsUnramifiedInRCF (D : ℤ) (p : ℕ) : Prop := by sorry

/-- Corollary 21.8 (Sutherland): the ring class field of discriminant `D` is
unramified at every rational prime `p` that does not divide the conductor of
`𝒪`. -/
theorem corollary_21_8_conductor_coprime
    (D : ℤ) (p : ℕ)
    (hD : IsImagQuadDiscriminant D)
    (hp : Nat.Prime p)
    (hndvd : ¬((p : ℤ) ∣ (ProperIdealNormCount.conductor D hD : ℤ))) :
    IsUnramifiedInRCF D p := by sorry

/-- The conductor of an order in an imaginary quadratic field divides the
discriminant. -/
theorem conductor_dvd_disc
    (D : ℤ) (hD : IsImagQuadDiscriminant D) :
    (ProperIdealNormCount.conductor D hD : ℤ) ∣ D := by sorry

end RingClassFieldRamification

namespace ImagQuadPrimeSplitting

open Elliptic_Curves

/-- Roots in `ZMod p` of the minimal polynomial of `ω = (D + √D)/2` (or
`√D`) for the imaginary quadratic discriminant `D`. -/
noncomputable def rootsMinPolyMod (D : ℤ) (p : ℕ) [Fact (Nat.Prime p)] : Finset (ZMod p) :=
  if D % 4 = 1 then
    Finset.univ.filter (fun x : ZMod p => x ^ 2 - x + ((1 - D) / 4 : ℤ) = 0)
  else
    Finset.univ.filter (fun x : ZMod p => x ^ 2 + ((-D / 4 : ℤ) : ZMod p) = 0)

/-- The number of `𝒪_K`-ideals of norm `p`, counted by the roots of the
minimal polynomial of `ω` modulo `p`. -/
noncomputable def numIdealsOfNorm (D : ℤ) (p : ℕ) [Fact (Nat.Prime p)] : ℤ :=
  (rootsMinPolyMod D p).card

/-- In `ZMod 2`, for any constant `c`, the equation `x^2 + c = 0` has exactly
one solution. -/
lemma card_filter_sq_add_eq_zero_ZMod2 (c : ZMod 2) :
    (Finset.univ.filter (fun x : ZMod 2 => x ^ 2 + c = 0)).card = 1 := by
  revert c; decide

/-- In `ZMod 2`, the equation `x^2 - x + c = 0` has `2` solutions if `c = 0`
and none otherwise. -/
lemma card_filter_sq_sub_x_add_ZMod2 (c : ZMod 2) :
    (Finset.univ.filter (fun x : ZMod 2 => x ^ 2 - x + c = 0)).card =
      if c = 0 then 2 else 0 := by
  revert c; decide

/-- Lemma 21.6 (Sutherland, ideal-counting version): the number of
`𝒪_K`-ideals of norm `p` equals `1 + (D/p)`. -/
theorem numIdealsOfNorm_eq_one_add_kroneckerSymbol (D : ℤ) (p : ℕ) [hp : Fact (Nat.Prime p)]
    (hD : IsImagQuadDiscriminant D) :
    numIdealsOfNorm D p = 1 + kroneckerSymbol p D := by
  obtain ⟨hDneg, hDmod⟩ := hD
  by_cases hp2 : p = 2
  ·
    subst hp2
    unfold numIdealsOfNorm rootsMinPolyMod kroneckerSymbol
    rcases hDmod with hD0 | hD1
    ·
      have hDeven : D % 2 = 0 := by omega
      have hD_not1 : ¬(D % 4 = 1) := by omega
      simp only [hD_not1, ite_false, hDeven, ite_true]
      rw [card_filter_sq_add_eq_zero_ZMod2]; norm_cast
    ·
      have hDodd : ¬(D % 2 = 0) := by omega
      simp only [hD1, ite_true, hDodd, ite_false]
      have hDmod8 : D % 8 = 1 ∨ D % 8 = 5 := by omega
      rcases hDmod8 with h8_1 | h8_5
      · have hc0 : ((((1 - D) / 4 : ℤ) : ZMod 2) = 0) := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact Int.dvd_of_emod_eq_zero (by omega)
        rw [card_filter_sq_sub_x_add_ZMod2, if_pos hc0]
        have : D % 8 = 1 ∨ D % 8 = 7 := Or.inl h8_1
        simp [this]
      · have hc1 : ((((1 - D) / 4 : ℤ) : ZMod 2) ≠ 0) := by
          rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; intro ⟨k, hk⟩; omega
        rw [card_filter_sq_sub_x_add_ZMod2, if_neg hc1]
        have : ¬(D % 8 = 1 ∨ D % 8 = 7) := by omega
        simp [this]
  ·
    have hodd : p ≠ 2 := hp2
    rw [kroneckerSymbol_odd_prime hodd]
    have hprime : Nat.Prime p := hp.out
    have hcard_sqrts := legendreSym.card_sqrts p hodd D
    suffices h : (rootsMinPolyMod D p).card = {x : ZMod p | x ^ 2 = (D : ZMod p)}.toFinset.card by
      rw [numIdealsOfNorm, h]; linarith
    have h2inv : IsUnit (2 : ZMod p) :=
      ZMod.isUnit_prime_of_not_dvd Nat.prime_two
        (fun h => hodd (hprime.eq_one_or_self_of_dvd 2 h |>.resolve_left (by omega) |>.symm))
    have h2ne : (2 : ZMod p) ≠ 0 := IsUnit.ne_zero h2inv
    have h4_ne : (4 : ZMod p) ≠ 0 := by
      have : IsUnit (4 : ZMod p) := by
        rw [show (4 : ZMod p) = 2 * 2 from by norm_num]; exact h2inv.mul h2inv
      exact IsUnit.ne_zero this
    obtain ⟨u, hu⟩ := h2inv


    have h2u_inv : (2 : ZMod p) * ↑u⁻¹ = 1 := by
      rw [← hu]; exact_mod_cast u.mul_inv

    rcases hDmod with hD0 | hD1
    ·
      simp only [rootsMinPolyMod, show ¬(D % 4 = 1) from by omega, ite_false]
      have h4_cast : (4 : ZMod p) * ((-D / 4 : ℤ) : ZMod p) = ((-D : ℤ) : ZMod p) := by
        rw [← Int.cast_ofNat, ← Int.cast_mul]; congr 1; omega
      have h_fwd : ∀ x : ZMod p, x ^ 2 + ((-D / 4 : ℤ) : ZMod p) = 0 →
          (2 * x) ^ 2 = (D : ZMod p) := by
        intro x hx
        have : (2 * x) ^ 2 = 4 * (x ^ 2 + ((-D / 4 : ℤ) : ZMod p)) + (D : ZMod p) := by
          rw [show (2 * x) ^ 2 = 4 * x ^ 2 from by ring, mul_add, h4_cast]; push_cast; ring
        rw [hx, mul_zero, zero_add] at this; exact this
      have h_bwd : ∀ y : ZMod p, y ^ 2 = (D : ZMod p) →
          (↑u⁻¹ * y) ^ 2 + ((-D / 4 : ℤ) : ZMod p) = 0 := by
        intro y hy
        have : (4 : ZMod p) * ((↑u⁻¹ * y) ^ 2 + ((-D / 4 : ℤ) : ZMod p)) = 0 := by
          have h4u : (4 : ZMod p) * (↑u⁻¹ * y) ^ 2 = y ^ 2 := by
            rw [show (4 : ZMod p) * (↑u⁻¹ * y) ^ 2 = (2 * ↑u⁻¹) ^ 2 * y ^ 2 from by ring]
            rw [h2u_inv, one_pow, one_mul]
          rw [mul_add, h4u, h4_cast, hy]; push_cast; ring
        exact (mul_eq_zero.mp this).resolve_left h4_ne
      apply Finset.card_bij (fun x _ => 2 * x)
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h_fwd x hx
      · intro x₁ _ x₂ _ h; exact mul_left_cancel₀ h2ne h
      · intro y hy
        simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact ⟨↑u⁻¹ * y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_bwd y hy⟩,
          by rw [show (2 : ZMod p) * (↑u⁻¹ * y) = (2 * ↑u⁻¹) * y from by ring, h2u_inv, one_mul]⟩
    ·
      simp only [rootsMinPolyMod, show D % 4 = 1 from hD1, ite_true]
      have h4_cast : (4 : ZMod p) * (((1 - D) / 4 : ℤ) : ZMod p) = ((1 - D : ℤ) : ZMod p) := by
        rw [← Int.cast_ofNat, ← Int.cast_mul]; congr 1; omega
      have h_fwd : ∀ x : ZMod p, x ^ 2 - x + ((1 - D) / 4 : ℤ) = 0 →
          (2 * x - 1) ^ 2 = (D : ZMod p) := by
        intro x hx
        have : (2 * x - 1) ^ 2 = 4 * (x ^ 2 - x + ((1 - D) / 4 : ℤ)) + (D : ZMod p) := by
          rw [show (2 * x - 1) ^ 2 = 4 * x ^ 2 - 4 * x + 1 from by ring,
              show (4 : ZMod p) * (x ^ 2 - x + ((1 - D) / 4 : ℤ)) =
                4 * x ^ 2 - 4 * x + 4 * ((1 - D) / 4 : ℤ) from by ring,
              h4_cast]; push_cast; ring
        rw [hx, mul_zero, zero_add] at this; exact this
      have h_bwd : ∀ y : ZMod p, y ^ 2 = (D : ZMod p) →
          (↑u⁻¹ * (y + 1)) ^ 2 - (↑u⁻¹ * (y + 1)) + ((1 - D) / 4 : ℤ) = 0 := by
        intro y hy
        have key : 2 * (↑u⁻¹ * (y + 1)) - 1 = y := by
          rw [show (2 : ZMod p) * (↑u⁻¹ * (y + 1)) = (2 * ↑u⁻¹) * (y + 1) from by ring]
          rw [h2u_inv, one_mul, add_sub_cancel_right]
        have h1 : (2 * (↑u⁻¹ * (y + 1)) - 1) ^ 2 =
            4 * ((↑u⁻¹ * (y + 1)) ^ 2 - (↑u⁻¹ * (y + 1)) + ((1 - D) / 4 : ℤ)) + (D : ZMod p) := by
          rw [show (2 * (↑u⁻¹ * (y + 1)) - 1) ^ 2 =
              4 * (↑u⁻¹ * (y + 1)) ^ 2 - 4 * (↑u⁻¹ * (y + 1)) + 1 from by ring,
              show (4 : ZMod p) * ((↑u⁻¹ * (y + 1)) ^ 2 - (↑u⁻¹ * (y + 1)) + ((1 - D) / 4 : ℤ)) =
                4 * (↑u⁻¹ * (y + 1)) ^ 2 - 4 * (↑u⁻¹ * (y + 1)) + 4 * ((1 - D) / 4 : ℤ) from by ring,
              h4_cast]; push_cast; ring
        rw [key, hy] at h1

        have h2 : (4 : ZMod p) * ((↑u⁻¹ * (y + 1)) ^ 2 - (↑u⁻¹ * (y + 1)) + ((1 - D) / 4 : ℤ)) = 0 := by
          have : (D : ZMod p) - (D : ZMod p) =
            4 * ((↑u⁻¹ * (y + 1)) ^ 2 - (↑u⁻¹ * (y + 1)) + ((1 - D) / 4 : ℤ)) + (D : ZMod p) - (D : ZMod p) := by
            rw [← h1]
          simp only [sub_self, add_sub_cancel_right] at this
          exact this.symm
        exact (mul_eq_zero.mp h2).resolve_left h4_ne
      apply Finset.card_bij (fun x _ => 2 * x - 1)
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h_fwd x hx
      · intro x₁ _ x₂ _ h
        have : 2 * x₁ = 2 * x₂ := by linear_combination h
        exact mul_left_cancel₀ h2ne this
      · intro y hy
        simp only [Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact ⟨↑u⁻¹ * (y + 1), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_bwd y hy⟩,
          by rw [show (2 : ZMod p) * (↑u⁻¹ * (y + 1)) = (2 * ↑u⁻¹) * (y + 1) from by ring,
             h2u_inv, one_mul, add_sub_cancel_right]⟩

end ImagQuadPrimeSplitting

namespace ImagQuadPrimeFactorization

open Elliptic_Curves ProperIdealInvertible

variable {d : ℤ}

/-- The prime ideal `𝔭 = (p, ω - r)` in `ℤ[√d]` above a rational prime `p`
and a root `r` of `x² + d ≡ 0 mod p`, used in Lemma 21.6. -/
def primeIdealAbove (p : ℕ) (r : ℤ) : Ideal (ℤ√d) :=
  Ideal.span {(p : ℤ√d), (⟨-r, 1⟩ : ℤ√d)}

/-- Infrastructure form: in `ℤ[√d]` with `d < 0`, every prime ideal `𝔭 ≠ ⊥`
of norm `p` has the form `(p, ω - r)` for some `r` with `r² + d ≡ 0 mod p`. -/
theorem primeIdeal_of_norm_eq_span_infrastructure
    {d : ℤ} (hd : d < 0) [IsDomain (ℤ√d)]
    (p : ℕ) [Fact (Nat.Prime p)]
    (𝔭 : Ideal (ℤ√d)) (h𝔭 : 𝔭 ≠ ⊥)
    (hnorm : idealNormZsqrtd 𝔭 = p) :
    ∃ r : ℤ, (r ^ 2 + d) % (p : ℤ) = 0 ∧
      𝔭 = primeIdealAbove p r := by sorry

/-- Infrastructure form (split case): when `r` is a root of `x² + d ≡ 0 mod p`
with `2r ≢ 0 mod p`, the principal ideal `(p)` in `ℤ[√d]` factors as
`𝔭 · 𝔭̄` with `𝔭 ≠ 𝔭̄`. -/
theorem principal_ideal_prime_split_infrastructure
    {d : ℤ} (hd : d < 0) [IsDomain (ℤ√d)]
    (p : ℕ) [Fact (Nat.Prime p)]
    (r : ℤ) (hroot : (r ^ 2 + d) % (p : ℤ) = 0)
    (hdistinct : (2 * r) % (p : ℤ) ≠ 0) :
    primeIdealAbove (d := d) p r * conjIdeal (primeIdealAbove (d := d) p r) =
      Ideal.span {(p : ℤ√d)} ∧
    primeIdealAbove (d := d) p r ≠
      conjIdeal (primeIdealAbove (d := d) p r) := by sorry

/-- Infrastructure form (ramified case): when `r` is a root of `x² + d ≡ 0
mod p` with `2r ≡ 0 mod p`, the principal ideal `(p)` in `ℤ[√d]` is
`𝔭²`. -/
theorem principal_ideal_prime_ramified_infrastructure
    {d : ℤ} (hd : d < 0) [IsDomain (ℤ√d)]
    (p : ℕ) [Fact (Nat.Prime p)]
    (r : ℤ) (hroot : (r ^ 2 + d) % (p : ℤ) = 0)
    (hramified : (2 * r) % (p : ℤ) = 0) :
    primeIdealAbove (d := d) p r ^ 2 =
      Ideal.span {(p : ℤ√d)} := by sorry

/-- Infrastructure form (inert case): if the Kronecker symbol `(4d/p) = -1`,
then the principal ideal `(p)` in `ℤ[√d]` is prime. -/
theorem principal_ideal_prime_inert_infrastructure
    {d : ℤ} (hd : d < 0) [IsDomain (ℤ√d)]
    (p : ℕ) [Fact (Nat.Prime p)]
    (hD : IsImagQuadDiscriminant (4 * d))
    (hkron : kroneckerSymbol p (4 * d) = -1) :
    (Ideal.span {(p : ℤ√d)}).IsPrime := by sorry

/-- User-facing version of `primeIdeal_of_norm_eq_span_infrastructure`. -/
theorem primeIdeal_of_norm_eq_span (hd : d < 0) [IsDomain (ℤ√d)]
    (p : ℕ) [Fact (Nat.Prime p)]
    (𝔭 : Ideal (ℤ√d)) (h𝔭 : 𝔭 ≠ ⊥)
    (hnorm : idealNormZsqrtd 𝔭 = p) :
    ∃ r : ℤ, (r ^ 2 + d) % (p : ℤ) = 0 ∧
      𝔭 = primeIdealAbove p r := by
  exact primeIdeal_of_norm_eq_span_infrastructure hd p 𝔭 h𝔭 hnorm

/-- User-facing version of `principal_ideal_prime_split_infrastructure`. -/
theorem principal_ideal_prime_split (hd : d < 0) [IsDomain (ℤ√d)]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (r : ℤ) (hroot : (r ^ 2 + d) % (p : ℤ) = 0)
    (hdistinct : (2 * r) % (p : ℤ) ≠ 0) :
    primeIdealAbove (d := d) p r * conjIdeal (primeIdealAbove (d := d) p r) =
      Ideal.span {(p : ℤ√d)} ∧
    primeIdealAbove (d := d) p r ≠
      conjIdeal (primeIdealAbove (d := d) p r) := by
  exact principal_ideal_prime_split_infrastructure hd p r hroot hdistinct

/-- User-facing version of `principal_ideal_prime_ramified_infrastructure`. -/
theorem principal_ideal_prime_ramified (hd : d < 0) [IsDomain (ℤ√d)]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (r : ℤ) (hroot : (r ^ 2 + d) % (p : ℤ) = 0)
    (hramified : (2 * r) % (p : ℤ) = 0) :
    primeIdealAbove (d := d) p r ^ 2 =
      Ideal.span {(p : ℤ√d)} := by
  exact principal_ideal_prime_ramified_infrastructure hd p r hroot hramified

/-- User-facing version of `principal_ideal_prime_inert_infrastructure`. -/
theorem principal_ideal_prime_inert (hd : d < 0) [IsDomain (ℤ√d)]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (hD : IsImagQuadDiscriminant (4 * d))
    (hkron : kroneckerSymbol p (4 * d) = -1) :
    (Ideal.span {(p : ℤ√d)}).IsPrime := by
  exact principal_ideal_prime_inert_infrastructure hd p hD hkron

end ImagQuadPrimeFactorization

namespace ImagQuadPrimeSplitting.IdealRootBijection

open Elliptic_Curves ImagQuadPrimeSplitting

/-- The ideal `(p, ω - r)` in `ℤ[√d]` is nonzero and has norm `p` whenever
`r² + d ≡ 0 mod p`. -/
theorem primeIdealAbove_hasNorm
    {d : ℤ} (hd : d < 0) [IsDomain (ℤ√d)]
    (p : ℕ) [Fact (Nat.Prime p)]
    (r : ℤ) (hroot : (r ^ 2 + d) % (p : ℤ) = 0) :
    ImagQuadPrimeFactorization.primeIdealAbove (d := d) p r ≠ ⊥ ∧
    ProperIdealInvertible.idealNormZsqrtd (ImagQuadPrimeFactorization.primeIdealAbove (d := d) p r) = p := by sorry

/-- Distinct roots `r ≠ s` (mod `p`) of `x² + d ≡ 0 mod p` give distinct
prime ideals `(p, ω - r) ≠ (p, ω - s)`. -/
theorem primeIdealAbove_injective
    {d : ℤ} (hd : d < 0) [IsDomain (ℤ√d)]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (r s : ℤ)
    (hr : (r ^ 2 + d) % (p : ℤ) = 0)
    (hs : (s ^ 2 + d) % (p : ℤ) = 0)
    (heq : ImagQuadPrimeFactorization.primeIdealAbove (d := d) p r =
           ImagQuadPrimeFactorization.primeIdealAbove (d := d) p s) :
    (r : ZMod p) = (s : ZMod p) := by sorry

/-- The number of `𝒪_K`-ideals of norm `p` in the imaginary quadratic field of
discriminant `4d` equals the number of roots `r ∈ ZMod p` for which
`(p, ω - r)` is a nonzero ideal of norm `p`. -/
theorem numIdealsOfNorm_eq_card_ideals_of_norm
    {d : ℤ} (hd : d < 0) [IsDomain (ℤ√d)]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (hD : IsImagQuadDiscriminant (4 * d)) :
    numIdealsOfNorm (4 * d) p =
      ↑(Finset.univ.filter (fun r : ZMod p =>
        (ImagQuadPrimeFactorization.primeIdealAbove (d := d) p (ZMod.val r) ≠ ⊥ ∧
         ProperIdealInvertible.idealNormZsqrtd
           (ImagQuadPrimeFactorization.primeIdealAbove (d := d) p (ZMod.val r)) = p))).card := by sorry

end ImagQuadPrimeSplitting.IdealRootBijection

namespace CMMethod.TwistSelection

open Elliptic_Curves

/-- Given an elliptic curve `E/F` with Frobenius trace `±t`, either `E` itself
or its quadratic twist has exactly `|F| + 1 - t` points. This is the twist
selection step in the CM method. -/
theorem exists_curve_or_twist_with_order
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (E : WeierstrassCurve.Affine F)
    (t : ℤ)
    (hfrob : Hasse.traceFrobenius E = t ∨ Hasse.traceFrobenius E = -t)
    (hE : Hasse.numPoints E ≤ 2 * Fintype.card F + 2) :
    (Hasse.numPoints E : ℤ) = (Fintype.card F : ℤ) + 1 - t ∨
    (QuadraticTwist.twistNumPoints E : ℤ) = (Fintype.card F : ℤ) + 1 - t := by
  rcases hfrob with h | h
  ·
    left
    have := Hasse.numPoints_eq_card_sub_trace E
    linarith
  ·
    right
    have hadd := QuadraticTwist.numPoints_add_twist E hE
    have hnum := Hasse.numPoints_eq_card_sub_trace E
    omega

end CMMethod.TwistSelection
