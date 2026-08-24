/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.Isogenies
import Atlas.EllipticCurves.code.PointCounting
import Atlas.EllipticCurves.code.JInvariant
import Atlas.EllipticCurves.code.EndomorphismAlgebra
import Atlas.EllipticCurves.code.EndAlgClassification

import Mathlib.Algebra.CharP.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank

universe u

namespace OrdinarySupersingular

variable {F : Type u} [Field F] [DecidableEq F]

/-- The separable degree of an isogeny `φ : E₁ → E₂`, i.e., the degree of the separable part of
the induced extension of function fields. -/
noncomputable def separableDegree {E₁ E₂ : WeierstrassCurve.Affine F}
    (φ : Isogeny E₁ E₂) : ℕ := by sorry

/-- The separable degree of an isogeny is strictly positive. -/
theorem separableDegree_pos {E₁ E₂ : WeierstrassCurve.Affine F}
    (φ : Isogeny E₁ E₂) : 0 < separableDegree φ := by sorry

/-- Separable degree is multiplicative under composition of isogenies. -/
theorem separableDegree_comp {E₁ E₂ E₃ : WeierstrassCurve.Affine F}
    (ψ : Isogeny E₂ E₃) (φ : Isogeny E₁ E₂) :
    separableDegree (Isogeny.comp ψ φ) = separableDegree ψ * separableDegree φ := by sorry

/-- The multiplication-by-`p` map `[p] : E → E` viewed as an isogeny, where `p` is the
characteristic of the base field. -/
noncomputable def mulByPIsogeny (E : WeierstrassCurve.Affine F) (p : ℕ)
    [Fact (Nat.Prime p)] [CharP F p] : Isogeny E E := by sorry

/-- The multiplication-by-`p` isogeny acts on points by the usual `ℤ`-scalar multiplication by
`p`. -/
theorem mulByPIsogeny_apply (E : WeierstrassCurve.Affine F) (p : ℕ)
    [Fact (Nat.Prime p)] [CharP F p] (P : E.Point) :
    (mulByPIsogeny E p).toAddMonoidHom P = (p : ℤ) • P := by sorry

/-- For any isogeny `φ : E₁ → E₂`, pre- and post-composition with the multiplication-by-`p` maps
yield isogenies with the same separable degree. -/
theorem mulByP_comp_separableDegree {E₁ E₂ : WeierstrassCurve.Affine F}
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p] (φ : Isogeny E₁ E₂) :
    separableDegree (Isogeny.comp (mulByPIsogeny E₂ p) φ) =
    separableDegree (Isogeny.comp φ (mulByPIsogeny E₁ p)) := by sorry

/-- The `p`-torsion subgroup of `E`: the set of points `P` killed by multiplication by `p`. -/
def pTorsionSubgroup (E : WeierstrassCurve.Affine F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p] : Set E.Point :=
  { P | (p : ℤ) • P = 0 }

/-- An elliptic curve `E` over a field of characteristic `p` is supersingular if its `p`-torsion
subgroup is trivial. -/
def IsSupersingular (E : WeierstrassCurve.Affine F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p] : Prop :=
  ∀ P : E.Point, (p : ℤ) • P = 0 → P = 0

/-- An elliptic curve `E` over a field of characteristic `p` is ordinary if it admits a nonzero
`p`-torsion point. -/
def IsOrdinary (E : WeierstrassCurve.Affine F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p] : Prop :=
  ∃ P : E.Point, (p : ℤ) • P = 0 ∧ P ≠ 0

/-- `E` is ordinary iff it is not supersingular. -/
theorem isOrdinary_iff_not_supersingular (E : WeierstrassCurve.Affine F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p] :
    IsOrdinary E p ↔ ¬ IsSupersingular E p := by
  constructor
  · rintro ⟨P, hP, hPne⟩ hss
    exact hPne (hss P hP)
  · intro hns
    unfold IsSupersingular at hns
    push_neg at hns
    exact hns

/-- Supersingularity is equivalent to the multiplication-by-`p` isogeny having separable degree
`1` (i.e., being purely inseparable). -/
theorem isSupersingular_iff_separableDegree
    {E : WeierstrassCurve.Affine F}
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p] :
    IsSupersingular E p ↔ separableDegree (mulByPIsogeny E p) = 1 := by sorry

/-- Every elliptic curve over a field of characteristic `p` is either ordinary or supersingular. -/
theorem ordinary_or_supersingular (E : WeierstrassCurve.Affine F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p] :
    IsOrdinary E p ∨ IsSupersingular E p := by
  rcases em (IsSupersingular E p) with hss | hns
  · exact Or.inr hss
  · exact Or.inl ((isOrdinary_iff_not_supersingular E p).mpr hns)

/-- Isogenous elliptic curves have the same separable degree for their multiplication-by-`p`
isogenies; in particular, this is an isogeny invariant. -/
theorem separableDegree_mulByP_eq_of_isogeny
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    (φ : Isogeny E₁ E₂) :
    separableDegree (mulByPIsogeny E₁ p) = separableDegree (mulByPIsogeny E₂ p) := by

  have h_comm := mulByP_comp_separableDegree p φ

  rw [separableDegree_comp, separableDegree_comp] at h_comm


  have hφ_pos := separableDegree_pos φ
  exact (Nat.eq_of_mul_eq_mul_left hφ_pos (by linarith)).symm

/-- Supersingularity is an isogeny invariant: if `E₁` and `E₂` are isogenous, then `E₁` is
supersingular iff `E₂` is. -/
theorem isSupersingular_iff_of_isogeny
    {E₁ E₂ : WeierstrassCurve.Affine F}
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    (φ : Isogeny E₁ E₂) :
    IsSupersingular E₁ p ↔ IsSupersingular E₂ p := by
  rw [isSupersingular_iff_separableDegree p, isSupersingular_iff_separableDegree p,
    separableDegree_mulByP_eq_of_isogeny p φ]

/-- Scalar multiplication by an integer `m` (acting on `E.Point` via `m • id`) gives a well-defined
algebraic endomorphism of `E`. -/
theorem intSmulEndomorphism_algebraic
    {F : Type*} [Field F] [DecidableEq F]
    (E : WeierstrassCurve.Affine F) (m : ℤ) :
    EllipticCurve.IsAlgebraicEndomorphism E (m • (1 : AddMonoid.End E.Point)) := by sorry

open EllipticCurve in
/-- The endomorphism of `E` given by multiplication by the integer `m`, packaged as an element of
the endomorphism ring of `E`. -/
def intSmulEndomorphism {F : Type*} [Field F] [DecidableEq F]
    (E : WeierstrassCurve.Affine F) (m : ℤ) : EndomorphismRing E :=
  ⟨m • (1 : AddMonoid.End E.Point), intSmulEndomorphism_algebraic E m⟩

/-- The Frobenius endomorphism of `E` over a finite field `F` of characteristic `p`, as an element
of the endomorphism ring. -/
noncomputable def frobEndomorphism {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    (E : WeierstrassCurve.Affine F) :
    EllipticCurve.EndomorphismRing E := by sorry

/-- The dual (Verschiebung) of the Frobenius endomorphism, as an element of the endomorphism
ring. -/
noncomputable def dualFrobEndomorphism {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    (E : WeierstrassCurve.Affine F) :
    EllipticCurve.EndomorphismRing E := by sorry

/-- The Frobenius endomorphism is inseparable. -/
theorem frobEndomorphism_insep {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    (E : WeierstrassCurve.Affine F) :
    PointCounting.EndInsep (frobEndomorphism p E) := by sorry

/-- The defining identity `π + π̂ = [t]` in the endomorphism ring: Frobenius plus its dual equals
multiplication by the trace of Frobenius. -/
theorem frob_add_dualFrob_eq_trace {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    (E : WeierstrassCurve.Affine F) :
    frobEndomorphism p E + dualFrobEndomorphism p E =
      intSmulEndomorphism E (Hasse.traceFrobenius E) := by sorry

/-- Multiplication-by-`m` is inseparable iff `p ∣ m`. -/
theorem intSmulEndomorphism_insep_iff {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    (E : WeierstrassCurve.Affine F) (m : ℤ) :
    PointCounting.EndInsep (intSmulEndomorphism E m) ↔ (p : ℤ) ∣ m := by sorry

/-- Supersingularity of `E/F_q` is equivalent to inseparability of the dual Frobenius. -/
theorem isSupersingular_iff_dualFrob_insep
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    (E : WeierstrassCurve.Affine F) :
    IsSupersingular E p ↔
      PointCounting.EndInsep (dualFrobEndomorphism p E) := by sorry

/-- Supersingularity of `E/F_q` is equivalent to `p` dividing the trace of Frobenius. The proof
uses Lemma 7.1: if `α` is an inseparable isogeny, then `α + β` is inseparable iff `β` is. -/
theorem isSupersingular_iff_trace_dvd
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    (E : WeierstrassCurve.Affine F) :
    IsSupersingular E p ↔
      (p : ℤ) ∣ Hasse.traceFrobenius E := by

  rw [isSupersingular_iff_dualFrob_insep p E]


  have h_frob_insep := frobEndomorphism_insep p E
  have h_add := PointCounting.lemma_7_1 (E := E) h_frob_insep
    (β := dualFrobEndomorphism p E)


  rw [frob_add_dualFrob_eq_trace p E] at h_add


  rw [← h_add]
  exact intSmulEndomorphism_insep_iff p E _

omit [DecidableEq F] in
/-- Frobenius compatibility of the `j`-invariant: applying the `p^2`-power Frobenius to the
coefficients `A`, `B` and to the resulting `j`-invariant agree. -/
theorem jInvariant_pow_frobenius (A B : F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p] :
    jInvariant (A ^ (p ^ 2)) (B ^ (p ^ 2)) = (jInvariant A B) ^ (p ^ 2) := by
  haveI : ExpChar F p := expChar_prime F p

  let φ := iterateFrobenius F p 2
  have hφ : ∀ x : F, φ x = x ^ (p ^ 2) := fun x => iterateFrobenius_def p 2 x

  suffices h : φ (jInvariant A B) = jInvariant (φ A) (φ B) by
    rw [← hφ (jInvariant A B), h]
    simp only [hφ]

  simp only [jInvariant, φ, map_div₀, map_mul, map_pow, map_add, map_ofNat]

/-- If `E : y² = x³ + Ax + B` is supersingular, then `E` is isomorphic to its `p²`-Frobenius
twist: there exists `μ ≠ 0` with `A^(p²) = μ⁴ A` and `B^(p²) = μ⁶ B`. -/
theorem supersingular_frobeniusTwist_iso (A B : F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    (hss : IsSupersingular (⟨0, 0, 0, A, B⟩ : WeierstrassCurve.Affine F) p) :
    ∃ μ : F, μ ≠ 0 ∧ A ^ (p ^ 2) = μ ^ 4 * A ∧ B ^ (p ^ 2) = μ ^ 6 * B := by sorry

/-- A supersingular curve has the same `j`-invariant as its `p²`-Frobenius twist. -/
theorem supersingular_jInvariant_eq_frobeniusTwist (A B : F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    (hss : IsSupersingular (⟨0, 0, 0, A, B⟩ : WeierstrassCurve.Affine F) p) :
    jInvariant A B = jInvariant (A ^ (p ^ 2)) (B ^ (p ^ 2)) := by
  obtain ⟨μ, hμ, hA, hB⟩ := supersingular_frobeniusTwist_iso A B p hss
  exact jInvariant_eq_of_iso A B (A ^ (p ^ 2)) (B ^ (p ^ 2)) μ hμ hA hB

/-- The `j`-invariant of a supersingular elliptic curve lies in `F_{p²}`: it is fixed by the
`p²`-power Frobenius. -/
theorem supersingular_jInvariant_in_Fp2 (A B : F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    (hss : IsSupersingular (⟨0, 0, 0, A, B⟩ : WeierstrassCurve.Affine F) p) :
    (jInvariant A B) ^ (p ^ 2) = jInvariant A B := by

  have h_twist := supersingular_jInvariant_eq_frobeniusTwist A B p hss

  have h_frob := jInvariant_pow_frobenius A B p

  rw [← h_frob, ← h_twist]

/-- The geometric endomorphism algebra of `E`: `End(E_{\bar F}) ⊗_ℤ ℚ`, the endomorphism algebra
of `E` after base-change to the algebraic closure. -/
noncomputable def GeometricEndomorphismAlgebra (E : WeierstrassCurve.Affine F) : Type u := by sorry

/-- Ring structure on the geometric endomorphism algebra. -/
noncomputable instance GeometricEndomorphismAlgebra.instRing (E : WeierstrassCurve.Affine F) :
  Ring (GeometricEndomorphismAlgebra E) := by sorry

/-- `ℚ`-algebra structure on the geometric endomorphism algebra. -/
noncomputable instance GeometricEndomorphismAlgebra.instAlgebra (E : WeierstrassCurve.Affine F) :
  @Algebra ℚ (GeometricEndomorphismAlgebra E) _
    (GeometricEndomorphismAlgebra.instRing E).toSemiring := by sorry

/-- The geometric endomorphism algebra of `E` is finite-dimensional over `ℚ`. -/
theorem GeometricEndomorphismAlgebra.instFiniteDimensional (E : WeierstrassCurve.Affine F) :
  @FiniteDimensional ℚ (GeometricEndomorphismAlgebra E)
    _ (GeometricEndomorphismAlgebra.instRing E).toAddCommGroup
    (@Algebra.toModule ℚ (GeometricEndomorphismAlgebra E) _ _
      (GeometricEndomorphismAlgebra.instAlgebra E)) := by sorry

/-- Positive-definite involution algebra structure (Rosati involution) on the geometric
endomorphism algebra of `E`. -/
noncomputable instance GeometricEndomorphismAlgebra.instPDInvAlgebra (E : WeierstrassCurve.Affine F) :
  @PositiveDefiniteInvolutionAlgebra (GeometricEndomorphismAlgebra E)
    (GeometricEndomorphismAlgebra.instRing E)
    (GeometricEndomorphismAlgebra.instAlgebra E) := by sorry

/-- The geometric endomorphism algebra of `E` is nontrivial. -/
theorem GeometricEndomorphismAlgebra.instNontrivial (E : WeierstrassCurve.Affine F) :
  @Nontrivial (GeometricEndomorphismAlgebra E) := by sorry

omit [Field F] [DecidableEq F] in
/-- The geometric endomorphism algebra of any elliptic curve falls into the three-way Albert
classification (rational / imaginary quadratic / quaternion). -/
theorem geometricEndomorphismAlgebra_classification
    {F : Type*} [Field F] [DecidableEq F]
    (E : WeierstrassCurve.Affine F) :
    @EndAlgClassification (GeometricEndomorphismAlgebra E)
      (GeometricEndomorphismAlgebra.instRing E)
      (GeometricEndomorphismAlgebra.instAlgebra E) := by
  letI : Ring (GeometricEndomorphismAlgebra E) := GeometricEndomorphismAlgebra.instRing E
  letI : Algebra ℚ (GeometricEndomorphismAlgebra E) := GeometricEndomorphismAlgebra.instAlgebra E
  haveI := GeometricEndomorphismAlgebra.instPDInvAlgebra E
  haveI := GeometricEndomorphismAlgebra.instNontrivial E
  exact endomorphism_algebra_classification (GeometricEndomorphismAlgebra E)

/-- The predicate that the geometric endomorphism algebra of `E` is a quaternion algebra: it has
`ℚ`-dimension `4` with two anticommuting elements squaring to negative rationals. -/
def IsQuaternionEndAlgebra (E : WeierstrassCurve.Affine F) : Prop :=
  let _inst_ring := GeometricEndomorphismAlgebra.instRing E
  let _inst_alg := GeometricEndomorphismAlgebra.instAlgebra E
  @Module.finrank ℚ (GeometricEndomorphismAlgebra E)
    _ _inst_ring.toAddCommMonoid
    (@Algebra.toModule ℚ (GeometricEndomorphismAlgebra E) _ _ _inst_alg)
  = 4 ∧
  ∃ α β : GeometricEndomorphismAlgebra E,
    (∃ a : ℚ, a < 0 ∧ α * α = @algebraMap ℚ (GeometricEndomorphismAlgebra E) _ _inst_ring.toSemiring _inst_alg a) ∧
    (∃ b : ℚ, b < 0 ∧ β * β = @algebraMap ℚ (GeometricEndomorphismAlgebra E) _ _inst_ring.toSemiring _inst_alg b) ∧
    α * β = -(β * α)

/-- For a supersingular elliptic curve, the geometric endomorphism algebra has `ℚ`-dimension
strictly greater than `1`, i.e., it is not just `ℚ`. -/
theorem supersingular_endAlgebra_not_rational
    {F : Type u} [Field F] [DecidableEq F]
    (E : WeierstrassCurve.Affine F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    (hss : IsSupersingular E p) :
    @Module.finrank ℚ (GeometricEndomorphismAlgebra E)
      _ (GeometricEndomorphismAlgebra.instRing E).toAddCommMonoid
      (@Algebra.toModule ℚ (GeometricEndomorphismAlgebra E) _ _
        (GeometricEndomorphismAlgebra.instAlgebra E)) ≠ 1 := by sorry

/-- For a supersingular elliptic curve, the geometric endomorphism algebra is not an imaginary
quadratic field, i.e., its `ℚ`-dimension is not `2`. -/
theorem supersingular_endAlgebra_not_imaginaryQuadratic
    {F : Type u} [Field F] [DecidableEq F]
    (E : WeierstrassCurve.Affine F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    (hss : IsSupersingular E p) :
    @Module.finrank ℚ (GeometricEndomorphismAlgebra E)
      _ (GeometricEndomorphismAlgebra.instRing E).toAddCommMonoid
      (@Algebra.toModule ℚ (GeometricEndomorphismAlgebra E) _ _
        (GeometricEndomorphismAlgebra.instAlgebra E)) ≠ 2 := by sorry

/-- The geometric endomorphism algebra of a supersingular elliptic curve is a quaternion algebra
(over `ℚ`). -/
theorem supersingular_geometricEndomorphismAlgebra_quaternion
    {F : Type u} [Field F] [DecidableEq F]
    (E : WeierstrassCurve.Affine F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    (hss : IsSupersingular E p) :
    IsQuaternionEndAlgebra E := by

  have hclass := geometricEndomorphismAlgebra_classification E
  letI : Ring (GeometricEndomorphismAlgebra E) := GeometricEndomorphismAlgebra.instRing E
  letI : Algebra ℚ (GeometricEndomorphismAlgebra E) := GeometricEndomorphismAlgebra.instAlgebra E

  cases hclass with
  | rational hdim =>

    exact absurd hdim (supersingular_endAlgebra_not_rational E p hss)
  | imaginaryQuadratic hdim _ =>

    exact absurd hdim (supersingular_endAlgebra_not_imaginaryQuadratic E p hss)
  | quaternionAlgebra hdim hαβ =>

    exact ⟨hdim, hαβ⟩

/-- If the geometric endomorphism algebra of `E` is a quaternion algebra, there exist two nonzero
anticommuting endomorphisms `α`, `β` in the endomorphism ring of `E`. -/
theorem quaternionEndAlgebra_anticommuting_endomorphisms
    {F : Type u} [Field F] [DecidableEq F]
    (E : WeierstrassCurve.Affine F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    (hquat : IsQuaternionEndAlgebra E) :
    ∃ (α β : EllipticCurve.EndomorphismRing E),
      α ≠ 0 ∧ β ≠ 0 ∧ α * β + β * α = 0 := by sorry

/-- For an ordinary elliptic curve, two nonzero anticommuting endomorphisms cannot exist: the
existence of a nontrivial `p`-torsion point contradicts the anticommutation relation. -/
theorem ordinary_torsion_anticommutation_contradiction
    {F : Type u} [Field F] [DecidableEq F]
    (E : WeierstrassCurve.Affine F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    (hord : IsOrdinary E p)
    (α β : EllipticCurve.EndomorphismRing E)
    (hα : α ≠ 0) (hβ : β ≠ 0)
    (hanti : α * β + β * α = 0) :
    False := by sorry

/-- The geometric endomorphism algebra of an ordinary elliptic curve is not a quaternion algebra. -/
theorem ordinary_not_quaternionEndAlgebra
    {F : Type u} [Field F] [DecidableEq F]
    (E : WeierstrassCurve.Affine F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    (hord : IsOrdinary E p) :
    ¬ IsQuaternionEndAlgebra E := by
  intro hquat

  obtain ⟨α, β, hα, hβ, hanti⟩ := quaternionEndAlgebra_anticommuting_endomorphisms E p hquat

  exact ordinary_torsion_anticommutation_contradiction E p hord α β hα hβ hanti

/-- If the geometric endomorphism algebra of `E` is a quaternion algebra, then `E` is
supersingular. -/
theorem quaternionEndAlgebra_imp_supersingular
    {F : Type u} [Field F] [DecidableEq F]
    (E : WeierstrassCurve.Affine F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    (hquat : IsQuaternionEndAlgebra E) :
    IsSupersingular E p := by

  by_contra hord

  exact ordinary_not_quaternionEndAlgebra E p
    ((isOrdinary_iff_not_supersingular E p).mpr hord) hquat

/-- The predicate that the geometric endomorphism algebra of `E` is an imaginary quadratic field:
it has `ℚ`-dimension `2` with a non-rational element squaring to a negative rational. -/
def IsImaginaryQuadraticEndAlgebra (E : WeierstrassCurve.Affine F) : Prop :=
  let _inst_ring := GeometricEndomorphismAlgebra.instRing E
  let _inst_alg := GeometricEndomorphismAlgebra.instAlgebra E
  @Module.finrank ℚ (GeometricEndomorphismAlgebra E)
    _ _inst_ring.toAddCommMonoid
    (@Algebra.toModule ℚ (GeometricEndomorphismAlgebra E) _ _ _inst_alg)
  = 2 ∧
  ∃ α : GeometricEndomorphismAlgebra E,
    (∀ q : ℚ, α ≠ @algebraMap ℚ (GeometricEndomorphismAlgebra E) _ _inst_ring.toSemiring _inst_alg q) ∧
    ∃ d : ℚ, d < 0 ∧ α * α = @algebraMap ℚ (GeometricEndomorphismAlgebra E) _ _inst_ring.toSemiring _inst_alg d

/-- The geometric endomorphism algebra of an ordinary elliptic curve over a finite field is an
imaginary quadratic field. -/
theorem ordinary_geometricEndomorphismAlgebra_imaginaryQuadratic
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (E : WeierstrassCurve.Affine F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p]
    (hord : IsOrdinary E p) :
    IsImaginaryQuadraticEndAlgebra E := by sorry

/-- The supersingular/ordinary dichotomy over a finite field: every elliptic curve `E/F_q` is
either supersingular (in which case `p` divides the trace of Frobenius and the geometric endomorphism
algebra is a quaternion algebra) or ordinary (in which case `p` does not divide the trace and the
algebra is an imaginary quadratic field). -/
theorem supersingular_ordinary_dichotomy
    {F : Type u} [Field F] [Fintype F] [DecidableEq F]
    (E : WeierstrassCurve.Affine F)
    (p : ℕ) [Fact (Nat.Prime p)] [CharP F p] :
    (IsSupersingular E p ∧
      (p : ℤ) ∣ Hasse.traceFrobenius (F := F) (W := E) ∧
      IsQuaternionEndAlgebra E) ∨
    (IsOrdinary E p ∧
      ¬ (p : ℤ) ∣ Hasse.traceFrobenius (F := F) (W := E) ∧
      IsImaginaryQuadraticEndAlgebra E) := by

  rcases ordinary_or_supersingular E p with hord | hss
  ·
    right
    refine ⟨hord, ?_, ordinary_geometricEndomorphismAlgebra_imaginaryQuadratic E p hord⟩


    exact fun hdvd => (isOrdinary_iff_not_supersingular E p).mp hord
      ((isSupersingular_iff_trace_dvd p E).mpr hdvd)
  ·
    left
    refine ⟨hss, ?_, ?_⟩

    · exact (isSupersingular_iff_trace_dvd p E).mp hss

    · exact supersingular_geometricEndomorphismAlgebra_quaternion E p hss

end OrdinarySupersingular

namespace OrdinarySupersingularClassification

open ConductorOrder

variable {d : ℤ}

/-- If the conductor-`f₁` order is contained in the conductor-`f₂` order, then `f₂ ∣ f₁`. This is
the standard correspondence between containment of orders and divisibility of conductors. -/
theorem conductor_dvd_of_le {f₁ f₂ : ℕ}
    (h : conductorOrder d f₁ ≤ conductorOrder d f₂) :
    f₂ ∣ f₁ := by

  have hmem : (⟨0, (f₁ : ℤ)⟩ : ℤ√d) ∈ conductorOrder d f₂ := by
    apply h
    simp [mem_conductorOrder_iff]

  rw [mem_conductorOrder_iff] at hmem
  exact Int.natCast_dvd_natCast.mp hmem

section EC_Application

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The Frobenius discriminant of `E/F_q`: `t² - 4q`, where `t = tr π_E`. -/
noncomputable def frobDiscriminant (E : WeierstrassCurve.Affine F) : ℤ :=
  (Hasse.traceFrobenius E) ^ 2 - 4 * (Fintype.card F : ℤ)

/-- The predicate that the Frobenius endomorphism is not an integer (i.e., `t² ≠ 4q`), so that
`ℤ[π_E]` is a non-trivial quadratic order. -/
def frobNotInt (E : WeierstrassCurve.Affine F) : Prop :=
  (Hasse.traceFrobenius E) ^ 2 ≠ 4 * (Fintype.card F : ℤ)

/-- The conductor of the order `ℤ[π_E]` inside the maximal quadratic order with discriminant
`frobDiscriminant E`. -/
noncomputable def frobeniusOrderConductor (E : WeierstrassCurve.Affine F)
    (hq : 0 < Fintype.card F)
    (hnotint : frobNotInt E) : ℕ := by sorry

/-- The conductor of the endomorphism ring of `E` inside the maximal quadratic order with
discriminant `frobDiscriminant E`. -/
noncomputable def endRingConductor (E : WeierstrassCurve.Affine F)
    (hq : 0 < Fintype.card F)
    (hnotint : frobNotInt E) : ℕ := by sorry

omit [DecidableEq F] in
/-- The Frobenius order `ℤ[π_E]` is contained in the endomorphism ring `End(E)`, expressed as a
containment of the corresponding conductor orders. -/
theorem frobeniusOrder_le_endRing_ax
    (E : WeierstrassCurve.Affine F)
    (hq : 0 < Fintype.card F)
    (hnotint : frobNotInt E) :
    conductorOrder (frobDiscriminant E)
        (frobeniusOrderConductor E hq hnotint) ≤
      conductorOrder (frobDiscriminant E)
        (endRingConductor E hq hnotint) := by sorry

omit [DecidableEq F] in
/-- The conductor of `End(E)` divides the conductor of `ℤ[π_E]`, as a consequence of the order
containment `ℤ[π_E] ⊆ End(E)`. -/
theorem endRingConductor_dvd_frobeniusOrderConductor
    (E : WeierstrassCurve.Affine F)
    (hq : 0 < Fintype.card F)
    (hnotint : frobNotInt E) :
    endRingConductor E hq hnotint ∣ frobeniusOrderConductor E hq hnotint :=
  conductor_dvd_of_le (frobeniusOrder_le_endRing_ax E hq hnotint)

omit [DecidableEq F] in
/-- The endomorphism ring is contained in the maximal order `O_K` (the conductor-`1` order), since
its conductor is a divisor of `1`. -/
theorem endRing_le_maximalOrder (E : WeierstrassCurve.Affine F)
    (hq : 0 < Fintype.card F)
    (hnotint : frobNotInt E) :
    conductorOrder (frobDiscriminant E)
        (endRingConductor E hq hnotint) ≤
      conductorOrder (frobDiscriminant E) 1 :=
  conductorOrder_le_of_dvd (one_dvd _)

omit [DecidableEq F] in
/-- Theorem 13.8 of Sutherland: for an elliptic curve `E/F_q` whose geometric endomorphism algebra
is an imaginary quadratic field `K`, the inclusions `ℤ[π_E] ⊆ End(E) ⊆ O_K` hold, and the
conductor of `End(E)` divides `[O_K : ℤ[π_E]]`. -/
theorem theorem_13_8 (E : WeierstrassCurve.Affine F)
    (hq : 0 < Fintype.card F)
    (hnotint : frobNotInt E) :

    (conductorOrder (frobDiscriminant E)
        (frobeniusOrderConductor E hq hnotint) ≤
      conductorOrder (frobDiscriminant E)
        (endRingConductor E hq hnotint) ∧
     conductorOrder (frobDiscriminant E)
        (endRingConductor E hq hnotint) ≤
      conductorOrder (frobDiscriminant E) 1) ∧

    endRingConductor E hq hnotint ∣ frobeniusOrderConductor E hq hnotint := by

  have h_frob_le_end := frobeniusOrder_le_endRing_ax E hq hnotint
  refine ⟨⟨h_frob_le_end, ?_⟩, ?_⟩

  · exact endRing_le_maximalOrder E hq hnotint

  · exact conductor_dvd_of_le h_frob_le_end

end EC_Application

end OrdinarySupersingularClassification
