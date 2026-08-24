/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.NumberTheory.Niven
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Polynomial.Bivariate

import Atlas.EllipticCurves.code.ComplexMultiplication

noncomputable section

open Polynomial Classical

/-- An integer `D` is an imaginary quadratic discriminant iff `D < 0` and
`D ≡ 0 or 1 (mod 4)`. These are exactly the discriminants of orders in imaginary
quadratic fields. -/
def IsImaginaryQuadraticDiscriminant (D : ℤ) : Prop :=
  D < 0 ∧ (D % 4 = 0 ∨ D % 4 = 1)

/-- The imaginary quadratic order in `ℂ` associated with an imaginary quadratic
discriminant `D`: it is generated as a subring of `ℂ` by `ω_D = (D + √|D| · i)/2`,
the standard generator of the unique order of discriminant `D` in `ℚ(√D)`. -/
noncomputable def imaginaryQuadraticOrder (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    Subring ℂ :=

  let sqrtAbsD : ℝ := Real.sqrt ((-D : ℤ) : ℝ)
  let ωD : ℂ := ((D : ℂ) + ↑sqrtAbsD * Complex.I) / 2
  Subring.closure {ωD}

/-- The finite set `Ell_𝒪(ℂ) = {j(E) : End(E) ≃ 𝒪}` of `j`-invariants of complex
elliptic curves with CM by the order `𝒪` of discriminant `D`. These are the roots
of the Hilbert class polynomial `H_D(X)`, indexed by the ideal class group of `𝒪`. -/
noncomputable def CMjInvariants (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) : Finset ℂ :=
  let 𝒪 := imaginaryQuadraticOrder D hD
  haveI : Finite (ComplexLattice.IdealClassGroup 𝒪) := ComplexLattice.IdealClassGroup.finite 𝒪
  haveI : Fintype (ComplexLattice.IdealClassGroup 𝒪) := Fintype.ofFinite _
  Finset.univ.image (fun c : ComplexLattice.IdealClassGroup 𝒪 =>
    (Quotient.out c).val.jInvariantLattice)

/-- The set `Ell_𝒪(ℂ)` of CM `j`-invariants is nonempty (every imaginary quadratic
order has at least one ideal class, so it has at least one CM `j`-invariant). -/
theorem CMjInvariants_nonempty (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    (CMjInvariants D hD).Nonempty := by
  let 𝒪 := imaginaryQuadraticOrder D hD
  letI : Finite (ComplexLattice.IdealClassGroup 𝒪) :=
    ComplexLattice.IdealClassGroup.finite 𝒪
  letI : Fintype (ComplexLattice.IdealClassGroup 𝒪) := Fintype.ofFinite _
  letI : CommGroup (ComplexLattice.IdealClassGroup 𝒪) :=
    ComplexLattice.IdealClassGroup.commGroup 𝒪
  exact Finset.Nonempty.image Finset.univ_nonempty _

/-- The Hilbert class polynomial `H_D(X) := ∏_{j ∈ Ell_𝒪(ℂ)} (X - j) ∈ ℂ[X]`
of an imaginary quadratic discriminant `D`. Its roots are precisely the
`j`-invariants of complex elliptic curves with CM by the order of discriminant `D`.
(Cf. Theorem 20.12: the coefficients are actually integers.) -/
def hilbertClassPoly (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) : ℂ[X] :=
  (CMjInvariants D hD).prod (fun j => X - C j)

/-- The Hilbert class polynomial `H_D` is monic, being a product of monic linear
factors `X - j`. -/
theorem hilbertClassPoly_monic (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    (hilbertClassPoly D hD).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ monic_X_sub_C _

/-- The natural degree of the Hilbert class polynomial equals the number of CM
`j`-invariants of discriminant `D` (which equals the class number `h(D)`). -/
theorem hilbertClassPoly_natDegree (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    (hilbertClassPoly D hD).natDegree = (CMjInvariants D hD).card := by
  rw [hilbertClassPoly, natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C j)]
  simp

/-- The classical modular polynomial `Φ_N(X, Y) ∈ ℤ[X][Y]` (Definition 19.15 /
Theorem 19.17): the minimal polynomial of `j_N(τ) := j(Nτ)` over `ℂ(j)`, viewed
as a bivariate polynomial with integer coefficients. -/
noncomputable def classicalModularPoly (N : ℕ) : Polynomial (Polynomial ℤ) := by sorry

/-- The diagonal `Φ_N(X, X)` of the classical modular polynomial, obtained by
substituting `X` for the outer variable. For prime `N` this is a polynomial whose
leading term is `-X^{2N}` (Lemma 20.9). -/
noncomputable def classicalModularPolyDiag (N : ℕ) : Polynomial ℤ :=
  Polynomial.eval X (classicalModularPoly N)

/-- For prime `N`, the diagonal `Φ_N(X, X)` has natural degree `2N` (corresponds
to Lemma 20.9: the leading term is `-X^{2N}`). -/
theorem classicalModularPolyDiag_natDegree_eq (N : ℕ) (hN : Nat.Prime N) :
    (classicalModularPolyDiag N).natDegree = 2 * N := by sorry

/-- For prime `N`, the leading coefficient of `Φ_N(X, X)` is `-1` (Lemma 20.9). -/
theorem classicalModularPolyDiag_leadingCoeff_eq (N : ℕ) (hN : Nat.Prime N) :
    (classicalModularPolyDiag N).leadingCoeff = -1 := by sorry

/-- For prime `N`, the negation `-Φ_N(X, X)` is monic. Direct consequence of
Lemma 20.9 (leading coefficient is `-1`). -/
theorem neg_classicalModularPolyDiag_monic (N : ℕ) (hN : Nat.Prime N) :
    (-(classicalModularPolyDiag N)).Monic := by
  show (-(classicalModularPolyDiag N)).leadingCoeff = 1
  rw [leadingCoeff_neg, classicalModularPolyDiag_leadingCoeff_eq N hN]
  norm_num

/-- Every CM `j`-invariant `j ∈ Ell_𝒪(ℂ)` is a root of `-Φ_p(X, X)` for some prime
`p`. This expresses each CM `j`-invariant as a root of a monic integer polynomial
(supporting the proof that CM `j`-invariants are algebraic integers). -/
theorem CMjInvariant_root_of_negModularPolyDiag
    (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D)
    (j : ℂ) (hj : j ∈ CMjInvariants D hD) :
    ∃ (p : ℕ) (_ : Nat.Prime p),
      Polynomial.eval₂ (algebraMap ℤ ℂ) j (-(classicalModularPolyDiag p)) = 0 := by sorry

/-- Corollary 20.13: every CM `j`-invariant is an algebraic integer over `ℤ`.
Proved by exhibiting it as a root of the monic integer polynomial `-Φ_p(X, X)`. -/
theorem CMjInvariant_isIntegral (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D)
    (j : ℂ) (hj : j ∈ CMjInvariants D hD) : IsIntegral ℤ j := by

  obtain ⟨p, hp, hroot⟩ := CMjInvariant_root_of_negModularPolyDiag D hD j hj

  have hmonic : (-(classicalModularPolyDiag p)).Monic :=
    neg_classicalModularPolyDiag_monic p hp

  exact ⟨-(classicalModularPolyDiag p), hmonic, hroot⟩

/-- Each coefficient of the Hilbert class polynomial `H_D(X)` is a rational number.
Comes from Galois-equivariance of the coefficients (they are fixed by
`Gal(ℚ̄/ℚ)`), and is one of the two ingredients in Theorem 20.12. -/
theorem galoisAction_coeffs_rational
    (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) (n : ℕ) :
    ∃ q : ℚ, ((CMjInvariants D hD).prod (fun j => X - C j)).coeff n = (q : ℂ) := by sorry

/-- Restated form of `galoisAction_coeffs_rational`: each coefficient of `H_D(X)`
is rational. -/
theorem hilbertClassPoly_coeff_rational (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D)
    (n : ℕ) : ∃ q : ℚ, (hilbertClassPoly D hD).coeff n = (q : ℂ) :=

  galoisAction_coeffs_rational D hD n

/-- For a finite set `s ⊂ ℂ` of algebraic integers, each coefficient of the monic
product `∏_{j∈s} (X - j)` is itself an algebraic integer. Used as a lemma toward
proving `H_D ∈ ℤ[X]`. -/
lemma coeff_prod_X_sub_C_isIntegral (s : Finset ℂ) (hint : ∀ j ∈ s, IsIntegral ℤ j)
    (n : ℕ) : IsIntegral ℤ ((s.prod (fun j => X - C j)).coeff n) := by
  have heq : s.prod (fun j => X - C j) = s.prod (fun j => X + C (-j)) := by
    congr 1; ext j; simp [sub_eq_add_neg, map_neg]
  rw [heq]
  by_cases hn : n ≤ s.card
  · rw [Finset.prod_X_add_C_coeff s (fun j => -j) hn]
    apply IsIntegral.sum
    intro t ht
    apply IsIntegral.prod
    intro i hi
    exact (hint i ((Finset.mem_powersetCard.mp ht).1 hi)).neg
  · push Not at hn
    have hdeg : (s.prod (fun j => X + C (-j))).natDegree = s.card := by
      conv_lhs => rw [heq.symm]
      rw [natDegree_prod_of_monic _ _ (fun j _ => monic_X_sub_C j)]
      simp
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact isIntegral_zero

/-- Theorem 20.12: the Hilbert class polynomial `H_D(X)` has integer coefficients,
i.e. lies in the image of `ℤ[X] → ℂ[X]`. Combines rationality of coefficients
with the fact that they are algebraic integers. -/
theorem hilbertClassPoly_int_coeffs (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    hilbertClassPoly D hD ∈ Polynomial.lifts (Int.castRingHom ℂ) := by
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n


  have hint : IsIntegral ℤ ((hilbertClassPoly D hD).coeff n) :=
    coeff_prod_X_sub_C_isIntegral _ (CMjInvariant_isIntegral D hD) n


  have hrat : ∃ q : ℚ, (hilbertClassPoly D hD).coeff n = (q : ℂ) :=
    hilbertClassPoly_coeff_rational D hD n

  have hZ : ∃ k : ℤ, (hilbertClassPoly D hD).coeff n = (k : ℂ) :=
    hint.exists_int_iff_exists_rat.mp hrat
  exact hZ.imp fun k hk => hk.symm

/-- Predicate: a complex number `j ∈ ℂ` is a CM `j`-invariant iff it appears in
`Ell_𝒪(ℂ)` for some imaginary quadratic order `𝒪` of discriminant `D`. -/
def IsCMjInvariant (j : ℂ) : Prop :=
  ∃ (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D), j ∈ CMjInvariants D hD

/-- Every CM `j`-invariant of discriminant `D` is a root of the Hilbert class
polynomial `H_D` (by construction, as `H_D` is the product over these roots). -/
theorem hilbertClassPoly_eval_eq_zero (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D)
    (j : ℂ) (hj : j ∈ CMjInvariants D hD) :
    Polynomial.eval j (hilbertClassPoly D hD) = 0 := by
  rw [hilbertClassPoly]
  simp only [eval_prod, Finset.prod_eq_zero_iff]
  exact ⟨j, hj, by simp⟩

/-- `IsRoot`-form of `hilbertClassPoly_eval_eq_zero`: every CM `j`-invariant is a
root of the Hilbert class polynomial. -/
theorem hilbertClassPoly_isRoot (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D)
    (j : ℂ) (hj : j ∈ CMjInvariants D hD) :
    (hilbertClassPoly D hD).IsRoot j :=
  hilbertClassPoly_eval_eq_zero D hD j hj

/-- Corollary 20.13 (general form): if `j ∈ ℂ` is the `j`-invariant of a complex
elliptic curve with complex multiplication, then `j` is an algebraic integer. -/
theorem cm_j_invariant_isIntegral (j : ℂ) (hcm : IsCMjInvariant j) : IsIntegral ℤ j := by
  obtain ⟨D, hD, hj⟩ := hcm

  have hlift := hilbertClassPoly_int_coeffs D hD

  have hmonic := hilbertClassPoly_monic D hD

  obtain ⟨q, hq_map, _, hq_monic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlift hmonic

  have hroot := hilbertClassPoly_eval_eq_zero D hD j hj

  exact ⟨q, hq_monic, by
    rw [Polynomial.eval₂_eq_eval_map]
    change Polynomial.eval j (Polynomial.map (Int.castRingHom ℂ) q) = 0
    rw [hq_map]
    exact hroot⟩

/-- The standard generator `ω_D := (D mod 2)/2 + i√|D|/2 ∈ ℂ` of the imaginary
quadratic order of discriminant `D`. -/
noncomputable def imagQuadGen (D : ℤ) : ℂ :=
  ⟨(D % 2 : ℤ) / 2, Real.sqrt ((-D : ℤ) : ℝ) / 2⟩

/-- Subring-of-`ℂ` version of the imaginary quadratic order of discriminant `D`:
the subring of `ℂ` generated by `imagQuadGen D`. -/
noncomputable def imagQuadOrder (D : ℤ) : Subring ℂ :=
  Subring.closure {imagQuadGen D}

/-- The ideal class group `cl(𝒪)` of the imaginary quadratic order of discriminant `D`. -/
def ImagQuadIdealClass (D : ℤ) (_hD : IsImaginaryQuadraticDiscriminant D) : Type :=
  ComplexLattice.IdealClassGroup (imagQuadOrder D)

/-- The number of CM `j`-invariants `Ell_𝒪(ℂ)` of discriminant `D` equals the
class number `|cl(𝒪)|` (cardinality of the ideal class group). -/
theorem CMjInvariants_card_eq_classNumber
    (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    (CMjInvariants D hD).card = Nat.card (ImagQuadIdealClass D hD) := by sorry

/-- The type of proper (invertible) `𝒪`-ideals for the imaginary quadratic order
of discriminant `D`. -/
noncomputable def ImagQuadProperIdeal (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) : Type := by sorry

/-- The (absolute) norm `N(𝔞)` of a proper `𝒪`-ideal `𝔞`, viewed as a natural number. -/
noncomputable def ImagQuadProperIdeal.norm {D : ℤ} {hD : IsImaginaryQuadraticDiscriminant D}
    (a : ImagQuadProperIdeal D hD) : ℕ := by sorry

/-- The ideal class in `cl(𝒪)` of a proper `𝒪`-ideal `𝔞`. -/
noncomputable def ImagQuadProperIdeal.idealClass {D : ℤ} {hD : IsImaginaryQuadraticDiscriminant D}
    (a : ImagQuadProperIdeal D hD) : ImagQuadIdealClass D hD := by sorry

/-- The norm of any proper `𝒪`-ideal is a positive natural number. -/
theorem ImagQuadProperIdeal.norm_pos {D : ℤ} {hD : IsImaginaryQuadraticDiscriminant D}
    (a : ImagQuadProperIdeal D hD) : 0 < a.norm := by sorry

/-- Theorem 20.11: every ideal class in `cl(𝒪)` of an imaginary quadratic order
contains infinitely many proper ideals of prime norm. -/
theorem ImagQuadIdealClass.infinite_prime_norm
  (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D)
  (c : ImagQuadIdealClass D hD) :
  Set.Infinite {a : ImagQuadProperIdeal D hD | a.idealClass = c ∧ Nat.Prime a.norm} := by sorry

/-- The commutative group structure on the ideal class group `cl(𝒪)` of an
imaginary quadratic order. -/
@[reducible] noncomputable def instCommGroupImagQuadIdealClass
    (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    CommGroup (ImagQuadIdealClass D hD) :=
  ComplexLattice.IdealClassGroup.commGroup (imagQuadOrder D)

/-- Typeclass-level commutative group instance on `cl(𝒪)`. -/
noncomputable instance (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    CommGroup (ImagQuadIdealClass D hD) := instCommGroupImagQuadIdealClass D hD

/-- The bijection between the ideal class group `cl(𝒪)` and the set of CM
`j`-invariants `Ell_𝒪(ℂ)` of discriminant `D` (the action of `cl(𝒪)` is simply
transitive on `Ell_𝒪(ℂ)`). -/
noncomputable def classGroupToCMjInvariantsBijection
    (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    ImagQuadIdealClass D hD ≃ ↥(CMjInvariants D hD) := by sorry

/-- The action homomorphism `cl(𝒪) → Sym(Ell_𝒪(ℂ))` arising from the simply
transitive action by left multiplication, transported across the bijection
`cl(𝒪) ≃ Ell_𝒪(ℂ)`. -/
noncomputable def classGroupActionHom (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    ImagQuadIdealClass D hD →* Equiv.Perm ↥(CMjInvariants D hD) :=
  let e := classGroupToCMjInvariantsBijection D hD
  { toFun := fun a => e.permCongr (Equiv.mulLeft a)
    map_one' := by
      ext x; simp [Equiv.permCongr_apply]
    map_mul' := fun a b => by
      ext x; simp [Equiv.permCongr_apply] }

/-- The image of `Gal(L/K)` in `Sym(Ell_𝒪(ℂ))`, where `L` is the splitting field
of `H_D(X)` over `K = ℚ(√D)` (i.e. the ring class field). The Galois group acts on
the roots of `H_D`, which are the CM `j`-invariants. -/
noncomputable def SplittingFieldGaloisSubgroup (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    Subgroup (Equiv.Perm ↥(CMjInvariants D hD)) := by sorry

/-- Theorem 20.14 (containment): the Galois group `Gal(L/K)` (acting on CM
`j`-invariants) lands inside the image of the class group action. -/
theorem galoisSubgroup_le_classGroupRange (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    SplittingFieldGaloisSubgroup D hD ≤ (classGroupActionHom D hD).range := by sorry

/-- Abbreviation for the Galois group of the splitting field of `H_D(X)` over
`K = ℚ(√D)`, realized as the subgroup of `Sym(Ell_𝒪(ℂ))`. -/
abbrev SplittingFieldGaloisGroup (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) : Type :=
  ↥(SplittingFieldGaloisSubgroup D hD)

/-- The group structure on the Galois group `Gal(L/K)`, inherited from
`Equiv.Perm`. -/
instance instGroupSplittingFieldGaloisGroup (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    Group (SplittingFieldGaloisGroup D hD) := inferInstance

/-- Transitivity of the class group action on CM `j`-invariants: for any pair of
CM `j`-invariants `j₁, j₂` there is `α ∈ cl(𝒪)` sending `j₁` to `j₂`. -/
theorem classGroupAction_transitive (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D)
    (j₁ j₂ : ↥(CMjInvariants D hD)) :
    ∃ α : ImagQuadIdealClass D hD, classGroupActionHom D hD α j₁ = j₂ := by
  let e := classGroupToCMjInvariantsBijection D hD
  refine ⟨e.symm j₂ * (e.symm j₁)⁻¹, ?_⟩


  have key : ∀ (α : ImagQuadIdealClass D hD) (j : ↥(CMjInvariants D hD)),
      classGroupActionHom D hD α j = e (α * e.symm j) := fun _ _ => rfl
  rw [key, mul_assoc, inv_mul_cancel, mul_one, Equiv.apply_symm_apply]

/-- The class group action homomorphism `cl(𝒪) → Sym(Ell_𝒪(ℂ))` is injective.
This is the freeness half of the simple transitivity of the action. -/
theorem classGroupActionHom_injective
    (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    Function.Injective (classGroupActionHom D hD) := by
  intro a b h

  unfold classGroupActionHom at h
  simp only [MonoidHom.coe_mk, OneHom.coe_mk] at h

  have h1 := (classGroupToCMjInvariantsBijection D hD).permCongr.injective h

  have h2 := Equiv.ext_iff.mp h1 1
  simp [Equiv.mulLeft] at h2
  exact h2

/-- Underlying function `Ψ_fun : Gal(L/K) → cl(𝒪)` of the homomorphism `Ψ`
appearing in Theorem 20.14: given `σ ∈ Gal(L/K)`, pick a base CM `j`-invariant
`j₀` and define `Ψ(σ)` to be the unique class group element sending `j₀ ↦ σ(j₀)`. -/
noncomputable def GalToClassGroup_fun (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D)
    (σ : SplittingFieldGaloisGroup D hD) : ImagQuadIdealClass D hD :=
  let j₀ : ↥(CMjInvariants D hD) :=
    ⟨(CMjInvariants_nonempty D hD).choose,
     Finset.mem_coe.mpr (CMjInvariants_nonempty D hD).choose_spec⟩
  Classical.choose (classGroupAction_transitive D hD j₀
    ((σ : Equiv.Perm ↥(CMjInvariants D hD)) j₀))

/-- Compatibility lemma: the action of `σ ∈ Gal(L/K)` on `Ell_𝒪(ℂ)` agrees with
the action of the class group element `Ψ_fun(σ)`, not just on a single base point
but as a permutation. -/
theorem GalToClassGroup_fun_compatible (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D)
    (σ : SplittingFieldGaloisGroup D hD) :
    (σ : Equiv.Perm ↥(CMjInvariants D hD)) =
      classGroupActionHom D hD (GalToClassGroup_fun D hD σ) := by

  have hrange := galoisSubgroup_le_classGroupRange D hD σ.2
  rw [MonoidHom.mem_range] at hrange
  obtain ⟨g, hg⟩ := hrange

  suffices h_eq : GalToClassGroup_fun D hD σ = g by rw [h_eq]; exact hg.symm

  let j₀ : ↥(CMjInvariants D hD) :=
    ⟨(CMjInvariants_nonempty D hD).choose,
     Finset.mem_coe.mpr (CMjInvariants_nonempty D hD).choose_spec⟩


  have hα : classGroupActionHom D hD (GalToClassGroup_fun D hD σ) j₀ =
      (σ : Equiv.Perm ↥(CMjInvariants D hD)) j₀ :=
    Classical.choose_spec (classGroupAction_transitive D hD j₀
      ((σ : Equiv.Perm ↥(CMjInvariants D hD)) j₀))

  have hg_j₀ : classGroupActionHom D hD g j₀ =
      (σ : Equiv.Perm ↥(CMjInvariants D hD)) j₀ := by rw [hg]

  have h_eq_j₀ : classGroupActionHom D hD (GalToClassGroup_fun D hD σ) j₀ =
      classGroupActionHom D hD g j₀ := by rw [hα, hg_j₀]

  let e := classGroupToCMjInvariantsBijection D hD

  change e.permCongr (Equiv.mulLeft (GalToClassGroup_fun D hD σ)) j₀ =
    e.permCongr (Equiv.mulLeft g) j₀ at h_eq_j₀
  simp only [Equiv.permCongr_apply, Equiv.coe_mulLeft] at h_eq_j₀

  exact mul_right_cancel (e.injective h_eq_j₀)

/-- The group homomorphism `Ψ : Gal(L/K) → cl(𝒪)` of Theorem 20.14, packaging
`GalToClassGroup_fun` together with the multiplicative structure (`map_one`,
`map_mul` are derived from compatibility). -/
noncomputable def GalToClassGroup_hom (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    SplittingFieldGaloisGroup D hD →* ImagQuadIdealClass D hD where
  toFun := GalToClassGroup_fun D hD
  map_one' := by


    apply classGroupActionHom_injective D hD
    have h := GalToClassGroup_fun_compatible D hD 1
    simp only [Subgroup.coe_one, map_one] at h ⊢
    exact h.symm
  map_mul' σ τ := by

    apply classGroupActionHom_injective D hD
    have h1 := GalToClassGroup_fun_compatible D hD (σ * τ)
    rw [map_mul, ← GalToClassGroup_fun_compatible D hD σ,
        ← GalToClassGroup_fun_compatible D hD τ, ← h1]
    simp only [Subgroup.coe_mul]

/-- Restated compatibility through the bundled homomorphism `Ψ`: the action of
`σ` on `Ell_𝒪(ℂ)` is the same as the action of `Ψ(σ) ∈ cl(𝒪)`. -/
theorem GalToClassGroup_compatible (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D)
    (σ : SplittingFieldGaloisGroup D hD) :
    (σ : Equiv.Perm ↥(CMjInvariants D hD)) = classGroupActionHom D hD (GalToClassGroup_hom D hD σ) :=
  GalToClassGroup_fun_compatible D hD σ

/-- Injectivity half of Theorem 20.14: the homomorphism `Ψ : Gal(L/K) → cl(𝒪)` is
injective. -/
theorem GalToClassGroup_injective (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    Function.Injective (GalToClassGroup_hom D hD) := by
  intro σ₁ σ₂ hΨ

  have hperm : (σ₁ : Equiv.Perm ↥(CMjInvariants D hD)) =
      (σ₂ : Equiv.Perm ↥(CMjInvariants D hD)) := by
    rw [GalToClassGroup_compatible D hD σ₁, GalToClassGroup_compatible D hD σ₂, hΨ]

  exact Subtype.val_injective hperm

/-- Characterization of roots of `H_D`: `z ∈ ℂ` is a root of the Hilbert class
polynomial iff `z ∈ Ell_𝒪(ℂ)`. Direct from the factored form `∏_{j} (X - j)`. -/
theorem hilbertClassPoly_isRoot_iff (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D)
    (z : ℂ) :
    (hilbertClassPoly D hD).IsRoot z ↔ z ∈ CMjInvariants D hD := by
  simp only [hilbertClassPoly, IsRoot, eval_prod, Finset.prod_eq_zero_iff,
    eval_sub, eval_X, eval_C, sub_eq_zero]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ha
  · intro h; exact ⟨z, h, rfl⟩

/-- Evaluation `Φ_N(j₁, j₂)` of the classical modular polynomial at a pair of
complex `j`-invariants `(j₁, j₂)`. -/
def evalClassicalModularPoly (N : ℕ) (j₁ j₂ : ℂ) : ℂ :=
  Polynomial.eval j₂
    (Polynomial.map (Polynomial.eval₂RingHom (algebraMap ℤ ℂ) j₁) (classicalModularPoly N))

/-- Predicate: complex `j`-invariants `j₁, j₂` are related by a cyclic `N`-isogeny.
Equivalently (by Theorem 20.3) one of `Φ_N(j₁, j₂) = 0` characterizations. -/
def AreCyclicNIsogenous (j₁ j₂ : ℂ) (N : ℕ) : Prop :=
  ∃ (E₁ E₂ : WeierstrassCurve.Affine ℂ) (_ : E₁.IsElliptic) (_ : E₂.IsElliptic),
    E₁.j = j₁ ∧ E₂.j = j₂ ∧
    ∃ (φ : E₁.Point →+ E₂.Point), Function.Surjective φ ∧

      ∃ (P : E₁.Point), addOrderOf P = N ∧
        ∀ Q : E₁.Point, φ Q = 0 → ∃ k : ℤ, Q = k • P

/-- Theorem 20.3 (over `ℂ`): `Φ_N(j₁, j₂) = 0` iff `j₁, j₂` are the `j`-invariants
of complex elliptic curves related by a cyclic isogeny of degree `N`. -/
theorem modularPoly_characterizes_cyclicIsogeny
    (N : ℕ) (j₁ j₂ : ℂ) :
    evalClassicalModularPoly N j₁ j₂ = 0 ↔ AreCyclicNIsogenous j₁ j₂ N := by sorry

/-- Theorem 20.7: the classical modular polynomial is symmetric in its two
variables, i.e. `Φ_N(X, Y) = Φ_N(Y, X)`. -/
theorem classicalModularPoly_symmetric (N : ℕ) (hN : 1 < N) :
    Polynomial.Bivariate.swap (classicalModularPoly N) = classicalModularPoly N := by sorry

/-- Coercion of `evalClassicalModularPoly` to the `aevalAeval` API: both compute
`Φ_N(j₁, j₂)` in `ℂ` via the same iterated evaluation, so they agree. -/
lemma evalClassicalModularPoly_eq_aevalAeval (N : ℕ) (j₁ j₂ : ℂ) :
    evalClassicalModularPoly N j₁ j₂ =
    Polynomial.aevalAeval j₁ j₂ (classicalModularPoly N) := by
  simp only [evalClassicalModularPoly, eval_map]
  have : (Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (algebraMap ℤ ℂ) j₁) j₂ :
      Polynomial (Polynomial ℤ) →+* ℂ) =
      (Polynomial.aevalAeval j₁ j₂ :
        Polynomial (Polynomial ℤ) →ₐ[ℤ] ℂ).toRingHom := by
    ext p
    · simp [algebraMap_int_eq]
    · simp [eval₂_C, eval₂_X]
    · simp [eval₂_X]
  exact RingHom.congr_fun this _

/-- Existence of Frobenius-type elements: for every ideal class `α ∈ cl(𝒪)`, some
Galois element `σ ∈ Gal(L/K)` acts on `Ell_𝒪(ℂ)` exactly via `α` under the class
group action. (Surjectivity of `Ψ` follows.) -/
theorem frobeniusElement_exists (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D)
    (α : ImagQuadIdealClass D hD) :
    ∃ σ : SplittingFieldGaloisGroup D hD,
      (σ : Equiv.Perm ↥(CMjInvariants D hD)) = classGroupActionHom D hD α := by sorry

/-- Compatibility: if `σ ∈ Gal(L/K)` acts as the class group element `α`, then
`Ψ(σ) = α`. -/
theorem frobeniusElement_mapsTo (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D)
    (σ : SplittingFieldGaloisGroup D hD) (α : ImagQuadIdealClass D hD)
    (hσ : (σ : Equiv.Perm ↥(CMjInvariants D hD)) = classGroupActionHom D hD α) :
    GalToClassGroup_hom D hD σ = α := by sorry

/-- Surjectivity half of Theorem 20.14 / Theorem 21.1: every class group element
is hit by some Galois element under `Ψ : Gal(L/K) → cl(𝒪)`. -/
theorem GalToClassGroup_surjective (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    Function.Surjective (GalToClassGroup_hom D hD) := by
  intro α
  obtain ⟨σ, hσ⟩ := frobeniusElement_exists D hD α
  exact ⟨σ, frobeniusElement_mapsTo D hD σ α hσ⟩

/-- Theorem 21.1: the homomorphism `Ψ : Gal(L/K) → cl(𝒪)` is a bijection. -/
theorem GalToClassGroup_bijective (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    Function.Bijective (GalToClassGroup_hom D hD) :=
  ⟨GalToClassGroup_injective D hD, GalToClassGroup_surjective D hD⟩

/-- Theorem 21.1 (packaged): the multiplicative equivalence
`Gal(L/K) ≃* cl(𝒪)` obtained by promoting `Ψ` to an iso. -/
def GalToClassGroup_mulEquiv (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    SplittingFieldGaloisGroup D hD ≃* ImagQuadIdealClass D hD :=
  MulEquiv.ofBijective (GalToClassGroup_hom D hD) (GalToClassGroup_bijective D hD)

/-- Galois transitivity on the roots of `H_D`: for any two CM `j`-invariants
`j₁, j₂`, there exists `σ ∈ Gal(L/K)` with `σ(j₁) = j₂`. Follows from transitivity
of the class group action together with surjectivity of `Ψ`. -/
theorem galoisAction_transitive_on_roots (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D)
    (j₁ j₂ : ↥(CMjInvariants D hD)) :
    ∃ σ : SplittingFieldGaloisGroup D hD,
      (σ : Equiv.Perm ↥(CMjInvariants D hD)) j₁ = j₂ := by


  obtain ⟨α, hα⟩ := classGroupAction_transitive D hD j₁ j₂


  obtain ⟨σ, hσ⟩ := GalToClassGroup_surjective D hD α


  have hperm : (σ : Equiv.Perm ↥(CMjInvariants D hD)) = classGroupActionHom D hD α := by
    rw [GalToClassGroup_compatible D hD σ, hσ]
  exact ⟨σ, hperm ▸ hα⟩

/-- The Galois group `Gal(L/K)` is abelian: it is isomorphic to the ideal class
group `cl(𝒪)`, which is abelian (Corollary 21.2). -/
theorem splittingFieldGaloisGroup_mul_comm (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D)
    (σ₁ σ₂ : SplittingFieldGaloisGroup D hD) : σ₁ * σ₂ = σ₂ * σ₁ := by
  have hinj := GalToClassGroup_injective D hD
  exact hinj (by rw [map_mul, map_mul, mul_comm])

/-- The commutative-group instance on `Gal(L/K)`: extending the group structure
with commutativity proved in `splittingFieldGaloisGroup_mul_comm`. -/
@[reducible] def instCommGroupSplittingFieldGaloisGroup' (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    CommGroup (SplittingFieldGaloisGroup D hD) :=
  { instGroupSplittingFieldGaloisGroup D hD with
    mul_comm := splittingFieldGaloisGroup_mul_comm D hD }

/-- Corollary 21.2 (formal content): the Hilbert class polynomial `H_D(X)` is
irreducible over `K = ℚ(√D)` (encoded as transitivity of the Galois action on its
roots) and `K(j(E))/K` is a finite abelian extension with Galois group isomorphic
to `cl(𝒪)`. -/
theorem hilbertClassPoly_irreducible_and_abelian_galois
    (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    (∀ j₁ j₂ : ↥(CMjInvariants D hD),
      ∃ σ : SplittingFieldGaloisGroup D hD,
        (σ : Equiv.Perm ↥(CMjInvariants D hD)) j₁ = j₂) ∧
    ∃ (_ : CommGroup (SplittingFieldGaloisGroup D hD)),
      Nonempty (SplittingFieldGaloisGroup D hD ≃* ImagQuadIdealClass D hD) :=
  ⟨galoisAction_transitive_on_roots D hD,
   instCommGroupSplittingFieldGaloisGroup' D hD,
   ⟨GalToClassGroup_mulEquiv D hD⟩⟩

end

namespace HilbertClassPolynomial

open Polynomial

/-- Theorem 20.12 (computational form): an integer polynomial `intPoly D` whose
image in `ℂ[X]` equals the Hilbert class polynomial `H_D(X)`, and which is monic
of the same degree. Chosen using `Polynomial.lifts_and_natDegree_eq_and_monic`. -/
noncomputable def intPoly (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) : Polynomial ℤ :=
  (Polynomial.lifts_and_natDegree_eq_and_monic
    (hilbertClassPoly_int_coeffs D hD) (hilbertClassPoly_monic D hD)).choose

/-- The integer-coefficient form `intPoly D` has the same natural degree as
`H_D(X)` (i.e. the class number `h(D)`). -/
theorem intPoly_natDegree (D : ℤ) (hD : IsImaginaryQuadraticDiscriminant D) :
    (intPoly D hD).natDegree = (hilbertClassPoly D hD).natDegree :=
  (Polynomial.lifts_and_natDegree_eq_and_monic
    (hilbertClassPoly_int_coeffs D hD) (hilbertClassPoly_monic D hD)).choose_spec.2.1

end HilbertClassPolynomial
