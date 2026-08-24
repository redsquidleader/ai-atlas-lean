/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.EllipticCurves.code.Isogenies

noncomputable section GaloisRepInfra

open Matrix CongruenceSubgroup

/-- The algebraic closure of `ℚ` inside `ℂ`, viewed as an intermediate field. This
provides a concrete model of `ℚ̄` sitting inside `ℂ`. -/
abbrev Qbar : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

/-- The absolute Galois group of `ℚ`, realized as the group of `ℚ`-algebra
automorphisms of `Qbar`. -/
abbrev AbsGaloisGroupQ := ↥Qbar ≃ₐ[ℚ] ↥Qbar

/-- A mod-`ℓ` Galois representation is a group homomorphism from the absolute Galois
group of `ℚ` to `GL₂(ℤ/ℓℤ)`. -/
abbrev GaloisRepMod (ℓ : ℕ) := AbsGaloisGroupQ →* GL (Fin 2) (ZMod ℓ)

/-- A specific element of the absolute Galois group of `ℚ` realizing complex
conjugation on `Qbar ⊆ ℂ`. -/
noncomputable def complexConjugation : AbsGaloisGroupQ := by sorry

/-- A mod-`ℓ` Galois representation `ρ` is *odd* if `det(ρ(c)) = -1`, where `c` is
complex conjugation. -/
def GaloisRepMod.IsOdd {ℓ : ℕ} (ρ : GaloisRepMod ℓ) : Prop :=
  GeneralLinearGroup.det (ρ complexConjugation) = -1

/-- A mod-`ℓ` Galois representation is *irreducible* if no nonzero vector
`v ∈ (ℤ/ℓℤ)²` is simultaneously an eigenvector of every `ρ(g)`. -/
def GaloisRepMod.IsIrreducible {ℓ : ℕ} (ρ : GaloisRepMod ℓ) : Prop :=
  ∀ (v : Fin 2 → ZMod ℓ), v ≠ 0 →
    ¬∀ (g : AbsGaloisGroupQ),
      ∃ (c : ZMod ℓ), (↑(ρ g) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) *ᵥ v = c • v

/-- An element of the absolute Galois group realizing a Frobenius at the prime `p`. -/
noncomputable def frobeniusElement (p : ℕ) (hp : Nat.Prime p) : AbsGaloisGroupQ := by sorry

/-- A mod-`ℓ` Galois representation `ρ` is *modular* if there exists a cusp form
`f` of some weight `k` and level `Γ₁(N)`, with integer Fourier coefficients
`a(n)`, such that for every prime `p` not dividing `ℓN` the trace of `ρ(Frob_p)`
equals `a(p) mod ℓ`. -/
def GaloisRepMod.IsModular {ℓ : ℕ} (ρ : GaloisRepMod ℓ) : Prop :=
  ∃ (N : ℕ) (k : ℤ) (_ : 0 < N) (_ : 0 < k)
    (f : CuspForm (Gamma1 N : Subgroup (GL (Fin 2) ℝ)) k)
    (a : ℕ → ℤ),

    (∀ n : ℕ, (ModularFormClass.qExpansion 1 (⇑f)).coeff n = (a n : ℂ)) ∧

    (∀ (p : ℕ) (hp : Nat.Prime p), ¬(p ∣ ℓ * N) →
      (↑(ρ (frobeniusElement p hp)) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).trace =
        (a p : ZMod ℓ))

end GaloisRepInfra

noncomputable section

namespace FLT

/-- An elliptic curve over `ℚ`: a Weierstrass curve in affine form together with a
proof that it satisfies the elliptic (nonsingular) condition. -/
abbrev EllipticCurveOverQ := { E : WeierstrassCurve.Affine ℚ // E.IsElliptic }

open UniqueFactorizationMonoid

/-- The minimal discriminant of an elliptic curve over `ℚ`: the discriminant of a
global minimal Weierstrass model. -/
noncomputable def minimalDiscriminant (E : EllipticCurveOverQ) : ℤ := by sorry

/-- The minimal discriminant of an elliptic curve over `ℚ` is nonzero (consequence
of nonsingularity of the global minimal model). -/
theorem minimalDiscriminant_ne_zero (E : EllipticCurveOverQ) : minimalDiscriminant E ≠ 0 := by sorry

/-- The conductor of an elliptic curve over `ℚ`, defined here as the radical of the
absolute value of the minimal discriminant. -/
noncomputable def conductor (E : EllipticCurveOverQ) : ℕ :=
  radical (minimalDiscriminant E).natAbs

/-- The conductor of any elliptic curve over `ℚ` is strictly positive. -/
theorem conductor_pos (E : EllipticCurveOverQ) : 0 < conductor E :=
  Nat.radical_pos _

/-- An elliptic curve over `ℚ` is *semistable* if it has no additive reduction at any
prime — equivalently, all bad reduction is multiplicative. -/
def IsSemistable (E : EllipticCurveOverQ) : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R ℚ] [IsFractionRing R ℚ],
    ¬ (E.val.minimal R).HasAdditiveReduction R

/-- An elliptic curve over `ℚ` is semistable iff its conductor is squarefree. -/
theorem isSemistable_iff_squarefree_conductor (E : EllipticCurveOverQ) :
    IsSemistable E ↔ Squarefree (conductor E) := by sorry

/-- `E` admits a rational cyclic `n`-isogeny: there is a `ℚ`-rational isogeny from
`E` whose kernel is cyclic of order `n`. -/
noncomputable def AdmitsRationalCyclicIsogeny (E : EllipticCurveOverQ) (n : ℕ) : Prop := by sorry

/-- If `E/ℚ` admits a rational cyclic `15`-isogeny then its conductor is not
squarefree. -/
theorem conductor_not_squarefree_of_admits_15_isogeny
    (E : EllipticCurveOverQ)
    (h : AdmitsRationalCyclicIsogeny E 15) :
    ¬ Squarefree (conductor E) := by sorry

/-- An elliptic curve admitting a rational cyclic `15`-isogeny cannot be semistable.
This follows from squarefree-conductor characterization of semistability. -/
theorem not_semistable_of_admits_15_isogeny
    (E : EllipticCurveOverQ)
    (h : AdmitsRationalCyclicIsogeny E 15) :
    ¬ IsSemistable E := by
  intro hss
  have hnsq := conductor_not_squarefree_of_admits_15_isogeny E h
  exact hnsq ((isSemistable_iff_squarefree_conductor E).mp hss)

/-- A semistable elliptic curve over `ℚ` admits no rational cyclic `15`-isogeny. -/
theorem no_semistable_rational_15_isogeny
    (E : EllipticCurveOverQ)
    (hss : IsSemistable E)
    (hiso : AdmitsRationalCyclicIsogeny E 15) :
    False :=
  not_semistable_of_admits_15_isogeny E hiso hss

/-- The mod-`ℓ` Galois representation attached to an elliptic curve `E/ℚ`, obtained
from the Galois action on the `ℓ`-torsion `E[ℓ]`. -/
noncomputable def galoisRepMod_of_EC (E : EllipticCurveOverQ) (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
    GaloisRepMod ℓ := by sorry

/-- The mod-`ℓ` representation attached to an elliptic curve `E/ℚ` is irreducible. -/
def ModLGaloisRepIsIrreducible
    (E : EllipticCurveOverQ) (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : Prop :=
  (galoisRepMod_of_EC E ℓ).IsIrreducible

/-- The mod-`ℓ` representation attached to an elliptic curve `E/ℚ` is modular. -/
def ModLGaloisRepIsModular
    (E : EllipticCurveOverQ) (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : Prop :=
  (galoisRepMod_of_EC E ℓ).IsModular

/-- The Dirichlet coefficients `a_n` of the `L`-series of `E/ℚ`. -/
noncomputable def LSeriesCoeff (E : EllipticCurveOverQ) : ℕ → ℤ := by sorry

/-- A weight-`2` newform of level `N`, specified by its Fourier coefficients:
normalized so that `a₁ = 1`, multiplicative on coprime indices, and satisfying the
standard Hecke recursion at primes `p ∤ N`. -/
structure Weight2Newform (N : ℕ) where
  coeff : ℕ → ℤ
  coeff_one : coeff 1 = 1
  coeff_mult : ∀ m n : ℕ, Nat.Coprime m n → coeff (m * n) = coeff m * coeff n
  coeff_prime_power : ∀ (p : ℕ) (r : ℕ), Nat.Prime p → ¬(p ∣ N) → r ≥ 1 →
    coeff (p ^ (r + 1)) = coeff p * coeff (p ^ r) - (p : ℤ) * coeff (p ^ (r - 1))

/-- The mod-`ℓ` representation of `E/ℚ` is modular of a prescribed weight and level:
there is a weight-`2` newform of the given level matching `tr ρ(Frob_p)` at primes
`p ∤ ℓ · level`. -/
def ModLGaloisRepIsModularOfWeightAndLevel
    (E : EllipticCurveOverQ) (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
    (weight : ℕ) (level : ℕ+) : Prop :=
  ∃ (f : Weight2Newform (level : ℕ)),
    weight = 2 ∧
    ∀ (p : ℕ) (hp : Nat.Prime p), ¬(p ∣ ℓ * (level : ℕ)) →
      (↑(galoisRepMod_of_EC E ℓ (frobeniusElement p hp)) :
        Matrix (Fin 2) (Fin 2) (ZMod ℓ)).trace = (f.coeff p : ZMod ℓ)

/-- The `ℓ`-adic Galois representation attached to `E/ℚ` is modular: there is a
weight-`2` newform of level equal to the conductor whose Fourier coefficients
match `a_p(E)` at primes `p ∤ ℓ · conductor`. -/
def LAdicGaloisRepIsModular
    (E : EllipticCurveOverQ) (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : Prop :=
  ∃ (f : Weight2Newform (conductor E)),
    ∀ (p : ℕ) (_hp : Nat.Prime p), ¬(p ∣ ℓ * conductor E) →
      f.coeff p = LSeriesCoeff E p

/-- `E/ℚ` is a *modular elliptic curve*: there is a weight-`2` newform of level the
conductor of `E` whose Fourier coefficients equal the `L`-series coefficients of
`E` for every `n ≥ 1`. -/
def IsModularEllipticCurve (E : EllipticCurveOverQ) : Prop :=
  ∃ f : Weight2Newform (conductor E),
    ∀ n : ℕ, n ≥ 1 → f.coeff n = LSeriesCoeff E n

/-- Taylor–Wiles modularity lifting: if `E/ℚ` is semistable and its mod-`ℓ`
representation is modular, then its `ℓ`-adic representation is modular and `E`
itself is a modular elliptic curve. -/
theorem taylor_wiles_modularity_lifting
    (E : EllipticCurveOverQ) (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
    (hss : IsSemistable E)
    (hmod : ModLGaloisRepIsModular E ℓ) :
    LAdicGaloisRepIsModular E ℓ ∧ IsModularEllipticCurve E := by sorry

/-- Ribet's level-lowering divisor: the product over primes `p ∥ N(E)` of those `p`
at which the mod-`ℓ` representation is unramified, i.e. `ℓ ∣ v_p(Δ_E)`. -/
noncomputable def ribetLevelDivisor (E : EllipticCurveOverQ) (ℓ : ℕ) : ℕ :=
  (Nat.primeFactors (conductor E)).prod fun p =>
    if (emultiplicity (p : ℕ) (conductor E) = 1) ∧
       (ℓ ∣ (emultiplicity (p : ℤ) (minimalDiscriminant E)).toNat)
    then p else 1

/-- The Ribet level divisor divides the conductor of `E`. -/
lemma ribetLevelDivisor_dvd (E : EllipticCurveOverQ) (ℓ : ℕ) :
    ribetLevelDivisor E ℓ ∣ conductor E := by
  simp only [ribetLevelDivisor]
  apply dvd_trans _ (Nat.prod_primeFactors_dvd _)
  apply Finset.prod_dvd_prod_of_dvd
  intro p _
  split_ifs <;> simp

/-- The Ribet level divisor is strictly positive. -/
lemma ribetLevelDivisor_pos (E : EllipticCurveOverQ) (ℓ : ℕ) :
    0 < ribetLevelDivisor E ℓ := by
  simp only [ribetLevelDivisor]
  apply Finset.prod_pos
  intro p hp
  split_ifs with h
  · exact Nat.pos_of_mem_primeFactors hp
  · exact Nat.zero_lt_one

/-- The level produced by Ribet's level-lowering theorem: the conductor of `E`
divided by the Ribet level divisor, as a positive natural number. -/
noncomputable def ribetLoweredLevel
    (E : EllipticCurveOverQ) (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : ℕ+ :=
  ⟨conductor E / ribetLevelDivisor E ℓ,
   Nat.div_pos (Nat.le_of_dvd (conductor_pos E) (ribetLevelDivisor_dvd E ℓ))
     (ribetLevelDivisor_pos E ℓ)⟩

/-- Ribet's level-lowering theorem: if `E/ℚ` is modular and the mod-`ℓ` representation
is irreducible, then the mod-`ℓ` representation is modular of weight `2` and level
equal to the Ribet-lowered level. -/
theorem ribet_level_lowering
    (E : EllipticCurveOverQ) (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
    (hmod : IsModularEllipticCurve E)
    (hirr : ModLGaloisRepIsIrreducible E ℓ) :
    ModLGaloisRepIsModularOfWeightAndLevel E ℓ 2 (ribetLoweredLevel E ℓ) := by sorry

/-- The Langlands–Tunnell theorem: if the mod-`3` representation of `E/ℚ` is
irreducible, then it is modular. -/
theorem langlands_tunnel
    (E : EllipticCurveOverQ)
    (hirr : ModLGaloisRepIsIrreducible E 3) :
    ModLGaloisRepIsModular E 3 := by sorry

/-- The Frey curve `y² = x(x - aᵉ)(x + bᵉ)` associated to a putative
counterexample `aᵉ + bᵉ = cᵉ` to Fermat's Last Theorem at prime exponent `ℓ`. -/
noncomputable def freyCurve (a b c : ℤ) (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : EllipticCurveOverQ := by sorry

/-- The Frey curve attached to a coprime Fermat triple is semistable. -/
theorem freyCurve_isSemistable (a b c : ℤ) (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
    (hflt : a ^ ℓ + b ^ ℓ = c ^ ℓ)
    (hcoprime : Int.gcd a (Int.gcd b c) = 1) :
    IsSemistable (freyCurve a b c ℓ) := by sorry

/-- Mazur's isogeny theorem: for primes `ℓ > 163`, no elliptic curve over `ℚ`
admits a rational cyclic `ℓ`-isogeny. -/
theorem mazur_isogeny_theorem
    (E : EllipticCurveOverQ) (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
    (hℓ : ℓ > 163) :
    ¬ AdmitsRationalCyclicIsogeny E ℓ := by sorry

/-- If the mod-`ℓ` Galois representation of `E/ℚ` is reducible, then `E` admits a
rational cyclic `ℓ`-isogeny (coming from a Galois-stable line in `E[ℓ]`). -/
theorem reducible_implies_rational_isogeny
    (E : EllipticCurveOverQ) (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
    (hred : ¬ ModLGaloisRepIsIrreducible E ℓ) :
    AdmitsRationalCyclicIsogeny E ℓ := by sorry

/-- The mod-`ℓ` representation of the Frey curve is irreducible (for `ℓ > 163`),
combining Mazur's isogeny theorem with the reducibility–isogeny correspondence. -/
theorem freyCurve_modLRep_irreducible (a b c : ℤ) (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
    (_hflt : a ^ ℓ + b ^ ℓ = c ^ ℓ)
    (hℓ_large : ℓ > 163) :
    ModLGaloisRepIsIrreducible (freyCurve a b c ℓ) ℓ := by
  by_contra hred
  exact mazur_isogeny_theorem (freyCurve a b c ℓ) ℓ hℓ_large
    (reducible_implies_rational_isogeny (freyCurve a b c ℓ) ℓ hred)

/-- For the Frey curve attached to a Fermat triple, Ribet's level-lowering produces
level `2`. -/
theorem freyCurve_ribetLoweredLevel_eq_two (a b c : ℤ) (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
    (hflt : a ^ ℓ + b ^ ℓ = c ^ ℓ)
    (hℓ_large : ℓ > 163) :
    ribetLoweredLevel (freyCurve a b c ℓ) ℓ = ⟨2, by norm_num⟩ := by sorry

/-- There is no weight-`2`, level-`2` cuspform: the space `S_2(Γ₀(2))` is zero, so no
elliptic curve has a mod-`ℓ` representation modular of weight `2` and level `2`. -/
theorem no_weight2_level2_modular_form
    (E : EllipticCurveOverQ) (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
    ¬ ModLGaloisRepIsModularOfWeightAndLevel E ℓ 2 ⟨2, by norm_num⟩ := by sorry

/-- The Frey curve attached to a Fermat triple is *not* modular: combining Ribet's
level-lowering with the nonexistence of weight-`2`, level-`2` newforms. -/
theorem freyCurve_not_modular (a b c : ℤ) (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
    (hflt : a ^ ℓ + b ^ ℓ = c ^ ℓ)
    (hℓ_large : ℓ > 163) :
    ¬ IsModularEllipticCurve (freyCurve a b c ℓ) := by
  intro hmod
  have hirr := freyCurve_modLRep_irreducible a b c ℓ hflt hℓ_large
  have hribet := ribet_level_lowering (freyCurve a b c ℓ) ℓ hmod hirr
  have hlevel := freyCurve_ribetLoweredLevel_eq_two a b c ℓ hflt hℓ_large
  rw [hlevel] at hribet
  exact no_weight2_level2_modular_form (freyCurve a b c ℓ) ℓ hribet

/-- `3` is a prime number. Provided as a `Fact` for use as a typeclass parameter. -/
instance : Fact (Nat.Prime 3) := ⟨by decide⟩
/-- `5` is a prime number. Provided as a `Fact` for use as a typeclass parameter. -/
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The mod-`ℓ` representations of two elliptic curves `E, E'` over `ℚ` are
isomorphic (at the level of traces): for every `g` in the absolute Galois group,
`tr ρ_E(g) = tr ρ_{E'}(g)`. -/
def ModLGaloisRepIsIsomorphic
    (E E' : EllipticCurveOverQ) (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : Prop :=
  ∀ (g : AbsGaloisGroupQ),
    (↑(galoisRepMod_of_EC E ℓ g) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).trace =
    (↑(galoisRepMod_of_EC E' ℓ g) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)).trace

/-- If the mod-`ℓ` representations of `E` and `E'` are isomorphic and `E`'s mod-`ℓ`
representation is modular, then so is `E'`'s. -/
theorem modLGaloisRep_modular_of_isomorphic
    (E E' : EllipticCurveOverQ) (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
    (hiso : ModLGaloisRepIsIsomorphic E E' ℓ)
    (hmod : ModLGaloisRepIsModular E ℓ) :
    ModLGaloisRepIsModular E' ℓ := by sorry

/-- For a semistable `E/ℚ` whose mod-`3` representation is reducible, the mod-`5`
representation is irreducible. (Used in the `3-5` trick.) -/
theorem reducible_mod3_implies_irreducible_mod5
    (E : EllipticCurveOverQ)
    (hss : IsSemistable E)
    (hred : ¬ ModLGaloisRepIsIrreducible E 3) :
    ModLGaloisRepIsIrreducible E 5 := by sorry

/-- If `E/ℚ` is a modular elliptic curve, then for any prime `ℓ` the mod-`ℓ`
representation of `E` is also modular. -/
theorem modular_implies_mod_rep_modular
    (E : EllipticCurveOverQ) (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
    (hmod : IsModularEllipticCurve E) :
    ModLGaloisRepIsModular E ℓ := by sorry

/-- Wiles's `3-5` trick: given a semistable `E/ℚ` whose mod-`5` representation is
irreducible, there exists a semistable `E'/ℚ` whose mod-`3` representation is
irreducible and whose mod-`5` representation is isomorphic to that of `E`. -/
theorem wiles_three_five_trick
    (E : EllipticCurveOverQ)
    (hss : IsSemistable E)
    (hirr5 : ModLGaloisRepIsIrreducible E 5) :
    ∃ E' : EllipticCurveOverQ,
      IsSemistable E' ∧
      ModLGaloisRepIsIrreducible E' 3 ∧
      ModLGaloisRepIsIsomorphic E' E 5 := by sorry

/-- Wiles's modularity theorem for semistable elliptic curves: every semistable
elliptic curve over `ℚ` is modular. Proof uses Langlands–Tunnell at the prime `3`
together with Wiles's `3-5` trick when the mod-`3` representation is reducible. -/
theorem wiles_modularity_semistable
    (E : EllipticCurveOverQ)
    (hss : IsSemistable E) :
    IsModularEllipticCurve E := by
  by_cases hirr3 : ModLGaloisRepIsIrreducible E 3
  ·
    have hmod3 : ModLGaloisRepIsModular E 3 := langlands_tunnel E hirr3
    exact (taylor_wiles_modularity_lifting E 3 hss hmod3).2
  ·
    have hirr5 : ModLGaloisRepIsIrreducible E 5 :=
      reducible_mod3_implies_irreducible_mod5 E hss hirr3

    obtain ⟨E', hss', hirr3', hiso⟩ :=
      wiles_three_five_trick E hss hirr5

    have hmodE'3 : ModLGaloisRepIsModular E' 3 := langlands_tunnel E' hirr3'

    have hmodE' : IsModularEllipticCurve E' :=
      (taylor_wiles_modularity_lifting E' 3 hss' hmodE'3).2

    have hmodE'5 : ModLGaloisRepIsModular E' 5 :=
      modular_implies_mod_rep_modular E' 5 hmodE'

    have hmodE5 : ModLGaloisRepIsModular E 5 :=
      modLGaloisRep_modular_of_isomorphic E' E 5 hiso hmodE'5
    exact (taylor_wiles_modularity_lifting E 5 hss hmodE5).2

/-- Wiles's modularity theorem for semistable elliptic curves (Theorem 25.8),
restated. -/
theorem taylor_wiles_modularity_theorem
    (E : EllipticCurveOverQ)
    (hss : IsSemistable E) :
    IsModularEllipticCurve E :=
  wiles_modularity_semistable E hss

/-- For a Fermat-like triple `aᵖ + bᵖ = cᵖ` with `a, b, c` all nonzero, the entries
can be assumed pairwise coprime: `gcd(a, gcd(b, c)) = 1`. -/
theorem freyCurve_coprimality_reduction (a b c : ℤ) (p : ℕ) [Fact (Nat.Prime p)]
    (heq : a ^ p + b ^ p = c ^ p)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    Int.gcd a (Int.gcd b c) = 1 := by sorry

/-- Fermat's Last Theorem for prime exponent `p > 163`, deduced via the Frey curve:
its semistability and Wiles's modularity contradict its non-modularity. -/
theorem flt_for_prime_gt_163 (p : ℕ) [Fact (Nat.Prime p)]
    (hp_large : p > 163) :
    FermatLastTheoremWith ℤ p := by
  intro a b c ha hb hc heq


  have hss := freyCurve_isSemistable a b c p heq
    (freyCurve_coprimality_reduction a b c p heq ha hb hc)

  have hmod := wiles_modularity_semistable (freyCurve a b c p) hss

  have hnmod := freyCurve_not_modular a b c p heq hp_large

  exact hnmod hmod

/-- Fermat's Last Theorem for odd primes `p` in the range `5 ≤ p ≤ 163`, handled by
the classical (pre-Wiles) techniques. -/
theorem flt_for_small_odd_primes (p : ℕ) (hp : Nat.Prime p) (hp_odd : Odd p)
    (hp_ge5 : p ≥ 5) (hp_le163 : p ≤ 163) : FermatLastTheoremFor p := by sorry

/-- Fermat's Last Theorem for any odd prime exponent `p`, combining the case `p = 3`
(`fermatLastTheoremThree`), the small-prime range, and the large-prime case from
Wiles/Ribet. -/
theorem flt_for_odd_prime (p : ℕ) (hp : Nat.Prime p) (hp_odd : Odd p) :
    FermatLastTheoremFor p := by

  have hp2 : p ≠ 2 := by intro h; rw [h] at hp_odd; exact (by decide : ¬ Odd 2) hp_odd
  have hp_ge2 := hp.two_le
  have hp_ge3 : p ≥ 3 := by omega
  by_cases hp3 : p = 3
  ·
    rw [hp3]
    exact fermatLastTheoremThree
  ·
    have hp_ge5 : p ≥ 5 := by obtain ⟨k, hk⟩ := hp_odd; omega
    by_cases hp_le163 : p ≤ 163
    ·
      exact flt_for_small_odd_primes p hp hp_odd hp_ge5 hp_le163
    ·
      simp only [not_le] at hp_le163
      rw [fermatLastTheoremFor_iff_int]
      haveI : Fact (Nat.Prime p) := ⟨hp⟩
      exact flt_for_prime_gt_163 p hp_le163

/-- Corollary 25.9 (Fermat's Last Theorem): for every `n > 2`, the equation
`xⁿ + yⁿ = zⁿ` has no integer solutions with `xyz ≠ 0`. -/
theorem fermats_last_theorem_cor_25_9 :
    ∀ n : ℕ, n > 2 → ∀ x y z : ℤ, x ^ n + y ^ n = z ^ n → x * y * z = 0 := by

  have hFLT : FermatLastTheorem := by
    apply FermatLastTheorem.of_odd_primes
    intro p hp hp_odd
    exact flt_for_odd_prime p hp hp_odd

  intro n hn x y z heq

  have hn3 : n ≥ 3 := by omega
  have hFLTn := hFLT n hn3


  rw [fermatLastTheoremFor_iff_int] at hFLTn


  by_contra h

  have hx : x ≠ 0 := left_ne_zero_of_mul (left_ne_zero_of_mul h)
  have hy : y ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul h)
  have hz : z ≠ 0 := right_ne_zero_of_mul h
  exact hFLTn x y z hx hy hz heq

end FLT

end

noncomputable section

namespace EllipticCurve

/-- Convenience abbreviation for `FLT.EllipticCurveOverQ`, the type of elliptic
curves over `ℚ`. -/
abbrev OverQ := FLT.EllipticCurveOverQ

/-- The conductor of an elliptic curve over `ℚ`, re-exported from the `FLT` namespace. -/
noncomputable def conductor (E : FLT.EllipticCurveOverQ) : ℕ := FLT.conductor E

/-- The minimal discriminant of an elliptic curve over `ℚ`, re-exported from `FLT`. -/
noncomputable def minimalDiscriminant (E : FLT.EllipticCurveOverQ) : ℤ :=
  FLT.minimalDiscriminant E

/-- The conductor of any elliptic curve over `ℚ` is strictly positive (re-export). -/
theorem conductor_pos (E : FLT.EllipticCurveOverQ) : 0 < conductor E :=
  FLT.conductor_pos E

/-- An elliptic curve over `ℚ` is semistable, re-exported from `FLT`. -/
def IsSemistable (E : FLT.EllipticCurveOverQ) : Prop := FLT.IsSemistable E

/-- Re-export: semistability is equivalent to the conductor being squarefree. -/
theorem isSemistable_iff_squarefree_conductor (E : FLT.EllipticCurveOverQ) :
    IsSemistable E ↔ Squarefree (conductor E) :=
  FLT.isSemistable_iff_squarefree_conductor E

end EllipticCurve

end

noncomputable section

/-- Serre's modularity conjecture (now a theorem of Khare–Wintenberger): every odd,
irreducible mod-`ℓ` Galois representation of `Gal(ℚ̄/ℚ)` arises from a modular
form. -/
theorem serre_modularity_conjecture (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
    (ρ : GaloisRepMod ℓ)
    (hodd : ρ.IsOdd)
    (hirr : ρ.IsIrreducible) :
    ρ.IsModular := by sorry

end
