/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Algebra.Module.SpanRankOperations
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.Maps

set_option synthInstance.maxHeartbeats 80000
set_option maxHeartbeats 400000

noncomputable section

open IsLocalRing

/-- The maximal ideal `m_x ⊂ k[x_1,…,x_n]` of polynomials vanishing at the point `x ∈ k^n`,
defined as the kernel of evaluation at `x`. -/
def maxIdealOfPoint {k : Type*} [Field k] {n : ℕ}
    (x : Fin n → k) : Ideal (MvPolynomial (Fin n) k) :=
  RingHom.ker (MvPolynomial.eval x)

/-- The vanishing ideal of a point `x ∈ k^n` is maximal, since the evaluation map is
surjective onto the field `k`. -/
instance maxIdealOfPoint_isMaximal {k : Type*} [Field k] {n : ℕ}
    (x : Fin n → k) : (maxIdealOfPoint x).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _
    (fun c => ⟨MvPolynomial.C c, MvPolynomial.eval_C c⟩)

/-- The image of `m_x` in the quotient `k[x_1,…,x_n]/I`, well-defined whenever `I ⊆ m_x`;
this is the maximal ideal of `x` viewed as a point of the affine variety `V(I)`. -/
def maxIdealOfPointInQuotient {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (_ : I ≤ maxIdealOfPoint x) :
    Ideal (MvPolynomial (Fin n) k ⧸ I) :=
  Ideal.map (Ideal.Quotient.mk I) (maxIdealOfPoint x)

/-- The image of `m_x` in `k[x_1,…,x_n]/I` is maximal. -/
instance maxIdealOfPointInQuotient_isMaximal {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint x) :
    (maxIdealOfPointInQuotient I x hI).IsMaximal := by
  apply Ideal.IsMaximal.map_of_surjective_of_ker_le
  · exact Ideal.Quotient.mk_surjective
  · rwa [Ideal.mk_ker]

/-- The image of `m_x` in `k[x_1,…,x_n]/I` is prime (since maximal ideals are prime). -/
instance maxIdealOfPointInQuotient_isPrime {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint x) :
    (maxIdealOfPointInQuotient I x hI).IsPrime :=
  (maxIdealOfPointInQuotient_isMaximal I x hI).isPrime

/-- The local ring of the affine variety `V(I)` at the point `x`, obtained as the
localization of `k[x_1,…,x_n]/I` at the maximal ideal of `x`. -/
abbrev localRingAtPoint {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k) (hI : I ≤ maxIdealOfPoint x) :=
  Localization.AtPrime (maxIdealOfPointInQuotient I x hI)

/-- The Jacobian matrix `(∂f_i/∂x_j)(x)` of a family of polynomials `f_1,…,f_m` evaluated
at the point `x ∈ k^n`. -/
def jacobianMatrix {k : Type*} [Field k] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k) (x : Fin n → k) :
    Matrix (Fin m) (Fin n) k :=
  fun i j => MvPolynomial.eval x (MvPolynomial.pderiv j (f i))

/-- Definition 34 (Lecture 18). The universal property characterising Kähler differentials:
`A`-linear maps `Ω[A⁄k] → M` correspond naturally to `k`-derivations `A → M`. -/
def Definition34_KaehlerDifferential_universalProperty
    (k : Type*) (A : Type*) [CommRing k] [CommRing A] [Algebra k A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] :
    (Ω[A⁄k] →ₗ[A] M) ≃ₗ[A] Derivation k A M :=
  KaehlerDifferential.linearMapEquivDerivation k A

/-- Definition 35 (Lecture 18). The Zariski cotangent space of a local ring `R`, defined as
`m/m²` viewed as a vector space over the residue field. -/
def Definition35_CotangentSpace
    (R : Type*) [CommRing R] [IsLocalRing R] :=
  IsLocalRing.CotangentSpace R

/-- Lemma 30 (Lecture 18). For a Noetherian local ring, the Krull dimension is at most the
dimension of the Zariski cotangent space. -/
theorem Lemma30_cotangentSpace_dim_ge_krullDim
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    ringKrullDim R ≤ Module.finrank (ResidueField R) (CotangentSpace R) := by
  rw [← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact ringKrullDim_le_spanFinrank_maximalIdeal R

/-- Definition 36 (Lecture 18). A Noetherian local ring is smooth (regular) iff the Zariski
cotangent space has dimension equal to the Krull dimension; equality in Lemma 30. -/
theorem Definition36_smooth_iff_regular
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    IsRegularLocalRing R ↔
      Module.finrank (ResidueField R) (CotangentSpace R) = ringKrullDim R :=
  IsRegularLocalRing.iff_finrank_cotangentSpace R

/-- Proposition 29 (Lecture 18). A Noetherian local `k`-algebra is regular (smooth) iff its
module of Kähler differentials `Ω[R⁄k]` is free. -/
theorem Proposition29_smooth_iff_omega_locally_free
    (k : Type*) (R : Type*) [Field k] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra k R] :
    IsRegularLocalRing R ↔ Module.Free R (Ω[R⁄k]) := by
  sorry

/-- The regular locus is open: if a prime `𝔭` of a finite-type `k`-algebra `A` has regular
localization, then some `f ∉ 𝔭` makes the localization regular at every prime not containing
`f`. -/
theorem regularLocus_isOpen
    (k : Type*) [Field k] (A : Type*) [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A]
    (𝔭 : Ideal A) [𝔭.IsPrime]
    (hreg : IsRegularLocalRing (Localization.AtPrime 𝔭)) :
    ∃ (f : A), f ∉ 𝔭 ∧
      ∀ (𝔮 : Ideal A) [𝔮.IsPrime], f ∉ 𝔮 →
        IsRegularLocalRing (Localization.AtPrime 𝔮) := by
  sorry

/-- The generic point of an integral finite-type `k`-algebra is regular: localizing at the
zero ideal gives a field, hence trivially a regular local ring. -/
theorem genericPoint_isRegularLocalRing
    (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    IsRegularLocalRing (Localization.AtPrime (⊥ : Ideal A)) := by

  have hField : IsField (Localization.AtPrime (⊥ : Ideal A)) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq]
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    simp

  letI : Field (Localization.AtPrime (⊥ : Ideal A)) := hField.toField
  infer_instance

/-- Proposition 30 (Lecture 18). For an integral finite-type `k`-algebra `A`, the smooth
(regular) locus is open and dense: there exists nonzero `f ∈ A` such that the localization
of `A` at every prime not containing `f` is regular. -/
theorem Proposition30_smooth_locus_open_dense
    (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ∃ (f : A), f ≠ 0 ∧
      ∀ (𝔭 : Ideal A) [𝔭.IsPrime] (_ : f ∉ 𝔭),
        IsRegularLocalRing (Localization.AtPrime 𝔭) := by


  have hgen : IsRegularLocalRing (Localization.AtPrime (⊥ : Ideal A)) :=
    genericPoint_isRegularLocalRing k A


  obtain ⟨f, hf_not_bot, hf_reg⟩ := regularLocus_isOpen k A ⊥ hgen

  have hf_ne : f ≠ 0 := by
    intro h
    exact hf_not_bot (h ▸ Ideal.zero_mem ⊥)
  exact ⟨f, hf_ne, fun 𝔭 _ h𝔭 => hf_reg 𝔭 h𝔭⟩

/-- Helper for Corollary 23: if the local ring at `x` of `V(f_1,…,f_m)` has Krull dimension
`n - m`, then `m ≤ n` (you cannot cut out a positive-dimensional variety with more equations
than ambient coordinates while preserving the expected dimension). -/
theorem completeIntersection_m_le_n
    {k : Type*} [Field k] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k)
    (x : Fin n → k)
    (hx : ∀ i, MvPolynomial.eval x (f i) = 0)
    (hI : Ideal.span (Set.range f) ≤ maxIdealOfPoint x)
    (hdim : ringKrullDim (localRingAtPoint (Ideal.span (Set.range f)) x hI) = (n - m : ℕ)) :
    m ≤ n := by sorry

/-- The cotangent space at a point of `V(f_1,…,f_m) ⊂ 𝔸ⁿ` has dimension equal to
`n - rank(Jac(f)(x))`: the differentials of the relations cut out a subspace of the ambient
cotangent space `(m_x/m_x²)`. -/
theorem cotangentSpace_finrank_eq_n_sub_jacobianRank
    {k : Type*} [Field k] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k)
    (x : Fin n → k)
    (hx : ∀ i, MvPolynomial.eval x (f i) = 0)
    (hI : Ideal.span (Set.range f) ≤ maxIdealOfPoint x) :
    Module.finrank
      (ResidueField (localRingAtPoint (Ideal.span (Set.range f)) x hI))
      (CotangentSpace (localRingAtPoint (Ideal.span (Set.range f)) x hI)) =
    n - (jacobianMatrix f x).rank := by sorry

/-- Corollary 23 (Lecture 18, Jacobian criterion). For a complete intersection `V(f_1,…,f_m)`
of expected dimension `n - m`, the local ring at `x` is regular iff the Jacobian matrix has
full rank `m` at `x`. -/
theorem Corollary23_jacobian_criterion
    {k : Type*} [Field k] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k)
    (x : Fin n → k)
    (hx : ∀ i, MvPolynomial.eval x (f i) = 0)
    (hI : Ideal.span (Set.range f) ≤ maxIdealOfPoint x)
    (hdim : ringKrullDim (localRingAtPoint (Ideal.span (Set.range f)) x hI) = (n - m : ℕ)) :
    (jacobianMatrix f x).rank = m ↔
      IsRegularLocalRing
        (localRingAtPoint (Ideal.span (Set.range f)) x hI) := by


  have hmn : m ≤ n := completeIntersection_m_le_n f x hx hI hdim


  have hcot : Module.finrank
      (ResidueField (localRingAtPoint (Ideal.span (Set.range f)) x hI))
      (CotangentSpace (localRingAtPoint (Ideal.span (Set.range f)) x hI)) =
    n - (jacobianMatrix f x).rank := cotangentSpace_finrank_eq_n_sub_jacobianRank f x hx hI


  rw [IsRegularLocalRing.iff_finrank_cotangentSpace]

  rw [hcot, hdim]

  have hrank_le_n : (jacobianMatrix f x).rank ≤ n :=
    le_trans (Matrix.rank_le_card_width _) (by simp)
  constructor
  · intro h; rw [h]
  · intro h
    have h' : n - (jacobianMatrix f x).rank = n - m := by exact_mod_cast h
    omega

/-- A single-row matrix has rank zero iff it is the zero matrix. -/
lemma matrix_fin1_rank_eq_zero_iff {k : Type*} [Field k] {n : ℕ}
    (M : Matrix (Fin 1) (Fin n) k) : M.rank = 0 ↔ M = 0 := by
  unfold Matrix.rank
  constructor
  · intro h
    rw [Submodule.finrank_eq_zero] at h
    rw [LinearMap.range_eq_bot] at h
    ext i j
    have hcol := LinearMap.ext_iff.mp h (Pi.single j 1)
    simp [Matrix.mulVecLin, Matrix.mulVec_single] at hcol
    have : M.col j 0 = 0 := by rw [hcol]; rfl
    simp [Matrix.col] at this
    fin_cases i
    exact this
  · intro h
    subst h
    exact Matrix.rank_zero

/-- A single-row matrix has rank one iff it has at least one nonzero entry. -/
lemma matrix_fin1_rank_eq_one_iff {k : Type*} [Field k] {n : ℕ}
    (M : Matrix (Fin 1) (Fin n) k) :
    M.rank = 1 ↔ ∃ j, M 0 j ≠ 0 := by
  have hle : M.rank ≤ 1 := by
    have := Matrix.rank_le_card_height M; simp at this; exact this
  constructor
  · intro h
    by_contra hall
    push Not at hall
    have hzero : M = 0 := by ext i j; fin_cases i; exact hall j
    rw [hzero, Matrix.rank_zero] at h; omega
  · intro ⟨j, hj⟩
    have hne : M ≠ 0 := by intro h; rw [h] at hj; simp at hj
    have hpos : 0 < M.rank := by
      by_contra h
      push Not at h
      exact hne ((matrix_fin1_rank_eq_zero_iff M).mp (by omega))
    omega

/-- Corollary 23, hypersurface case: for a hypersurface `V(P) ⊂ 𝔸ⁿ`, smoothness at `x`
amounts to some partial derivative `∂P/∂x_i` being nonzero at `x`, i.e. the Jacobian
(`1 × n`) matrix has rank one. -/
theorem Corollary23_hypersurface_criterion
    {k : Type*} [Field k] {n : ℕ}
    (P : MvPolynomial (Fin n) k)
    (x : Fin n → k)
    (_hx : MvPolynomial.eval x P = 0) :
    (∃ i : Fin n, MvPolynomial.eval x (MvPolynomial.pderiv i P) ≠ 0) ↔
    (jacobianMatrix (fun _ : Fin 1 => P) x).rank = 1 := by
  rw [matrix_fin1_rank_eq_one_iff]
  simp [jacobianMatrix]

/-- Helper for Proposition 31: if `I` agrees with `span(f)` after inverting a single element
not vanishing at `x`, and `span(f)` is regular at `x`, then so is `I`. This is the local
descent step used to deduce regularity for `I` from regularity for a locally-generating
subfamily. -/
theorem localRingAtPoint_isRegular_of_local_generation_and_span_regular
    {k : Type*} [Field k] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k)
    (hI : I ≤ maxIdealOfPoint x)
    (f : Fin m → MvPolynomial (Fin n) k)
    (hfI : ∀ i, f i ∈ I)
    (u : MvPolynomial (Fin n) k)
    (hu : MvPolynomial.eval x u ≠ 0)
    (hgen : ∀ g ∈ I, u * g ∈ Ideal.span (Set.range f))
    (hJ : Ideal.span (Set.range f) ≤ maxIdealOfPoint x)
    (hreg_span : IsRegularLocalRing (localRingAtPoint (Ideal.span (Set.range f)) x hJ)) :
    IsRegularLocalRing (localRingAtPoint I x hI) := by sorry

/-- If the Jacobian rows `(∂f_i/∂x_j)(x)` are `k`-linearly independent, then the local ring
of `V(f_1,…,f_m)` at `x` has the expected Krull dimension `n - m`. -/
theorem krullDim_localRingAtPoint_span_eq
    {k : Type*} [Field k] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k)
    (x : Fin n → k)
    (hx : ∀ i, MvPolynomial.eval x (f i) = 0)
    (hI : Ideal.span (Set.range f) ≤ maxIdealOfPoint x)
    (hf_indep : LinearIndependent k
      (fun i : Fin m => (fun j : Fin n =>
        MvPolynomial.eval x (MvPolynomial.pderiv j (f i))))) :
    ringKrullDim (localRingAtPoint (Ideal.span (Set.range f)) x hI) = (n - m : ℕ) := by sorry

/-- At a smooth (regular) point `x` of `V(I)`, one can find polynomials `f_1,…,f_m ∈ I`
whose Jacobian rows at `x` are linearly independent — i.e. local generators for the
cotangent obstructions. -/
theorem smooth_point_cotangent_generators_exist
    {k : Type*} [Field k] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k)
    (hI : I ≤ maxIdealOfPoint x)
    (hreg : IsRegularLocalRing (localRingAtPoint I x hI)) :
    ∃ (m : ℕ) (f : Fin m → MvPolynomial (Fin n) k),
      (∀ i, f i ∈ I) ∧
      LinearIndependent k
        (fun i : Fin m => (fun j : Fin n =>
          MvPolynomial.eval x (MvPolynomial.pderiv j (f i)))) := by sorry

/-- A smooth complete intersection is locally a domain: a regular local ring is in
particular an integral domain. -/
theorem smooth_complete_intersection_is_domain
    {k : Type*} [Field k] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k)
    (x : Fin n → k)
    (hx : ∀ i, MvPolynomial.eval x (f i) = 0)
    (hI : Ideal.span (Set.range f) ≤ maxIdealOfPoint x)
    (hreg : IsRegularLocalRing (localRingAtPoint (Ideal.span (Set.range f)) x hI)) :
    IsDomain (localRingAtPoint (Ideal.span (Set.range f)) x hI) := by sorry

/-- If `span(f) ⊂ I` and the two ideals define local rings of the same Krull dimension at
`x`, with the smaller one a domain, then `I` and `span(f)` agree after multiplying by some
unit `u` (i.e. they agree locally near `x`). -/
theorem locally_irreducible_containment_gives_local_generators
    {k : Type*} [Field k] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (f : Fin m → MvPolynomial (Fin n) k)
    (x : Fin n → k)
    (hI : I ≤ maxIdealOfPoint x)
    (hfI : ∀ i, f i ∈ I)
    (hJ : Ideal.span (Set.range f) ≤ maxIdealOfPoint x)
    (hdomain : IsDomain (localRingAtPoint (Ideal.span (Set.range f)) x hJ))
    (hdim : ringKrullDim (localRingAtPoint I x hI) =
            ringKrullDim (localRingAtPoint (Ideal.span (Set.range f)) x hJ)) :
    ∃ (u : MvPolynomial (Fin n) k),
      MvPolynomial.eval x u ≠ 0 ∧
      ∀ g ∈ I, u * g ∈ Ideal.span (Set.range f) := by sorry

/-- If the local ring at `x` of `V(I)` is regular and `f_1,…,f_m ∈ I` have linearly
independent Jacobian rows at `x`, then the local rings of `V(I)` and `V(span f)` have the
same Krull dimension at `x`. -/
theorem krullDim_localRingAtPoint_eq_of_regular_and_generators
    {k : Type*} [Field k] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k))
    (x : Fin n → k)
    (hI : I ≤ maxIdealOfPoint x)
    (hreg : IsRegularLocalRing (localRingAtPoint I x hI))
    (f : Fin m → MvPolynomial (Fin n) k)
    (hfI : ∀ i, f i ∈ I)
    (hf_indep : LinearIndependent k
      (fun i : Fin m => (fun j : Fin n =>
        MvPolynomial.eval x (MvPolynomial.pderiv j (f i)))))
    (hJ : Ideal.span (Set.range f) ≤ maxIdealOfPoint x)
    (hx : ∀ i, MvPolynomial.eval x (f i) = 0) :
    ringKrullDim (localRingAtPoint I x hI) =
    ringKrullDim (localRingAtPoint (Ideal.span (Set.range f)) x hJ) := by sorry

/-- If each `f_i` vanishes at `x`, then `span(f_1,…,f_m) ⊆ m_x`. -/
lemma span_range_le_maxIdealOfPoint {k : Type*} [Field k] {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k) (x : Fin n → k)
    (hx : ∀ i, MvPolynomial.eval x (f i) = 0) :
    Ideal.span (Set.range f) ≤ maxIdealOfPoint x := by
  rw [Ideal.span_le]
  intro p hp
  obtain ⟨i, rfl⟩ := hp
  rw [maxIdealOfPoint, SetLike.mem_coe, RingHom.mem_ker]
  exact hx i

/-- Polynomials in an ideal `I ⊆ m_x` all vanish at the point `x`. -/
lemma eval_eq_zero_of_mem_le_maxIdeal {k : Type*} [Field k] {n m : ℕ}
    (I : Ideal (MvPolynomial (Fin n) k)) (x : Fin n → k) (hI : I ≤ maxIdealOfPoint x)
    (f : Fin m → MvPolynomial (Fin n) k) (hfI : ∀ i, f i ∈ I) :
    ∀ i, MvPolynomial.eval x (f i) = 0 := by
  intro i
  have h := hI (hfI i)
  rwa [maxIdealOfPoint, RingHom.mem_ker] at h

/-- Proposition 31 (Lecture 18). Smoothness of `V(I)` at `x` is equivalent to the existence
of polynomials `f_1,…,f_m ∈ I` with linearly independent Jacobian rows at `x` whose span,
after inverting some `u(x) ≠ 0`, equals `I` locally. -/
theorem Proposition31_smooth_point_characterization
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
        ∀ g ∈ I, u * g ∈ Ideal.span (Set.range f)) := by
  constructor
  ·

    intro hreg
    obtain ⟨m, f, hfI, hf_indep⟩ := smooth_point_cotangent_generators_exist I x hI hreg

    have hx : ∀ i, MvPolynomial.eval x (f i) = 0 := eval_eq_zero_of_mem_le_maxIdeal I x hI f hfI

    have hJ : Ideal.span (Set.range f) ≤ maxIdealOfPoint x := span_range_le_maxIdealOfPoint f x hx

    have hdim_span := krullDim_localRingAtPoint_span_eq f x hx hJ hf_indep

    have hrank : (jacobianMatrix f x).rank = m := by
      have h : LinearIndependent k (jacobianMatrix f x).row := by
        simp only [Matrix.row]; exact hf_indep
      rw [LinearIndependent.rank_matrix h, Fintype.card_fin]

    have hreg_span : IsRegularLocalRing (localRingAtPoint (Ideal.span (Set.range f)) x hJ) :=
      (Corollary23_jacobian_criterion f x hx hJ hdim_span).mp hrank

    have hdomain := smooth_complete_intersection_is_domain f x hx hJ hreg_span

    have hdim_eq := krullDim_localRingAtPoint_eq_of_regular_and_generators
      I x hI hreg f hfI hf_indep hJ hx
    obtain ⟨u, hu, hgen⟩ := locally_irreducible_containment_gives_local_generators
      I f x hI hfI hJ hdomain hdim_eq
    exact ⟨m, f, hfI, hf_indep, u, hu, hgen⟩
  ·

    rintro ⟨m, f, hfI, hf_indep, u, hu, hgen⟩

    have hx : ∀ i, MvPolynomial.eval x (f i) = 0 := eval_eq_zero_of_mem_le_maxIdeal I x hI f hfI

    have hJ : Ideal.span (Set.range f) ≤ maxIdealOfPoint x := span_range_le_maxIdealOfPoint f x hx

    have hdim_span := krullDim_localRingAtPoint_span_eq f x hx hJ hf_indep

    have hrank : (jacobianMatrix f x).rank = m := by
      have h : LinearIndependent k (jacobianMatrix f x).row := by
        simp only [Matrix.row]; exact hf_indep
      rw [LinearIndependent.rank_matrix h, Fintype.card_fin]

    have hreg_span : IsRegularLocalRing (localRingAtPoint (Ideal.span (Set.range f)) x hJ) :=
      (Corollary23_jacobian_criterion f x hx hJ hdim_span).mp hrank

    exact localRingAtPoint_isRegular_of_local_generation_and_span_regular
      I x hI f hfI u hu hgen hJ hreg_span

end
