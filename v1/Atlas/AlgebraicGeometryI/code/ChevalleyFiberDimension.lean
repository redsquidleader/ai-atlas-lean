/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.ChevalleyImage
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

noncomputable section

open PrimeSpectrum Topology

namespace ChevalleyFiberDim

/-- The Krull dimension of the fiber of `Spec A → Spec B` over a prime `q ∈ Spec B`. -/
def fiberKrullDim {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    (q : PrimeSpectrum B) : WithBot ℕ∞ :=
  ringKrullDim (A ⧸ (q.asIdeal.map (algebraMap B A)))

/-- The generic point of `Spec B` for an integral domain `B`, given by the zero ideal. -/
def genericPoint (B : Type*) [CommRing B] [IsDomain B] : PrimeSpectrum B :=
  ⟨⊥, Ideal.isPrime_bot⟩

/-- The set of primes `q` in the image of `Spec A → Spec B` whose fiber has dimension at least
`d`; this is the set whose upper semicontinuity is part of Chevalley's theorem. -/
def fiberDimGeInImage {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    (d : ℕ) : Set (PrimeSpectrum B) :=
  {q | q ∈ Set.range (PrimeSpectrum.comap (algebraMap B A)) ∧
    (d : WithBot ℕ∞) ≤ fiberKrullDim (A := A) q}

/-- The generic fiber of `Spec A → Spec B` has Krull dimension equal to `dim A`. -/
theorem fiberKrullDim_generic_eq (B A : Type*) [CommRing B] [CommRing A]
    [IsDomain B] [Algebra B A] :
    fiberKrullDim (A := A) (genericPoint B) = ringKrullDim A := by
  unfold fiberKrullDim genericPoint
  exact RingEquiv.ringKrullDim
    ((Ideal.quotEquivOfEq (Ideal.map_bot (f := algebraMap B A))).trans
      (RingEquiv.quotientBot A))

/-- The bundled data of a dominant morphism of integral schemes of finite type:
the algebra map is injective, the algebra is finite type, and we record the transcendence degree
of the function field extension. -/
structure DominantFiniteTypeMorphism (B A : Type*) [CommRing B] [CommRing A]
    [IsDomain B] [IsDomain A] [IsNoetherianRing B] [Algebra B A] where
  injective : Function.Injective (algebraMap B A)
  finiteType : Algebra.FiniteType B A
  transDeg : ℕ

/-- If `q ∈ Spec B` is in the image of `Spec A → Spec B`, then the fiber over `q` is nontrivial
(i.e. `A / qA ≠ 0`). -/
lemma fiber_nontrivial_of_in_image {B A : Type*} [CommRing B] [CommRing A]
    [Algebra B A] {q : PrimeSpectrum B}
    (hq : q ∈ Set.range (PrimeSpectrum.comap (algebraMap B A))) :
    Nontrivial (A ⧸ (q.asIdeal.map (algebraMap B A))) := by
  obtain ⟨p, hp⟩ := hq
  have hle : q.asIdeal.map (algebraMap B A) ≤ p.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    show b ∈ (PrimeSpectrum.comap (algebraMap B A) p).asIdeal
    rw [hp]; exact hb
  have : Nontrivial (A ⧸ p.asIdeal) :=
    Ideal.Quotient.nontrivial_iff.mpr (Ideal.IsPrime.ne_top p.isPrime)
  exact (Ideal.Quotient.factor_surjective hle).nontrivial

/-- The image of a morphism of finite type between Noetherian affine schemes is constructible
(Chevalley, Thm 21.2, Lec 21). -/
theorem fiber_dim_usc_image_constructible (B A : Type*) [CommRing B] [CommRing A]
    [IsNoetherianRing B] [Algebra B A] [Algebra.FiniteType B A] :
    IsConstructible (Set.range (PrimeSpectrum.comap (algebraMap B A))) :=
  isConstructible_range_comap
    (RingHom.finitePresentation_algebraMap.mpr
      (Algebra.FinitePresentation.of_finiteType.mp ‹_›))

/-- Fiber dimension is order-reversing: if `q ⊆ q'`, then the fiber over `q'` has dimension at
most that of the fiber over `q`. -/
theorem fiberKrullDim_anti {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    {q q' : PrimeSpectrum B} (hle : q.asIdeal ≤ q'.asIdeal) :
    fiberKrullDim (A := A) q' ≤ fiberKrullDim (A := A) q :=
  ringKrullDim_le_of_surjective
    (Ideal.Quotient.factor (Ideal.map_mono hle))
    (Ideal.Quotient.factor_surjective (Ideal.map_mono hle))

/-- Every fiber dimension is bounded above by the dimension of the generic fiber. -/
theorem fiberKrullDim_le_generic {B A : Type*} [CommRing B] [CommRing A]
    [IsDomain B] [Algebra B A] (q : PrimeSpectrum B) :
    fiberKrullDim (A := A) q ≤ fiberKrullDim (A := A) (genericPoint B) :=
  fiberKrullDim_anti bot_le

/-- Noether normalization descent: for a dominant finite-type morphism between integral domains,
after inverting some nonzero `b ∈ B`, the localized algebra `A[b⁻¹]` is finite over a polynomial
ring `B[b⁻¹][x₁,…,xₙ]`, and the basic open `D(b)` lies in the image. -/
theorem noether_normalization_descent (B A : Type*) [CommRing B] [CommRing A]
    [IsDomain B] [IsDomain A] [IsNoetherianRing B]
    [Algebra B A] [Algebra.FiniteType B A]
    (hf : Function.Injective (algebraMap B A)) :
    ∃ (n : ℕ) (b : B) (_ : b ≠ 0)
      (φ : MvPolynomial (Fin n) (Localization.Away b) →+*
        Localization.Away ((algebraMap B A) b)),
      φ.Finite ∧ Function.Injective φ ∧
      φ.comp MvPolynomial.C = Localization.awayMap (algebraMap B A) b ∧
      (↑(basicOpen b) : Set (PrimeSpectrum B)) ⊆
        Set.range (PrimeSpectrum.comap (algebraMap B A)) := by sorry

/-- Lemma 3.3 factorization: an alias for `noether_normalization_descent`, exposing the same
existence statement under the name used in the textbook. -/
theorem lemma33_factorization (B A : Type*) [CommRing B] [CommRing A]
    [IsDomain B] [IsDomain A] [IsNoetherianRing B]
    [Algebra B A] [Algebra.FiniteType B A]
    (hf : Function.Injective (algebraMap B A)) :
    ∃ (n : ℕ) (b : B) (_ : b ≠ 0)
      (φ : MvPolynomial (Fin n) (Localization.Away b) →+*
        Localization.Away ((algebraMap B A) b)),
      φ.Finite ∧ Function.Injective φ ∧
      φ.comp MvPolynomial.C = Localization.awayMap (algebraMap B A) b ∧
      (↑(basicOpen b) : Set (PrimeSpectrum B)) ⊆
        Set.range (PrimeSpectrum.comap (algebraMap B A)) :=
  noether_normalization_descent B A hf

/-- Packaged data corresponding to the conclusion of Lemma 3.3: a nonzero element `b ∈ B`, an
integer `n`, a finite injective map from `B[b⁻¹][x₁,…,xₙ]` into `A[b⁻¹]` compatible with the
algebra map, and the fact that `D(b)` lies in the image of `Spec A → Spec B`. -/
structure Lemma33Data (B A : Type*) [CommRing B] [CommRing A] [Algebra B A] where
  b : B
  hb : b ≠ 0
  n : ℕ
  φ : MvPolynomial (Fin n) (Localization.Away b) →+*
      Localization.Away ((algebraMap B A) b)
  φ_finite : φ.Finite
  φ_injective : Function.Injective φ
  φ_compat : φ.comp MvPolynomial.C = Localization.awayMap (algebraMap B A) b
  basicOpen_sub_image :
    (↑(basicOpen b) : Set (PrimeSpectrum B)) ⊆
      Set.range (PrimeSpectrum.comap (algebraMap B A))

/-- Construct a `Lemma33Data` witness by unpacking the existence statement of
`lemma33_factorization`. -/
noncomputable def Lemma33Data.ofChevalley (B A : Type*) [CommRing B] [CommRing A]
    [IsDomain B] [IsDomain A] [IsNoetherianRing B]
    [Algebra B A] [Algebra.FiniteType B A]
    (hf : Function.Injective (algebraMap B A)) : Lemma33Data B A :=
  let h := lemma33_factorization B A hf
  let n := h.choose
  let h1 := h.choose_spec
  let b := h1.choose
  let h2 := h1.choose_spec
  let hb := h2.choose
  let h3 := h2.choose_spec
  let φ := h3.choose
  let h4 := h3.choose_spec
  { b := b
    hb := hb
    n := n
    φ := φ
    φ_finite := h4.1
    φ_injective := h4.2.1
    φ_compat := h4.2.2.1
    basicOpen_sub_image := h4.2.2.2 }

/-- Over the basic open `D(b)` of `Lemma33Data`, the fibers of `Spec A → Spec B` are nontrivial. -/
theorem Lemma33Data.fiber_nontrivial {B A : Type*} [CommRing B] [CommRing A]
    [Algebra B A] (L : Lemma33Data B A)
    {q : PrimeSpectrum B} (hq : q ∈ (↑(basicOpen L.b) : Set (PrimeSpectrum B))) :
    Nontrivial (A ⧸ (q.asIdeal.map (algebraMap B A))) :=
  fiber_nontrivial_of_in_image (L.basicOpen_sub_image hq)

/-- Over the basic open `D(b)`, the fiber dimensions of `Spec A → Spec B` are nonnegative. -/
theorem Lemma33Data.fiberKrullDim_nonneg {B A : Type*} [CommRing B] [CommRing A]
    [Algebra B A] (L : Lemma33Data B A)
    {q : PrimeSpectrum B} (hq : q ∈ (↑(basicOpen L.b) : Set (PrimeSpectrum B))) :
    (0 : WithBot ℕ∞) ≤ fiberKrullDim (A := A) q :=
  @ringKrullDim_nonneg_of_nontrivial _ _ (L.fiber_nontrivial hq)

/-- The locus in `Spec B` where the fiber of `Spec A → Spec B` has dimension at least `d`. -/
def fiberDimGe {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    (d : WithBot ℕ∞) : Set (PrimeSpectrum B) :=
  {q | d ≤ fiberKrullDim (A := A) q}

/-- `fiberDimGeInImage d` is the intersection of the image with the `d`-th fiber-dimension
locus. -/
theorem fiberDimGeInImage_eq_inter {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    (d : ℕ) :
    fiberDimGeInImage (A := A) d =
      Set.range (PrimeSpectrum.comap (algebraMap B A)) ∩ fiberDimGe (A := A) (d : WithBot ℕ∞) := by
  ext q
  simp [fiberDimGeInImage, fiberDimGe, Set.mem_inter_iff, Set.mem_setOf_eq]

/-- A flat morphism of finite type between Noetherian schemes is an open map. -/
theorem flat_morphism_isOpenMap (B A : Type*) [CommRing B] [CommRing A]
    [IsNoetherianRing B] [Algebra B A] [Algebra.FiniteType B A]
    [Module.Flat B A] :
    IsOpenMap (PrimeSpectrum.comap (algebraMap B A)) := by
  have : Algebra.FinitePresentation B A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  exact isOpenMap_comap_of_hasGoingDown_of_finitePresentation

/-- A ring equivalence comparing the iterated fiber `(A/𝔭A)/(q'A)` to the fiber `A/q'A`, used
when comparing fiber dimensions along specializations. -/
noncomputable def doubleQuot_fiber_equiv {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    {𝔭 q' : PrimeSpectrum B} (hle : 𝔭.asIdeal ≤ q'.asIdeal) :
    (A ⧸ 𝔭.asIdeal.map (algebraMap B A)) ⧸
      (q'.asIdeal.map (algebraMap B A)).map
        (Ideal.Quotient.mk (𝔭.asIdeal.map (algebraMap B A))) ≃+*
    A ⧸ q'.asIdeal.map (algebraMap B A) :=
  (DoubleQuot.quotQuotEquivQuotSup _ _).trans
    (Ideal.quotEquivOfEq (sup_eq_right.mpr (Ideal.map_mono hle)))

/-- Part 1 of Chevalley's Theorem 21.2 (Lec 21): the image of a morphism of finite type between
Noetherian schemes is constructible. -/
theorem chevalley_thm21_2_part1 (B A : Type*) [CommRing B] [CommRing A]
    [IsNoetherianRing B] [Algebra B A] [Algebra.FiniteType B A] :
    IsConstructible (Set.range (PrimeSpectrum.comap (algebraMap B A))) :=
  fiber_dim_usc_image_constructible B A

/-- The locus where the fiber dimension is at least `d` is closed: this is the geometric form of
upper semicontinuity of fiber dimension. -/
theorem fiberDimGe_isClosed (B A : Type*) [CommRing B] [CommRing A]
    [IsDomain B] [IsDomain A] [IsNoetherianRing B]
    [Algebra B A] [Algebra.FiniteType B A]
    (hf : Function.Injective (algebraMap B A))
    (d : ℕ) : IsClosed (fiberDimGe (B := B) (A := A) (d : WithBot ℕ∞)) := by sorry

/-- Part 2 of Chevalley's Theorem 21.2 (Lec 21): upper semicontinuity of fiber dimension. The
locus in the image where fibers have dimension at least `d` is the trace of a closed set. -/
theorem chevalley_thm21_2_part2 (B A : Type*) [CommRing B] [CommRing A]
    [IsDomain B] [IsDomain A] [IsNoetherianRing B]
    [Algebra B A] [Algebra.FiniteType B A]
    (hf : Function.Injective (algebraMap B A)) (d : ℕ) :
    ∃ Z : Set (PrimeSpectrum B), IsClosed Z ∧
      fiberDimGeInImage (A := A) d =
        Set.range (PrimeSpectrum.comap (algebraMap B A)) ∩ Z :=
  ⟨fiberDimGe (A := A) (d : WithBot ℕ∞),
   fiberDimGe_isClosed B A hf d,
   fiberDimGeInImage_eq_inter d⟩

/-- For dominant morphisms of finite type, every nonempty fiber has dimension at least
`dim A - dim B`. -/
theorem chevalley_thm21_2_fiber_dim_lower_bound (B A : Type*) [CommRing B] [CommRing A]
    [IsDomain B] [IsDomain A] [IsNoetherianRing B]
    [Algebra B A] [Algebra.FiniteType B A]
    (hf : Function.Injective (algebraMap B A))
    {q : PrimeSpectrum B}
    (hq : q ∈ Set.range (PrimeSpectrum.comap (algebraMap B A))) :
    fiberKrullDim (A := A) q + ringKrullDim B ≥ ringKrullDim A := by sorry

/-- Part 3 of Chevalley's Theorem 21.2 (Lec 21): if `f : Spec A → Spec B` has dense image, there
is a nonempty open subset `U ⊆ Spec B` over which every fiber has the expected dimension
`dim A - dim B`. -/
theorem chevalley_thm21_2_part3 (B A : Type*) [CommRing B] [CommRing A]
    [IsDomain B] [IsDomain A] [IsNoetherianRing B]
    [Algebra B A] [Algebra.FiniteType B A]
    (hf : Function.Injective (algebraMap B A)) :
    ∃ b : B, b ≠ 0 ∧
      (↑(basicOpen b) : Set (PrimeSpectrum B)) ⊆
        Set.range (PrimeSpectrum.comap (algebraMap B A)) ∧
      ∀ q ∈ (↑(basicOpen b) : Set (PrimeSpectrum B)),
        fiberKrullDim (A := A) q + ringKrullDim B = ringKrullDim A := by sorry

end ChevalleyFiberDim
