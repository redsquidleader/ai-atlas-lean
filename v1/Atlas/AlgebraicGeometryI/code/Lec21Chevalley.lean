/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Ideal.Quotient.Operations

noncomputable section

open PrimeSpectrum Topology

/-- The Krull dimension of the (scheme-theoretic) fiber of `Spec A → Spec B` over a prime
`q ∈ Spec B`, computed as the Krull dimension of `A / qA`. -/
def fiberKrullDim {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    (q : PrimeSpectrum B) : WithBot ℕ∞ :=
  ringKrullDim (A ⧸ (q.asIdeal.map (algebraMap B A)))

/-- The set of points `q ∈ Spec B` whose fiber in `Spec A` has Krull dimension at least `d`. -/
def fiberDimGe {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    (d : WithBot ℕ∞) : Set (PrimeSpectrum B) :=
  {q | d ≤ fiberKrullDim (A := A) q}

/-- The points in the image of `Spec A → Spec B` whose fiber has dimension at least `d`. -/
def fiberDimGeInImage {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    (d : ℕ) : Set (PrimeSpectrum B) :=
  {q | q ∈ Set.range (PrimeSpectrum.comap (algebraMap B A)) ∧
    (d : WithBot ℕ∞) ≤ fiberKrullDim (A := A) q}

/-- The set of image points with fiber dimension `≥ d` is the intersection of the image of
`Spec A → Spec B` with the upper-level set `fiberDimGe d`. -/
theorem fiberDimGeInImage_eq_inter {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    (d : ℕ) :
    fiberDimGeInImage (A := A) d =
      Set.range (PrimeSpectrum.comap (algebraMap B A)) ∩ fiberDimGe (A := A) (d : WithBot ℕ∞) := by
  ext q
  simp [fiberDimGeInImage, fiberDimGe, Set.mem_inter_iff, Set.mem_setOf_eq]

/-- Chevalley's theorem (Theorem 21.2, part 1): For a finite-type morphism between Noetherian
schemes, the image of `Spec A → Spec B` is a constructible subset. -/
theorem chevalley_thm21_2_part1 (B A : Type*) [CommRing B] [CommRing A]
    [IsNoetherianRing B] [Algebra B A] [Algebra.FiniteType B A] :
    IsConstructible (Set.range (PrimeSpectrum.comap (algebraMap B A))) := by
  have hfp : (algebraMap B A).FinitePresentation :=
    RingHom.finitePresentation_algebraMap.mpr
      (Algebra.FinitePresentation.of_finiteType.mp ‹Algebra.FiniteType B A›)
  exact PrimeSpectrum.isConstructible_range_comap hfp

/-- Upper-semicontinuity of fiber dimension: the locus of points in `Spec B` where the fiber
of a dominant finite-type morphism has dimension at least `d` is closed. -/
theorem fiberDimGe_isClosed (B A : Type*) [CommRing B] [CommRing A]
    [IsDomain B] [IsDomain A] [IsNoetherianRing B]
    [Algebra B A] [Algebra.FiniteType B A]
    (hf : Function.Injective (algebraMap B A))
    (d : ℕ) : IsClosed (fiberDimGe (B := B) (A := A) (d : WithBot ℕ∞)) := by sorry

/-- Chevalley's theorem (Theorem 21.2, part 2): The locus in the image of a dominant
finite-type morphism where the fiber has dimension at least `d` is closed in the image. -/
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

/-- Chevalley's theorem (Theorem 21.2, part 3): For a dominant finite-type morphism, there is
a nonempty basic open of the base on which the morphism is surjective and the dimension
formula `dim(fiber) + dim B = dim A` holds. -/
theorem chevalley_thm21_2_part3 (B A : Type*) [CommRing B] [CommRing A]
    [IsDomain B] [IsDomain A] [IsNoetherianRing B]
    [Algebra B A] [Algebra.FiniteType B A]
    (hf : Function.Injective (algebraMap B A)) :
    ∃ b : B, b ≠ 0 ∧
      (↑(PrimeSpectrum.basicOpen b) : Set (PrimeSpectrum B)) ⊆
        Set.range (PrimeSpectrum.comap (algebraMap B A)) ∧
      ∀ q ∈ (↑(PrimeSpectrum.basicOpen b) : Set (PrimeSpectrum B)),
        fiberKrullDim (A := A) q + ringKrullDim B = ringKrullDim A := by sorry

end
