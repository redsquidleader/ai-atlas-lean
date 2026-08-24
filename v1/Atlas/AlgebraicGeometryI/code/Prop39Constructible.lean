/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.Lec21NormalExtension


namespace Proposition39_g159

open Proposition39

/-- Proposition 39 (codimension-2 extension): if `A` is a Noetherian normal domain with
fraction field `K`, `I` is an ideal of height at least `2`, and `x ∈ K` lies in the
localisation `A_p` at every prime `p` not containing `I`, then `x ∈ A`. -/
theorem proposition_39_codim2_extension
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    (I : Ideal A) (hI : 2 ≤ I.height) (x : K)
    (hx : ∀ (p : PrimeSpectrum A), ¬(I ≤ p.asIdeal) → x ∈ Localization.subalgebra.ofField K
      p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors) :
    x ∈ Set.range (algebraMap A K) :=
  proposition39_codim2_extension I hI x hx

/-- Reformulation of Proposition 39 as an intersection: the image of `A` inside `K` equals
the intersection of all localisations at primes not containing `I`, whenever `I` has
height at least `2`. -/
theorem proposition_39_range
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    (I : Ideal A) (hI : 2 ≤ I.height) :
    Set.range (algebraMap A K) =
    ⋂ (p : PrimeSpectrum A) (_ : ¬(I ≤ p.asIdeal)),
      (Localization.subalgebra.ofField K
        p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors : Set K) :=
  proposition39_range I hI

end Proposition39_g159
