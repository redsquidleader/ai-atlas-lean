/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Noetherian.Basic
import Atlas.AlgebraicGeometryI.code.Lec21NormalExtension

noncomputable section

open PrimeSpectrum

/-- Proposition 39 (Lecture 20). On a normal Noetherian domain `R`, the intersection over
primes `p` with `I ⊄ p` of the localizations `R_p ⊂ K` is trivial (equal to `R` itself, i.e.
the bottom subalgebra), provided `I` has height ≥ 2. This is the algebraic form of
"regular functions extend across closed subsets of codimension ≥ 2 in a normal variety". -/
theorem normal_codim2_extension
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (I : Ideal R) (hI : 2 ≤ I.height) :
    (⨅ (p : PrimeSpectrum R) (_ : ¬ (I ≤ p.asIdeal)),
      Localization.subalgebra.ofField K p.asIdeal.primeCompl
        p.asIdeal.primeCompl_le_nonZeroDivisors) = ⊥ := by
  apply le_antisymm
  ·
    rw [← Proposition39.iInf_heightOnePrime_localization_eq_bot (A := R) (K := K)]
    apply le_iInf
    intro q
    apply iInf_le_of_le ⟨q.asIdeal, q.isPrime⟩
    apply iInf_le_of_le (not_le_heightOnePrime_of_height_ge_two I hI q)
    exact le_refl _
  · exact bot_le

/-- Element-level form of Proposition 39: an element of the fraction field `K` that lies in
`R_p` for every prime `p` outside the codimension-≥-2 locus `V(I)` is in fact in the image
of `R → K`. -/
theorem normal_codim2_extension_mem
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (I : Ideal R) (hI : 2 ≤ I.height)
    (x : K) (hx : ∀ (p : PrimeSpectrum R), ¬ (I ≤ p.asIdeal) →
      x ∈ Localization.subalgebra.ofField K p.asIdeal.primeCompl
        p.asIdeal.primeCompl_le_nonZeroDivisors) :
    x ∈ Set.range (algebraMap R K) := by
  rw [← Algebra.mem_bot]
  rw [← normal_codim2_extension R K I hI]
  simp only [Algebra.mem_iInf]
  exact hx

end
