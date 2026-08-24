/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

noncomputable section
open Ideal

/-- Krull dimension of a commutative ring as a natural number
(returning `0` in degenerate or infinite cases). -/
def dimNat (R : Type*) [CommRing R] : ℕ :=
  (Option.getD (ringKrullDim R) ⊤).toNat

/-- Equidimensionality of polynomial rings (Lec 8, Prop 10): for any
prime ideal `Q` in `k[x_1,…,x_n]`, height `Q` plus dimension of the
quotient equals `n`. -/
theorem equidimensional_mvpoly_nat
    (k : Type*) [Field k] (n : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) k)) [Q.IsPrime] :
    Q.height.toNat + dimNat (MvPolynomial (Fin n) k ⧸ Q) = n := by sorry

/-- Lec 8, Thm 8.1 (intersection codimension, dimension form): for any
two irreducible subvarieties of `𝔸ⁿ` and a minimal prime `P` over
their sum, `dim X + dim Y ≤ dim(X ∩ Y) + n`. -/
theorem intersection_dim_bound_nat
    (k : Type*) [Field k] (n : ℕ)
    (I J : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime] [J.IsPrime]
    (P : Ideal (MvPolynomial (Fin n) k))
    (hP : P ∈ (I ⊔ J).minimalPrimes) :
    dimNat (MvPolynomial (Fin n) k ⧸ I) +
    dimNat (MvPolynomial (Fin n) k ⧸ J) ≤
    dimNat (MvPolynomial (Fin n) k ⧸ P) + n := by sorry

/-- Lec 8, Thm 8.1 (intersection codimension): for prime ideals
`I, J ⊆ k[x_1,…,x_n]` and any minimal prime `P` over `I + J`,
the codimension of `P` is at most the sum of codimensions of `I, J`. -/
theorem thm81_intersection_codim_bound
    (k : Type*) [Field k] (n : ℕ)
    (I J : Ideal (MvPolynomial (Fin n) k)) [I.IsPrime] [J.IsPrime]
    (P : Ideal (MvPolynomial (Fin n) k))
    (hP : P ∈ (I ⊔ J).minimalPrimes) :
    P.height ≤ I.height + J.height := by

  have hPprime : P.IsPrime := hP.1.1
  haveI : P.IsPrime := hPprime

  have hI_ne : I.height ≠ ⊤ := Ideal.height_ne_top ‹I.IsPrime›.ne_top
  have hJ_ne : J.height ≠ ⊤ := Ideal.height_ne_top ‹J.IsPrime›.ne_top
  have hP_ne : P.height ≠ ⊤ := Ideal.height_ne_top hPprime.ne_top

  have eqP := equidimensional_mvpoly_nat k n P
  have eqI := equidimensional_mvpoly_nat k n I
  have eqJ := equidimensional_mvpoly_nat k n J

  have bound := intersection_dim_bound_nat k n I J P hP

  suffices h : P.height.toNat ≤ I.height.toNat + J.height.toNat by
    rw [(ENat.coe_toNat hP_ne).symm]
    calc (↑P.height.toNat : ℕ∞)
        ≤ ↑(I.height.toNat + J.height.toNat) := by exact_mod_cast h
      _ = ↑I.height.toNat + ↑J.height.toNat := by push_cast; ring
      _ = I.height + J.height := by rw [ENat.coe_toNat hI_ne, ENat.coe_toNat hJ_ne]

  omega

/-- A minimal prime over `I + J` in a noetherian ring has height at
most the sum of the span-ranks of `I` and `J` (via Krull's height
theorem). -/
theorem height_minPrime_sup_le_spanRank_add
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I J : Ideal R) (P : Ideal R)
    (hP : P ∈ (I ⊔ J).minimalPrimes) :
    P.height ≤ Cardinal.toENat (Submodule.spanRank I) +
               Cardinal.toENat (Submodule.spanRank J) :=
  calc P.height
      ≤ Cardinal.toENat (Submodule.spanRank (I ⊔ J)) :=
        Ideal.height_le_spanRank_toENat_of_mem_minimal_primes _ _ hP
    _ ≤ Cardinal.toENat (Submodule.spanRank I + Submodule.spanRank J) :=
        OrderHomClass.mono Cardinal.toENat Submodule.spanRank_sup_le_sum_spanRank
    _ = Cardinal.toENat (Submodule.spanRank I) + Cardinal.toENat (Submodule.spanRank J) :=
        map_add Cardinal.toENat _ _

/-- A minimal prime over `I + J` in a noetherian ring has height at
most the sum of the (finite) span-ranks of `I` and `J`. -/
theorem height_minPrime_sup_le_spanFinrank_add
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I J : Ideal R) (P : Ideal R)
    (hP : P ∈ (I ⊔ J).minimalPrimes) :
    P.height ≤ ↑(Submodule.spanFinrank I + Submodule.spanFinrank J) := by
  have h := height_minPrime_sup_le_spanRank_add I J P hP

  have hfgI : I.FG := IsNoetherian.noetherian I
  have hfgJ : J.FG := IsNoetherian.noetherian J
  have hltI := Submodule.spanRank_finite_iff_fg.mpr hfgI
  have hltJ := Submodule.spanRank_finite_iff_fg.mpr hfgJ
  obtain ⟨nI, hI⟩ := Cardinal.lt_aleph0.mp hltI
  obtain ⟨nJ, hJ⟩ := Cardinal.lt_aleph0.mp hltJ
  simp only [Submodule.spanFinrank, hI, hJ, Cardinal.toNat_natCast] at h ⊢
  simpa [Cardinal.toENat_nat] using h

end
