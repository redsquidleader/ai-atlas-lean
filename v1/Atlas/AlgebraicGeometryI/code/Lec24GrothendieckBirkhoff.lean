/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Data.Multiset.Sort

open AlgebraicGeometry CategoryTheory Limits

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GrothendieckBirkhoff

variable (k : Type*) [Field k]

/-- The projective line `ℙ¹_k` realised as `Proj k[x₀, x₁]`. -/
noncomputable def P1 : Scheme :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)

/-- The category of `O_{ℙ¹}`-modules on `ℙ¹_k`. -/
noncomputable def ModulesP1 := (P1 k).Modules

/-- The Serre twisting sheaf `O_{ℙ¹}(d)` of degree `d` on `ℙ¹_k`. -/
noncomputable def serreTwist (k : Type*) [Field k] (d : ℤ) : (P1 k).Modules := sorry

/-- The predicate that a sheaf of modules `E` on `X` is locally free of rank `r`
(a vector bundle of rank `r`). -/
def IsLocallyFreeOfRank (X : Scheme) (E : X.Modules) (r : ℕ) : Prop := sorry

/-- A normalisation condition on a vector bundle on `ℙ¹_k`, fixing the convention used
in the inductive proof of the Grothendieck-Birkhoff splitting theorem. -/
def IsNormalized (k : Type*) [Field k] (E : (P1 k).Modules) : Prop := sorry

/-- Any rank-`(r+2)` vector bundle on `ℙ¹_k` can be put into normalised form by twisting,
and any splitting of the normalised bundle yields a splitting of the original. -/
lemma normalization_exists (k : Type*) [Field k]
    (r : ℕ) (E : (P1 k).Modules)
    (hlf : IsLocallyFreeOfRank (P1 k) E (r + 2)) :
    ∃ (E_norm : (P1 k).Modules),
      IsLocallyFreeOfRank (P1 k) E_norm (r + 2) ∧
      IsNormalized k E_norm ∧
      (∀ (d : Fin (r + 2) → ℤ),
        Nonempty (E_norm ≅ ∐ fun i => serreTwist k (d i)) →
        ∃ (d' : Fin (r + 2) → ℤ),
          Nonempty (E ≅ ∐ fun i => serreTwist k (d' i))) := sorry

/-- For a normalised rank-`(r+2)` bundle on `ℙ¹`, a chosen global section gives a rank-`(r+1)`
quotient `E'` whose splitting (with non-positive degrees) lifts back to `E`. -/
lemma section_and_quotient (k : Type*) [Field k]
    (r : ℕ) (E : (P1 k).Modules)
    (hlf : IsLocallyFreeOfRank (P1 k) E (r + 2))
    (hnorm : IsNormalized k E) :
    ∃ (E' : (P1 k).Modules),
      IsLocallyFreeOfRank (P1 k) E' (r + 1) ∧
      (∀ (d : Fin (r + 1) → ℤ), (∀ i, d i ≤ 0) →
        Nonempty (E' ≅ ∐ fun i => serreTwist k (d i)) →
        ∃ (d_full : Fin (r + 2) → ℤ),
          Nonempty (E ≅ ∐ fun i => serreTwist k (d_full i))) := sorry

/-- Normalisation forces the splitting summands of the rank-`(r+1)` quotient to have
non-positive degrees, ensuring the inductive step yields a valid Grothendieck splitting. -/
lemma degree_bound_from_normalization (k : Type*) [Field k]
    (r : ℕ) (E E' : (P1 k).Modules)
    (hlf : IsLocallyFreeOfRank (P1 k) E (r + 2))
    (hnorm : IsNormalized k E)
    (hlf' : IsLocallyFreeOfRank (P1 k) E' (r + 1))
    (d : Fin (r + 1) → ℤ)
    (hd : Nonempty (E' ≅ ∐ fun i => serreTwist k (d i))) :
    ∀ i, d i ≤ 0 := sorry

/-- Base case (rank 0): the zero bundle on `ℙ¹` splits as an empty direct sum of twists. -/
lemma rank_zero_splitting
    (k : Type*) [Field k]
    (E : (P1 k).Modules) (hr : IsLocallyFreeOfRank (P1 k) E 0) :
    ∃ (d : Fin 0 → ℤ), Nonempty (E ≅ ∐ fun i => serreTwist k (d i)) := sorry

/-- Base case (rank 1): every line bundle on `ℙ¹_k` is isomorphic to some `O_{ℙ¹}(d)`. -/
lemma line_bundle_splitting
    (k : Type*) [Field k]
    (E : (P1 k).Modules) (hr : IsLocallyFreeOfRank (P1 k) E 1) :
    ∃ (d : Fin 1 → ℤ), Nonempty (E ≅ ∐ fun i => serreTwist k (d i)) := sorry

/-- Inductive step in the Grothendieck-Birkhoff proof: given the splitting result for all
ranks `≤ r + 1`, every rank-`(r + 2)` bundle splits as a direct sum of Serre twists. -/
theorem inductive_splitting_step
    (r : ℕ)
    (IH : ∀ (s : ℕ), s ≤ r + 1 → ∀ (E' : (P1 k).Modules),
      IsLocallyFreeOfRank (P1 k) E' s →
      ∃ (d : Fin s → ℤ), Nonempty (E' ≅ ∐ fun i => serreTwist k (d i)))
    (E : (P1 k).Modules)
    (hlf : IsLocallyFreeOfRank (P1 k) E (r + 2)) :
    ∃ (d : Fin (r + 2) → ℤ), Nonempty (E ≅ ∐ fun i => serreTwist k (d i)) := by

  obtain ⟨E_norm, hlf_norm, hnorm, transfer⟩ :=
    normalization_exists k r E hlf

  obtain ⟨E', hlf', splitting_from_quotient⟩ :=
    section_and_quotient k r E_norm hlf_norm hnorm

  obtain ⟨d', hd'⟩ := IH (r + 1) (le_refl _) E' hlf'

  have hle : ∀ i, d' i ≤ 0 :=
    degree_bound_from_normalization k r E_norm E' hlf_norm hnorm hlf' d' hd'

  obtain ⟨d_full, hd_full⟩ := splitting_from_quotient d' hle hd'

  exact transfer d_full hd_full

/-- Grothendieck-Birkhoff (Theorem 24.1, existence): Every rank-`r` vector bundle on
`ℙ¹_k` is isomorphic to a direct sum `⨁ O_{ℙ¹}(dᵢ)` of Serre twists. -/
theorem thm24_1_grothendieck_birkhoff_existence
    (E : (P1 k).Modules) (r : ℕ) (hr : IsLocallyFreeOfRank (P1 k) E r) :
    ∃ (d : Fin r → ℤ), Nonempty (E ≅ ∐ fun i => serreTwist k (d i)) := by

  suffices h : ∀ (n : ℕ) (E : (P1 k).Modules),
      IsLocallyFreeOfRank (P1 k) E n →
      ∃ (d : Fin n → ℤ), Nonempty (E ≅ ∐ fun i => serreTwist k (d i)) from
    h r E hr
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro E hlf
    match n, hlf with
    | 0, hlf => exact rank_zero_splitting k E hlf
    | 1, hlf => exact line_bundle_splitting k E hlf
    | n + 2, hlf =>
      exact inductive_splitting_step k n
        (fun s hs E' hlf' => ih s (by omega) E' hlf') E hlf

/-- Helper: Two Grothendieck-Birkhoff splittings of the same bundle agree as multisets
of integers. -/
lemma grothendieck_birkhoff_uniqueness_helper
    (k : Type*) [Field k]
    (E : (P1 k).Modules) (r : ℕ) (hr : IsLocallyFreeOfRank (P1 k) E r)
    (d d' : Fin r → ℤ)
    (hd : Nonempty (E ≅ ∐ fun i => serreTwist k (d i)))
    (hd' : Nonempty (E ≅ ∐ fun i => serreTwist k (d' i))) :
    Multiset.ofList (List.ofFn d) = Multiset.ofList (List.ofFn d') := sorry

/-- Grothendieck-Birkhoff (Theorem 24.1, uniqueness): The multiset of degrees in the
splitting of a vector bundle on `ℙ¹_k` is uniquely determined. -/
theorem thm24_1_grothendieck_birkhoff_uniqueness
    (E : (P1 k).Modules) (r : ℕ) (hr : IsLocallyFreeOfRank (P1 k) E r)
    (d d' : Fin r → ℤ)
    (hd : Nonempty (E ≅ ∐ fun i => serreTwist k (d i)))
    (hd' : Nonempty (E ≅ ∐ fun i => serreTwist k (d' i))) :
    Multiset.ofList (List.ofFn d) = Multiset.ofList (List.ofFn d') :=
  grothendieck_birkhoff_uniqueness_helper k E r hr d d' hd hd'

/-- Grothendieck-Birkhoff (Theorem 24.1, full statement): Every vector bundle on `ℙ¹_k`
splits uniquely (as a multiset of degrees) into a direct sum of Serre twists. -/
theorem thm24_1_grothendieck_birkhoff
    (E : (P1 k).Modules) (r : ℕ) (hr : IsLocallyFreeOfRank (P1 k) E r) :
    (∃ (d : Fin r → ℤ), Nonempty (E ≅ ∐ fun i => serreTwist k (d i))) ∧
    (∀ (d d' : Fin r → ℤ),
      Nonempty (E ≅ ∐ fun i => serreTwist k (d i)) →
      Nonempty (E ≅ ∐ fun i => serreTwist k (d' i)) →
      Multiset.ofList (List.ofFn d) = Multiset.ofList (List.ofFn d')) :=
  ⟨thm24_1_grothendieck_birkhoff_existence k E r hr,
   fun d d' hd hd' => thm24_1_grothendieck_birkhoff_uniqueness k E r hr d d' hd hd'⟩

end GrothendieckBirkhoff
