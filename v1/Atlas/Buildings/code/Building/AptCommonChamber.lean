/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.MaximalApartments

open scoped Classical

variable {V : Type} [DecidableEq V]

/-- Section 4.4 corollary in the case of a single apartment system $\mathcal{A}$: for apartments
$A, A' \in \mathcal{A}$ sharing a chamber $C$ that is maximal in $A$, there exists a label-preserving
simplicial map $\varphi : A \to A'$ fixing $A \cap A'$, and every bijective such map preserves labels. -/
theorem section_4_4_corollary_same_system (b : Building V)
    {L : Type} [DecidableEq L]
    (𝒜 : ApartmentSystem b.toChamberComplex)
    (A : SimplicialComplex V) (hA : A ∈ 𝒜.apartments)
    (A' : SimplicialComplex V) (hA' : A' ∈ 𝒜.apartments)
    (C : Finset V) (hCmax : A.IsMaximal C) (hCA' : C ∈ A'.faces)
    (lab : Labelling b.toChamberComplex.toSimplicialComplex L) :

    (∃ φ : SimplicialMap A A',
      (∀ v, (∃ s ∈ A.faces, v ∈ s) → (∃ t ∈ A'.faces, v ∈ t) → φ.toFun v = v) ∧
      (∀ s ∈ A.faces, lab.labelMap (s.image φ.toFun) = lab.labelMap s)) ∧

    (∀ (φ : SimplicialMap A A'),
      Function.Bijective φ.toFun →
      (∀ v, (∃ s ∈ A.faces, v ∈ s) → (∃ t ∈ A'.faces, v ∈ t) → φ.toFun v = v) →
      ∀ s ∈ A.faces, lab.labelMap (s.image φ.toFun) = lab.labelMap s) :=
  section_4_4_corollary b 𝒜 𝒜 A hA A' hA' C hCmax hCA' lab
