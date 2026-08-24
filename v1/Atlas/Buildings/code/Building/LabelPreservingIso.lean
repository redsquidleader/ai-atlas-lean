/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.Building.AptIsoFixesIntersection
import Atlas.Buildings.code.Building.Labels

open scoped Classical

variable {V : Type*} [DecidableEq V]

/-- A map $\varphi : V \to V$ is *label-preserving* on apartment $A$ relative to a given labelling
$\mathrm{lab}$ if it preserves the label of every face of $A$. -/
def IsLabelPreservingMap
    {L : Type*} [DecidableEq L]
    (b : Building V) (A : SimplicialComplex V)
    (lab : Labelling b.toChamberComplex.toSimplicialComplex L)
    (φ : V → V) : Prop :=
  ∀ s ∈ A.faces, lab.labelMap (s.image φ) = lab.labelMap s

/-- A map $\varphi : V \to V$ is *universally label-preserving* on $A$ if it is label-preserving
relative to every labelling of the building. -/
def IsUniversallyLabelPreserving
    (b : Building V) (A : SimplicialComplex V)
    (φ : V → V) : Prop :=
  ∀ (L : Type*) [DecidableEq L] (lab : Labelling b.toChamberComplex.toSimplicialComplex L),
    IsLabelPreservingMap b A lab φ

/-- An apartment isomorphism that fixes the intersection of two apartments $A \cap A'$ (containing
some common chamber $C$) is automatically label-preserving on $A$ for every labelling: such a map
acts as the identity on every face of $A$. -/
theorem apt_iso_fixing_intersection_is_label_preserving
    {V : Type} [DecidableEq V]
    (b : Building V)
    (A A' : SimplicialComplex V)
    (hA : A ∈ b.apartmentSystem.apartments)
    (hA' : A' ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC_A : C ∈ A.faces) (hC_A' : C ∈ A'.faces)
    (hC_max : b.toChamberComplex.toSimplicialComplex.IsMaximal C)
    (φ : V → V)
    (_hφ_face : ∀ s ∈ A.faces, s.image φ ∈ A'.faces)
    (hφ_fixes : ∀ v, (∃ s ∈ A.faces, v ∈ s) → (∃ s ∈ A'.faces, v ∈ s) → φ v = v)
    (L : Type) [DecidableEq L]
    (lab : Labelling b.toChamberComplex.toSimplicialComplex L) :
    ∀ s ∈ A.faces, lab.labelMap (s.image φ) = lab.labelMap s := by


  have hA'_sub_A : A'.faces ⊆ A.faces :=
    apt_faces_subset b A A' hA hA' C hC_A hC_A' hC_max
  have hA_sub_A' : A.faces ⊆ A'.faces :=
    apt_faces_subset b A' A hA' hA C hC_A' hC_A hC_max


  have hφ_id : ∀ v, (∃ s ∈ A.faces, v ∈ s) → φ v = v := by
    intro v hv
    apply hφ_fixes v hv
    obtain ⟨s, hs, hvs⟩ := hv
    exact ⟨s, hA_sub_A' hs, hvs⟩

  intro s hs
  have : s.image φ = s := by
    ext v; simp only [Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hφ_id w ⟨s, hs, hw⟩]; exact hw
    · intro hv; exact ⟨v, hv, hφ_id v ⟨s, hs, hv⟩⟩
  rw [this]

/-- Existence and universality of label-preserving apartment isomorphisms: for any two apartments
$A, A'$ sharing a common chamber $C$, there is a bijection $\varphi$ that fixes $A \cap A'$ and is
label-preserving for every labelling; moreover every such $\varphi$ is label-preserving. -/
theorem apt_iso_label_preserving
    {V : Type} [DecidableEq V]
    (b : Building V)
    (A A' : SimplicialComplex V)
    (hA : A ∈ b.apartmentSystem.apartments)
    (hA' : A' ∈ b.apartmentSystem.apartments)
    (C : Finset V) (hC_A : C ∈ A.faces) (hC_A' : C ∈ A'.faces)
    (hC_max : b.toChamberComplex.toSimplicialComplex.IsMaximal C) :

    (∃ (φ : V → V),
      (∀ s ∈ A.faces, s.image φ ∈ A'.faces) ∧
      (∀ v, (∃ s ∈ A.faces, v ∈ s) → (∃ s ∈ A'.faces, v ∈ s) → φ v = v) ∧
      Function.Bijective φ ∧
      ∀ (L : Type) [DecidableEq L]
        (lab : Labelling b.toChamberComplex.toSimplicialComplex L),
        ∀ s ∈ A.faces, lab.labelMap (s.image φ) = lab.labelMap s) ∧

    (∀ (φ : V → V),
      (∀ s ∈ A.faces, s.image φ ∈ A'.faces) →
      (∀ v, (∃ s ∈ A.faces, v ∈ s) → (∃ s ∈ A'.faces, v ∈ s) → φ v = v) →
      ∀ (L : Type) [DecidableEq L]
        (lab : Labelling b.toChamberComplex.toSimplicialComplex L),
        ∀ s ∈ A.faces, lab.labelMap (s.image φ) = lab.labelMap s) := by
  constructor
  ·
    obtain ⟨φ, hφ_face, hφ_fixes, hφ_bij⟩ :=
      apt_iso_exists_fixing_intersection b A A' hA hA' C hC_A hC_A' hC_max
    have hφ_fwd : ∀ s ∈ A.faces, s.image φ ∈ A'.faces := fun s hs => (hφ_face s).mp hs
    exact ⟨φ, hφ_fwd, hφ_fixes, hφ_bij,
      fun L _ lab => apt_iso_fixing_intersection_is_label_preserving
        b A A' hA hA' C hC_A hC_A' hC_max φ hφ_fwd hφ_fixes L lab⟩
  ·
    intro φ hφ_face hφ_fixes L _ lab
    exact apt_iso_fixing_intersection_is_label_preserving
      b A A' hA hA' C hC_A hC_A' hC_max φ hφ_face hφ_fixes L lab
