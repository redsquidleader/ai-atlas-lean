/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.Lec14QCohProjective

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u

noncomputable section

variable {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The Serre twisting sheaf `O(d)` on `Proj 𝒜`, defined as the tilde of the
shifted graded module `R(d)`. -/
def twistingSheaf (d : ℤ) : (Proj 𝒜).Modules :=
  tildeProj 𝒜 (GrMod.shift 𝒜 d)

/-- Unfolding lemma: `O(d)` is by definition the tilde of the shifted module
`R(d)`. -/
theorem twistingSheaf_eq_tildeProj_shift (d : ℤ) :
    twistingSheaf 𝒜 d = tildeProj 𝒜 (GrMod.shift 𝒜 d) := rfl

/-- Predicate: a sheaf of `O_X`-modules is locally free of rank `n`. -/
noncomputable def IsLocallyFreeRank : {X : Scheme.{u}} → X.Modules → ℕ → Prop := by sorry

/-- A line bundle is a locally free sheaf of rank one. -/
def IsLineBundle {X : Scheme.{u}} (ℱ : X.Modules) : Prop :=
  IsLocallyFreeRank ℱ 1

/-- Each twisting sheaf `O(d)` on `Proj 𝒜` is a line bundle (locally free of
rank one). -/
theorem twistingSheaf_isLineBundle (d : ℤ) :
    IsLineBundle (twistingSheaf 𝒜 d) := by sorry

/-- The degree-`d` graded piece of `A` packaged as an additive subgroup. -/
def degreePiece (d : ℕ) : AddSubgroup A where
  carrier := (𝒜 d : Set A)
  add_mem' ha hb := add_mem ha hb
  zero_mem' := zero_mem (𝒜 d)
  neg_mem' ha := neg_mem ha

/-- Global sections of `O(d)` on `Proj 𝒜` are in bijection with the degree-`d`
graded piece of `𝒜`. -/
theorem globalSections_twistingSheaf (d : ℕ) :
    ∃ (f : (degreePiece 𝒜 d) →+ ((twistingSheaf 𝒜 (↑d)).val.obj (Opposite.op ⊤))),
      Function.Bijective f := by sorry

/-- Corollary 18: every coherent sheaf on `Proj 𝒜` is a quotient of a finite
direct sum of twists `O(-d)^k` of the structure sheaf. -/
theorem cor18_coherent_quotient_of_twistingSheaf
    (ℱ : (Proj 𝒜).Modules)
    (hcoh : IsCoherentSheaf ℱ) :
    ∃ (d : ℕ) (k : ℕ),

      ∃ (φ : tildeProj 𝒜 ((GrMod.shift 𝒜 (-↑d)).directSumCopies k) ⟶ ℱ),
        Epi φ :=
  coherent_sheaf_quotient_of_twisted_structure_sheaf 𝒜 ℱ hcoh

end
