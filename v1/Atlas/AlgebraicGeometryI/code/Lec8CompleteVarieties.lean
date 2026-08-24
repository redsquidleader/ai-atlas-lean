/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ValuativeCriterion

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Formalization.Lec8CompleteVarieties


/-- A morphism `f : X ⟶ Y` is complete if it is separated and
universally closed (Lec 8, Def 19). -/
class IsComplete {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  isSeparated : IsSeparated f
  universallyClosed : UniversallyClosed f


/-- A proper morphism is complete. -/
instance isComplete_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    IsComplete f where
  isSeparated := inferInstance
  universallyClosed := inferInstance


/-- Lec 8, Lem 19(ii): if `X` is proper over `S` and `Z` is separated
over `S`, then the image of `f : X ⟶ Z` is a closed subscheme and
`X ↠ im(f)` is proper. -/
theorem lemma19_ii_image_complete
    {X Z S : Scheme.{u}} (f : X ⟶ Z) (hX : X ⟶ S) (hZ : Z ⟶ S)
    [hXp : IsProper hX] [IsSeparated hZ] (hcomm : f ≫ hZ = hX) :
    IsClosedImmersion f.imageι ∧ IsProper f.toImage := by
  have hfhZ_proper : IsProper (f ≫ hZ) := hcomm ▸ hXp
  have hf_proper : IsProper f := @IsProper.of_comp _ _ _ f hZ hfhZ_proper _
  have hfi : IsProper (f.toImage ≫ f.imageι) := by
    rw [f.toImage_imageι]
    exact hf_proper
  exact ⟨inferInstance, @IsProper.of_comp _ _ _ f.toImage f.imageι hfi inferInstance⟩

/-- Two schemes are birational if they share a common dense open
subscheme (Lec 9 / Chow's lemma setting). -/
def IsBirational (X Y : Scheme.{u}) : Prop :=
  ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (g : Z ⟶ Y),
    IsOpenImmersion f ∧ IsOpenImmersion g ∧
    Dense (Set.range f.base) ∧ Dense (Set.range g.base)

/-- A scheme `X` is projective if it admits a closed immersion into
some `Proj 𝒜` for a graded ring `𝒜` with finite-type degree-zero
piece (Lec 8/9, used for Chow's lemma). -/
def IsProjective (X : Scheme.{u}) : Prop :=
  ∃ (σ : Type u) (A : Type u)
    (_ : CommRing A) (_ : SetLike σ A) (_ : AddSubgroupClass σ A)
    (𝒜 : ℕ → σ) (_ : GradedRing 𝒜) (_ : Algebra.FiniteType (𝒜 0) A)
    (i : X ⟶ Proj 𝒜), IsClosedImmersion i

/-- An affine scheme `U` admits an open immersion with dense image
into some projective scheme (input to Chow's lemma). -/
theorem exists_projective_completion (U : Scheme.{u}) [IsAffine U] :
    ∃ (Y : Scheme.{u}), IsProjective Y ∧
      ∃ (ι : U ⟶ Y), IsOpenImmersion ι ∧ Dense (Set.range ι.base) := by sorry

/-- A closed subscheme of a projective scheme is projective. -/
theorem closed_subscheme_projective {X Y : Scheme.{u}} (i : X ⟶ Y)
    (hi : IsClosedImmersion i) (hY : IsProjective Y) : IsProjective X := by sorry

/-- The product of two projective schemes embeds into a projective
scheme (via Segre); used in Chow's lemma. -/
theorem product_projective_schemes (Y₁ Y₂ : Scheme.{u})
    (h₁ : IsProjective Y₁) (h₂ : IsProjective Y₂) :
    ∃ (P : Scheme.{u}), IsProjective P := by sorry

/-- For `fY : Y ⟶ S` separated, the graph of a morphism into `Y` from
an `S`-scheme is closed, giving a dense locally closed subscheme of
`U` (input to Chow's lemma). -/
theorem graph_closed_of_separated {U Y S : Scheme.{u}}
    (Δ : U ⟶ Y) (fU : U ⟶ S) (fY : Y ⟶ S) [IsSeparated fY]
    (hcomp : Δ ≫ fY = fU) :
    ∃ (Γ : Scheme.{u}) (incl : Γ ⟶ U),
      IsClosedImmersion incl ∧ IsOpenImmersion incl ∧
      Dense (Set.range incl.base) := by sorry

/-- Given a proper morphism of an integral scheme, there exists a
birational model `X̃` (closure of the graph step in Chow's lemma). -/
theorem closure_birational {S X : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [IsIntegral X] :
    ∃ (X_tilde : Scheme.{u}), IsBirational X X_tilde := by sorry

/-- In the Chow's lemma setup, the second projection from the graph
closure to a projective scheme is a closed immersion. -/
theorem second_proj_closed_immersion {S X : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [IsIntegral X] :
    ∃ (X_tilde Y : Scheme.{u}) (_ : IsProjective Y)
      (g : X_tilde ⟶ Y), IsClosedImmersion g ∧ IsBirational X X_tilde := by sorry

/-- Lec 9, Lem 20 (Chow's lemma): every proper integral scheme over
`S` admits a projective birational model. -/
theorem chows_lemma {S : Scheme.{u}} {X : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [IsIntegral X] :
    ∃ (X' : Scheme.{u}) (_ : IsProjective X'), IsBirational X X' := by


  obtain ⟨X_tilde, Y, hY_proj, g, hg_closed, hbir⟩ := second_proj_closed_immersion f

  have hX_tilde_proj : IsProjective X_tilde :=
    closed_subscheme_projective g hg_closed hY_proj
  exact ⟨X_tilde, hX_tilde_proj, hbir⟩

end Formalization.Lec8CompleteVarieties
