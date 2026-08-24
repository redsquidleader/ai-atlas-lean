/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.ChowLemmaHelper
import Atlas.AlgebraicGeometryI.code.ChowHelperBlowupProjective

open AlgebraicGeometry CategoryTheory Limits

universe u

noncomputable section

namespace ChowLemma

/-- A scheme is proper (as an abstract property) when it is equipped with a proper morphism to
some base scheme `S`. -/
class IsProper (X : Scheme.{u}) : Prop where
  exists_proper_morphism : ∃ (S : Scheme.{u}) (f : X ⟶ S), AlgebraicGeometry.IsProper f

/-- A scheme is projective when it embeds as a closed subscheme of some `Proj 𝒜`. -/
def IsProjective (X : Scheme.{u}) : Prop :=
  ChowHelperBlowupProjective.IsProjectiveScheme X

/-- Two schemes are birational when they share a common dense open subscheme. -/
def Birational (X Y : Scheme.{u}) : Prop :=
  ChowHelperBlowupProjective.IsBirational X Y

/-- Chow's lemma (Lem 20, Lec 9): a complete irreducible variety is birational to a projective
variety. -/
theorem chow_lemma (X : Scheme.{u}) [IsProper X] [AlgebraicGeometry.IsIntegral X] :
    ∃ (X' : Scheme.{u}), IsProjective X' ∧ Birational X' X := by

  obtain ⟨S, f, hf⟩ := IsProper.exists_proper_morphism (X := X)

  haveI : AlgebraicGeometry.IsProper f := hf


  obtain ⟨X', hproj, hbir⟩ :=
    ChowHelperBlowupProjective.chow_helper_blowup_projective f


  exact ⟨X', hproj, ChowHelperBlowupProjective.isBirational_symm hbir⟩

end ChowLemma
