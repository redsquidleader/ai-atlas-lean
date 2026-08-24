/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Lemma29Completeness

universe u


/-- The DVR valuative criterion: every injective map from a DVR to the
function field of `X` extends to a local ring map at some specialization
of the generic point (Lemma 29, completeness setting). -/
def SatisfiesDVRCriterion (X : Scheme.{u}) [IrreducibleSpace X] : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (φ : CommRingCat.of R ⟶ X.functionField) (_ : Function.Injective φ),
    ∃ (x : X) (hx : (genericPoint (X : TopCat) : X) ⤳ x),
      ∃ ψ : X.presheaf.stalk x ⟶ CommRingCat.of R,
        ψ ≫ φ = X.presheaf.stalkSpecializes hx

/-- Lemma 29: for an irreducible reduced scheme `X` over `S`, the DVR
valuative criterion holds iff the structure morphism `X ⟶ S` is proper
(equivalently, `X` is complete). -/
theorem lemma_29_dvr_criterion_iff_complete
    (X S : Scheme.{u}) [X.Over S]
    [IrreducibleSpace X]
    [IsReduced X] :
    SatisfiesDVRCriterion X ↔ IsProper (X ↘ S) := by sorry


/-- Helper for Lemma 29: a proper dominant morphism whose normalization
map is an isomorphism is locally quasi-finite. -/
theorem locallyQuasiFinite_of_isIso_fromNormalization
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsDominant f] [IsIso f.fromNormalization] :
    LocallyQuasiFinite f := by sorry

/-- Lemma 29 (Lec 17): a proper birational morphism to a normal target
is an isomorphism. -/
theorem lemma_29_birational_complete_normal_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f]
    [IsDominant f]
    [IsIso f.fromNormalization] :
    IsIso f := by
  have : LocallyQuasiFinite f := locallyQuasiFinite_of_isIso_fromNormalization f
  have : IsIso f.toNormalization :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  rw [← f.toNormalization_fromNormalization]
  infer_instance

end Lemma29Completeness
