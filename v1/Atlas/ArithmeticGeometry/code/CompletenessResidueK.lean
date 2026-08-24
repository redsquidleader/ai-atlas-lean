/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.ValuationResidue

universe u

open AlgebraicGeometry.CompletenessValuationCriterion

def HasResidueFieldK {k : Type u} [Field k] {V : AlgVariety k} (R : ValRingOver V) : Prop :=
  ∃ (Φ : R.valSub →+* k),
    (RingHom.ker Φ = IsLocalRing.maximalIdeal R.valSub) ∧
    Function.Surjective Φ

def SatisfiesValuationCriterionResidueK {k : Type u} [Field k] (X : AlgVariety k) : Prop :=
  ∀ (Z : SubvarietyOf X) (R : ValRingOver Z.toVariety),
    HasResidueFieldK R →
    ∃ P : Z.toVariety.carrier, localRing_le P R

theorem corollary_16_31 {k : Type u} [Field k] [IsAlgClosed k]
    (X : AlgVariety k)
    (hX : SatisfiesValuationCriterionResidueK X) :
    IsCompleteVariety X.carrier := by
  apply completeness_valuation_criterion X
  intro Z R

  obtain ⟨R'_val, hle, hkR', Φ, hker, hsurj⟩ :=
    lemma_16_30 Z.toVariety.baseEmbed Z.toVariety.baseEmbed_inj R.valSub R.contains_base

  let R' : ValRingOver Z.toVariety := ⟨R'_val, hkR'⟩

  have hres : HasResidueFieldK R' := ⟨Φ, hker, hsurj⟩

  obtain ⟨P, hP⟩ := hX Z R' hres

  exact ⟨P, fun x hx => hle (hP x hx)⟩
