/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Yoneda
import Atlas.TensorCategories.code.InvertibleObjects

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category

universe v u

namespace CategoryTheory


section TensorDual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- In a rigid monoidal category, the right dual of a tensor product `X ⊗ Y` is naturally
isomorphic to `Yᘁ ⊗ Xᘁ`. -/
theorem rightDualTensorIso' (X Y : C) :
    Nonempty (HasRightDual.rightDual (X ⊗ Y) ≅
      HasRightDual.rightDual Y ⊗ HasRightDual.rightDual X) := by
  have adj1 := tensorRightAdjunction (X ⊗ Y) ((X ⊗ Y)ᘁ)
  have comp_adj := (tensorRightAdjunction X (Xᘁ : C)).comp (tensorRightAdjunction Y (Yᘁ : C))
  have assoc1 : tensorRight X ⋙ tensorRight Y ≅ tensorRight (X ⊗ Y) :=
    NatIso.ofComponents (fun Z => (α_ Z X Y)) (by intros; simp [tensorRight])
  have assoc2 : tensorRight (Yᘁ : C) ⋙ tensorRight (Xᘁ : C) ≅
      tensorRight ((Yᘁ : C) ⊗ (Xᘁ : C)) :=
    NatIso.ofComponents (fun Z => (α_ Z Yᘁ Xᘁ)) (by intros; simp [tensorRight])
  have adj2 := (comp_adj.ofNatIsoLeft assoc1).ofNatIsoRight assoc2
  exact ⟨(λ_ ((X ⊗ Y)ᘁ)).symm ≪≫
    (Adjunction.rightAdjointUniq adj1 adj2).app (𝟙_ C) ≪≫
    (λ_ ((Yᘁ : C) ⊗ (Xᘁ : C)))⟩

end TensorDual


section Corollary

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- The double right dual `(Xᘁ)ᘁ` of an object `X` in a rigid monoidal category. -/
def doubleDualObj (X : C) : C :=
  HasRightDual.rightDual (HasRightDual.rightDual X)

variable (C) in
/-- A choice of distinguished invertible object `L_ρ` in a rigid monoidal category `C`,
along with a proof that it is invertible. This is the categorical analogue of the
distinguished group-like element in a quasi-Hopf algebra (Section 1.51). -/
class HasDistinguishedInvData where
  distinguished : C
  invertible : IsInvertibleObject distinguished

variable [HasDistinguishedInvData C]

/-- The distinguished invertible object `L_ρ` of `C` supplied by `HasDistinguishedInvData`. -/
def distinguishedObj : C := HasDistinguishedInvData.distinguished (C := C)

/-- The distinguished object `L_ρ` is invertible. -/
instance distinguishedObj_invertible : IsInvertibleObject (distinguishedObj (C := C)) :=
  HasDistinguishedInvData.invertible (C := C)

/-- Axiom-form statement (Lemma 1.51.2 for projectives): for any projective object `P`,
its right dual `Pᘁ` is isomorphic to `P ⊗ L_ρ`. -/
theorem dualIsoTensorD_axiom : ∀ (P : C) [Projective P],
    Nonempty (HasRightDual.rightDual P ≅ P ⊗ distinguishedObj (C := C)) := by
  intro P _
  sorry

/-- Axiom-form statement (Lemma 1.51.2 for simples): for any simple object `L`, its right
dual `Lᘁ` is isomorphic to `L ⊗ L_ρ`. -/
theorem simpleIsoTensorD_axiom' [Limits.HasZeroMorphisms C] :
    ∀ (L : C) [Simple L],
    Nonempty (HasRightDual.rightDual L ≅ L ⊗ distinguishedObj (C := C)) := by
  intro L _
  sorry

/-- Corollary 1.51.3 (projective version): For any projective `P` in a rigid category with
distinguished invertible object `L_ρ`, one has `P** ≅ L_ρᘁ ⊗ P ⊗ L_ρ`. -/
theorem Corollary_1_51_3_projective (P : C) [Projective P] :
    Nonempty (doubleDualObj P ≅
      HasRightDual.rightDual (distinguishedObj (C := C)) ⊗ P ⊗ distinguishedObj (C := C)) := by
  unfold doubleDualObj

  obtain ⟨φ₁⟩ := dualIsoTensorD_axiom P

  obtain ⟨φ₂⟩ := rightDualTensorIso' P (distinguishedObj (C := C))

  obtain ⟨φ₃⟩ := dualIsoTensorD_axiom P

  letI : ExactPairing (HasRightDual.rightDual P) (doubleDualObj P) := HasRightDual.exact
  letI ep₂ : ExactPairing (P ⊗ distinguishedObj (C := C)) (doubleDualObj P) :=
    exactPairingCongrLeft φ₁.symm
  letI ep₃ : ExactPairing (P ⊗ distinguishedObj (C := C))
      (HasRightDual.rightDual (P ⊗ distinguishedObj (C := C))) := HasRightDual.exact
  let ψ₁ : doubleDualObj P ≅ HasRightDual.rightDual (P ⊗ distinguishedObj (C := C)) :=
    rightDualIso ep₂ ep₃

  let ψ₃ : HasRightDual.rightDual (distinguishedObj (C := C)) ⊗ HasRightDual.rightDual P ≅
    HasRightDual.rightDual (distinguishedObj (C := C)) ⊗ (P ⊗ distinguishedObj (C := C)) :=
    tensorIso (Iso.refl _) φ₃
  exact ⟨ψ₁.trans (φ₂.trans ψ₃)⟩

/-- Corollary 1.51.3 (simple version): For any simple object `L` in a rigid category with
distinguished invertible object `L_ρ`, one has `L** ≅ L_ρᘁ ⊗ L ⊗ L_ρ`. -/
theorem Corollary_1_51_3_simple [Limits.HasZeroMorphisms C] (L : C) [Simple L] :
    Nonempty (doubleDualObj L ≅
      HasRightDual.rightDual (distinguishedObj (C := C)) ⊗ L ⊗ distinguishedObj (C := C)) := by
  unfold doubleDualObj

  obtain ⟨φ₁⟩ := simpleIsoTensorD_axiom' L

  obtain ⟨φ₂⟩ := rightDualTensorIso' L (distinguishedObj (C := C))

  obtain ⟨φ₃⟩ := simpleIsoTensorD_axiom' L

  letI : ExactPairing (HasRightDual.rightDual L) (doubleDualObj L) := HasRightDual.exact
  letI ep₂ : ExactPairing (L ⊗ distinguishedObj (C := C)) (doubleDualObj L) :=
    exactPairingCongrLeft φ₁.symm
  letI ep₃ : ExactPairing (L ⊗ distinguishedObj (C := C))
      (HasRightDual.rightDual (L ⊗ distinguishedObj (C := C))) := HasRightDual.exact
  let ψ₁ : doubleDualObj L ≅ HasRightDual.rightDual (L ⊗ distinguishedObj (C := C)) :=
    rightDualIso ep₂ ep₃

  let ψ₃ : HasRightDual.rightDual (distinguishedObj (C := C)) ⊗ HasRightDual.rightDual L ≅
    HasRightDual.rightDual (distinguishedObj (C := C)) ⊗ (L ⊗ distinguishedObj (C := C)) :=
    tensorIso (Iso.refl _) φ₃
  exact ⟨ψ₁.trans (φ₂.trans ψ₃)⟩

end Corollary

end CategoryTheory
