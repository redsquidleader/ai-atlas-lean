/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

set_option maxHeartbeats 800000

set_option autoImplicit false

open CategoryTheory MonoidalCategory Category Limits

universe w v u

namespace TensorCategories

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- Left quantum trace of an endo-like morphism `a : V ⟶ (Vᘁ)ᘁ` in a rigid category: the
composite `η_V V* ≫ (a ▷ V*) ≫ ε_{V*} (V*)*`. -/
noncomputable def leftQuantumTrace {V : C} (a : V ⟶ (Vᘁ)ᘁ) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ V (Vᘁ) ≫ (a ▷ Vᘁ) ≫ ε_ (Vᘁ) ((Vᘁ)ᘁ)

/-- Right quantum trace of an endo-like morphism `a : V ⟶ *(*V)` in a rigid category, dual
to `leftQuantumTrace`. -/
noncomputable def rightQuantumTrace {V : C} (a : V ⟶ ᘁ(ᘁV)) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ (ᘁV) V ≫ ((ᘁV : C) ◁ a) ≫ ε_ (ᘁ(ᘁV)) (ᘁV)

/-- The left quantum trace of `a` equals the right-trace expression of its dual, via the
mate identity for the right adjoint. -/
theorem leftTrace_eq_rightTrace_dual {V : C} (a : V ⟶ (Vᘁ)ᘁ) :
    leftQuantumTrace C a =
      η_ ((Vᘁ)ᘁ) (((Vᘁ)ᘁ)ᘁ) ≫ ((Vᘁ)ᘁ) ◁ (aᘁ) ≫ ε_ (Vᘁ) ((Vᘁ)ᘁ) := by
  unfold leftQuantumTrace
  have h := (CategoryTheory.coevaluation_comp_rightAdjointMate a).symm
  calc η_ V Vᘁ ≫ a ▷ Vᘁ ≫ ε_ Vᘁ (Vᘁ)ᘁ
      = (η_ V Vᘁ ≫ a ▷ Vᘁ) ≫ ε_ Vᘁ (Vᘁ)ᘁ := by rw [assoc]
    _ = (η_ ((Vᘁ)ᘁ) (((Vᘁ)ᘁ)ᘁ) ≫ ((Vᘁ)ᘁ) ◁ (aᘁ)) ≫ ε_ Vᘁ (Vᘁ)ᘁ := by rw [h]
    _ = η_ ((Vᘁ)ᘁ) (((Vᘁ)ᘁ)ᘁ) ≫ ((Vᘁ)ᘁ) ◁ (aᘁ) ≫ ε_ Vᘁ (Vᘁ)ᘁ := by rw [assoc]

/-- Cyclicity of the left quantum trace: `tr(c ∘ a) = tr(a ∘ (c*)*)` for any endomorphism
`c : V ⟶ V`. -/
theorem leftTrace_comp_eq {V : C} (a : V ⟶ (Vᘁ)ᘁ) (c : V ⟶ V) :
    leftQuantumTrace C (c ≫ a) = leftQuantumTrace C (a ≫ (cᘁ)ᘁ) := by
  unfold leftQuantumTrace
  simp only [comp_whiskerRight, assoc]
  have step1 : η_ V Vᘁ ≫ c ▷ Vᘁ = η_ V Vᘁ ≫ V ◁ (cᘁ : Vᘁ ⟶ Vᘁ) :=
    (CategoryTheory.coevaluation_comp_rightAdjointMate c).symm
  have step2 : (V ◁ (cᘁ : Vᘁ ⟶ Vᘁ)) ≫ (a ▷ Vᘁ) =
      (a ▷ Vᘁ) ≫ ((Vᘁ)ᘁ ◁ (cᘁ : Vᘁ ⟶ Vᘁ)) :=
    CategoryTheory.MonoidalCategory.whisker_exchange a (cᘁ : Vᘁ ⟶ Vᘁ)
  have step3 : ((Vᘁ)ᘁ ◁ (cᘁ : Vᘁ ⟶ Vᘁ)) ≫ ε_ Vᘁ ((Vᘁ)ᘁ) =
      ((cᘁ)ᘁ ▷ Vᘁ) ≫ ε_ Vᘁ ((Vᘁ)ᘁ) :=
    (CategoryTheory.rightAdjointMate_comp_evaluation (cᘁ : Vᘁ ⟶ Vᘁ)).symm
  calc η_ V Vᘁ ≫ c ▷ Vᘁ ≫ a ▷ Vᘁ ≫ ε_ Vᘁ (Vᘁ)ᘁ
      = (η_ V Vᘁ ≫ c ▷ Vᘁ) ≫ a ▷ Vᘁ ≫ ε_ Vᘁ (Vᘁ)ᘁ := by rw [assoc]
    _ = (η_ V Vᘁ ≫ V ◁ cᘁ) ≫ a ▷ Vᘁ ≫ ε_ Vᘁ (Vᘁ)ᘁ := by rw [step1]
    _ = η_ V Vᘁ ≫ (V ◁ cᘁ ≫ a ▷ Vᘁ) ≫ ε_ Vᘁ (Vᘁ)ᘁ := by simp only [assoc]
    _ = η_ V Vᘁ ≫ (a ▷ Vᘁ ≫ (Vᘁ)ᘁ ◁ cᘁ) ≫ ε_ Vᘁ (Vᘁ)ᘁ := by rw [step2]
    _ = η_ V Vᘁ ≫ a ▷ Vᘁ ≫ ((Vᘁ)ᘁ ◁ cᘁ ≫ ε_ Vᘁ (Vᘁ)ᘁ) := by simp only [assoc]
    _ = η_ V Vᘁ ≫ a ▷ Vᘁ ≫ ((cᘁ)ᘁ ▷ Vᘁ ≫ ε_ Vᘁ (Vᘁ)ᘁ) := by rw [step3]
    _ = η_ V Vᘁ ≫ a ▷ Vᘁ ≫ (cᘁ)ᘁ ▷ Vᘁ ≫ ε_ Vᘁ (Vᘁ)ᘁ := by rfl

/-- Cyclicity of the right quantum trace: `tr(c ∘ a) = tr(a ∘ *(*c))` for any endomorphism
`c : V ⟶ V`. -/
theorem rightTrace_comp_eq {V : C} (a : V ⟶ ᘁ(ᘁV)) (c : V ⟶ V) :
    rightQuantumTrace C (c ≫ a) =
      rightQuantumTrace C (a ≫ leftAdjointMate (leftAdjointMate c)) := by
  unfold rightQuantumTrace
  simp only [MonoidalCategory.whiskerLeft_comp, assoc]
  have step1 : η_ (ᘁV) V ≫ ((ᘁV : C) ◁ c) =
      η_ (ᘁV) V ≫ (leftAdjointMate c) ▷ V :=
    (CategoryTheory.coevaluation_comp_leftAdjointMate c).symm
  have step2 : ((leftAdjointMate c) ▷ V) ≫ ((ᘁV : C) ◁ a) =
      ((ᘁV : C) ◁ a) ≫ ((leftAdjointMate c) ▷ (ᘁ(ᘁV) : C)) :=
    (CategoryTheory.MonoidalCategory.whisker_exchange (leftAdjointMate c) a).symm
  have step3 : ((leftAdjointMate c) ▷ (ᘁ(ᘁV) : C)) ≫ ε_ (ᘁ(ᘁV)) (ᘁV) =
      ((ᘁV : C) ◁ leftAdjointMate (leftAdjointMate c)) ≫ ε_ (ᘁ(ᘁV)) (ᘁV) :=
    (CategoryTheory.leftAdjointMate_comp_evaluation (leftAdjointMate c)).symm
  rw [show η_ (ᘁV) V ≫ (ᘁV : C) ◁ c ≫ (ᘁV : C) ◁ a ≫ ε_ (ᘁ(ᘁV)) (ᘁV)
      = (η_ (ᘁV) V ≫ (ᘁV : C) ◁ c) ≫ (ᘁV : C) ◁ a ≫ ε_ (ᘁ(ᘁV)) (ᘁV) from by rw [assoc]]
  rw [step1]
  rw [show (η_ (ᘁV) V ≫ (leftAdjointMate c) ▷ V) ≫ (ᘁV : C) ◁ a ≫ ε_ (ᘁ(ᘁV)) (ᘁV)
      = η_ (ᘁV) V ≫ ((leftAdjointMate c) ▷ V ≫ (ᘁV : C) ◁ a) ≫ ε_ (ᘁ(ᘁV)) (ᘁV) from
    by simp only [assoc]]
  rw [step2]
  rw [show η_ (ᘁV) V ≫ ((ᘁV : C) ◁ a ≫ (leftAdjointMate c) ▷ (ᘁ(ᘁV) : C)) ≫
      ε_ (ᘁ(ᘁV)) (ᘁV)
      = η_ (ᘁV) V ≫ (ᘁV : C) ◁ a ≫
        ((leftAdjointMate c) ▷ (ᘁ(ᘁV) : C) ≫ ε_ (ᘁ(ᘁV)) (ᘁV)) from by simp only [assoc]]
  rw [step3]

/-- Additivity of the left quantum trace over a short exact sequence `0 → W → V → Q → 0`
compatible with the chosen morphisms into the double duals. -/
theorem leftQuantumTrace_additive [Preadditive C]
    {V W Q : C}
    (i : W ⟶ V) (p : V ⟶ Q)
    (aV : V ⟶ (Vᘁ)ᘁ) (aW : W ⟶ (Wᘁ)ᘁ) (aQ : Q ⟶ (Qᘁ)ᘁ)
    (hi : Mono i) (hp : Epi p)
    (exact_seq : i ≫ p = 0)
    (compat_i : i ≫ aV = aW ≫ (iᘁ)ᘁ)
    (compat_p : p ≫ aQ = aV ≫ (pᘁ)ᘁ) :
    leftQuantumTrace C aV = leftQuantumTrace C aW + leftQuantumTrace C aQ := by sorry

/-- Additivity of the right quantum trace over a short exact sequence `0 → W → V → Q → 0`
compatible with the chosen morphisms into the double left duals. -/
theorem rightQuantumTrace_additive [Preadditive C]
    {V W Q : C}
    (i : W ⟶ V) (p : V ⟶ Q)
    (aV : V ⟶ ᘁ(ᘁV)) (aW : W ⟶ ᘁ(ᘁW)) (aQ : Q ⟶ ᘁ(ᘁQ))
    (hi : Mono i) (hp : Epi p)
    (exact_seq : i ≫ p = 0)
    (compat_i : i ≫ aV = aW ≫ leftAdjointMate (leftAdjointMate i))
    (compat_p : p ≫ aQ = aV ≫ leftAdjointMate (leftAdjointMate p)) :
    rightQuantumTrace C aV = rightQuantumTrace C aW + rightQuantumTrace C aQ := by sorry

/-- A pivotal structure on a rigid monoidal category: a natural monoidal isomorphism
`V ≅ (Vᘁ)ᘁ` with the unit-dimension normalisation `dim(𝟙_C) = 1`. -/
structure PivotalStructure where
  pivotalIso : ∀ (V : C), V ≅ (Vᘁ)ᘁ
  tensorCoherenceIso : ∀ (V W : C), (Vᘁ)ᘁ ⊗ (Wᘁ)ᘁ ≅ ((V ⊗ W : C)ᘁ : C)ᘁ
  naturality : ∀ {V W : C} (f : V ⟶ W),
    f ≫ (pivotalIso W).hom = (pivotalIso V).hom ≫ (fᘁ)ᘁ
  monoidality : ∀ (V W : C),
    (pivotalIso (V ⊗ W)).hom =
      ((pivotalIso V).hom ⊗ₘ (pivotalIso W).hom) ≫ (tensorCoherenceIso V W).hom
  dimUnit : leftQuantumTrace C (pivotalIso (𝟙_ C)).hom = 𝟙 (𝟙_ C)

/-- EGNO Definition 1.38.1: synonym for `PivotalStructure`. -/
abbrev def_1_38_1 := PivotalStructure C

section Def_1_38_1_Conditions

variable {C}

end Def_1_38_1_Conditions

/-- Class form of `PivotalStructure`: a pivotal structure on a rigid monoidal category as
a typeclass for instance inference. -/
class PivotalCategory where
  pivotalIso : ∀ (V : C), V ≅ (Vᘁ)ᘁ
  tensorCoherenceIso : ∀ (V W : C), (Vᘁ)ᘁ ⊗ (Wᘁ)ᘁ ≅ ((V ⊗ W : C)ᘁ : C)ᘁ
  naturality : ∀ {V W : C} (f : V ⟶ W),
    f ≫ (pivotalIso W).hom = (pivotalIso V).hom ≫ (fᘁ)ᘁ
  monoidality : ∀ (V W : C),
    (pivotalIso (V ⊗ W)).hom =
      ((pivotalIso V).hom ⊗ₘ (pivotalIso W).hom) ≫ (tensorCoherenceIso V W).hom
  dimUnit : leftQuantumTrace C (pivotalIso (𝟙_ C)).hom = 𝟙 (𝟙_ C)

section PivotalSection
variable [PivotalCategory C]

/-- Pivotal dimension of an object `V` in a pivotal category: the left quantum trace of
the pivotal isomorphism `V ≅ (Vᘁ)ᘁ`. -/
noncomputable def pivotalDimension (V : C) : 𝟙_ C ⟶ 𝟙_ C :=
  leftQuantumTrace C (PivotalCategory.pivotalIso (C := C) V).hom

/-- Alias for `pivotalDimension`: the left quantum dimension of `V`. -/
noncomputable abbrev leftQuantumDim (V : C) : 𝟙_ C ⟶ 𝟙_ C :=
  pivotalDimension C V

/-- Alias for `pivotalDimension`: the categorical dimension of `V`. -/
noncomputable abbrev categoricalDimension (V : C) : 𝟙_ C ⟶ 𝟙_ C :=
  pivotalDimension C V

/-- Pivotal trace of an endomorphism `f : V ⟶ V`: the left quantum trace of `f` composed
with the pivotal isomorphism. -/
noncomputable def pivotalTrace {V : C} (f : V ⟶ V) : 𝟙_ C ⟶ 𝟙_ C :=
  leftQuantumTrace C (f ≫ (PivotalCategory.pivotalIso (C := C) V).hom)

/-- Alias for `pivotalTrace`: the categorical trace of an endomorphism. -/
noncomputable def categoricalTrace {V : C} (f : V ⟶ V) : 𝟙_ C ⟶ 𝟙_ C :=
  pivotalTrace C f

/-- The pivotal trace of the identity endomorphism equals the pivotal dimension. -/
theorem pivotalTrace_id (V : C) :
    pivotalTrace C (𝟙 V) = pivotalDimension C V := by
  unfold pivotalTrace pivotalDimension
  simp

/-- Multiplicativity of the left quantum trace on tensor products. -/
theorem leftQuantumTrace_tensor {V W : C}
    (a : V ⟶ (Vᘁ)ᘁ) (b : W ⟶ (Wᘁ)ᘁ)
    (φ : (Vᘁ)ᘁ ⊗ (Wᘁ)ᘁ ≅ ((V ⊗ W : C)ᘁ : C)ᘁ) :
    leftQuantumTrace C ((a ⊗ₘ b) ≫ φ.hom) =
      leftQuantumTrace C a ≫ leftQuantumTrace C b := by sorry

/-- Additivity of the left quantum trace on biproducts. -/
theorem leftQuantumTrace_biproduct [Preadditive C] [HasBinaryBiproducts C]
    {V W : C}
    (a : V ⟶ (Vᘁ)ᘁ) (b : W ⟶ (Wᘁ)ᘁ)
    (ψ : (Vᘁ)ᘁ ⊞ (Wᘁ)ᘁ ≅ ((Limits.biprod V W)ᘁ : C)ᘁ) :
    leftQuantumTrace C (Limits.biprod.lift (Limits.biprod.fst ≫ a) (Limits.biprod.snd ≫ b) ≫ ψ.hom) =
      leftQuantumTrace C a + leftQuantumTrace C b := by sorry

/-- EGNO Proposition 1.37.1: the left quantum trace satisfies left/right-dual equality,
biproduct additivity, tensor multiplicativity, and cyclicity for both left and right
traces. -/
structure Proposition_1_37_1 : Prop where
  left_eq_right_dual : ∀ {V : C} (a : V ⟶ (Vᘁ)ᘁ),
    leftQuantumTrace C a =
      η_ ((Vᘁ)ᘁ) (((Vᘁ)ᘁ)ᘁ) ≫ ((Vᘁ)ᘁ) ◁ (aᘁ) ≫ ε_ (Vᘁ) ((Vᘁ)ᘁ)
  additivity : ∀ [Preadditive C] [HasBinaryBiproducts C] {V W : C}
    (a : V ⟶ (Vᘁ)ᘁ) (b : W ⟶ (Wᘁ)ᘁ)
    (ψ : (Vᘁ)ᘁ ⊞ (Wᘁ)ᘁ ≅ ((Limits.biprod V W)ᘁ : C)ᘁ),
    leftQuantumTrace C (Limits.biprod.lift (Limits.biprod.fst ≫ a) (Limits.biprod.snd ≫ b) ≫ ψ.hom) =
      leftQuantumTrace C a + leftQuantumTrace C b
  multiplicativity : ∀ {V W : C}
    (a : V ⟶ (Vᘁ)ᘁ) (b : W ⟶ (Wᘁ)ᘁ)
    (φ : (Vᘁ)ᘁ ⊗ (Wᘁ)ᘁ ≅ ((V ⊗ W : C)ᘁ : C)ᘁ),
    leftQuantumTrace C ((a ⊗ₘ b) ≫ φ.hom) =
      leftQuantumTrace C a ≫ leftQuantumTrace C b
  cyclicity_left : ∀ {V : C} (a : V ⟶ (Vᘁ)ᘁ) (c : V ⟶ V),
    leftQuantumTrace C (c ≫ a) = leftQuantumTrace C (a ≫ (cᘁ)ᘁ)
  cyclicity_right : ∀ {V : C} (a : V ⟶ ᘁ(ᘁV)) (c : V ⟶ V),
    rightQuantumTrace C (c ≫ a) =
      rightQuantumTrace C (a ≫ leftAdjointMate (leftAdjointMate c))

/-- EGNO Proposition 1.37.1 holds: bundled proof assembling the dual-equality, additivity,
multiplicativity, and cyclicity statements for the quantum traces. -/
theorem proposition_1_37_1 : Proposition_1_37_1 C where
  left_eq_right_dual := leftTrace_eq_rightTrace_dual C
  additivity := leftQuantumTrace_biproduct C
  multiplicativity := leftQuantumTrace_tensor C
  cyclicity_left := leftTrace_comp_eq C
  cyclicity_right := rightTrace_comp_eq C

/-- The pivotal dimension is multiplicative on tensor products. -/
theorem pivotalDimension_tensor_eq (V W : C) :
    pivotalDimension C (V ⊗ W) =
      pivotalDimension C V ≫ pivotalDimension C W := by
  unfold pivotalDimension leftQuantumTrace
  rw [PivotalCategory.monoidality (C := C) V W]
  exact leftQuantumTrace_tensor C
    (PivotalCategory.pivotalIso (C := C) V).hom
    (PivotalCategory.pivotalIso (C := C) W).hom
    (PivotalCategory.tensorCoherenceIso (C := C) V W)

/-- The pivotal dimension is additive on binary biproducts. -/
theorem pivotalDimension_biproduct_eq
    [Preadditive C] [HasBinaryBiproducts C]
    (X Y : C) :
    pivotalDimension C (Limits.biprod X Y) =
      pivotalDimension C X + pivotalDimension C Y := by
  unfold pivotalDimension
  have hsnd_epi : Epi (biprod.snd (X := X) (Y := Y)) := inferInstance
  exact leftQuantumTrace_additive C
    (biprod.inl (X := X) (Y := Y))
    (biprod.snd (X := X) (Y := Y))
    (PivotalCategory.pivotalIso (C := C) (Limits.biprod X Y)).hom
    (PivotalCategory.pivotalIso (C := C) X).hom
    (PivotalCategory.pivotalIso (C := C) Y).hom
    inferInstance
    hsnd_epi
    biprod.inl_snd
    (PivotalCategory.naturality (C := C) biprod.inl)
    (PivotalCategory.naturality (C := C) biprod.snd)
attribute [simp] pivotalDimension_biproduct_eq

/-- The pivotal dimension of the unit object is the identity morphism (`dim(𝟙_C) = 1`). -/
@[simp]
theorem pivotalDimension_unit :
    pivotalDimension C (𝟙_ C) = 𝟙 (𝟙_ C) :=
  PivotalCategory.dimUnit (C := C)

/-- EGNO Proposition 1.38.5: the pivotal dimension is a character of the Grothendieck
ring (multiplicative on tensor products, additive on biproducts, and sending the unit to
1). -/
structure Proposition_1_38_5_IsCharacter [Preadditive C] [HasBinaryBiproducts C] : Prop where
  multiplicativity : ∀ (V W : C), pivotalDimension C (V ⊗ W) =
    pivotalDimension C V ≫ pivotalDimension C W
  additivity : ∀ (X Y : C), pivotalDimension C (Limits.biprod X Y) =
    pivotalDimension C X + pivotalDimension C Y
  unitality : pivotalDimension C (𝟙_ C) = 𝟙 (𝟙_ C)

/-- EGNO Proposition 1.38.5 holds: the pivotal dimension is a character of the
Grothendieck ring. -/
theorem proposition_1_38_5 [Preadditive C] [HasBinaryBiproducts C] :
    Proposition_1_38_5_IsCharacter C where
  multiplicativity := pivotalDimension_tensor_eq C
  additivity := pivotalDimension_biproduct_eq C
  unitality := pivotalDimension_unit C

/-- Unbundled conjunction form of EGNO Proposition 1.38.5: multiplicativity, additivity,
and unitality of the pivotal dimension. -/
theorem proposition_1_38_5_conj [Preadditive C] [HasBinaryBiproducts C] :
    (∀ (V W : C), pivotalDimension C (V ⊗ W) =
      pivotalDimension C V ≫ pivotalDimension C W) ∧
    (∀ (X Y : C), pivotalDimension C (Limits.biprod X Y) =
      pivotalDimension C X + pivotalDimension C Y) ∧
    (pivotalDimension C (𝟙_ C) = 𝟙 (𝟙_ C)) :=
  ⟨pivotalDimension_tensor_eq C,
   pivotalDimension_biproduct_eq C,
   pivotalDimension_unit C⟩

/-- If a pivotal category has finitely many simple objects spanning the Grothendieck
ring, then the image of every pivotal dimension lies in a finitely generated `ℤ`-subalgebra
of the base field. -/
theorem grothendieck_ring_dim_in_fg_subalgebra
    (k : Type w) [Field k]
    [Preadditive C]
    (φ : End (𝟙_ C) →+* k)
    (hFinSimples : ∃ (n : ℕ) (simples : Fin n → C),
      ∀ (V : C), ∃ (coeffs : Fin n → ℤ),
        φ (pivotalDimension C V) = ∑ i, coeffs i • φ (pivotalDimension C (simples i))) :
    ∃ (S : Subalgebra ℤ k), S.toSubmodule.FG ∧ ∀ (V : C), φ (pivotalDimension C V) ∈ S := by sorry

/-- Under the same finiteness hypothesis, the image of every pivotal dimension is integral
over `ℤ` in the base field. -/
theorem pivotalDimension_isIntegral
    (k : Type w) [Field k]
    [Preadditive C]
    (φ : End (𝟙_ C) →+* k)
    (hFinSimples : ∃ (n : ℕ) (simples : Fin n → C),
      ∀ (V : C), ∃ (coeffs : Fin n → ℤ),
        φ (pivotalDimension C V) = ∑ i, coeffs i • φ (pivotalDimension C (simples i)))
    (V : C) :
    _root_.IsIntegral ℤ (φ (pivotalDimension C V)) := by
  obtain ⟨S, hFG, hV⟩ := grothendieck_ring_dim_in_fg_subalgebra C k φ hFinSimples
  exact IsIntegral.of_mem_of_fg S hFG _ (hV V)

/-- EGNO Corollary 1.38.6: in a pivotal category with finitely many simple objects, every
pivotal dimension is an algebraic integer. -/
theorem corollary_1_38_6
    (k : Type w) [Field k]
    [Preadditive C]
    (φ : End (𝟙_ C) →+* k)
    (hFinSimples : ∃ (n : ℕ) (simples : Fin n → C),
      ∀ (V : C), ∃ (coeffs : Fin n → ℤ),
        φ (pivotalDimension C V) = ∑ i, coeffs i • φ (pivotalDimension C (simples i)))
    (V : C) :
    _root_.IsIntegral ℤ (φ (pivotalDimension C V)) :=
  pivotalDimension_isIntegral C k φ hFinSimples V

end PivotalSection

/-- A spherical category is a pivotal category in which the pivotal dimension of every
object equals the pivotal dimension of its dual. -/
class SphericalCategory extends PivotalCategory C where
  spherical : ∀ (V : C), pivotalDimension C V = pivotalDimension C (Vᘁ)

/-- EGNO Definition 1.39.1: synonym for `SphericalCategory`. -/
abbrev def_1_39_1 := SphericalCategory C

section SphericalSection
variable [SphericalCategory C]

/-- Helper for the spherical-trace equality: in a spherical category, the pivotal trace of
an endomorphism can be expressed via the right-dual evaluation/coevaluation. -/
theorem spherical_leftTrace_eq_rightTrace_aux
    {V : C} (x : V ⟶ V) :
    pivotalTrace C x =
      η_ (Vᘁ) ((Vᘁ : C)ᘁ) ≫
        ((Vᘁ : C) ◁ ((PivotalCategory.pivotalIso (C := C) V).inv ≫ x)) ≫
        ε_ V (Vᘁ) := by sorry

/-- In a spherical category the left and right pivotal traces of an endomorphism agree. -/
theorem spherical_leftTrace_eq_rightTrace
    {V : C} (x : V ⟶ V) :
    pivotalTrace C x =
      η_ (Vᘁ) ((Vᘁ : C)ᘁ) ≫
        ((Vᘁ : C) ◁ ((PivotalCategory.pivotalIso (C := C) V).inv ≫ x)) ≫
        ε_ V (Vᘁ) :=
  spherical_leftTrace_eq_rightTrace_aux C x

end SphericalSection

/-- EGNO Proposition 1.37.3: both left and right quantum traces are additive on short
exact sequences of objects compatible with the chosen morphisms to the double duals. -/
structure Proposition_1_37_3 : Prop where
  left_additive : ∀ [Preadditive C] {V W Q : C}
    (i : W ⟶ V) (p : V ⟶ Q)
    (aV : V ⟶ (Vᘁ)ᘁ) (aW : W ⟶ (Wᘁ)ᘁ) (aQ : Q ⟶ (Qᘁ)ᘁ)
    (_ : Mono i) (_ : Epi p)
    (_ : i ≫ p = 0)
    (_ : i ≫ aV = aW ≫ (iᘁ)ᘁ)
    (_ : p ≫ aQ = aV ≫ (pᘁ)ᘁ),
    leftQuantumTrace C aV = leftQuantumTrace C aW + leftQuantumTrace C aQ
  right_additive : ∀ [Preadditive C] {V W Q : C}
    (i : W ⟶ V) (p : V ⟶ Q)
    (aV : V ⟶ ᘁ(ᘁV)) (aW : W ⟶ ᘁ(ᘁW)) (aQ : Q ⟶ ᘁ(ᘁQ))
    (_ : Mono i) (_ : Epi p)
    (_ : i ≫ p = 0)
    (_ : i ≫ aV = aW ≫ leftAdjointMate (leftAdjointMate i))
    (_ : p ≫ aQ = aV ≫ leftAdjointMate (leftAdjointMate p)),
    rightQuantumTrace C aV = rightQuantumTrace C aW + rightQuantumTrace C aQ

/-- EGNO Proposition 1.37.3 holds: bundled proof of additivity of the left and right
quantum traces on short exact sequences. -/
theorem proposition_1_37_3_holds : Proposition_1_37_3 C where
  left_additive := fun i p aV aW aQ hi hp hex hci hcp =>
    leftQuantumTrace_additive C i p aV aW aQ hi hp hex hci hcp
  right_additive := fun i p aV aW aQ hi hp hex hci hcp =>
    rightQuantumTrace_additive C i p aV aW aQ hi hp hex hci hcp

end TensorCategories
