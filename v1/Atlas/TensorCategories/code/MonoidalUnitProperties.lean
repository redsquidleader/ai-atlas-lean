/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.Tactic.CategoryTheory.Monoidal.PureCoherence

set_option maxHeartbeats 400000

open CategoryTheory MonoidalCategory Category

universe v u

namespace TensorCategories

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Restatement of the triangle axiom for a monoidal category at any pair of objects. -/
theorem triangle_diagram (X Y : C) :
    (α_ X (𝟙_ C) Y).hom ≫ X ◁ (λ_ Y).hom = (ρ_ X).hom ▷ Y :=
  MonoidalCategory.triangle X Y

/-- The left and right unitors of the unit object agree on hom components. -/
theorem leftUnitor_unit_eq_rightUnitor_unit :
    (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom := by
  monoidal_coherence

/-- The left and right unitors of the unit object agree on inv components. -/
theorem leftUnitor_unit_eq_rightUnitor_unit_inv :
    (λ_ (𝟙_ C)).inv = (ρ_ (𝟙_ C)).inv := by
  monoidal_coherence

/-- Part of EGNO Proposition 1.2.2: compatibility of the associator with the left unitor on
the left, expressed via whiskering. -/
theorem prop_1_2_2_left (X Y : C) :
    (α_ (𝟙_ C) X Y).hom ≫ (λ_ (X ⊗ Y)).hom = (λ_ X).hom ▷ Y := by
  simp

/-- Part of EGNO Proposition 1.2.2: compatibility of the associator with the right unitor
on the right, expressed via whiskering. -/
theorem prop_1_2_2_right (X Y : C) :
    (ρ_ (X ⊗ Y)).hom = (α_ X Y (𝟙_ C)).hom ≫ X ◁ (ρ_ Y).hom := by
  simp

/-- EGNO Proposition 1.2.2: the left and right unitors of the unit object coincide. -/
theorem Proposition_1_2_2_leftUnitor_unit_eq_rightUnitor_unit :
    (λ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom :=
  unitors_equal

/-- Part of EGNO Proposition 1.2.3: the left unitor of `𝟙_ C ⊗ X` factors through left
whiskering by the unit. -/
theorem prop_1_2_3_left (X : C) :
    (λ_ (𝟙_ C ⊗ X)).hom = (𝟙_ C) ◁ (λ_ X).hom := by
  rw [leftUnitor_tensor_hom, leftUnitor_unit_eq_rightUnitor_unit,
      ← MonoidalCategory.triangle]
  simp

/-- Part of EGNO Proposition 1.2.3: the right unitor of `X ⊗ 𝟙_ C` factors through right
whiskering by the unit. -/
theorem prop_1_2_3_right (X : C) :
    (ρ_ (X ⊗ 𝟙_ C)).hom = (ρ_ X).hom ▷ (𝟙_ C) := by
  rw [rightUnitor_tensor_hom, ← leftUnitor_unit_eq_rightUnitor_unit]
  simp

/-- EGNO Proposition 1.2.3: the left and right unitor identities at the unit object. -/
theorem Proposition_1_2_3 (X : C) :
    (λ_ (𝟙_ C ⊗ X)).hom = (𝟙_ C) ◁ (λ_ X).hom ∧
    (ρ_ (X ⊗ 𝟙_ C)).hom = (ρ_ X).hom ▷ (𝟙_ C) :=
  ⟨prop_1_2_3_left X, prop_1_2_3_right X⟩

/-- An abstract characterisation of a unit object `U`: it admits natural isomorphisms
exhibiting `tensorRight U` and `tensorLeft U` as the identity functor, and these satisfy
a triangle-type compatibility. -/
structure IsUnitObject (U : C) where
  rightUnitor' : tensorRight U ≅ Functor.id C
  leftUnitor' : tensorLeft U ≅ Functor.id C
  triangle' : ∀ (X Y : C),
    (α_ X U Y).hom ≫ X ◁ (leftUnitor'.hom.app Y) = (rightUnitor'.hom.app X) ▷ Y

/-- The canonical unit object `𝟙_ C` satisfies `IsUnitObject`, with the unitors as its
distinguished natural isomorphisms. -/
noncomputable def unitIsUnitObject : IsUnitObject (𝟙_ C) where
  rightUnitor' := NatIso.ofComponents (fun X => ρ_ X) (by aesop_cat)
  leftUnitor' := NatIso.ofComponents (fun X => λ_ X) (by aesop_cat)
  triangle' := fun X Y => by simp [NatIso.ofComponents]

/-- Construction of an isomorphism `𝟙_ C ≅ U` for any object `U` satisfying
`IsUnitObject`. -/
noncomputable def unit_object_iso_of_isUnit (U : C) (hU : IsUnitObject U) : 𝟙_ C ≅ U :=
  (hU.rightUnitor'.app (𝟙_ C)).symm ≪≫ (λ_ U)

/-- Existence half of EGNO Proposition 1.2.4: any object satisfying `IsUnitObject` is
isomorphic to `𝟙_ C`. -/
theorem prop_1_2_4_existence (U : C) (hU : IsUnitObject U) : Nonempty (𝟙_ C ≅ U) :=
  ⟨unit_object_iso_of_isUnit U hU⟩

/-- The left and right unitors of the unit object coincide as isomorphisms. -/
theorem unit_iso_unique :
    (λ_ (𝟙_ C)) = (ρ_ (𝟙_ C)) := by
  ext
  exact leftUnitor_unit_eq_rightUnitor_unit

/-- The composite of `(λ_ (𝟙_ C)).inv` and `(ρ_ (𝟙_ C)).hom` is the identity on the unit. -/
theorem unit_unique_self_iso :
    (λ_ (𝟙_ C)).inv ≫ (ρ_ (𝟙_ C)).hom = 𝟙 (𝟙_ C) := by
  rw [leftUnitor_unit_eq_rightUnitor_unit_inv]
  simp

/-- Naturality of the right unitor at the unit applied to a hom `c : 𝟙_ C ⟶ 𝟙_ C`. -/
theorem tensorHom_id_right_unit_comm (c : 𝟙_ C ⟶ 𝟙_ C) :
    (c ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom ≫ c := by
  simp [MonoidalCategory.tensorHom_def]

/-- A unit endomorphism `b` that is compatible with the right unitor via `b ⊗ₘ b` is the
identity. -/
theorem unit_endo_compat_is_id (b : 𝟙_ C ⟶ 𝟙_ C) [IsIso b]
    (hb : (b ⊗ₘ b) ≫ (ρ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom ≫ b) :
    b = 𝟙 (𝟙_ C) := by

  have h_nat : (b ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ (𝟙_ C)).hom = (ρ_ (𝟙_ C)).hom ≫ b :=
    tensorHom_id_right_unit_comm b

  have h_eq : b ⊗ₘ b = b ⊗ₘ 𝟙 (𝟙_ C) :=
    (cancel_mono (ρ_ (𝟙_ C)).hom).mp (hb.trans h_nat.symm)


  have h_whisker : (𝟙_ C) ◁ b = 𝟙 (𝟙_ C ⊗ 𝟙_ C) := by
    have h1 : b ⊗ₘ b = b ▷ (𝟙_ C) ≫ (𝟙_ C) ◁ b := MonoidalCategory.tensorHom_def b b
    have h2 : b ⊗ₘ 𝟙 (𝟙_ C) = b ▷ (𝟙_ C) := by
      simp [MonoidalCategory.tensorHom_def]
    rw [h1, h2] at h_eq
    rwa [← cancel_epi (b ▷ (𝟙_ C)), comp_id]

  have h_lnat := leftUnitor_naturality (C := C) b

  rw [h_whisker, id_comp] at h_lnat

  rw [← cancel_epi (λ_ (𝟙_ C)).hom, comp_id]
  exact h_lnat.symm

/-- Uniqueness half of EGNO Proposition 1.2.4: two isomorphisms `𝟙_ C ≅ U` compatible
with the right unitors coincide. -/
theorem unit_iso_compatible_unique (U : C) (hU : IsUnitObject U)
    (f g : 𝟙_ C ≅ U)
    (hf : (f.hom ⊗ₘ f.hom) ≫ hU.rightUnitor'.hom.app U = (ρ_ (𝟙_ C)).hom ≫ f.hom)
    (hg : (g.hom ⊗ₘ g.hom) ≫ hU.rightUnitor'.hom.app U = (ρ_ (𝟙_ C)).hom ≫ g.hom) :
    f = g := by
  let r'_U : U ⊗ U ⟶ U := hU.rightUnitor'.hom.app U
  change (f.hom ⊗ₘ f.hom) ≫ r'_U = (ρ_ (𝟙_ C)).hom ≫ f.hom at hf
  change (g.hom ⊗ₘ g.hom) ≫ r'_U = (ρ_ (𝟙_ C)).hom ≫ g.hom at hg
  ext
  suffices h : f.hom ≫ g.inv = 𝟙 (𝟙_ C) by
    have := congr_arg (· ≫ g.hom) h
    simp at this
    exact this
  apply unit_endo_compat_is_id
  rw [← MonoidalCategory.tensorHom_comp_tensorHom]


  have cancel_g : r'_U ≫ g.inv = (g.inv ⊗ₘ g.inv) ≫ (ρ_ (𝟙_ C)).hom := by
    rw [← cancel_epi (g.hom ⊗ₘ g.hom)]
    rw [← assoc, hg, assoc, Iso.hom_inv_id, comp_id]
    rw [← assoc, MonoidalCategory.tensorHom_comp_tensorHom]
    simp

  have hf_ginv : (f.hom ⊗ₘ f.hom) ≫ r'_U ≫ g.inv = (ρ_ (𝟙_ C)).hom ≫ f.hom ≫ g.inv := by
    rw [← assoc, hf, assoc]
  rw [assoc, ← cancel_g]
  exact hf_ginv

/-- EGNO Proposition 1.2.4: existence and uniqueness of a compatible isomorphism between
the unit object and any `IsUnitObject`. -/
theorem Proposition_1_2_4 (U : C) (hU : IsUnitObject U) :
    (∃ η : 𝟙_ C ≅ U, True) ∧
    (∀ (f g : 𝟙_ C ≅ U),
      (f.hom ⊗ₘ f.hom) ≫ hU.rightUnitor'.hom.app U = (ρ_ (𝟙_ C)).hom ≫ f.hom →
      (g.hom ⊗ₘ g.hom) ≫ hU.rightUnitor'.hom.app U = (ρ_ (𝟙_ C)).hom ≫ g.hom →
      f = g) :=
  ⟨⟨unit_object_iso_of_isUnit U hU, trivial⟩,
   fun f g hf hg => unit_iso_compatible_unique U hU f g hf hg⟩

/-- Composition of two unit endomorphisms recovered from the tensor product via the right
unitor. -/
theorem tensorHom_via_rightUnitor_eq (f g : 𝟙_ C ⟶ 𝟙_ C) :
    (ρ_ (𝟙_ C)).inv ≫ (f ⊗ₘ g) ≫ (ρ_ (𝟙_ C)).hom = f ≫ g := by

  rw [rightUnitor_inv_comp_tensorHom_assoc]


  rw [← leftUnitor_unit_eq_rightUnitor_unit, leftUnitor_naturality,
      leftUnitor_unit_eq_rightUnitor_unit]
  simp

/-- Variant of `tensorHom_via_rightUnitor_eq`: composing in the opposite order also yields
the same conjugated tensor of unit endomorphisms. -/
theorem tensorHom_via_rightUnitor_eq' (f g : 𝟙_ C ⟶ 𝟙_ C) :
    (ρ_ (𝟙_ C)).inv ≫ (f ⊗ₘ g) ≫ (ρ_ (𝟙_ C)).hom = g ≫ f := by
  rw [← leftUnitor_unit_eq_rightUnitor_unit_inv,
      leftUnitor_inv_comp_tensorHom_assoc]

  rw [rightUnitor_naturality]
  simp [leftUnitor_unit_eq_rightUnitor_unit_inv]

/-- Endomorphisms of the unit object commute under composition. -/
theorem endomorphism_unit_comm (f g : 𝟙_ C ⟶ 𝟙_ C) :
    f ≫ g = g ≫ f := by
  rw [← tensorHom_via_rightUnitor_eq, tensorHom_via_rightUnitor_eq']

/-- The monoid `End (𝟙_ C)` is commutative. -/
theorem endomorphism_unit_mul_comm (f g : End (𝟙_ C)) :
    f * g = g * f := by
  show g ≫ f = f ≫ g
  exact (endomorphism_unit_comm f g).symm

/-- EGNO Proposition 1.2.7: endomorphisms of the unit object commute. -/
theorem Proposition_1_2_7 (f g : 𝟙_ C ⟶ 𝟙_ C) :
    f ≫ g = g ≫ f :=
  endomorphism_unit_comm f g

end TensorCategories
