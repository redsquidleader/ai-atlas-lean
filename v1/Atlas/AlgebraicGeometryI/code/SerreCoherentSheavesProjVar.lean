/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.PicardGroup

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

noncomputable section

namespace Corollary19

/-- An invertible sheaf (line bundle) on a scheme `X`: a sheaf of modules
that is locally free of rank 1. -/
noncomputable def IsInvertibleSheaf {X : Scheme.{u}} (ℒ : X.Modules) : Prop := by sorry

/-- The structure sheaf `𝒪_X` is invertible (trivially of rank 1). -/
theorem isInvertibleSheaf_unit (X : Scheme.{u}) :
    IsInvertibleSheaf (SheafOfModules.unit X.ringCatSheaf) := by sorry

/-- The type of invertible sheaves on `X`. -/
def InvertibleSheaf (X : Scheme.{u}) : Type (u + 1) :=
  { ℒ : X.Modules // IsInvertibleSheaf ℒ }

/-- Setoid identifying two invertible sheaves when they are isomorphic. -/
instance invertibleSheafSetoid (X : Scheme.{u}) : Setoid (InvertibleSheaf X) where
  r ℒ₁ ℒ₂ := Nonempty (ℒ₁.val ≅ ℒ₂.val)
  iseqv := {
    refl := fun _ => ⟨Iso.refl _⟩
    symm := fun ⟨i⟩ => ⟨i.symm⟩
    trans := fun ⟨i⟩ ⟨j⟩ => ⟨i.trans j⟩
  }

/-- The Picard group of a scheme `X`: isomorphism classes of invertible
sheaves on `X`. -/
def PicardGroupScheme (X : Scheme.{u}) : Type (u + 1) :=
  Quotient (invertibleSheafSetoid X)

/-- Commutative group structure on `PicardGroupScheme X` via tensor
product of line bundles, with identity given by `𝒪_X` and inverses by
duals. -/
instance instCommGroupPicardGroupScheme (X : Scheme.{u}) :
    CommGroup (PicardGroupScheme X) where
  mul := sorry
  mul_assoc := sorry
  one := Quotient.mk'' ⟨SheafOfModules.unit X.ringCatSheaf, isInvertibleSheaf_unit X⟩
  one_mul := sorry
  mul_one := sorry
  inv := sorry
  inv_mul_cancel := sorry
  mul_comm := sorry

/-- Class of an invertible sheaf in the Picard group. -/
def PicardGroupScheme.mk {X : Scheme.{u}} (ℒ : X.Modules)
    (h : IsInvertibleSheaf ℒ) : PicardGroupScheme X :=
  Quotient.mk'' ⟨ℒ, h⟩

/-- Two invertible sheaves represent the same Picard class iff they are
isomorphic. -/
theorem PicardGroupScheme.mk_eq_iff {X : Scheme.{u}}
    (ℒ₁ ℒ₂ : X.Modules) (h₁ : IsInvertibleSheaf ℒ₁) (h₂ : IsInvertibleSheaf ℒ₂) :
    PicardGroupScheme.mk ℒ₁ h₁ = PicardGroupScheme.mk ℒ₂ h₂ ↔ Nonempty (ℒ₁ ≅ ℒ₂) :=
  Quotient.eq''

/-- The class of the structure sheaf is the identity of the Picard group. -/
theorem PicardGroupScheme.mk_unit (X : Scheme.{u}) :
    PicardGroupScheme.mk (SheafOfModules.unit X.ringCatSheaf)
      (isInvertibleSheaf_unit X) = 1 :=
  rfl

section AffineCase

variable (R : Type u) [CommRing R]

/-- The Picard group of a commutative ring is naturally a commutative
group. -/
instance picardGroup_affine_commGroup : CommGroup (CommRing.Pic R) := inferInstance

/-- Affine case of the Picard group: for `X = Spec R`, the scheme Picard
group is naturally isomorphic to the ring Picard group `Pic R`. -/
noncomputable def picardGroupScheme_spec_equiv :
    PicardGroupScheme (Spec (.of R)) ≃* CommRing.Pic R := by sorry

end AffineCase

/-- Multiplication in `Pic R` corresponds to tensor product of invertible
modules. -/
theorem pic_mul_eq_tensor {R : Type u} [CommSemiring R]
    {M N : Type*} [AddCommMonoid M] [Module R M] [Module.Invertible R M]
    [AddCommMonoid N] [Module R N] [Module.Invertible R N] :
    CommRing.Pic.mk R (M ⊗[R] N) = CommRing.Pic.mk R M * CommRing.Pic.mk R N :=
  CommRing.Pic.mk_tensor

/-- The trivial line bundle `R` represents the identity in `Pic R`. -/
theorem pic_identity {R : Type u} [CommSemiring R] :
    CommRing.Pic.mk R R = 1 :=
  CommRing.Pic.mk_self

/-- The inverse of a Picard class is represented by the dual module. -/
theorem pic_inv_eq_dual {R : Type u} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] [Module.Invertible R M] :
    CommRing.Pic.mk R (Module.Dual R M) = (CommRing.Pic.mk R M)⁻¹ :=
  CommRing.Pic.mk_dual

/-- Commutativity of multiplication in `Pic R`. -/
theorem pic_comm {R : Type u} [CommSemiring R]
    (a b : CommRing.Pic R) : a * b = b * a :=
  mul_comm a b

/-- Two invertible modules represent the same Picard class iff they are
isomorphic as `R`-modules. -/
theorem pic_eq_iff_iso {R : Type u} [CommSemiring R]
    {M N : Type*} [AddCommMonoid M] [Module R M] [Module.Invertible R M]
    [AddCommMonoid N] [Module R N] [Module.Invertible R N] :
    CommRing.Pic.mk R M = CommRing.Pic.mk R N ↔ Nonempty (M ≃ₗ[R] N) :=
  CommRing.Pic.mk_eq_mk_iff

/-- A Picard class is trivial iff the underlying invertible module is free. -/
theorem pic_trivial_iff_free {R : Type u} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M] [Module.Invertible R M] :
    CommRing.Pic.mk R M = 1 ↔ Module.Free R M :=
  CommRing.Pic.mk_eq_one_iff_free

end Corollary19

end
