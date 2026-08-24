/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ModuleCategory
import Atlas.TensorCategories.code.ExactModuleCategory
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

set_option maxHeartbeats 800000

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Category MonoidalCategory LeftModCat

/-- A left module category `M` over `C` has internal Hom if for every pair `m, n ∈ M`
there is an object `moduleIHom m n ∈ C` and a natural equivalence
`(X ⊗ᵐ m ⟶ n) ≃ (X ⟶ moduleIHom m n)` (Definition 2.10.2). -/
class HasModuleInternalHom (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    (M : Type u₂) [Category.{v₂} M] [LeftModuleCategory C M] where
  moduleIHom : M → M → C
  moduleIHomEquiv : ∀ (X : C) (m n : M),
    (X ⊗ᵐ m ⟶ n) ≃ (X ⟶ moduleIHom m n)
  moduleIHomEquiv_natural : ∀ {X Y : C} (f : X ⟶ Y) (m n : M) (g : Y ⊗ᵐ m ⟶ n),
    moduleIHomEquiv X m n (f ▷ᵐ m ≫ g) = f ≫ moduleIHomEquiv Y m n g

export HasModuleInternalHom (moduleIHom moduleIHomEquiv moduleIHomEquiv_natural)

namespace ModuleInternalHom

scoped notation "ihom" => HasModuleInternalHom.moduleIHom

end ModuleInternalHom

/-- Convenience abbreviation for `moduleIHom m₁ m₂`, the internal Hom in `C` of the
module objects `m₁, m₂ : M`. -/
abbrev internalModuleHom {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
    [HasModuleInternalHom C M] (m₁ m₂ : M) : C :=
  moduleIHom (C := C) m₁ m₂

/-- Definition 2.10.2: the internal Hom `Hom(m₁, m₂)` in `C` of two module objects of
the module category `M`. -/
def definition_2_10_2 {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
    [HasModuleInternalHom C M] (m₁ m₂ : M) : C :=
  moduleIHom (C := C) m₁ m₂

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
    [HasModuleInternalHom C M]

/-- The evaluation morphism `moduleIHom m n ⊗ᵐ m ⟶ n`, obtained as the counit of the
internal Hom adjunction by transporting the identity of `moduleIHom m n`. -/
def moduleIHomEv (m n : M) : (moduleIHom (C := C) m n) ⊗ᵐ m ⟶ n :=
  (moduleIHomEquiv (moduleIHom m n) m n).symm (𝟙 _)

/-- The inverse of `moduleIHomEquiv` is given by whiskering by `m` and post-composing
with the evaluation morphism. -/
theorem moduleIHomEquiv_symm_eq (X : C) (m n : M) (h : X ⟶ moduleIHom (C := C) m n) :
    (moduleIHomEquiv X m n).symm h = h ▷ᵐ m ≫ moduleIHomEv m n := by
  apply (moduleIHomEquiv X m n).injective
  rw [Equiv.apply_symm_apply]
  have key := moduleIHomEquiv_natural h m n (moduleIHomEv m n)
  rw [key]
  simp [moduleIHomEv, Equiv.apply_symm_apply]

/-- The composition morphism `Hom(n, p) ⊗ Hom(m, n) ⟶ Hom(m, p)` of internal Homs,
defined via the action associator and the evaluation morphisms. -/
def moduleIHomComp (m n p : M) :
    moduleIHom (C := C) n p ⊗ moduleIHom m n ⟶ moduleIHom m p :=
  moduleIHomEquiv _ m p
    ((actμ_ (moduleIHom n p) (moduleIHom m n) m).hom ≫
      (moduleIHom n p) ◁ᵐ moduleIHomEv m n ≫
      moduleIHomEv n p)

omit [HasModuleInternalHom C M] in
/-- Right whiskering of a composition of morphisms in `C` by a module object equals the
composition of right whiskerings. -/
@[reassoc]
lemma actWhiskerRight_comp {X₁ X₂ X₃ : C} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) (N : M) :
    (f ≫ g) ▷ᵐ N = f ▷ᵐ N ≫ g ▷ᵐ N := by
  have h := LeftModuleCategory.actTensorHom_comp (M := M) f (𝟙 N) g (𝟙 N)
  simp [LeftModuleCategory.actTensorHom_def] at h; exact h.symm

omit [HasModuleInternalHom C M] in
/-- Left whiskering of a composition of module morphisms by an object of `C` equals the
composition of left whiskerings. -/
@[reassoc]
lemma actWhiskerLeft_comp (X : C) {M₁ M₂ M₃ : M} (f : M₁ ⟶ M₂) (g : M₂ ⟶ M₃) :
    X ◁ᵐ (f ≫ g) = X ◁ᵐ f ≫ X ◁ᵐ g := by
  have h := LeftModuleCategory.actTensorHom_comp (M := M) (𝟙 X) f (𝟙 X) g
  simp [LeftModuleCategory.actTensorHom_def] at h; exact h.symm

omit [HasModuleInternalHom C M] in
/-- Interchange law for the module action: right whiskering by `M₁` followed by left
whiskering by `X₂` equals left whiskering by `X₁` followed by right whiskering by `M₂`. -/
@[reassoc]
lemma actWhisker_interchange {X₁ X₂ : C} {M₁ M₂ : M} (f : X₁ ⟶ X₂) (g : M₁ ⟶ M₂) :
    f ▷ᵐ M₁ ≫ X₂ ◁ᵐ g = X₁ ◁ᵐ g ≫ f ▷ᵐ M₂ := by
  have h1 := LeftModuleCategory.actTensorHom_def (M := M) f g
  have h2 := LeftModuleCategory.actTensorHom_comp (M := M) (𝟙 X₁) g f (𝟙 M₂)
  rw [id_comp, comp_id] at h2
  rw [LeftModuleCategory.actTensorHom_def, LeftModuleCategory.actTensorHom_def] at h2
  simp at h2; rw [← h1, ← h2]

/-- The internal Hom adjunction equivalence
`(X ⊗ᵐ m ⟶ n) ≃ (X ⟶ moduleIHom m n)`, packaged as a standalone definition. -/
def moduleIHom_adjunction (X : C) (m n : M) :
    (X ⊗ᵐ m ⟶ n) ≃ (X ⟶ moduleIHom (C := C) m n) :=
  moduleIHomEquiv X m n

/-- The natural isomorphism `Hom(𝟙_ C ⊗ᵐ m, n) ≅ Hom(m, n)` coming from the unit
isomorphism `actℓ_ m : 𝟙_ C ⊗ᵐ m ≅ m`. -/
def moduleIHom_unit_iso (m n : M) :
    moduleIHom (C := C) (𝟙_ C ⊗ᵐ m) n ≅ moduleIHom m n where
  hom := moduleIHomEquiv _ m n
    ((moduleIHom (C := C) (𝟙_ C ⊗ᵐ m) n) ◁ᵐ (actℓ_ m).inv ≫ moduleIHomEv (𝟙_ C ⊗ᵐ m) n)
  inv := moduleIHomEquiv _ (𝟙_ C ⊗ᵐ m) n
    ((moduleIHom (C := C) m n) ◁ᵐ (actℓ_ m).hom ≫ moduleIHomEv m n)
  hom_inv_id := by
    apply (moduleIHomEquiv _ (𝟙_ C ⊗ᵐ m) n).symm.injective
    rw [moduleIHomEquiv_symm_eq, actWhiskerRight_comp, assoc]
    have h1 : (moduleIHomEquiv _ (𝟙_ C ⊗ᵐ m) n
          (moduleIHom (C := C) m n ◁ᵐ (actℓ_ m).hom ≫ moduleIHomEv m n)) ▷ᵐ (𝟙_ C ⊗ᵐ m) ≫
        moduleIHomEv (𝟙_ C ⊗ᵐ m) n =
        moduleIHom (C := C) m n ◁ᵐ (actℓ_ m).hom ≫ moduleIHomEv m n := by
      rw [← moduleIHomEquiv_symm_eq, Equiv.symm_apply_apply]
    rw [h1, actWhisker_interchange_assoc]
    have h2 : (moduleIHomEquiv _ m n
          (moduleIHom (C := C) (𝟙_ C ⊗ᵐ m) n ◁ᵐ (actℓ_ m).inv ≫ moduleIHomEv (𝟙_ C ⊗ᵐ m) n)) ▷ᵐ m ≫
        moduleIHomEv m n =
        moduleIHom (C := C) (𝟙_ C ⊗ᵐ m) n ◁ᵐ (actℓ_ m).inv ≫ moduleIHomEv (𝟙_ C ⊗ᵐ m) n := by
      rw [← moduleIHomEquiv_symm_eq, Equiv.symm_apply_apply]
    rw [h2, ← actWhiskerLeft_comp_assoc, Iso.hom_inv_id,
      LeftModuleCategory.actWhiskerLeft_id, id_comp]
    rfl
  inv_hom_id := by
    apply (moduleIHomEquiv _ m n).symm.injective
    rw [moduleIHomEquiv_symm_eq, actWhiskerRight_comp, assoc]
    have h1 : (moduleIHomEquiv _ m n
          (moduleIHom (C := C) (𝟙_ C ⊗ᵐ m) n ◁ᵐ (actℓ_ m).inv ≫ moduleIHomEv (𝟙_ C ⊗ᵐ m) n)) ▷ᵐ m ≫
        moduleIHomEv m n =
        moduleIHom (C := C) (𝟙_ C ⊗ᵐ m) n ◁ᵐ (actℓ_ m).inv ≫ moduleIHomEv (𝟙_ C ⊗ᵐ m) n := by
      rw [← moduleIHomEquiv_symm_eq, Equiv.symm_apply_apply]
    rw [h1, actWhisker_interchange_assoc]
    have h2 : (moduleIHomEquiv _ (𝟙_ C ⊗ᵐ m) n
          (moduleIHom (C := C) m n ◁ᵐ (actℓ_ m).hom ≫ moduleIHomEv m n)) ▷ᵐ (𝟙_ C ⊗ᵐ m) ≫
        moduleIHomEv (𝟙_ C ⊗ᵐ m) n =
        moduleIHom (C := C) m n ◁ᵐ (actℓ_ m).hom ≫ moduleIHomEv m n := by
      rw [← moduleIHomEquiv_symm_eq, Equiv.symm_apply_apply]
    rw [h2, ← actWhiskerLeft_comp_assoc, Iso.inv_hom_id,
      LeftModuleCategory.actWhiskerLeft_id, id_comp]
    rfl

/-- Curry equivalence: `(T ⊗ X ⟶ Hom(m, n)) ≃ (T ⟶ Hom(X ⊗ᵐ m, n))`, obtained by
combining the internal Hom adjunction with the action associator. -/
def moduleIHom_curry_equiv (T X : C) (m n : M) :
    (T ⊗ X ⟶ moduleIHom (C := C) m n) ≃ (T ⟶ moduleIHom (C := C) (X ⊗ᵐ m) n) :=
  ((moduleIHomEquiv (T ⊗ X) m n).symm.trans
    (Equiv.mk
      (fun (f : (T ⊗ X) ⊗ᵐ m ⟶ n) => (actμ_ T X m).inv ≫ f)
      (fun (g : T ⊗ᵐ (X ⊗ᵐ m) ⟶ n) => (actμ_ T X m).hom ≫ g)
      (fun f => by simp)
      (fun g => by simp))).trans
    (moduleIHomEquiv T (X ⊗ᵐ m) n)

/-- Tensor equivalence: `(Y ⟶ Hom(X ⊗ᵐ m, n)) ≃ (Y ⟶ Hom(m, n) ⊗ Xᘁ)` when `X` has a
right dual, obtained from `moduleIHom_curry_equiv` and `tensorRightHomEquiv`. -/
def moduleIHom_tensor_equiv (Y X : C) [HasRightDual X] (m n : M) :
    (Y ⟶ moduleIHom (C := C) (X ⊗ᵐ m) n) ≃ (Y ⟶ moduleIHom (C := C) m n ⊗ Xᘁ) :=
  (moduleIHom_curry_equiv Y X m n).symm.trans (tensorRightHomEquiv Y X Xᘁ (moduleIHom m n))

/-- Naturality in `T` of the inverse curry equivalence:
`(curry^{-1} _ _ m n) (f ≫ g) = f ▷ X ≫ (curry^{-1} _ _ m n) g`. -/
theorem moduleIHom_curry_equiv_symm_natural {T₁ T₂ X : C} {m n : M}
    (f : T₁ ⟶ T₂) (g : T₂ ⟶ moduleIHom (C := C) (X ⊗ᵐ m) n) :
    (moduleIHom_curry_equiv T₁ X m n).symm (f ≫ g) =
      f ▷ X ≫ (moduleIHom_curry_equiv T₂ X m n).symm g := by


  show moduleIHomEquiv (T₁ ⊗ X) m n
    ((actμ_ T₁ X m).hom ≫ (moduleIHomEquiv T₁ (X ⊗ᵐ m) n).symm (f ≫ g)) =
    f ▷ X ≫ moduleIHomEquiv (T₂ ⊗ X) m n
      ((actμ_ T₂ X m).hom ≫ (moduleIHomEquiv T₂ (X ⊗ᵐ m) n).symm g)

  rw [show (moduleIHomEquiv T₁ (X ⊗ᵐ m) n).symm (f ≫ g) =
    f ▷ᵐ (X ⊗ᵐ m) ≫ (moduleIHomEquiv T₂ (X ⊗ᵐ m) n).symm g from by
      rw [moduleIHomEquiv_symm_eq, actWhiskerRight_comp, assoc,
          ← moduleIHomEquiv_symm_eq]]

  have h_mu_nat : (actμ_ T₁ X m).hom ≫ f ▷ᵐ (X ⊗ᵐ m) =
    (f ▷ X) ▷ᵐ m ≫ (actμ_ T₂ X m).hom := by
    have := LeftModuleCategory.actAssociator_naturality (M := M) f (𝟙 X) (𝟙 m)
    simp [LeftModuleCategory.actTensorHom_def] at this
    exact this.symm

  conv_lhs => rw [show (actμ_ T₁ X m).hom ≫ f ▷ᵐ (X ⊗ᵐ m) ≫ (moduleIHomEquiv T₂ (X ⊗ᵐ m) n).symm g =
    (f ▷ X) ▷ᵐ m ≫ (actμ_ T₂ X m).hom ≫ (moduleIHomEquiv T₂ (X ⊗ᵐ m) n).symm g from by
      rw [← assoc, h_mu_nat, assoc]]

  rw [moduleIHomEquiv_natural]

/-- Naturality in `Y` of `moduleIHom_tensor_equiv`:
`tensor_equiv (f ≫ g) = f ≫ tensor_equiv g`. -/
theorem moduleIHom_tensor_equiv_natural {Y₁ Y₂ X : C} [HasRightDual X] {m n : M}
    (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ moduleIHom (C := C) (X ⊗ᵐ m) n) :
    moduleIHom_tensor_equiv Y₁ X m n (f ≫ g) =
      f ≫ moduleIHom_tensor_equiv Y₂ X m n g := by
  simp only [moduleIHom_tensor_equiv, Equiv.trans_apply]
  rw [moduleIHom_curry_equiv_symm_natural]


  apply (tensorRightHomEquiv Y₁ X Xᘁ (moduleIHom m n)).symm.injective
  rw [Equiv.symm_apply_apply, tensorRightHomEquiv_symm_naturality]
  congr 1
  exact ((tensorRightHomEquiv Y₂ X Xᘁ (moduleIHom m n)).symm_apply_apply _).symm

/-- The natural isomorphism `Hom(X ⊗ᵐ m, n) ≅ Hom(m, n) ⊗ Xᘁ` produced from
`moduleIHom_tensor_equiv` (Lemma 2.10.4 part 3). -/
def moduleIHom_curry_iso (X : C) [HasRightDual X] (m n : M) :
    moduleIHom (C := C) (X ⊗ᵐ m) n ≅ moduleIHom (C := C) m n ⊗ Xᘁ where
  hom := moduleIHom_tensor_equiv _ X m n (𝟙 _)
  inv := (moduleIHom_tensor_equiv _ X m n).symm (𝟙 _)
  hom_inv_id := by


    apply (moduleIHom_tensor_equiv _ X m n).injective
    rw [moduleIHom_tensor_equiv_natural]
    simp [Equiv.apply_symm_apply]
  inv_hom_id := by


    apply (moduleIHom_tensor_equiv _ X m n).symm.injective
    have h_nat_symm : ∀ {A B : C} (f : A ⟶ B) (g : B ⟶ moduleIHom (C := C) (X ⊗ᵐ m) n),
        (moduleIHom_tensor_equiv _ X m n).symm
          (f ≫ moduleIHom_tensor_equiv B X m n g) = f ≫ g := by
      intro A B f g
      conv_rhs => rw [← Equiv.symm_apply_apply (moduleIHom_tensor_equiv A X m n) (f ≫ g)]
      congr 1
      exact (moduleIHom_tensor_equiv_natural f g).symm
    simp only [h_nat_symm, comp_id]

/-- Left inverse condition for `modTensorHomEquiv`: applying the unit-evaluation pair
recovers the original morphism `f : N ⟶ X ⊗ᵐ P`. -/
theorem modTensorHomEquiv_left_inv
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
    (X : C) [HasRightDual X] (N P : M) (f : N ⟶ X ⊗ᵐ P) :
    (actℓ_ N).inv ≫ (η_ X Xᘁ) ▷ᵐ N ≫ (actμ_ X Xᘁ N).hom ≫
      X ◁ᵐ (Xᘁ ◁ᵐ f ≫ (actμ_ Xᘁ X P).inv ≫ (ε_ X Xᘁ) ▷ᵐ P ≫ (actℓ_ P).hom) = f := by sorry

/-- Right inverse condition for `modTensorHomEquiv`: applying the inverse direction
recovers the original morphism `g : Xᘁ ⊗ᵐ N ⟶ P`. -/
theorem modTensorHomEquiv_right_inv
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
    (X : C) [HasRightDual X] (N P : M) (g : Xᘁ ⊗ᵐ N ⟶ P) :
    Xᘁ ◁ᵐ ((actℓ_ N).inv ≫ (η_ X Xᘁ) ▷ᵐ N ≫ (actμ_ X Xᘁ N).hom ≫ X ◁ᵐ g) ≫
      (actμ_ Xᘁ X P).inv ≫ (ε_ X Xᘁ) ▷ᵐ P ≫ (actℓ_ P).hom = g := by sorry

/-- The module-level duality equivalence `(N ⟶ X ⊗ᵐ P) ≃ (Xᘁ ⊗ᵐ N ⟶ P)` arising from
the rigidity of `C` together with the left module structure on `M`. -/
def modTensorHomEquiv (X : C) [HasRightDual X] (N P : M) :
    (N ⟶ X ⊗ᵐ P) ≃ (Xᘁ ⊗ᵐ N ⟶ P) where
  toFun f := Xᘁ ◁ᵐ f ≫ (actμ_ Xᘁ X P).inv ≫ (ε_ X Xᘁ) ▷ᵐ P ≫ (actℓ_ P).hom
  invFun g := (actℓ_ N).inv ≫ (η_ X Xᘁ) ▷ᵐ N ≫ (actμ_ X Xᘁ N).hom ≫ X ◁ᵐ g
  left_inv f := modTensorHomEquiv_left_inv X N P f
  right_inv g := modTensorHomEquiv_right_inv X N P g

/-- Naturality of `modTensorHomEquiv` in the source module object:
`(f ≫ g)^∨ = Xᘁ ◁ᵐ f ≫ g^∨`. -/
theorem modTensorHomEquiv_natural {X : C} [HasRightDual X] {N₁ N₂ : M} (f : N₁ ⟶ N₂)
    {P : M} (g : N₂ ⟶ X ⊗ᵐ P) :
    modTensorHomEquiv X N₁ P (f ≫ g) =
      Xᘁ ◁ᵐ f ≫ modTensorHomEquiv X N₂ P g := by
  simp only [modTensorHomEquiv, Equiv.coe_fn_mk]
  rw [actWhiskerLeft_comp, assoc]

/-- Equivalence `(Y ⟶ Hom(m₁, X ⊗ᵐ m₂)) ≃ (Y ⟶ X ⊗ Hom(m₁, m₂))`, built from the
internal Hom adjunction, the module duality equivalence, and the action associator. -/
def moduleIHom_tensor_left_equiv (Y X : C) [HasRightDual X] (m₁ m₂ : M) :
    (Y ⟶ moduleIHom (C := C) m₁ (X ⊗ᵐ m₂)) ≃ (Y ⟶ X ⊗ moduleIHom (C := C) m₁ m₂) :=

  (moduleIHomEquiv Y m₁ (X ⊗ᵐ m₂)).symm

  |>.trans (modTensorHomEquiv X (Y ⊗ᵐ m₁) m₂)

  |>.trans (Equiv.mk
    (fun (f : Xᘁ ⊗ᵐ (Y ⊗ᵐ m₁) ⟶ m₂) => (actμ_ Xᘁ Y m₁).hom ≫ f)
    (fun (g : (Xᘁ ⊗ Y) ⊗ᵐ m₁ ⟶ m₂) => (actμ_ Xᘁ Y m₁).inv ≫ g)
    (fun f => by simp)
    (fun g => by simp))

  |>.trans (moduleIHomEquiv (Xᘁ ⊗ Y) m₁ m₂)

  |>.trans (tensorLeftHomEquiv Y X Xᘁ (moduleIHom m₁ m₂))

/-- Naturality in `Y` of `moduleIHom_tensor_left_equiv`:
`tensor_left_equiv (f ≫ g) = f ≫ tensor_left_equiv g`. -/
theorem moduleIHom_tensor_left_equiv_natural {Y₁ Y₂ X : C} [HasRightDual X] {m₁ m₂ : M}
    (f : Y₁ ⟶ Y₂) (g : Y₂ ⟶ moduleIHom (C := C) m₁ (X ⊗ᵐ m₂)) :
    moduleIHom_tensor_left_equiv Y₁ X m₁ m₂ (f ≫ g) =
      f ≫ moduleIHom_tensor_left_equiv Y₂ X m₁ m₂ g := by
  simp only [moduleIHom_tensor_left_equiv, Equiv.trans_apply, Equiv.coe_fn_mk]

  rw [show (moduleIHomEquiv Y₁ m₁ (X ⊗ᵐ m₂)).symm (f ≫ g) =
    f ▷ᵐ m₁ ≫ (moduleIHomEquiv Y₂ m₁ (X ⊗ᵐ m₂)).symm g from by
      rw [moduleIHomEquiv_symm_eq, actWhiskerRight_comp, assoc,
          ← moduleIHomEquiv_symm_eq]]

  rw [modTensorHomEquiv_natural]


  have h_mu_nat : (actμ_ Xᘁ Y₁ m₁).hom ≫ Xᘁ ◁ᵐ (f ▷ᵐ m₁) =
    (Xᘁ ◁ f) ▷ᵐ m₁ ≫ (actμ_ Xᘁ Y₂ m₁).hom := by
    have := LeftModuleCategory.actAssociator_naturality (M := M) (𝟙 Xᘁ) f (𝟙 m₁)
    simp [LeftModuleCategory.actTensorHom_def] at this
    exact this.symm
  conv_lhs =>
    rw [show (actμ_ Xᘁ Y₁ m₁).hom ≫ Xᘁ ◁ᵐ (f ▷ᵐ m₁) ≫
      modTensorHomEquiv X (Y₂ ⊗ᵐ m₁) m₂ ((moduleIHomEquiv Y₂ m₁ (X ⊗ᵐ m₂)).symm g) =
      (Xᘁ ◁ f) ▷ᵐ m₁ ≫ (actμ_ Xᘁ Y₂ m₁).hom ≫
      modTensorHomEquiv X (Y₂ ⊗ᵐ m₁) m₂ ((moduleIHomEquiv Y₂ m₁ (X ⊗ᵐ m₂)).symm g) from by
        rw [← assoc, h_mu_nat, assoc]]

  rw [moduleIHomEquiv_natural]

  apply (tensorLeftHomEquiv Y₁ X Xᘁ (moduleIHom m₁ m₂)).symm.injective
  rw [Equiv.symm_apply_apply, tensorLeftHomEquiv_symm_naturality]
  congr 1
  exact ((tensorLeftHomEquiv Y₂ X Xᘁ (moduleIHom m₁ m₂)).symm_apply_apply _).symm

/-- The natural isomorphism `Hom(m₁, X ⊗ᵐ m₂) ≅ X ⊗ Hom(m₁, m₂)` (Lemma 2.10.4 part 4). -/
def moduleIHom_tensor_left_iso (X : C) [HasRightDual X] (m₁ m₂ : M) :
    moduleIHom (C := C) m₁ (X ⊗ᵐ m₂) ≅ X ⊗ moduleIHom (C := C) m₁ m₂ where
  hom := moduleIHom_tensor_left_equiv _ X m₁ m₂ (𝟙 _)
  inv := (moduleIHom_tensor_left_equiv _ X m₁ m₂).symm (𝟙 _)
  hom_inv_id := by
    apply (moduleIHom_tensor_left_equiv _ X m₁ m₂).injective
    rw [moduleIHom_tensor_left_equiv_natural]
    simp [Equiv.apply_symm_apply]
  inv_hom_id := by
    apply (moduleIHom_tensor_left_equiv _ X m₁ m₂).symm.injective
    have h_nat_symm : ∀ {A B : C} (f : A ⟶ B) (g : B ⟶ moduleIHom (C := C) m₁ (X ⊗ᵐ m₂)),
        (moduleIHom_tensor_left_equiv _ X m₁ m₂).symm
          (f ≫ moduleIHom_tensor_left_equiv B X m₁ m₂ g) = f ≫ g := by
      intro A B f g
      conv_rhs => rw [← Equiv.symm_apply_apply (moduleIHom_tensor_left_equiv A X m₁ m₂) (f ≫ g)]
      congr 1
      exact (moduleIHom_tensor_left_equiv_natural f g).symm
    simp only [h_nat_symm, comp_id]

/-- Global sections equivalence `(m₁ ⟶ X ⊗ᵐ m₂) ≃ (𝟙_ C ⟶ X ⊗ Hom(m₁, m₂))`,
underlying Lemma 2.10.4 part 2. -/
def moduleIHom_global_sections_equiv (X : C) [HasRightDual X] (m₁ m₂ : M) :
    (m₁ ⟶ X ⊗ᵐ m₂) ≃ (𝟙_ C ⟶ X ⊗ moduleIHom (C := C) m₁ m₂) :=

  (modTensorHomEquiv X m₁ m₂)

  |>.trans (moduleIHomEquiv Xᘁ m₁ m₂)

  |>.trans (Equiv.mk
    (fun (f : Xᘁ ⟶ moduleIHom (C := C) m₁ m₂) => (ρ_ Xᘁ).hom ≫ f)
    (fun (g : Xᘁ ⊗ 𝟙_ C ⟶ moduleIHom (C := C) m₁ m₂) => (ρ_ Xᘁ).inv ≫ g)
    (fun f => by simp)
    (fun g => by simp))

  |>.trans (tensorLeftHomEquiv (𝟙_ C) X Xᘁ (moduleIHom m₁ m₂))

/-- Lemma 2.10.4 part 1: the internal Hom adjunction
`(X ⊗ᵐ m ⟶ n) ≃ (X ⟶ Hom(m, n))`. -/
def lemma_2_10_4_part1 (X : C) (m n : M) :
    (X ⊗ᵐ m ⟶ n) ≃ (X ⟶ moduleIHom (C := C) m n) :=
  moduleIHom_adjunction X m n

/-- Lemma 2.10.4 part 2: when `X` is rigid, morphisms `m₁ ⟶ X ⊗ᵐ m₂` correspond to
global sections of `X ⊗ Hom(m₁, m₂)`. -/
def lemma_2_10_4_part2 (X : C) [HasRightDual X] (m₁ m₂ : M) :
    (m₁ ⟶ X ⊗ᵐ m₂) ≃ (𝟙_ C ⟶ X ⊗ moduleIHom (C := C) m₁ m₂) :=
  moduleIHom_global_sections_equiv X m₁ m₂

/-- Lemma 2.10.4 part 3: when `X` is rigid, `Hom(X ⊗ᵐ m, n) ≅ Hom(m, n) ⊗ Xᘁ`. -/
def lemma_2_10_4_part3 (X : C) [HasRightDual X] (m n : M) :
    moduleIHom (C := C) (X ⊗ᵐ m) n ≅ moduleIHom m n ⊗ Xᘁ :=
  moduleIHom_curry_iso X m n

/-- Lemma 2.10.4 part 4: when `X` is rigid, `Hom(m₁, X ⊗ᵐ m₂) ≅ X ⊗ Hom(m₁, m₂)`. -/
def lemma_2_10_4_part4 (X : C) [HasRightDual X] (m₁ m₂ : M) :
    moduleIHom (C := C) m₁ (X ⊗ᵐ m₂) ≅ X ⊗ moduleIHom (C := C) m₁ m₂ :=
  moduleIHom_tensor_left_iso X m₁ m₂

/-- Lemma 2.10.4 (combined): the four natural equivalences/isomorphisms for the internal
Hom with a rigid object `X`, packaged as a single product. -/
def lemma_2_10_4 (X : C) [HasRightDual X] (m₁ m₂ : M) :
    ((X ⊗ᵐ m₁ ⟶ m₂) ≃ (X ⟶ moduleIHom (C := C) m₁ m₂)) ×
    ((m₁ ⟶ X ⊗ᵐ m₂) ≃ (𝟙_ C ⟶ X ⊗ moduleIHom (C := C) m₁ m₂)) ×
    (moduleIHom (C := C) (X ⊗ᵐ m₁) m₂ ≅ moduleIHom m₁ m₂ ⊗ Xᘁ) ×
    (moduleIHom (C := C) m₁ (X ⊗ᵐ m₂) ≅ X ⊗ moduleIHom (C := C) m₁ m₂) :=
  ⟨lemma_2_10_4_part1 X m₁ m₂,
   lemma_2_10_4_part2 X m₁ m₂,
   lemma_2_10_4_part3 X m₁ m₂,
   lemma_2_10_4_part4 X m₁ m₂⟩

/-- Functorial action of `moduleIHom` on a morphism in the right argument:
`Hom(m₁, m₂) ⟶ Hom(m₁, m₂')` induced by `f : m₂ ⟶ m₂'`. -/
def moduleIHomMapRight (m₁ : M) {m₂ m₂' : M} (f : m₂ ⟶ m₂') :
    moduleIHom (C := C) m₁ m₂ ⟶ moduleIHom m₁ m₂' :=
  moduleIHomEquiv (moduleIHom m₁ m₂) m₁ m₂' (moduleIHomEv m₁ m₂ ≫ f)

/-- Contravariant functorial action of `moduleIHom` in the left argument:
`Hom(m₁', m₂) ⟶ Hom(m₁, m₂)` induced by `f : m₁ ⟶ m₁'`. -/
def moduleIHomMapLeft {m₁ m₁' : M} (f : m₁ ⟶ m₁') (m₂ : M) :
    moduleIHom (C := C) m₁' m₂ ⟶ moduleIHom m₁ m₂ :=
  moduleIHomEquiv (moduleIHom m₁' m₂) m₁ m₂
    ((moduleIHom (C := C) m₁' m₂) ◁ᵐ f ≫ moduleIHomEv m₁' m₂)

/-- Naturality of `moduleIHomEquiv` in the right (target) module argument:
`moduleIHomEquiv X m₁ m₂' (h ≫ g) = moduleIHomEquiv X m₁ m₂ h ≫ moduleIHomMapRight m₁ g`. -/
theorem moduleIHomEquiv_natural_right (X : C) (m₁ : M) {m₂ m₂' : M}
    (g : m₂ ⟶ m₂') (h : X ⊗ᵐ m₁ ⟶ m₂) :
    moduleIHomEquiv X m₁ m₂' (h ≫ g) =
      moduleIHomEquiv X m₁ m₂ h ≫ moduleIHomMapRight m₁ g := by

  rw [moduleIHomMapRight]
  rw [← moduleIHomEquiv_natural]


  have key := moduleIHomEquiv_symm_eq X m₁ m₂ (moduleIHomEquiv X m₁ m₂ h)
  rw [Equiv.symm_apply_apply] at key

  congr 1
  conv_lhs => rw [key]
  rw [assoc]

/-- Naturality of `moduleIHom_tensor_left_equiv` in the right module argument `m₂`:
post-composition with `Hom(m₁, X ◁ᵐ f)` corresponds to post-composition with
`X ◁ Hom(m₁, f)`. -/
theorem moduleIHom_tensor_left_equiv_natural_m₂ {Y X : C} [HasRightDual X]
    {m₁ m₂ m₂' : M} (f : m₂ ⟶ m₂') (g : Y ⟶ moduleIHom (C := C) m₁ (X ⊗ᵐ m₂)) :
    moduleIHom_tensor_left_equiv Y X m₁ m₂' (g ≫ moduleIHomMapRight m₁ (X ◁ᵐ f)) =
      moduleIHom_tensor_left_equiv Y X m₁ m₂ g ≫ X ◁ moduleIHomMapRight m₁ f := by sorry

/-- Naturality of `moduleIHom_tensor_left_equiv` in the rigid object `X`:
post-composition with `Hom(m₁, f ▷ᵐ m₂)` corresponds to post-composition with `f ▷ Hom(m₁, m₂)`. -/
theorem moduleIHom_tensor_left_equiv_natural_X {Y X₁ X₂ : C}
    [HasRightDual X₁] [HasRightDual X₂]
    {m₁ m₂ : M} (f : X₁ ⟶ X₂) (g : Y ⟶ moduleIHom (C := C) m₁ (X₁ ⊗ᵐ m₂)) :
    moduleIHom_tensor_left_equiv Y X₂ m₁ m₂
      (g ≫ moduleIHomMapRight m₁ (f ▷ᵐ m₂)) =
    moduleIHom_tensor_left_equiv Y X₁ m₁ m₂ g ≫ f ▷ moduleIHom (C := C) m₁ m₂ := by sorry

/-- If `f : m₂ ⟶ m₂'` is a monomorphism, then `moduleIHomMapRight m₁ f` is also a
monomorphism, using the internal Hom adjunction. -/
theorem moduleIHomRight_preserves_mono_proof
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [LeftModuleCategory C M]
    [HasModuleInternalHom C M]
    (m₁ : M) {m₂ m₂' : M} (f : m₂ ⟶ m₂') (hf : Mono f) :
    Mono (moduleIHomMapRight (C := C) m₁ f) := by
  constructor
  intro X g h hgh
  apply (moduleIHomEquiv X m₁ m₂).symm.injective
  have hg := moduleIHomEquiv_natural_right X m₁ f ((moduleIHomEquiv X m₁ m₂).symm g)
  rw [Equiv.apply_symm_apply] at hg
  have hh := moduleIHomEquiv_natural_right X m₁ f ((moduleIHomEquiv X m₁ m₂).symm h)
  rw [Equiv.apply_symm_apply] at hh
  have key : (moduleIHomEquiv X m₁ m₂).symm g ≫ f =
      (moduleIHomEquiv X m₁ m₂).symm h ≫ f := by
    apply (moduleIHomEquiv X m₁ m₂').injective
    rw [hg, hh, hgh]
  exact hf.right_cancellation _ _ key

/-- In an exact module category, if `f : m₂ ⟶ m₂'` is an epimorphism, then
`moduleIHomMapRight m₁ f` is also an epimorphism (Corollary 2.10.6, exactness in `m₂`). -/
theorem moduleIHomRight_preserves_epi_ax
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]
    [HasModuleInternalHom C M]
    (m₁ : M) {m₂ m₂' : M} (f : m₂ ⟶ m₂') (hf : Epi f) :
    Epi (moduleIHomMapRight (C := C) m₁ f) := by


  sorry

/-- In an exact module category, a monomorphism `f : m₁ ⟶ m₁'` induces an epimorphism
`moduleIHomMapLeft f m₂` (Corollary 2.10.6, mono-to-epi exactness in `m₁`). -/
theorem moduleIHomLeft_sends_mono_to_epi_ax
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]
    [HasModuleInternalHom C M]
    {m₁ m₁' : M} (f : m₁ ⟶ m₁') (hf : Mono f) (m₂ : M) :
    Epi (moduleIHomMapLeft (C := C) f m₂) := by


  sorry

/-- In an exact module category, an epimorphism `f : m₁ ⟶ m₁'` induces a monomorphism
`moduleIHomMapLeft f m₂` (Corollary 2.10.6, epi-to-mono exactness in `m₁`). -/
theorem moduleIHomLeft_sends_epi_to_mono_ax
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]
    [HasModuleInternalHom C M]
    {m₁ m₁' : M} (f : m₁ ⟶ m₁') (hf : Epi f) (m₂ : M) :
    Mono (moduleIHomMapLeft (C := C) f m₂) := by


  sorry

/-- Combined statement of Corollary 2.10.6 collecting the four exactness properties of
the internal Hom functors `moduleIHomMapRight` and `moduleIHomMapLeft` in an exact module
category. -/
theorem corollary_2_10_6_combined
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]
    [HasModuleInternalHom C M] :

    (∀ (m₁ : M) {m₂ m₂' : M} (f : m₂ ⟶ m₂'), Mono f → Mono (moduleIHomMapRight (C := C) m₁ f)) ∧
    (∀ (m₁ : M) {m₂ m₂' : M} (f : m₂ ⟶ m₂'), Epi f → Epi (moduleIHomMapRight (C := C) m₁ f)) ∧

    (∀ {m₁ m₁' : M} (f : m₁ ⟶ m₁'), Mono f → ∀ (m₂ : M), Epi (moduleIHomMapLeft (C := C) f m₂)) ∧
    (∀ {m₁ m₁' : M} (f : m₁ ⟶ m₁'), Epi f → ∀ (m₂ : M), Mono (moduleIHomMapLeft (C := C) f m₂)) :=
  ⟨fun m₁ _ _ f hf => moduleIHomRight_preserves_mono_proof m₁ f hf,
   fun m₁ _ _ f hf => moduleIHomRight_preserves_epi_ax m₁ f hf,
   fun f hf m₂ => moduleIHomLeft_sends_mono_to_epi_ax f hf m₂,
   fun f hf m₂ => moduleIHomLeft_sends_epi_to_mono_ax f hf m₂⟩

/-- Corollary 2.10.6: in an exact module category, the internal Hom is biexact, i.e.
preserves monos in `m₂`, epis in `m₂`, sends monos in `m₁` to epis, and epis in `m₁` to
monos. -/
theorem corollary_2_10_6
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {M : Type u₂} [Category.{v₂} M] [ExactModuleCategory C M]
    [HasModuleInternalHom C M] :
    (∀ (m₁ : M) {m₂ m₂' : M} (f : m₂ ⟶ m₂'), Mono f → Mono (moduleIHomMapRight (C := C) m₁ f)) ∧
    (∀ (m₁ : M) {m₂ m₂' : M} (f : m₂ ⟶ m₂'), Epi f → Epi (moduleIHomMapRight (C := C) m₁ f)) ∧
    (∀ {m₁ m₁' : M} (f : m₁ ⟶ m₁'), Mono f → ∀ (m₂ : M), Epi (moduleIHomMapLeft (C := C) f m₂)) ∧
    (∀ {m₁ m₁' : M} (f : m₁ ⟶ m₁'), Epi f → ∀ (m₂ : M), Mono (moduleIHomMapLeft (C := C) f m₂)) :=
  corollary_2_10_6_combined

end CategoryTheory
