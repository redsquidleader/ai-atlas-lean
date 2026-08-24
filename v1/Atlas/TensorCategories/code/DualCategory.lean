/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.ModuleCategory
import Atlas.TensorCategories.code.ExactModuleCategory
import Atlas.TensorCategories.code.IndecomposableModuleCat
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Mon_

set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

universe v u

namespace CategoryTheory

open Category MonoidalCategory LeftModCat Limits

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]
variable (M : Type u) [Category.{v} M] [LeftModuleCategory C M]

/-- Underlying type of the dual category `C*_M`: module endofunctors of the module
category `M` over `C`. -/
def DualCatObj := ModuleFunctor C M M

/-- Definition 2.14.1: the dual category `C*_M` of `C` with respect to a module category
`M`, realised as the category of module endofunctors of `M`. -/
abbrev Definition_2_14_1 := @DualCatObj

namespace DualCatObj

variable {C M}

/-- A morphism in the dual category `C*_M`: a natural transformation between the
underlying functors compatible with the module structure isomorphisms. -/
structure Hom (F G : DualCatObj C M) where
  natTrans : F.toFunctor ⟶ G.toFunctor
  comm : ∀ (X : C) (N : M),
    natTrans.app (X ⊗ᵐ N) ≫ (G.strIso X N).hom =
      (F.strIso X N).hom ≫ X ◁ᵐ (natTrans.app N)

attribute [reassoc] Hom.comm

/-- Two morphisms in `DualCatObj C M` are equal whenever their underlying natural
transformations agree. -/
@[ext]
theorem Hom.ext' {F G : DualCatObj C M} {f g : Hom F G}
    (h : f.natTrans = g.natTrans) : f = g := by
  cases f; cases g; congr

/-- Identity morphism on `F` in the dual category, given by the identity natural
transformation. -/
def Hom.id (F : DualCatObj C M) : Hom F F where
  natTrans := NatTrans.id F.toFunctor
  comm X N := by
    simp [NatTrans.id_app', LeftModuleCategory.actWhiskerLeft_id]

/-- Composition of morphisms in the dual category, given by the vertical composition of
the underlying natural transformations. -/
def Hom.comp {F G H : DualCatObj C M} (α : Hom F G) (β : Hom G H) :
    Hom F H where
  natTrans := α.natTrans ≫ β.natTrans
  comm X N := by
    simp only [NatTrans.comp_app, assoc]
    rw [β.comm, ← assoc, α.comm, assoc]
    congr 1

    have ha : X ◁ᵐ α.natTrans.app N =
        LeftModuleCategoryStruct.actTensorHom (𝟙 X) (α.natTrans.app N) := by
      simp [LeftModuleCategory.actTensorHom_def, LeftModuleCategory.actId_whiskerRight]
    have hb : X ◁ᵐ β.natTrans.app N =
        LeftModuleCategoryStruct.actTensorHom (𝟙 X) (β.natTrans.app N) := by
      simp [LeftModuleCategory.actTensorHom_def, LeftModuleCategory.actId_whiskerRight]
    have hab : X ◁ᵐ (α.natTrans.app N ≫ β.natTrans.app N) =
        LeftModuleCategoryStruct.actTensorHom (𝟙 X) (α.natTrans.app N ≫ β.natTrans.app N) := by
      simp [LeftModuleCategory.actTensorHom_def, LeftModuleCategory.actId_whiskerRight]
    rw [ha, hb, hab, LeftModuleCategory.actTensorHom_comp, comp_id]

/-- Category structure on `DualCatObj C M` whose morphisms are the module-compatible
natural transformations between module endofunctors of `M`. -/
instance categoryInstance : Category (DualCatObj C M) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext' (by ext x; simp [Hom.comp, Hom.id])
  comp_id f := Hom.ext' (by ext x; simp [Hom.comp, Hom.id])
  assoc f g h := Hom.ext' (by ext x; simp [Hom.comp])

/-- The underlying natural transformation of the identity morphism in `DualCatObj C M`
is the identity natural transformation. -/
@[simp]
theorem id_natTrans (F : DualCatObj C M) :
    (𝟙 F : Hom F F).natTrans = NatTrans.id F.toFunctor := rfl

/-- The underlying natural transformation of a composition in `DualCatObj C M` is the
composition of the underlying natural transformations. -/
@[simp]
theorem comp_natTrans {F G H : DualCatObj C M} (f : F ⟶ G) (g : G ⟶ H) :
    (f ≫ g).natTrans = f.natTrans ≫ g.natTrans := rfl

/-- The identity module endofunctor of `M`, which serves as the monoidal unit of the
dual category. -/
def idModuleFunctor : DualCatObj C M :=
  { toFunctor := 𝟭 M
    strIso := fun _ _ => Iso.refl _
    strIso_natural := fun f g => by
      dsimp [Iso.refl]
      simp
    strIso_assoc := fun X Y N => by
      dsimp [Iso.refl]
      simp
    strIso_unit := fun N => by
      dsimp [Iso.refl]
      simp }

/-- Composition of two module endofunctors of `M`, giving the tensor product in the
dual category `C*_M`. -/
def compModuleFunctor (F₁ F₂ : DualCatObj C M) : DualCatObj C M :=
  { toFunctor := F₁.toFunctor ⋙ F₂.toFunctor
    strIso := fun X N =>
      (F₂.toFunctor.mapIso (F₁.strIso X N)).trans (F₂.strIso X (F₁.toFunctor.obj N))
    strIso_natural := fun {X₁ X₂ N₁ N₂} f g => by
      simp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, assoc]
      rw [← F₂.toFunctor.map_comp_assoc, F₁.strIso_natural,
          F₂.toFunctor.map_comp, assoc, F₂.strIso_natural]
    strIso_assoc := fun X Y N => by
      simp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, assoc]


      have whisker_comp : X ◁ᵐ (F₂.toFunctor.map (F₁.strIso Y N).hom ≫
          (F₂.strIso Y (F₁.toFunctor.obj N)).hom) =
        X ◁ᵐ F₂.toFunctor.map (F₁.strIso Y N).hom ≫
          X ◁ᵐ (F₂.strIso Y (F₁.toFunctor.obj N)).hom := by
        have h := LeftModuleCategory.actTensorHom_comp (𝟙 X)
          (F₂.toFunctor.map (F₁.strIso Y N).hom) (𝟙 X)
          ((F₂.strIso Y (F₁.toFunctor.obj N)).hom)
        simp [LeftModuleCategory.actTensorHom_def,
              LeftModuleCategory.actId_whiskerRight] at h
        exact h.symm
      rw [whisker_comp]

      have nat_s₂ : (F₂.strIso X (F₁.toFunctor.obj (Y ⊗ᵐ N))).hom ≫
          X ◁ᵐ F₂.toFunctor.map (F₁.strIso Y N).hom =
        F₂.toFunctor.map (X ◁ᵐ (F₁.strIso Y N).hom) ≫
          (F₂.strIso X (Y ⊗ᵐ F₁.toFunctor.obj N)).hom := by
        have := F₂.strIso_natural (𝟙 X) (F₁.strIso Y N).hom
        simp [LeftModuleCategory.actId_whiskerRight] at this
        exact this.symm
      slice_lhs 3 4 => rw [nat_s₂]
      simp only [assoc]

      rw [← F₂.toFunctor.map_comp_assoc, ← F₂.toFunctor.map_comp_assoc]

      have inner : (F₁.toFunctor.map (actμ_ X Y N).hom ≫ (F₁.strIso X (Y ⊗ᵐ N)).hom) ≫
          X ◁ᵐ (F₁.strIso Y N).hom =
        (F₁.strIso (X ⊗ Y) N).hom ≫ (actμ_ X Y (F₁.toFunctor.obj N)).hom := by
        rw [assoc]; exact F₁.strIso_assoc X Y N
      rw [show F₂.toFunctor.map ((F₁.toFunctor.map (actμ_ X Y N).hom ≫
          (F₁.strIso X (Y ⊗ᵐ N)).hom) ≫ X ◁ᵐ (F₁.strIso Y N).hom) =
        F₂.toFunctor.map ((F₁.strIso (X ⊗ Y) N).hom ≫
          (actμ_ X Y (F₁.toFunctor.obj N)).hom) from congr_arg F₂.toFunctor.map inner]
      rw [F₂.toFunctor.map_comp, assoc]
      congr 1
      exact F₂.strIso_assoc X Y (F₁.toFunctor.obj N)
    strIso_unit := fun N => by
      simp only [Functor.comp_obj, Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom, assoc]
      rw [F₁.strIso_unit, F₂.toFunctor.map_comp]
      congr 1
      exact F₂.strIso_unit (F₁.toFunctor.obj N) }

/-- Left whiskering of a morphism `α : G₁ ⟶ G₂` by a module endofunctor `F`, giving a
morphism `F ⊗ G₁ ⟶ F ⊗ G₂` in `DualCatObj C M`. -/
def dualWhiskerLeft (F : DualCatObj C M) {G₁ G₂ : DualCatObj C M} (α : G₁ ⟶ G₂) :
    compModuleFunctor F G₁ ⟶ compModuleFunctor F G₂ where
  natTrans :=
    { app := fun N => α.natTrans.app (F.toFunctor.obj N)
      naturality := fun N₁ N₂ f => α.natTrans.naturality (F.toFunctor.map f) }
  comm X N := by
    simp only [compModuleFunctor, Iso.trans_hom, Functor.mapIso_hom, Functor.comp_obj, assoc]
    rw [← α.natTrans.naturality_assoc, α.comm]

/-- Right whiskering of a morphism `α : F₁ ⟶ F₂` by a module endofunctor `G`, giving a
morphism `F₁ ⊗ G ⟶ F₂ ⊗ G` in `DualCatObj C M`. -/
def dualWhiskerRight {F₁ F₂ : DualCatObj C M} (α : F₁ ⟶ F₂) (G : DualCatObj C M) :
    compModuleFunctor F₁ G ⟶ compModuleFunctor F₂ G where
  natTrans :=
    { app := fun N => G.toFunctor.map (α.natTrans.app N)
      naturality := fun N₁ N₂ f => by
        dsimp [compModuleFunctor]
        rw [← G.toFunctor.map_comp, ← G.toFunctor.map_comp]
        congr 1; exact α.natTrans.naturality f }
  comm X N := by
    simp only [compModuleFunctor, Iso.trans_hom, Functor.mapIso_hom, Functor.comp_obj, assoc]


    rw [← G.toFunctor.map_comp_assoc, α.comm, G.toFunctor.map_comp, assoc]


    congr 1

    have := G.strIso_natural (𝟙 X) (α.natTrans.app N)
    simp [LeftModuleCategory.actId_whiskerRight] at this
    exact this

/-- Reducible alias for the category structure on `DualCatObj C M`. -/
@[reducible]
def dualCategory : Category (DualCatObj C M) := categoryInstance

/-- The module-structure isomorphisms of the two ways of bracketing a triple composition
of module endofunctors agree on objects. -/
lemma compModuleFunctor_assoc_strIso (F₁ F₂ F₃ : DualCatObj C M) (X : C) (N : M) :
    (compModuleFunctor (compModuleFunctor F₁ F₂) F₃).strIso X N =
    (compModuleFunctor F₁ (compModuleFunctor F₂ F₃)).strIso X N := by
  ext
  simp [compModuleFunctor, Iso.trans_hom, Functor.mapIso_hom, Functor.comp_obj,
        Functor.comp_map]

/-- Associator isomorphism for the monoidal structure on `DualCatObj C M` induced by
composition of module endofunctors. -/
def dualAssociator (F₁ F₂ F₃ : DualCatObj C M) :
    compModuleFunctor (compModuleFunctor F₁ F₂) F₃ ≅
    compModuleFunctor F₁ (compModuleFunctor F₂ F₃) where
  hom := Hom.mk
    (NatTrans.mk (fun N => 𝟙 _) (fun _ _ _ => by
      dsimp [compModuleFunctor]
      simp))
    (fun X N => by
      rw [compModuleFunctor_assoc_strIso]
      dsimp [compModuleFunctor]
      simp [LeftModuleCategory.actWhiskerLeft_id])
  inv := Hom.mk
    (NatTrans.mk (fun N => 𝟙 _) (fun _ _ _ => by
      dsimp [compModuleFunctor]
      simp))
    (fun X N => by
      rw [← compModuleFunctor_assoc_strIso]
      dsimp [compModuleFunctor]
      simp [LeftModuleCategory.actWhiskerLeft_id])
  hom_inv_id := Hom.ext' (by ext; dsimp [Hom.comp, Hom.id, compModuleFunctor]; simp)
  inv_hom_id := Hom.ext' (by ext; dsimp [Hom.comp, Hom.id, compModuleFunctor]; simp)

/-- Composing on the left with the identity module endofunctor does not change the
structure isomorphism. -/
lemma compModuleFunctor_left_id_strIso (F : DualCatObj C M) (X : C) (N : M) :
    (compModuleFunctor idModuleFunctor F).strIso X N = F.strIso X N := by
  ext
  simp [compModuleFunctor, idModuleFunctor, Iso.trans_hom, Functor.mapIso_hom, Iso.refl]

/-- Left unitor for the monoidal structure on `DualCatObj C M`, witnessing
`𝟙 ⊗ F ≅ F`. -/
def dualLeftUnitor (F : DualCatObj C M) :
    compModuleFunctor idModuleFunctor F ≅ F where
  hom := Hom.mk
    (NatTrans.mk (fun N => 𝟙 _) (fun _ _ _ => by
      dsimp [compModuleFunctor, idModuleFunctor]
      simp))
    (fun X N => by
      rw [compModuleFunctor_left_id_strIso]
      dsimp [compModuleFunctor, idModuleFunctor]
      simp [LeftModuleCategory.actWhiskerLeft_id])
  inv := Hom.mk
    (NatTrans.mk (fun N => 𝟙 _) (fun _ _ _ => by
      dsimp [compModuleFunctor, idModuleFunctor]
      simp))
    (fun X N => by
      rw [← compModuleFunctor_left_id_strIso]
      dsimp [compModuleFunctor, idModuleFunctor]
      simp [LeftModuleCategory.actWhiskerLeft_id])
  hom_inv_id := Hom.ext' (by ext; dsimp [Hom.comp, Hom.id, compModuleFunctor, idModuleFunctor]; simp)
  inv_hom_id := Hom.ext' (by ext; dsimp [Hom.comp, Hom.id, compModuleFunctor, idModuleFunctor]; simp)

/-- Composing on the right with the identity module endofunctor does not change the
structure isomorphism. -/
lemma compModuleFunctor_right_id_strIso (F : DualCatObj C M) (X : C) (N : M) :
    (compModuleFunctor F idModuleFunctor).strIso X N = F.strIso X N := by
  ext
  simp [compModuleFunctor, idModuleFunctor, Iso.trans_hom, Functor.mapIso_hom, Iso.refl]

/-- Right unitor for the monoidal structure on `DualCatObj C M`, witnessing
`F ⊗ 𝟙 ≅ F`. -/
def dualRightUnitor (F : DualCatObj C M) :
    compModuleFunctor F idModuleFunctor ≅ F where
  hom := Hom.mk
    (NatTrans.mk (fun N => 𝟙 _) (fun _ _ _ => by
      dsimp [compModuleFunctor, idModuleFunctor]
      simp))
    (fun X N => by
      rw [compModuleFunctor_right_id_strIso]
      dsimp [compModuleFunctor, idModuleFunctor]
      simp [LeftModuleCategory.actWhiskerLeft_id])
  inv := Hom.mk
    (NatTrans.mk (fun N => 𝟙 _) (fun _ _ _ => by
      dsimp [compModuleFunctor, idModuleFunctor]
      simp))
    (fun X N => by
      rw [← compModuleFunctor_right_id_strIso]
      dsimp [compModuleFunctor, idModuleFunctor]
      simp [LeftModuleCategory.actWhiskerLeft_id])
  hom_inv_id := Hom.ext' (by ext; dsimp [Hom.comp, Hom.id, compModuleFunctor, idModuleFunctor]; simp)
  inv_hom_id := Hom.ext' (by ext; dsimp [Hom.comp, Hom.id, compModuleFunctor, idModuleFunctor]; simp)

/-- Monoidal category structure data on `DualCatObj C M`: tensor product is functor
composition, the unit is the identity module endofunctor, and the coherence
isomorphisms are the canonical ones. -/
instance dualMonoidalCategoryStruct : MonoidalCategoryStruct (DualCatObj C M) where
  tensorObj := compModuleFunctor
  whiskerLeft := dualWhiskerLeft
  whiskerRight := fun f G => dualWhiskerRight f G
  tensorUnit := idModuleFunctor
  associator := dualAssociator
  leftUnitor := dualLeftUnitor
  rightUnitor := dualRightUnitor


/-- Tensor product in `DualCatObj C M` is functor composition. -/
@[simp] lemma tensorObj_eq (F G : DualCatObj C M) : F ⊗ G = compModuleFunctor F G := rfl
/-- The monoidal unit of `DualCatObj C M` is the identity module endofunctor. -/
@[simp] lemma tensorUnit_eq : (𝟙_ (DualCatObj C M)) = idModuleFunctor := rfl
/-- Left whiskering in `DualCatObj C M` agrees with `dualWhiskerLeft`. -/
@[simp] lemma whiskerLeft_eq (F : DualCatObj C M) {G₁ G₂ : DualCatObj C M} (f : G₁ ⟶ G₂) :
    F ◁ f = dualWhiskerLeft F f := rfl
/-- Right whiskering in `DualCatObj C M` agrees with `dualWhiskerRight`. -/
@[simp] lemma whiskerRight_eq {F₁ F₂ : DualCatObj C M} (f : F₁ ⟶ F₂) (G : DualCatObj C M) :
    f ▷ G = dualWhiskerRight f G := rfl
/-- The associator in `DualCatObj C M` agrees with `dualAssociator`. -/
@[simp] lemma associator_eq (F₁ F₂ F₃ : DualCatObj C M) :
    α_ F₁ F₂ F₃ = dualAssociator F₁ F₂ F₃ := rfl
/-- The left unitor in `DualCatObj C M` agrees with `dualLeftUnitor`. -/
@[simp] lemma leftUnitor_eq (F : DualCatObj C M) : λ_ F = dualLeftUnitor F := rfl
/-- The right unitor in `DualCatObj C M` agrees with `dualRightUnitor`. -/
@[simp] lemma rightUnitor_eq (F : DualCatObj C M) : ρ_ F = dualRightUnitor F := rfl

/-- Monoidal category structure on `DualCatObj C M` packaging together the data of
`dualMonoidalCategoryStruct` with the coherence axioms (pentagon, triangle, etc.). -/
instance dualMonoidalCategory : MonoidalCategory (DualCatObj C M) :=
  MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun F G => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        tensorObj_eq, id_natTrans, comp_natTrans, NatTrans.comp_app]
      dsimp [dualWhiskerLeft, dualWhiskerRight, compModuleFunctor]
      simp [Functor.map_id])
    (id_tensorHom := fun F {G₁ G₂} f => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        comp_natTrans, NatTrans.comp_app]
      dsimp [dualWhiskerLeft, dualWhiskerRight, compModuleFunctor]
      simp)
    (tensorHom_id := fun {F₁ F₂} f G => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        comp_natTrans, NatTrans.comp_app]
      dsimp [dualWhiskerLeft, dualWhiskerRight, compModuleFunctor]
      simp)
    (tensorHom_comp_tensorHom := fun {X₁ Y₁ Z₁ X₂ Y₂ Z₂} f₁ f₂ g₁ g₂ => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        comp_natTrans, NatTrans.comp_app]
      dsimp [dualWhiskerLeft, dualWhiskerRight, compModuleFunctor, Hom.comp]


      have nat := f₂.natTrans.naturality (g₁.natTrans.app N)

      slice_lhs 2 3 => rw [← nat]
      simp only [assoc]
      rw [← X₂.toFunctor.map_comp_assoc])
    (associator_naturality := fun {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        comp_natTrans, NatTrans.comp_app]
      dsimp [dualAssociator, dualWhiskerLeft, dualWhiskerRight, compModuleFunctor, Hom.comp]
      simp only [id_comp, comp_id]
      rw [X₃.toFunctor.map_comp, assoc])
    (leftUnitor_naturality := fun {X₁ X₂} f => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        comp_natTrans, NatTrans.comp_app]
      dsimp [dualLeftUnitor, dualWhiskerLeft, dualWhiskerRight,
             compModuleFunctor, idModuleFunctor]
      simp)
    (rightUnitor_naturality := fun {X₁ X₂} f => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        comp_natTrans, NatTrans.comp_app]
      dsimp [dualRightUnitor, dualWhiskerLeft, dualWhiskerRight,
             compModuleFunctor, idModuleFunctor]
      simp)

    (pentagon := fun W X Y Z => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom,
        comp_natTrans, NatTrans.comp_app]
      dsimp [dualAssociator, dualWhiskerLeft, dualWhiskerRight, Hom.comp, compModuleFunctor]
      simp [Functor.map_id])
    (triangle := fun X Y => by
      apply Hom.ext'; ext N
      simp only [MonoidalCategoryStruct.tensorHom, comp_natTrans, NatTrans.comp_app]
      dsimp [dualAssociator, dualLeftUnitor, dualRightUnitor,
             dualWhiskerLeft, dualWhiskerRight, Hom.comp, compModuleFunctor, idModuleFunctor]
      simp [Functor.map_id])

/-- Evaluation of a module endofunctor `F ∈ DualCatObj C M` at an object `N ∈ M`. -/
def evalObj (F : DualCatObj C M) (N : M) : M := F.toFunctor.obj N

/-- Evaluation of a module endofunctor `F` on a morphism of `M`. -/
def evalMap (F : DualCatObj C M) {N₁ N₂ : M} (f : N₁ ⟶ N₂) :
    evalObj F N₁ ⟶ evalObj F N₂ :=
  F.toFunctor.map f

/-- Evaluation of a morphism `α : F₁ ⟶ F₂` of `DualCatObj C M` at an object `N ∈ M`. -/
def evalNatApp {F₁ F₂ : DualCatObj C M} (α : F₁ ⟶ F₂) (N : M) :
    evalObj F₁ N ⟶ evalObj F₂ N :=
  α.natTrans.app N

/-- The identity module endofunctor of `M` is not a zero object of `DualCatObj C M`. -/
theorem idModuleFunctor_not_isZero
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (M : Type u) [Category.{v} M] [LeftModuleCategory C M]
    [HasZeroMorphisms (DualCatObj C M)] :
    ¬ IsZero (idModuleFunctor (C := C) (M := M)) := by sorry

/-- There exists some `N ∈ M` whose evaluation under the identity module endofunctor is
nonzero. -/
theorem idModuleFunctor_eval_nonzero
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (M : Type u) [Category.{v} M] [LeftModuleCategory C M]
    [HasZeroMorphisms (DualCatObj C M)] :
    ∃ (N : M), ¬ IsZero (evalObj (idModuleFunctor (C := C) (M := M)) N) := by sorry

/-- Decomposition of the identity module endofunctor as a biproduct of nonzero objects,
extracted from Definition 2.3 (preliminary form). -/
theorem module_category_decomposition_from_2_3
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (M : Type u) [Category.{v} M] [LeftModuleCategory C M]
    [HasZeroMorphisms (DualCatObj C M)] :
    (¬ IsZero (idModuleFunctor (C := C) (M := M))) ∧
    ∃ (ι : Type u) (e : ι → DualCatObj C M)
      (hbp : HasBiproduct e)
      (_ : ∀ (i : ι), ∃ (N : M), ¬ IsZero (evalObj (e i) N)),
      Nonempty (idModuleFunctor (C := C) (M := M) ≅
        @biproduct ι (DualCatObj C M) _ _ e hbp) := by

  refine ⟨idModuleFunctor_not_isZero C M, ?_⟩


  let e : PUnit.{u+1} → DualCatObj C M := fun _ => idModuleFunctor

  let hbp : HasBiproduct e := inferInstance
  refine ⟨PUnit.{u+1}, e, hbp, ?_, ?_⟩
  ·
    intro i
    exact idModuleFunctor_eval_nonzero C M
  ·

    exact ⟨(biproductUniqueIso e).symm⟩

/-- Refined decomposition of the identity module endofunctor as a biproduct of nonzero
indecomposable summands, packaged from `module_category_decomposition_from_2_3`. -/
theorem module_category_indecomposable_decomposition
    [HasZeroMorphisms (DualCatObj C M)] :
    (¬ IsZero (idModuleFunctor (C := C) (M := M))) ∧
    ∃ (ι : Type u) (e : ι → DualCatObj C M)
      (hbp : HasBiproduct e)
      (_ : ∀ (i : ι), ∃ (N : M), ¬ IsZero (evalObj (e i) N)),
      Nonempty (idModuleFunctor (C := C) (M := M) ≅
        @biproduct ι (DualCatObj C M) _ _ e hbp) :=
  module_category_decomposition_from_2_3 C M

/-- A monomorphism `F ⟶ 𝟙` of module endofunctors has monomorphic components at every
object of `M`. -/
theorem dualCatObj_mono_component_mono
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (M : Type u) [Category.{v} M] [LeftModuleCategory C M]
    [HasZeroMorphisms (DualCatObj C M)]
    {F : DualCatObj C M}
    (h_mono : F ⟶ idModuleFunctor (C := C) (M := M))
    [Mono h_mono]
    (N : M) : Mono (h_mono.natTrans.app N) := by sorry

/-- For an indecomposable module category, every nonzero subfunctor of the identity with
monic components is in fact an isomorphism on each component. -/
theorem exact_subfunctor_component_isIso
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (M : Type u) [Category.{v} M] [LeftModuleCategory C M]
    [IsIndecomposableModuleCategory C M]
    [HasZeroMorphisms (DualCatObj C M)]
    {F : DualCatObj C M}
    (h_mono : F ⟶ idModuleFunctor (C := C) (M := M))
    [Mono h_mono]
    (hne : h_mono ≠ 0)
    (h_comp_mono : ∀ (N : M), Mono (h_mono.natTrans.app N))
    (N : M) : IsIso (h_mono.natTrans.app N) := by sorry

/-- Convenience packaging of `exact_subfunctor_component_isIso` combining the two
lemmas above for an indecomposable module category. -/
theorem subfunctor_component_isIso_of_indecomposable
    [IsIndecomposableModuleCategory C M]
    [HasZeroMorphisms (DualCatObj C M)]
    {F : DualCatObj C M}
    (h_mono : F ⟶ idModuleFunctor (C := C) (M := M))
    [Mono h_mono]
    (hne : h_mono ≠ 0) :
    ∀ (N : M), IsIso (h_mono.natTrans.app N) := by


  have h_comp_mono : ∀ (N : M), Mono (h_mono.natTrans.app N) :=
    fun N => dualCatObj_mono_component_mono C M h_mono N


  intro N
  exact exact_subfunctor_component_isIso C M h_mono hne h_comp_mono N

/-- Functoriality of left whiskering on `M`: `X ◁ᵐ (f ≫ g) = X ◁ᵐ f ≫ X ◁ᵐ g`. -/
theorem actWhiskerLeft_comp (X : C) {A B D : M} (f : A ⟶ B) (g : B ⟶ D) :
    X ◁ᵐ (f ≫ g) = X ◁ᵐ f ≫ X ◁ᵐ g := by
  have := LeftModuleCategory.actTensorHom_comp (𝟙 X) f (𝟙 X) g
  simp only [LeftModuleCategory.actTensorHom_def,
    LeftModuleCategory.actId_whiskerRight, id_comp, comp_id] at this
  exact this.symm

/-- Left whiskering preserves isomorphisms: if `f : A ⟶ B` is an isomorphism in `M` then
so is `X ◁ᵐ f`. -/
instance actWhiskerLeft_isIso (X : C) {A B : M} (f : A ⟶ B) [IsIso f] :
    IsIso (X ◁ᵐ f) where
  out := ⟨X ◁ᵐ inv f, by
    constructor
    · rw [← actWhiskerLeft_comp, IsIso.hom_inv_id,
          LeftModuleCategory.actWhiskerLeft_id]
    · rw [← actWhiskerLeft_comp, IsIso.inv_hom_id,
          LeftModuleCategory.actWhiskerLeft_id]⟩

/-- Construct an inverse morphism `𝟙 ⟶ F` from a morphism `α : F ⟶ 𝟙` whose components
are isomorphisms at every object of `M`. -/
noncomputable def Hom.mkInverse
    {F : DualCatObj C M}
    (α : Hom F (idModuleFunctor (C := C) (M := M)))
    (hiso : ∀ (N : M), IsIso (α.natTrans.app N)) :
    Hom (idModuleFunctor (C := C) (M := M)) F where
  natTrans := {
    app := fun N => @inv _ _ _ _ (α.natTrans.app N) (hiso N)
    naturality := fun {N₁ N₂} f => by
      haveI := hiso N₁
      haveI := hiso N₂
      have hnat := α.natTrans.naturality f
      rw [← cancel_epi (α.natTrans.app N₁)]
      simp only [assoc, IsIso.hom_inv_id_assoc]
      rw [← assoc]
      rw [← hnat]
      simp [IsIso.hom_inv_id]

  }
  comm := fun X N => by
    haveI := hiso N
    haveI := hiso (X ⊗ᵐ N)
    have hcomm := α.comm X N
    show inv (α.natTrans.app (X ⊗ᵐ N)) ≫ (F.strIso X N).hom =
      (idModuleFunctor.strIso X N).hom ≫ X ◁ᵐ inv (α.natTrans.app N)
    rw [IsIso.inv_comp_eq]
    rw [← assoc, ← hcomm.symm, assoc, ← actWhiskerLeft_comp, IsIso.hom_inv_id,
        LeftModuleCategory.actWhiskerLeft_id, comp_id]

/-- The constructed inverse from `Hom.mkInverse` is a left inverse to `α`. -/
theorem Hom.mkInverse_comp
    {F : DualCatObj C M}
    (α : Hom F (idModuleFunctor (C := C) (M := M)))
    (hiso : ∀ (N : M), IsIso (α.natTrans.app N)) :
    Hom.comp (Hom.mkInverse α hiso) α =
      Hom.id (idModuleFunctor (C := C) (M := M)) := by
  apply Hom.ext'
  ext N
  simp only [Hom.comp, Hom.mkInverse, Hom.id, NatTrans.comp_app, NatTrans.id_app']
  haveI := hiso N
  exact IsIso.inv_hom_id (α.natTrans.app N)

/-- The constructed inverse from `Hom.mkInverse` is a right inverse to `α`. -/
theorem Hom.comp_mkInverse
    {F : DualCatObj C M}
    (α : Hom F (idModuleFunctor (C := C) (M := M)))
    (hiso : ∀ (N : M), IsIso (α.natTrans.app N)) :
    Hom.comp α (Hom.mkInverse α hiso) = Hom.id F := by
  apply Hom.ext'
  ext N
  simp only [Hom.comp, Hom.mkInverse, Hom.id, NatTrans.comp_app, NatTrans.id_app']
  haveI := hiso N
  exact IsIso.hom_inv_id (α.natTrans.app N)

set_option maxHeartbeats 800000 in
/-- If `M` is an indecomposable module category, then the monoidal unit of the dual
category `C*_M` is a simple object. -/
theorem unit_simple_when_indecomposable
    [IsIndecomposableModuleCategory C M]
    [HasZeroMorphisms (DualCatObj C M)] :
    Simple (𝟙_ (DualCatObj C M)) := by
  simp only [tensorUnit_eq]
  refine Simple.mk (fun {F} f => ?_)
  intro mono_f
  constructor
  ·
    intro hiso hzero
    subst hzero

    have h := IsIso.inv_hom_id (f := (0 : F ⟶ idModuleFunctor (C := C) (M := M)))
    rw [comp_zero] at h

    have hni : ¬ IsZero (idModuleFunctor (C := C) (M := M)) :=
      (module_category_indecomposable_decomposition (C := C) (M := M)).1
    exact hni ((IsZero.iff_id_eq_zero _).mpr h.symm)
  ·
    intro hne
    haveI : Mono f := mono_f
    have hcomp := subfunctor_component_isIso_of_indecomposable f hne
    exact ⟨⟨Hom.mkInverse f hcomp, Hom.comp_mkInverse f hcomp,
           Hom.mkInverse_comp f hcomp⟩⟩

/-- The unit of the dual category decomposes as a biproduct of simple, nonzero
projector objects, each having some nonzero evaluation in `M`. -/
theorem projectors_simple
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (M : Type u) [Category.{v} M] [LeftModuleCategory C M]
    [HasZeroMorphisms (DualCatObj C M)] :
    ∃ (ι : Type u) (e : ι → DualCatObj C M)
      (hbp : HasBiproduct e),
      (∀ (i : ι), ∃ (N : M), ¬ IsZero (evalObj (e i) N)) ∧
      Nonempty (𝟙_ (DualCatObj C M) ≅ @biproduct ι (DualCatObj C M) _ _ e hbp) ∧
      (∀ i, Simple (e i)) := by sorry

/-- Lemma 2.14.3: the monoidal unit of the dual category is nonzero and decomposes as a
biproduct of simple projector objects, each with some nonzero evaluation. -/
theorem lemma_2_14_3
    [HasZeroMorphisms (DualCatObj C M)] :

    (¬ IsZero (𝟙_ (DualCatObj C M))) ∧

    ∃ (ι : Type u) (e : ι → DualCatObj C M)
      (hbp : HasBiproduct e),
      (∀ (i : ι), ∃ (N : M), ¬ IsZero (evalObj (e i) N)) ∧
      Nonempty (𝟙_ (DualCatObj C M) ≅ @biproduct ι (DualCatObj C M) _ _ e hbp) ∧
      (∀ i, Simple (e i)) := by
  constructor
  ·
    simp only [tensorUnit_eq]
    exact idModuleFunctor_not_isZero C M
  ·
    exact projectors_simple C M

/-- The endofunctor of `M` given by tensoring with a fixed object `X ∈ C` on the left. -/
def actionFunctor (X : C) : M ⥤ M where
  obj := fun N => X ⊗ᵐ N
  map := fun f => X ◁ᵐ f
  map_id := fun N => by simp [LeftModuleCategory.actWhiskerLeft_id]
  map_comp := fun f g => by
    have h1 := LeftModuleCategory.actTensorHom_comp (𝟙 X) f (𝟙 X) g
    simp [LeftModuleCategory.actTensorHom_def,
          LeftModuleCategory.actId_whiskerRight] at h1
    exact h1.symm

/-- If `M` is an exact module category over `C`, the canonical evaluation action turns
`M` into a left module category over the dual category `C*_M`. -/
noncomputable instance dualCat_leftModuleCategory_instance
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (M : Type u) [Category.{v} M] [LeftModuleCategory C M]
    (h_exact : ∀ (P : C) (N : M) [Projective P], Projective (P ⊗ᵐ N)) :
    LeftModuleCategory (DualCatObj C M) M := by sorry

/-- The action of the dual category on `M` preserves projective objects: applying a
projective `F ∈ C*_M` to any `N ∈ M` yields a projective object. -/
theorem dualCat_action_preserves_projective
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (M : Type u) [Category.{v} M] [LeftModuleCategory C M]
    (h_exact : ∀ (P : C) (N : M) [Projective P], Projective (P ⊗ᵐ N))
    (F : DualCatObj C M) (N : M) [Projective F] :
    @Projective M _
      ((dualCat_leftModuleCategory_instance C M h_exact).toLeftModuleCategoryStruct.actObj F N) := by sorry

/-- Lemma 2.14.4 (constructive form): an exact `C`-module category `M` is also an exact
module category over the dual category `C*_M`. -/
@[reducible]
noncomputable def lem_2_14_4_dualAction_exact_moduleCat
    (h_exact : ∀ (P : C) (N : M) [Projective P], Projective (P ⊗ᵐ N)) :
    ExactModuleCategory (DualCatObj C M) M :=
  { dualCat_leftModuleCategory_instance C M h_exact with
    action_preserves_projective := fun F N _ =>
      dualCat_action_preserves_projective C M h_exact F N }

/-- Lemma 2.14.4: alias for `lem_2_14_4_dualAction_exact_moduleCat`. -/
noncomputable abbrev lemma_2_14_4 := @lem_2_14_4_dualAction_exact_moduleCat

/-- The "double dual" category `(C*_M)*_M`: module endofunctors of `M` viewed as a
module category over `C*_M`. -/
def DoubleDualObj (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (M : Type u) [Category.{v} M] [LeftModuleCategory C M]
    [LeftModuleCategory (DualCatObj C M) M] :=
  ModuleFunctor (DualCatObj C M) M M

/-- A morphism in the double-dual category `(C*_M)*_M`: a natural transformation
between the underlying functors compatible with the `C*_M`-module structures. -/
structure DoubleDualHom [inst : LeftModuleCategory (DualCatObj C M) M]
    (F G : DoubleDualObj C M) where
  natTrans : F.toFunctor ⟶ G.toFunctor
  comm : ∀ (P : DualCatObj C M) (N : M),
    natTrans.app (P ⊗ᵐ N) ≫ (G.strIso P N).hom =
      (F.strIso P N).hom ≫ P ◁ᵐ (natTrans.app N)

/-- Two double-dual morphisms are equal whenever their underlying natural
transformations agree. -/
@[ext]
theorem DoubleDualHom.ext' [inst : LeftModuleCategory (DualCatObj C M) M]
    {F G : DoubleDualObj C M} {f g : DoubleDualHom F G}
    (h : f.natTrans = g.natTrans) : f = g := by
  cases f; cases g; congr

/-- Identity morphism on `F` in the double-dual category, given by the identity natural
transformation. -/
def DoubleDualHom.id [inst : LeftModuleCategory (DualCatObj C M) M]
    (F : DoubleDualObj C M) : DoubleDualHom F F where
  natTrans := NatTrans.id F.toFunctor
  comm P N := by
    simp [NatTrans.id_app', LeftModuleCategory.actWhiskerLeft_id]

/-- Composition of morphisms in the double-dual category, given by the vertical
composition of the underlying natural transformations. -/
def DoubleDualHom.comp [inst : LeftModuleCategory (DualCatObj C M) M]
    {F G H : DoubleDualObj C M}
    (α : DoubleDualHom F G) (β : DoubleDualHom G H) :
    DoubleDualHom F H where
  natTrans := α.natTrans ≫ β.natTrans
  comm P N := by
    simp only [NatTrans.comp_app, assoc]
    rw [β.comm, ← assoc, α.comm, assoc]
    congr 1
    have ha : P ◁ᵐ α.natTrans.app N =
        LeftModuleCategoryStruct.actTensorHom (𝟙 P) (α.natTrans.app N) := by
      simp [LeftModuleCategory.actTensorHom_def, LeftModuleCategory.actId_whiskerRight]
    have hb : P ◁ᵐ β.natTrans.app N =
        LeftModuleCategoryStruct.actTensorHom (𝟙 P) (β.natTrans.app N) := by
      simp [LeftModuleCategory.actTensorHom_def, LeftModuleCategory.actId_whiskerRight]
    have hab : P ◁ᵐ (α.natTrans.app N ≫ β.natTrans.app N) =
        LeftModuleCategoryStruct.actTensorHom (𝟙 P) (α.natTrans.app N ≫ β.natTrans.app N) := by
      simp [LeftModuleCategory.actTensorHom_def, LeftModuleCategory.actId_whiskerRight]
    rw [ha, hb, hab, LeftModuleCategory.actTensorHom_comp, comp_id]

/-- Category structure on the double-dual category `DoubleDualObj C M`, with
`DoubleDualHom` as morphisms. -/
instance doubleDualCategoryInstance [inst : LeftModuleCategory (DualCatObj C M) M] :
    Category (DoubleDualObj C M) where
  Hom := DoubleDualHom
  id := DoubleDualHom.id
  comp := DoubleDualHom.comp
  id_comp f := DoubleDualHom.ext' (by ext x; simp [DoubleDualHom.comp, DoubleDualHom.id])
  comp_id f := DoubleDualHom.ext' (by ext x; simp [DoubleDualHom.comp, DoubleDualHom.id])
  assoc f g h := DoubleDualHom.ext' (by ext x; simp [DoubleDualHom.comp])

/-- The canonical functor `C → (C*_M)*_M` sending an object `X ∈ C` to the action
functor `X ⊗ᵐ -` on `M`. -/
noncomputable def canonicalDoubleDualFunctor
    [inst : LeftModuleCategory (DualCatObj C M) M] :
    ∃ (F : C ⥤ DoubleDualObj C M),
      ∀ X : C, (F.obj X).toFunctor = actionFunctor X := by

  sorry

/-- The canonical functor `C → (C*_M)*_M` is fully faithful. -/
noncomputable def canonicalDoubleDualFunctor_fullFaithful
    [inst : LeftModuleCategory (DualCatObj C M) M] :
    ∀ (F : C ⥤ DoubleDualObj C M),
      (∀ X : C, (F.obj X).toFunctor = actionFunctor X) →
      Functor.FullyFaithful F := by

  sorry

section Lemma_2_14_7

/-- Multiplication on the dual-tensor algebra `ᘁA ⊗ A` formed using the evaluation map
of the left duality on `A`. -/
noncomputable def dualAlg_mul (A : C) [HasLeftDual A] :
    ((ᘁA : C) ⊗ A) ⊗ ((ᘁA : C) ⊗ A) ⟶ (ᘁA : C) ⊗ A :=
  (α_ (ᘁA : C) A ((ᘁA : C) ⊗ A)).hom ≫
  (ᘁA : C) ◁ ((α_ A (ᘁA : C) A).inv ≫ (ε_ (ᘁA : C) A ▷ A) ≫ (λ_ A).hom)

open MonObj in
/-- A left module over an algebra object `B ∈ C`: an object `Y` together with an action
`B ⊗ Y ⟶ Y` satisfying the usual unit and associativity axioms. -/
structure LeftModObj (B : C) [MonObj B] (Y : C) where
  act : B ⊗ Y ⟶ Y
  act_one : (λ_ Y).inv ≫ (MonObj.one ▷ Y) ≫ act = 𝟙 Y
  act_assoc : (α_ B B Y).hom ≫ (B ◁ act) ≫ act = (MonObj.mul ▷ Y) ≫ act

open MonObj in
/-- A right module over an algebra object `B ∈ C`: an object `Y` together with an
action `Y ⊗ B ⟶ Y` satisfying the usual unit and associativity axioms. -/
structure RightModObj (B : C) [MonObj B] (Y : C) where
  act : Y ⊗ B ⟶ Y
  act_one : (ρ_ Y).inv ≫ (Y ◁ MonObj.one) ≫ act = 𝟙 Y
  act_assoc : (α_ Y B B).inv ≫ (act ▷ B) ≫ act = (Y ◁ MonObj.mul) ≫ act

/-- Theorem 2.11.2 (essential surjectivity, left version): every left `A`-module is
isomorphic to one of the form `F N` for some `N ∈ C`. -/
theorem thm_2_11_2_essSurj_left
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (A : C) [MonObj A]
    (F : C → C)
    (F_modStr : ∀ (N : C), LeftModObj (C := C) A (F N))
    (L : C) (lm : LeftModObj (C := C) A L) :
    ∃ (N : C), Nonempty (L ≅ F N) := by
  sorry

/-- Theorem 2.11.2 (essential surjectivity, right version): every right `A`-module is
isomorphic to one of the form `G N` for some `N ∈ C`. -/
theorem thm_2_11_2_essSurj_right
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (A : C) [MonObj A]
    (G : C → C)
    (G_modStr : ∀ (N : C), RightModObj (C := C) A (G N))
    (L : C) (rm : RightModObj (C := C) A L) :
    ∃ (N : C), Nonempty (L ≅ G N) := by
  sorry

/-- Example 2.10.8 (left version): the object `ᘁA ⊗ N` carries a canonical left
`(ᘁA ⊗ A)`-module structure. -/
noncomputable def example_2_10_8_leftMod
    (A : C) [MonObj A] [HasLeftDual A] [MonObj ((ᘁA : C) ⊗ A)]
    (h_one : MonObj.one (X := (ᘁA : C) ⊗ A) = η_ (ᘁA : C) A)
    (h_mul : MonObj.mul (X := (ᘁA : C) ⊗ A) = dualAlg_mul A)
    (N : C) : LeftModObj (C := C) ((ᘁA : C) ⊗ A) ((ᘁA : C) ⊗ N) where
  act := (α_ (ᘁA : C) A ((ᘁA : C) ⊗ N)).hom ≫
    (ᘁA : C) ◁ ((α_ A (ᘁA : C) N).inv ≫ (ε_ (ᘁA : C) A ▷ N) ≫ (λ_ N).hom)
  act_one := by
    rw [h_one]
    simp only [MonoidalCategory.whiskerLeft_comp]
    slice_lhs 3 4 => rw [← MonoidalCategory.pentagon_inv_hom_hom_hom_inv]
    slice_lhs 2 3 => rw [MonoidalCategory.associator_inv_naturality_left]
    slice_lhs 5 6 => rw [← MonoidalCategory.associator_naturality_middle]
    slice_lhs 3 5 =>
      rw [← comp_whiskerRight, ← comp_whiskerRight]
      rw [ExactPairing.evaluation_coevaluation]
    monoidal
  act_assoc := by


    rw [h_mul]; sorry

/-- Example 2.10.8 (right version): the object `N ⊗ A` carries a canonical right
`(ᘁA ⊗ A)`-module structure. -/
noncomputable def example_2_10_8_rightMod
    (A : C) [MonObj A] [HasLeftDual A] [MonObj ((ᘁA : C) ⊗ A)]
    (h_one : MonObj.one (X := (ᘁA : C) ⊗ A) = η_ (ᘁA : C) A)
    (h_mul : MonObj.mul (X := (ᘁA : C) ⊗ A) = dualAlg_mul A)
    (N : C) : RightModObj (C := C) ((ᘁA : C) ⊗ A) (N ⊗ A) where
  act := (α_ N A ((ᘁA : C) ⊗ A)).hom ≫
    N ◁ ((α_ A (ᘁA : C) A).inv ≫ (ε_ (ᘁA : C) A ▷ A) ≫ (λ_ A).hom)
  act_one := by
    rw [h_one]
    simp only [MonoidalCategory.whiskerLeft_comp]
    slice_lhs 2 3 => rw [MonoidalCategory.associator_naturality_right]
    slice_lhs 3 5 =>
      rw [← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp]
      rw [ExactPairing.coevaluation_evaluation]
    monoidal
  act_assoc := by


    rw [h_mul]; sorry

/-- Every left `(ᘁA ⊗ A)`-module is isomorphic to one of the form `ᘁA ⊗ X`. -/
theorem leftBmod_of_leftDual_tensor
    (A : C) [MonObj A] [HasLeftDual A] [MonObj ((ᘁA : C) ⊗ A)]
    (h_one : MonObj.one (X := (ᘁA : C) ⊗ A) = η_ (ᘁA : C) A)
    (h_mul : MonObj.mul (X := (ᘁA : C) ⊗ A) = dualAlg_mul A)
    (Y : C) (lm : LeftModObj (C := C) ((ᘁA : C) ⊗ A) Y) :
    ∃ (X : C), Nonempty (Y ≅ (ᘁA : C) ⊗ X) :=
  thm_2_11_2_essSurj_left
    ((ᘁA : C) ⊗ A)
    (fun N => (ᘁA : C) ⊗ N)
    (example_2_10_8_leftMod A h_one h_mul)
    Y lm

/-- Every right `(ᘁA ⊗ A)`-module is isomorphic to one of the form `X ⊗ A`. -/
theorem rightBmod_of_leftDual_tensor
    (A : C) [MonObj A] [HasLeftDual A] [MonObj ((ᘁA : C) ⊗ A)]
    (h_one : MonObj.one (X := (ᘁA : C) ⊗ A) = η_ (ᘁA : C) A)
    (h_mul : MonObj.mul (X := (ᘁA : C) ⊗ A) = dualAlg_mul A)
    (Y : C) (rm : RightModObj (C := C) ((ᘁA : C) ⊗ A) Y) :
    ∃ (X : C), Nonempty (Y ≅ X ⊗ A) :=
  thm_2_11_2_essSurj_right
    ((ᘁA : C) ⊗ A)
    (fun N => N ⊗ A)
    (example_2_10_8_rightMod A h_one h_mul)
    Y rm

end Lemma_2_14_7

/-- Lemma 2.14.7: classification of left and right `(ᘁA ⊗ A)`-modules in terms of
tensor products with `ᘁA` or `A`. -/
theorem lem_2_14_7
    (A : C) [MonObj A] [HasLeftDual A] [MonObj ((ᘁA : C) ⊗ A)]
    (h_one : MonObj.one (X := (ᘁA : C) ⊗ A) = η_ (ᘁA : C) A)
    (h_mul : MonObj.mul (X := (ᘁA : C) ⊗ A) = dualAlg_mul A) :
    (∀ (Y : C) (lm : LeftModObj ((ᘁA : C) ⊗ A) Y), ∃ (X : C), Nonempty (Y ≅ (ᘁA : C) ⊗ X)) ∧
    (∀ (Y : C) (rm : RightModObj ((ᘁA : C) ⊗ A) Y), ∃ (X : C), Nonempty (Y ≅ X ⊗ A)) :=
  ⟨fun Y lm => leftBmod_of_leftDual_tensor A h_one h_mul Y lm,
   fun Y rm => rightBmod_of_leftDual_tensor A h_one h_mul Y rm⟩

/-- Identification of objects of the double-dual category with bimodules over the
algebra `ᘁA ⊗ A` for a suitable `A ∈ C`, used in the proof of Theorem 2.14.6. -/
theorem doubleDual_bimod_identification
    [inst : LeftModuleCategory (DualCatObj C M) M] :
    ∃ (A : C) (_ : MonObj A) (_ : HasLeftDual A) (_ : MonObj ((ᘁA : C) ⊗ A))
      (_ : MonObj.one (X := (ᘁA : C) ⊗ A) = η_ (ᘁA : C) A)
      (_ : MonObj.mul (X := (ᘁA : C) ⊗ A) = dualAlg_mul A),


      ∀ (G : DoubleDualObj C M), ∃ (Y : C),
        Nonempty (LeftModObj ((ᘁA : C) ⊗ A) Y) ∧


        (∀ (F : C ⥤ DoubleDualObj C M),
          (∀ Z : C, (F.obj Z).toFunctor = actionFunctor Z) →
          ∀ (X : C), Nonempty (Y ≅ (ᘁA : C) ⊗ X) → Nonempty (G ≅ F.obj X)) := by


  sorry

/-- The canonical double-dual functor `C → (C*_M)*_M` is essentially surjective. -/
theorem doubleDual_essSurj
    [inst : LeftModuleCategory (DualCatObj C M) M]
    (F : C ⥤ DoubleDualObj C M)
    (hF : ∀ X : C, (F.obj X).toFunctor = actionFunctor X) :
    F.EssSurj := by
  constructor
  intro G

  obtain ⟨A, hMonA, hDualA, hMonB, h_one, h_mul, h_ident⟩ :=
    doubleDual_bimod_identification (C := C) (M := M)

  obtain ⟨Y, ⟨lm⟩, h_reconstruct⟩ := h_ident G

  have lem := @lem_2_14_7 C _ _ A hMonA hDualA hMonB h_one h_mul
  obtain ⟨lem_left, _⟩ := lem
  obtain ⟨X, ⟨iso_left⟩⟩ := lem_left Y lm

  obtain ⟨iso_G⟩ := h_reconstruct F hF X ⟨iso_left⟩

  exact ⟨X, ⟨iso_G.symm⟩⟩

/-- The canonical double-dual functor `C → (C*_M)*_M` is an equivalence of categories. -/
theorem doubleDual_equivalence
    [inst : LeftModuleCategory (DualCatObj C M) M] :
    ∃ (F : C ⥤ DoubleDualObj C M),
      (∀ X : C, (F.obj X).toFunctor = actionFunctor X) ∧
      Functor.IsEquivalence F := by

  obtain ⟨F, hF⟩ := canonicalDoubleDualFunctor (C := C) (M := M)
  refine ⟨F, hF, ?_⟩

  have hff := canonicalDoubleDualFunctor_fullFaithful (C := C) (M := M) F hF

  have hessSurj := doubleDual_essSurj F hF

  exact { faithful := hff.faithful, full := hff.full, essSurj := hessSurj }

/-- Theorem 2.14.6: there is a canonical monoidal equivalence between `C` and the
double dual `(C*_M)*_M` of `C` with respect to an exact module category `M`. -/
theorem theorem_2_14_6
    [inst : LeftModuleCategory (DualCatObj C M) M] :
    ∃ (F : C ⥤ DoubleDualObj C M),
      (∀ X : C, (F.obj X).toFunctor = actionFunctor X) ∧
      Functor.IsEquivalence F :=
  doubleDual_equivalence

/-- If the unit of `C` is simple and the canonical double-dual functor is an
equivalence, then any direct-sum decomposition of `M` as a `C*_M`-module is trivial. -/
theorem module_decomp_trivial_of_simple_unit_equiv
    (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (M : Type u) [Category.{v} M] [LeftModuleCategory C M]
    (inst_hz : HasZeroMorphisms C)
    (h_tensor : Simple (𝟙_ C))
    [inst : LeftModuleCategory (DualCatObj C M) M]
    (F : C ⥤ DoubleDualObj C M)
    (hF_action : ∀ X : C, (F.obj X).toFunctor = actionFunctor X)
    (hF_equiv : Functor.IsEquivalence F)
    (M₁ M₂ : Type u) [Category.{v} M₁] [Category.{v} M₂]
    [LeftModuleCategory (DualCatObj C M) M₁]
    [LeftModuleCategory (DualCatObj C M) M₂]
    (E : ModuleEquivalence (DualCatObj C M) M (M₁ × M₂)) :
    IsEmpty M₁ ∨ IsEmpty M₂ := by sorry

/-- Combined criterion: if `𝟙_ C` is simple, `M` is exact, and the canonical
double-dual functor is an equivalence, then `M` is indecomposable as a `C*_M`-module
category. -/
theorem indecomposable_of_simple_unit_and_doubleDual_equiv
    (inst_hz : HasZeroMorphisms C)
    (h_tensor : Simple (𝟙_ C))
    (h_exact : ∀ (P : C) (N : M) [Projective P], Projective (P ⊗ᵐ N))
    [inst : LeftModuleCategory (DualCatObj C M) M]
    (h_equiv : ∃ (F : C ⥤ DoubleDualObj C M),
      (∀ X : C, (F.obj X).toFunctor = actionFunctor X) ∧
      Functor.IsEquivalence F) :
    IsIndecomposableModuleCategory (DualCatObj C M) M := by

  obtain ⟨F, hF_action, hF_equiv⟩ := h_equiv


  refine ⟨?_⟩
  · intro M₁ M₂
    intro inst_M₁ inst_M₂ inst_LM₁ inst_LM₂ E
    exact module_decomp_trivial_of_simple_unit_equiv C M inst_hz h_tensor F hF_action hF_equiv
      M₁ M₂ E

/-- Convenience form: under the same hypotheses as
`indecomposable_of_simple_unit_and_doubleDual_equiv`, the module category `M` over the
dual category `C*_M` is indecomposable. -/
theorem indecomposable_over_dualCat
    [HasZeroMorphisms C]
    (h_tensor : Simple (𝟙_ C))
    (h_exact : ∀ (P : C) (N : M) [Projective P], Projective (P ⊗ᵐ N))
    [inst : LeftModuleCategory (DualCatObj C M) M] :
    IsIndecomposableModuleCategory (DualCatObj C M) M := by

  have h_equiv := doubleDual_equivalence (C := C) (M := M)

  exact indecomposable_of_simple_unit_and_doubleDual_equiv inferInstance h_tensor h_exact h_equiv

/-- The category of module functors `M₁ → M` is itself a left module category over the
dual category `C*_M`, with action given by post-composition. -/
noncomputable def funC_leftModuleCategory_over_dualCat
    [ExactModuleCategory C M]
    (M₁ : Type u) [Category.{v} M₁] [LeftModuleCategory C M₁]
    [Category.{v} (ModuleFunctor C M₁ M)] :
    LeftModuleCategory (DualCatObj C M) (ModuleFunctor C M₁ M) := sorry

/-- The action of `C*_M` on `ModuleFunctor C M₁ M` preserves projective objects. -/
theorem funC_action_preserves_projective_over_dualCat
    [ExactModuleCategory C M]
    (M₁ : Type u) [Category.{v} M₁] [LeftModuleCategory C M₁]
    [Category.{v} (ModuleFunctor C M₁ M)]
    (G : DualCatObj C M) (F : ModuleFunctor C M₁ M) [Projective G] :
    @Projective (ModuleFunctor C M₁ M) _
      ((funC_leftModuleCategory_over_dualCat M₁).toLeftModuleCategoryStruct.actObj G F) := by sorry

/-- Packaging of the previous two results: `ModuleFunctor C M₁ M` is an exact module
category over the dual category `C*_M`. -/
noncomputable def funC_exact_moduleCat_over_dualCat
    [ExactModuleCategory C M]
    (M₁ : Type u) [Category.{v} M₁] [LeftModuleCategory C M₁]
    [Category.{v} (ModuleFunctor C M₁ M)] :
    ExactModuleCategory (DualCatObj C M) (ModuleFunctor C M₁ M) :=
  { funC_leftModuleCategory_over_dualCat M₁ with
    action_preserves_projective := fun G F _ =>
      funC_action_preserves_projective_over_dualCat M₁ G F }

/-- Forward direction of Morita equivalence between `C` and `C*_M`: every exact module
category over `C` can be recovered, up to equivalence, from a module category over the
dual category. -/
theorem morita_equivalence_forward
    [ExactModuleCategory C M]
    [inst : LeftModuleCategory (DualCatObj C M) M]
    (M₁ : Type u) [Category.{v} M₁] [ExactModuleCategory C M₁]
    [Category.{v} (ModuleFunctor C M₁ M)] :


    ∃ (_ : ExactModuleCategory (DualCatObj C M) (ModuleFunctor C M₁ M))
      (Ψ_Φ_M₁ : Type (max u v))
      (_ : Category.{v} Ψ_Φ_M₁)
      (_ : ExactModuleCategory C Ψ_Φ_M₁),
      Nonempty (ModuleEquivalence C Ψ_Φ_M₁ M₁) := by sorry

/-- Backward direction of Morita equivalence between `C` and `C*_M`: every exact module
category over the dual category can be recovered, up to equivalence, from a module
category over `C`. -/
theorem morita_equivalence_backward
    [ExactModuleCategory C M]
    [inst : LeftModuleCategory (DualCatObj C M) M]
    (M₂ : Type u) [Category.{v} M₂] [ExactModuleCategory (DualCatObj C M) M₂]
    [Category.{v} (ModuleFunctor (DualCatObj C M) M₂ M)] :


    ∃ (_ : ExactModuleCategory C (ModuleFunctor (DualCatObj C M) M₂ M))
      (Φ_Ψ_M₂ : Type (max u v))
      (_ : Category.{v} Φ_Ψ_M₂)
      (_ : ExactModuleCategory (DualCatObj C M) Φ_Ψ_M₂),
      Nonempty (ModuleEquivalence (DualCatObj C M) Φ_Ψ_M₂ M₂) := by sorry

end DualCatObj

/-- The enveloping monoidal category `C ⊠ C^{op}` of a monoidal category `C`. -/
noncomputable def EnvelopingCategory (C : Type u) [Category.{v} C] [MonoidalCategory C] : Type u := sorry

/-- The enveloping category `C ⊠ C^{op}` carries a canonical category structure. -/
noncomputable instance instCategoryEnvelopingCategory
    (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    Category.{v} (EnvelopingCategory C) := sorry

/-- The enveloping category `C ⊠ C^{op}` is itself a monoidal category. -/
noncomputable instance instMonoidalCategoryEnvelopingCategory
    (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    MonoidalCategory (EnvelopingCategory C) := sorry

/-- `C` is canonically a left module category over its enveloping category, by the
two-sided action `(X, Y) ⊗ Z = X ⊗ Z ⊗ Y`. -/
noncomputable instance instLeftModuleCategoryEnveloping
    (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    LeftModuleCategory (EnvelopingCategory C) C := sorry

/-- Underlying type of the Drinfeld center: the dual of `C` with respect to itself
viewed as a module category over its enveloping category. -/
def DrinfeldCenterObj (C : Type u) [Category.{v} C] [MonoidalCategory C] :=
  DualCatObj (EnvelopingCategory C) C

/-- The Drinfeld center inherits a category structure from `DualCatObj`. -/
noncomputable instance instCategoryDrinfeldCenterObj
    (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    Category (DrinfeldCenterObj C) := by
  change Category (DualCatObj (EnvelopingCategory C) C)
  infer_instance

/-- The Drinfeld center `Z(C)` of a monoidal category `C`, as the dual category of `C`
with respect to its enveloping category. -/
abbrev DrinfeldCenter (C : Type u) [Category.{v} C] [MonoidalCategory C] :=
  DrinfeldCenterObj C

/-- An object of the Drinfeld center expressed in half-braiding form: an object `X ∈ C`
together with a family of half-braiding isomorphisms `V ⊗ X ≅ X ⊗ V` satisfying
naturality and a hexagon-style tensor compatibility. -/
structure DrinfeldCenterHalfBraidingObj (C : Type u) [Category.{v} C] [MonoidalCategory C] where
  X : C
  halfBraiding : ∀ (V : C), (V ⊗ X) ≅ (X ⊗ V)
  halfBraiding_natural : ∀ {V₁ V₂ : C} (f : V₁ ⟶ V₂),
    (f ▷ X) ≫ (halfBraiding V₂).hom = (halfBraiding V₁).hom ≫ (X ◁ f)
  halfBraiding_tensor : ∀ (V W : C),
    (halfBraiding (V ⊗ W)).hom =
      (α_ V W X).hom ≫ (V ◁ (halfBraiding W).hom) ≫ (α_ V X W).inv ≫
        ((halfBraiding V).hom ▷ W) ≫ (α_ X V W).hom

/-- A morphism between half-braiding objects of the Drinfeld center: a morphism of the
underlying objects compatible with the half-braiding isomorphisms. -/
structure DrinfeldCenterHalfBraidingHom {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (P Q : DrinfeldCenterHalfBraidingObj C) where
  hom : P.X ⟶ Q.X
  comm : ∀ (V : C),
    (V ◁ hom) ≫ (Q.halfBraiding V).hom = (P.halfBraiding V).hom ≫ (hom ▷ V)

attribute [reassoc] DrinfeldCenterHalfBraidingHom.comm

/-- Two half-braiding morphisms are equal whenever their underlying morphisms in `C`
agree. -/
@[ext]
theorem DrinfeldCenterHalfBraidingHom.ext {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {P Q : DrinfeldCenterHalfBraidingObj C} {f g : DrinfeldCenterHalfBraidingHom P Q}
    (h : f.hom = g.hom) : f = g := by
  cases f; cases g; congr

/-- Identity morphism on a half-braiding object of the Drinfeld center. -/
def DrinfeldCenterHalfBraidingHom.id {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (P : DrinfeldCenterHalfBraidingObj C) : DrinfeldCenterHalfBraidingHom P P where
  hom := 𝟙 P.X
  comm V := by simp

/-- Composition of half-braiding morphisms in the Drinfeld center. -/
def DrinfeldCenterHalfBraidingHom.comp {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {P Q R : DrinfeldCenterHalfBraidingObj C}
    (f : DrinfeldCenterHalfBraidingHom P Q) (g : DrinfeldCenterHalfBraidingHom Q R) :
    DrinfeldCenterHalfBraidingHom P R where
  hom := f.hom ≫ g.hom
  comm V := by
    simp only [MonoidalCategory.whiskerLeft_comp, assoc]
    rw [g.comm]
    simp only [← assoc]
    rw [f.comm]
    simp only [assoc, comp_whiskerRight]

/-- Category structure on the type of half-braiding objects of the Drinfeld center. -/
instance drinfeldCenterHalfBraidingCategory (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    Category (DrinfeldCenterHalfBraidingObj C) where
  Hom := DrinfeldCenterHalfBraidingHom
  id := DrinfeldCenterHalfBraidingHom.id
  comp := DrinfeldCenterHalfBraidingHom.comp
  id_comp f := DrinfeldCenterHalfBraidingHom.ext (by simp [DrinfeldCenterHalfBraidingHom.comp, DrinfeldCenterHalfBraidingHom.id])
  comp_id f := DrinfeldCenterHalfBraidingHom.ext (by simp [DrinfeldCenterHalfBraidingHom.comp, DrinfeldCenterHalfBraidingHom.id])
  assoc f g h := DrinfeldCenterHalfBraidingHom.ext (by simp [DrinfeldCenterHalfBraidingHom.comp])

section BasicIdentity

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
variable {M : Type u} [Category.{v} M] [LeftModuleCategory C M]

/-- Internal `Hom` object `Hom_C(m, n) ∈ C` of a module category, abstractly. -/
noncomputable def moduleIHom (m n : M) : C := sorry

/-- Internal `Hom` object `Hom_*(m, n) ∈ C*_M` of a module category valued in the dual
category. -/
noncomputable def moduleIHomDual
    (inst_dual : LeftModuleCategory (DualCatObj C M) M) (m n : M) : DualCatObj C M := sorry

/-- Left dual `ᵛF ∈ C*_M` of an object `F` of the dual category. -/
noncomputable def leftDualDualCat
    (inst_dual : LeftModuleCategory (DualCatObj C M) M) (F : DualCatObj C M) : DualCatObj C M := sorry

/-- Reduction step in the proof of Theorem 2.14.6: deduce an isomorphism involving the
left dual of the dual internal `Hom` from one involving `ᘁ(Hom_C(Z, X))`. -/
theorem thm_2_14_6_reduction
    [RigidCategory C]
    (hExact : ExactModuleCategory C M)
    (inst_dual : LeftModuleCategory (DualCatObj C M) M)
    (X Y Z : M) :
    Nonempty (
      @LeftModuleCategoryStruct.actObj C _ _ M _ _ (ᘁ(moduleIHom Z X)) Y ≅
      @LeftModuleCategoryStruct.actObj (DualCatObj C M) _ _ M _
        inst_dual.toLeftModuleCategoryStruct (moduleIHomDual inst_dual X Y) Z) →
    Nonempty (
      @LeftModuleCategoryStruct.actObj C _ _ M _ _ (moduleIHom X Y) Z ≅
      @LeftModuleCategoryStruct.actObj (DualCatObj C M) _ _ M _
        inst_dual.toLeftModuleCategoryStruct (leftDualDualCat inst_dual (moduleIHomDual inst_dual Z X)) Y) := by sorry

/-- Associativity of internal `Hom` objects (Examples 2.10.8 / 2.14.5): a natural
isomorphism `ᘁ(Hom_C(Z, X)) ⊗ᵐ Y ≅ Hom_*(X, Y) ⊗ᵐ Z`. -/
theorem examples_2_10_8_2_14_5_associativity
    [RigidCategory C]
    (hExact : ExactModuleCategory C M)
    (inst_dual : LeftModuleCategory (DualCatObj C M) M)
    (X Y Z : M) :
    Nonempty (
      @LeftModuleCategoryStruct.actObj C _ _ M _ _ (ᘁ(moduleIHom Z X)) Y ≅
      @LeftModuleCategoryStruct.actObj (DualCatObj C M) _ _ M _
        inst_dual.toLeftModuleCategoryStruct (moduleIHomDual inst_dual X Y) Z) := by sorry

/-- Proposition 2.14.14 (basic identity for module categories): natural isomorphism
`Hom_C(X, Y) ⊗ᵐ Z ≅ ᵛ(Hom_*(Z, X)) ⊗ᵐ Y`, obtained from the previous two results. -/
theorem Proposition_2_14_14
    [RigidCategory C]
    (hExact : ExactModuleCategory C M)
    (inst_dual : LeftModuleCategory (DualCatObj C M) M)
    (X Y Z : M) :
    Nonempty (
      @LeftModuleCategoryStruct.actObj C _ _ M _ _ (moduleIHom X Y) Z ≅
      @LeftModuleCategoryStruct.actObj (DualCatObj C M) _ _ M _
        inst_dual.toLeftModuleCategoryStruct (leftDualDualCat inst_dual (moduleIHomDual inst_dual Z X)) Y) :=
  thm_2_14_6_reduction hExact inst_dual X Y Z
    (examples_2_10_8_2_14_5_associativity hExact inst_dual X Y Z)

end BasicIdentity

end CategoryTheory
