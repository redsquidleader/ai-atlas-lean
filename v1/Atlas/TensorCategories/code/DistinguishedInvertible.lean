/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.CategoryTheory.Yoneda
import Atlas.TensorCategories.code.InvertibleObjects
import Atlas.TensorCategories.code.PivotalSpherical
import Atlas.TensorCategories.code.CategoricalFreeness

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category Limits TensorCategories

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]


def doubleDual (X : C) : C :=
  HasRightDual.rightDual (HasRightDual.rightDual X)


@[reducible]
noncomputable def IsInvertibleObject.ofEvalCoeval (D : C)
    (hEval : IsIso (ε_ D (HasRightDual.rightDual D)))
    (hCoeval : IsIso (η_ D (HasRightDual.rightDual D))) :
    IsInvertibleObject D where
  tensorInverse := HasRightDual.rightDual D
  compIso := @asIso _ _ _ _ (η_ D (HasRightDual.rightDual D)) hCoeval |>.symm
  invCompIso := @asIso _ _ _ _ (ε_ D (HasRightDual.rightDual D)) hEval


theorem dualOfProjectiveIsProjective
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    (P : C) [Projective P] [Projective (𝟙_ C)] :
    Projective (HasRightDual.rightDual P) where
  factors {E X} f e _ := by

    let Φ := tensorLeftHomEquiv (𝟙_ C) P (HasRightDual.rightDual P)

    let f₁ : HasRightDual.rightDual P ⊗ 𝟙_ C ⟶ X := (ρ_ _).hom ≫ f

    let f₂ : 𝟙_ C ⟶ P ⊗ X := Φ X f₁

    have adj : tensorLeft P ⊣ tensorLeft (ᘁP) := tensorLeftAdjunction (ᘁP) P
    have : PreservesColimitsOfSize.{0, 0} (tensorLeft P) :=
      adj.leftAdjoint_preservesColimits
    have : (tensorLeft P).PreservesEpimorphisms :=
      preservesEpimorphisms_of_preservesColimitsOfShape _

    have : Epi (P ◁ e) := (tensorLeft P).map_epi e

    obtain ⟨g₂, hg₂⟩ := Projective.factors f₂ (P ◁ e)


    let g₁ : HasRightDual.rightDual P ⊗ 𝟙_ C ⟶ E := (Φ E).symm g₂

    use (ρ_ _).inv ≫ g₁


    have key : g₁ ≫ e = f₁ := by
      apply (Φ X).injective
      rw [tensorLeftHomEquiv_naturality g₁ e]
      change (Φ E) g₁ ≫ P ◁ e = (Φ X) f₁
      simp only [g₁, Equiv.apply_symm_apply]
      exact hg₂
    simp only [assoc, key, f₁, Iso.inv_hom_id_assoc]


variable (C) in
/-- Data of a distinguished invertible object `L_ρ ∈ C` (Definition 1.51.4): an object
whose tensor product with every projective `P` is naturally isomorphic to `P^{**}`, and
which is fixed by the double-dual functor. -/
class HasDistinguishedInvertibleData where
  distinguished : C
  doubleDual_iso_tensor : ∀ (P : C) [Projective P],
    Nonempty (doubleDual P ≅ distinguished ⊗ P)
  doubleDual_self : Nonempty (doubleDual distinguished ≅ distinguished)


/-- The property that an object `X` has Frobenius-Perron dimension equal to one with
respect to the supplied `FPdimFunction`. -/
def HasFPdimOne {C : Type u} [Category.{v} C] [MonoidalCategory C]
    (f : FPdimFunction (C := C)) (X : C) : Prop := f.fpDim X = 1

/-- Existence of an `FPdimFunction` on `C` witnessing that the distinguished invertible
object has Frobenius-Perron dimension one. -/
noncomputable def distinguished_fpDim_one {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [RigidCategory C] [HasDistinguishedInvertibleData C] :
    Σ' (f : FPdimFunction (C := C)),
      HasFPdimOne f (HasDistinguishedInvertibleData.distinguished (C := C)) := by sorry

/-- Any object of Frobenius-Perron dimension one in a rigid monoidal category is
invertible. -/
noncomputable def fpDimOne_implies_invertible {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [RigidCategory C] (f : FPdimFunction (C := C)) (X : C) (h : HasFPdimOne f X) :
    IsInvertibleObject X := by sorry

/-- Lemma 1.51.1: in a finite tensor category, the distinguished object `L_ρ` is
invertible. -/
@[reducible]
noncomputable def lemma_1_51_1 {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    [HasDistinguishedInvertibleData C] :
    IsInvertibleObject (HasDistinguishedInvertibleData.distinguished (C := C)) :=
  let ⟨f, hf⟩ := @distinguished_fpDim_one C _ _ _ _
  fpDimOne_implies_invertible f _ hf

/-- Bundled data of a distinguished invertible object: an invertible object whose tensor
product with every projective is naturally isomorphic to its double dual and which is
fixed by the double-dual functor. -/
structure DistinguishedInvertibleData (C : Type u) [Category.{v} C] [MonoidalCategory C]
    [RigidCategory C] where
  obj : C
  invertible : IsInvertibleObject obj
  doubleDual_tensor : ∀ (P : C) [Projective P], Nonempty (doubleDual P ≅ obj ⊗ P)
  doubleDual_self : Nonempty (doubleDual obj ≅ obj)

/-- Package the `HasDistinguishedInvertibleData` instance into the bundled
`DistinguishedInvertibleData` structure. -/
noncomputable def distinguishedInvertibleExists
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    [HasDistinguishedInvertibleData C] :
    DistinguishedInvertibleData C :=
  { obj := HasDistinguishedInvertibleData.distinguished,
    invertible := lemma_1_51_1,
    doubleDual_tensor := HasDistinguishedInvertibleData.doubleDual_iso_tensor,
    doubleDual_self := HasDistinguishedInvertibleData.doubleDual_self }


variable (C) in
/-- Data needed to extend a pivotal-style structure from projective objects to all of `C`:
a way to extend a natural isomorphism `P ≅ P^{**}` (for projective `P`) to all objects,
together with the required naturality, monoidality, and unit-trace conditions. -/
class HasDoubleDualExtension where
  extend_pivotalIso :
    (∀ (P : C) [Projective P], Nonempty (doubleDual P ≅ P)) →
    (∀ (X : C), X ≅ (Xᘁ)ᘁ)
  extend_pivotalIso_natural :
    ∀ (hProj : ∀ (P : C) [Projective P], Nonempty (doubleDual P ≅ P))
      {V W : C} (f : V ⟶ W),
    f ≫ (extend_pivotalIso hProj W).hom =
      (extend_pivotalIso hProj V).hom ≫ (fᘁ)ᘁ
  extend_tensorCoherenceIso :
    (∀ (P : C) [Projective P], Nonempty (doubleDual P ≅ P)) →
    (∀ (V W : C), (Vᘁ)ᘁ ⊗ (Wᘁ)ᘁ ≅ ((V ⊗ W : C)ᘁ : C)ᘁ)
  extend_monoidality :
    ∀ (hProj : ∀ (P : C) [Projective P], Nonempty (doubleDual P ≅ P))
      (V W : C),
    (extend_pivotalIso hProj (V ⊗ W)).hom =
      ((extend_pivotalIso hProj V).hom ⊗ₘ (extend_pivotalIso hProj W).hom) ≫
        (extend_tensorCoherenceIso hProj V W).hom
  extend_dimUnit :
    ∀ (hProj : ∀ (P : C) [Projective P], Nonempty (doubleDual P ≅ P)),
    TensorCategories.leftQuantumTrace C (extend_pivotalIso hProj (𝟙_ C)).hom = 𝟙 (𝟙_ C)

/-- Construct a `HasDoubleDualExtension` instance from a canonical choice of pivotal-style
data already defined on all objects of `C`. -/
@[reducible] noncomputable def hasDoubleDualExtensionOfCanonical
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    (j : ∀ (X : C), X ≅ (Xᘁ)ᘁ)
    (j_nat : ∀ {V W : C} (f : V ⟶ W), f ≫ (j W).hom = (j V).hom ≫ (fᘁ)ᘁ)
    (tc : ∀ (V W : C), (Vᘁ)ᘁ ⊗ (Wᘁ)ᘁ ≅ ((V ⊗ W : C)ᘁ : C)ᘁ)
    (j_mon : ∀ (V W : C), (j (V ⊗ W)).hom = ((j V).hom ⊗ₘ (j W).hom) ≫ (tc V W).hom)
    (j_dimUnit : TensorCategories.leftQuantumTrace C (j (𝟙_ C)).hom = 𝟙 (𝟙_ C))
    : HasDoubleDualExtension C where
  extend_pivotalIso _ := j
  extend_pivotalIso_natural _ := j_nat
  extend_tensorCoherenceIso _ := tc
  extend_monoidality _ := j_mon
  extend_dimUnit _ := j_dimUnit

/-- Every pivotal category admits a `HasDoubleDualExtension` instance, given by the
ambient pivotal data. -/
noncomputable instance hasDoubleDualExtension_of_pivotal
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    [PivotalCategory C] : HasDoubleDualExtension C :=
  hasDoubleDualExtensionOfCanonical
    PivotalCategory.pivotalIso
    PivotalCategory.naturality
    PivotalCategory.tensorCoherenceIso
    PivotalCategory.monoidality
    PivotalCategory.dimUnit


/-- Build a pivotal structure on `C` from a family of double-dual isomorphisms on
projective objects together with a `HasDoubleDualExtension` instance. -/
@[reducible] noncomputable def pivotalFromProjectiveDoubleDual
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    [HasDoubleDualExtension C]
    (hDoubleDual : ∀ (P : C) [Projective P], Nonempty (doubleDual P ≅ P)) :
    PivotalCategory C where
  pivotalIso := HasDoubleDualExtension.extend_pivotalIso hDoubleDual
  tensorCoherenceIso := HasDoubleDualExtension.extend_tensorCoherenceIso hDoubleDual
  naturality := HasDoubleDualExtension.extend_pivotalIso_natural hDoubleDual
  monoidality := HasDoubleDualExtension.extend_monoidality hDoubleDual
  dimUnit := HasDoubleDualExtension.extend_dimUnit hDoubleDual

/-- If an invertible object `D` satisfies `D ⊗ P ≅ 𝟙_C ⊗ P` for every projective `P`
(and the unit is projective), then `D` is isomorphic to the unit. -/
theorem tensorIdentityOnProjectives
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    (D : C) (_hInv : IsInvertibleObject D)
    (h : ∀ (P : C) [Projective P], Nonempty (D ⊗ P ≅ (𝟙_ C) ⊗ P))
    [Projective (𝟙_ C)] :
    Nonempty (D ≅ 𝟙_ C) := by
  obtain ⟨φ⟩ := h (𝟙_ C)
  exact ⟨(ρ_ D).symm.trans (φ.trans (λ_ (𝟙_ C)))⟩

/-- If the distinguished invertible object is isomorphic to the unit, then `C` admits a
pivotal structure: this is the "easy" direction of the distinguished/pivotal equivalence. -/
@[reducible] noncomputable def pivotalOfDistinguishedIsoUnit
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    [HasDoubleDualExtension C]
    {D : C} (_hInv : IsInvertibleObject D)
    (hDoubleDual : ∀ (P : C) [Projective P], Nonempty (doubleDual P ≅ D ⊗ P))
    (hIso : D ≅ 𝟙_ C) :
    PivotalCategory C :=
  pivotalFromProjectiveDoubleDual (fun P _ => by
    obtain ⟨φ⟩ := hDoubleDual P
    exact ⟨φ.trans ((tensorIso hIso (Iso.refl P)).trans (λ_ P))⟩)

/-- Conversely, in any pivotal category the distinguished invertible object is
isomorphic to the unit. -/
theorem distinguishedIsoUnitOfPivotal
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    {D : C} (hInv : IsInvertibleObject D)
    (hDoubleDual : ∀ (P : C) [Projective P], Nonempty (doubleDual P ≅ D ⊗ P))
    (hPiv : PivotalCategory C)
    [Projective (𝟙_ C)] :
    Nonempty (D ≅ 𝟙_ C) :=
  tensorIdentityOnProjectives D hInv (fun P _ => by
    obtain ⟨φ⟩ := hDoubleDual P
    exact ⟨φ.symm.trans ((hPiv.pivotalIso P).symm.trans (λ_ P).symm)⟩)


noncomputable section

namespace HasDistinguishedInvertible

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
  [HasDistinguishedInvertibleData C]

/-- The distinguished invertible object `D = L_ρ` of `C` (Definition 1.51.4). -/
def D (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    [HasDistinguishedInvertibleData C] : C :=
  (distinguishedInvertibleExists C).obj

/-- The distinguished invertible object is invertible. -/
@[reducible]
def D_invertible : IsInvertibleObject (D C) :=
  (distinguishedInvertibleExists C).invertible

/-- Lemma 1.51.1, packaged as a `Nonempty` witness. -/
theorem Lemma_1_51_1_D_invertible :
    Nonempty (IsInvertibleObject (D C)) :=
  ⟨D_invertible⟩

/-- The right-cancellation isomorphism `D ⊗ D⁻¹ ≅ 𝟙_C` of the invertible object `D`. -/
def D_compIso : (D C) ⊗ (D_invertible (C := C)).tensorInverse ≅ 𝟙_ C :=
  (D_invertible (C := C)).compIso

/-- The left-cancellation isomorphism `D⁻¹ ⊗ D ≅ 𝟙_C` of the invertible object `D`. -/
def D_invCompIso : (D_invertible (C := C)).tensorInverse ⊗ (D C) ≅ 𝟙_ C :=
  (D_invertible (C := C)).invCompIso

/-- The natural double-dual isomorphism `P^{**} ≅ D ⊗ P` for projective `P`. -/
def doubleDualIsoProj (P : C) [Projective P] :
    doubleDual P ≅ D C ⊗ P :=
  ((distinguishedInvertibleExists C).doubleDual_tensor P).some

/-- The double dual of `D` is isomorphic to `D` itself. -/
def D_selfDualIso : doubleDual (D C) ≅ D C :=
  (distinguishedInvertibleExists C).doubleDual_self.some

/-- Yoneda-level natural isomorphism between `Hom(-, P^*)` and `Hom(-, P ⊗ D)` for
projective `P`, used to deduce Lemma 1.51.2. -/
noncomputable def homSpaceNatIso_proj (P : C) [Projective P] :
    yoneda.obj (HasRightDual.rightDual P) ≅ yoneda.obj (P ⊗ D C) := by
  sorry

/-- For projective `P`, the right dual `P^*` is isomorphic to `P ⊗ D`. -/
theorem dualIsoTensorD (P : C) [Projective P] :
    Nonempty (HasRightDual.rightDual P ≅ P ⊗ D C) :=
  ⟨Yoneda.fullyFaithful.preimageIso (homSpaceNatIso_proj P)⟩

/-- Lemma 1.51.2 for projective objects: `P^* ≅ P ⊗ D` for any projective `P`. -/
theorem Lemma_1_51_2_projective (P : C) [Projective P] :
    Nonempty (HasRightDual.rightDual P ≅ P ⊗ D C) :=
  dualIsoTensorD P

/-- Compatibility of right duals with tensor products: `(X ⊗ Y)^* ≅ Y^* ⊗ X^*`. -/
theorem rightDualTensorIso : ∀ (X Y : C),
    Nonempty (HasRightDual.rightDual (X ⊗ Y) ≅
      HasRightDual.rightDual Y ⊗ HasRightDual.rightDual X) := by
  intro X Y
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

/-- Corollary 1.51.3 (projective case): the double dual of a projective `P` is
isomorphic to `D^* ⊗ P ⊗ D`. -/
theorem doubleDualIsoSandwich (P : C) [Projective P] :
    Nonempty (doubleDual P ≅ HasRightDual.rightDual (D C) ⊗ P ⊗ D C) := by
  unfold doubleDual

  obtain ⟨φ₁⟩ := dualIsoTensorD P

  obtain ⟨φ₂⟩ := rightDualTensorIso P (D C)

  obtain ⟨φ₃⟩ := dualIsoTensorD P

  letI : ExactPairing (HasRightDual.rightDual P) (doubleDual P) :=
    HasRightDual.exact
  letI ep₂ : ExactPairing (P ⊗ D C) (doubleDual P) :=
    exactPairingCongrLeft φ₁.symm
  letI ep₃ : ExactPairing (P ⊗ D C) (HasRightDual.rightDual (P ⊗ D C)) :=
    HasRightDual.exact
  let ψ₁ : doubleDual P ≅ HasRightDual.rightDual (P ⊗ D C) :=
    rightDualIso ep₂ ep₃

  let ψ₂ := φ₂

  let ψ₃ : HasRightDual.rightDual (D C) ⊗ HasRightDual.rightDual P ≅
    HasRightDual.rightDual (D C) ⊗ (P ⊗ D C) :=
    tensorIso (Iso.refl _) φ₃
  exact ⟨ψ₁.trans (ψ₂.trans ψ₃)⟩

/-- Corollary 1.51.3 (projective version, named form): the double dual of a projective
`P` decomposes as `D^* ⊗ P ⊗ D`. -/
theorem Corollary_1_51_3_projective (P : C) [Projective P] :
    Nonempty (doubleDual P ≅ HasRightDual.rightDual (D C) ⊗ P ⊗ D C) :=
  doubleDualIsoSandwich P

/-- Yoneda-level natural isomorphism between `Hom(-, L^*)` and `Hom(-, L ⊗ D)` for
simple `L`, used to deduce the simple version of Lemma 1.51.2. -/
noncomputable def homSpaceNatIso_simple [Limits.HasZeroMorphisms C] :
    ∀ (L : C) [Simple L],
    yoneda.obj (HasRightDual.rightDual L) ≅ yoneda.obj (L ⊗ D C) := by
  intro L _
  sorry

/-- For simple `L`, the right dual `L^*` is isomorphic to `L ⊗ D`. -/
theorem simpleIsoTensorD [Limits.HasZeroMorphisms C] (L : C) [Simple L] :
    Nonempty (HasRightDual.rightDual L ≅ L ⊗ D C) :=
  ⟨Yoneda.fullyFaithful.preimageIso (homSpaceNatIso_simple L)⟩

/-- Lemma 1.51.2 for simple objects: `L^* ≅ L ⊗ D` for any simple `L`. -/
theorem Lemma_1_51_2_simple [Limits.HasZeroMorphisms C] (L : C) [Simple L] :
    Nonempty (HasRightDual.rightDual L ≅ L ⊗ D C) :=
  simpleIsoTensorD L

/-- Corollary 1.51.3 (simple case): the double dual of a simple `L` is isomorphic to
`D^* ⊗ L ⊗ D`. -/
theorem doubleDualIsoSandwichSimple [Limits.HasZeroMorphisms C] (L : C) [Simple L] :
    Nonempty (doubleDual L ≅ HasRightDual.rightDual (D C) ⊗ L ⊗ D C) := by
  unfold doubleDual

  obtain ⟨φ₁⟩ := simpleIsoTensorD L

  obtain ⟨φ₂⟩ := rightDualTensorIso L (D C)

  obtain ⟨φ₃⟩ := simpleIsoTensorD L

  letI : ExactPairing (HasRightDual.rightDual L) (doubleDual L) :=
    HasRightDual.exact
  letI ep₂ : ExactPairing (L ⊗ D C) (doubleDual L) :=
    exactPairingCongrLeft φ₁.symm
  letI ep₃ : ExactPairing (L ⊗ D C) (HasRightDual.rightDual (L ⊗ D C)) :=
    HasRightDual.exact
  let ψ₁ : doubleDual L ≅ HasRightDual.rightDual (L ⊗ D C) :=
    rightDualIso ep₂ ep₃

  let ψ₂ := φ₂

  let ψ₃ : HasRightDual.rightDual (D C) ⊗ HasRightDual.rightDual L ≅
    HasRightDual.rightDual (D C) ⊗ (L ⊗ D C) :=
    tensorIso (Iso.refl _) φ₃
  exact ⟨ψ₁.trans (ψ₂.trans ψ₃)⟩

/-- Corollary 1.51.3 (simple version, named form): the double dual of a simple `L`
decomposes as `D^* ⊗ L ⊗ D`. -/
theorem Corollary_1_51_3_simple [Limits.HasZeroMorphisms C] (L : C) [Simple L] :
    Nonempty (doubleDual L ≅ HasRightDual.rightDual (D C) ⊗ L ⊗ D C) :=
  doubleDualIsoSandwichSimple L

/-- Corollary 1.51.3: for every projective and every simple object `X`, the double dual
`X^{**}` is naturally isomorphic to `D^* ⊗ X ⊗ D`. -/
theorem Corollary_1_51_3 [Limits.HasZeroMorphisms C] :
    (∀ (P : C) [Projective P],
      Nonempty (doubleDual P ≅ HasRightDual.rightDual (D C) ⊗ P ⊗ D C)) ∧
    (∀ (L : C) [Simple L],
      Nonempty (doubleDual L ≅ HasRightDual.rightDual (D C) ⊗ L ⊗ D C)) :=
  ⟨fun P _ => Corollary_1_51_3_projective P,
   fun L _ => Corollary_1_51_3_simple L⟩

end HasDistinguishedInvertible


open scoped TensorProduct in
/-- A quasi-Hopf algebra over `k`: an algebra `H` equipped with a coproduct, counit, an
invertible associator `Φ`, an antipode together with elements `α, β ∈ H`, and a left
`H`-module structure on the linear dual `H^*`. -/
class IsQuasiHopfAlgebra (k : Type*) (H : Type*) [Field k] [Ring H] [Algebra k H] where
  comul : H →ₐ[k] H ⊗[k] H
  counit : H →ₐ[k] k
  rTensor_counit_comp_comul :
    counit.toLinearMap.rTensor H ∘ₗ comul.toLinearMap = (TensorProduct.mk k k H) 1
  lTensor_counit_comp_comul :
    counit.toLinearMap.lTensor H ∘ₗ comul.toLinearMap = (TensorProduct.mk k H k).flip 1
  Φ : H ⊗[k] H ⊗[k] H
  Φ_invertible : ∃ Ψ : H ⊗[k] H ⊗[k] H, Φ * Ψ = 1 ∧ Ψ * Φ = 1
  antipode : H ≃ₗ[k] H
  antipode_anti_mul : ∀ x y : H, antipode (x * y) = antipode y * antipode x
  antipode_one : antipode 1 = 1
  α : H
  β : H
  leftModuleDual : Module H (Module.Dual k H)

/-- The property of being a quasi-Frobenius algebra (placeholder predicate used in the
proof of Corollary 1.51.5). -/
def IsQuasiFrobeniusAlgebra
    (k : Type*) [Field k]
    (H : Type*) [Ring H] [Algebra k H] [Module.Finite k H] : Prop := sorry

/-- The property that the dimensions of the socle and cosocle of `H` match, a numerical
criterion used in the proof of Corollary 1.51.5. -/
def HasSocleCosocleDimMatch
    (k : Type*) [Field k]
    (H : Type*) [Ring H] [Algebra k H] [Module.Finite k H] : Prop := sorry

/-- Every quasi-Hopf algebra is quasi-Frobenius. -/
theorem quasiHopf_isQuasiFrobenius
    (k : Type*) [Field k]
    (H : Type*) [Ring H] [Algebra k H] [Module.Finite k H]
    (hQH : IsQuasiHopfAlgebra k H) :
    IsQuasiFrobeniusAlgebra k H := by sorry

/-- Every quasi-Hopf algebra has matching socle and cosocle dimensions. -/
theorem quasiHopf_hasSocleCosocleDimMatch
    (k : Type*) [Field k]
    (H : Type*) [Ring H] [Algebra k H] [Module.Finite k H]
    (hQH : IsQuasiHopfAlgebra k H) :
    HasSocleCosocleDimMatch k H := by sorry

/-- A quasi-Frobenius quasi-Hopf algebra whose socle and cosocle dimensions match is in
fact Frobenius. -/
theorem quasiFrobenius_dimMatch_imp_frobenius
    (k : Type*) [Field k]
    (H : Type*) [Ring H] [Algebra k H] [Module.Finite k H]
    (hQH : IsQuasiHopfAlgebra k H)
    (hQF : IsQuasiFrobeniusAlgebra k H)
    (hDM : HasSocleCosocleDimMatch k H) :
    letI : Module H (Module.Dual k H) := hQH.leftModuleDual
    Nonempty (H ≃ₗ[H] Module.Dual k H) := by sorry

/-- Combining the previous lemmas: every quasi-Hopf algebra is Frobenius. -/
theorem quasiHopfAlgebraIsFrobenius
    (k : Type*) [Field k]
    (H : Type*) [Ring H] [Algebra k H] [Module.Finite k H]
    [hQH : IsQuasiHopfAlgebra k H] :
    letI : Module H (Module.Dual k H) := hQH.leftModuleDual
    Nonempty (H ≃ₗ[H] Module.Dual k H) := by

  have hQF : IsQuasiFrobeniusAlgebra k H := quasiHopf_isQuasiFrobenius k H hQH

  have hDM : HasSocleCosocleDimMatch k H := quasiHopf_hasSocleCosocleDimMatch k H hQH

  exact quasiFrobenius_dimMatch_imp_frobenius k H hQH hQF hDM

/-- Corollary 1.51.5: any finite-dimensional quasi-Hopf algebra is a Frobenius algebra,
i.e. `H` is isomorphic to its linear dual as a left `H`-module. -/
theorem Corollary_1_51_5
    (k : Type*) [Field k]
    (H : Type*) [Ring H] [Algebra k H] [Module.Finite k H]
    [hQH : IsQuasiHopfAlgebra k H] :
    letI : Module H (Module.Dual k H) := hQH.leftModuleDual
    Nonempty (H ≃ₗ[H] Module.Dual k H) :=
  quasiHopfAlgebraIsFrobenius k H


namespace DistinguishedInvertiblePivotalEquiv

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
  [HasDistinguishedInvertibleData C] [HasDoubleDualExtension C] [Projective (𝟙_ C)]

/-- The distinguished invertible object `D` is isomorphic to the unit if and only if `C`
admits a pivotal structure. -/
theorem D_iso_unit_iff_pivotal :
    Nonempty (HasDistinguishedInvertible.D C ≅ (𝟙_ C : C)) ↔
    Nonempty (PivotalCategory C) := by
  constructor
  · rintro ⟨iso⟩
    exact ⟨pivotalOfDistinguishedIsoUnit
      HasDistinguishedInvertible.D_invertible
      (fun P _ => (distinguishedInvertibleExists C).doubleDual_tensor P)
      iso⟩
  · rintro ⟨piv⟩
    exact distinguishedIsoUnitOfPivotal
      HasDistinguishedInvertible.D_invertible
      (fun P _ => (distinguishedInvertibleExists C).doubleDual_tensor P)
      piv

end DistinguishedInvertiblePivotalEquiv

end


/-- The monoidal unit `𝟙_C` is always an invertible object, with both inverses given by
the unit isomorphisms. -/
@[reducible]
def unitIsInvertibleObject
    (C : Type u) [Category.{v} C] [MonoidalCategory C] :
    IsInvertibleObject (𝟙_ C) where
  tensorInverse := 𝟙_ C
  compIso := λ_ (𝟙_ C)
  invCompIso := λ_ (𝟙_ C)

/-- Any pivotal category carries a `HasDistinguishedInvertibleData` instance whose
distinguished invertible object is the monoidal unit. -/
instance hasDistinguishedInvertibleDataOfPivotal
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    [piv : PivotalCategory C] :
    HasDistinguishedInvertibleData C where
  distinguished := 𝟙_ C
  doubleDual_iso_tensor := fun P _ =>
    ⟨(piv.pivotalIso P).symm.trans (λ_ P).symm⟩
  doubleDual_self := ⟨(piv.pivotalIso (𝟙_ C)).symm⟩

end CategoryTheory
