/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ArithmeticGeometry.code.CurveTheory

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace ArithmeticGeometry

namespace Thm19_2

variable (k : Type u) [Field k] [PerfectField k]

structure FunctionFieldCat where
  carrier : Type u
  [fieldInst : Field carrier]
  [algInst : Algebra k carrier]
  finitelyGenerated : (⊤ : IntermediateField k carrier).FG
  transcendenceDegreeOne : ∃ (x : carrier), Transcendental k x ∧
    Algebra.IsAlgebraic (IntermediateField.adjoin k {x}) carrier
  algClosedInF : ∀ (x : carrier), IsAlgebraic k x → x ∈ Set.range (algebraMap k carrier)

attribute [instance] FunctionFieldCat.fieldInst FunctionFieldCat.algInst

instance : CoeSort (FunctionFieldCat k) (Type u) := ⟨FunctionFieldCat.carrier⟩

@[ext]
structure FunctionFieldCat.Hom (F₁ F₂ : FunctionFieldCat k) where
  toAlgHom : F₁.carrier →ₐ[k] F₂.carrier

instance : Category (FunctionFieldCat k) where
  Hom F₁ F₂ := FunctionFieldCat.Hom k F₁ F₂
  id F := ⟨AlgHom.id k F.carrier⟩
  comp f g := ⟨g.toAlgHom.comp f.toAlgHom⟩

structure SmProjCurve where
  toScheme : Scheme.{u}
  structureMorphism : toScheme ⟶ Spec (.of k)
  [isIntegral : IsIntegral toScheme]
  [isProper : IsProper structureMorphism]
  [isSmooth : SmoothOfRelativeDimension 1 structureMorphism]

attribute [instance] SmProjCurve.isIntegral SmProjCurve.isProper SmProjCurve.isSmooth

@[ext]
structure SmProjCurve.Hom (C₁ C₂ : SmProjCurve k) where
  toSchemeHom : C₁.toScheme ⟶ C₂.toScheme
  over_spec : toSchemeHom ≫ C₂.structureMorphism = C₁.structureMorphism

instance SmProjCurve.categoryInstance : Category (SmProjCurve k) where
  Hom C₁ C₂ := SmProjCurve.Hom k C₁ C₂
  id C := ⟨𝟙 C.toScheme, by simp⟩
  comp f g := ⟨f.toSchemeHom ≫ g.toSchemeHom, by
    rw [Category.assoc, g.over_spec, f.over_spec]⟩
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp [Category.assoc]

def SmProjCurve.algebraMapHom (C : SmProjCurve k) :
    CommRingCat.of k ⟶ C.toScheme.functionField := by
  haveI : IrreducibleSpace C.toScheme := irreducibleSpace_of_isIntegral C.toScheme
  haveI : Nonempty C.toScheme := IsIntegral.nonempty
  haveI : Nonempty (⊤ : C.toScheme.Opens) := ⟨⟨IsIntegral.nonempty.some, trivial⟩⟩
  exact (Scheme.ΓSpecIso (.of k)).inv ≫ C.structureMorphism.appTop ≫
    C.toScheme.germToFunctionField ⊤

instance SmProjCurve.algebraFunctionField (C : SmProjCurve k) :
    Algebra k C.toScheme.functionField :=
  (C.algebraMapHom k).hom.toAlgebra

theorem SmProjCurve.funField_finitelyGenerated (C : SmProjCurve k) :
    (⊤ : IntermediateField k C.toScheme.functionField).FG := by sorry

theorem SmProjCurve.funField_transcendenceDegreeOne (C : SmProjCurve k) :
    ∃ (x : C.toScheme.functionField), Transcendental k x ∧
      Algebra.IsAlgebraic (IntermediateField.adjoin k {x}) C.toScheme.functionField := by sorry

theorem SmProjCurve.funField_algClosedInF (C : SmProjCurve k) :
    ∀ (x : C.toScheme.functionField),
      IsAlgebraic k x → x ∈ Set.range (algebraMap k C.toScheme.functionField) := by sorry

def SmProjCurve.toFunctionFieldCat (C : SmProjCurve k) : FunctionFieldCat k where
  carrier := C.toScheme.functionField
  finitelyGenerated := C.funField_finitelyGenerated k
  transcendenceDegreeOne := C.funField_transcendenceDegreeOne k
  algClosedInF := C.funField_algClosedInF k

theorem SmProjCurve.Hom.map_genericPoint {C₁ C₂ : SmProjCurve k}
    (f : C₁ ⟶ C₂) :
    f.toSchemeHom (genericPoint C₁.toScheme) = genericPoint C₂.toScheme := by sorry

theorem SmProjCurve.Hom.pullback_algebraMap_commutes {C₁ C₂ : SmProjCurve k}
    (f : C₁ ⟶ C₂) (r : k) :
    let _ := irreducibleSpace_of_isIntegral C₁.toScheme
    let _ := irreducibleSpace_of_isIntegral C₂.toScheme
    ((C₂.toScheme.presheaf.stalkCongr
      (.of_eq (SmProjCurve.Hom.map_genericPoint k f).symm)).hom ≫
      f.toSchemeHom.stalkMap (genericPoint C₁.toScheme)).hom
        (algebraMap k (C₂.toFunctionFieldCat k).carrier r) =
      algebraMap k (C₁.toFunctionFieldCat k).carrier r := by

  letI : IrreducibleSpace C₁.toScheme := irreducibleSpace_of_isIntegral C₁.toScheme
  letI : IrreducibleSpace C₂.toScheme := irreducibleSpace_of_isIntegral C₂.toScheme
  haveI : Nonempty C₁.toScheme := IsIntegral.nonempty
  haveI : Nonempty C₂.toScheme := IsIntegral.nonempty
  haveI : Nonempty (⊤ : C₁.toScheme.Opens) := ⟨⟨IsIntegral.nonempty.some, trivial⟩⟩
  haveI : Nonempty (⊤ : C₂.toScheme.Opens) := ⟨⟨IsIntegral.nonempty.some, trivial⟩⟩


  have hdiag : C₂.toScheme.germToFunctionField ⊤ ≫
      (C₂.toScheme.presheaf.stalkCongr (.of_eq (map_genericPoint k f).symm)).hom ≫
      f.toSchemeHom.stalkMap (genericPoint C₁.toScheme) =
      f.toSchemeHom.appTop ≫ C₁.toScheme.germToFunctionField ⊤ := by
    unfold Scheme.germToFunctionField
    rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.germ_stalkSpecializes_assoc,
        Scheme.Hom.germ_stalkMap]
    congr 1

  have happ : C₂.structureMorphism.appTop ≫ f.toSchemeHom.appTop =
      C₁.structureMorphism.appTop := by
    have h : (f.toSchemeHom ≫ C₂.structureMorphism).appTop = C₁.structureMorphism.appTop := by
      rw [f.over_spec]
    rw [← h]; simp [Scheme.Hom.appTop]


  show ((C₂.toScheme.germToFunctionField ⊤ ≫
      (C₂.toScheme.presheaf.stalkCongr (.of_eq (map_genericPoint k f).symm)).hom ≫
      f.toSchemeHom.stalkMap (genericPoint C₁.toScheme)).hom
      (((Scheme.ΓSpecIso (.of k)).inv ≫ C₂.structureMorphism.appTop).hom r)) =
    ((Scheme.ΓSpecIso (.of k)).inv ≫ C₁.structureMorphism.appTop ≫
      C₁.toScheme.germToFunctionField ⊤).hom r
  rw [hdiag]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  congr 1
  have := congr_arg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of k)).inv.hom r)) happ
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
  exact this

def SmProjCurve.Hom.pullbackAlgHom {C₁ C₂ : SmProjCurve k}
    (f : C₁ ⟶ C₂) : (C₂.toFunctionFieldCat k) ⟶ (C₁.toFunctionFieldCat k) := by
  haveI := irreducibleSpace_of_isIntegral C₁.toScheme
  haveI := irreducibleSpace_of_isIntegral C₂.toScheme
  exact ⟨AlgHom.mk
    ((C₂.toScheme.presheaf.stalkCongr
      (.of_eq (SmProjCurve.Hom.map_genericPoint k f).symm)).hom ≫
      f.toSchemeHom.stalkMap (genericPoint C₁.toScheme)).hom
    (SmProjCurve.Hom.pullback_algebraMap_commutes k f)⟩

theorem SmProjCurve.Hom.pullbackAlgHom_id (C : SmProjCurve k) :
    SmProjCurve.Hom.pullbackAlgHom k (𝟙 C) = 𝟙 (C.toFunctionFieldCat k) := by

  have hmor : (C.toScheme.presheaf.stalkCongr
      (.of_eq (map_genericPoint k (𝟙 C)).symm)).hom ≫
      Scheme.Hom.stalkMap (𝟙 C.toScheme) (genericPoint C.toScheme) =
      𝟙 (C.toScheme.presheaf.stalk (genericPoint C.toScheme)) := by
    rw [TopCat.Presheaf.stalkCongr_hom, Scheme.Hom.stalkMap_id]
    erw [Category.comp_id]
    convert TopCat.Presheaf.stalkSpecializes_refl C.toScheme.presheaf (genericPoint C.toScheme)
  apply FunctionFieldCat.Hom.ext
  apply AlgHom.ext
  intro x
  show (pullbackAlgHom k (𝟙 C)).toAlgHom x = x

  show ((C.toScheme.presheaf.stalkCongr
      (.of_eq (map_genericPoint k (𝟙 C)).symm)).hom ≫
      Scheme.Hom.stalkMap (𝟙 C.toScheme) (genericPoint C.toScheme)).hom x = x
  rw [hmor]; rfl

theorem SmProjCurve.Hom.pullbackAlgHom_comp {C₁ C₂ C₃ : SmProjCurve k}
    (f : C₁ ⟶ C₂) (g : C₂ ⟶ C₃) :
    SmProjCurve.Hom.pullbackAlgHom k (f ≫ g) =
    SmProjCurve.Hom.pullbackAlgHom k g ≫ SmProjCurve.Hom.pullbackAlgHom k f := by
  apply FunctionFieldCat.Hom.ext
  apply AlgHom.ext
  intro x

  let ηX := genericPoint C₁.toScheme
  let ηY := genericPoint C₂.toScheme
  let ηZ := genericPoint C₃.toScheme


  have decomp := Scheme.Hom.stalkMap_comp f.toSchemeHom g.toSchemeHom ηX


  have hmor : (C₃.toScheme.presheaf.stalkCongr
      (.of_eq (map_genericPoint k (f ≫ g)).symm)).hom ≫
      Scheme.Hom.stalkMap (f.toSchemeHom ≫ g.toSchemeHom) ηX =
    ((C₃.toScheme.presheaf.stalkCongr (.of_eq (map_genericPoint k g).symm)).hom ≫
      g.toSchemeHom.stalkMap ηY) ≫
    ((C₂.toScheme.presheaf.stalkCongr (.of_eq (map_genericPoint k f).symm)).hom ≫
      f.toSchemeHom.stalkMap ηX) := by
    rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkCongr_hom]
    rw [decomp]
    simp only [Category.assoc]

    rw [← Scheme.Hom.stalkSpecializes_stalkMap_assoc g.toSchemeHom (f.toSchemeHom ηX) ηY]


    rw [← Category.assoc (C₃.toScheme.presheaf.stalkSpecializes _)
      (C₃.toScheme.presheaf.stalkSpecializes _)]
    erw [TopCat.Presheaf.stalkSpecializes_comp]
    congr 1

  show ((C₃.toScheme.presheaf.stalkCongr
      (.of_eq (map_genericPoint k (f ≫ g)).symm)).hom ≫
      Scheme.Hom.stalkMap (f.toSchemeHom ≫ g.toSchemeHom) ηX).hom x =
    ((C₂.toScheme.presheaf.stalkCongr (.of_eq (map_genericPoint k f).symm)).hom ≫
      f.toSchemeHom.stalkMap ηX).hom
    (((C₃.toScheme.presheaf.stalkCongr (.of_eq (map_genericPoint k g).symm)).hom ≫
      g.toSchemeHom.stalkMap ηY).hom x)
  rw [hmor]; rfl

def functionFieldFunctor : (SmProjCurve k)ᵒᵖ ⥤ FunctionFieldCat k where
  obj C := C.unop.toFunctionFieldCat k
  map {C₁ C₂} f := SmProjCurve.Hom.pullbackAlgHom k f.unop
  map_id C := SmProjCurve.Hom.pullbackAlgHom_id k C.unop
  map_comp {X Y Z} f g := by

    show SmProjCurve.Hom.pullbackAlgHom k (f ≫ g).unop =
      SmProjCurve.Hom.pullbackAlgHom k f.unop ≫ SmProjCurve.Hom.pullbackAlgHom k g.unop
    change SmProjCurve.Hom.pullbackAlgHom k (g.unop ≫ f.unop) =
      SmProjCurve.Hom.pullbackAlgHom k f.unop ≫ SmProjCurve.Hom.pullbackAlgHom k g.unop
    exact SmProjCurve.Hom.pullbackAlgHom_comp k g.unop f.unop

lemma SmProjCurve.fromSpecStalk_genericPoint_isDominant (C : SmProjCurve k) :
    IsDominant (C.toScheme.fromSpecStalk (genericPoint C.toScheme)) := by
  haveI : IrreducibleSpace C.toScheme := irreducibleSpace_of_isIntegral C.toScheme
  constructor
  show Dense (Set.range (C.toScheme.fromSpecStalk (genericPoint C.toScheme)))
  rw [show Set.range (⇑(C.toScheme.fromSpecStalk (genericPoint C.toScheme))) =
      {y | y ⤳ genericPoint C.toScheme} from Scheme.range_fromSpecStalk]
  apply Dense.mono (s₁ := {genericPoint C.toScheme})
  · intro y hy
    simp only [Set.mem_singleton_iff] at hy
    rw [Set.mem_setOf_eq, hy]
  · rw [dense_iff_closure_eq]
    exact genericPoint_closure (α := C.toScheme)

lemma SmProjCurve.Hom.ext_of_fromSpecStalk_genericPoint {C₁ C₂ : SmProjCurve k}
    (f g : C₁ ⟶ C₂)
    (h : C₁.toScheme.fromSpecStalk (genericPoint C₁.toScheme) ≫ f.toSchemeHom =
         C₁.toScheme.fromSpecStalk (genericPoint C₁.toScheme) ≫ g.toSchemeHom) :
    f = g := by
  have hfg : f.toSchemeHom = g.toSchemeHom := by
    haveI : IsReduced C₁.toScheme := inferInstance
    haveI : IsSeparated C₂.structureMorphism := inferInstance
    haveI : IrreducibleSpace C₁.toScheme := irreducibleSpace_of_isIntegral C₁.toScheme
    haveI := C₁.fromSpecStalk_genericPoint_isDominant k
    exact ext_of_isDominant_of_isSeparated C₂.structureMorphism
      (by rw [f.over_spec, g.over_spec]) _ h
  exact SmProjCurve.Hom.ext hfg

lemma SmProjCurve.Hom.pullbackAlgHom_eq_imp_fromSpecStalk_eq {C₁ C₂ : SmProjCurve k}
    (f g : C₁ ⟶ C₂)
    (h : SmProjCurve.Hom.pullbackAlgHom k f = SmProjCurve.Hom.pullbackAlgHom k g) :
    C₁.toScheme.fromSpecStalk (genericPoint C₁.toScheme) ≫ f.toSchemeHom =
    C₁.toScheme.fromSpecStalk (genericPoint C₁.toScheme) ≫ g.toSchemeHom := by

  have heq_fun : ∀ x, (SmProjCurve.Hom.pullbackAlgHom k f).toAlgHom x =
                       (SmProjCurve.Hom.pullbackAlgHom k g).toAlgHom x := by
    intro x; rw [h]
  have heq_ring :
    (C₂.toScheme.presheaf.stalkCongr (.of_eq (SmProjCurve.Hom.map_genericPoint k f).symm)).hom ≫
      f.toSchemeHom.stalkMap (genericPoint C₁.toScheme) =
    (C₂.toScheme.presheaf.stalkCongr (.of_eq (SmProjCurve.Hom.map_genericPoint k g).symm)).hom ≫
      g.toSchemeHom.stalkMap (genericPoint C₁.toScheme) := by
    apply CommRingCat.hom_ext; ext x; exact heq_fun x

  rw [TopCat.Presheaf.stalkCongr_hom] at heq_ring

  haveI : IrreducibleSpace C₁.toScheme := irreducibleSpace_of_isIntegral C₁.toScheme
  haveI : IrreducibleSpace C₂.toScheme := irreducibleSpace_of_isIntegral C₂.toScheme
  set η₁ := genericPoint C₁.toScheme
  set η₂ := genericPoint C₂.toScheme

  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk f.toSchemeHom (x := η₁)]
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk g.toSchemeHom (x := η₁)]

  rw [show C₂.toScheme.fromSpecStalk (f.toSchemeHom η₁) =
    Spec.map (C₂.toScheme.presheaf.stalkSpecializes
      (Inseparable.of_eq (SmProjCurve.Hom.map_genericPoint k f).symm).specializes') ≫
    C₂.toScheme.fromSpecStalk η₂ from
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk _).symm]
  rw [show C₂.toScheme.fromSpecStalk (g.toSchemeHom η₁) =
    Spec.map (C₂.toScheme.presheaf.stalkSpecializes
      (Inseparable.of_eq (SmProjCurve.Hom.map_genericPoint k g).symm).specializes') ≫
    C₂.toScheme.fromSpecStalk η₂ from
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk _).symm]

  simp only [← Category.assoc]
  congr 1
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1

theorem functionFieldFunctor_faithful :
    (functionFieldFunctor k).Faithful := by
  constructor
  intro X Y f g hfg


  apply Quiver.Hom.unop_inj


  apply SmProjCurve.Hom.ext_of_fromSpecStalk_genericPoint k
  exact SmProjCurve.Hom.pullbackAlgHom_eq_imp_fromSpecStalk_eq k f.unop g.unop hfg

instance FunctionFieldCat.toFunctionField_k (F : FunctionFieldCat k) :
    ArithmeticGeometry.FunctionField_k k F.carrier where
  finitelyGenerated := F.finitelyGenerated
  transcendenceDegreeOne := F.transcendenceDegreeOne
  algClosedInF := fun x hx => by
    have := F.algClosedInF x hx
    rwa [IntermediateField.mem_bot, Set.mem_range]

theorem SmoothProjectiveCurveData_realizes_as_SmProjCurve
    {k : Type u} [Field k] [PerfectField k]
    (F : FunctionFieldCat k)
    {n : ℕ} (C : ArithmeticGeometry.SmoothProjectiveCurveData k F.carrier n) :
    ∃ (S : SmProjCurve k), Nonempty (S.toFunctionFieldCat k ≅ F) := by sorry

theorem smoothProjectiveModel (F : FunctionFieldCat k) :
    ∃ (C : SmProjCurve k), Nonempty (C.toFunctionFieldCat k ≅ F) := by

  haveI : ArithmeticGeometry.FunctionField_k k F.carrier := F.toFunctionField_k k

  obtain ⟨n, ⟨Cabs⟩⟩ := ArithmeticGeometry.abstract_curve_is_smooth_projective k F.carrier

  exact SmoothProjectiveCurveData_realizes_as_SmProjCurve F Cabs

theorem dvr_surjective_algHom_lifts_to_schemeMorphism
    {k : Type u} [Field k] [PerfectField k]
    {C₁ C₂ : SmProjCurve k}
    (θ : (C₂.toFunctionFieldCat k) ⟶ (C₁.toFunctionFieldCat k))
    (hSurj : ∀ (P : DVROfFunctionField k (C₁.toFunctionFieldCat k).carrier),
      ∃ (Q : DVROfFunctionField k (C₂.toFunctionFieldCat k).carrier),
        ∀ (f : (C₂.toFunctionFieldCat k).carrier), f ∈ Q.valRing →
          θ.toAlgHom f ∈ P.valRing) :
    ∃ (f : C₁ ⟶ C₂), SmProjCurve.Hom.pullbackAlgHom k f = θ := by sorry

theorem morphism_constant_or_surjective_fullness_witness
    {k : Type u} [Field k] [PerfectField k]
    {C₁ C₂ : SmProjCurve k}
    (θ : (C₂.toFunctionFieldCat k) ⟶ (C₁.toFunctionFieldCat k))
    (P : DVROfFunctionField k (C₁.toFunctionFieldCat k).carrier) :
    ∃ (Q : DVROfFunctionField k (C₂.toFunctionFieldCat k).carrier),
      ∀ (f : (C₂.toFunctionFieldCat k).carrier), f ∈ Q.valRing →
        θ.toAlgHom f ∈ P.valRing := by sorry

theorem functionFieldHom_lifts_to_schemeMorphism
    {k : Type u} [Field k] [PerfectField k]
    {C₁ C₂ : SmProjCurve k}
    (θ : (C₂.toFunctionFieldCat k) ⟶ (C₁.toFunctionFieldCat k)) :
    ∃ (f : C₁ ⟶ C₂), SmProjCurve.Hom.pullbackAlgHom k f = θ := by


  have hSurj : ∀ (P : DVROfFunctionField k (C₁.toFunctionFieldCat k).carrier),
      ∃ (Q : DVROfFunctionField k (C₂.toFunctionFieldCat k).carrier),
        ∀ (f : (C₂.toFunctionFieldCat k).carrier), f ∈ Q.valRing →
          θ.toAlgHom f ∈ P.valRing :=
    morphism_constant_or_surjective_fullness_witness θ

  exact dvr_surjective_algHom_lifts_to_schemeMorphism θ hSurj

theorem functionFieldFunctor_full :
    (functionFieldFunctor k).Full where
  map_surjective {X Y} θ := by


    obtain ⟨f, hf⟩ := functionFieldHom_lifts_to_schemeMorphism θ
    exact ⟨f.op, hf⟩

theorem functionFieldFunctor_essSurj :
    (functionFieldFunctor k).EssSurj where
  mem_essImage F := by
    obtain ⟨C, ⟨iso⟩⟩ := smoothProjectiveModel k F
    exact ⟨Opposite.op C, ⟨iso⟩⟩

theorem functionFieldFunctor_isEquivalence (k : Type u) [Field k] [PerfectField k] :
    (functionFieldFunctor k).IsEquivalence := by
  haveI := functionFieldFunctor_faithful k
  haveI := functionFieldFunctor_full k
  haveI := functionFieldFunctor_essSurj k
  exact Functor.IsEquivalence.mk

def curve_functionField_contravariantEquivalence (k : Type u) [Field k] [PerfectField k] :
    (SmProjCurve k)ᵒᵖ ≌ FunctionFieldCat k := by
  haveI := functionFieldFunctor_isEquivalence k
  exact (functionFieldFunctor k).asEquivalence

end Thm19_2

end ArithmeticGeometry
