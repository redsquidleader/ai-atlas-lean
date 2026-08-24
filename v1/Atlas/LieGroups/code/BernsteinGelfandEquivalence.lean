/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.HCBimoduleProjectives
import Atlas.LieGroups.code.CategoryO
import Atlas.LieGroups.code.CategoryOII
import Atlas.LieGroups.code.JantzenFiltration
import Atlas.LieGroups.code.DufloJoseph
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Analysis.Complex.Basic

noncomputable section

open TensorProduct

universe u_R u_g u_mod

structure LieModuleObj (R : Type u_R) [CommRing R]
    (g : Type u_g) [LieRing g] [LieAlgebra R g] where
  carrier : Type u_mod
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module R carrier]
  [instLieRingModule : LieRingModule g carrier]
  [instLieModule : LieModule R g carrier]

attribute [instance] LieModuleObj.instAddCommGroup LieModuleObj.instModule
  LieModuleObj.instLieRingModule LieModuleObj.instLieModule

variable {R : Type u_R} [CommRing R]
variable {g : Type u_g} [LieRing g] [LieAlgebra R g]

def IsRegularWeight
    {D : TriangularDecomposition R g}
    {rd : PositiveRootData D}
    (wg : WeylGroupData D)
    (cd : RootCorootData rd)
    (lam : D.𝔥 →ₗ[R] R) : Prop :=
  ∀ α ∈ rd.posRoots, cd.corootPairing (lam + wg.ρ) α ≠ 0

structure LieModuleMor
    (R : Type u_R) [CommRing R]
    (g : Type u_g) [LieRing g] [LieAlgebra R g]
    (X Y : LieModuleObj.{u_R, u_g, u_mod} R g) where
  toLinearMap : X.carrier →ₗ[R] Y.carrier
  lie_compat : ∀ (x : g) (m : X.carrier),
    toLinearMap (⁅x, m⁆) = ⁅x, toLinearMap m⁆

structure LieModuleIso
    (R : Type u_R) [CommRing R]
    (g : Type u_g) [LieRing g] [LieAlgebra R g]
    (X Y : LieModuleObj.{u_R, u_g, u_mod} R g) where
  forward : LieModuleMor R g X Y
  backward : LieModuleMor R g Y X
  left_inv : ∀ m : X.carrier,
    backward.toLinearMap (forward.toLinearMap m) = m
  right_inv : ∀ m : Y.carrier,
    forward.toLinearMap (backward.toLinearMap m) = m

structure TlambdaData
    (theta : CenterCharacter R g) where
  applyObj :
    (Y : LieBimodule.{u_R, u_g, u_mod} R g) →
    (hY : IsInHCThetaOne Y theta) →
    LieModuleObj.{u_R, u_g, u_mod} R g
  applyHom :
    {Y₁ Y₂ : LieBimodule.{u_R, u_g, u_mod} R g} →
    {hY₁ : IsInHCThetaOne Y₁ theta} →
    {hY₂ : IsInHCThetaOne Y₂ theta} →
    HCThetaOneHom Y₁ Y₂ theta hY₁ hY₂ →
    LieModuleMor R g (applyObj Y₁ hY₁) (applyObj Y₂ hY₂)
  applyHom_comp :
    {Y₁ Y₂ Y₃ : LieBimodule.{u_R, u_g, u_mod} R g} →
    {hY₁ : IsInHCThetaOne Y₁ theta} →
    {hY₂ : IsInHCThetaOne Y₂ theta} →
    {hY₃ : IsInHCThetaOne Y₃ theta} →
    (g' : HCThetaOneHom Y₂ Y₃ theta hY₂ hY₃) →
    (f : HCThetaOneHom Y₁ Y₂ theta hY₁ hY₂) →
    (comp_gf : HCThetaOneHom Y₁ Y₃ theta hY₁ hY₃) →
    comp_gf.toLinearMap = g'.toLinearMap.comp f.toLinearMap →
    (applyHom comp_gf).toLinearMap = (applyHom g').toLinearMap.comp (applyHom f).toLinearMap
  applyHom_id :
    {Y : LieBimodule.{u_R, u_g, u_mod} R g} →
    {hY : IsInHCThetaOne Y theta} →
    (idY : HCThetaOneHom Y Y theta hY hY) →
    idY.toLinearMap = LinearMap.id →
    (applyHom idY).toLinearMap = LinearMap.id
  applyHom_surjective :
    {Y₁ Y₂ : LieBimodule.{u_R, u_g, u_mod} R g} →
    {hY₁ : IsInHCThetaOne Y₁ theta} →
    {hY₂ : IsInHCThetaOne Y₂ theta} →
    (f : HCThetaOneHom Y₁ Y₂ theta hY₁ hY₂) →
    Function.Surjective f.toLinearMap →
    Function.Surjective (applyHom f).toLinearMap
  applyHom_exact :
    {Y₁ Y₂ Y₃ : LieBimodule.{u_R, u_g, u_mod} R g} →
    {hY₁ : IsInHCThetaOne Y₁ theta} →
    {hY₂ : IsInHCThetaOne Y₂ theta} →
    {hY₃ : IsInHCThetaOne Y₃ theta} →
    (p₁ : HCThetaOneHom Y₁ Y₂ theta hY₁ hY₂) →
    (p₀ : HCThetaOneHom Y₂ Y₃ theta hY₂ hY₃) →
    Function.Exact p₁.toLinearMap p₀.toLinearMap →
    Function.Surjective p₀.toLinearMap →
    Function.Exact (applyHom p₁).toLinearMap (applyHom p₀).toLinearMap
  applyObj_isCategoryO :
    {D : TriangularDecomposition R g} →
    {rd : PositiveRootData D} →
    (Y : LieBimodule.{u_R, u_g, u_mod} R g) →
    (hY : IsInHCThetaOne Y theta) →
    IsCategoryO D rd (applyObj Y hY).carrier

structure HlambdaData
    (theta : CenterCharacter R g) where
  applyObj :
    (X : LieModuleObj.{u_R, u_g, u_mod} R g) →
    LieBimodule.{u_R, u_g, u_mod} R g
  inHCThetaOne :
    (X : LieModuleObj.{u_R, u_g, u_mod} R g) →
    IsInHCThetaOne (applyObj X) theta

structure IsInBlock_LambdaPlusP
    {D : TriangularDecomposition R g}
    (rd : PositiveRootData D)
    (X : LieModuleObj.{u_R, u_g, u_mod} R g)
    (theta : CenterCharacter R g) : Prop where
  inCategoryO : IsCategoryO D rd X.carrier
  existsUEAAction :
    ∃ (ueaAct : UniversalEnvelopingAlgebra R g →ₐ[R] Module.End R X.carrier),
      GeneralizedEigenspaceCenter X.carrier ueaAct theta = ⊤

def IsInO_Lambda
    {D : TriangularDecomposition R g}
    (rd : PositiveRootData D)
    (theta : CenterCharacter R g)
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    (X : LieModuleObj.{u_R, u_g, u_mod} R g) : Prop :=
  IsInBlock_LambdaPlusP rd X theta ∧
  ∃ (P₀ P₁ : LieBimodule.{u_R, u_g, u_mod} R g)
    (hP₀ : IsInHCThetaOne P₀ theta) (hP₁ : IsInHCThetaOne P₁ theta),
    IsProjectiveInHCThetaOne P₀ theta hP₀ ∧
    IsProjectiveInHCThetaOne P₁ theta hP₁ ∧

    ∃ (_f₁ : (Tl.applyObj P₁ hP₁).carrier →ₗ[R] (Tl.applyObj P₀ hP₀).carrier)
      (f₀ : (Tl.applyObj P₀ hP₀).carrier →ₗ[R] X.carrier),
      Function.Surjective f₀

theorem proposition_25_10

    {ObjA ObjB : Type*}

    (HomA : ObjA → ObjA → Type*)
    (HomB : ObjB → ObjB → Type*)

    (T_obj : ObjA → ObjB)
    (T_map : ∀ {X Y : ObjA}, HomA X Y → HomB (T_obj X) (T_obj Y))

    (IsProjA : ObjA → Prop)
    (_IsProjB : ObjB → Prop)

    (compA : ∀ {X Y Z : ObjA}, HomA Y Z → HomA X Y → HomA X Z)
    (compB : ∀ {X Y Z : ObjB}, HomB Y Z → HomB X Y → HomB X Z)

    (_T_functorial : ∀ {X Y Z : ObjA} (g : HomA Y Z) (f : HomA X Y),
      T_map (compA g f) = compB (T_map g) (T_map f))

    (idA : ∀ (X : ObjA), HomA X X)
    (idB : ∀ (X : ObjB), HomB X X)
    (_T_preserves_id : ∀ (X : ObjA), T_map (idA X) = idB (T_obj X))


    (IsPresentationA : ∀ {P₁ P₀ X : ObjA}, HomA P₁ P₀ → HomA P₀ X → Prop)

    (IsPresentationB : ∀ {Q₁ Q₀ Y : ObjB}, HomB Q₁ Q₀ → HomB Q₀ Y → Prop)

    (_enough_proj : ∀ X : ObjA, ∃ (P₀ P₁ : ObjA), IsProjA P₀ ∧ IsProjA P₁ ∧
      ∃ (p₁ : HomA P₁ P₀) (p₀ : HomA P₀ X), IsPresentationA p₁ p₀)

    (_T_preserves_proj : ∀ P : ObjA, IsProjA P → _IsProjB (T_obj P))

    (_T_right_exact : ∀ {P₁ P₀ X : ObjA} (p₁ : HomA P₁ P₀) (p₀ : HomA P₀ X),
      IsPresentationA p₁ p₀ → IsPresentationB (T_map p₁) (T_map p₀))

    (_T_ff_on_proj : ∀ (P₀ P₁ : ObjA), IsProjA P₀ → IsProjA P₁ →
      Function.Bijective (fun f : HomA P₁ P₀ => T_map f))

    (IsIsoB : ∀ {Y₁ Y₂ : ObjB}, HomB Y₁ Y₂ → Prop)


    (_lift_through_pres : ∀ {P₁ P₀ X P₁' P₀' X' : ObjA}
      (p₁ : HomA P₁ P₀) (p₀ : HomA P₀ X)
      (p₁' : HomA P₁' P₀') (p₀' : HomA P₀' X')
      (_ : IsPresentationA p₁ p₀) (_ : IsPresentationA p₁' p₀')
      (_ : IsProjA P₀) (_ : IsProjA P₁),
      ∀ (a : HomA X X'), ∃ (a₀ : HomA P₀ P₀') (a₁ : HomA P₁ P₁'),
        compA p₀' a₀ = compA a p₀ ∧ compA a₀ p₁ = compA p₁' a₁)

    (_lift_through_presB : ∀ {Q₁ Q₀ Y Q₁' Q₀' Y' : ObjB}
      (q₁ : HomB Q₁ Q₀) (q₀ : HomB Q₀ Y)
      (q₁' : HomB Q₁' Q₀') (q₀' : HomB Q₀' Y')
      (_ : IsPresentationB q₁ q₀) (_ : IsPresentationB q₁' q₀')
      (_ : _IsProjB Q₀) (_ : _IsProjB Q₁),
      ∀ (b : HomB Y Y'), ∃ (b₀ : HomB Q₀ Q₀') (b₁ : HomB Q₁ Q₁'),
        compB q₀' b₀ = compB b q₀ ∧ compB b₀ q₁ = compB q₁' b₁)

    (_pres_epi : ∀ {P₁ P₀ X : ObjA} (p₁ : HomA P₁ P₀) (p₀ : HomA P₀ X),
      IsPresentationA p₁ p₀ →
      ∀ {Y : ObjA} (f g : HomA X Y), compA f p₀ = compA g p₀ → f = g)

    (_presB_epi : ∀ {Q₁ Q₀ Y : ObjB} (q₁ : HomB Q₁ Q₀) (q₀ : HomB Q₀ Y),
      IsPresentationB q₁ q₀ →
      ∀ {Z : ObjB} (f g : HomB Y Z), compB f q₀ = compB g q₀ → f = g)


    (_five_lemma_inj : ∀ {P₁ P₀ X Q₁ Q₀ Y : ObjA}
      (p₁ : HomA P₁ P₀) (p₀ : HomA P₀ X)
      (q₁ : HomA Q₁ Q₀) (q₀ : HomA Q₀ Y)
      (_ : IsPresentationA p₁ p₀) (_ : IsPresentationA q₁ q₀)
      (_ : IsProjA P₀) (_ : IsProjA P₁) (_ : IsProjA Q₀) (_ : IsProjA Q₁)
      (a₀ a₀' : HomA P₀ Q₀),
      compB (T_map q₀) (T_map a₀) = compB (T_map q₀) (T_map a₀') →
      a₀ = a₀')


    (_descent_through_pres : ∀ {P₁ P₀ X P₁' P₀' X' : ObjA}
      (p₁ : HomA P₁ P₀) (p₀ : HomA P₀ X)
      (p₁' : HomA P₁' P₀') (p₀' : HomA P₀' X')
      (_ : IsPresentationA p₁ p₀) (_ : IsPresentationA p₁' p₀')
      (a₀ : HomA P₀ P₀') (a₁ : HomA P₁ P₁'),
      compA a₀ p₁ = compA p₁' a₁ →
      ∃ (a : HomA X X'), compA p₀' a₀ = compA a p₀)


    (_cokernel_in_image : ∀ {P₁ P₀ : ObjA} (g : HomA P₁ P₀),
      IsProjA P₀ → IsProjA P₁ →
      ∀ (Y : ObjB) (f₀ : HomB (T_obj P₀) Y),
      IsPresentationB (T_map g) f₀ →
      ∃ (X : ObjA) (iso : HomB (T_obj X) Y), IsIsoB iso) :

    (∀ (X Y : ObjA), Function.Bijective (fun f : HomA X Y => T_map f))
    ∧


    (∀ (X : ObjA), ∃ (P₀ P₁ : ObjA), IsProjA P₀ ∧ IsProjA P₁ ∧
      ∃ (f₁ : HomB (T_obj P₁) (T_obj P₀))
        (f₀ : HomB (T_obj P₀) (T_obj X)),
        IsPresentationB f₁ f₀)
    ∧


    (∀ (Y : ObjB) (P₀ P₁ : ObjA) (f₁ : HomB (T_obj P₁) (T_obj P₀))
       (f₀ : HomB (T_obj P₀) Y),
      IsProjA P₀ → IsProjA P₁ → IsPresentationB f₁ f₀ →
      ∃ (X : ObjA) (iso : HomB (T_obj X) Y), IsIsoB iso) := by
  refine ⟨?_, ?_, ?_⟩
  ·


    intro X Y
    obtain ⟨P₀, P₁, hP₀, hP₁, p₁, p₀, hpresX⟩ := _enough_proj X
    obtain ⟨Q₀, Q₁, hQ₀, hQ₁, q₁, q₀, hpresY⟩ := _enough_proj Y
    have hpresTX := _T_right_exact p₁ p₀ hpresX
    have hpresTY := _T_right_exact q₁ q₀ hpresY
    constructor
    ·


      intro a a' hTeq

      have hTeq' : T_map a = T_map a' := hTeq

      obtain ⟨a₀, a₁, ha₀, ha₁⟩ :=
        _lift_through_pres p₁ p₀ q₁ q₀ hpresX hpresY hP₀ hP₁ a
      obtain ⟨a₀', a₁', ha₀', ha₁'⟩ :=
        _lift_through_pres p₁ p₀ q₁ q₀ hpresX hpresY hP₀ hP₁ a'

      have hcomp : compB (T_map q₀) (T_map a₀) = compB (T_map q₀) (T_map a₀') := by
        have lhs : compB (T_map q₀) (T_map a₀) = compB (T_map a) (T_map p₀) := by
          rw [← _T_functorial, ← _T_functorial]; exact congrArg T_map ha₀
        have rhs : compB (T_map q₀) (T_map a₀') = compB (T_map a') (T_map p₀) := by
          rw [← _T_functorial, ← _T_functorial]; exact congrArg T_map ha₀'
        rw [lhs, rhs, hTeq']

      have ha₀_eq :=
        _five_lemma_inj p₁ p₀ q₁ q₀ hpresX hpresY hP₀ hP₁ hQ₀ hQ₁ a₀ a₀' hcomp

      have hap : compA a p₀ = compA a' p₀ := by rw [← ha₀, ← ha₀', ha₀_eq]

      exact _pres_epi p₁ p₀ hpresX a a' hap
    ·


      intro b

      obtain ⟨b₀, b₁, hb₀, hb₁⟩ := _lift_through_presB
        (T_map p₁) (T_map p₀) (T_map q₁) (T_map q₀)
        hpresTX hpresTY
        (_T_preserves_proj P₀ hP₀) (_T_preserves_proj P₁ hP₁) b

      obtain ⟨a₀, ha₀_eq⟩ := (_T_ff_on_proj Q₀ P₀ hQ₀ hP₀).2 b₀
      obtain ⟨a₁, ha₁_eq⟩ := (_T_ff_on_proj Q₁ P₁ hQ₁ hP₁).2 b₁
      have ha₀T : T_map a₀ = b₀ := ha₀_eq
      have ha₁T : T_map a₁ = b₁ := ha₁_eq


      have hcompat : compA a₀ p₁ = compA q₁ a₁ := by
        have h1 : T_map (compA a₀ p₁) = T_map (compA q₁ a₁) := by
          rw [_T_functorial, _T_functorial, ha₀T, ha₁T]; exact hb₁
        exact (_T_ff_on_proj Q₀ P₁ hQ₀ hP₁).1 h1

      obtain ⟨a, ha⟩ := _descent_through_pres p₁ p₀ q₁ q₀ hpresX hpresY a₀ a₁ hcompat


      refine ⟨a, ?_⟩
      apply _presB_epi (T_map p₁) (T_map p₀) hpresTX (T_map a) b
      have step1 : compB (T_map a) (T_map p₀) = compB (T_map q₀) (T_map a₀) := by
        rw [← _T_functorial, ← ha, _T_functorial]
      have step2 : compB (T_map q₀) (T_map a₀) = compB (T_map q₀) b₀ := by
        rw [ha₀T]
      rw [step1, step2]; exact hb₀
  ·


    intro X
    obtain ⟨P₀, P₁, hP₀, hP₁, p₁, p₀, hpres⟩ := _enough_proj X
    exact ⟨P₀, P₁, hP₀, hP₁, T_map p₁, T_map p₀, _T_right_exact p₁ p₀ hpres⟩
  ·


    intro Y P₀ P₁ f₁ f₀ hP₀ hP₁ hpresB
    obtain ⟨g, hg⟩ := (_T_ff_on_proj P₀ P₁ hP₀ hP₁).2 f₁
    have hgT : T_map g = f₁ := hg
    rw [← hgT] at hpresB
    exact _cokernel_in_image g hP₀ hP₁ Y f₀ hpresB

section Theorem25_8

variable {D : TriangularDecomposition R g}

def VermaCarrier (D : TriangularDecomposition R g) (wt : D.𝔥 →ₗ[R] R) : Type u_mod :=
  (verma_module_exists (R := R) (𝔤 := g) D wt).choose

noncomputable instance VermaCarrier.instACG (D : TriangularDecomposition R g)
    (wt : D.𝔥 →ₗ[R] R) : AddCommGroup (VermaCarrier D wt) :=
  (verma_module_exists (R := R) (𝔤 := g) D wt).choose_spec.choose

noncomputable instance VermaCarrier.instMod (D : TriangularDecomposition R g)
    (wt : D.𝔥 →ₗ[R] R) : Module R (VermaCarrier D wt) :=
  (verma_module_exists (R := R) (𝔤 := g) D wt).choose_spec.choose_spec.choose

noncomputable instance VermaCarrier.instLRM (D : TriangularDecomposition R g)
    (wt : D.𝔥 →ₗ[R] R) : LieRingModule g (VermaCarrier D wt) :=
  (verma_module_exists (R := R) (𝔤 := g) D wt).choose_spec.choose_spec.choose_spec.choose

noncomputable instance VermaCarrier.instLM (D : TriangularDecomposition R g)
    (wt : D.𝔥 →ₗ[R] R) : LieModule R g (VermaCarrier D wt) :=
  (verma_module_exists (R := R) (𝔤 := g) D wt).choose_spec.choose_spec.choose_spec.choose_spec.choose

@[reducible] def LieBimodule.instLieRingModuleOfLeftAction
    (Y : LieBimodule.{u_R, u_g, u_mod} R g) : LieRingModule g Y.carrier where
  bracket x m := Y.leftAction (UniversalEnvelopingAlgebra.ι R x) m
  add_lie x y m := by
    show Y.leftAction (UniversalEnvelopingAlgebra.ι R (x + y)) m =
      Y.leftAction (UniversalEnvelopingAlgebra.ι R x) m +
      Y.leftAction (UniversalEnvelopingAlgebra.ι R y) m
    rw [map_add, map_add, LinearMap.add_apply]
  lie_add x m n := by
    show Y.leftAction (UniversalEnvelopingAlgebra.ι R x) (m + n) =
      Y.leftAction (UniversalEnvelopingAlgebra.ι R x) m +
      Y.leftAction (UniversalEnvelopingAlgebra.ι R x) n
    rw [map_add]
  leibniz_lie x y m := by
    show Y.leftAction (UniversalEnvelopingAlgebra.ι R x)
        (Y.leftAction (UniversalEnvelopingAlgebra.ι R y) m) =
      Y.leftAction (UniversalEnvelopingAlgebra.ι R ⁅x, y⁆) m +
      Y.leftAction (UniversalEnvelopingAlgebra.ι R y)
        (Y.leftAction (UniversalEnvelopingAlgebra.ι R x) m)
    rw [LieHom.map_lie, Ring.lie_def, map_sub, LinearMap.sub_apply, map_mul, map_mul]
    show Y.leftAction _ (Y.leftAction _ m) =
      Y.leftAction _ (Y.leftAction _ m) - Y.leftAction _ (Y.leftAction _ m) +
      Y.leftAction _ (Y.leftAction _ m)
    abel

@[reducible] def LieBimodule.instLieModuleOfLeftAction
    (Y : LieBimodule.{u_R, u_g, u_mod} R g) :
    @LieModule R g Y.carrier _ _ _ Y.instAddCommGroup Y.instModule
      Y.instLieRingModuleOfLeftAction :=
  @LieModule.mk R g Y.carrier _ _ _ Y.instAddCommGroup Y.instModule
    Y.instLieRingModuleOfLeftAction
    (fun r x m => by
      change Y.leftAction (UniversalEnvelopingAlgebra.ι R (r • x)) m =
        r • Y.leftAction (UniversalEnvelopingAlgebra.ι R x) m
      rw [map_smul, map_smul, LinearMap.smul_apply])
    (fun r x m => by
      change Y.leftAction (UniversalEnvelopingAlgebra.ι R x) (r • m) =
        r • Y.leftAction (UniversalEnvelopingAlgebra.ι R x) m
      rw [map_smul])

def Tlambda_exists
    {rd : PositiveRootData D}
    (wg : WeylGroupData D)
    (theta : CenterCharacter R g)
    (lam : D.𝔥 →ₗ[R] R)
    (_hdom : IsDominantWeightLE rd wg lam) :
    TlambdaData.{u_R, u_g, u_mod} theta where


  applyObj := fun Y _hY =>
    let _inst1 := Y.instLieRingModuleOfLeftAction
    let _inst2 := Y.instLieModuleOfLeftAction
    { carrier := Y.carrier ⊗[R] VermaCarrier D (lam - wg.ρ)
      instAddCommGroup := inferInstance
      instModule := inferInstance
      instLieRingModule := TensorProduct.LieModule.lieRingModule
      instLieModule := TensorProduct.LieModule.lieModule }


  applyHom := fun {Y₁ Y₂ _hY₁ _hY₂} f =>
    let _inst1 := Y₁.instLieRingModuleOfLeftAction
    let _inst2 := Y₁.instLieModuleOfLeftAction
    let _inst3 := Y₂.instLieRingModuleOfLeftAction
    let _inst4 := Y₂.instLieModuleOfLeftAction
    { toLinearMap := TensorProduct.map f.toLinearMap LinearMap.id


      lie_compat := fun x t => by
        refine t.induction_on ?_ ?_ ?_
        · simp [lie_zero, map_zero]
        · intro m n
          simp only [TensorProduct.LieModule.lie_tmul_right, map_add,
            TensorProduct.map_tmul, LinearMap.id_apply]
          congr 1; congr 1
          show f.toLinearMap (Y₁.leftAction (UniversalEnvelopingAlgebra.ι R x) m) =
            Y₂.leftAction (UniversalEnvelopingAlgebra.ι R x) (f.toLinearMap m)
          exact f.left_compat (UniversalEnvelopingAlgebra.ι R x) m
        · intro t₁ t₂ ht₁ ht₂
          simp [lie_add, map_add, ht₁, ht₂] }


  applyHom_comp := fun {Y₁ Y₂ Y₃ _hY₁ _hY₂ _hY₃} g' f comp_gf h_eq => by
    show TensorProduct.map comp_gf.toLinearMap LinearMap.id =
      (TensorProduct.map g'.toLinearMap LinearMap.id).comp
        (TensorProduct.map f.toLinearMap LinearMap.id)
    rw [h_eq, ← TensorProduct.map_comp]
    simp


  applyHom_id := fun {Y _hY} idY h_eq => by
    show TensorProduct.map idY.toLinearMap LinearMap.id = LinearMap.id
    rw [h_eq, TensorProduct.map_id]


  applyHom_surjective := fun {Y₁ Y₂ _hY₁ _hY₂} f hf_surj => by
    show Function.Surjective (TensorProduct.map f.toLinearMap LinearMap.id)
    exact TensorProduct.map_surjective hf_surj Function.surjective_id


  applyHom_exact := fun {Y₁ Y₂ Y₃ _hY₁ _hY₂ _hY₃} p₁ p₀ hex hsurj => by
    show Function.Exact (TensorProduct.map p₁.toLinearMap LinearMap.id)
      (TensorProduct.map p₀.toLinearMap LinearMap.id)
    have h1 : TensorProduct.map p₁.toLinearMap (LinearMap.id : VermaCarrier D (lam - wg.ρ) →ₗ[R]
        VermaCarrier D (lam - wg.ρ)) =
        LinearMap.rTensor (VermaCarrier D (lam - wg.ρ)) p₁.toLinearMap := by
      ext; simp [LinearMap.rTensor, TensorProduct.map_tmul]
    have h2 : TensorProduct.map p₀.toLinearMap (LinearMap.id : VermaCarrier D (lam - wg.ρ) →ₗ[R]
        VermaCarrier D (lam - wg.ρ)) =
        LinearMap.rTensor (VermaCarrier D (lam - wg.ρ)) p₀.toLinearMap := by
      ext; simp [LinearMap.rTensor, TensorProduct.map_tmul]
    rw [h1, h2]
    exact rTensor_exact (VermaCarrier D (lam - wg.ρ)) hex hsurj


  applyObj_isCategoryO := fun {D' rd'} Y _hY => by
    sorry

theorem vermaCarrier_central_character
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {D : TriangularDecomposition R g}
    (wg : WeylGroupData D)
    (wt : D.𝔥 →ₗ[R] R)
    (z : ↥(Subalgebra.center R (UniversalEnvelopingAlgebra R g)))
    (m : VermaCarrier D wt) :
    (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R g (VermaCarrier D wt)))
      (z : UniversalEnvelopingAlgebra R g) m = (evalHC D wg (wt + wg.ρ)) z • m := by


  have hvm : Nonempty (IsVermaModule D (VermaCarrier D wt) wt) :=
    (verma_module_exists (R := R) (𝔤 := g) D wt).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  obtain ⟨hIsVerma⟩ := hvm
  have hic := vermaHasInfinitesimalCharacter D wg (VermaCarrier D wt) wt hIsVerma

  exact (vermaHasInfinitesimalCharacter D wg (VermaCarrier D wt) wt hIsVerma).center_acts_by_scalar z m

theorem homFinBimodule_vermaCarrier_isHC
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    [Module.Finite R g] {D : TriangularDecomposition R g}
    (wt : D.𝔥 →ₗ[R] R)
    (N : Type u_mod) [AddCommGroup N] [Module R N] [LieRingModule g N] [LieModule R g N] :
    IsHarishChandraBimodule (HomFinBimodule (R := R) (𝔤 := g) (VermaCarrier D wt) N) := by
  constructor

  intro ⟨T, hT⟩


  obtain ⟨S, hfin, hT_mem, hstab⟩ := hT

  have hS_sub_HomFin : ∀ f : VermaCarrier D wt →ₗ[R] N, f ∈ S → f ∈ HomFin (R := R) (𝔤 := g) (VermaCarrier D wt) N := by
    intro f hf
    exact ⟨S, hfin, hf, hstab⟩

  let S' : Submodule R (↥(HomFin (R := R) (𝔤 := g) (VermaCarrier D wt) N)) :=
    S.comap (HomFin (R := R) (𝔤 := g) (VermaCarrier D wt) N).subtype
  refine ⟨S', ?_, ?_, ?_⟩
  ·


    have : Module.Finite R S := hfin


    let e : S' →ₗ[R] S :=
      { toFun := fun ⟨⟨f, hf_homfin⟩, hf_S⟩ => ⟨f, hf_S⟩
        map_add' := fun _ _ => by ext; rfl
        map_smul' := fun _ _ => by ext; rfl }
    have he_inj : Function.Injective e := fun ⟨⟨f₁, _⟩, _⟩ ⟨⟨f₂, _⟩, _⟩ h => by
      have : f₁ = f₂ := Subtype.mk.inj h
      subst this; rfl
    have he_surj : Function.Surjective e := fun ⟨f, hf_S⟩ =>
      ⟨⟨⟨f, hS_sub_HomFin f hf_S⟩, hf_S⟩, rfl⟩
    exact Module.Finite.equiv (LinearEquiv.ofBijective e ⟨he_inj, he_surj⟩).symm
  ·
    show T ∈ S
    exact hT_mem
  ·
    intro x ⟨f, hf_homfin⟩ hf_S'

    show ((HomFinBimodule (R := R) (𝔤 := g) (VermaCarrier D wt) N).adjointAction x ⟨f, hf_homfin⟩).val ∈ S


    rw [homFinBimodule_adjointAction_val (VermaCarrier D wt) N x ⟨f, hf_homfin⟩]
    exact hstab x f hf_S'

theorem homFinBimodule_right_character
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    [Module.Finite R g] {D : TriangularDecomposition R g}
    (wg : WeylGroupData D)
    (wt : D.𝔥 →ₗ[R] R)
    (X : LieModuleObj.{u_R, u_g, u_mod} R g)
    (z : Subalgebra.center R (UniversalEnvelopingAlgebra R g))
    (m : (HomFinBimodule (R := R) (𝔤 := g) (VermaCarrier D wt) X.carrier).carrier) :
    (HomFinBimodule (R := R) (𝔤 := g) (VermaCarrier D wt) X.carrier).rightAction
      (MulOpposite.op (z : UniversalEnvelopingAlgebra R g)) m =
    (evalHC D wg (wt + wg.ρ)) z • m := by


  obtain ⟨T, hT⟩ := m
  simp only [HomFinBimodule]
  ext v


  show (T ∘ₗ (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R g (VermaCarrier D wt))) (↑z)) v =
    (evalHC D wg (wt + wg.ρ)) z • T v
  rw [LinearMap.comp_apply, vermaCarrier_central_character wg wt z v, T.map_smul]

def Hlambda_exists
    [Module.Finite R g]
    {rd : PositiveRootData D}
    (wg : WeylGroupData D)
    (theta : CenterCharacter R g)
    (lam : D.𝔥 →ₗ[R] R)
    (_hdom : IsDominantWeightLE rd wg lam)
    (htheta : theta = evalHC D wg lam) :
    HlambdaData.{u_R, u_g, u_mod} theta where


  applyObj := fun X =>
    HomFinBimodule (R := R) (𝔤 := g) (VermaCarrier D (lam - wg.ρ)) X.carrier


  inHCThetaOne := fun _X =>
    { isHC := homFinBimodule_vermaCarrier_isHC (lam - wg.ρ) _X.carrier
      right_annihilated := fun z m => by


        have h := homFinBimodule_right_character wg (lam - wg.ρ) _X z m


        simp only [sub_add_cancel] at h
        rw [h, htheta] }

abbrev HCThetaOneObj (R : Type u_R) [CommRing R] (g : Type u_g) [LieRing g] [LieAlgebra R g]
    (theta : CenterCharacter R g) :=
  { Y : LieBimodule.{u_R, u_g, u_mod} R g // IsInHCThetaOne Y theta }

def HCThetaOneHomBundled {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    (theta : CenterCharacter R g)
    (A B : HCThetaOneObj.{u_R, u_g, u_mod} R g theta) : Type u_mod :=
  HCThetaOneHom A.1 B.1 theta A.2 B.2

def TlambdaObjBundled {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    (A : HCThetaOneObj.{u_R, u_g, u_mod} R g theta) : LieModuleObj.{u_R, u_g, u_mod} R g :=
  Tl.applyObj A.1 A.2

def TlambdaMapBundled {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    {A B : HCThetaOneObj.{u_R, u_g, u_mod} R g theta}
    (f : HCThetaOneHomBundled theta A B) :
    LieModuleMor R g (TlambdaObjBundled Tl A) (TlambdaObjBundled Tl B) :=
  Tl.applyHom f

def IsProjHCBundled {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    (theta : CenterCharacter R g)
    (A : HCThetaOneObj.{u_R, u_g, u_mod} R g theta) : Prop :=
  IsProjectiveInHCThetaOne A.1 theta A.2

noncomputable def HCThetaOne_comp
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    {A B C : HCThetaOneObj.{u_R, u_g, u_mod} R g theta} :
    HCThetaOneHomBundled theta B C → HCThetaOneHomBundled theta A B →
    HCThetaOneHomBundled theta A C :=
  fun g' f => {
    toLinearMap := g'.toLinearMap.comp f.toLinearMap
    left_compat := fun u m => by
      simp [LinearMap.comp_apply]
      rw [f.left_compat, g'.left_compat]
    right_compat := fun u m => by
      simp [LinearMap.comp_apply]
      rw [f.right_compat, g'.right_compat]
  }

def LieModuleMor_comp
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {X Y Z : LieModuleObj.{u_R, u_g, u_mod} R g}
    (g' : LieModuleMor R g Y Z) (f : LieModuleMor R g X Y) :
    LieModuleMor R g X Z where
  toLinearMap := g'.toLinearMap.comp f.toLinearMap
  lie_compat x m := by
    simp [LinearMap.comp_apply]
    rw [f.lie_compat, g'.lie_compat]

def LieModuleMor_sub
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {X Y : LieModuleObj.{u_R, u_g, u_mod} R g}
    (f g' : LieModuleMor R g X Y) : LieModuleMor R g X Y where
  toLinearMap := f.toLinearMap - g'.toLinearMap
  lie_compat x m := by
    simp only [LinearMap.sub_apply]
    rw [f.lie_compat, g'.lie_compat, lie_sub]

noncomputable def HCThetaOne_id
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (A : HCThetaOneObj.{u_R, u_g, u_mod} R g theta) :
    HCThetaOneHomBundled theta A A :=
  { toLinearMap := LinearMap.id
    left_compat := fun _ _ => rfl
    right_compat := fun _ _ => rfl }

def LieModuleMor_id
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    (X : LieModuleObj.{u_R, u_g, u_mod} R g) :
    LieModuleMor R g X X where
  toLinearMap := LinearMap.id
  lie_compat _ _ := rfl

def IsPresentationHC
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    {P₁ P₀ X : HCThetaOneObj.{u_R, u_g, u_mod} R g theta}
    (p₁ : HCThetaOneHomBundled theta P₁ P₀) (p₀ : HCThetaOneHomBundled theta P₀ X) : Prop :=
  Function.Surjective p₀.toLinearMap ∧
  (∀ m : P₁.1.carrier, p₀.toLinearMap (p₁.toLinearMap m) = 0) ∧
  (∀ m : P₀.1.carrier, p₀.toLinearMap m = 0 → ∃ n : P₁.1.carrier, p₁.toLinearMap n = m)

def IsPresentationO
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {Q₁ Q₀ Y : LieModuleObj.{u_R, u_g, u_mod} R g}
    (q₁ : LieModuleMor R g Q₁ Q₀) (q₀ : LieModuleMor R g Q₀ Y) : Prop :=
  Function.Surjective q₀.toLinearMap ∧
  (∀ m : Q₁.carrier, q₀.toLinearMap (q₁.toLinearMap m) = 0) ∧
  (∀ m : Q₀.carrier, q₀.toLinearMap m = 0 → ∃ n : Q₁.carrier, q₁.toLinearMap n = m)

def IsProjO
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    (P : LieModuleObj.{u_R, u_g, u_mod} R g) : Prop :=
  ∀ (Y₁ Y₂ : LieModuleObj.{u_R, u_g, u_mod} R g)
    (g' : LieModuleMor R g Y₁ Y₂) (f : LieModuleMor R g P Y₂),
    Function.Surjective g'.toLinearMap →
    ∃ (f' : LieModuleMor R g P Y₁),
      ∀ m : P.carrier, g'.toLinearMap (f'.toLinearMap m) = f.toLinearMap m

def IsIsoO
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {Y₁ Y₂ : LieModuleObj.{u_R, u_g, u_mod} R g}
    (f : LieModuleMor R g Y₁ Y₂) : Prop :=
  ∃ (g' : LieModuleMor R g Y₂ Y₁),
    (∀ m : Y₁.carrier, g'.toLinearMap (f.toLinearMap m) = m) ∧
    (∀ m : Y₂.carrier, f.toLinearMap (g'.toLinearMap m) = m)

theorem LieModuleMor.ext'
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {X Y : LieModuleObj.{u_R, u_g, u_mod} R g}
    {f g' : LieModuleMor R g X Y}
    (h : f.toLinearMap = g'.toLinearMap) : f = g' := by
  cases f; cases g'; simp only [LieModuleMor.mk.injEq] at *; exact h

theorem Tlambda_functorial
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    {A B C : HCThetaOneObj.{u_R, u_g, u_mod} R g theta}
    (g' : HCThetaOneHomBundled theta B C) (f : HCThetaOneHomBundled theta A B) :
    TlambdaMapBundled Tl (HCThetaOne_comp g' f) =
    LieModuleMor_comp (TlambdaMapBundled Tl g') (TlambdaMapBundled Tl f) := by
  apply LieModuleMor.ext'


  show (Tl.applyHom (HCThetaOne_comp g' f)).toLinearMap =
    (Tl.applyHom g').toLinearMap.comp (Tl.applyHom f).toLinearMap
  exact Tl.applyHom_comp g' f (HCThetaOne_comp g' f) rfl

theorem Tlambda_preserves_id
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    (A : HCThetaOneObj.{u_R, u_g, u_mod} R g theta) :
    TlambdaMapBundled Tl (HCThetaOne_id A) = LieModuleMor_id (TlambdaObjBundled Tl A) := by
  apply LieModuleMor.ext'
  show (Tl.applyHom (HCThetaOne_id A)).toLinearMap = LinearMap.id
  exact Tl.applyHom_id (HCThetaOne_id A) rfl

theorem HCThetaOne_enough_proj_cover
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    [LieAlgebra.IsSemisimple R g] [Module.Finite R g]
    {theta : CenterCharacter R g}
    (X : HCThetaOneObj.{u_R, u_g, u_mod} R g theta) :
    ∃ (P : HCThetaOneObj.{u_R, u_g, u_mod} R g theta),
      IsProjHCBundled theta P ∧
      ∃ (π : HCThetaOneHomBundled theta P X), Function.Surjective π.toLinearMap := by
  obtain ⟨P, hP, hProj, π, hSurj⟩ := hc_theta_one_enough_projectives theta X.1 X.2
  exact ⟨⟨P, hP⟩, hProj, π, hSurj⟩

theorem HCThetaOne_kernel_in_category
    {R : Type u_R} [CommRing R] [IsNoetherianRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    {P₀ X : HCThetaOneObj.{u_R, u_g, u_mod} R g theta}
    (p₀ : HCThetaOneHomBundled theta P₀ X) :
    ∃ (K : HCThetaOneObj.{u_R, u_g, u_mod} R g theta)
      (ι : HCThetaOneHomBundled theta K P₀),
      Function.Injective ι.toLinearMap ∧
      (∀ m : K.1.carrier, p₀.toLinearMap (ι.toLinearMap m) = 0) ∧
      (∀ m : P₀.1.carrier, p₀.toLinearMap m = 0 → ∃ n : K.1.carrier, ι.toLinearMap n = m) := by
  set K_sub : Submodule R P₀.1.carrier := p₀.toLinearMap.ker with hK_sub_def
  have hL : ∀ (u : UniversalEnvelopingAlgebra R g) (m : P₀.1.carrier),
      m ∈ K_sub → (P₀.1.leftAction u) m ∈ K_sub := by
    intro u m hm; rw [LinearMap.mem_ker] at hm ⊢; rw [p₀.left_compat, hm, map_zero]
  have hR : ∀ (u : (UniversalEnvelopingAlgebra R g)ᵐᵒᵖ) (m : P₀.1.carrier),
      m ∈ K_sub → (P₀.1.rightAction u) m ∈ K_sub := by
    intro u m hm; rw [LinearMap.mem_ker] at hm ⊢; rw [p₀.right_compat, hm, map_zero]
  let kerBimod : LieBimodule R g :=
  { carrier := K_sub
    leftAction :=
    { toFun := fun u => (P₀.1.leftAction u).restrict (fun m hm => hL u m hm)
      map_one' := by
        ext ⟨m, hm⟩; simp only [LinearMap.restrict_apply]
        exact congr_fun (congr_arg DFunLike.coe (map_one P₀.1.leftAction)) m
      map_mul' := fun u v => by
        ext ⟨m, hm⟩
        simp only [LinearMap.restrict_apply]
        show (P₀.1.leftAction (u * v)) m = (P₀.1.leftAction u) ((P₀.1.leftAction v) m)
        exact congr_fun (congr_arg DFunLike.coe (map_mul P₀.1.leftAction u v)) m
      map_zero' := by
        ext ⟨m, hm⟩; simp only [LinearMap.restrict_apply]
        exact congr_fun (congr_arg DFunLike.coe (map_zero P₀.1.leftAction)) m
      map_add' := fun u v => by
        ext ⟨m, hm⟩
        simp only [LinearMap.restrict_apply]
        show (P₀.1.leftAction (u + v)) m = (P₀.1.leftAction u) m + (P₀.1.leftAction v) m
        exact congr_fun (congr_arg DFunLike.coe (map_add P₀.1.leftAction u v)) m
      commutes' := fun r => by
        ext ⟨m, hm⟩; simp only [LinearMap.restrict_apply]
        exact congr_fun (congr_arg DFunLike.coe (AlgHom.commutes P₀.1.leftAction r)) m }
    rightAction :=
    { toFun := fun u => (P₀.1.rightAction u).restrict (fun m hm => hR u m hm)
      map_one' := by
        ext ⟨m, hm⟩; simp only [LinearMap.restrict_apply]
        exact congr_fun (congr_arg DFunLike.coe (map_one P₀.1.rightAction)) m
      map_mul' := fun u v => by
        ext ⟨m, hm⟩
        simp only [LinearMap.restrict_apply]
        show (P₀.1.rightAction (u * v)) m = (P₀.1.rightAction u) ((P₀.1.rightAction v) m)
        exact congr_fun (congr_arg DFunLike.coe (map_mul P₀.1.rightAction u v)) m
      map_zero' := by
        ext ⟨m, hm⟩; simp only [LinearMap.restrict_apply]
        exact congr_fun (congr_arg DFunLike.coe (map_zero P₀.1.rightAction)) m
      map_add' := fun u v => by
        ext ⟨m, hm⟩
        simp only [LinearMap.restrict_apply]
        show (P₀.1.rightAction (u + v)) m = (P₀.1.rightAction u) m + (P₀.1.rightAction v) m
        exact congr_fun (congr_arg DFunLike.coe (map_add P₀.1.rightAction u v)) m
      commutes' := fun r => by
        ext ⟨m, hm⟩; simp only [LinearMap.restrict_apply]
        exact congr_fun (congr_arg DFunLike.coe (AlgHom.commutes P₀.1.rightAction r)) m }
    actions_commute := fun u v ⟨m, hm⟩ =>
      Subtype.ext (P₀.1.actions_commute u v m) }
  have kerIsHC : IsInHCThetaOne kerBimod theta := by
    constructor
    · constructor
      intro ⟨m, hm⟩
      obtain ⟨S, hS_fg, hm_in_S, hS_stable⟩ := P₀.2.isHC.locally_finite m
      refine ⟨S.comap K_sub.subtype, ?_, ?_, ?_⟩
      · rw [Module.Finite.iff_fg]
        apply Submodule.fg_of_fg_map_injective (Submodule.subtype K_sub)
          (Submodule.injective_subtype K_sub)
        rw [Submodule.map_comap_subtype]
        exact (Module.Finite.iff_fg.mp hS_fg).of_le inf_le_right
      · exact hm_in_S
      · intro x s hs_mem
        show (P₀.1.adjointAction x) s.1 ∈ S
        exact hS_stable x s.1 hs_mem
    · intro z ⟨m, hm⟩
      exact Subtype.ext (P₀.2.right_annihilated z m)
  exact ⟨⟨kerBimod, kerIsHC⟩,
    ⟨K_sub.subtype,
     fun u ⟨m, hm⟩ => by
       show K_sub.subtype ((P₀.1.leftAction u).restrict (fun m hm => hL u m hm) ⟨m, hm⟩) =
         (P₀.1.leftAction u) (K_sub.subtype ⟨m, hm⟩)
       simp [LinearMap.restrict_apply],
     fun u ⟨m, hm⟩ => by
       show K_sub.subtype ((P₀.1.rightAction u).restrict (fun m hm => hR u m hm) ⟨m, hm⟩) =
         (P₀.1.rightAction u) (K_sub.subtype ⟨m, hm⟩)
       simp [LinearMap.restrict_apply]⟩,
    Submodule.subtype_injective K_sub,
    fun ⟨m, hm⟩ => hm,
    fun m hm => ⟨⟨m, by rwa [LinearMap.mem_ker]⟩, rfl⟩⟩

theorem HCThetaOne_enough_proj
    {R : Type u_R} [CommRing R] [IsNoetherianRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    [LieAlgebra.IsSemisimple R g] [Module.Finite R g]
    {theta : CenterCharacter R g} :
    ∀ X : HCThetaOneObj.{u_R, u_g, u_mod} R g theta,
      ∃ (P₀ P₁ : HCThetaOneObj.{u_R, u_g, u_mod} R g theta),
        IsProjHCBundled theta P₀ ∧ IsProjHCBundled theta P₁ ∧
        ∃ (p₁ : HCThetaOneHomBundled theta P₁ P₀)
          (p₀ : HCThetaOneHomBundled theta P₀ X),
          IsPresentationHC p₁ p₀ := by
  intro X

  obtain ⟨P₀, hP₀_proj, p₀, hp₀_surj⟩ := HCThetaOne_enough_proj_cover X

  obtain ⟨K, ι, _, hι_comp, hι_exact⟩ := HCThetaOne_kernel_in_category p₀

  obtain ⟨P₁, hP₁_proj, s, hs_surj⟩ := HCThetaOne_enough_proj_cover K


  let p₁ : HCThetaOneHomBundled theta P₁ P₀ :=
    { toLinearMap := ι.toLinearMap.comp s.toLinearMap
      left_compat := fun u m => by
        show ι.toLinearMap (s.toLinearMap (P₁.1.leftAction u m)) =
             P₀.1.leftAction u (ι.toLinearMap (s.toLinearMap m))
        rw [s.left_compat, ι.left_compat]
      right_compat := fun u m => by
        show ι.toLinearMap (s.toLinearMap (P₁.1.rightAction u m)) =
             P₀.1.rightAction u (ι.toLinearMap (s.toLinearMap m))
        rw [s.right_compat, ι.right_compat] }
  refine ⟨P₀, P₁, hP₀_proj, hP₁_proj, p₁, p₀, ?_, ?_, ?_⟩
  ·
    exact hp₀_surj
  ·
    intro m
    exact hι_comp (s.toLinearMap m)
  ·
    intro m hm
    obtain ⟨n, hn⟩ := hι_exact m hm
    obtain ⟨k, hk⟩ := hs_surj n
    exact ⟨k, by show ι.toLinearMap (s.toLinearMap k) = m; rw [hk, hn]⟩

noncomputable def Hlambda_applyObj_bundled
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    (X : LieModuleObj.{u_R, u_g, u_mod} R g) :
    HCThetaOneObj.{u_R, u_g, u_mod} R g theta :=
  sorry

noncomputable def Hlambda_applyHom_bundled
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    {X Y : LieModuleObj.{u_R, u_g, u_mod} R g}
    (f : LieModuleMor R g X Y) :
    HCThetaOneHomBundled theta (Hlambda_applyObj_bundled Tl X) (Hlambda_applyObj_bundled Tl Y) :=
  sorry

theorem Hlambda_preserves_surjective
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    {X Y : LieModuleObj.{u_R, u_g, u_mod} R g}
    (f : LieModuleMor R g X Y)
    (hf_surj : Function.Surjective f.toLinearMap) :
    Function.Surjective (Hlambda_applyHom_bundled Tl f).toLinearMap := by
  sorry

noncomputable def adjunction_forward
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    (P : HCThetaOneObj.{u_R, u_g, u_mod} R g theta)
    {Y : LieModuleObj.{u_R, u_g, u_mod} R g}
    (f : LieModuleMor R g (TlambdaObjBundled Tl P) Y) :
    HCThetaOneHomBundled theta P (Hlambda_applyObj_bundled Tl Y) :=
  sorry

theorem adjunction_backward_lift
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    (P : HCThetaOneObj.{u_R, u_g, u_mod} R g theta)
    {Y₁ Y₂ : LieModuleObj.{u_R, u_g, u_mod} R g}
    (g' : LieModuleMor R g Y₁ Y₂)
    (f : LieModuleMor R g (TlambdaObjBundled Tl P) Y₂)
    (χ : HCThetaOneHomBundled theta P (Hlambda_applyObj_bundled Tl Y₁))
    (hχ : ∀ m : P.1.carrier,
      (Hlambda_applyHom_bundled Tl g').toLinearMap (χ.toLinearMap m) =
        (adjunction_forward Tl P f).toLinearMap m) :
    ∃ (f' : LieModuleMor R g (TlambdaObjBundled Tl P) Y₁),
      ∀ m : (TlambdaObjBundled Tl P).carrier,
        g'.toLinearMap (f'.toLinearMap m) = f.toLinearMap m := by
  sorry

theorem adjunction_Hlambda_lifting
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    (P : HCThetaOneObj.{u_R, u_g, u_mod} R g theta)
    {Y₁ Y₂ : LieModuleObj.{u_R, u_g, u_mod} R g}
    (g' : LieModuleMor R g Y₁ Y₂)
    (f : LieModuleMor R g (TlambdaObjBundled Tl P) Y₂)
    (hg_surj : Function.Surjective g'.toLinearMap) :

    ∃ (A₁ A₂ : HCThetaOneObj.{u_R, u_g, u_mod} R g theta)
      (φ : HCThetaOneHomBundled theta A₁ A₂)
      (ψ : HCThetaOneHomBundled theta P A₂),

      Function.Surjective φ.toLinearMap ∧

      (∀ (χ : HCThetaOneHomBundled theta P A₁),
        (∀ m : P.1.carrier, φ.toLinearMap (χ.toLinearMap m) = ψ.toLinearMap m) →
        ∃ (f' : LieModuleMor R g (TlambdaObjBundled Tl P) Y₁),
          ∀ m : (TlambdaObjBundled Tl P).carrier,
            g'.toLinearMap (f'.toLinearMap m) = f.toLinearMap m) := by

  refine ⟨Hlambda_applyObj_bundled Tl Y₁, Hlambda_applyObj_bundled Tl Y₂,
    Hlambda_applyHom_bundled Tl g', adjunction_forward Tl P f,
    Hlambda_preserves_surjective Tl g' hg_surj, ?_⟩

  intro χ hχ
  exact adjunction_backward_lift Tl P g' f χ hχ

theorem Tlambda_preserves_proj
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta) :
    ∀ P : HCThetaOneObj.{u_R, u_g, u_mod} R g theta,
      IsProjHCBundled theta P → IsProjO (TlambdaObjBundled Tl P) := by
  intro P hP_proj Y₁ Y₂ g' f hg_surj

  obtain ⟨A₁, A₂, φ, ψ, hφ_surj, hlift⟩ :=
    adjunction_Hlambda_lifting Tl P g' f hg_surj


  have hP_proj' := hP_proj
  unfold IsProjHCBundled IsProjectiveInHCThetaOne at hP_proj'
  obtain ⟨χ, hχ⟩ := hP_proj' A₁.1 A₂.1 A₁.2 A₂.2 φ ψ hφ_surj

  exact hlift χ hχ

theorem Tlambda_right_exact
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    {P₁ P₀ X : HCThetaOneObj.{u_R, u_g, u_mod} R g theta}
    (p₁ : HCThetaOneHomBundled theta P₁ P₀)
    (p₀ : HCThetaOneHomBundled theta P₀ X) :
    IsPresentationHC p₁ p₀ →
    IsPresentationO (TlambdaMapBundled Tl p₁) (TlambdaMapBundled Tl p₀) := by
  intro ⟨hsurj, hcomp, hexact_ker⟩

  have hex : Function.Exact p₁.toLinearMap p₀.toLinearMap := by
    intro y
    constructor
    · intro hy; exact hexact_ker y hy
    · intro ⟨x, hx⟩; rw [← hx]; exact hcomp x

  have hex_T := Tl.applyHom_exact p₁ p₀ hex hsurj
  refine ⟨Tl.applyHom_surjective p₀ hsurj, ?_, ?_⟩

  · intro m
    exact (hex_T ((Tl.applyHom p₁).toLinearMap m)).mpr ⟨m, rfl⟩

  · intro m hm
    exact (hex_T m).mp hm

theorem Tlambda_ff_on_proj
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta) :
    ∀ (P₀ P₁ : HCThetaOneObj.{u_R, u_g, u_mod} R g theta),
      IsProjHCBundled theta P₀ → IsProjHCBundled theta P₁ →
      Function.Bijective (fun f : HCThetaOneHomBundled theta P₁ P₀ => TlambdaMapBundled Tl f) := by
  sorry

theorem HCThetaOne_lift_through_pres
    {R : Type u_R} [CommRing R] [IsNoetherianRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    {P₁ P₀ X P₁' P₀' X' : HCThetaOneObj.{u_R, u_g, u_mod} R g theta}
    (p₁ : HCThetaOneHomBundled theta P₁ P₀)
    (p₀ : HCThetaOneHomBundled theta P₀ X)
    (p₁' : HCThetaOneHomBundled theta P₁' P₀')
    (p₀' : HCThetaOneHomBundled theta P₀' X')
    (_ : IsPresentationHC p₁ p₀) (_ : IsPresentationHC p₁' p₀')
    (_ : IsProjHCBundled theta P₀) (_ : IsProjHCBundled theta P₁) :
    ∀ (a : HCThetaOneHomBundled theta X X'),
      ∃ (a₀ : HCThetaOneHomBundled theta P₀ P₀')
        (a₁ : HCThetaOneHomBundled theta P₁ P₁'),
        HCThetaOne_comp p₀' a₀ = HCThetaOne_comp a p₀ ∧
        HCThetaOne_comp a₀ p₁ = HCThetaOne_comp p₁' a₁ := by
  rename_i hp hp' hP₀ hP₁
  intro a


  obtain ⟨a₀_lift, ha₀⟩ := hP₀ P₀'.1 X'.1 P₀'.2 X'.2 p₀' (HCThetaOne_comp a p₀) hp'.1

  obtain ⟨K, ι, hι_inj, hK_incl, hK_surj⟩ := HCThetaOne_kernel_in_category p₀'

  have h_comp_zero : ∀ m : P₁.1.carrier,
      p₀'.toLinearMap (a₀_lift.toLinearMap (p₁.toLinearMap m)) = 0 := by
    intro m
    rw [ha₀ (p₁.toLinearMap m)]
    show (HCThetaOne_comp a p₀).toLinearMap (p₁.toLinearMap m) = 0
    simp only [HCThetaOne_comp]
    show a.toLinearMap (p₀.toLinearMap (p₁.toLinearMap m)) = 0
    rw [hp.2.1 m, map_zero]


  have h_factor_comp : ∀ m : P₁.1.carrier,
      ∃ n : K.1.carrier, ι.toLinearMap n = a₀_lift.toLinearMap (p₁.toLinearMap m) :=
    fun m => hK_surj _ (h_comp_zero m)

  have h_factor_p1' : ∀ m : P₁'.1.carrier,
      ∃ n : K.1.carrier, ι.toLinearMap n = p₁'.toLinearMap m :=
    fun m => hK_surj _ (hp'.2.1 m)


  have h_p1'_surj_K : ∀ k : K.1.carrier,
      ∃ m : P₁'.1.carrier, ι.toLinearMap (Classical.choose (h_factor_p1' m)) = ι.toLinearMap k := by
    intro k
    obtain ⟨m, hm⟩ := hp'.2.2 (ι.toLinearMap k) (hK_incl k)
    exact ⟨m, by rw [Classical.choose_spec (h_factor_p1' m), hm]⟩


  let p₁'_K_fun : P₁'.1.carrier → K.1.carrier :=
    fun m => Classical.choose (h_factor_p1' m)
  have hp₁'_K_spec : ∀ m, ι.toLinearMap (p₁'_K_fun m) = p₁'.toLinearMap m :=
    fun m => Classical.choose_spec (h_factor_p1' m)


  have hp₁'_K_add : ∀ m₁ m₂, p₁'_K_fun (m₁ + m₂) = p₁'_K_fun m₁ + p₁'_K_fun m₂ := by
    intro m₁ m₂
    apply hι_inj
    rw [hp₁'_K_spec, map_add, map_add, hp₁'_K_spec, hp₁'_K_spec]
  have hp₁'_K_smul : ∀ (r : R) m, p₁'_K_fun (r • m) = r • p₁'_K_fun m := by
    intro r m
    apply hι_inj
    rw [hp₁'_K_spec, map_smul, map_smul, hp₁'_K_spec]
  let p₁'_K_lin : P₁'.1.carrier →ₗ[R] K.1.carrier :=
    { toFun := p₁'_K_fun
      map_add' := hp₁'_K_add
      map_smul' := hp₁'_K_smul }

  have hp₁'_K_left : ∀ (u : UniversalEnvelopingAlgebra R g) (m : P₁'.1.carrier),
      p₁'_K_lin (P₁'.1.leftAction u m) = K.1.leftAction u (p₁'_K_lin m) := by
    intro u m
    apply hι_inj
    show ι.toLinearMap (p₁'_K_fun (P₁'.1.leftAction u m)) = ι.toLinearMap (K.1.leftAction u (p₁'_K_fun m))
    rw [hp₁'_K_spec, p₁'.left_compat, ← hp₁'_K_spec m, ← ι.left_compat]
  have hp₁'_K_right : ∀ (u : (UniversalEnvelopingAlgebra R g)ᵐᵒᵖ) (m : P₁'.1.carrier),
      p₁'_K_lin (P₁'.1.rightAction u m) = K.1.rightAction u (p₁'_K_lin m) := by
    intro u m
    apply hι_inj
    show ι.toLinearMap (p₁'_K_fun (P₁'.1.rightAction u m)) = ι.toLinearMap (K.1.rightAction u (p₁'_K_fun m))
    rw [hp₁'_K_spec, p₁'.right_compat, ← hp₁'_K_spec m, ← ι.right_compat]
  let p₁'_K : HCThetaOneHomBundled theta P₁' K :=
    { toLinearMap := p₁'_K_lin
      left_compat := hp₁'_K_left
      right_compat := hp₁'_K_right }


  have hp₁'_K_surj : Function.Surjective p₁'_K.toLinearMap := by
    intro k
    obtain ⟨m, hm⟩ := hp'.2.2 (ι.toLinearMap k) (hK_incl k)
    refine ⟨m, ?_⟩
    apply hι_inj
    show ι.toLinearMap (p₁'_K_fun m) = ι.toLinearMap k
    rw [hp₁'_K_spec, hm]

  let comp_K_fun : P₁.1.carrier → K.1.carrier :=
    fun m => Classical.choose (h_factor_comp m)
  have hcomp_K_spec : ∀ m, ι.toLinearMap (comp_K_fun m) = a₀_lift.toLinearMap (p₁.toLinearMap m) :=
    fun m => Classical.choose_spec (h_factor_comp m)
  have hcomp_K_add : ∀ m₁ m₂, comp_K_fun (m₁ + m₂) = comp_K_fun m₁ + comp_K_fun m₂ := by
    intro m₁ m₂
    apply hι_inj
    rw [hcomp_K_spec, map_add, map_add, map_add, hcomp_K_spec, hcomp_K_spec]
  have hcomp_K_smul : ∀ (r : R) m, comp_K_fun (r • m) = r • comp_K_fun m := by
    intro r m
    apply hι_inj
    rw [hcomp_K_spec, map_smul, map_smul, map_smul, hcomp_K_spec]
  let comp_K_lin : P₁.1.carrier →ₗ[R] K.1.carrier :=
    { toFun := comp_K_fun
      map_add' := hcomp_K_add
      map_smul' := hcomp_K_smul }
  have hcomp_K_left : ∀ (u : UniversalEnvelopingAlgebra R g) (m : P₁.1.carrier),
      comp_K_lin (P₁.1.leftAction u m) = K.1.leftAction u (comp_K_lin m) := by
    intro u m
    apply hι_inj
    show ι.toLinearMap (comp_K_fun (P₁.1.leftAction u m)) = ι.toLinearMap (K.1.leftAction u (comp_K_fun m))
    rw [hcomp_K_spec, p₁.left_compat, a₀_lift.left_compat, ← hcomp_K_spec m, ← ι.left_compat]
  have hcomp_K_right : ∀ (u : (UniversalEnvelopingAlgebra R g)ᵐᵒᵖ) (m : P₁.1.carrier),
      comp_K_lin (P₁.1.rightAction u m) = K.1.rightAction u (comp_K_lin m) := by
    intro u m
    apply hι_inj
    show ι.toLinearMap (comp_K_fun (P₁.1.rightAction u m)) = ι.toLinearMap (K.1.rightAction u (comp_K_fun m))
    rw [hcomp_K_spec, p₁.right_compat, a₀_lift.right_compat, ← hcomp_K_spec m, ← ι.right_compat]
  let comp_K : HCThetaOneHomBundled theta P₁ K :=
    { toLinearMap := comp_K_lin
      left_compat := hcomp_K_left
      right_compat := hcomp_K_right }

  obtain ⟨a₁_lift, ha₁⟩ := hP₁ P₁'.1 K.1 P₁'.2 K.2 p₁'_K comp_K hp₁'_K_surj


  refine ⟨a₀_lift, a₁_lift, ?_, ?_⟩
  ·


    show HCThetaOne_comp p₀' a₀_lift = HCThetaOne_comp a p₀
    have h_eq : (HCThetaOne_comp p₀' a₀_lift).toLinearMap = (HCThetaOne_comp a p₀).toLinearMap := by
      ext m
      show p₀'.toLinearMap (a₀_lift.toLinearMap m) = (HCThetaOne_comp a p₀).toLinearMap m
      exact ha₀ m
    have : ∀ {M₁ M₂ θ hM₁ hM₂} (f g : @HCThetaOneHom R _ g _ _ M₁ M₂ θ hM₁ hM₂),
        f.toLinearMap = g.toLinearMap → f = g := by
      intro M₁ M₂ θ hM₁ hM₂ f g h
      cases f; cases g; congr 1
    exact this _ _ h_eq
  ·


    show HCThetaOne_comp a₀_lift p₁ = HCThetaOne_comp p₁' a₁_lift
    cases h1 : (HCThetaOne_comp a₀_lift p₁)
    cases h2 : (HCThetaOne_comp p₁' a₁_lift)
    congr 1
    have h1' := congr_arg HCThetaOneHom.toLinearMap h1
    have h2' := congr_arg HCThetaOneHom.toLinearMap h2
    simp at h1' h2'
    ext m

    have key : p₁'_K.toLinearMap (a₁_lift.toLinearMap m) = comp_K.toLinearMap m := ha₁ m
    have hι := congr_arg ι.toLinearMap key
    rw [show ι.toLinearMap (p₁'_K.toLinearMap (a₁_lift.toLinearMap m)) = p₁'.toLinearMap (a₁_lift.toLinearMap m) from hp₁'_K_spec _] at hι
    rw [show ι.toLinearMap (comp_K.toLinearMap m) = a₀_lift.toLinearMap (p₁.toLinearMap m) from hcomp_K_spec _] at hι
    rw [← h1', ← h2']
    show a₀_lift.toLinearMap (p₁.toLinearMap m) = p₁'.toLinearMap (a₁_lift.toLinearMap m)
    exact hι.symm

noncomputable instance LieModuleMor_ker_lieRingModule
    {X Y : LieModuleObj.{u_R, u_g, u_mod} R g}
    (f : LieModuleMor R g X Y) : LieRingModule g f.toLinearMap.ker where
  bracket x m := ⟨⁅x, m.1⁆, by
    simp [LinearMap.mem_ker]; rw [f.lie_compat, m.2, lie_zero]⟩
  add_lie x y m := Subtype.ext (add_lie x y m.1)
  lie_add x m n := Subtype.ext (lie_add x m.1 n.1)
  leibniz_lie x y m := Subtype.ext (leibniz_lie x y m.1)

noncomputable instance LieModuleMor_ker_lieModule
    {X Y : LieModuleObj.{u_R, u_g, u_mod} R g}
    (f : LieModuleMor R g X Y) : LieModule R g f.toLinearMap.ker where
  smul_lie r x m := by
    apply Subtype.ext; show ⁅r • x, m.1⁆ = r • ⁅x, m.1⁆; exact smul_lie r x m.1
  lie_smul r x m := by
    apply Subtype.ext; show ⁅x, r • m.1⁆ = r • ⁅x, m.1⁆; exact lie_smul r x m.1

noncomputable def LieModuleMor_kerObj
    {X Y : LieModuleObj.{u_R, u_g, u_mod} R g}
    (f : LieModuleMor R g X Y) : LieModuleObj.{u_R, u_g, u_mod} R g where
  carrier := f.toLinearMap.ker

noncomputable def LieModuleMor_corestrToKer
    {A B C : LieModuleObj.{u_R, u_g, u_mod} R g}
    (q₁ : LieModuleMor R g A B) (q₀ : LieModuleMor R g B C)
    (hcomp : ∀ m : A.carrier, q₀.toLinearMap (q₁.toLinearMap m) = 0) :
    LieModuleMor R g A (LieModuleMor_kerObj q₀) where
  toLinearMap := q₁.toLinearMap.codRestrict q₀.toLinearMap.ker (fun m => by
    simp [LinearMap.mem_ker]; exact hcomp m)
  lie_compat x m := by
    apply Subtype.ext
    show q₁.toLinearMap ⁅x, m⁆ = ⁅x, q₁.toLinearMap m⁆
    exact q₁.lie_compat x m

lemma LieModuleMor_corestrToKer_surj
    {A B C : LieModuleObj.{u_R, u_g, u_mod} R g}
    (q₁ : LieModuleMor R g A B) (q₀ : LieModuleMor R g B C)
    (hcomp : ∀ m : A.carrier, q₀.toLinearMap (q₁.toLinearMap m) = 0)
    (hexact : ∀ m : B.carrier, q₀.toLinearMap m = 0 → ∃ n : A.carrier, q₁.toLinearMap n = m) :
    Function.Surjective (LieModuleMor_corestrToKer q₁ q₀ hcomp).toLinearMap := by
  intro ⟨m, hm⟩
  simp [LinearMap.mem_ker] at hm
  obtain ⟨n, hn⟩ := hexact m hm
  exact ⟨n, Subtype.ext (by show q₁.toLinearMap n = m; exact hn)⟩

theorem O_lift_through_pres
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {Q₁ Q₀ Y Q₁' Q₀' Y' : LieModuleObj.{u_R, u_g, u_mod} R g}
    (q₁ : LieModuleMor R g Q₁ Q₀)
    (q₀ : LieModuleMor R g Q₀ Y)
    (q₁' : LieModuleMor R g Q₁' Q₀')
    (q₀' : LieModuleMor R g Q₀' Y')
    (hpres : IsPresentationO q₁ q₀) (hpres' : IsPresentationO q₁' q₀')
    (hproj₀ : IsProjO Q₀) (hproj₁ : IsProjO Q₁) :
    ∀ (b : LieModuleMor R g Y Y'),
      ∃ (b₀ : LieModuleMor R g Q₀ Q₀')
        (b₁ : LieModuleMor R g Q₁ Q₁'),
        LieModuleMor_comp q₀' b₀ = LieModuleMor_comp b q₀ ∧
        LieModuleMor_comp b₀ q₁ = LieModuleMor_comp q₁' b₁ := by
  intro b
  obtain ⟨hq₀_surj, hq₀q₁_zero, hq₀_exact⟩ := hpres
  obtain ⟨hq₀'_surj, hq₀'q₁'_zero, hq₀'_exact⟩ := hpres'

  let bq₀ := LieModuleMor_comp b q₀
  obtain ⟨b₀, hb₀⟩ := hproj₀ Q₀' Y' q₀' bq₀ hq₀'_surj

  have hb₀q₁_in_ker : ∀ m : Q₁.carrier, q₀'.toLinearMap (b₀.toLinearMap (q₁.toLinearMap m)) = 0 := by
    intro m; rw [hb₀]
    show b.toLinearMap (q₀.toLinearMap (q₁.toLinearMap m)) = 0
    rw [hq₀q₁_zero]; simp

  let b₀q₁_to_ker : LieModuleMor R g Q₁ (LieModuleMor_kerObj q₀') :=
    LieModuleMor_corestrToKer (LieModuleMor_comp b₀ q₁) q₀' (by
      intro m; show q₀'.toLinearMap (b₀.toLinearMap (q₁.toLinearMap m)) = 0
      exact hb₀q₁_in_ker m)

  let q₁'_to_ker := LieModuleMor_corestrToKer q₁' q₀' hq₀'q₁'_zero
  have hq₁'_to_ker_surj := LieModuleMor_corestrToKer_surj q₁' q₀' hq₀'q₁'_zero hq₀'_exact

  obtain ⟨b₁, hb₁⟩ := hproj₁ Q₁' (LieModuleMor_kerObj q₀') q₁'_to_ker b₀q₁_to_ker hq₁'_to_ker_surj
  refine ⟨b₀, b₁, ?_, ?_⟩
  ·
    apply LieModuleMor.ext'; ext m
    show q₀'.toLinearMap (b₀.toLinearMap m) = b.toLinearMap (q₀.toLinearMap m)
    exact hb₀ m
  ·
    apply LieModuleMor.ext'; ext m
    show b₀.toLinearMap (q₁.toLinearMap m) = q₁'.toLinearMap (b₁.toLinearMap m)
    have h := hb₁ m
    have h' := congr_arg Subtype.val h

    change q₁'.toLinearMap (b₁.toLinearMap m) = b₀.toLinearMap (q₁.toLinearMap m) at h'
    exact h'.symm

theorem HCThetaOne_pres_epi
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    {P₁ P₀ X : HCThetaOneObj.{u_R, u_g, u_mod} R g theta}
    (p₁ : HCThetaOneHomBundled theta P₁ P₀)
    (p₀ : HCThetaOneHomBundled theta P₀ X) :
    IsPresentationHC p₁ p₀ →
    ∀ {Y : HCThetaOneObj.{u_R, u_g, u_mod} R g theta}
      (f g : HCThetaOneHomBundled theta X Y),
      HCThetaOne_comp f p₀ = HCThetaOne_comp g p₀ → f = g := by
  intro ⟨hsurj, _, _⟩ _Y f' g' heq

  have hcomp_eq : (HCThetaOne_comp f' p₀).toLinearMap = (HCThetaOne_comp g' p₀).toLinearMap :=
    congr_arg (fun h => h.toLinearMap) heq

  have hext : f'.toLinearMap = g'.toLinearMap := by
    ext x
    obtain ⟨m, hm⟩ := hsurj x
    rw [← hm]
    have := LinearMap.ext_iff.mp hcomp_eq m
    simp [HCThetaOne_comp] at this
    exact this

  cases f'; cases g'; congr 1

theorem O_pres_epi
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {Q₁ Q₀ Y : LieModuleObj.{u_R, u_g, u_mod} R g}
    (q₁ : LieModuleMor R g Q₁ Q₀)
    (q₀ : LieModuleMor R g Q₀ Y) :
    IsPresentationO q₁ q₀ →
    ∀ {Z : LieModuleObj.{u_R, u_g, u_mod} R g}
      (f g : LieModuleMor R g Y Z),
      LieModuleMor_comp f q₀ = LieModuleMor_comp g q₀ → f = g := by
  intro ⟨hsurj, _, _⟩ _Z f' g' heq
  have hcomp_eq : (LieModuleMor_comp f' q₀).toLinearMap = (LieModuleMor_comp g' q₀).toLinearMap :=
    congr_arg (fun h => h.toLinearMap) heq
  have hext : f'.toLinearMap = g'.toLinearMap := by
    ext x
    obtain ⟨m, hm⟩ := hsurj x
    rw [← hm]
    have := LinearMap.ext_iff.mp hcomp_eq m
    simp [LieModuleMor_comp] at this
    exact this
  cases f'; cases g'; congr 1

theorem Tlambda_faithful_on_projHC_ax
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    {P₁ P₀ X Q₁ Q₀ Y : HCThetaOneObj.{u_R, u_g, u_mod} R g theta}
    (p₁ : HCThetaOneHomBundled theta P₁ P₀)
    (p₀ : HCThetaOneHomBundled theta P₀ X)
    (q₁ : HCThetaOneHomBundled theta Q₁ Q₀)
    (q₀ : HCThetaOneHomBundled theta Q₀ Y)
    (_ : IsPresentationHC p₁ p₀) (_ : IsPresentationHC q₁ q₀)
    (_ : IsProjHCBundled theta P₀) (_ : IsProjHCBundled theta P₁)
    (_ : IsProjHCBundled theta Q₀) (_ : IsProjHCBundled theta Q₁)
    (a₀ a₀' : HCThetaOneHomBundled theta P₀ Q₀) :
    LieModuleMor_comp (TlambdaMapBundled Tl q₀) (TlambdaMapBundled Tl a₀) =
    LieModuleMor_comp (TlambdaMapBundled Tl q₀) (TlambdaMapBundled Tl a₀') →
    a₀ = a₀' := by
  sorry

theorem Tlambda_five_lemma_inj
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    {P₁ P₀ X Q₁ Q₀ Y : HCThetaOneObj.{u_R, u_g, u_mod} R g theta}
    (p₁ : HCThetaOneHomBundled theta P₁ P₀)
    (p₀ : HCThetaOneHomBundled theta P₀ X)
    (q₁ : HCThetaOneHomBundled theta Q₁ Q₀)
    (q₀ : HCThetaOneHomBundled theta Q₀ Y)
    (hp : IsPresentationHC p₁ p₀) (hq : IsPresentationHC q₁ q₀)
    (hP₀ : IsProjHCBundled theta P₀) (hP₁ : IsProjHCBundled theta P₁)
    (hQ₀ : IsProjHCBundled theta Q₀) (hQ₁ : IsProjHCBundled theta Q₁)
    (a₀ a₀' : HCThetaOneHomBundled theta P₀ Q₀) :
    LieModuleMor_comp (TlambdaMapBundled Tl q₀) (TlambdaMapBundled Tl a₀) =
    LieModuleMor_comp (TlambdaMapBundled Tl q₀) (TlambdaMapBundled Tl a₀') →
    a₀ = a₀' :=
  Tlambda_faithful_on_projHC_ax Tl p₁ p₀ q₁ q₀ hp hq hP₀ hP₁ hQ₀ hQ₁ a₀ a₀'

theorem HCThetaOne_descent_through_pres
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    {P₁ P₀ X P₁' P₀' X' : HCThetaOneObj.{u_R, u_g, u_mod} R g theta}
    (p₁ : HCThetaOneHomBundled theta P₁ P₀)
    (p₀ : HCThetaOneHomBundled theta P₀ X)
    (p₁' : HCThetaOneHomBundled theta P₁' P₀')
    (p₀' : HCThetaOneHomBundled theta P₀' X')
    (hpres : IsPresentationHC p₁ p₀) (hpres' : IsPresentationHC p₁' p₀')
    (a₀ : HCThetaOneHomBundled theta P₀ P₀')
    (a₁ : HCThetaOneHomBundled theta P₁ P₁') :
    HCThetaOne_comp a₀ p₁ = HCThetaOne_comp p₁' a₁ →
    ∃ (a : HCThetaOneHomBundled theta X X'),
      HCThetaOne_comp p₀' a₀ = HCThetaOne_comp a p₀ := by
  intro hcompat
  obtain ⟨hp₀_surj, hp₀_comp, hp₀_exact⟩ := hpres
  obtain ⟨hp₀'_surj, hp₀'_comp, _⟩ := hpres'

  have hcompat_lm : ∀ n : P₁.1.carrier,
      a₀.toLinearMap (p₁.toLinearMap n) = p₁'.toLinearMap (a₁.toLinearMap n) := by
    intro n; exact LinearMap.ext_iff.mp (congr_arg HCThetaOneHom.toLinearMap hcompat) n

  have hker : ∀ m : P₀.1.carrier, p₀.toLinearMap m = 0 →
      p₀'.toLinearMap (a₀.toLinearMap m) = 0 := by
    intro m hm
    obtain ⟨n, hn⟩ := hp₀_exact m hm
    rw [← hn, hcompat_lm, hp₀'_comp]

  let e := p₀.toLinearMap.quotKerEquivOfSurjective hp₀_surj
  have hle : LinearMap.ker p₀.toLinearMap ≤
      LinearMap.ker (p₀'.toLinearMap.comp a₀.toLinearMap) := by
    intro m hm; simp [LinearMap.mem_ker] at hm ⊢; exact hker m hm
  let lifted := Submodule.liftQ _ (p₀'.toLinearMap.comp a₀.toLinearMap) hle
  let aLinMap : X.1.carrier →ₗ[R] X'.1.carrier := lifted.comp e.symm.toLinearMap

  have hfact : ∀ m : P₀.1.carrier,
      aLinMap (p₀.toLinearMap m) = p₀'.toLinearMap (a₀.toLinearMap m) := by
    intro m
    show lifted (e.symm (p₀.toLinearMap m)) = _
    rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
    simp [lifted, Submodule.liftQ_apply, LinearMap.comp_apply]

  have hleft : ∀ (u : UniversalEnvelopingAlgebra R g) (x : X.1.carrier),
      aLinMap ((X.1.leftAction u) x) = (X'.1.leftAction u) (aLinMap x) := by
    intro u x
    obtain ⟨m, hm⟩ := hp₀_surj x
    subst hm
    rw [← p₀.left_compat u m, hfact, hfact,
        a₀.left_compat u m, p₀'.left_compat u (a₀.toLinearMap m)]
  have hright : ∀ (u : (UniversalEnvelopingAlgebra R g)ᵐᵒᵖ) (x : X.1.carrier),
      aLinMap ((X.1.rightAction u) x) = (X'.1.rightAction u) (aLinMap x) := by
    intro u x
    obtain ⟨m, hm⟩ := hp₀_surj x
    subst hm
    rw [← p₀.right_compat u m, hfact, hfact,
        a₀.right_compat u m, p₀'.right_compat u (a₀.toLinearMap m)]
  let a : HCThetaOneHomBundled theta X X' :=
    ⟨aLinMap, hleft, hright⟩
  refine ⟨a, ?_⟩

  show HCThetaOne_comp p₀' a₀ = HCThetaOne_comp a p₀
  unfold HCThetaOne_comp
  congr 1
  ext m
  show p₀'.toLinearMap (a₀.toLinearMap m) = aLinMap (p₀.toLinearMap m)
  exact (hfact m).symm

theorem HCThetaOne_cokernel_exists
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    {P₁ P₀ : HCThetaOneObj.{u_R, u_g, u_mod} R g theta}
    (g' : HCThetaOneHomBundled theta P₁ P₀) :
    ∃ (X : HCThetaOneObj.{u_R, u_g, u_mod} R g theta)
      (p₀ : HCThetaOneHomBundled theta P₀ X),
      IsPresentationHC g' p₀ := by

  set S : Submodule R P₀.1.carrier := LinearMap.range g'.toLinearMap with hS_def

  have hS_left : ∀ (u : UniversalEnvelopingAlgebra R g) (s : P₀.1.carrier),
      s ∈ S → P₀.1.leftAction u s ∈ S := by
    intro u s ⟨n, hn⟩; exact ⟨P₁.1.leftAction u n, by rw [g'.left_compat, hn]⟩
  have hS_right : ∀ (u : (UniversalEnvelopingAlgebra R g)ᵐᵒᵖ) (s : P₀.1.carrier),
      s ∈ S → P₀.1.rightAction u s ∈ S := by
    intro u s ⟨n, hn⟩; exact ⟨P₁.1.rightAction u n, by rw [g'.right_compat, hn]⟩
  have hS_lc : ∀ u, S ≤ S.comap (P₀.1.leftAction u) := fun u _ hm => hS_left u _ hm
  have hS_rc : ∀ u, S ≤ S.comap (P₀.1.rightAction u) := fun u _ hm => hS_right u _ hm

  let Xbim : LieBimodule R g := {
    carrier := P₀.1.carrier ⧸ S
    leftAction := {
      toFun := fun u => S.mapQ S (P₀.1.leftAction u) (hS_lc u)
      map_one' := by
        apply LinearMap.ext; intro x; obtain ⟨m, rfl⟩ := S.mkQ_surjective x
        simp only [Submodule.mapQ_apply, Submodule.mkQ_apply]
        congr 1; exact LinearMap.congr_fun (map_one P₀.1.leftAction) m
      map_mul' := fun u v => by
        apply LinearMap.ext; intro x; obtain ⟨m, rfl⟩ := S.mkQ_surjective x
        simp only [Submodule.mapQ_apply, Submodule.mkQ_apply]
        congr 1; exact LinearMap.congr_fun (map_mul P₀.1.leftAction u v) m
      map_zero' := by
        apply LinearMap.ext; intro x; obtain ⟨m, rfl⟩ := S.mkQ_surjective x
        simp only [Submodule.mapQ_apply, Submodule.mkQ_apply, LinearMap.zero_apply]
        rw [show P₀.1.leftAction 0 = 0 from map_zero P₀.1.leftAction, LinearMap.zero_apply]
        exact S.mkQ.map_zero
      map_add' := fun u v => by
        apply LinearMap.ext; intro x; obtain ⟨m, rfl⟩ := S.mkQ_surjective x
        simp only [Submodule.mapQ_apply, Submodule.mkQ_apply, LinearMap.add_apply]
        rw [show P₀.1.leftAction (u + v) = P₀.1.leftAction u + P₀.1.leftAction v from
          map_add P₀.1.leftAction u v, LinearMap.add_apply]
        exact S.mkQ.map_add _ _
      commutes' := fun r => by
        apply LinearMap.ext; intro x; obtain ⟨m, rfl⟩ := S.mkQ_surjective x
        simp only [Submodule.mapQ_apply, Submodule.mkQ_apply,
          Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply]
        rw [show P₀.1.leftAction (r • 1) = r • P₀.1.leftAction 1 from
              map_smul P₀.1.leftAction r 1,
            show P₀.1.leftAction 1 = 1 from map_one P₀.1.leftAction,
            LinearMap.smul_apply]
        rfl }
    rightAction := {
      toFun := fun u => S.mapQ S (P₀.1.rightAction u) (hS_rc u)
      map_one' := by
        apply LinearMap.ext; intro x; obtain ⟨m, rfl⟩ := S.mkQ_surjective x
        simp only [Submodule.mapQ_apply, Submodule.mkQ_apply]
        congr 1; exact LinearMap.congr_fun (map_one P₀.1.rightAction) m
      map_mul' := fun u v => by
        apply LinearMap.ext; intro x; obtain ⟨m, rfl⟩ := S.mkQ_surjective x
        simp only [Submodule.mapQ_apply, Submodule.mkQ_apply]
        congr 1; exact LinearMap.congr_fun (map_mul P₀.1.rightAction u v) m
      map_zero' := by
        apply LinearMap.ext; intro x; obtain ⟨m, rfl⟩ := S.mkQ_surjective x
        simp only [Submodule.mapQ_apply, Submodule.mkQ_apply, LinearMap.zero_apply]
        rw [show P₀.1.rightAction 0 = 0 from map_zero P₀.1.rightAction, LinearMap.zero_apply]
        exact S.mkQ.map_zero
      map_add' := fun u v => by
        apply LinearMap.ext; intro x; obtain ⟨m, rfl⟩ := S.mkQ_surjective x
        simp only [Submodule.mapQ_apply, Submodule.mkQ_apply, LinearMap.add_apply]
        rw [show P₀.1.rightAction (u + v) = P₀.1.rightAction u + P₀.1.rightAction v from
          map_add P₀.1.rightAction u v, LinearMap.add_apply]
        exact S.mkQ.map_add _ _
      commutes' := fun r => by
        apply LinearMap.ext; intro x; obtain ⟨m, rfl⟩ := S.mkQ_surjective x
        simp only [Submodule.mapQ_apply, Submodule.mkQ_apply,
          Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply]
        rw [show P₀.1.rightAction (r • 1) = r • P₀.1.rightAction 1 from
              map_smul P₀.1.rightAction r 1,
            show P₀.1.rightAction 1 = 1 from map_one P₀.1.rightAction,
            LinearMap.smul_apply]
        rfl }
    actions_commute := fun u v q => by
      obtain ⟨m, rfl⟩ := S.mkQ_surjective q
      simp only [Submodule.mkQ_apply]
      exact congr_arg (Submodule.Quotient.mk (p := S)) (P₀.1.actions_commute u v m) }

  have hXbim : IsInHCThetaOne Xbim theta := {
    isHC := {
      locally_finite := fun q => by
        obtain ⟨m, rfl⟩ := S.mkQ_surjective q
        obtain ⟨T, hfin, hm, hstab⟩ := P₀.2.isHC.locally_finite m
        refine ⟨T.map S.mkQ, Module.Finite.map _ _, ⟨m, hm, rfl⟩, fun x s hs => ?_⟩
        obtain ⟨t, ht, rfl⟩ := hs
        refine ⟨P₀.1.adjointAction x t, hstab x t ht, ?_⟩


        show (S.mapQ S (P₀.1.leftAction ((UniversalEnvelopingAlgebra.ι R) x)) (hS_lc _)) (S.mkQ t) -
             (S.mapQ S (P₀.1.rightAction (MulOpposite.op ((UniversalEnvelopingAlgebra.ι R) x))) (hS_rc _)) (S.mkQ t) =
             S.mkQ (P₀.1.adjointAction x t)
        simp only [LieBimodule.adjointAction, LinearMap.sub_apply,
          Submodule.mapQ_apply, Submodule.mkQ_apply, map_sub]
    }
    right_annihilated := fun z q => by
      obtain ⟨m, rfl⟩ := S.mkQ_surjective q

      show (S.mapQ S (P₀.1.rightAction (MulOpposite.op (z : UniversalEnvelopingAlgebra R g)))
        (hS_rc _)) (S.mkQ m) = theta z • S.mkQ m
      simp only [Submodule.mapQ_apply, Submodule.mkQ_apply]
      rw [show theta z • Submodule.Quotient.mk m =
            Submodule.Quotient.mk (theta z • m) from (map_smul S.mkQ _ _).symm]
      exact congr_arg (Submodule.Quotient.mk (p := S)) (P₀.2.right_annihilated z m) }


  let X : HCThetaOneObj R g theta := ⟨Xbim, hXbim⟩
  let p₀_hom : HCThetaOneHomBundled theta P₀ X := {
    toLinearMap := S.mkQ
    left_compat := fun u m => by
      show S.mkQ (P₀.1.leftAction u m) =
        (S.mapQ S (P₀.1.leftAction u) (hS_lc u)) (S.mkQ m)
      simp only [Submodule.mapQ_apply, Submodule.mkQ_apply]
    right_compat := fun u m => by
      show S.mkQ (P₀.1.rightAction u m) =
        (S.mapQ S (P₀.1.rightAction u) (hS_rc u)) (S.mkQ m)
      simp only [Submodule.mapQ_apply, Submodule.mkQ_apply] }
  exact ⟨X, p₀_hom, by
    refine ⟨?_, ?_, ?_⟩

    · exact Submodule.mkQ_surjective S

    · intro m
      show S.mkQ (g'.toLinearMap m) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨m, rfl⟩

    · intro m hm
      have : S.mkQ m = 0 := hm
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
      exact this⟩

theorem O_cokernel_unique_iso
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {Q₁ Q₀ Z₁ Z₂ : LieModuleObj.{u_R, u_g, u_mod} R g}
    (q₁ : LieModuleMor R g Q₁ Q₀)
    (q₀ : LieModuleMor R g Q₀ Z₁)
    (f₀ : LieModuleMor R g Q₀ Z₂)
    (hpres₁ : IsPresentationO q₁ q₀)
    (hpres₂ : IsPresentationO q₁ f₀) :
    ∃ (iso : LieModuleMor R g Z₁ Z₂), IsIsoO iso := by

  obtain ⟨hq₀_surj, hq₀_zero, hq₀_exact⟩ := hpres₁
  obtain ⟨hf₀_surj, hf₀_zero, hf₀_exact⟩ := hpres₂


  have hf₀_vanish_ker_q₀ : ∀ m : Q₀.carrier,
      q₀.toLinearMap m = 0 → f₀.toLinearMap m = 0 := by
    intro m hm
    obtain ⟨n, hn⟩ := hq₀_exact m hm
    rw [← hn, hf₀_zero]

  have hq₀_vanish_ker_f₀ : ∀ m : Q₀.carrier,
      f₀.toLinearMap m = 0 → q₀.toLinearMap m = 0 := by
    intro m hm
    obtain ⟨n, hn⟩ := hf₀_exact m hm
    rw [← hn, hq₀_zero]


  have hker_q₀_sub_ker_f₀ : LinearMap.ker q₀.toLinearMap ≤ LinearMap.ker f₀.toLinearMap := by
    intro m hm
    rw [LinearMap.mem_ker] at hm ⊢
    exact hf₀_vanish_ker_q₀ m hm
  have hker_f₀_sub_ker_q₀ : LinearMap.ker f₀.toLinearMap ≤ LinearMap.ker q₀.toLinearMap := by
    intro m hm
    rw [LinearMap.mem_ker] at hm ⊢
    exact hq₀_vanish_ker_f₀ m hm


  have hϕ_exists : ∀ z : Z₁.carrier, ∃ m : Q₀.carrier,
      q₀.toLinearMap m = z := hq₀_surj
  have hψ_exists : ∀ z : Z₂.carrier, ∃ m : Q₀.carrier,
      f₀.toLinearMap m = z := hf₀_surj

  classical

  let ϕ_fun : Z₁.carrier → Z₂.carrier :=
    fun z => f₀.toLinearMap (hϕ_exists z).choose

  have hϕ_wd : ∀ (z : Z₁.carrier) (m : Q₀.carrier),
      q₀.toLinearMap m = z → f₀.toLinearMap m = ϕ_fun z := by
    intro z m hm
    have hpre := (hϕ_exists z).choose_spec

    have hdiff : q₀.toLinearMap (m - (hϕ_exists z).choose) = 0 := by
      rw [map_sub, hm, hpre, sub_self]

    have : f₀.toLinearMap (m - (hϕ_exists z).choose) = 0 :=
      hf₀_vanish_ker_q₀ _ hdiff
    rw [map_sub] at this
    exact sub_eq_zero.mp this

  let ψ_fun : Z₂.carrier → Z₁.carrier :=
    fun z => q₀.toLinearMap (hψ_exists z).choose
  have hψ_wd : ∀ (z : Z₂.carrier) (m : Q₀.carrier),
      f₀.toLinearMap m = z → q₀.toLinearMap m = ψ_fun z := by
    intro z m hm
    have hpre := (hψ_exists z).choose_spec
    have hdiff : f₀.toLinearMap (m - (hψ_exists z).choose) = 0 := by
      rw [map_sub, hm, hpre, sub_self]
    have : q₀.toLinearMap (m - (hψ_exists z).choose) = 0 :=
      hq₀_vanish_ker_f₀ _ hdiff
    rw [map_sub] at this
    exact sub_eq_zero.mp this

  have hϕ_add : ∀ z₁ z₂ : Z₁.carrier, ϕ_fun (z₁ + z₂) = ϕ_fun z₁ + ϕ_fun z₂ := by
    intro z₁ z₂

    have hm₁ := (hϕ_exists z₁).choose_spec
    have hm₂ := (hϕ_exists z₂).choose_spec

    have hsum : q₀.toLinearMap ((hϕ_exists z₁).choose + (hϕ_exists z₂).choose) = z₁ + z₂ := by
      rw [map_add, hm₁, hm₂]
    rw [← hϕ_wd (z₁ + z₂) _ hsum, map_add]
  have hϕ_smul : ∀ (r : R) (z : Z₁.carrier), ϕ_fun (r • z) = r • ϕ_fun z := by
    intro r z
    have hm := (hϕ_exists z).choose_spec
    have hsmul : q₀.toLinearMap (r • (hϕ_exists z).choose) = r • z := by
      rw [map_smul, hm]
    rw [← hϕ_wd (r • z) _ hsmul, map_smul]

  let ϕ_lin : Z₁.carrier →ₗ[R] Z₂.carrier :=
    { toFun := ϕ_fun
      map_add' := hϕ_add
      map_smul' := hϕ_smul }

  have hψ_add : ∀ z₁ z₂ : Z₂.carrier, ψ_fun (z₁ + z₂) = ψ_fun z₁ + ψ_fun z₂ := by
    intro z₁ z₂
    have hm₁ := (hψ_exists z₁).choose_spec
    have hm₂ := (hψ_exists z₂).choose_spec
    have hsum : f₀.toLinearMap ((hψ_exists z₁).choose + (hψ_exists z₂).choose) = z₁ + z₂ := by
      rw [map_add, hm₁, hm₂]
    rw [← hψ_wd (z₁ + z₂) _ hsum, map_add]
  have hψ_smul : ∀ (r : R) (z : Z₂.carrier), ψ_fun (r • z) = r • ψ_fun z := by
    intro r z
    have hm := (hψ_exists z).choose_spec
    have hsmul : f₀.toLinearMap (r • (hψ_exists z).choose) = r • z := by
      rw [map_smul, hm]
    rw [← hψ_wd (r • z) _ hsmul, map_smul]
  let ψ_lin : Z₂.carrier →ₗ[R] Z₁.carrier :=
    { toFun := ψ_fun
      map_add' := hψ_add
      map_smul' := hψ_smul }

  have hϕ_lie : ∀ (x : g) (z : Z₁.carrier),
      ϕ_lin (⁅x, z⁆) = ⁅x, ϕ_lin z⁆ := by
    intro x z
    show ϕ_fun (⁅x, z⁆) = ⁅x, ϕ_fun z⁆
    have hm := (hϕ_exists z).choose_spec

    have hpre : q₀.toLinearMap ⁅x, (hϕ_exists z).choose⁆ = ⁅x, z⁆ := by
      rw [q₀.lie_compat, hm]

    rw [← hϕ_wd (⁅x, z⁆) _ hpre]

    rw [f₀.lie_compat]


  have hψ_lie : ∀ (x : g) (z : Z₂.carrier),
      ψ_lin (⁅x, z⁆) = ⁅x, ψ_lin z⁆ := by
    intro x z
    show ψ_fun (⁅x, z⁆) = ⁅x, ψ_fun z⁆
    have hm := (hψ_exists z).choose_spec
    have hpre : f₀.toLinearMap ⁅x, (hψ_exists z).choose⁆ = ⁅x, z⁆ := by
      rw [f₀.lie_compat, hm]
    rw [← hψ_wd (⁅x, z⁆) _ hpre]
    rw [q₀.lie_compat]

  let ϕ_mor : LieModuleMor R g Z₁ Z₂ := ⟨ϕ_lin, hϕ_lie⟩
  let ψ_mor : LieModuleMor R g Z₂ Z₁ := ⟨ψ_lin, hψ_lie⟩

  have h_left_inv : ∀ m : Z₁.carrier, ψ_mor.toLinearMap (ϕ_mor.toLinearMap m) = m := by
    intro z
    show ψ_fun (ϕ_fun z) = z


    have step : q₀.toLinearMap (hϕ_exists z).choose = ψ_fun (ϕ_fun z) :=
      hψ_wd (ϕ_fun z) (hϕ_exists z).choose rfl
    rw [← step]
    exact (hϕ_exists z).choose_spec
  have h_right_inv : ∀ m : Z₂.carrier, ϕ_mor.toLinearMap (ψ_mor.toLinearMap m) = m := by
    intro z
    show ϕ_fun (ψ_fun z) = z
    have step : f₀.toLinearMap (hψ_exists z).choose = ϕ_fun (ψ_fun z) :=
      hϕ_wd (ψ_fun z) (hψ_exists z).choose rfl
    rw [← step]
    exact (hψ_exists z).choose_spec
  exact ⟨ϕ_mor, ψ_mor, h_left_inv, h_right_inv⟩

theorem O_cokernel_in_image
    {R : Type u_R} [CommRing R] {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {theta : CenterCharacter R g}
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    {P₁ P₀ : HCThetaOneObj.{u_R, u_g, u_mod} R g theta}
    (g' : HCThetaOneHomBundled theta P₁ P₀) :
    IsProjHCBundled theta P₀ → IsProjHCBundled theta P₁ →
    ∀ (Y : LieModuleObj.{u_R, u_g, u_mod} R g)
      (f₀ : LieModuleMor R g (TlambdaObjBundled Tl P₀) Y),
      IsPresentationO (TlambdaMapBundled Tl g') f₀ →
      ∃ (X : HCThetaOneObj.{u_R, u_g, u_mod} R g theta)
        (iso : LieModuleMor R g (TlambdaObjBundled Tl X) Y),
        IsIsoO iso := by
  intro _hP₀ _hP₁ Y f₀ hpresY

  obtain ⟨X, p₀, hpresX⟩ := HCThetaOne_cokernel_exists g'

  have hpresO : IsPresentationO (TlambdaMapBundled Tl g') (TlambdaMapBundled Tl p₀) :=
    Tlambda_right_exact Tl g' p₀ hpresX


  obtain ⟨iso, hiso⟩ := O_cokernel_unique_iso (TlambdaMapBundled Tl g')
    (TlambdaMapBundled Tl p₀) f₀ hpresO hpresY
  exact ⟨X, iso, hiso⟩

theorem Tlambda_prop_25_10_application
    [IsNoetherianRing R]
    [LieAlgebra.IsSemisimple R g] [Module.Finite R g]
    {D : TriangularDecomposition R g}
    {rd : PositiveRootData D}
    (_wg : WeylGroupData D)
    (theta : CenterCharacter R g)
    (lam : D.𝔥 →ₗ[R] R)
    (_hdom : IsDominantWeightLE rd _wg lam)
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta) :

    ∀ (Y₁ Y₂ : LieBimodule.{u_R, u_g, u_mod} R g)
      (hY₁ : IsInHCThetaOne Y₁ theta) (hY₂ : IsInHCThetaOne Y₂ theta),
    Function.Bijective (fun (f : HCThetaOneHom Y₁ Y₂ theta hY₁ hY₂) =>
      Tl.applyHom f) := by

  have h := proposition_25_10
    (ObjA := HCThetaOneObj.{u_R, u_g, u_mod} R g theta)
    (ObjB := LieModuleObj.{u_R, u_g, u_mod} R g)
    (HomA := HCThetaOneHomBundled theta)
    (HomB := LieModuleMor R g)
    (T_obj := TlambdaObjBundled Tl)
    (T_map := fun f => TlambdaMapBundled Tl f)
    (IsProjA := IsProjHCBundled theta)
    (_IsProjB := IsProjO)
    (compA := fun g f => HCThetaOne_comp g f)
    (compB := fun g f => LieModuleMor_comp g f)
    (fun g f => Tlambda_functorial Tl g f)
    (idA := HCThetaOne_id)
    (idB := LieModuleMor_id)
    (fun A => Tlambda_preserves_id Tl A)
    (IsPresentationA := fun p₁ p₀ => IsPresentationHC p₁ p₀)
    (IsPresentationB := fun q₁ q₀ => IsPresentationO q₁ q₀)
    HCThetaOne_enough_proj
    (Tlambda_preserves_proj Tl)
    (fun p₁ p₀ h => Tlambda_right_exact Tl p₁ p₀ h)
    (Tlambda_ff_on_proj Tl)
    (IsIsoB := fun f => IsIsoO f)
    (fun p₁ p₀ p₁' p₀' hp hp' hP₀ hP₁ a =>
      HCThetaOne_lift_through_pres p₁ p₀ p₁' p₀' hp hp' hP₀ hP₁ a)
    (fun q₁ q₀ q₁' q₀' hq hq' hQ₀ hQ₁ b =>
      O_lift_through_pres q₁ q₀ q₁' q₀' hq hq' hQ₀ hQ₁ b)
    (fun p₁ p₀ hp => HCThetaOne_pres_epi p₁ p₀ hp)
    (fun q₁ q₀ hq => O_pres_epi q₁ q₀ hq)
    (fun p₁ p₀ q₁ q₀ hp hq hP₀ hP₁ hQ₀ hQ₁ a₀ a₀' h =>
      Tlambda_five_lemma_inj Tl p₁ p₀ q₁ q₀ hp hq hP₀ hP₁ hQ₀ hQ₁ a₀ a₀' h)
    (fun p₁ p₀ p₁' p₀' hp hp' a₀ a₁ hc =>
      HCThetaOne_descent_through_pres p₁ p₀ p₁' p₀' hp hp' a₀ a₁ hc)
    (fun g' hP₀ hP₁ Y f₀ hpres =>
      O_cokernel_in_image Tl g' hP₀ hP₁ Y f₀ hpres)

  obtain ⟨hff, _, _⟩ := h

  intro Y₁ Y₂ hY₁ hY₂
  exact hff ⟨Y₁, hY₁⟩ ⟨Y₂, hY₂⟩

noncomputable def adjunction_unit_Tl_iso
    {R : Type u_R} [CommRing R]
    {g : Type u_g} [LieRing g] [LieAlgebra R g]
    (theta : CenterCharacter R g)
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    (Hl : HlambdaData.{u_R, u_g, u_mod} theta)
    (Y : LieBimodule.{u_R, u_g, u_mod} R g)
    (hY : IsInHCThetaOne Y theta) :
    LieModuleIso R g (Tl.applyObj Y hY)
      (Tl.applyObj (Hl.applyObj (Tl.applyObj Y hY)) (Hl.inHCThetaOne (Tl.applyObj Y hY))) :=
  sorry

theorem adjunction_unit_iso_of_fully_faithful
    {R : Type u_R} [CommRing R]
    {g : Type u_g} [LieRing g] [LieAlgebra R g]
    (theta : CenterCharacter R g)
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    (Hl : HlambdaData.{u_R, u_g, u_mod} theta)
    (hff : ∀ (Y₁ Y₂ : LieBimodule.{u_R, u_g, u_mod} R g)
             (hY₁ : IsInHCThetaOne Y₁ theta) (hY₂ : IsInHCThetaOne Y₂ theta),
           Function.Bijective (fun (f : HCThetaOneHom Y₁ Y₂ theta hY₁ hY₂) =>
             Tl.applyHom f))
    (Y : LieBimodule.{u_R, u_g, u_mod} R g)
    (hY : IsInHCThetaOne Y theta) :
    ∃ (isoF : HCThetaOneHom Y (Hl.applyObj (Tl.applyObj Y hY)) theta hY (Hl.inHCThetaOne (Tl.applyObj Y hY)))
      (isoB : HCThetaOneHom (Hl.applyObj (Tl.applyObj Y hY)) Y theta (Hl.inHCThetaOne (Tl.applyObj Y hY)) hY),
      (∀ m : Y.carrier, isoB.toLinearMap (isoF.toLinearMap m) = m) ∧
      (∀ m : (Hl.applyObj (Tl.applyObj Y hY)).carrier, isoF.toLinearMap (isoB.toLinearMap m) = m) := by

  set HlTlY := Hl.applyObj (Tl.applyObj Y hY)
  set hHlTlY := Hl.inHCThetaOne (Tl.applyObj Y hY)

  set iso := adjunction_unit_Tl_iso theta Tl Hl Y hY

  set φ := iso.forward
  set ψ := iso.backward

  have hsurj_F := (hff Y HlTlY hY hHlTlY).2
  have hsurj_B := (hff HlTlY Y hHlTlY hY).2
  obtain ⟨fF, hfF_eq⟩ := hsurj_F φ
  obtain ⟨fB, hfB_eq⟩ := hsurj_B ψ

  let comp_BF : HCThetaOneHom Y Y theta hY hY :=
    { toLinearMap := fB.toLinearMap.comp fF.toLinearMap
      left_compat := fun u m => by
        simp only [LinearMap.comp_apply]
        rw [fF.left_compat, fB.left_compat]
      right_compat := fun u m => by
        simp only [LinearMap.comp_apply]
        rw [fF.right_compat, fB.right_compat] }

  let id_Y : HCThetaOneHom Y Y theta hY hY :=
    { toLinearMap := LinearMap.id
      left_compat := fun _u _m => rfl
      right_compat := fun _u _m => rfl }


  have h_comp_lm : (Tl.applyHom comp_BF).toLinearMap =
      (Tl.applyHom fB).toLinearMap.comp (Tl.applyHom fF).toLinearMap :=
    Tl.applyHom_comp fB fF comp_BF rfl

  rw [show Tl.applyHom fF = φ from hfF_eq, show Tl.applyHom fB = ψ from hfB_eq] at h_comp_lm


  have h_ψφ_id : ψ.toLinearMap.comp φ.toLinearMap = LinearMap.id := by
    ext m
    exact iso.left_inv m

  have h_id_lm : (Tl.applyHom id_Y).toLinearMap = LinearMap.id :=
    Tl.applyHom_id id_Y rfl

  have h_same_lm : (Tl.applyHom comp_BF).toLinearMap = (Tl.applyHom id_Y).toLinearMap := by
    rw [h_comp_lm, h_ψφ_id, h_id_lm]

  have hinj := (hff Y Y hY hY).1
  have h_eq_BF : comp_BF = id_Y := by
    apply hinj
    show Tl.applyHom comp_BF = Tl.applyHom id_Y
    have : ∀ (f₁ f₂ : LieModuleMor R g (Tl.applyObj Y hY) (Tl.applyObj Y hY)),
        f₁.toLinearMap = f₂.toLinearMap → f₁ = f₂ := fun f₁ f₂ h => by
      cases f₁; cases f₂; congr
    exact this _ _ h_same_lm

  have h_linmap_BF : fB.toLinearMap.comp fF.toLinearMap = LinearMap.id := by
    have := congr_arg HCThetaOneHom.toLinearMap h_eq_BF
    exact this

  let comp_FB : HCThetaOneHom HlTlY HlTlY theta hHlTlY hHlTlY :=
    { toLinearMap := fF.toLinearMap.comp fB.toLinearMap
      left_compat := fun u m => by
        simp only [LinearMap.comp_apply]
        rw [fB.left_compat, fF.left_compat]
      right_compat := fun u m => by
        simp only [LinearMap.comp_apply]
        rw [fB.right_compat, fF.right_compat] }
  let id_HlTlY : HCThetaOneHom HlTlY HlTlY theta hHlTlY hHlTlY :=
    { toLinearMap := LinearMap.id
      left_compat := fun _u _m => rfl
      right_compat := fun _u _m => rfl }
  have h_comp_FB_lm : (Tl.applyHom comp_FB).toLinearMap =
      (Tl.applyHom fF).toLinearMap.comp (Tl.applyHom fB).toLinearMap :=
    Tl.applyHom_comp fF fB comp_FB rfl
  rw [show Tl.applyHom fF = φ from hfF_eq, show Tl.applyHom fB = ψ from hfB_eq] at h_comp_FB_lm
  have h_φψ_id : φ.toLinearMap.comp ψ.toLinearMap = LinearMap.id := by
    ext m
    exact iso.right_inv m
  have h_id_HlTlY_lm : (Tl.applyHom id_HlTlY).toLinearMap = LinearMap.id :=
    Tl.applyHom_id id_HlTlY rfl
  have h_same_FB_lm : (Tl.applyHom comp_FB).toLinearMap = (Tl.applyHom id_HlTlY).toLinearMap := by
    rw [h_comp_FB_lm, h_φψ_id, h_id_HlTlY_lm]
  have hinj2 := (hff HlTlY HlTlY hHlTlY hHlTlY).1
  have h_eq_FB : comp_FB = id_HlTlY := by
    apply hinj2
    show Tl.applyHom comp_FB = Tl.applyHom id_HlTlY
    have : ∀ (f₁ f₂ : LieModuleMor R g (Tl.applyObj HlTlY hHlTlY) (Tl.applyObj HlTlY hHlTlY)),
        f₁.toLinearMap = f₂.toLinearMap → f₁ = f₂ := fun f₁ f₂ h => by
      cases f₁; cases f₂; congr
    exact this _ _ h_same_FB_lm
  have h_linmap_FB : fF.toLinearMap.comp fB.toLinearMap = LinearMap.id := by
    have := congr_arg HCThetaOneHom.toLinearMap h_eq_FB
    exact this

  refine ⟨fF, fB, fun m => ?_, fun m => ?_⟩
  · have := LinearMap.ext_iff.mp h_linmap_BF m
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    exact this
  · have := LinearMap.ext_iff.mp h_linmap_FB m
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    exact this

theorem Tlambda_unit_isomorphism
    [IsNoetherianRing R]
    [LieAlgebra.IsSemisimple R g] [Module.Finite R g]
    {D : TriangularDecomposition R g}
    {rd : PositiveRootData D}
    (_wg : WeylGroupData D)
    (theta : CenterCharacter R g)
    (lam : D.𝔥 →ₗ[R] R)
    (_hdom : IsDominantWeightLE rd _wg lam)
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    (Hl : HlambdaData.{u_R, u_g, u_mod} theta) :
    ∀ (Y : LieBimodule.{u_R, u_g, u_mod} R g)
      (hY : IsInHCThetaOne Y theta),
      let TlY := Tl.applyObj Y hY
      let HlTlY := Hl.applyObj TlY
      let hHlTlY := Hl.inHCThetaOne TlY
      ∃ (isoF : HCThetaOneHom Y HlTlY theta hY hHlTlY)
        (isoB : HCThetaOneHom HlTlY Y theta hHlTlY hY),
        (∀ m : Y.carrier, isoB.toLinearMap (isoF.toLinearMap m) = m) ∧
        (∀ m : HlTlY.carrier, isoF.toLinearMap (isoB.toLinearMap m) = m) := by

  have hff := Tlambda_prop_25_10_application _wg theta lam _hdom Tl
  intro Y hY
  exact adjunction_unit_iso_of_fully_faithful theta Tl Hl hff Y hY

theorem adjunction_counit_iso_on_essential_image
    {R : Type u_R} [CommRing R]
    {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {D : TriangularDecomposition R g}
    {rd : PositiveRootData D}
    (theta : CenterCharacter R g)
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    (Hl : HlambdaData.{u_R, u_g, u_mod} theta)
    (hff : ∀ (Y₁ Y₂ : LieBimodule.{u_R, u_g, u_mod} R g)
             (hY₁ : IsInHCThetaOne Y₁ theta) (hY₂ : IsInHCThetaOne Y₂ theta),
           Function.Bijective (fun (f : HCThetaOneHom Y₁ Y₂ theta hY₁ hY₂) =>
             Tl.applyHom f))
    (hunit : ∀ (Y : LieBimodule.{u_R, u_g, u_mod} R g)
               (hY : IsInHCThetaOne Y theta),
             let TlY := Tl.applyObj Y hY
             let HlTlY := Hl.applyObj TlY
             let hHlTlY := Hl.inHCThetaOne TlY
             ∃ (isoF : HCThetaOneHom Y HlTlY theta hY hHlTlY)
               (isoB : HCThetaOneHom HlTlY Y theta hHlTlY hY),
               (∀ m : Y.carrier, isoB.toLinearMap (isoF.toLinearMap m) = m) ∧
               (∀ m : HlTlY.carrier, isoF.toLinearMap (isoB.toLinearMap m) = m))
    (X : LieModuleObj.{u_R, u_g, u_mod} R g)
    (hX : IsInO_Lambda rd theta Tl X) :
    Nonempty (LieModuleIso R g (Tl.applyObj (Hl.applyObj X) (Hl.inHCThetaOne X)) X) := by
  sorry

theorem Tlambda_counit_isomorphism
    [IsNoetherianRing R]
    [LieAlgebra.IsSemisimple R g] [Module.Finite R g]
    {D : TriangularDecomposition R g}
    {rd : PositiveRootData D}
    (_wg : WeylGroupData D)
    (theta : CenterCharacter R g)
    (lam : D.𝔥 →ₗ[R] R)
    (_hdom : IsDominantWeightLE rd _wg lam)
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    (Hl : HlambdaData.{u_R, u_g, u_mod} theta) :
    ∀ (X : LieModuleObj.{u_R, u_g, u_mod} R g),
      IsInO_Lambda rd theta Tl X →
      let Y := Hl.applyObj X
      let hY := Hl.inHCThetaOne X
      Nonempty (LieModuleIso R g (Tl.applyObj Y hY) X) := by

  have hff := Tlambda_prop_25_10_application _wg theta lam _hdom Tl

  have hunit : ∀ (Y : LieBimodule.{u_R, u_g, u_mod} R g)
                 (hY : IsInHCThetaOne Y theta),
               let TlY := Tl.applyObj Y hY
               let HlTlY := Hl.applyObj TlY
               let hHlTlY := Hl.inHCThetaOne TlY
               ∃ (isoF : HCThetaOneHom Y HlTlY theta hY hHlTlY)
                 (isoB : HCThetaOneHom HlTlY Y theta hHlTlY hY),
                 (∀ m : Y.carrier, isoB.toLinearMap (isoF.toLinearMap m) = m) ∧
                 (∀ m : HlTlY.carrier, isoF.toLinearMap (isoB.toLinearMap m) = m) :=
    fun Y hY => adjunction_unit_iso_of_fully_faithful theta Tl Hl hff Y hY
  intro X hX
  exact adjunction_counit_iso_on_essential_image theta Tl Hl hff hunit X hX

theorem bernstein_gelfand_25_8_ii
    [IsNoetherianRing R]
    [LieAlgebra.IsSemisimple R g] [Module.Finite R g]
    {rd : PositiveRootData D}
    (_wg : WeylGroupData D)
    (theta : CenterCharacter R g)
    (lam : D.𝔥 →ₗ[R] R)
    (_hdom : IsDominantWeightLE rd _wg lam)
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    (Hl : HlambdaData.{u_R, u_g, u_mod} theta) :


    (∀ (Y₁ Y₂ : LieBimodule.{u_R, u_g, u_mod} R g)
      (hY₁ : IsInHCThetaOne Y₁ theta) (hY₂ : IsInHCThetaOne Y₂ theta),
    Function.Bijective (fun (f : HCThetaOneHom Y₁ Y₂ theta hY₁ hY₂) =>
      Tl.applyHom f))
    ∧


    (∀ (Y : LieBimodule.{u_R, u_g, u_mod} R g)
      (hY : IsInHCThetaOne Y theta),
      let TlY := Tl.applyObj Y hY
      let HlTlY := Hl.applyObj TlY
      let hHlTlY := Hl.inHCThetaOne TlY
      ∃ (isoF : HCThetaOneHom Y HlTlY theta hY hHlTlY)
        (isoB : HCThetaOneHom HlTlY Y theta hHlTlY hY),
        (∀ m : Y.carrier, isoB.toLinearMap (isoF.toLinearMap m) = m) ∧
        (∀ m : HlTlY.carrier, isoF.toLinearMap (isoB.toLinearMap m) = m))
    ∧


    (∀ (X : LieModuleObj.{u_R, u_g, u_mod} R g),
      IsInO_Lambda rd theta Tl X →
      let Y := Hl.applyObj X
      let hY := Hl.inHCThetaOne X
      Nonempty (LieModuleIso R g (Tl.applyObj Y hY) X)) :=
  ⟨Tlambda_prop_25_10_application _wg theta lam _hdom Tl,
   Tlambda_unit_isomorphism _wg theta lam _hdom Tl Hl,
   Tlambda_counit_isomorphism _wg theta lam _hdom Tl Hl⟩

theorem theorem_23_6_regular_block_eq
    {R : Type u_R} [CommRing R]
    {g : Type u_g} [LieRing g] [LieAlgebra R g]
    {D : TriangularDecomposition R g}
    {rd : PositiveRootData D}
    (wg : WeylGroupData D)
    (cd : RootCorootData rd)
    (theta : CenterCharacter R g)
    (lam : D.𝔥 →ₗ[R] R)
    (_hdom : IsDominantWeightLE rd wg lam)
    (_hreg : IsRegularWeight wg cd lam)
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    (X : LieModuleObj.{u_R, u_g, u_mod} R g)
    (hBlock : IsInBlock_LambdaPlusP rd X theta) :
    IsInO_Lambda rd theta Tl X := by
  sorry

theorem bernstein_gelfand_25_8_i
    [IsNoetherianRing R]
    [LieAlgebra.IsSemisimple R g] [Module.Finite R g]
    {rd : PositiveRootData D}
    (wg : WeylGroupData D)
    (cd : RootCorootData rd)
    (theta : CenterCharacter R g)
    (lam : D.𝔥 →ₗ[R] R)
    (_hdom : IsDominantWeightLE rd wg lam)
    (_hreg : IsRegularWeight wg cd lam)
    (Tl : TlambdaData.{u_R, u_g, u_mod} theta)
    (Hl : HlambdaData.{u_R, u_g, u_mod} theta) :

    (∀ (Y₁ Y₂ : LieBimodule.{u_R, u_g, u_mod} R g)
       (hY₁ : IsInHCThetaOne Y₁ theta) (hY₂ : IsInHCThetaOne Y₂ theta),
     Function.Bijective (fun (f : HCThetaOneHom Y₁ Y₂ theta hY₁ hY₂) =>
       Tl.applyHom f))
    ∧


    (∀ (X : LieModuleObj.{u_R, u_g, u_mod} R g),
     IsInBlock_LambdaPlusP rd X theta →
     let Y := Hl.applyObj X
     let hY := Hl.inHCThetaOne X
     Nonempty (LieModuleIso R g (Tl.applyObj Y hY) X)) := by


  obtain ⟨hff, _, hcounit⟩ := bernstein_gelfand_25_8_ii wg theta lam _hdom Tl Hl
  refine ⟨hff, ?_⟩
  intro X hBlock


  have hInOLambda : IsInO_Lambda rd theta Tl X :=
    theorem_23_6_regular_block_eq wg cd theta lam _hdom _hreg Tl X hBlock
  exact hcounit X hInOLambda

end Theorem25_8

section Corollary25_11

def IsKFiniteVector
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module R V]
    (π : Representation R G V) (K : Subgroup G) (v : V) : Prop :=
  (Submodule.span R (Set.range (fun k : K => π k v))).FG

def IsAdmissibleRepresentation
    {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module R V]
    (π : Representation R G V) (K : Subgroup G) : Prop :=
  ∀ v : V, IsKFiniteVector π K v →
    ∃ (S : Submodule R V), Module.Finite R S ∧ v ∈ S ∧
      ∀ (k : K) (s : V), s ∈ S → π (k : G) s ∈ S

structure RealizingRepData
    (theta : CenterCharacter R g)
    (M : LieBimodule.{u_R, u_g, u_mod} R g)
    (_hM : IsInHCThetaOne M theta) where
  G : Type*
  [instGroupG : Group G]
  [instTopG : TopologicalSpace G]
  [instTopGroupG : IsTopologicalGroup G]
  [instSCG : SimplyConnectedSpace G]
  K : Subgroup G
  [instCompactK : CompactSpace K]
  V : Type*
  [instNACGV : NormedAddCommGroup V]
  [instIPSV : InnerProductSpace ℂ V]
  [instCompleteV : CompleteSpace V]
  [instModRV : Module R V]
  [instLieRingModuleGV : LieRingModule g V]
  [instLieModuleGV : LieModule R g V]
  π : Representation R G V
  admissible : IsAdmissibleRepresentation π K
  kFinBimod : LieBimodule.{u_R, u_g, u_mod} R g
  kFinInHCTheta : IsInHCThetaOne kFinBimod theta
  embedding : kFinBimod.carrier →ₗ[R] V
  embedding_injective : Function.Injective embedding
  embedding_lie_compat : ∀ (x : g) (w : kFinBimod.carrier),
    embedding (kFinBimod.leftAction (UniversalEnvelopingAlgebra.ι R x) w) =
    instLieRingModuleGV.bracket x (embedding w)
  embedding_KFinite : ∀ w : kFinBimod.carrier, IsKFiniteVector π K (embedding w)
  isoForward : HCThetaOneHom kFinBimod M theta kFinInHCTheta _hM
  isoBackward : HCThetaOneHom M kFinBimod theta _hM kFinInHCTheta
  iso_left_inv : ∀ m : M.carrier,
    isoForward.toLinearMap (isoBackward.toLinearMap m) = m
  iso_right_inv : ∀ v : kFinBimod.carrier,
    isoBackward.toLinearMap (isoForward.toLinearMap v) = v

attribute [instance] RealizingRepData.instGroupG RealizingRepData.instTopG
  RealizingRepData.instTopGroupG RealizingRepData.instSCG
  RealizingRepData.instCompactK RealizingRepData.instNACGV
  RealizingRepData.instIPSV RealizingRepData.instCompleteV
  RealizingRepData.instModRV RealizingRepData.instLieRingModuleGV
  RealizingRepData.instLieModuleGV

universe u_G u_V

theorem corollary_6_13_sub_realizable
    {R : Type u_R} [CommRing R]
    {g : Type u_g} [LieRing g] [LieAlgebra R g]
    (theta : CenterCharacter R g)
    (M : LieBimodule.{u_R, u_g, u_mod} R g)
    (hM : IsInHCThetaOne M theta)
    (N : LieBimodule.{u_R, u_g, u_mod} R g)
    (hN : IsInHCThetaOne N theta)
    (f : HCThetaOneHom M N theta hM hN)
    (hf_inj : Function.Injective f.toLinearMap)
    (h_real : Nonempty (RealizingRepData.{u_R, u_g, u_mod, u_G, u_V} theta N hN)) :
    Nonempty (RealizingRepData.{u_R, u_g, u_mod, u_G, u_V} theta M hM) := by

  obtain ⟨rN⟩ := h_real


  exact ⟨{
    G := rN.G
    K := rN.K
    V := rN.V
    π := rN.π
    admissible := rN.admissible
    kFinBimod := M
    kFinInHCTheta := hM
    embedding := rN.embedding.comp (rN.isoBackward.toLinearMap.comp f.toLinearMap)
    embedding_injective := by
      intro a b hab
      simp only [LinearMap.coe_comp, Function.comp_apply] at hab
      have hinj_emb := rN.embedding_injective hab
      have hinj_back : Function.Injective rN.isoBackward.toLinearMap := by
        intro x y hxy
        have := congr_arg rN.isoForward.toLinearMap hxy
        simp only [rN.iso_left_inv] at this
        exact this
      exact hf_inj (hinj_back hinj_emb)
    embedding_lie_compat := by
      intro x w
      simp only [LinearMap.coe_comp, Function.comp_apply]


      rw [f.left_compat, rN.isoBackward.left_compat, rN.embedding_lie_compat]
    embedding_KFinite := fun m => by
      simp only [LinearMap.coe_comp, Function.comp_apply]
      exact rN.embedding_KFinite (rN.isoBackward.toLinearMap (f.toLinearMap m))
    isoForward := ⟨LinearMap.id, fun u m => rfl, fun u m => rfl⟩
    isoBackward := ⟨LinearMap.id, fun u m => rfl, fun u m => rfl⟩
    iso_left_inv := fun m => rfl
    iso_right_inv := fun v => rfl
  }⟩

theorem tensor_bimodule_has_realizing_data
    {R : Type u_R} [CommRing R]
    {g : Type u_g} [LieRing g] [LieAlgebra R g]
    [LieAlgebra.IsSemisimple R g] [Module.Finite R g]
    (theta : CenterCharacter R g)
    (P : LieBimodule.{u_R, u_g, u_mod} R g)
    (hP : IsInHCThetaOne P theta)
    (V : Type u_mod) [AddCommGroup V] [Module R V]
    (hTV : IsTensorProductBimoduleWithUTheta P theta V) :
    Nonempty (RealizingRepData.{u_R, u_g, u_mod, u_G, u_V} theta P hP) := by
  sorry

theorem hc_theta_one_tensor_bimodule_embeds
    {R : Type u_R} [CommRing R]
    {g : Type u_g} [LieRing g] [LieAlgebra R g]
    [LieAlgebra.IsSemisimple R g] [Module.Finite R g]
    (theta : CenterCharacter R g)
    (Y : LieBimodule.{u_R, u_g, u_mod} R g)
    (hY : IsInHCThetaOne Y theta) :
    ∃ (I : LieBimodule.{u_R, u_g, u_mod} R g) (hI : IsInHCThetaOne I theta)
      (W : Type u_mod) (_ : AddCommGroup W) (_ : Module R W),
      IsTensorProductBimoduleWithUTheta I theta W ∧
      ∃ (ι : HCThetaOneHom Y I theta hY hI), Function.Injective ι.toLinearMap := by


  sorry

noncomputable def embedding_into_realizable_bimodule_core
    {R : Type u_R} [CommRing R]
    {g : Type u_g} [LieRing g] [LieAlgebra R g]
    [LieAlgebra.IsSemisimple R g] [Module.Finite R g]
    (theta : CenterCharacter R g)
    (M : LieBimodule.{u_R, u_g, u_mod} R g)
    (hM : IsInHCThetaOne M theta) :
    ∃ (N : LieBimodule.{u_R, u_g, u_mod} R g)
      (hN : IsInHCThetaOne N theta)
      (f : HCThetaOneHom M N theta hM hN),
      Function.Injective f.toLinearMap ∧
      Nonempty (RealizingRepData.{u_R, u_g, u_mod, u_G, u_V} theta N hN) := by


  obtain ⟨I, hI, W, hW_acg, hW_mod, hTW, ι, hι_inj⟩ :=
    hc_theta_one_tensor_bimodule_embeds theta M hM

  have hI_real : Nonempty (RealizingRepData.{u_R, u_g, u_mod, u_G, u_V} theta I hI) :=
    tensor_bimodule_has_realizing_data theta I hI W hTW
  exact ⟨I, hI, ι, hι_inj, hI_real⟩

theorem corollary_25_11_realizability
    [LieAlgebra.IsSemisimple R g] [Module.Finite R g]
    (theta : CenterCharacter R g)
    (M : LieBimodule.{u_R, u_g, u_mod} R g)
    (hM : IsInHCThetaOne M theta) :
    Nonempty (RealizingRepData (R := R) (g := g) (theta := theta) (M := M) (_hM := hM)) := by


  obtain ⟨N, hN, f, hf_inj, h_real⟩ :=
    embedding_into_realizable_bimodule_core (R := R) (g := g) theta M hM

  exact corollary_6_13_sub_realizable (R := R) (g := g) theta M hM N hN f hf_inj h_real

end Corollary25_11

end
