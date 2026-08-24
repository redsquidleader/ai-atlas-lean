/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.Algebra.Category.Grp.Abelian

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

universe u

namespace AffinePushforwardHigher

/-- Global sections functor `Γ(X, -) : X.Modules ⥤ Ab` for a scheme `X`. -/
def globalSectionsFunctor (X : Scheme.{u}) : X.Modules ⥤ Ab where
  obj F := Γ(F, ⊤)
  map φ := Scheme.Modules.Hom.app φ ⊤
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The global sections functor is additive. -/
instance globalSectionsFunctor_additive (X : Scheme.{u}) :
    (globalSectionsFunctor X).Additive where
  map_add := fun {_ _ _ _} => rfl

/-- Naturally isomorphic additive functors have naturally isomorphic right derived functors. -/
def rightDerivedFunctorIso
    {C : Type*} [Category C] {D : Type*} [Category D]
    [Abelian C] [Abelian D] [HasInjectiveResolutions C]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    (τ : F ≅ G) (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived τ.hom n
  inv := NatTrans.rightDerived τ.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, τ.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, τ.inv_hom_id, NatTrans.rightDerived_id]

/-- Pushforward along an affine morphism is exact on (quasi-coherent) modules. -/
theorem affinePushforwardExact
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    (Scheme.Modules.pushforward f).PreservesHomology := by sorry

/-- Natural isomorphism `Γ(X, -) ≅ Γ(Y, f_*(-))`. -/
noncomputable def globalSectionsCompPushforwardIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    globalSectionsFunctor X ≅
      Scheme.Modules.pushforward f ⋙ globalSectionsFunctor Y := by sorry

/-- For `f` affine and `F` quasi-coherent, exactness of `f_*` gives
`Rⁿ(Γ_Y ∘ f_*)(F) ≅ Rⁿ Γ_Y (f_*F)`. -/
noncomputable def rightDerivedCompExactIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions Y.Modules]
    (F : X.Modules) [F.IsQuasicoherent]
    (n : ℕ) :
    ((Scheme.Modules.pushforward f ⋙ globalSectionsFunctor Y).rightDerived n).obj F ≅
    ((globalSectionsFunctor Y).rightDerived n).obj ((Scheme.Modules.pushforward f).obj F) := by sorry

set_option maxHeartbeats 800000 in
/-- Higher direct images vanish along affine morphisms: `Rⁿf_*F = 0` for `n > 0` when `f` is
affine and `F` is quasi-coherent (Prop 44, Lec 23). -/
theorem higherDirectImageVanishing
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (F : X.Modules) [F.IsQuasicoherent]
    [HasInjectiveResolutions X.Modules]
    (n : ℕ) (hn : 0 < n) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived n).obj F) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  haveI := affinePushforwardExact f
  set G := Scheme.Modules.pushforward f
  let I : InjectiveResolution F := injectiveResolution F

  refine IsZero.of_iso ?_ (I.isoRightDerivedObj G (n + 1))

  erw [← HomologicalComplex.exactAt_iff_isZero_homology]

  have h_exact : I.cocomplex.ExactAt (n + 1) := I.cocomplex_exactAt_succ n
  rw [HomologicalComplex.exactAt_iff] at h_exact ⊢
  exact h_exact.map G

/-- Cohomology along an affine pushforward: `Hⁿ(Y, f_*F) ≅ Hⁿ(X, F)` (Prop 44, Lec 23). -/
def affinePushforwardCohomologyIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (F : X.Modules) [F.IsQuasicoherent]
    [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions Y.Modules]
    (n : ℕ) :
    ((globalSectionsFunctor Y).rightDerived n).obj
      ((Scheme.Modules.pushforward f).obj F) ≅
    ((globalSectionsFunctor X).rightDerived n).obj F :=

  (rightDerivedCompExactIso f F n).symm ≪≫

  (rightDerivedFunctorIso _ _ (globalSectionsCompPushforwardIso f) n).symm.app F

end AffinePushforwardHigher

end
