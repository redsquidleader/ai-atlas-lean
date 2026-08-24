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

/-- The global sections functor `Γ(X, -) : X.Modules ⥤ Ab` sending a sheaf of `O_X`-modules to
its abelian group of global sections. -/
def Scheme.Modules.globalSectionsFunctor (X : Scheme.{u}) :
    X.Modules ⥤ Ab where
  obj F := Γ(F, ⊤)
  map φ := Scheme.Modules.Hom.app φ ⊤
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `Γ(X, -)` is an additive functor. -/
instance Scheme.Modules.globalSectionsFunctor_additive
    (X : Scheme.{u}) : (Scheme.Modules.globalSectionsFunctor X).Additive where
  map_add := fun {_ _ _ _} => rfl

/-- Naturally isomorphic additive functors have naturally isomorphic right derived functors:
if `F ≅ G` then `RⁿF ≅ RⁿG` for every `n`. -/
def rightDerivedFunctorIso
    {C : Type*} [Category C] {D : Type*} [Category D]
    [Abelian C] [Abelian D] [HasInjectiveResolutions C]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    (τ : F ≅ G) (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived τ.hom n
  inv := NatTrans.rightDerived τ.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, τ.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, τ.inv_hom_id, NatTrans.rightDerived_id]

/-- The pushforward `f_*` along an affine morphism preserves homology of complexes of
quasi-coherent modules; equivalently it is exact on quasi-coherent sheaves. -/
theorem pushforward_affine_preservesHomology
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    (Scheme.Modules.pushforward f).PreservesHomology := by sorry

set_option maxHeartbeats 800000 in
/-- Vanishing of higher direct images along an affine morphism: for `f` affine and `F`
quasi-coherent on `X`, `Rⁿf_* F = 0` for all `n > 0` (Prop 44, Lec 23). -/
theorem prop44_higher_direct_image_vanishing
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (F : X.Modules) [F.IsQuasicoherent]
    [HasInjectiveResolutions X.Modules]
    (n : ℕ) (hn : 0 < n) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived n).obj F) := by
  obtain ⟨n, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  haveI := pushforward_affine_preservesHomology f
  set G := Scheme.Modules.pushforward f
  let I : InjectiveResolution F := injectiveResolution F

  refine IsZero.of_iso ?_ (I.isoRightDerivedObj G (n + 1))

  erw [← HomologicalComplex.exactAt_iff_isZero_homology]

  have h_exact : I.cocomplex.ExactAt (n + 1) := I.cocomplex_exactAt_succ n
  rw [HomologicalComplex.exactAt_iff] at h_exact ⊢
  exact h_exact.map G

/-- Natural isomorphism `Γ(X, -) ≅ Γ(Y, f_*(-))` from the definition of pushforward sections. -/
noncomputable def globalSections_comp_pushforward_iso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] :
    Scheme.Modules.globalSectionsFunctor X ≅
      Scheme.Modules.pushforward f ⋙ Scheme.Modules.globalSectionsFunctor Y := by sorry

/-- For `f` affine and `F` quasi-coherent, the right derived functors of the composite
`Γ(Y, -) ∘ f_*` agree with those of `Γ(Y, -)` applied to `f_*F`, since `f_*` is exact in this case
(so the Grothendieck spectral sequence degenerates). -/
noncomputable def rightDerived_comp_exact_iso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions Y.Modules]
    (F : X.Modules) [F.IsQuasicoherent]
    (n : ℕ) :
    ((Scheme.Modules.pushforward f ⋙ Scheme.Modules.globalSectionsFunctor Y).rightDerived n).obj F ≅
    ((Scheme.Modules.globalSectionsFunctor Y).rightDerived n).obj ((Scheme.Modules.pushforward f).obj F) := by sorry

/-- Proposition 44 (Lec 23): for `f : X → Y` affine and `F` quasi-coherent on `X`, the cohomology
of `f_*F` on `Y` agrees with the cohomology of `F` on `X`: `Hⁿ(Y, f_*F) ≅ Hⁿ(X, F)`. -/
def prop44_affine_pushforward_cohomology
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (F : X.Modules) [F.IsQuasicoherent]
    [HasInjectiveResolutions X.Modules]
    [HasInjectiveResolutions Y.Modules]
    (n : ℕ) :
    ((Scheme.Modules.globalSectionsFunctor Y).rightDerived n).obj
      ((Scheme.Modules.pushforward f).obj F) ≅
    ((Scheme.Modules.globalSectionsFunctor X).rightDerived n).obj F :=

  (rightDerived_comp_exact_iso f F n).symm ≪≫

  (rightDerivedFunctorIso _ _ (globalSections_comp_pushforward_iso f) n).symm.app F

end
