/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace Proposition18

/-- The category of quasi-coherent sheaves of modules on a scheme `X`, realized
as the full subcategory of `X.Modules` cut out by the quasi-coherence property. -/
abbrev Scheme.Qcoh (X : Scheme.{u}) :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory

/-- Inclusion of quasi-coherent sheaves on `X` into all sheaves of modules on `X`. -/
def Scheme.Qcoh.incl (X : Scheme.{u}) : Scheme.Qcoh X ⥤ X.Modules :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).ι

/-- The tilde functor `M ↦ M̃` viewed with codomain the quasi-coherent subcategory
of `(Spec R).Modules`; sends an `R`-module to the associated quasi-coherent sheaf
on `Spec R`. -/
def tildeFunctorToQcoh (R : CommRingCat.{u}) : ModuleCat.{u} R ⥤ Scheme.Qcoh (Spec R) where
  obj M := ⟨tilde M, inferInstance⟩
  map f := ObjectProperty.homMk (tilde.map f)

/-- The tilde functor `Mod R → (Spec R).Modules` is fully faithful, the
fundamental input to Thm 11.1 / Thm 12.1. -/
def tilde_fullyFaithful (R : CommRingCat.{u}) :
    (tilde.functor R).FullyFaithful :=
  tilde.fullyFaithfulFunctor

/-- The adjunction `tilde ⊣ Γ` between the tilde functor and the global-sections
functor, one half of the equivalence `Mod R ≃ QCoh(Spec R)`. -/
def tildeGammaAdj (R : CommRingCat.{u}) :
    tilde.functor R ⊣ moduleSpecΓFunctor :=
  tilde.adjunction

/-- For any `R`-module `M`, the sheaf `M̃` on `Spec R` is quasi-coherent (Cor 16). -/
theorem tilde_isQuasicoherent {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    (tilde M).IsQuasicoherent :=
  inferInstance

/-- `tildeFunctorToQcoh R` is full: every map between tilde sheaves comes from
a module map, lifted from fullness of the underlying tilde functor. -/
instance tildeFunctorToQcoh_full (R : CommRingCat.{u}) : (tildeFunctorToQcoh R).Full where
  map_surjective {M N} f := by
    refine ⟨(tilde.functor R).preimage f.hom, ?_⟩
    apply ObjectProperty.hom_ext
    exact (tilde.functor R).map_preimage f.hom

/-- `tildeFunctorToQcoh R` is faithful: two `R`-module maps with equal tilde
images coincide. -/
instance tildeFunctorToQcoh_faithful (R : CommRingCat.{u}) :
    (tildeFunctorToQcoh R).Faithful where
  map_injective {M N f g} h := by
    have := congr_arg InducedCategory.Hom.hom h
    dsimp [tildeFunctorToQcoh] at this
    exact (tilde.functor R).map_injective this

set_option backward.isDefEq.respectTransparency false in
/-- If a sheaf of modules `ℱ` on `Spec R` is in the essential image of the
tilde functor, then it is quasi-coherent. -/
theorem isQuasicoherent_of_mem_essImage_tilde {R : CommRingCat.{u}}
    {ℱ : (Spec R).Modules} (h : (tilde.functor R).essImage ℱ) :
    ℱ.IsQuasicoherent := by
  rw [← isIso_fromTildeΓ_iff] at h
  haveI := h
  exact ((presentationTilde.{u} (moduleSpecΓFunctor.obj ℱ)
    Set.univ (by simp) _ (Submodule.span_eq _)).of_isIso ℱ.fromTildeΓ).isQuasicoherent


/-- Converse direction (Thm 12.1): every quasi-coherent sheaf on `Spec R`
arises (up to isomorphism) as `M̃` for some `R`-module `M`. -/
theorem mem_essImage_tilde_of_isQuasicoherent {R : CommRingCat.{u}}
    (ℱ : (Spec R).Modules) [hℱ : ℱ.IsQuasicoherent] :
    (tilde.functor R).essImage ℱ := by sorry

/-- Characterization (Thm 11.1 / Thm 12.1): a sheaf of modules on `Spec R` is
quasi-coherent iff it lies in the essential image of the tilde functor. -/
theorem mem_essImage_tilde_iff_isQuasicoherent {R : CommRingCat.{u}}
    (ℱ : (Spec R).Modules) :
    (tilde.functor R).essImage ℱ ↔ ℱ.IsQuasicoherent :=
  ⟨isQuasicoherent_of_mem_essImage_tilde,
   fun hℱ => @mem_essImage_tilde_of_isQuasicoherent R ℱ hℱ⟩

/-- `tildeFunctorToQcoh R` is essentially surjective: every quasi-coherent
sheaf on `Spec R` is isomorphic to `M̃` for some module `M`. -/
instance tildeFunctorToQcoh_essSurj (R : CommRingCat.{u}) :
    (tildeFunctorToQcoh R).EssSurj where
  mem_essImage := by
    intro ⟨ℱ, hℱ⟩
    have h := @mem_essImage_tilde_of_isQuasicoherent _ ℱ hℱ
    obtain ⟨M, ⟨iso⟩⟩ := h
    refine ⟨M, ⟨?_⟩⟩
    refine ⟨ObjectProperty.homMk iso.hom, ObjectProperty.homMk iso.inv, ?_, ?_⟩
    · apply ObjectProperty.hom_ext
      exact iso.hom_inv_id
    · apply ObjectProperty.hom_ext
      exact iso.inv_hom_id

/-- The tilde functor `Mod R → QCoh(Spec R)` is an equivalence of categories,
combining fullness, faithfulness, and essential surjectivity. -/
instance tildeFunctorToQcoh_isEquivalence (R : CommRingCat.{u}) :
    (tildeFunctorToQcoh R).IsEquivalence where
  essSurj := tildeFunctorToQcoh_essSurj R

/-- The fundamental equivalence (Thm 11.1 / Thm 12.1):
`Mod(R) ≃ QCoh(Spec R)` via `M ↦ M̃`, with inverse the global-sections functor `Γ`. -/
def qcoh_spec_equiv_moduleCat (R : CommRingCat.{u}) :
    ModuleCat.{u} R ≌ Scheme.Qcoh (Spec R) :=
  (tildeFunctorToQcoh R).asEquivalence


/-- Lem 24 (Lec 12): the pushforward `f_*` along an affine morphism preserves
quasi-coherent sheaves. -/
theorem pushforward_isQuasicoherent_of_isAffineHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
    (ℱ : X.Modules) [hℱ : ℱ.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj ℱ).IsQuasicoherent := by sorry

end Proposition18
