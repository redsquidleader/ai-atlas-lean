/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.NoetherianSpace
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
  PrimeSpectrum

universe u

namespace QCohSheaves

/-- Localization of an `R`-module at the powers of `f`, packaged as a `ModuleCat`. -/
def localizedModuleCat {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (f : R) :
    ModuleCat.{u} R :=
  ModuleCat.of R (LocalizedModule (Submonoid.powers f) M)

/-- Image of `f ∈ R` under the natural isomorphism `R ≅ Γ(Spec R, 𝒪)`,
producing a global section of the structure sheaf of `Spec R`. -/
def toSpecGlobal {R : CommRingCat.{u}} (f : R) : Γ(Spec R, ⊤) :=
  (ConcreteCategory.hom (Scheme.ΓSpecIso R).inv) f

/-- Open immersion of the basic open `D(f)` into `Spec R`. -/
def basicOpenInclusion {R : CommRingCat.{u}} (f : R) :
    ↑((Spec R).basicOpen (toSpecGlobal f)) ⟶ Spec R :=
  Scheme.Opens.ι ((Spec R).basicOpen (toSpecGlobal f))

/-- Prop 16 (Lec 12) input: applying tilde to `M`, then restricting and pushing
forward along `D(f) ↪ Spec R`, gives a sheaf whose `fromTildeΓ` counit is an
isomorphism. -/
theorem prop16_pushforward_pullback_qc {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (f : R) :
    IsIso (Scheme.Modules.fromTildeΓ
      ((Scheme.Modules.pushforward (basicOpenInclusion f)).obj
        ((Scheme.Modules.pullback (basicOpenInclusion f)).obj (tilde M)))) := by sorry

/-- Global sections of the pushforward of `M̃|_{D(f)}` are naturally isomorphic
to the localization `M_f`. -/
noncomputable def prop16_globalSections_iso {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (f : R) :
    moduleSpecΓFunctor.obj
      ((Scheme.Modules.pushforward (basicOpenInclusion f)).obj
        ((Scheme.Modules.pullback (basicOpenInclusion f)).obj (tilde M))) ≅
    localizedModuleCat M f := by sorry

/-- Prop 16: pushforward-pullback of `M̃` along `D(f) ↪ Spec R` is naturally
isomorphic to the tilde of the localized module `M_f`. -/
def prop16_pushforward_pullback_tilde_iso
    {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (f : R) :
    (Scheme.Modules.pushforward (basicOpenInclusion f)).obj
      ((Scheme.Modules.pullback (basicOpenInclusion f)).obj (tilde M)) ≅
    tilde (localizedModuleCat M f) := by
  set F := (Scheme.Modules.pushforward (basicOpenInclusion f)).obj
      ((Scheme.Modules.pullback (basicOpenInclusion f)).obj (tilde M))

  haveI := prop16_pushforward_pullback_qc M f


  exact (asIso F.fromTildeΓ).symm ≪≫
    (tilde.functor R).mapIso (prop16_globalSections_iso M f)

/-- For any quasi-coherent sheaf on `Spec R`, the counit `F̃Γ → F` is an
isomorphism (the affine reconstruction lemma underlying the equivalence). -/
theorem prop16_qcoh_fromTildeΓ_iso {R : CommRingCat.{u}}
    (F : (Spec R).Modules) [F.IsQuasicoherent] : IsIso F.fromTildeΓ := by sorry

/-- Quasi-coherent version of Prop 16: pushforward-pullback of a quasi-coherent
sheaf `F` along `D(f) ↪ Spec R` is isomorphic to the tilde of the localization
of its global sections at `f`. -/
def prop16_pushforward_pullback_qcoh_iso
    {R : CommRingCat.{u}} (F : (Spec R).Modules) [F.IsQuasicoherent] (f : R) :
    (Scheme.Modules.pushforward (basicOpenInclusion f)).obj
      ((Scheme.Modules.pullback (basicOpenInclusion f)).obj F) ≅
    tilde (localizedModuleCat (moduleSpecΓFunctor.obj F) f) := by
  haveI := prop16_qcoh_fromTildeΓ_iso F
  exact (Scheme.Modules.pushforward (basicOpenInclusion f)).mapIso
    ((Scheme.Modules.pullback (basicOpenInclusion f)).mapIso
      (asIso F.fromTildeΓ).symm) ≪≫
    prop16_pushforward_pullback_tilde_iso (moduleSpecΓFunctor.obj F) f

/-- The sheaf `M̃` on `Spec R` is quasi-coherent (Cor 16, registered as an instance). -/
instance tilde_isQuasicoherent_goal94 {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    (tilde M).IsQuasicoherent :=
  inferInstance

/-- The adjunction `tilde ⊣ Γ` between modules over `R` and sheaves of modules
on `Spec R`. -/
def tilde_gamma_adjunction (R : CommRingCat.{u}) :
    tilde.functor R ⊣ moduleSpecΓFunctor :=
  tilde.adjunction

/-- Predicate version of quasi-coherence for a sheaf of modules on a scheme. -/
def IsQuasicoherentSheaf {X : Scheme.{u}} (F : X.Modules) : Prop :=
  F.IsQuasicoherent

end QCohSheaves
