/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Localization.Away.Basic

open AlgebraicGeometry CategoryTheory

namespace PushforwardDirectLimit

variable {R : CommRingCat.{0}}

/-- The localisation `M[f⁻¹]` of an `R`-module `M` at the powers of `f`, packaged as a
`ModuleCat R`. -/
noncomputable def localizedModuleCat (M : ModuleCat.{0} R) (f : R) :
    ModuleCat.{0} R :=
  ModuleCat.of R (LocalizedModule (Submonoid.powers f) M)

/-- The image of `f ∈ R` as a global section of `Spec R` via the canonical isomorphism
`Γ(Spec R, ⊤) ≅ R`. -/
noncomputable def toSpecGlobal (f : R) : Γ(Spec R, ⊤) :=
  (ConcreteCategory.hom (Scheme.ΓSpecIso R).inv) f

/-- The open immersion of the basic open `D(f) ⊆ Spec R` into `Spec R`. -/
noncomputable def basicOpenInclusion (f : R) : ↑((Spec R).basicOpen (toSpecGlobal f)) ⟶ Spec R :=
  Scheme.Opens.ι ((Spec R).basicOpen (toSpecGlobal f))

/-- For any module `M`, the canonical map `tildeΓ → id` is an isomorphism on
`f_* f^* (M̃)`, where `f : D(f) ↪ Spec R`. -/
theorem isIso_fromTildeΓ_pushforward_pullback (M : ModuleCat.{0} R) (f : R) :
    IsIso (Scheme.Modules.fromTildeΓ
      ((Scheme.Modules.pushforward (basicOpenInclusion f)).obj
        ((Scheme.Modules.pullback (basicOpenInclusion f)).obj (tilde M)))) := by sorry

/-- The global sections of `f_* f^* M̃` are isomorphic to the localisation `M[f⁻¹]`. -/
noncomputable def globalSections_pushforward_pullback_iso (M : ModuleCat.{0} R) (f : R) :
    moduleSpecΓFunctor.obj
      ((Scheme.Modules.pushforward (basicOpenInclusion f)).obj
        ((Scheme.Modules.pullback (basicOpenInclusion f)).obj (tilde M))) ≅
    localizedModuleCat M f := by sorry

/-- Quasicoherence implies the canonical map `tildeΓ → id` is an isomorphism on
`Spec R`. -/
theorem isIso_fromTildeΓ_qcoh_spec
    (F : (Spec R).Modules) [F.IsQuasicoherent] : IsIso F.fromTildeΓ := by sorry

/-- For a basic open `D(f) ↪ Spec R`, pushforward followed by pullback of `M̃`
identifies with the tilde of the localisation `M[f⁻¹]`. -/
noncomputable def pushforward_pullback_tilde_iso (M : ModuleCat.{0} R) (f : R) :
    (Scheme.Modules.pushforward (basicOpenInclusion f)).obj
      ((Scheme.Modules.pullback (basicOpenInclusion f)).obj (tilde M)) ≅
    tilde (localizedModuleCat M f) := by
  set F := (Scheme.Modules.pushforward (basicOpenInclusion f)).obj
      ((Scheme.Modules.pullback (basicOpenInclusion f)).obj (tilde M))

  haveI := isIso_fromTildeΓ_pushforward_pullback M f


  exact (asIso F.fromTildeΓ).symm ≪≫
    (tilde.functor R).mapIso (globalSections_pushforward_pullback_iso M f)

/-- For a quasicoherent `F` on `Spec R` and a basic open `D(f)`, the composite
`f_* f^* F` is isomorphic to the tilde of the localisation of `Γ(F)` at `f`. -/
noncomputable def pushforward_pullback_qcoh_iso
    (F : (Spec R).Modules) [F.IsQuasicoherent] (f : R) :
    (Scheme.Modules.pushforward (basicOpenInclusion f)).obj
      ((Scheme.Modules.pullback (basicOpenInclusion f)).obj F) ≅
    tilde (localizedModuleCat (moduleSpecΓFunctor.obj F) f) := by


  haveI := isIso_fromTildeΓ_qcoh_spec F

  exact (Scheme.Modules.pushforward (basicOpenInclusion f)).mapIso
    ((Scheme.Modules.pullback (basicOpenInclusion f)).mapIso
      (asIso F.fromTildeΓ).symm) ≪≫
    pushforward_pullback_tilde_iso (moduleSpecΓFunctor.obj F) f

end PushforwardDirectLimit
