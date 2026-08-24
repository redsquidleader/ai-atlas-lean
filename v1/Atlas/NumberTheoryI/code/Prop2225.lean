/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.GlobalCFT
import Atlas.NumberTheoryI.code.Ch22Conductor

noncomputable section

open NumberField RayClassField GlobalConductor KroneckerWeber

namespace ConductorRamification

universe u

variable {K : Type u} [Field K] [NumberField K]
         {L : Type u} [Field L] [NumberField L]
         [Algebra K L] [FiniteDimensional K L] [IsAbelianExtension K L]

theorem conductorVal_eq_zero_iff_unramified (𝔭 : Prime' K) :
    (GlobalCFT.extensionConductor K L) (Place.finite 𝔭) = 0 ↔
      GlobalCFT.IsUnramifiedIn K L 𝔭 :=
  GlobalCFT.proposition_22_25_unramified K L 𝔭

theorem conductorVal_eq_one_iff_tamelyRamified (𝔭 : Prime' K) :
    (GlobalCFT.extensionConductor K L) (Place.finite 𝔭) = 1 ↔
      (GlobalCFT.IsTamelyRamifiedIn K L 𝔭 ∧ ¬ GlobalCFT.IsUnramifiedIn K L 𝔭) :=
  GlobalCFT.proposition_22_25_tame K L 𝔭

theorem conductorVal_ge_two_iff_wildlyRamified (𝔭 : Prime' K) :
    2 ≤ (GlobalCFT.extensionConductor K L) (Place.finite 𝔭) ↔
      GlobalCFT.IsWildlyRamifiedIn K L 𝔭 :=
  GlobalCFT.proposition_22_25_wild K L 𝔭

theorem proposition_22_25 (𝔭 : Prime' K) :
    ((GlobalCFT.extensionConductor K L) (Place.finite 𝔭) = 0 ↔
      GlobalCFT.IsUnramifiedIn K L 𝔭) ∧
    ((GlobalCFT.extensionConductor K L) (Place.finite 𝔭) = 1 ↔
      (GlobalCFT.IsTamelyRamifiedIn K L 𝔭 ∧ ¬ GlobalCFT.IsUnramifiedIn K L 𝔭)) ∧
    (2 ≤ (GlobalCFT.extensionConductor K L) (Place.finite 𝔭) ↔
      GlobalCFT.IsWildlyRamifiedIn K L 𝔭) :=
  ⟨conductorVal_eq_zero_iff_unramified 𝔭,
   conductorVal_eq_one_iff_tamelyRamified 𝔭,
   conductorVal_ge_two_iff_wildlyRamified 𝔭⟩

end ConductorRamification
