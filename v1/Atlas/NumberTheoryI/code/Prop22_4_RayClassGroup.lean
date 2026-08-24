/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.RayClassFields
import Atlas.NumberTheoryI.code.Cor227
import Atlas.NumberTheoryI.code.GlobalCFT

open RayClassField GlobalCFT

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

theorem proposition_22_4_equivalence :
    Equivalence (CongruenceSubgroupPair.IsEquiv (K := K)) where
  refl := CongruenceSubgroupPair.isEquiv_refl
  symm := CongruenceSubgroupPair.IsEquiv.symm'
  trans := fun h₁ h₂ => h₁.trans' h₂

end
