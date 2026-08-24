/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.GlobalCFT

open NumberField RayClassField

universe u

namespace NormIndexInequality

theorem norm_index_inequality
    (K : Type u) (L : Type u) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (𝔪 : Modulus K)
    (h_cond : Modulus.dvd (GlobalCFT.extensionConductor K L) 𝔪) :
    (GlobalCFT.NormGroup K L 𝔪).index ≤ Module.finrank K L :=
  GlobalCFT.theorem_22_29_norm_index_inequality K L 𝔪 h_cond

end NormIndexInequality
