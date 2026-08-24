/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.VecPivotal.DoubleDualIso
import Atlas.TensorCategories.code.VecPivotal.MonoidalCoherence
import Atlas.TensorCategories.code.PivotalSpherical

set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Module Category

universe u

noncomputable section

variable (k : Type u) [Field k]

namespace TensorCategories

/-- `FGModuleCat k` has a pivotal category structure given by the canonical
double-dual evaluation isomorphism together with the tensor-coherence iso
of Section 1.38. -/
instance instPivotalCategoryFGModuleCat :
    PivotalCategory (FGModuleCat.{u} k) where
  pivotalIso V := (Module.evalEquiv k V).toFGModuleCatIso
  tensorCoherenceIso := vecCanonicalTensorCoherence k
  naturality f := by
    sorry
  monoidality V W := by
    sorry
  dimUnit := by
    sorry

end TensorCategories

end
