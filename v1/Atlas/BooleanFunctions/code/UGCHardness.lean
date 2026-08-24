/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.UniqueGames

namespace UGCHardness

def UGC : Prop :=
  ∀ ε δ : ℝ, ε > 0 → δ > 0 →
    ∃ k : ℕ, UniqueGames.IsNPHardGapUniqueGame k (1 - ε) δ


theorem goemansWilliamson_optimal_assuming_ugc :
  UGC → ∀ ε : ℝ, ε > 0 →
    MaxCut.IsNPHardGapMaxCut (1 - ε) (MaxCut.goemansWilliamsonConstant + ε) := by sorry

end UGCHardness
