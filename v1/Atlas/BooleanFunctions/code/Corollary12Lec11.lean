/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.BooleanFunctions.code.UGCHardness

namespace UGCHardness

theorem corollary_1_2 (hUGC : UGC) :
    ∀ ε : ℝ, ε > 0 →
      MaxCut.IsNPHardGapMaxCut (1 - ε) (MaxCut.goemansWilliamsonConstant + ε) :=
  goemansWilliamson_optimal_assuming_ugc hUGC

end UGCHardness
