/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.MfStarAlgebra

/-- Corollary 1.43.5 (EGNO): if `A` is a multifusion ring, then the algebra
`A ⊗_ℤ ℂ` is semisimple. -/
theorem Corollary_1_43_5 {ι : Type*} [DecidableEq ι] [Fintype ι] (M : MultifusionRingDef ι) :
    IsSemisimpleRing (MfGrRingOfC M) :=
  M.mf_complexified_semisimple
