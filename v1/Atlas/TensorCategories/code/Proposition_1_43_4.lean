/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.StarAlgebras

/-- Proposition 1.43.4: For a based ring `A` (here, a multifusion ring `R`), the algebra
`A ⊗_ℤ ℂ` is canonically a `*`-algebra with trace. -/
noncomputable def Proposition_1_43_4 {ι : Type*} [DecidableEq ι] [Fintype ι]
    (R : MultifusionRingDef ι) : StarAlgWithTrace :=
  R.prop_1_43_4
