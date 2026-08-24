/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.HopfAlgebra

/-- The antipode of a finite-dimensional Hopf algebra over a field is injective. -/
theorem antipode_injective_of_finiteDimensional
    (k : Type u) [Field k]
    (H : Type v) [Ring H] [HopfAlgebra k H]
    [FiniteDimensional k H] :
    Function.Injective (⇑(HopfAlgebra.antipode k) : H → H) :=
  (HopfAlgebra.antipode_bijective k H).1
