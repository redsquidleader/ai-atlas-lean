/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.GlobalFields

open NumberField

namespace InfinitePlaceBaseChange

noncomputable def ringEquiv {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (v : NumberField.InfinitePlace K) :
    TensorProduct K L v.Completion ≃+*
      ((w : { w : NumberField.InfinitePlace L // w.comap (algebraMap K L) = v }) →
        w.val.Completion) :=
  canonicalMapEquiv v

end InfinitePlaceBaseChange
