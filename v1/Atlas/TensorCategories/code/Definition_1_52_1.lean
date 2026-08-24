/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.IntegralsDefs

set_option autoImplicit false

universe u v

/-- Definition 1.52.1 (left integral): A left integral in an algebra H with counit eps is an
element I in H such that xI = eps(x)I for all x in H. -/
abbrev Definition_1_52_1_LeftIntegral (R : Type u) [CommSemiring R]
    (H : Type v) [Semiring H] [Algebra R H] [Coalgebra R H] (I : H) : Prop :=
  Def_1_52_1_IsLeftIntegral R H I

/-- Definition 1.52.1 (right integral): A right integral in an algebra H with counit eps is an
element I in H such that Ix = eps(x)I for all x in H. -/
abbrev Definition_1_52_1_RightIntegral (R : Type u) [CommSemiring R]
    (H : Type v) [Semiring H] [Algebra R H] [Coalgebra R H] (I : H) : Prop :=
  Def_1_52_1_IsRightIntegral R H I
