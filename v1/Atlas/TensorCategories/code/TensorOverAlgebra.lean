/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.AlgebrasInCategories

universe v u

namespace CategoryTheory

open Category MonoidalCategory Limits MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

section TensorOverAlgebra

variable {A : C} [MonObj A] [HasCoequalizers C]

/-- Definition 2.9.22: the tensor product `M ⊗_A N` of a right `A`-module `M` and a left
`A`-module `N` in a monoidal category, constructed as a coequalizer. -/
noncomputable def tensorOverAlgebra (M N : C) (rmod : RightModObj A M)
    (actL : A ⊗ N ⟶ N) : C :=
  sorry

/-- Definition 2.9.22: alias for the tensor product `M ⊗_A N` over an algebra in a monoidal
category. -/
noncomputable abbrev Definition_2_9_22 (M N : C) (rmod : RightModObj A M)
    (actL : A ⊗ N ⟶ N) : C :=
  sorry

/-- The canonical coequalizer projection `M ⊗ N → M ⊗_A N` realizing the tensor product over `A`. -/
noncomputable def tensorOverAlgebra.π (M N : C) (rmod : RightModObj A M)
    (actL : A ⊗ N ⟶ N) :
    M ⊗ N ⟶ tensorOverAlgebra M N rmod actL :=
  sorry

/-- The coequalizer relation defining `M ⊗_A N`: the two ways of acting by `A` (on `M` from the
right and on `N` from the left) become equal after composing with the projection. -/
theorem tensorOverAlgebra.condition (M N : C) (rmod : RightModObj A M)
    (actL : A ⊗ N ⟶ N) :
    rmod.act ▷ N ≫ tensorOverAlgebra.π M N rmod actL =
    ((α_ M A N).hom ≫ (M ◁ actL)) ≫ tensorOverAlgebra.π M N rmod actL :=
  sorry

end TensorOverAlgebra

end CategoryTheory
