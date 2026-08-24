/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.ProjectiveFunctors

noncomputable section

open Classical ProjectiveFunctors

section KrullSchmidtCategoryO

universe u

variable {R : Type u} [CommRing R]
variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {Δ : TriangularDecomposition R 𝔤}
variable (rd : PositiveRootData Δ)

end KrullSchmidtCategoryO

end
