/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.Prop_1_45_10
import Atlas.TensorCategories.code.QuasiTensorFunctor

open Finset BigOperators FusionRing FusionRing.FPdimData

/-- A quasi-tensor functor between fusion rings induces a fusion ring homomorphism whose
matrix entries are nonnegative, reflecting the categorical positivity of multiplicities
under quasi-tensor functors. -/
theorem quasiTensorFunctor_induces_fusionRingHom
    {ι : Type} [DecidableEq ι] [Fintype ι] [Nonempty ι]
    {κ : Type} [DecidableEq κ] [Fintype κ] [Nonempty κ]
    (R : FusionRing ι) (S : FusionRing κ) :
    ∃ (φ : FusionRingHom R S), ∀ i l, (0 : ℤ) ≤ φ.M i l := by sorry
