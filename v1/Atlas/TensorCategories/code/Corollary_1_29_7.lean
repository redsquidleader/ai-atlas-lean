/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.CartierKostant.Axioms

/-- Injectivity of the canonical map `U(Prim(H)) → H` from the universal enveloping
algebra of the primitives of `H` to `H` itself, in characteristic zero. -/
theorem corollary_1_29_7_canonicalMapUEA_injective
    (k : Type u) (H : Type v)
    [Field k] [CharZero k]
    [Ring H] [HopfAlgebra k H] :
    Function.Injective (HopfAlgebra.canonicalMapUEA (R := k) (H := H)) := by
  sorry

/-- Corollary 1.29.7 (EGNO): if `H` is a Hopf algebra over a field of characteristic zero,
then the natural map `ξ : U(Prim(H)) → H` is injective. -/
theorem Corollary_1_29_7
    (k : Type u) (H : Type v)
    [Field k] [CharZero k]
    [Ring H] [HopfAlgebra k H] :
    Function.Injective (HopfAlgebra.canonicalMapUEA (R := k) (H := H)) :=
  corollary_1_29_7_canonicalMapUEA_injective k H
