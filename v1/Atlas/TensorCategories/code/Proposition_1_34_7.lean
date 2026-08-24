/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.QuasiTensorFunctor

open CategoryTheory MonoidalCategory

universe v u w

/-- Proposition 1.34.7: If a finite `k`-linear abelian monoidal category `C` admits a
quasi-fiber functor, then this functor is unique up to twisting (in particular, the underlying
functors are naturally isomorphic). -/
theorem Proposition_1_34_7
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear k C] [Abelian C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear k C]
    (hHomFiniteDim : ∀ (X Y : C), FiniteDimensional k (X ⟶ Y))
    (F₁ F₂ : TensorCategories.QuasiFiberFunctor k C) :
    Nonempty (F₁.F ≅ F₂.F) :=
  TensorCategories.prop_1_34_7 k C hHomFiniteDim F₁ F₂
