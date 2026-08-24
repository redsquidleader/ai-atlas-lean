/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.CategoricalFreeness

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe v u v₁ u₁ w

/-- Corollary 1.50.3: If C is integral and F : C → D is a surjective quasi-tensor functor between
finite tensor categories, then D is also integral, and the object F(R_C) is free of rank
FPdim(C)/FPdim(D) (which is an integer). -/
theorem Corollary_1_50_3
    {k : Type w} [Field k]
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C]
      [Preadditive C] [Linear k C] [MonoidalPreadditive C] [MonoidalLinear k C]
      [RigidCategory C]
    {D : Type u₁} [Category.{v₁} D] [MonoidalCategory D] [Abelian D]
      [Preadditive D] [Linear k D] [MonoidalPreadditive D] [MonoidalLinear k D]
      [RigidCategory D]
    (QTF : SurjectiveQuasiTensorFunctor k C D)
    (decompC : FiniteMultitensorDecompData k C)
    (decompD : FiniteMultitensorDecompData k D)
    (dC : FPdimFunction (C := C))
    (dD : FPdimFunction (C := D))
    (hC_pos : categoricalFPdim decompC dC > 0)
    (hD_pos : categoricalFPdim decompD dD > 0)
    (hC_int : dC.IsIntegral) :

    dD.IsIntegral ∧

    (∃ (n : ℕ), n > 0 ∧
      categoricalFPdim decompC dC / categoricalFPdim decompD dD = ↑n) ∧

    (∃ (n : ℕ), n > 0 ∧
      ∀ j : decompD.I,
        coeffF_RC QTF decompC decompD dC j = ↑n * dD.fpDim (decompD.simpleObj j)) ∧

    (∃ (nC nD m : ℕ),
      categoricalFPdim decompC dC = ↑nC ∧
      categoricalFPdim decompD dD = ↑nD ∧
      nD * m = nC ∧ 0 < nD ∧ 0 < m) :=
  corollary_1_50_3 QTF decompC decompD dC dD hC_pos hD_pos hC_int
