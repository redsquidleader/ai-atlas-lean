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

/-- Theorem 1.50.1: For a surjective quasi-tensor functor `F : C → D` between finite
multitensor categories, the image of the regular object `R_C` satisfies
`F(R_C) = (FPdim(C)/FPdim(D)) R_D`, i.e. each Frobenius-Perron coefficient is given by
the ratio of categorical FP-dimensions times the FP-dimension of the corresponding
simple object. -/
theorem Theorem_1_50_1
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
    (hD_pos : categoricalFPdim decompD dD > 0) :
    ∀ j : decompD.I,
      coeffF_RC QTF decompC decompD dC j =
        (categoricalFPdim decompC dC / categoricalFPdim decompD dD) *
          dD.fpDim (decompD.simpleObj j) :=
  CategoryTheory.thm_1_50_1 QTF decompC decompD dC dD hC_pos hD_pos
