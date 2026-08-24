/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.TannakaReconstruction

open CategoryTheory

/-- Theorem 1.23.1: Let `C` be a `k`-linear abelian category with an exact faithful
functor `F : C → Vec`. Then `F` defines an equivalence between `C` and the category
of finite-dimensional right comodules over `Coend(F)` (equivalently, continuous
finite-dimensional left `End(F)`-modules). -/
theorem theorem_1_23_1
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [Abelian C] [Linear k C]
    (F : C ⥤ ModuleCat.{w} k)
    [F.Faithful]
    [F.PreservesMonomorphisms]
    [F.PreservesEpimorphisms] :
    Nonempty (TannakaReconstructionData k C F) :=
  ⟨tannaka_reconstruction_categorical k C F⟩
