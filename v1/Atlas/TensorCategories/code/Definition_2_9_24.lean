/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.IndecomposableModuleCat
import Mathlib.CategoryTheory.Monoidal.Bimod
import Mathlib.CategoryTheory.Monoidal.Mod_

set_option maxHeartbeats 800000

universe v u

namespace CategoryTheory

open Category MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Definition 2.9.24: an `(A, B)`-bimodule in `C`, i.e. an object of `Bimod A B`. -/
abbrev Definition_2_9_24_Bimodule (A B : Mon C) := Bimod A B

/-- Underlying object of an `(A, B)`-bimodule. -/
abbrev Definition_2_9_24_Bimodule.obj {A B : Mon C}
    (M : Definition_2_9_24_Bimodule A B) : C := M.X

/-- Left action `A ⊗ M ⟶ M` of an `(A, B)`-bimodule. -/
abbrev Definition_2_9_24_Bimodule.leftAction {A B : Mon C}
    (M : Definition_2_9_24_Bimodule A B) : A.X ⊗ M.X ⟶ M.X :=
  M.actLeft

/-- Right action `M ⊗ B ⟶ M` of an `(A, B)`-bimodule. -/
abbrev Definition_2_9_24_Bimodule.rightAction {A B : Mon C}
    (M : Definition_2_9_24_Bimodule A B) : M.X ⊗ B.X ⟶ M.X :=
  M.actRight

/-- The left and right actions of an `(A, B)`-bimodule commute: applying the right
action after the left action equals reassociating then applying the left action after
the right. -/
theorem Definition_2_9_24_Bimodule.actions_commute {A B : Mon C}
    (M : Definition_2_9_24_Bimodule A B) :
    M.actLeft ▷ B.X ≫ M.actRight =
      (α_ A.X M.X B.X).hom ≫ A.X ◁ M.actRight ≫ M.actLeft :=
  M.middle_assoc

/-- An algebra `A ∈ C` is indecomposable when its category of left modules is
indecomposable as a left `C`-module category. -/
def IsIndecomposableAlgebra (C : Type u) [Category.{v} C] [MonoidalCategory C]
    (A : C) [MonObj A]
    [LeftModuleCategory C (Mod_ C A)] : Prop :=
  IsIndecomposableModuleCategory C (Mod_ C A)

end CategoryTheory
