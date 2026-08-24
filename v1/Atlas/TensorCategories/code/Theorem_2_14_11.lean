/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.DualCategory

set_option maxHeartbeats 800000

universe v u

namespace CategoryTheory

end CategoryTheory

open CategoryTheory in
/-- Theorem 2.14.11: Let `M` be an exact module category over `C`. The assignments
`M₁ ↦ Fun_C(M₁, M)` and `M₂ ↦ Fun_{C^*_M}(M₂, M)` are mutually inverse bijections
between equivalence classes of exact module categories over `C` and over the dual
category `C^*_M`. -/
theorem Theorem_2_14_11
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {M : Type u} [Category.{v} M] [LeftModuleCategory C M]
    [ExactModuleCategory C M]
    [inst : LeftModuleCategory (DualCatObj C M) M] :


    (∀ (M₁ : Type u) [Category.{v} M₁] [ExactModuleCategory C M₁]
       [Category.{v} (ModuleFunctor C M₁ M)],
       ∃ (_ : ExactModuleCategory (DualCatObj C M) (ModuleFunctor C M₁ M))
         (Ψ_Φ_M₁ : Type (max u v))
         (_ : Category.{v} Ψ_Φ_M₁)
         (_ : ExactModuleCategory C Ψ_Φ_M₁),
         Nonempty (ModuleEquivalence C Ψ_Φ_M₁ M₁)) ∧


    (∀ (M₂ : Type u) [Category.{v} M₂] [ExactModuleCategory (DualCatObj C M) M₂]
       [Category.{v} (ModuleFunctor (DualCatObj C M) M₂ M)],
       ∃ (_ : ExactModuleCategory C (ModuleFunctor (DualCatObj C M) M₂ M))
         (Φ_Ψ_M₂ : Type (max u v))
         (_ : Category.{v} Φ_Ψ_M₂)
         (_ : ExactModuleCategory (DualCatObj C M) Φ_Ψ_M₂),
         Nonempty (ModuleEquivalence (DualCatObj C M) Φ_Ψ_M₂ M₂)) :=
  ⟨fun M₁ => DualCatObj.morita_equivalence_forward M₁,
   fun M₂ => DualCatObj.morita_equivalence_backward M₂⟩
