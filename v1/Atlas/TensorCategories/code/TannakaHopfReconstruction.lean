/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.TannakaReconstruction

open CategoryTheory

universe w

/-- Theorem 1.22.11: Tannaka-Krein reconstruction gives a bijection between finite tensor
categories with a fiber functor (up to monoidal equivalence) and finite-dimensional Hopf
algebras (up to isomorphism), via `(C, F) ↦ End(F)` and `H ↦ (Rep(H), Forget)`. -/
theorem thm_1_22_11
    (k : Type w) [Field k] :

    (∀ (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
      [Linear k C] [RigidCategory C]
      (F : C ⥤ ModuleCat.{w} k)
      (hFaithful : F.Faithful)
      (hMono : F.PreservesMonomorphisms)
      (hEpi : F.PreservesEpimorphisms)
      (hMonoidal : F.Monoidal),
      Nonempty (FiniteTannakaHopfData k C))
    ∧

    (∀ (H : Type w) [Ring H] [Algebra k H] [HopfAlgebra k H] [FiniteDimensional k H],
      Nonempty (HopfAlgebraRepData k H))
    ∧


    (∀ (H : Type w) [Ring H] [Algebra k H] [HopfAlgebra k H] [FiniteDimensional k H]
      (repData : HopfAlgebraRepData k H)
      [instLinear : Linear k repData.RepH]
      (reconData : FiniteTannakaHopfData (C := repData.RepH) k),
      Nonempty (BialgebraEquiv k reconData.H H)) := by
  exact ⟨fun C _ _ _ _ _ F hF hM hE hMon =>
    ⟨tannaka_hopf_reconstruction k C F hF hM hE hMon⟩,
   fun H _ _ _ _ => ⟨tannaka_hopf_inverse k H⟩,
   fun H _ _ _ _ repData _ reconData =>
    tannaka_hopf_roundtrip_algebra k H repData reconData⟩
