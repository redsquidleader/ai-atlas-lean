/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.TannakaHopfReconstruction

open CategoryTheory

universe w

/-- Theorem 1.22.11 (Etingof–Gelaki–Nikshych–Ostrik): The assignments
`(C, F) ↦ H = End(F)` and `H ↦ (Rep(H), Forget)` are mutually inverse bijections
between finite tensor categories `C` with a fiber functor `F` (up to monoidal
equivalence) and finite-dimensional Hopf algebras over `k` (up to isomorphism). -/
theorem Theorem_1_22_11
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
      Nonempty (BialgebraEquiv k reconData.H H)) :=
  thm_1_22_11 k

/-- Alternative lower-case statement of Theorem 1.22.11 giving the same bijection
between finite tensor categories with a fiber functor and finite-dimensional
Hopf algebras over `k`. -/
theorem theorem_1_22_11
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
      Nonempty (BialgebraEquiv k reconData.H H)) :=
  thm_1_22_11 k
