/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.TannakaReconstruction

open CategoryTheory

universe w

/-- Theorem 1.23.2 (Etingof–Gelaki–Nikshych–Ostrik): The assignments
`(C, F) ↦ H = Coend(F)` and `H ↦ (H-Comod, Forget)` give mutually inverse
bijections between three pairs of structures: monoidal categories with fiber
functors and bialgebras; categories with right duals and bialgebras with antipode;
and tensor categories and Hopf algebras. -/
theorem Theorem_1_23_2
    (k : Type w) [Field k] :

    (∀ (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
      [Linear k C]
      (F : C ⥤ ModuleCat.{w} k)
      (hFaithful : F.Faithful)
      (hMono : F.PreservesMonomorphisms)
      (hEpi : F.PreservesEpimorphisms)
      (hMonoidal : F.Monoidal),
      Nonempty (MonoidalTannakaData k C))
    ∧

    (∀ (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
      [Linear k C] [RightRigidCategory C]
      (F : C ⥤ ModuleCat.{w} k)
      (hFaithful : F.Faithful)
      (hMono : F.PreservesMonomorphisms)
      (hEpi : F.PreservesEpimorphisms)
      (hMonoidal : F.Monoidal),
      Nonempty (TannakaWithAntipodeData k C))
    ∧

    (∀ (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
      [Linear k C] [RigidCategory C]
      (F : C ⥤ ModuleCat.{w} k)
      (hFaithful : F.Faithful)
      (hMono : F.PreservesMonomorphisms)
      (hEpi : F.PreservesEpimorphisms)
      (hMonoidal : F.Monoidal),
      Nonempty (TannakaHopfData k C))
    ∧

    (∀ (H : Type w) [Ring H] [Algebra k H] [Bialgebra k H],
      Nonempty (BialgebraComoduleData k H)) :=
  thm_1_23_2 k

/-- Alternative lower-case statement of Theorem 1.23.2 packaging the same
bijections between monoidal categories with fiber functors and bialgebras/Hopf algebras. -/
theorem theorem_1_23_2
    (k : Type w) [Field k] :
    (∀ (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
      [Linear k C]
      (F : C ⥤ ModuleCat.{w} k)
      (hFaithful : F.Faithful)
      (hMono : F.PreservesMonomorphisms)
      (hEpi : F.PreservesEpimorphisms)
      (hMonoidal : F.Monoidal),
      Nonempty (MonoidalTannakaData k C))
    ∧
    (∀ (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
      [Linear k C] [RightRigidCategory C]
      (F : C ⥤ ModuleCat.{w} k)
      (hFaithful : F.Faithful)
      (hMono : F.PreservesMonomorphisms)
      (hEpi : F.PreservesEpimorphisms)
      (hMonoidal : F.Monoidal),
      Nonempty (TannakaWithAntipodeData k C))
    ∧
    (∀ (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
      [Linear k C] [RigidCategory C]
      (F : C ⥤ ModuleCat.{w} k)
      (hFaithful : F.Faithful)
      (hMono : F.PreservesMonomorphisms)
      (hEpi : F.PreservesEpimorphisms)
      (hMonoidal : F.Monoidal),
      Nonempty (TannakaHopfData k C))
    ∧
    (∀ (H : Type w) [Ring H] [Algebra k H] [Bialgebra k H],
      Nonempty (BialgebraComoduleData k H)) :=
  thm_1_23_2 k

/-- Part 1 of Theorem 1.23.2: a monoidal category with a fiber functor produces
a bialgebra (`MonoidalTannakaData`) via `H = Coend(F)`. -/
theorem Theorem_1_23_2_part1
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C]
    (F : C ⥤ ModuleCat.{w} k)
    (hFaithful : F.Faithful)
    (hMono : F.PreservesMonomorphisms)
    (hEpi : F.PreservesEpimorphisms)
    (hMonoidal : F.Monoidal) :
    Nonempty (MonoidalTannakaData k C) :=
  (thm_1_23_2 k).1 C F hFaithful hMono hEpi hMonoidal

/-- Part 2 of Theorem 1.23.2: a monoidal category with right duals and a fiber
functor produces a bialgebra equipped with an antipode (`TannakaWithAntipodeData`). -/
theorem Theorem_1_23_2_part2
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] [RightRigidCategory C]
    (F : C ⥤ ModuleCat.{w} k)
    (hFaithful : F.Faithful)
    (hMono : F.PreservesMonomorphisms)
    (hEpi : F.PreservesEpimorphisms)
    (hMonoidal : F.Monoidal) :
    Nonempty (TannakaWithAntipodeData k C) :=
  (thm_1_23_2 k).2.1 C F hFaithful hMono hEpi hMonoidal

/-- Part 3 of Theorem 1.23.2: a rigid (tensor) category with a fiber functor produces
a Hopf algebra (`TannakaHopfData`). -/
theorem Theorem_1_23_2_part3
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] [RigidCategory C]
    (F : C ⥤ ModuleCat.{w} k)
    (hFaithful : F.Faithful)
    (hMono : F.PreservesMonomorphisms)
    (hEpi : F.PreservesEpimorphisms)
    (hMonoidal : F.Monoidal) :
    Nonempty (TannakaHopfData k C) :=
  (thm_1_23_2 k).2.2.1 C F hFaithful hMono hEpi hMonoidal

/-- Inverse direction of Theorem 1.23.2: a bialgebra `H` over `k` yields the
category of `H`-comodules (`BialgebraComoduleData`). -/
theorem Theorem_1_23_2_inverse
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H] [Bialgebra k H] :
    Nonempty (BialgebraComoduleData k H) :=
  (thm_1_23_2 k).2.2.2 H
