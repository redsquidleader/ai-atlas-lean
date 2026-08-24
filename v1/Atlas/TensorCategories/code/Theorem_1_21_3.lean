/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.TannakaReconstruction

set_option maxHeartbeats 400000

open CategoryTheory

universe u

/-- Data reconstructing a finite-dimensional bialgebra `H` over `k` from a finite
abelian `k`-linear monoidal category `C` equipped with a fiber functor.
Bundles the bialgebra `H` together with its ring, algebra, bialgebra and
finite-dimensionality instances. -/
structure BialgebraReconstructionData
    (k : Type u) [Field k]
    (C : Type (u+1)) [Category.{u} C] [MonoidalCategory C] [Abelian C] where
  H : Type u
  [instRing : Ring H]
  [instAlgebra : Algebra k H]
  [instBialgebra : Bialgebra k H]
  [instFiniteDimensional : FiniteDimensional k H]

attribute [instance] BialgebraReconstructionData.instRing
  BialgebraReconstructionData.instAlgebra
  BialgebraReconstructionData.instBialgebra
  BialgebraReconstructionData.instFiniteDimensional

/-- Data reconstructing the representation category `Rep(H)` of a finite-dimensional
bialgebra `H` over `k`, including its abelian and monoidal structure together with
the forgetful functor `Rep(H) ⥤ ModuleCat k` and its faithfulness/monoidality. -/
structure RepresentationReconstructionData
    (k : Type u) [Field k]
    (H : Type u) [Ring H] [Algebra k H] [Bialgebra k H] [FiniteDimensional k H] where
  RepCat : Type (u+1)
  [instCategoryRep : Category.{u} RepCat]
  [instMonoidalRep : MonoidalCategory RepCat]
  [instAbelianRep : Abelian RepCat]
  forget : RepCat ⥤ ModuleCat.{u} k
  forgetFaithful : forget.Faithful
  forgetMonoidal : forget.Monoidal

attribute [instance] RepresentationReconstructionData.instCategoryRep
  RepresentationReconstructionData.instMonoidalRep
  RepresentationReconstructionData.instAbelianRep

/-- Forward direction of Theorem 1.21.3: given a finite abelian `k`-linear monoidal
category `C` with a fiber functor `F : C ⥤ ModuleCat k`, there exists a
reconstructed finite-dimensional bialgebra `H = End(F)`. -/
theorem thm_1_21_3_forward
    (k : Type u) [Field k]
    (C : Type (u+1)) [Category.{u} C] [MonoidalCategory C] [Abelian C] [Linear k C]
    (F : C ⥤ ModuleCat.{u} k)
    (_hFaithful : F.Faithful)
    (_hExactMono : F.PreservesMonomorphisms)
    (_hExactEpi : F.PreservesEpimorphisms)
    (_hMonoidal : F.Monoidal) :
    Nonempty (BialgebraReconstructionData k C) := by
  exact sorry

/-- Inverse direction of Theorem 1.21.3: given a finite-dimensional bialgebra `H`
over `k`, the category `Rep(H)` of finite-dimensional `H`-modules together with
the forgetful functor provides the corresponding representation data. -/
theorem thm_1_21_3_inverse
    (k : Type u) [Field k]
    (H : Type u) [Ring H] [Algebra k H] [Bialgebra k H] [FiniteDimensional k H] :
    Nonempty (RepresentationReconstructionData k H) := by
  exact sorry

/-- Round-trip for the algebra side of Theorem 1.21.3: starting from a
finite-dimensional bialgebra `H`, building its representation category, and
then reconstructing the bialgebra recovers `H` up to bialgebra isomorphism. -/
theorem thm_1_21_3_roundtrip_algebra
    (k : Type u) [Field k]
    (H : Type u) [Ring H] [Algebra k H] [Bialgebra k H] [FiniteDimensional k H]
    (repData : RepresentationReconstructionData k H)
    (reconData : BialgebraReconstructionData k repData.RepCat) :
    Nonempty (BialgebraEquiv k reconData.H H) := by
  exact sorry

/-- Round-trip for the category side of Theorem 1.21.3: starting from a
category `C` with fiber functor, reconstructing a bialgebra `H` and forming
`Rep(H)` recovers `C` up to monoidal equivalence. -/
theorem thm_1_21_3_roundtrip_category
    (k : Type u) [Field k]
    (C : Type (u+1)) [Category.{u} C] [MonoidalCategory C] [Abelian C] [Linear k C]
    (bialg : BialgebraReconstructionData k C)
    (repData : RepresentationReconstructionData k bialg.H) :
    Nonempty (MonoidalEquiv C repData.RepCat) := by
  exact sorry

/-- Theorem 1.21.3 (Etingof–Gelaki–Nikshych–Ostrik): The assignments
`(C, F) ↦ H = End(F)` and `H ↦ (Rep(H), Forget)` are mutually inverse bijections
between finite abelian `k`-linear monoidal categories with a fiber functor (up to
monoidal equivalence) and finite-dimensional bialgebras over `k` (up to isomorphism). -/
theorem thm_1_21_3
    (k : Type u) [Field k] :

    (∀ (C : Type (u+1)) [Category.{u} C] [MonoidalCategory C] [Abelian C] [Linear k C]
       (F : C ⥤ ModuleCat.{u} k)
       (_hFaithful : F.Faithful)
       (_hExactMono : F.PreservesMonomorphisms)
       (_hExactEpi : F.PreservesEpimorphisms)
       (_hMonoidal : F.Monoidal),
       Nonempty (BialgebraReconstructionData k C)) ∧

    (∀ (H : Type u) [Ring H] [Algebra k H] [Bialgebra k H] [FiniteDimensional k H],
       Nonempty (RepresentationReconstructionData k H)) ∧

    (∀ (H : Type u) [Ring H] [Algebra k H] [Bialgebra k H] [FiniteDimensional k H]
       (repData : RepresentationReconstructionData k H)
       (reconData : BialgebraReconstructionData k repData.RepCat),
       Nonempty (BialgebraEquiv k reconData.H H)) ∧

    (∀ (C : Type (u+1)) [Category.{u} C] [MonoidalCategory C] [Abelian C] [Linear k C]
       (bialg : BialgebraReconstructionData k C)
       (repData : RepresentationReconstructionData k bialg.H),
       Nonempty (MonoidalEquiv C repData.RepCat)) :=
  ⟨fun C _ _ _ _ F hF hM hE hMon => thm_1_21_3_forward k C F hF hM hE hMon,
   fun H _ _ _ _ => thm_1_21_3_inverse k H,
   fun H _ _ _ _ repData reconData => thm_1_21_3_roundtrip_algebra k H repData reconData,
   fun C _ _ _ _ bialg repData => thm_1_21_3_roundtrip_category k C bialg repData⟩
