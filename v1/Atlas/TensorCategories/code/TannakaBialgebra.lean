/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Atlas.TensorCategories.code.QuasiBialgebra
import Atlas.TensorCategories.code.QuasiTensorFunctor

set_option maxHeartbeats 800000
set_option autoImplicit false

open CategoryTheory
open TensorCategories

universe u v w

noncomputable section

/-- The bialgebra structure on `End F` for a fiber functor `F : C ⥤ ModuleCat k`,
packaging the algebra and bialgebra instances required by Theorem 1.21.1. -/
structure EndBialgebraStructure
    (k : Type u) [Field k]
    {C : Type (u+1)} [Category.{u} C] [MonoidalCategory C] [Abelian C] [Linear k C]
    (F : C ⥤ ModuleCat.{u} k) where
  algebraInst : Algebra k (End F)
  bialgebraInst : @Bialgebra k (End F) _ (Ring.toSemiring)

/-- Data witnessing the monoidal equivalence `C ≃ Rep(H)` provided by Tannaka reconstruction
for a fiber functor `F`, together with the underlying bialgebra `End F`. -/
structure EndMonoidalEquivData
    (k : Type u) [Field k]
    {C : Type (u+1)} [Category.{u} C] [MonoidalCategory C] [Abelian C] [Linear k C]
    (F : C ⥤ ModuleCat.{u} k) where
  bialg : EndBialgebraStructure k F
  RepH : Type (u+1)
  [instCatRepH : Category.{u} RepH]
  [instMonRepH : MonoidalCategory RepH]
  [instAbRepH : Abelian RepH]
  equiv : C ≌ RepH
  functorMonoidal : equiv.functor.Monoidal
  inverseMonoidal : equiv.inverse.Monoidal
  forgetRep : RepH ⥤ ModuleCat.{u} k
  forgetFaithful : forgetRep.Faithful
  forgetMonoidal : forgetRep.Monoidal
  compatF : F ≅ equiv.functor ⋙ forgetRep

attribute [instance] EndMonoidalEquivData.instCatRepH
  EndMonoidalEquivData.instMonRepH
  EndMonoidalEquivData.instAbRepH

/-- Theorem 1.21.1 (bialgebra part): for a fiber functor `F`, the algebra `End F` carries
a canonical bialgebra structure whose comultiplication and counit are algebra homomorphisms. -/
def thm_1_21_1_bialgebra
    (k : Type u) [Field k]
    {C : Type (u+1)} [Category.{u} C] [MonoidalCategory C] [Abelian C] [Linear k C]
    (F : C ⥤ ModuleCat.{u} k)
    (_hFaithful : F.Faithful)
    (_hExactMono : F.PreservesMonomorphisms)
    (_hExactEpi : F.PreservesEpimorphisms)
    (_hMonoidal : F.Monoidal) :
    EndBialgebraStructure k F := by
  exact sorry

/-- Theorem 1.21.1 (monoidal equivalence part): for a fiber functor `F`, the category `C`
is monoidally equivalent to the representation category of the bialgebra `End F`. -/
def thm_1_21_1_monoidal_equiv
    (k : Type u) [Field k]
    {C : Type (u+1)} [Category.{u} C] [MonoidalCategory C] [Abelian C] [Linear k C]
    (F : C ⥤ ModuleCat.{u} k)
    (_hFaithful : F.Faithful)
    (_hExactMono : F.PreservesMonomorphisms)
    (_hExactEpi : F.PreservesEpimorphisms)
    (_hMonoidal : F.Monoidal) :
    EndMonoidalEquivData k F := by
  exact sorry

/-- Theorem 1.21.1: combined Tannaka reconstruction giving both the bialgebra structure on
`End F` and the monoidal equivalence `C ≃ Rep(End F)`. -/
def thm_1_21_1
    (k : Type u) [Field k]
    {C : Type (u+1)} [Category.{u} C] [MonoidalCategory C] [Abelian C] [Linear k C]
    (F : C ⥤ ModuleCat.{u} k)
    (hFaithful : F.Faithful)
    (hExactMono : F.PreservesMonomorphisms)
    (hExactEpi : F.PreservesEpimorphisms)
    (hMonoidal : F.Monoidal) :
    EndBialgebraStructure k F × EndMonoidalEquivData k F :=
  ⟨thm_1_21_1_bialgebra k F hFaithful hExactMono hExactEpi hMonoidal,
   thm_1_21_1_monoidal_equiv k F hFaithful hExactMono hExactEpi hMonoidal⟩

/-- A bundled monoidal equivalence between two monoidal categories `C` and `D`,
consisting of an underlying equivalence together with monoidal structures on both directions. -/
structure MonoidalEquiv_134
    (C : Type*) [Category C] [MonoidalCategory C]
    (D : Type*) [Category D] [MonoidalCategory D] where
  equiv : C ≌ D
  functorMonoidal : equiv.functor.Monoidal
  inverseMonoidal : equiv.inverse.Monoidal

/-- Data witnessing the reconstruction (Theorem 1.34.8) of a finite-dimensional quasi-bialgebra
`H` from a finite k-linear abelian monoidal category `C` admitting a quasi-fiber functor. -/
structure QuasiBialgebraReconstructionData
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] where
  H : Type w
  [instRing : Ring H]
  [instAlgebra : Algebra k H]
  [instFiniteDimensional : FiniteDimensional k H]
  [instQuasiBialgebra : QuasiBialgebra k H]
  RepH : Type (w+1)
  [instCategoryRepH : Category.{w} RepH]
  [instMonoidalRepH : MonoidalCategory RepH]
  [instAbelianRepH : Abelian RepH]
  monoidalEquiv : MonoidalEquiv_134 C RepH
  forgetRep : RepH ⥤ ModuleCat.{w} k
  forgetFaithful : forgetRep.Faithful

attribute [instance] QuasiBialgebraReconstructionData.instRing
  QuasiBialgebraReconstructionData.instAlgebra
  QuasiBialgebraReconstructionData.instFiniteDimensional
  QuasiBialgebraReconstructionData.instQuasiBialgebra
  QuasiBialgebraReconstructionData.instCategoryRepH
  QuasiBialgebraReconstructionData.instMonoidalRepH
  QuasiBialgebraReconstructionData.instAbelianRepH

/-- Data for the inverse direction of Theorem 1.34.8: from a finite-dimensional quasi-bialgebra `H`,
the representation category `Rep(H)` together with its forgetful (quasi-fiber) functor. -/
structure QuasiBialgebraRepData
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H]
    [QuasiBialgebra k H] [FiniteDimensional k H] where
  RepH : Type (w+1)
  [instCategoryRepH : Category.{w} RepH]
  [instMonoidalRepH : MonoidalCategory RepH]
  [instAbelianRepH : Abelian RepH]
  forgetRep : RepH ⥤ ModuleCat.{w} k
  forgetFaithful : forgetRep.Faithful
  forgetPreservesMono : forgetRep.PreservesMonomorphisms
  forgetPreservesEpi : forgetRep.PreservesEpimorphisms

attribute [instance] QuasiBialgebraRepData.instCategoryRepH
  QuasiBialgebraRepData.instMonoidalRepH
  QuasiBialgebraRepData.instAbelianRepH

/-- Theorem 1.34.8 (forward direction): from a quasi-fiber functor on `C`, reconstruct a
finite-dimensional quasi-bialgebra `H` together with the monoidal equivalence `C ≃ Rep(H)`. -/
def tannaka_reconstruction_quasi_bialgebra_forward
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C]
    (QF : QuasiFiberFunctor k C) :
    QuasiBialgebraReconstructionData k C := by sorry

/-- Theorem 1.34.8 (inverse direction): from a finite-dimensional quasi-bialgebra `H`,
produce the representation category `Rep(H)` equipped with its forgetful quasi-fiber functor. -/
def tannaka_reconstruction_quasi_bialgebra_inverse
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H]
    [QuasiBialgebra k H] [FiniteDimensional k H] :
    QuasiBialgebraRepData k H := by sorry

/-- Roundtrip on the categorical side of Theorem 1.34.8: reconstructing from `C` produces
a category `Rep(H)` monoidally equivalent to `C`. -/
def tannaka_reconstruction_quasi_bialgebra_roundtrip_category
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C]
    (QF : QuasiFiberFunctor k C) :
    let data := tannaka_reconstruction_quasi_bialgebra_forward k C QF
    MonoidalEquiv_134 C data.RepH :=
  (tannaka_reconstruction_quasi_bialgebra_forward k C QF).monoidalEquiv

/-- Roundtrip on the algebraic side of Theorem 1.34.8: reconstructing from `Rep(H)`
recovers a quasi-bialgebra isomorphic to the original `H`. -/
theorem tannaka_reconstruction_quasi_bialgebra_roundtrip_algebra
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H]
    [instQB : QuasiBialgebra k H] [FiniteDimensional k H]
    (repData : QuasiBialgebraRepData k H)
    [instLinear : Linear k repData.RepH]
    (reconData : QuasiBialgebraReconstructionData (C := repData.RepH) k) :
    Nonempty (reconData.H ≃ₐ[k] H) := by sorry

/-- Theorem 1.34.8: any quasi-fiber functor `(F, J) : C → Vec` on a finite k-linear abelian
monoidal category `C` reconstructs a finite-dimensional quasi-bialgebra `H` with `C ≃ Rep(H)`. -/
theorem tannaka_reconstruction_bialgebra_1_34_8
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C]
    (QF : QuasiFiberFunctor k C) :
    ∃ (data : QuasiBialgebraReconstructionData k C),

      Nonempty (MonoidalEquiv_134 C data.RepH) :=
  ⟨tannaka_reconstruction_quasi_bialgebra_forward k C QF,
   ⟨(tannaka_reconstruction_quasi_bialgebra_forward k C QF).monoidalEquiv⟩⟩

end
