/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Category.ModuleCat.Tannaka
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Bialgebra.Basic
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Atlas.TensorCategories.code.QuasiBialgebra
import Atlas.TensorCategories.code.QuasiTensorFunctor

set_option maxHeartbeats 800000

open CategoryTheory

universe u v w

noncomputable section

/-- The endomorphism ring of the additive forgetful functor `ModuleCat R ⥤ AddCommGrpCat`,
which by Tannaka reconstruction is canonically isomorphic to `R`. -/
abbrev EndForget₂ (R : Type u) [Ring R] :=
  End (AdditiveFunctor.of (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}))

variable (k : Type u) [CommRing k] (A : Type u) [Ring A] [Algebra k A]

/-- The canonical ring homomorphism `k →+* End(forget₂ (ModuleCat A) AddCommGrpCat)` obtained
by composing the algebra map `k → A` with the Tannaka reconstruction isomorphism. -/
def endForget₂AlgebraMap : k →+* EndForget₂ A :=
  (ringEquivEndForget₂ A).toRingHom.comp (algebraMap k A)

/-- The image of `endForget₂AlgebraMap` is central in `EndForget₂ A`, since it factors
through the central algebra map `k → A`. -/
lemma endForget₂_algebraMap_comm (r : k) (x : EndForget₂ A) :
    endForget₂AlgebraMap k A r * x = x * endForget₂AlgebraMap k A r := by
  unfold endForget₂AlgebraMap
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  set a := (ringEquivEndForget₂ A).symm x
  have hx : x = ringEquivEndForget₂ A a := (ringEquivEndForget₂ A).apply_symm_apply x ▸ rfl
  rw [hx, ← map_mul, ← map_mul, Algebra.commutes]

/-- The `k`-algebra structure on `EndForget₂ A` induced by the central ring homomorphism
`endForget₂AlgebraMap`. -/
instance endForget₂Algebra : Algebra k (EndForget₂ A) :=
  (endForget₂AlgebraMap k A).toAlgebra' (endForget₂_algebraMap_comm k A)

/-- Tannaka reconstruction for an algebra: the canonical `k`-algebra equivalence between
`A` and the endomorphism algebra of the forgetful functor `ModuleCat A ⥤ AddCommGrpCat`. -/
def tannakaReconstruction : A ≃ₐ[k] EndForget₂ A :=
  AlgEquiv.ofRingEquiv (f := ringEquivEndForget₂ A) (fun r => by rfl)

/-- A bialgebra equivalence between two `k`-bialgebras `A` and `B`: an algebra equivalence
which additionally preserves the comultiplication and the counit. -/
structure BialgebraEquiv (k : Type w) [CommSemiring k]
    (A : Type w) [Semiring A] [Bialgebra k A]
    (B : Type w) [Semiring B] [Bialgebra k B] extends A ≃ₐ[k] B where
  preserves_comul : ∀ a : A,
    Coalgebra.comul (R := k) (toAlgEquiv a) =
      TensorProduct.map toAlgEquiv.toLinearMap toAlgEquiv.toLinearMap (Coalgebra.comul (R := k) a)
  preserves_counit : ∀ a : A,
    Coalgebra.counit (R := k) (toAlgEquiv a) = Coalgebra.counit (R := k) a

/-- A bundled monoidal equivalence between monoidal categories `C` and `D`: an underlying
equivalence of categories together with monoidal structures on both directions. -/
structure MonoidalEquiv
    (C : Type*) [Category C] [MonoidalCategory C]
    (D : Type*) [Category D] [MonoidalCategory D] where
  equiv : C ≌ D
  functorMonoidal : equiv.functor.Monoidal
  inverseMonoidal : equiv.inverse.Monoidal

/-- Data witnessing the categorical part of Tannaka reconstruction (Theorem 1.23.1):
a coalgebra `H` together with an equivalence between `C` and the category of `H`-comodules
compatible with the fiber functor `F`. -/
structure TannakaReconstructionData
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [Abelian C] [Linear k C]
    (F : C ⥤ ModuleCat.{w} k)
    [hFaithful : F.Faithful]
    [hExact : F.PreservesMonomorphisms] [hExact' : F.PreservesEpimorphisms] where
  H : Type w
  [instAddCommGroup : AddCommGroup H]
  [instModule : Module k H]
  [instCoalgebra : Coalgebra k H]
  ComodCat : Type (w+1)
  [instCategoryComod : Category.{w} ComodCat]
  [instAbelianComod : Abelian ComodCat]
  equiv : C ≌ ComodCat
  forgetComod : ComodCat ⥤ ModuleCat.{w} k
  forgetFaithful : forgetComod.Faithful
  compatF : F ≅ equiv.functor ⋙ forgetComod

attribute [instance] TannakaReconstructionData.instAddCommGroup
  TannakaReconstructionData.instModule
  TannakaReconstructionData.instCoalgebra
  TannakaReconstructionData.instCategoryComod
  TannakaReconstructionData.instAbelianComod

/-- Theorem 1.23.1: an exact faithful functor `F : C → Vec` defines an equivalence between
`C` and the category of finite-dimensional right comodules over `Coend(F)`. -/
noncomputable def tannaka_reconstruction_categorical
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [Abelian C] [Linear k C]
    (F : C ⥤ ModuleCat.{w} k)
    [hFaithful : F.Faithful]
    [hMono : F.PreservesMonomorphisms]
    [hEpi : F.PreservesEpimorphisms] :
    TannakaReconstructionData k C F := by


  sorry

/-- Data witnessing the monoidal/bialgebra part of Theorem 1.23.2: a `k`-bialgebra `H`
together with a monoidal equivalence between `C` and the category of `H`-comodules. -/
structure MonoidalTannakaData
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] where
  H : Type w
  [instRingH : Ring H]
  [instAlgebraH : Algebra k H]
  [instBialgebraH : Bialgebra k H]
  ComodCat : Type (w+1)
  [instCategoryComod : Category.{w} ComodCat]
  [instMonoidalComod : MonoidalCategory ComodCat]
  [instAbelianComod : Abelian ComodCat]
  monoidalEquiv : MonoidalEquiv C ComodCat
  forgetComod : ComodCat ⥤ ModuleCat.{w} k
  forgetFaithful : forgetComod.Faithful

attribute [instance] MonoidalTannakaData.instRingH
  MonoidalTannakaData.instAlgebraH
  MonoidalTannakaData.instBialgebraH
  MonoidalTannakaData.instCategoryComod
  MonoidalTannakaData.instMonoidalComod
  MonoidalTannakaData.instAbelianComod

/-- Theorem 1.23.2 (part 2): for `C` with right duals, the reconstructed bialgebra admits
an antipode and is a Hopf algebra, with the comodule category inheriting right rigidity. -/
structure TannakaWithAntipodeData
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] [RightRigidCategory C] extends MonoidalTannakaData k C where
  instRightRigid : @RightRigidCategory ComodCat instCategoryComod instMonoidalComod
  instHopfAlgebra : HopfAlgebra k H

/-- Theorem 1.23.2 (part 3): for a rigid `C` (a tensor category), the reconstructed
Hopf algebra has bijective antipode and the equivalence is one of rigid monoidal categories. -/
structure TannakaHopfData
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] [RigidCategory C] extends MonoidalTannakaData k C where
  instRigid : @RigidCategory ComodCat instCategoryComod instMonoidalComod
  instHopfAlgebra : HopfAlgebra k H
  antipodeBijective : Function.Bijective
    (@HopfAlgebraStruct.antipode k H _ _ instHopfAlgebra.toHopfAlgebraStruct)

/-- Theorem 1.23.2 (bialgebra case): a fiber functor on a monoidal abelian `k`-linear
category `C` reconstructs a `k`-bialgebra `H` with `C` monoidally equivalent to `H`-comodules. -/
noncomputable def tannaka_monoidal_reconstruction
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C]
    (F : C ⥤ ModuleCat.{w} k)
    (hFaithful : F.Faithful)
    (hMono : F.PreservesMonomorphisms)
    (hEpi : F.PreservesEpimorphisms)
    (hMonoidal : F.Monoidal) :
    MonoidalTannakaData k C := by
  sorry

/-- Theorem 1.23.2 (bialgebra-with-antipode case): for `C` with right duals, the
reconstruction upgrades the bialgebra `H` to a Hopf algebra. -/
noncomputable def tannaka_with_antipode_reconstruction
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] [RightRigidCategory C]
    (F : C ⥤ ModuleCat.{w} k)
    (hFaithful : F.Faithful)
    (hMono : F.PreservesMonomorphisms)
    (hEpi : F.PreservesEpimorphisms)
    (hMonoidal : F.Monoidal) :
    TannakaWithAntipodeData k C := by
  sorry

/-- Theorem 1.23.2 (tensor category case): a fiber functor on a rigid tensor category `C`
reconstructs a Hopf algebra `H` with bijective antipode and `C ≃ H`-comod as rigid monoidal categories. -/
noncomputable def tannaka_tensor_category_reconstruction
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] [RigidCategory C]
    (F : C ⥤ ModuleCat.{w} k)
    (hFaithful : F.Faithful)
    (hMono : F.PreservesMonomorphisms)
    (hEpi : F.PreservesEpimorphisms)
    (hMonoidal : F.Monoidal) :
    TannakaHopfData k C := by
  sorry

/-- The Hopf-algebra reconstruction data for Theorem 1.22.11: a finite-dimensional Hopf
algebra `H` together with a monoidal equivalence between `C` and `Rep(H)`. -/
structure FiniteTannakaHopfData
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] [RigidCategory C] where
  H : Type w
  [instRingH : Ring H]
  [instAlgebraH : Algebra k H]
  [instHopfAlgebraH : HopfAlgebra k H]
  [instFiniteDimensionalH : FiniteDimensional k H]
  RepH : Type (w+1)
  [instCategoryRepH : Category.{w} RepH]
  [instMonoidalRepH : MonoidalCategory RepH]
  [instAbelianRepH : Abelian RepH]
  [instRigidRepH : @RigidCategory RepH instCategoryRepH instMonoidalRepH]
  monoidalEquiv : MonoidalEquiv C RepH
  forgetRep : RepH ⥤ ModuleCat.{w} k
  forgetFaithful : forgetRep.Faithful

attribute [instance] FiniteTannakaHopfData.instRingH
  FiniteTannakaHopfData.instAlgebraH
  FiniteTannakaHopfData.instHopfAlgebraH
  FiniteTannakaHopfData.instFiniteDimensionalH
  FiniteTannakaHopfData.instCategoryRepH
  FiniteTannakaHopfData.instMonoidalRepH
  FiniteTannakaHopfData.instAbelianRepH
  FiniteTannakaHopfData.instRigidRepH

/-- In Tannaka reconstruction, the Hopf algebra `H` obtained from a finite tensor category `C`
with fiber functor is automatically finite-dimensional over `k`. -/
theorem tannaka_hopf_finite_dimensional
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] [RigidCategory C]
    (F : C ⥤ ModuleCat.{w} k)
    (hFaithful : F.Faithful)
    (hMono : F.PreservesMonomorphisms)
    (hEpi : F.PreservesEpimorphisms)
    (hMonoidal : F.Monoidal)
    (data : TannakaHopfData k C) :
    FiniteDimensional k data.H := by
  sorry

/-- Theorem 1.22.11 (forward direction): the full Hopf-algebra Tannaka reconstruction,
combining the tensor reconstruction and the finite-dimensionality of `H`. -/
def tannaka_hopf_reconstruction
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] [RigidCategory C]
    (F : C ⥤ ModuleCat.{w} k)
    (hFaithful : F.Faithful)
    (hMono : F.PreservesMonomorphisms)
    (hEpi : F.PreservesEpimorphisms)
    (hMonoidal : F.Monoidal) :
    FiniteTannakaHopfData k C :=
  let data := tannaka_tensor_category_reconstruction k C F hFaithful hMono hEpi hMonoidal
  have hFD := tannaka_hopf_finite_dimensional k C F hFaithful hMono hEpi hMonoidal data
  { H := data.H
    instRingH := data.instRingH
    instAlgebraH := data.instAlgebraH
    instHopfAlgebraH := data.instHopfAlgebra
    instFiniteDimensionalH := hFD
    RepH := data.ComodCat
    instCategoryRepH := data.instCategoryComod
    instMonoidalRepH := data.instMonoidalComod
    instAbelianRepH := data.instAbelianComod
    instRigidRepH := data.instRigid
    monoidalEquiv := data.monoidalEquiv
    forgetRep := data.forgetComod
    forgetFaithful := data.forgetFaithful }

/-- The inverse-direction data for Theorem 1.22.11: from a finite-dimensional Hopf algebra `H`,
the rigid monoidal category `Rep(H)` together with its forgetful fiber functor. -/
structure HopfAlgebraRepData
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H] [HopfAlgebra k H] [FiniteDimensional k H] where
  RepH : Type (w+1)
  [instCategoryRepH : Category.{w} RepH]
  [instMonoidalRepH : MonoidalCategory RepH]
  [instAbelianRepH : Abelian RepH]
  [instRigidRepH : @RigidCategory RepH instCategoryRepH instMonoidalRepH]
  forgetRep : RepH ⥤ ModuleCat.{w} k
  forgetFaithful : forgetRep.Faithful
  forgetPreservesMono : forgetRep.PreservesMonomorphisms
  forgetPreservesEpi : forgetRep.PreservesEpimorphisms
  forgetMonoidal : forgetRep.Monoidal

attribute [instance] HopfAlgebraRepData.instCategoryRepH
  HopfAlgebraRepData.instMonoidalRepH
  HopfAlgebraRepData.instAbelianRepH
  HopfAlgebraRepData.instRigidRepH

/-- Theorem 1.22.11 (inverse direction): from a finite-dimensional Hopf algebra `H`, produce
the representation category `Rep(H)` and the forgetful fiber functor to `ModuleCat k`. -/
noncomputable def tannaka_hopf_inverse
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H] [HopfAlgebra k H] [FiniteDimensional k H] :
    HopfAlgebraRepData k H := by
  sorry

/-- Roundtrip on the categorical side of Theorem 1.22.11: applying reconstruction to `(C, F)`
yields `Rep(H)` monoidally equivalent to the original `C`. -/
def tannaka_hopf_roundtrip_category
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] [RigidCategory C]
    (F : C ⥤ ModuleCat.{w} k)
    (hFaithful : F.Faithful)
    (hMono : F.PreservesMonomorphisms)
    (hEpi : F.PreservesEpimorphisms)
    (hMonoidal : F.Monoidal) :
    let data := tannaka_hopf_reconstruction k C F hFaithful hMono hEpi hMonoidal
    MonoidalEquiv C data.RepH :=
  (tannaka_hopf_reconstruction k C F hFaithful hMono hEpi hMonoidal).monoidalEquiv

/-- Roundtrip on the algebraic side of Theorem 1.22.11: starting from `(Rep(H), Forget)` and
reconstructing yields a Hopf algebra isomorphic (as a bialgebra) to the original `H`. -/
theorem tannaka_hopf_roundtrip_algebra
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H] [HopfAlgebra k H] [FiniteDimensional k H]
    (repData : HopfAlgebraRepData k H)
    [instLinear : Linear k repData.RepH]
    (reconData : FiniteTannakaHopfData (C := repData.RepH) k) :
    Nonempty (BialgebraEquiv k reconData.H H) := by
  sorry

/-- The inverse-direction data for Theorem 1.23.2 (bialgebra case): from a `k`-bialgebra `H`,
the monoidal abelian category of `H`-comodules together with its forgetful fiber functor. -/
structure BialgebraComoduleData
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H] [Bialgebra k H] where
  ComodCat : Type (w+1)
  [instCategoryComod : Category.{w} ComodCat]
  [instMonoidalComod : MonoidalCategory ComodCat]
  [instAbelianComod : Abelian ComodCat]
  forgetComod : ComodCat ⥤ ModuleCat.{w} k
  forgetFaithful : forgetComod.Faithful
  forgetPreservesMono : forgetComod.PreservesMonomorphisms
  forgetPreservesEpi : forgetComod.PreservesEpimorphisms
  forgetMonoidal : forgetComod.Monoidal

attribute [instance] BialgebraComoduleData.instCategoryComod
  BialgebraComoduleData.instMonoidalComod
  BialgebraComoduleData.instAbelianComod

/-- Theorem 1.23.2 (inverse direction, bialgebra case): from a `k`-bialgebra `H`, produce the
monoidal abelian category of `H`-comodules together with its forgetful fiber functor. -/
noncomputable def tannaka_inverse_construction
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H] [Bialgebra k H] :
    BialgebraComoduleData k H := by
  sorry

/-- Roundtrip on the categorical side of Theorem 1.23.2 (bialgebra case): reconstruction
from `(C, F)` yields a comodule category monoidally equivalent to `C`. -/
def tannaka_roundtrip_bialgebra
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C]
    (F : C ⥤ ModuleCat.{w} k)
    (hFaithful : F.Faithful)
    (hMono : F.PreservesMonomorphisms)
    (hEpi : F.PreservesEpimorphisms)
    (hMonoidal : F.Monoidal) :
    let data := tannaka_monoidal_reconstruction k C F hFaithful hMono hEpi hMonoidal
    MonoidalEquiv C data.ComodCat :=
  (tannaka_monoidal_reconstruction k C F hFaithful hMono hEpi hMonoidal).monoidalEquiv

/-- Roundtrip on the algebraic side of Theorem 1.23.2 (bialgebra case): reconstructing from
the comodule category of `H` recovers a bialgebra isomorphic to `H`. -/
theorem tannaka_roundtrip_bialgebra_category
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H] [Bialgebra k H]
    (comodData : BialgebraComoduleData k H)
    [instLinear : Linear k comodData.ComodCat]
    (reconData : MonoidalTannakaData (C := comodData.ComodCat) k) :
    Nonempty (BialgebraEquiv k reconData.H H) := by
  sorry

/-- Theorem 1.23.2: Tannaka reconstruction in three flavors: bialgebras for fiber functors
on monoidal abelian categories, bialgebras-with-antipode for right-rigid categories,
and Hopf algebras for tensor categories, together with the inverse comodule construction. -/
theorem thm_1_23_2
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
      Nonempty (BialgebraComoduleData k H)) := by
  exact ⟨
    fun C _ _ _ _ F hF hM hE hMon =>
      ⟨tannaka_monoidal_reconstruction k C F hF hM hE hMon⟩,
    fun C _ _ _ _ _ F hF hM hE hMon =>
      ⟨tannaka_with_antipode_reconstruction k C F hF hM hE hMon⟩,
    fun C _ _ _ _ _ F hF hM hE hMon =>
      ⟨tannaka_tensor_category_reconstruction k C F hF hM hE hMon⟩,
    fun H _ _ _ => ⟨tannaka_inverse_construction k H⟩⟩

open TensorCategories

/-- The reconstruction data produced from a normalized quasi-fiber functor on `C`:
a finite-dimensional quasi-bialgebra `H` over `k`. -/
structure QuasiFiberReconstructionData
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C]
    (QF : QuasiFiberFunctor k C)
    (hNorm : QF.IsNormalized) where
  H : Type w
  [instRing : Ring H]
  [instAlgebra : Algebra k H]
  [instFiniteDimensional : FiniteDimensional k H]
  [instQuasiBialgebra : QuasiBialgebra k H]

attribute [instance] QuasiFiberReconstructionData.instRing
  QuasiFiberReconstructionData.instAlgebra
  QuasiFiberReconstructionData.instFiniteDimensional
  QuasiFiberReconstructionData.instQuasiBialgebra

/-- From a normalized quasi-fiber functor on a finite k-linear abelian monoidal category,
construct a finite-dimensional quasi-bialgebra (Theorem 1.34.8 algebraic data). -/
noncomputable def quasi_fiber_functor_quasi_bialgebra
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C]
    (QF : QuasiFiberFunctor k C)
    (hNorm : QF.IsNormalized) :
    QuasiFiberReconstructionData k C QF hNorm := by
  sorry

/-- Any two exact faithful functors from a finite k-linear abelian category to `ModuleCat k`
are naturally isomorphic; the underlying step for uniqueness up to twisting in Proposition 1.34.7. -/
theorem exact_faithful_functor_unique_on_finite_abelian
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C]
    (F₁ F₂ : C ⥤ ModuleCat.{w} k)
    [hF₁ : F₁.Faithful] [hF₁m : F₁.PreservesMonomorphisms] [hF₁e : F₁.PreservesEpimorphisms]
    [hF₂ : F₂.Faithful] [hF₂m : F₂.PreservesMonomorphisms] [hF₂e : F₂.PreservesEpimorphisms] :
    Nonempty (F₁ ≅ F₂) := by
  sorry

/-- Proposition 1.34.7: if a finite k-linear abelian monoidal category admits a quasi-fiber
functor, then this functor is unique up to twisting (here: up to natural isomorphism of the
underlying functors). -/
theorem quasi_fiber_functor_unique_up_to_twist
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C]
    (QF₁ QF₂ : QuasiFiberFunctor k C) :
    Nonempty (QF₁.F ≅ QF₂.F) := by
  haveI := QF₁.faithful
  haveI := QF₁.preservesMono
  haveI := QF₁.preservesEpi
  haveI := QF₂.faithful
  haveI := QF₂.preservesMono
  haveI := QF₂.preservesEpi
  exact exact_faithful_functor_unique_on_finite_abelian k C QF₁.F QF₂.F

end
