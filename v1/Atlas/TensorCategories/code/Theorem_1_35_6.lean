/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.TannakaReconstruction

set_option maxHeartbeats 800000

noncomputable section

open CategoryTheory TensorCategories

universe w

/-- Reconstruction data for part (i) of Theorem 1.35.6: bundles a finite-dimensional
quasi-bialgebra `H` equipped with an antipode together with the representation category
`Rep(H)` and the monoidal equivalence with `C`. -/
structure QuasiBialgebraAntipodeReconstructionData
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] [RightRigidCategory C] where
  H : Type w
  [instRing : Ring H]
  [instAlgebra : Algebra k H]
  [instFiniteDimensional : FiniteDimensional k H]
  [instQuasiBialgebra : QuasiBialgebra k H]
  instAntipode : QuasiBialgebraAntipode k H
  RepH : Type (w+1)
  [instCategoryRepH : Category.{w} RepH]
  [instMonoidalRepH : MonoidalCategory RepH]
  [instAbelianRepH : Abelian RepH]
  monoidalEquiv : MonoidalEquiv C RepH
  forgetRep : RepH ⥤ ModuleCat.{w} k
  forgetFaithful : forgetRep.Faithful

attribute [instance] QuasiBialgebraAntipodeReconstructionData.instRing
  QuasiBialgebraAntipodeReconstructionData.instAlgebra
  QuasiBialgebraAntipodeReconstructionData.instFiniteDimensional
  QuasiBialgebraAntipodeReconstructionData.instQuasiBialgebra
  QuasiBialgebraAntipodeReconstructionData.instCategoryRepH
  QuasiBialgebraAntipodeReconstructionData.instMonoidalRepH
  QuasiBialgebraAntipodeReconstructionData.instAbelianRepH

/-- Forward direction of Theorem 1.35.6(i): a finite abelian `k`-linear monoidal
category with right duals admitting a quasi-fiber functor yields a finite-dimensional
quasi-bialgebra with antipode. -/
def theorem_1_35_6_i_forward
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] [RightRigidCategory C]
    (QF : QuasiFiberFunctor k C) :
    QuasiBialgebraAntipodeReconstructionData k C := by sorry

/-- Representation data on the algebra side of Theorem 1.35.6(i): the representation
category `Rep(H)` of a quasi-bialgebra with antipode together with its forgetful
functor and the relevant categorical structure (right rigid, etc.). -/
structure QuasiBialgebraAntipodeRepData
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H] [FiniteDimensional k H]
    [QuasiBialgebra k H]
    (antipode : QuasiBialgebraAntipode k H) where
  RepH : Type (w+1)
  [instCategoryRepH : Category.{w} RepH]
  [instMonoidalRepH : MonoidalCategory RepH]
  [instAbelianRepH : Abelian RepH]
  [instRightRigidRepH : @RightRigidCategory RepH instCategoryRepH instMonoidalRepH]
  forgetRep : RepH ⥤ ModuleCat.{w} k
  forgetFaithful : forgetRep.Faithful
  forgetPreservesMono : forgetRep.PreservesMonomorphisms
  forgetPreservesEpi : forgetRep.PreservesEpimorphisms

attribute [instance] QuasiBialgebraAntipodeRepData.instCategoryRepH
  QuasiBialgebraAntipodeRepData.instMonoidalRepH
  QuasiBialgebraAntipodeRepData.instAbelianRepH
  QuasiBialgebraAntipodeRepData.instRightRigidRepH

/-- Inverse direction of Theorem 1.35.6(i): a finite-dimensional quasi-bialgebra
with antipode yields the representation category with its forgetful functor. -/
def theorem_1_35_6_i_inverse
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H] [FiniteDimensional k H]
    [QuasiBialgebra k H]
    (antipode : QuasiBialgebraAntipode k H) :
    QuasiBialgebraAntipodeRepData k H antipode := by sorry

/-- Round-trip for Theorem 1.35.6(i) on the category side: extracting the monoidal
equivalence between `C` and the representation category of the reconstructed
quasi-bialgebra with antipode. -/
def theorem_1_35_6_i_roundtrip_category
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] [RightRigidCategory C]
    (QF : QuasiFiberFunctor k C) :
    let data := theorem_1_35_6_i_forward k C QF
    MonoidalEquiv C data.RepH :=
  (theorem_1_35_6_i_forward k C QF).monoidalEquiv

/-- Round-trip for Theorem 1.35.6(i) on the algebra side: the reconstructed
quasi-bialgebra (with antipode) coming from the representation category of a
quasi-bialgebra with antipode is isomorphic to the original algebra. -/
theorem theorem_1_35_6_i_roundtrip_algebra
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H] [FiniteDimensional k H]
    [qb : QuasiBialgebra k H]
    (antipode : QuasiBialgebraAntipode k H)
    (repData : QuasiBialgebraAntipodeRepData k H antipode)
    [instLinear : Linear k repData.RepH]
    (reconData : QuasiBialgebraAntipodeReconstructionData (C := repData.RepH) k) :

    Nonempty (reconData.H ≃ₐ[k] H) := by sorry

/-- Reconstruction data for part (ii) of Theorem 1.35.6: bundles a finite-dimensional
quasi-Hopf algebra `H` together with its rigid representation category and the
monoidal equivalence between `C` and `Rep(H)`. -/
structure QuasiHopfReconstructionData
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] [RigidCategory C] where
  H : Type w
  [instRing : Ring H]
  [instAlgebra : Algebra k H]
  [instFiniteDimensional : FiniteDimensional k H]
  [instQuasiHopf : QuasiHopfAlgebra k H]
  RepH : Type (w+1)
  [instCategoryRepH : Category.{w} RepH]
  [instMonoidalRepH : MonoidalCategory RepH]
  [instAbelianRepH : Abelian RepH]
  [instRigidRepH : @RigidCategory RepH instCategoryRepH instMonoidalRepH]
  monoidalEquiv : MonoidalEquiv C RepH
  forgetRep : RepH ⥤ ModuleCat.{w} k
  forgetFaithful : forgetRep.Faithful

attribute [instance] QuasiHopfReconstructionData.instRing
  QuasiHopfReconstructionData.instAlgebra
  QuasiHopfReconstructionData.instFiniteDimensional
  QuasiHopfReconstructionData.instQuasiHopf
  QuasiHopfReconstructionData.instCategoryRepH
  QuasiHopfReconstructionData.instMonoidalRepH
  QuasiHopfReconstructionData.instAbelianRepH
  QuasiHopfReconstructionData.instRigidRepH

/-- Forward direction of Theorem 1.35.6(ii): a finite tensor category admitting a
quasi-fiber functor produces a finite-dimensional quasi-Hopf algebra. -/
def theorem_1_35_6_ii_forward
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] [RigidCategory C]
    (QF : QuasiFiberFunctor k C) :
    QuasiHopfReconstructionData k C := by sorry

/-- Representation data on the algebra side of Theorem 1.35.6(ii): packages the
rigid representation category of a finite-dimensional quasi-Hopf algebra together
with its faithful exact forgetful functor to `ModuleCat k`. -/
structure QuasiHopfRepData
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H] [FiniteDimensional k H]
    [QuasiHopfAlgebra k H] where
  RepH : Type (w+1)
  [instCategoryRepH : Category.{w} RepH]
  [instMonoidalRepH : MonoidalCategory RepH]
  [instAbelianRepH : Abelian RepH]
  [instRigidRepH : @RigidCategory RepH instCategoryRepH instMonoidalRepH]
  forgetRep : RepH ⥤ ModuleCat.{w} k
  forgetFaithful : forgetRep.Faithful
  forgetPreservesMono : forgetRep.PreservesMonomorphisms
  forgetPreservesEpi : forgetRep.PreservesEpimorphisms

attribute [instance] QuasiHopfRepData.instCategoryRepH
  QuasiHopfRepData.instMonoidalRepH
  QuasiHopfRepData.instAbelianRepH
  QuasiHopfRepData.instRigidRepH

/-- Inverse direction of Theorem 1.35.6(ii): a finite-dimensional quasi-Hopf
algebra yields the data of its rigid representation category with forgetful functor. -/
def theorem_1_35_6_ii_inverse
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H] [FiniteDimensional k H]
    [QuasiHopfAlgebra k H] :
    QuasiHopfRepData k H := by sorry

/-- Round-trip for Theorem 1.35.6(ii) on the category side: a finite tensor category
admitting a quasi-fiber functor is monoidally equivalent to the representations of
the reconstructed quasi-Hopf algebra. -/
def theorem_1_35_6_ii_roundtrip_category
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C] [RigidCategory C]
    (QF : QuasiFiberFunctor k C) :
    let data := theorem_1_35_6_ii_forward k C QF
    MonoidalEquiv C data.RepH :=
  (theorem_1_35_6_ii_forward k C QF).monoidalEquiv

/-- Round-trip for Theorem 1.35.6(ii) on the algebra side: the reconstructed
quasi-Hopf algebra coming from the representation category of a quasi-Hopf algebra
is isomorphic to the original. -/
theorem theorem_1_35_6_ii_roundtrip_algebra
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H] [FiniteDimensional k H]
    [QuasiHopfAlgebra k H]
    (repData : QuasiHopfRepData k H)
    [instLinear : Linear k repData.RepH]
    (reconData : QuasiHopfReconstructionData (C := repData.RepH) k) :

    Nonempty (reconData.H ≃ₐ[k] H) := by sorry

/-- Alias for `theorem_1_35_6_i_forward` (Theorem 1.35.6(i) forward direction). -/
abbrev Theorem_1_35_6_i_forward := @theorem_1_35_6_i_forward

/-- Alias for `theorem_1_35_6_i_inverse` (Theorem 1.35.6(i) inverse direction). -/
abbrev Theorem_1_35_6_i_inverse := @theorem_1_35_6_i_inverse

/-- Alias for `theorem_1_35_6_ii_forward` (Theorem 1.35.6(ii) forward direction). -/
abbrev Theorem_1_35_6_ii_forward := @theorem_1_35_6_ii_forward

/-- Alias for `theorem_1_35_6_ii_inverse` (Theorem 1.35.6(ii) inverse direction). -/
abbrev Theorem_1_35_6_ii_inverse := @theorem_1_35_6_ii_inverse

/-- Alias for part (i) of Theorem 1.35.6 (forward direction). -/
abbrev Theorem_1_35_6_part_i := @theorem_1_35_6_i_forward

/-- Alias for part (ii) of Theorem 1.35.6 (forward direction). -/
abbrev Theorem_1_35_6_part_ii := @theorem_1_35_6_ii_forward

/-- Top-level alias for Theorem 1.35.6 (bijection between categories admitting
quasi-fiber functors with right duals/rigidity and quasi-bialgebras with
antipode/quasi-Hopf algebras). -/
abbrev Theorem_1_35_6 := @theorem_1_35_6_i_forward

end
