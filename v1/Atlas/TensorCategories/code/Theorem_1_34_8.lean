/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.TannakaBialgebra

open CategoryTheory
open TensorCategories

universe w

noncomputable section

/-- Theorem 1.34.8 (Etingof–Gelaki–Nikshych–Ostrik): The assignments
`(C, F) ↦ H = End(F)` and `H ↦ (Rep(H), Forget)` are mutually inverse bijections
between finite `k`-linear abelian monoidal categories admitting a quasi-fiber functor
and finite-dimensional quasi-bialgebras over `k` up to twist equivalence and isomorphism. -/
theorem theorem_1_34_8
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C]
    (QF : QuasiFiberFunctor k C) :
    ∃ (data : QuasiBialgebraReconstructionData k C),
      Nonempty (MonoidalEquiv_134 C data.RepH) :=
  tannaka_reconstruction_bialgebra_1_34_8 k C QF

/-- Inverse direction of Theorem 1.34.8: a finite-dimensional quasi-bialgebra
gives rise to the data of its representation category equipped with a quasi-fiber
functor. -/
noncomputable def theorem_1_34_8_inverse
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H]
    [QuasiBialgebra k H] [FiniteDimensional k H] :
    QuasiBialgebraRepData k H :=
  tannaka_reconstruction_quasi_bialgebra_inverse k H

/-- Round-trip for the category side of Theorem 1.34.8: reconstructing a
quasi-bialgebra from a category with quasi-fiber functor and then taking its
representations recovers the original category up to monoidal equivalence. -/
noncomputable def theorem_1_34_8_roundtrip_category
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C]
    (QF : QuasiFiberFunctor k C) :
    let data := tannaka_reconstruction_quasi_bialgebra_forward k C QF
    MonoidalEquiv_134 C data.RepH :=
  tannaka_reconstruction_quasi_bialgebra_roundtrip_category k C QF

/-- Round-trip for the algebra side of Theorem 1.34.8: starting from a
finite-dimensional quasi-bialgebra, forming its representation category, and then
reconstructing recovers the original quasi-bialgebra up to algebra isomorphism. -/
theorem theorem_1_34_8_roundtrip_algebra
    (k : Type w) [Field k]
    (H : Type w) [Ring H] [Algebra k H]
    [instQB : QuasiBialgebra k H] [FiniteDimensional k H]
    (repData : QuasiBialgebraRepData k H)
    [instLinear : Linear k repData.RepH]
    (reconData : QuasiBialgebraReconstructionData (C := repData.RepH) k) :
    Nonempty (reconData.H ≃ₐ[k] H) :=
  tannaka_reconstruction_quasi_bialgebra_roundtrip_algebra k H repData reconData

/-- Upper-case alias of `theorem_1_34_8`, stating the Etingof–Gelaki–Nikshych–Ostrik
bijection between finite `k`-linear abelian monoidal categories with a quasi-fiber
functor and finite-dimensional quasi-bialgebras. -/
theorem Theorem_1_34_8
    (k : Type w) [Field k]
    (C : Type (w+1)) [Category.{w} C] [MonoidalCategory C] [Abelian C]
    [Linear k C]
    (QF : QuasiFiberFunctor k C) :
    ∃ (data : QuasiBialgebraReconstructionData k C),
      Nonempty (MonoidalEquiv_134 C data.RepH) :=
  theorem_1_34_8 k C QF

end
