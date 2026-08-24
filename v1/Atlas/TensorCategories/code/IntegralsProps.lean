/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.IntegralsDefs
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option maxHeartbeats 400000

set_option autoImplicit false

open Coalgebra Submodule
open scoped TensorProduct

universe u v


/-- One direction of Proposition 1.52.5: in a finite dimensional semisimple ring `H`, the
counit of any nonzero left integral is nonzero. -/
theorem semisimple_implies_counit_ne_zero
    {k : Type u} [Field k] {H : Type v} [Ring H] [Algebra k H]
    [FiniteDimensional k H] [Coalgebra k H]
    {I : H} (hI : IsLeftIntegral k H I) (hI_ne : I ≠ 0)
    (hss : IsSemisimpleRing H) :
    Coalgebra.counit (R := k) I ≠ 0 := by sorry

/-- Converse direction of Proposition 1.52.5: if a nonzero left integral `I` has nonzero
counit, then the underlying finite dimensional ring `H` is semisimple. -/
theorem counit_ne_zero_implies_semisimple
    {k : Type u} [Field k] {H : Type v} [Ring H] [Algebra k H]
    [FiniteDimensional k H] [Coalgebra k H]
    {I : H} (hI : IsLeftIntegral k H I) (hI_ne : I ≠ 0)
    (hε : Coalgebra.counit (R := k) I ≠ 0) :
    IsSemisimpleRing H := by sorry

/-- Proposition 1.52.5: for a nonzero left integral `I` in a finite dimensional ring `H`,
semisimplicity is equivalent to `ε(I) ≠ 0`, which in turn is equivalent to `I * I ≠ 0`. -/
theorem Proposition_1_52_5 (k : Type u) [Field k] (H : Type v) [Ring H] [Algebra k H]
    [FiniteDimensional k H] [Coalgebra k H]
    (I : H) (hI : IsLeftIntegral k H I) (hI_ne : I ≠ 0) :
    (IsSemisimpleRing H ↔ Coalgebra.counit (R := k) I ≠ 0) ∧
    (Coalgebra.counit (R := k) I ≠ 0 ↔ I * I ≠ 0) := by
  constructor
  ·
    exact ⟨semisimple_implies_counit_ne_zero hI hI_ne,
           counit_ne_zero_implies_semisimple hI hI_ne⟩
  ·
    exact prop_1_52_5_iii_iff_ii hI hI_ne |>.symm
