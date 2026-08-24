/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.CartierKostant.Axioms

open scoped TensorProduct

universe u

namespace Lemma1332

/-- Lemma 1.33.2 (EGNO). A symmetric 2-cocycle on the symmetric algebra `S(V)` over a
characteristic-zero field is a 2-coboundary. Wraps `SymmetricAlgebra.symmetric_cocycle_is_coboundary`. -/
theorem symmetric_cocycle_is_coboundary
    (k : Type u) (V : Type u) [Field k] [CharZero k]
    [AddCommGroup V] [Module k V]
    (u : SymmetricAlgebra k V ⊗[k] SymmetricAlgebra k V)
    (hsymm : SymmetricAlgebra.IsSymmetricTensor k V u)
    (hcocycle : SymmetricAlgebra.IsCocycle2 k V u) :
    SymmetricAlgebra.IsCoboundary2 k V u :=
  SymmetricAlgebra.symmetric_cocycle_is_coboundary k V u hsymm hcocycle

end Lemma1332
