/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfComputation.code.CFGtoPDA
import Atlas.TheoryOfComputation.code.CFLInterRegular

universe u

namespace CFGPDAEquiv

variable {α : Type u}

/-- **Sipser, Lecture 4 (Equivalence of CFGs and PDAs).** A language `A` is
context-free iff some PDA recognizes it. The forward direction is the
`CFG → PDA` construction; the reverse is the `PDA → CFG` construction. -/
theorem cfl_iff_pda_recognizes (A : Language α) :
    Language.IsContextFree A ↔
      ∃ (σ : Type u) (γ : Type u) (M : PDA α σ γ), M.language = A := by
  constructor
  ·
    exact cfl_recognized_by_pda A
  ·
    rintro ⟨σ, γ, M, rfl⟩
    exact pda_language_isContextFree M

end CFGPDAEquiv
