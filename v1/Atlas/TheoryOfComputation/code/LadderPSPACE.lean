/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfComputation.code.LadderNSPACE

open Computability TuringMachine SpaceComplexity

namespace SpaceComplexity

/-- **Theorem (Sipser, Lecture 17).** `LADDER_DFA ∈ SPACE(n²)`.

Applying Savitch's Theorem (`NSPACE(f(n)) ⊆ SPACE(f(n)²)`) to the linear-space NTM bound
`LADDER_DFA ∈ NSPACE(n)` gives a deterministic decision procedure using `O(n²)` space.
Intuitively: a recursive procedure for the bounded ladder problem uses `O(n)` space per level
and `O(log t) = O(n)` recursion depth, for a total of `O(n²)` space. -/
theorem LADDER_DFA_in_SPACE_n2 {α : Type} {σ : Type}
    [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]
    (B : DFA α σ) :
    InSPACE (fun n => n ^ 2) (LADDER_DFA_Lang B) :=
  savitch id (fun n => Nat.le_refl n) (LADDER_DFA_Lang B) (LADDER_DFA_in_NSPACE_n B)

/-- **Theorem (Sipser, Lecture 17).** `LADDER_DFA ∈ PSPACE`. This follows immediately from
`LADDER_DFA ∈ SPACE(n²)` since `PSPACE = ⋃_k SPACE(n^k)`. -/
theorem LADDER_DFA_in_PSPACE {α : Type} {σ : Type}
    [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]
    (B : DFA α σ) :
    InPSPACE (LADDER_DFA_Lang B) :=
  ⟨2, LADDER_DFA_in_SPACE_n2 B⟩

end SpaceComplexity
