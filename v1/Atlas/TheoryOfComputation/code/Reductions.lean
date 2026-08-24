/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfComputation.code.TuringMachines
namespace TuringMachine

open TuringMachine

variable {Γ : Type}

/-- Read the first `n` cells of the tape of configuration `c` as a list. -/
def Config.readTape (c : Config Q Γ) (n : ℕ) : List Γ :=
  (List.range n).map (fun i => c.tape ((i : ℕ) : ℤ))

/-- A function `f : Σ* → Σ*` is (Turing-)computable if there is a TM `F` that,
on every input `w`, halts with the string `f w` written as the prefix of its
tape. -/
def IsComputableFunction (f : List Γ → List Γ) : Prop :=
  ∃ (Q : Type) (_ : DecidableEq Q) (F : TM Q Γ),
    ∀ w : List Γ, ∃ n : ℕ,
      F.isHaltConfig (F.runOnInput w n) ∧
      Config.readTape (F.runOnInput w n) (f w).length = f w

/-- Mapping reducibility `A ≤ₘ B`: there is a computable function `f` with
`w ∈ A ↔ f w ∈ B` (Sipser, Lecture 9). -/
def MappingReducible (A B : Set (List Γ)) : Prop :=
  ∃ f : List Γ → List Γ,
    IsComputableFunction f ∧
    ∀ w : List Γ, w ∈ A ↔ f w ∈ B

/-- Notation `A ≤ₘ B` for mapping reducibility. -/
scoped infixl:50 " ≤ₘ " => MappingReducible

/-- Given a transducer for the computable function `f` and a recognizer `R` for
some language, there exists a single TM `S` whose acceptance behavior on input
`w` mirrors `R`'s behavior on `f w`. (Composition of TMs.) -/
theorem transducerRecognizerComposition
    {Γ : Type} (f : List Γ → List Γ)
    (hf : IsComputableFunction f)
    {QR : Type} [DecidableEq QR] (R : TM QR Γ) :
    ∃ (QS : Type) (_ : DecidableEq QS) (S : TM QS Γ),
      (∀ w, S.accepts w ↔ R.accepts (f w)) := by sorry

end TuringMachine

open TuringMachine in
/-- **Sipser, Lecture 9.** If `A ≤ₘ B` and `B` is Turing-recognizable, then `A`
is Turing-recognizable. -/
theorem TuringMachine.isTuringRecognizable_of_mappingReducible
    {Γ : Type} {A B : Set (List Γ)}
    (hAB : A ≤ₘ B) (hB : IsTuringRecognizable B) : IsTuringRecognizable A := by
  obtain ⟨f, hf_comp, hf_red⟩ := hAB
  obtain ⟨Q_B, decEq_B, M_B, hLang_B⟩ := hB
  obtain ⟨Q_S, decEq_S, S, hAcc_S⟩ :=
    TuringMachine.transducerRecognizerComposition f hf_comp M_B
  exact ⟨Q_S, decEq_S, S, by
    ext w
    simp only [TM.language, Set.mem_setOf_eq]
    rw [hAcc_S w]
    constructor
    · intro hacc
      have : f w ∈ @TM.language Q_B Γ decEq_B M_B := hacc
      rw [hLang_B] at this
      exact (hf_red w).mpr this
    · intro hw
      have : f w ∈ B := (hf_red w).mp hw
      rw [← hLang_B] at this
      exact this⟩

namespace TuringMachine

/-- **Sipser, Corollary in Lecture 9.** If `A ≤ₘ B` and `A` is T-unrecognizable,
then so is `B`. Contrapositive form of `isTuringRecognizable_of_mappingReducible`. -/
theorem not_isTuringRecognizable_of_mappingReducible
    {Γ : Type} {A B : Set (List Γ)}
    (hAB : A ≤ₘ B) (hA : ¬IsTuringRecognizable A) : ¬IsTuringRecognizable B := by
  intro hB
  exact hA (isTuringRecognizable_of_mappingReducible hAB hB)

end TuringMachine
