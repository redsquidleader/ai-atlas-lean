/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Countable
import Mathlib.Computability.Language
import Mathlib.Computability.ContextFreeGrammar
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

import Atlas.TheoryOfComputation.code.TuringMachines
import Atlas.TheoryOfComputation.code.Reductions

namespace Decidability

/-- A set `s : Set α` is countable if it is finite or has the same size as `ℕ`. -/
def IsCountable {α : Type*} (s : Set α) : Prop := s.Countable

/-- For any countably infinite type `α`, the power set `Set α` is uncountable.
This is a form of Cantor's theorem and underlies the proof that some language is undecidable. -/
theorem set_not_countable_of_countable_infinite {α : Type*} [Countable α] [Infinite α] :
    ¬ Countable (Set α) := by
  intro h
  obtain ⟨f, hf⟩ := exists_injective_nat (Set α)
  haveI : Denumerable α := Denumerable.mk' (nonempty_equiv_of_countable.some)
  let e := (Denumerable.eqv α).symm
  exact Function.cantor_injective (e ∘ f) (e.injective.comp hf)

/-- **Corollary (Sipser Lecture 8).** The set ℒ of all languages over a nonempty countable
alphabet is uncountable. Combined with the countability of Turing machines, this shows that
some language is not Turing-decidable. -/
theorem languages_uncountable (Alphabet : Type*) [Nonempty Alphabet] [Countable Alphabet] :
    ¬ Countable (Language Alphabet) :=
  set_not_countable_of_countable_infinite

end Decidability

open TuringMachine

/-- A `TMDesc` packages a Turing machine together with its (decidable) state type and an input
string. This corresponds to the encoded pair `⟨M, w⟩` used throughout Sipser's undecidability
arguments — for example, the input to a putative decider for `A_TM`. -/
structure TuringMachine.TMDesc (Γ : Type) where
  Q : Type
  decEq : DecidableEq Q
  tm : TuringMachine.TM Q Γ
  input : List Γ

namespace TuringMachine

variable {Γ : Type}

/-- `d.accepts` holds when the underlying TM `d.tm` accepts the input `d.input`. -/
def TMDesc.accepts (d : TMDesc Γ) : Prop :=
  @TM.accepts d.Q Γ d.decEq d.tm d.input

/-- `d.halts` holds when the underlying TM `d.tm` halts (accepts or rejects) on the input
`d.input`. -/
def TMDesc.halts (d : TMDesc Γ) : Prop :=
  @TM.halts d.Q Γ d.decEq d.tm d.input

/-- Additivity of `run`: running `M` for `m + n` steps equals running it for `m` steps and
then for an additional `n` steps. -/
theorem TM.run_add {Q Γ : Type} [DecidableEq Q]
    (M : TM Q Γ) (c : Config Q Γ) (m n : ℕ) :
    M.run c (m + n) = M.run (M.run c m) n := by
  induction n with
  | zero => simp [TM.run]
  | succ n ih =>
    show M.step (M.run c (m + n)) = M.step (M.run (M.run c m) n)
    rw [ih]

end TuringMachine

/-- A `TMEncoding` over alphabet `Γ` is a bundle of all the encoding/universal-machine
machinery used informally in Sipser. It provides:
* an injective encoding `encode : TMDesc Γ → List Γ` with a decoder,
* a self-reference principle (used for the Recursion Theorem / diagonal argument),
* a universal TM `U` that simulates encoded TMs whenever they halt,
* sequential composition of a decider with another TM, and
* transducer composition with computable functions, as used in mapping reductions. -/
structure TuringMachine.TMEncoding (Γ : Type) where
  encode : TuringMachine.TMDesc Γ → List Γ
  decode : List Γ → Option (TuringMachine.TMDesc Γ)
  encode_injective : Function.Injective encode
  decode_encode : ∀ d, decode (encode d) = some d
  selfRef : ∀ {Q₀ : Type} [DecidableEq Q₀] (M : TuringMachine.TM Q₀ Γ),
    ∃ d : TuringMachine.TMDesc Γ,
      d.accepts ↔ @TuringMachine.TM.accepts Q₀ Γ _ M (encode d)
  universalSim : ∃ (QU : Type) (_ : DecidableEq QU) (U : TuringMachine.TM QU Γ),
    (∀ d : TuringMachine.TMDesc Γ, d.halts →
      @TuringMachine.TM.halts QU Γ _ U (encode d)) ∧
    (∀ d : TuringMachine.TMDesc Γ, d.halts →
      (@TuringMachine.TM.accepts QU Γ _ U (encode d) ↔ d.accepts)) ∧
    (∀ s, @TuringMachine.TM.accepts QU Γ _ U s →
      ∃ d : TuringMachine.TMDesc Γ, encode d = s ∧ d.accepts)
  sequentialComposition : ∀ {QR QU : Type}
    [DecidableEq QR] [DecidableEq QU]
    (R : TuringMachine.TM QR Γ) (U : TuringMachine.TM QU Γ),
    R.isDecider →
    (∀ w, @TuringMachine.TM.accepts QR Γ _ R w →
      @TuringMachine.TM.halts QU Γ _ U w) →
    ∃ (QS : Type) (_ : DecidableEq QS) (S : TuringMachine.TM QS Γ),
      S.isDecider ∧
      (∀ w, @TuringMachine.TM.accepts QS Γ _ S w ↔
        (@TuringMachine.TM.accepts QR Γ _ R w ∧
         @TuringMachine.TM.accepts QU Γ _ U w))
  transducerComposition : ∀ (f : List Γ → List Γ),
    TuringMachine.IsComputableFunction f →
    ∀ {QR : Type} [DecidableEq QR] (R : TuringMachine.TM QR Γ),
    R.isDecider →
    ∃ (QS : Type) (_ : DecidableEq QS) (S : TuringMachine.TM QS Γ),
      S.isDecider ∧
      (∀ w, @TuringMachine.TM.accepts QS Γ _ S w ↔
        @TuringMachine.TM.accepts QR Γ _ R (f w))

namespace TuringMachine

/-- Dovetailing simulation. Given TMs `M₁`, `M₂` such that for every input `w` at least one of
them accepts, one can construct a decider `T` that simulates both in parallel and accepts iff
`M₁` accepts. This is the technical content behind Sipser's Lecture 8 theorem "If `A` and `Aᶜ`
are T-recognizable then `A` is decidable." -/
theorem parallel_simulation {Γ : Type}
    {Q₁ Q₂ : Type} [DecidableEq Q₁] [DecidableEq Q₂]
    (M₁ : TM Q₁ Γ) (M₂ : TM Q₂ Γ)
    (hcov : ∀ w : List Γ, M₁.accepts w ∨ M₂.accepts w) :
    ∃ (Q : Type) (_ : DecidableEq Q) (T : TM Q Γ),
      T.isDecider ∧ (∀ w, T.accepts w ↔ M₁.accepts w) := by
  classical


  let ST := ((ℤ → Γ) × ℕ) ⊕ Bool
  haveI : DecidableEq ST := Classical.decEq _
  let T : TM ST Γ :=
    { blank := M₁.blank
      inputAlpha := M₁.inputAlpha
      blank_not_in_inputAlpha := M₁.blank_not_in_inputAlpha
      δ := fun q γ => match q with
        | .inl (f, n) =>
          let f' := Function.update f (n : ℤ) γ
          let wn : List Γ := (List.range (n + 1)).map (fun i => f' (i : ℤ))
          if M₁.isAcceptConfig (M₁.runOnInput wn n) then
            (.inr true, γ, Direction.R)
          else if M₂.isAcceptConfig (M₂.runOnInput wn n) then
            (.inr false, γ, Direction.R)
          else (.inl (f', n + 1), γ, Direction.R)
        | .inr b => (.inr b, γ, Direction.R)
      q₀ := .inl (fun _ => M₁.blank, 0)
      qAccept := .inr true
      qReject := .inr false
      qReject_ne_qAccept := fun h => by cases h }
  refine ⟨ST, ‹_›, T, ?_, ?_⟩
  ·
    intro w
    sorry
  ·
    intro w
    sorry

/-- **Theorem (Sipser Lecture 8).** If both `A` and its complement `Aᶜ` are Turing-recognizable
then `A` is Turing-decidable. The proof runs the two recognizers in parallel and accepts/rejects
according to whichever halts first. -/
theorem recognizable_complement_decidable {Γ : Type}
    {A : Set (List Γ)}
    (hA : IsTuringRecognizable A)
    (hAc : IsTuringRecognizable Aᶜ) :
    IsTuringDecidable A := by
  obtain ⟨Q₁, hQ₁, M₁, hM₁⟩ := hA
  obtain ⟨Q₂, hQ₂, M₂, hM₂⟩ := hAc
  have hcov : ∀ w : List Γ, M₁.accepts w ∨ M₂.accepts w := by
    intro w
    rcases Classical.em (w ∈ A) with h | h
    · left; have : w ∈ M₁.language := hM₁ ▸ h; exact this
    · right; have : w ∈ M₂.language := hM₂ ▸ h; exact this
  obtain ⟨Q, hQ, T, hDecider, hAccepts⟩ := parallel_simulation M₁ M₂ hcov
  exact ⟨Q, hQ, T, hDecider, by ext w; simp [TM.language, hAccepts, ← hM₁]⟩

end TuringMachine

namespace TuringMachine

variable {Γ : Type}

/-- The acceptance problem for Turing machines: `A_TM = {⟨M, w⟩ | M accepts w}`.
The classical Sipser theorem says this language is undecidable but Turing-recognizable. -/
def A_TM (enc : TMEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : TMDesc Γ, enc.encode d = s ∧ d.accepts}

/-- The halting problem: `HALT_TM = {⟨M, w⟩ | M halts on w}`, also undecidable. -/
def HALT_TM (enc : TMEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : TMDesc Γ, enc.encode d = s ∧ d.halts}

/-- If a TM accepts an input then it halts on that input (accepting is a form of halting). -/
theorem TM.halts_of_accepts {Q : Type} [DecidableEq Q] (M : TM Q Γ) (w : List Γ)
    (h : M.accepts w) : M.halts w := by
  obtain ⟨n, hacc⟩ := h
  exact ⟨n, Or.inl hacc⟩

/-- Acceptance implies halting at the level of languages: `A_TM ⊆ HALT_TM`. -/
theorem A_TM_subset_HALT_TM (enc : TMEncoding Γ) :
    A_TM enc ⊆ HALT_TM enc := by
  intro s ⟨d, henc, hacc⟩
  refine ⟨d, henc, ?_⟩
  obtain ⟨n, hacc'⟩ := hacc
  exact ⟨n, Or.inl hacc'⟩

end TuringMachine

/-- The "flipped" TM `H.flip` swaps the accept and reject states of `H`. If `H` is a decider
then `H.flip` decides the complement of `L(H)`. This is the standard construction used in the
diagonal proof that `A_TM` is undecidable. -/
def TuringMachine.TM.flip {Q : Type} (Γ : Type) [DecidableEq Q] (H : TuringMachine.TM Q Γ) :
    TuringMachine.TM Q Γ where
  blank := H.blank
  inputAlpha := H.inputAlpha
  blank_not_in_inputAlpha := H.blank_not_in_inputAlpha
  δ := H.δ
  q₀ := H.q₀
  qAccept := H.qReject
  qReject := H.qAccept
  qReject_ne_qAccept := H.qReject_ne_qAccept.symm

/-- Swapping accept/reject states does not change the one-step transition function of the TM
on non-halting configurations, and on halting configurations both sides idle, so the `step`
functions agree pointwise. -/
theorem TuringMachine.TM.flip_step {Q : Type} {Γ : Type} [DecidableEq Q]
    (H : TuringMachine.TM Q Γ) (c : TuringMachine.Config Q Γ) :
    (H.flip Γ).step c = H.step c := by
  simp only [TuringMachine.TM.step, TuringMachine.TM.flip]
  split_ifs with h1 h2 h2
  · rfl
  ·
    exfalso; exact h2 (h1.elim Or.inr Or.inl)
  ·
    exfalso; exact h1 (h2.elim Or.inr Or.inl)
  · rfl

/-- The `n`-step run is the same for `H` and `H.flip`, since their step functions agree
pointwise. -/
theorem TuringMachine.TM.flip_run {Q : Type} {Γ : Type} [DecidableEq Q]
    (H : TuringMachine.TM Q Γ) (c : TuringMachine.Config Q Γ) (n : ℕ) :
    (H.flip Γ).run c n = H.run c n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [TuringMachine.TM.run, ih, H.flip_step]

/-- If `H` is a decider then its flip `H.flip` accepts `w` iff `H` does not accept `w`. This is
the crucial property that allows the flip to decide the complement language. -/
theorem TuringMachine.TM.flip_accepts_iff {Q : Type} {Γ : Type} [DecidableEq Q]
    (H : TuringMachine.TM Q Γ) (hH : H.isDecider) (w : List Γ) :
    (H.flip Γ).accepts w ↔ ¬ H.accepts w := by

  have hrun_add : ∀ (c : TuringMachine.Config Q Γ) (a b : ℕ),
      H.run (H.run c a) b = H.run c (a + b) := by
    intro c a b; induction b with
    | zero => rfl
    | succ b ih =>
      change H.step (H.run (H.run c a) b) = _; rw [ih]; rfl

  have hrun_eq : ∀ n, (H.flip Γ).runOnInput w n = H.runOnInput w n := by
    intro n
    show (H.flip Γ).run ((H.flip Γ).initConfig w) n = H.run (H.initConfig w) n
    have hinit : (H.flip Γ).initConfig w = H.initConfig w := by
      simp [TuringMachine.TM.initConfig, TuringMachine.TM.flip]
    rw [hinit, H.flip_run]


  have h_eq : (H.flip Γ).accepts w ↔ H.rejects w := by
    constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩
    · change (H.runOnInput w n).state = H.qReject
      change ((H.flip Γ).runOnInput w n).state = (H.flip Γ).qAccept at hn
      rwa [show (H.flip Γ).runOnInput w n = H.runOnInput w n from hrun_eq n,
           show (H.flip Γ).qAccept = H.qReject from rfl] at hn
    · change ((H.flip Γ).runOnInput w n).state = (H.flip Γ).qAccept
      rw [show (H.flip Γ).runOnInput w n = H.runOnInput w n from hrun_eq n,
          show (H.flip Γ).qAccept = H.qReject from rfl]
      exact hn
  rw [h_eq]
  constructor
  · rintro ⟨n, href⟩ ⟨m, hacc⟩

    have reject_persists : ∀ k,
        (H.run (H.run (H.initConfig w) n) k).state = H.qReject := by
      intro k
      induction k with
      | zero => exact href
      | succ k ihk =>
        show (H.step (H.run (H.run (H.initConfig w) n) k)).state = H.qReject
        rw [H.step_of_halt _ (Or.inr ihk)]; exact ihk
    have hstable2 := H.accepts_stable (H.runOnInput w m) n hacc
    simp only [TuringMachine.TM.runOnInput] at hstable2
    rw [hrun_add, show m + n = n + m from Nat.add_comm m n] at hstable2
    have hrej := reject_persists m
    rw [hrun_add] at hrej
    exact H.qReject_ne_qAccept (hrej.symm.trans hstable2)
  · intro hna
    obtain ⟨n, hn⟩ := hH w
    rcases hn with hacc | href
    · exact absurd ⟨n, hacc⟩ hna
    · exact ⟨n, href⟩

/-- **Theorem (Sipser, undecidability of A_TM).** The acceptance problem
`A_TM = {⟨M, w⟩ | M accepts w}` is not Turing-decidable. The proof is the classical Turing
diagonal argument: assuming a decider `H` exists, the flipped machine `D = H.flip` (which
decides whether `H` rejects) leads to a contradiction via the self-reference principle
provided by `TMEncoding`. -/
theorem TuringMachine.A_TM_not_decidable
    {Γ : Type} (enc : TuringMachine.TMEncoding Γ) :
    ¬TuringMachine.IsTuringDecidable (TuringMachine.A_TM enc) := by
  intro ⟨QH, decEqH, H, hDecider, hLang⟩

  have hH_iff : ∀ d : TuringMachine.TMDesc Γ,
      @TuringMachine.TM.accepts QH Γ decEqH H (enc.encode d) ↔ d.accepts := by
    intro d
    have hLang' : ∀ w, @TuringMachine.TM.accepts QH Γ decEqH H w ↔
        w ∈ TuringMachine.A_TM enc := by
      intro w
      change w ∈ @TuringMachine.TM.language QH Γ decEqH H ↔ w ∈ TuringMachine.A_TM enc
      rw [hLang]
    rw [hLang' (enc.encode d)]
    constructor
    · rintro ⟨d', henc, hacc⟩
      have := enc.encode_injective henc
      subst this
      exact hacc
    · intro hacc
      exact ⟨d, rfl, hacc⟩

  let D := @TuringMachine.TM.flip QH Γ decEqH H
  have hD : ∀ w, @TuringMachine.TM.accepts QH Γ decEqH D w ↔
      ¬ @TuringMachine.TM.accepts QH Γ decEqH H w :=
    TuringMachine.TM.flip_accepts_iff H hDecider

  obtain ⟨d₀, hSelfRef⟩ := enc.selfRef D

  have hcontra : d₀.accepts ↔ ¬ d₀.accepts := by
    calc d₀.accepts
        ↔ @TuringMachine.TM.accepts QH Γ decEqH D (enc.encode d₀) := hSelfRef
      _ ↔ ¬ @TuringMachine.TM.accepts QH Γ decEqH H (enc.encode d₀) := hD _
      _ ↔ ¬ d₀.accepts := not_congr (hH_iff d₀)

  by_cases h : d₀.accepts
  · exact hcontra.mp h h
  · exact h (hcontra.mpr h)

/-- A decider for `HALT_TM` yields a decider for `A_TM`. This is the standard reduction
`A_TM ≤ HALT_TM`: first use the `HALT_TM`-decider to check that `M` halts on `w`, then run the
universal TM `U` (which is guaranteed to halt on inputs whose underlying TM halts) to determine
whether `M` accepts. Together with the undecidability of `A_TM` this implies the undecidability
of `HALT_TM`. -/
theorem TuringMachine.A_TM_decidable_of_HALT_TM_decidable
    {Γ : Type} (enc : TuringMachine.TMEncoding Γ)
    (hHalt : TuringMachine.IsTuringDecidable (TuringMachine.HALT_TM enc)) :
    TuringMachine.IsTuringDecidable (TuringMachine.A_TM enc) := by

  obtain ⟨QR, decEqR, R, hR_dec, hR_lang⟩ := hHalt

  obtain ⟨QU, decEqU, U, hU_halts, hU_accepts, _⟩ := enc.universalSim

  have hR_iff : ∀ d : TuringMachine.TMDesc Γ,
      @TuringMachine.TM.accepts QR Γ decEqR R (enc.encode d) ↔ d.halts := by
    intro d
    have : ∀ w, @TuringMachine.TM.accepts QR Γ decEqR R w ↔
        w ∈ TuringMachine.HALT_TM enc := by
      intro w
      change w ∈ @TuringMachine.TM.language QR Γ decEqR R ↔ w ∈ TuringMachine.HALT_TM enc
      rw [hR_lang]
    rw [this]
    exact ⟨fun ⟨d', henc, hhalts⟩ => enc.encode_injective henc ▸ hhalts,
           fun hhalts => ⟨d, rfl, hhalts⟩⟩

  have hU_halts_when_R_accepts : ∀ w,
      @TuringMachine.TM.accepts QR Γ decEqR R w →
      @TuringMachine.TM.halts QU Γ decEqU U w := by
    intro w hRw

    have hw_in_halt : w ∈ TuringMachine.HALT_TM enc := by
      have : w ∈ @TuringMachine.TM.language QR Γ decEqR R := hRw
      rwa [hR_lang] at this
    obtain ⟨d, henc, hd_halts⟩ := hw_in_halt
    rw [← henc]
    exact hU_halts d hd_halts

  obtain ⟨QS, decEqS, S, hS_dec, hS_accepts⟩ :=
    enc.sequentialComposition R U hR_dec hU_halts_when_R_accepts

  exact ⟨QS, decEqS, S, hS_dec, by
    ext w
    simp only [TuringMachine.TM.language, Set.mem_setOf_eq]
    rw [hS_accepts w]
    constructor
    ·
      rintro ⟨hRw, hUw⟩

      have hw_halt : w ∈ TuringMachine.HALT_TM enc := by
        have : w ∈ @TuringMachine.TM.language QR Γ decEqR R := hRw
        rwa [hR_lang] at this
      obtain ⟨d, henc, hd_halts⟩ := hw_halt
      rw [TuringMachine.A_TM]
      exact ⟨d, henc, (hU_accepts d hd_halts).mp (henc ▸ hUw)⟩
    ·
      rintro ⟨d, henc, hd_acc⟩
      constructor
      ·
        rw [← henc]
        have hd_halts : d.halts := by
          have hd_in_ATM : enc.encode d ∈ TuringMachine.A_TM enc := ⟨d, rfl, hd_acc⟩
          have hd_in_HALT := TuringMachine.A_TM_subset_HALT_TM enc hd_in_ATM
          obtain ⟨d', henc', hd'_halts⟩ := hd_in_HALT
          exact enc.encode_injective henc' ▸ hd'_halts
        exact (hR_iff d).mpr hd_halts
      ·
        rw [← henc]
        have hd_halts : d.halts := by
          have hd_in_ATM : enc.encode d ∈ TuringMachine.A_TM enc := ⟨d, rfl, hd_acc⟩
          have hd_in_HALT := TuringMachine.A_TM_subset_HALT_TM enc hd_in_ATM
          obtain ⟨d', henc', hd'_halts⟩ := hd_in_HALT
          exact enc.encode_injective henc' ▸ hd'_halts
        exact (hU_accepts d hd_halts).mpr hd_acc⟩

namespace TuringMachine

/-- **Theorem (Sipser).** The halting problem `HALT_TM = {⟨M, w⟩ | M halts on w}` is
undecidable, by reduction from `A_TM`. -/
theorem HALT_TM_not_decidable
    {Γ : Type} (enc : TMEncoding Γ) : ¬IsTuringDecidable (HALT_TM enc) := by
  intro hHalt
  exact A_TM_not_decidable enc (A_TM_decidable_of_HALT_TM_decidable enc hHalt)

end TuringMachine

namespace Decidability

open TuringMachine

/-- The head movement directions `L` and `R` form a two-element `Fintype`. -/
instance : Fintype Direction where
  elems := {Direction.L, Direction.R}
  complete := fun x => by cases x <;> simp

/-- A language is "finitely Turing-decidable" if it is decided by some TM whose state set is
`Fin n` for some `n`. Up to renaming of states this is no weaker than `IsTuringDecidable`, but
restricting to `Fin n` makes the collection of such machines countable. -/
def IsTuringDecidableFinite {Γ : Type} (A : Set (List Γ)) : Prop :=
  ∃ (n : ℕ) (M : TM (Fin n) Γ), M.isDecider ∧ M.language = A

/-- The raw data of a finite-state Turing machine over `Γ`: a state count `n`, a blank symbol,
a transition function, and start/accept/reject states. This is the carrier used to enumerate
TMs in a countable family. -/
abbrev TMDescType (Γ : Type) :=
  Σ n : ℕ, Γ × (Fin n → Γ → Fin n × Γ × Direction) × Fin n × Fin n × Fin n

/-- For finite alphabets, the set of finite-state TM descriptions is countable. -/
instance tmDescType_countable (Γ : Type) [Fintype Γ] [DecidableEq Γ] :
    Countable (TMDescType Γ) :=
  inferInstance

/-- Map a piece of raw TM data to its language. If `qAccept = qReject` (ill-formed data) the
language is empty; otherwise it is the language of the corresponding `TM`. -/
noncomputable def tmDescToLang (Γ : Type) [DecidableEq Γ] :
    TMDescType Γ → Set (List Γ) :=
  fun ⟨n, blank, δ, q₀, qAccept, qReject⟩ =>
    if h : qReject ≠ qAccept then
      (TM.mk blank ∅ (Set.notMem_empty _) δ q₀ qAccept qReject h : TM (Fin n) Γ).language
    else ∅

/-- Two TMs that agree on blank, transition function, start, accept, and reject states
accept the same language. The "extra" data in a TM record (e.g. `inputAlpha`) does not affect
the language. -/
theorem TM.language_eq_of_same_data {Q Γ : Type} [DecidableEq Q]
    (M₁ M₂ : TM Q Γ)
    (hblank : M₁.blank = M₂.blank) (hδ : M₁.δ = M₂.δ)
    (hq₀ : M₁.q₀ = M₂.q₀) (hqA : M₁.qAccept = M₂.qAccept)
    (hqR : M₁.qReject = M₂.qReject) :
    M₁.language = M₂.language := by
  have hstep : ∀ c, M₁.step c = M₂.step c := fun c => by
    simp only [TM.step, hδ, hqA, hqR]
  have hrun : ∀ c k, M₁.run c k = M₂.run c k := by
    intro c k; induction k with
    | zero => rfl
    | succ k ih => simp only [TM.run, ih, hstep]
  ext w
  simp only [TM.language, Set.mem_setOf_eq, TM.accepts, TM.isAcceptConfig,
    TM.runOnInput, hqA, hblank, hq₀, TM.initConfig, hrun]

/-- Every language of a TM with state set `Fin n` arises as `tmDescToLang` of some encoded
description. -/
theorem language_in_range_tmDescToLang {Γ : Type} [Fintype Γ] [DecidableEq Γ]
    {n : ℕ} (M : TM (Fin n) Γ) :
    M.language ∈ Set.range (tmDescToLang Γ) := by
  refine ⟨⟨n, M.blank, M.δ, M.q₀, M.qAccept, M.qReject⟩, ?_⟩
  simp only [tmDescToLang, dif_pos M.qReject_ne_qAccept]
  exact TM.language_eq_of_same_data _ _ rfl rfl rfl rfl rfl

/-- **Corollary (Sipser Lecture 8).** Some language is not Turing-decidable. The argument is
the cardinality argument: there are only countably many Turing machines but uncountably many
languages, so some language cannot be decided. -/
theorem exists_undecidable_language (Γ : Type) [Fintype Γ] [DecidableEq Γ] [Nonempty Γ] :
    ∃ L : Set (List Γ), ¬ IsTuringDecidableFinite L := by
  by_contra hall
  push Not at hall


  have hsurj : Function.Surjective (tmDescToLang Γ) := by
    intro L
    obtain ⟨n, M, _, hL⟩ := hall L
    obtain ⟨enc, henc⟩ := language_in_range_tmDescToLang M
    exact ⟨enc, by rw [henc, hL]⟩

  have hcount : Countable (Set (List Γ)) := hsurj.countable

  exact set_not_countable_of_countable_infinite hcount

/-- An explicit witness to "some language is undecidable": `A_TM` itself is undecidable. -/
theorem exists_undecidable_language' {Γ : Type} (enc : TMEncoding Γ) :
    ∃ A : Set (List Γ), ¬ IsTuringDecidable A :=
  ⟨A_TM enc, A_TM_not_decidable enc⟩

/-- Restatement: there exists a language over `Γ` that is not Turing-decidable. -/
theorem some_language_not_decidable (Γ : Type) [Fintype Γ] [DecidableEq Γ] [Nonempty Γ] :
    ∃ L : Set (List Γ), ¬ IsTuringDecidableFinite L :=
  exists_undecidable_language Γ

end Decidability

namespace PostCorrespondence

/-- A *domino* in the Post Correspondence Problem is a pair of strings (`top`, `bottom`) over
the alphabet `α`. -/
structure Domino (α : Type) where
  top : List α
  bottom : List α

/-- A *PCP instance* is a finite list of dominoes. -/
def PCPInstance (α : Type) := List (Domino α)

/-- A PCP instance `P` *has a match* if there is a nonempty sequence of indices `i₁, …, iₖ` such
that concatenating the tops in order produces the same string as concatenating the bottoms in
order. The PCP language is precisely the set of encoded instances with a match. -/
def hasMatch {α : Type} (P : PCPInstance α) : Prop :=
  ∃ (indices : List (Fin P.length)),
    indices ≠ [] ∧
    (indices.map (fun i => (P.get i).top)).flatten =
    (indices.map (fun i => (P.get i).bottom)).flatten

/-- An injective encoding/decoding scheme that turns PCP instances over `Γ` into strings
over `Γ`. -/
structure PCPEncoding (Γ : Type) where
  encode : PCPInstance Γ → List Γ
  decode : List Γ → Option (PCPInstance Γ)
  encode_injective : Function.Injective encode
  decode_encode : ∀ P, decode (encode P) = some P

variable {Γ : Type}

/-- The Post Correspondence Problem language `PCP = {⟨P⟩ | P has a match}`. By Sipser's
Lecture 10 theorem, this language is undecidable. -/
def PCP (enc : PCPEncoding Γ) : Set (List Γ) :=
  {s | ∃ P : PCPInstance Γ, enc.encode P = s ∧ hasMatch P}

end PostCorrespondence

namespace LBADecidability

open TuringMachine

/-- An `LBADesc` packages a linearly bounded automaton (a finite-state TM constrained to its
input region) with an input string. Following Sipser, `LBA = ⟨B, w⟩` is the typical input to
`A_LBA`. -/
structure LBADesc (Γ : Type) where
  Q : Type
  decEq : DecidableEq Q
  finQ : Fintype Q
  lba : @LBA Q Γ decEq
  input : List Γ

variable {Γ : Type}

/-- `d.accepts` holds when the LBA `d.lba` accepts the input string `d.input`. -/
def LBADesc.accepts (d : LBADesc Γ) : Prop :=
  @LBA.accepts d.Q Γ d.decEq d.lba d.input

/-- Injective encoding/decoding of `LBADesc`s into strings, used to formulate the language
`A_LBA`. -/
structure LBAEncoding (Γ : Type) where
  encode : LBADesc Γ → List Γ
  decode : List Γ → Option (LBADesc Γ)
  encode_injective : Function.Injective encode
  decode_encode : ∀ d, decode (encode d) = some d

/-- The acceptance language for LBAs: `A_LBA = {⟨B, w⟩ | LBA B accepts w}`. Sipser's Lecture 10
theorem shows this language is *decidable*. -/
def A_LBA (enc : LBAEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : LBADesc Γ, enc.encode d = s ∧ d.accepts}

/-- A *bounded configuration* records only the data of an LBA configuration that can vary in
the bounded simulation: state, head position in `Fin m`, and tape contents on the first `m`
cells. The total number of such configurations is finite. -/
def BoundedConfig (Q : Type) (Γ : Type) (m : ℕ) :=
  Q × Fin m × (Fin m → Γ)

/-- The set of bounded configurations of an LBA with state set `Q`, tape alphabet `Γ`, and
input bound `m` is finite when `Q` and `Γ` are. This finiteness is the basis of the decidability
of `A_LBA`: an LBA either accepts within `|Q| · m · |Γ|^m` steps or loops. -/
noncomputable instance instFintypeBoundedConfig (Q : Type) (Γ : Type) (m : ℕ)
    [Fintype Q] [DecidableEq Γ] [Fintype Γ] : Fintype (BoundedConfig Q Γ m) := by
  change Fintype (Q × Fin m × (Fin m → Γ))
  infer_instance

/-- Extract the bounded-configuration view of a TM configuration whose head lies in `[0, m)`. -/
def extractBoundedConfig {Q Γ : Type} (m : ℕ) (c : Config Q Γ)
    (h0 : 0 ≤ c.headPos) (h1 : c.headPos < ↑m) : BoundedConfig Q Γ m :=
  (c.state,
   ⟨c.headPos.toNat, by omega⟩,
   fun i => c.tape ↑i)

/-- An LBA never modifies tape cells outside the input region `[0, max 1 |w|)`: for any
position `i` outside this region, the tape symbol after `n` steps equals the initial symbol. -/
theorem lba_tape_outside_unchanged {Q Γ : Type} [DecidableEq Q]
    (B : LBA Q Γ) (w : List Γ) (n : ℕ) (i : ℤ)
    (hi : i < 0 ∨ ↑(max 1 w.length) ≤ i) :
    (B.toTM.runOnInput w n).tape i = (B.toTM.initConfig w).tape i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [TM.runOnInput, TM.run] at *
    rw [TM.step]
    split_ifs with hhalt
    · exact ih
    · simp only
      have hbnd := B.head_bounded w n
      simp only [TM.runOnInput] at hbnd
      have hne : i ≠ (B.toTM.run (B.toTM.initConfig w) n).headPos := by
        rcases hi with hi | hi <;> omega
      simp only [Function.update, dif_neg hne]
      exact ih

/-- If two configurations of an LBA running on input `w` agree on their bounded views (state,
head position, and tape contents in `[0, max 1 |w|)`) then they are equal as full
configurations, since the tape outside that window is fixed. This is the key lemma underlying
the pigeonhole argument that bounds LBA running time. -/
theorem lba_configs_eq_of_bounded_eq {Q Γ : Type} [DecidableEq Q]
    (B : LBA Q Γ) (w : List Γ) (n₁ n₂ : ℕ)
    (h : extractBoundedConfig (max 1 w.length)
           (B.toTM.runOnInput w n₁)
           (B.head_bounded w n₁).1
           (B.head_bounded w n₁).2 =
         extractBoundedConfig (max 1 w.length)
           (B.toTM.runOnInput w n₂)
           (B.head_bounded w n₂).1
           (B.head_bounded w n₂).2) :
    B.toTM.runOnInput w n₁ = B.toTM.runOnInput w n₂ := by
  simp only [extractBoundedConfig, BoundedConfig, Prod.mk.injEq] at h
  obtain ⟨hstate, hhead_fin, htape⟩ := h
  have hhead : (B.toTM.runOnInput w n₁).headPos =
      (B.toTM.runOnInput w n₂).headPos := by
    simp only [Fin.mk.injEq] at hhead_fin
    have h1 := (B.head_bounded w n₁).1
    have h2 := (B.head_bounded w n₂).1
    omega
  have htape_eq : (B.toTM.runOnInput w n₁).tape =
      (B.toTM.runOnInput w n₂).tape := by
    funext i
    by_cases hrange : 0 ≤ i ∧ i < ↑(max 1 w.length)
    · have := congr_fun htape ⟨i.toNat, by omega⟩
      simp only at this
      convert this using 1 <;> simp [Int.toNat_of_nonneg hrange.1]
    · push Not at hrange

      have hi : i < 0 ∨ ↑(max 1 w.length) ≤ i := by
        by_cases h0 : 0 ≤ i
        · exact Or.inr (hrange h0)
        · exact Or.inl (by omega)
      rw [lba_tape_outside_unchanged B w n₁ i hi,
          lba_tape_outside_unchanged B w n₂ i hi]
  exact Config.mk.injEq _ _ _ _ _ _ |>.mpr ⟨hstate, hhead, htape_eq⟩

/-- Acceptance of an LBA description is decidable (classically). Constructively this follows
from the finiteness of LBA configurations, which bounds the search for an accepting run. -/
noncomputable instance lbaDesc_accepts_decidable
    (d : LBADesc Γ) : Decidable d.accepts := Classical.dec _


/-- There is a universal TM `U` that, when run on the encoding of an `LBADesc d`, simulates the
LBA `d.lba` on input `d.input` and decides whether it accepts. `U` always halts because LBAs
have only finitely many configurations on a fixed input, so non-acceptance can be detected by
pigeonhole. -/
theorem A_LBA_bounded_simulator {Γ : Type} [Fintype Γ]
    (enc : LBAEncoding Γ) :
    ∃ (QU : Type) (_ : DecidableEq QU) (U : TuringMachine.TM QU Γ),
      U.isDecider ∧
      (∀ d : LBADesc Γ, @TuringMachine.TM.accepts QU Γ _ U (enc.encode d) ↔ d.accepts) ∧
      (∀ s, @TuringMachine.TM.accepts QU Γ _ U s →
        ∃ d : LBADesc Γ, enc.encode d = s ∧ d.accepts) := by sorry

/-- **Theorem (Sipser Lecture 10).** `A_LBA = {⟨B, w⟩ | LBA B accepts w}` is Turing-decidable.
The decider simulates `B` on `w` for enough steps that, by pigeonhole on bounded
configurations, either acceptance has occurred or the LBA is in a loop. -/
theorem A_LBA_decidable [Fintype Γ] (enc : LBAEncoding Γ) :
    IsTuringDecidable (A_LBA enc) := by
  obtain ⟨QU, hQU, U, hDecider, hAccepts, hValid⟩ := A_LBA_bounded_simulator enc
  exact ⟨QU, hQU, U, hDecider, by
    ext w
    simp only [TM.language, Set.mem_setOf_eq, A_LBA]
    constructor
    · intro hacc
      exact hValid w hacc
    · rintro ⟨d, henc, hd⟩
      rw [← henc]
      exact (hAccepts d).mpr hd⟩

end LBADecidability

namespace ELBA

open TuringMachine

/-- An `LBAMachineDesc` is an LBA on its own (no input attached), used for the emptiness
problem `E_LBA`. -/
structure LBAMachineDesc (Γ : Type) where
  Q : Type
  decEq : DecidableEq Q
  finQ : Fintype Q
  lba : @LBA Q Γ decEq

variable {Γ : Type}

/-- The language accepted by an LBA description. -/
def LBAMachineDesc.language (d : LBAMachineDesc Γ) : Set (List Γ) :=
  @LBA.language d.Q Γ d.decEq d.lba

/-- Injective encoding/decoding of LBA machine descriptions, used to formulate `E_LBA`. -/
structure LBAMachineEncoding (Γ : Type) where
  encode : LBAMachineDesc Γ → List Γ
  decode : List Γ → Option (LBAMachineDesc Γ)
  encode_injective : Function.Injective encode
  decode_encode : ∀ d, decode (encode d) = some d

/-- The emptiness problem for LBAs: `E_LBA = {⟨B⟩ | L(B) = ∅}`. By Sipser's Lecture 10 theorem,
this language is undecidable. -/
def E_LBA (enc : LBAMachineEncoding Γ) : Set (List Γ) :=
  {s | ∃ d : LBAMachineDesc Γ, enc.encode d = s ∧ d.language = ∅}

end ELBA


/-- Computation-history construction for `E_LBA`. Given a TM description `d`, one can build an
LBA `bd` whose language is empty iff `d` does *not* accept. (The LBA recognizes valid
accepting computation histories of `d`; emptiness corresponds to no accepting history existing,
i.e. `d` does not accept.) -/
theorem compHistLBAConstruction {Γ : Type}
    (d : TuringMachine.TMDesc Γ) :
    ∃ bd : ELBA.LBAMachineDesc Γ, bd.language = ∅ ↔ ¬d.accepts := by sorry


/-- A default LBA description whose language is empty, used for malformed inputs of the
mapping reduction. -/
theorem compHistLBADefault {Γ : Type} :
    ∃ bd : ELBA.LBAMachineDesc Γ, bd.language = ∅ := by sorry


/-- The transducer that maps a TM description to its computation-history LBA description is
TM-computable. This is the computability side of the reduction `A_TM ≤ₘ E_LBAᶜ`. -/
theorem compHistTransductionComputable {Γ : Type}
    (f : List Γ → List Γ)
    (tmEnc : TuringMachine.TMEncoding Γ)
    (lbaEnc : ELBA.LBAMachineEncoding Γ)
    (hValid : ∀ d : TuringMachine.TMDesc Γ,
      ∃ bd : ELBA.LBAMachineDesc Γ,
        f (tmEnc.encode d) = lbaEnc.encode bd ∧
        (bd.language = ∅ ↔ ¬d.accepts))
    (hInvalid : ∀ w, (∀ d, tmEnc.encode d ≠ w) →
      ∃ bd : ELBA.LBAMachineDesc Γ,
        f w = lbaEnc.encode bd ∧ bd.language = ∅) :
    TuringMachine.IsComputableFunction f := by sorry


/-- **Computation-history transducer for `E_LBA`.** There exists a computable function `f`
mapping TM encodings to LBA encodings such that on a valid TM input `⟨d⟩`, `f` produces an
LBA whose language is empty iff `d` does not accept, and on invalid inputs `f` produces an
LBA with empty language. This is the engine of the reduction `A_TM ≤ₘ (E_LBA)ᶜ`. -/
theorem ELBA.compHistTransducer {Γ : Type}
    (tmEnc : TuringMachine.TMEncoding Γ)
    (lbaEnc : ELBA.LBAMachineEncoding Γ) :
    ∃ f : List Γ → List Γ,
      TuringMachine.IsComputableFunction f ∧
      (∀ d : TuringMachine.TMDesc Γ,
        ∃ bd : ELBA.LBAMachineDesc Γ,
          f (tmEnc.encode d) = lbaEnc.encode bd ∧
          (bd.language = ∅ ↔ ¬d.accepts)) ∧
      (∀ w, (∀ d, tmEnc.encode d ≠ w) →
        ∃ bd : ELBA.LBAMachineDesc Γ,
          f w = lbaEnc.encode bd ∧ bd.language = ∅) := by
  classical

  have hLBA : ∀ d : TuringMachine.TMDesc Γ,
      ∃ bd : ELBA.LBAMachineDesc Γ, bd.language = ∅ ↔ ¬d.accepts :=
    fun d => compHistLBAConstruction d

  have hDefault : ∃ bd : ELBA.LBAMachineDesc Γ, bd.language = ∅ :=
    compHistLBADefault

  let g : TuringMachine.TMDesc Γ → ELBA.LBAMachineDesc Γ :=
    fun d => (hLBA d).choose
  have hg : ∀ d, (g d).language = ∅ ↔ ¬d.accepts :=
    fun d => (hLBA d).choose_spec
  let bd₀ : ELBA.LBAMachineDesc Γ := hDefault.choose
  have hbd₀ : bd₀.language = ∅ := hDefault.choose_spec


  let f : List Γ → List Γ := fun w =>
    if h : ∃ d, tmEnc.encode d = w then
      lbaEnc.encode (g h.choose)
    else
      lbaEnc.encode bd₀
  have hValid : ∀ d : TuringMachine.TMDesc Γ,
      ∃ bd : ELBA.LBAMachineDesc Γ,
        f (tmEnc.encode d) = lbaEnc.encode bd ∧
        (bd.language = ∅ ↔ ¬d.accepts) := by
    intro d
    refine ⟨g d, ?_, hg d⟩
    show f (tmEnc.encode d) = lbaEnc.encode (g d)
    simp only [f]
    have hex : ∃ d', tmEnc.encode d' = tmEnc.encode d := ⟨d, rfl⟩
    rw [dif_pos hex]
    have heq : hex.choose = d := tmEnc.encode_injective hex.choose_spec
    rw [heq]
  have hInvalid : ∀ w, (∀ d, tmEnc.encode d ≠ w) →
      ∃ bd : ELBA.LBAMachineDesc Γ,
        f w = lbaEnc.encode bd ∧ bd.language = ∅ := by
    intro w hinv
    refine ⟨bd₀, ?_, hbd₀⟩
    show f w = lbaEnc.encode bd₀
    simp only [f]
    have hnex : ¬∃ d, tmEnc.encode d = w := by
      intro ⟨d, hd⟩; exact hinv d hd
    rw [dif_neg hnex]
  refine ⟨f, ?_, hValid, hInvalid⟩

  exact compHistTransductionComputable f tmEnc lbaEnc hValid hInvalid

/-- **Mapping reduction `A_TM ≤ₘ (E_LBA)ᶜ`.** Using the computation-history construction, the
acceptance problem for TMs many-one reduces to the *non*-emptiness problem for LBAs. Since
`A_TM` is undecidable, so is `(E_LBA)ᶜ`, and hence so is `E_LBA`. -/
theorem ELBA.A_TM_mapping_reduces_to_compl_E_LBA
    {Γ : Type}
    (tmEnc : TuringMachine.TMEncoding Γ)
    (lbaEnc : ELBA.LBAMachineEncoding Γ) :
    TuringMachine.MappingReducible (TuringMachine.A_TM tmEnc) (ELBA.E_LBA lbaEnc)ᶜ := by
  obtain ⟨f, hcomp, hvalid, hinvalid⟩ := ELBA.compHistTransducer tmEnc lbaEnc
  refine ⟨f, hcomp, ?_⟩
  intro w
  simp only [TuringMachine.A_TM, Set.mem_setOf_eq, Set.mem_compl_iff, ELBA.E_LBA]
  constructor
  ·
    rintro ⟨d, henc, hacc⟩
    obtain ⟨bd, hfenc, hlang⟩ := hvalid d
    rw [← henc, hfenc]
    intro ⟨bd', hbd'enc, hbd'lang⟩
    have hbdeq := lbaEnc.encode_injective hbd'enc
    rw [hbdeq] at hbd'lang
    exact (hlang.mp hbd'lang) hacc
  ·
    intro hcompl
    by_cases hex : ∃ d : TuringMachine.TMDesc Γ, tmEnc.encode d = w
    · obtain ⟨d, henc⟩ := hex
      obtain ⟨bd, hfenc, hlang⟩ := hvalid d
      refine ⟨d, henc, ?_⟩
      by_contra hna
      apply hcompl
      rw [← henc, hfenc]
      exact ⟨bd, rfl, hlang.mpr hna⟩
    ·
      simp only [not_exists] at hex
      obtain ⟨bd, hfenc, hbdlang⟩ := hinvalid w hex

      exfalso; apply hcompl
      rw [hfenc]
      exact ⟨bd, rfl, hbdlang⟩

/-- If `E_LBA` were decidable, so would `A_TM` be: combine a decider for `E_LBA`, flip it to
decide the complement, and pre-compose with the computation-history transducer. -/
theorem ELBA.A_TM_decidable_of_E_LBA_decidable
    {Γ : Type}
    (tmEnc : TuringMachine.TMEncoding Γ)
    (lbaEnc : ELBA.LBAMachineEncoding Γ)
    (hELBA : TuringMachine.IsTuringDecidable (ELBA.E_LBA lbaEnc)) :
    TuringMachine.IsTuringDecidable (TuringMachine.A_TM tmEnc) := by

  obtain ⟨QR, decEqR, R, hR_dec, hR_lang⟩ := hELBA

  have hR'_dec : @TuringMachine.TM.isDecider QR Γ decEqR (R.flip Γ) := by
    intro w
    obtain ⟨n, hn⟩ := hR_dec w
    refine ⟨n, ?_⟩
    have hrun_eq : (R.flip Γ).runOnInput w n = R.runOnInput w n := by
      simp only [TuringMachine.TM.runOnInput]
      have hinit : (R.flip Γ).initConfig w = R.initConfig w := by
        simp only [TuringMachine.TM.initConfig, TuringMachine.TM.flip]
      rw [hinit, R.flip_run]
    rcases hn with h | h
    · exact Or.inr (by rwa [TuringMachine.TM.isRejectConfig, hrun_eq,
        show (R.flip Γ).qReject = R.qAccept from rfl])
    · exact Or.inl (by rwa [TuringMachine.TM.isAcceptConfig, hrun_eq,
        show (R.flip Γ).qAccept = R.qReject from rfl])
  have hR'_lang : @TuringMachine.TM.language QR Γ decEqR (R.flip Γ) =
      (ELBA.E_LBA lbaEnc)ᶜ := by
    ext w
    simp only [TuringMachine.TM.language, Set.mem_setOf_eq, Set.mem_compl_iff]
    rw [TuringMachine.TM.flip_accepts_iff R hR_dec w]
    constructor
    · intro hnacc hw
      exact hnacc (by rwa [← hR_lang] at hw)
    · intro hw
      rw [show @TuringMachine.TM.accepts QR Γ decEqR R w ↔
          w ∈ ELBA.E_LBA lbaEnc from by
        change w ∈ @TuringMachine.TM.language QR Γ decEqR R ↔ _; rw [hR_lang]]
      exact hw

  obtain ⟨f, hf_comp, hf_correct⟩ :=
    ELBA.A_TM_mapping_reduces_to_compl_E_LBA tmEnc lbaEnc

  obtain ⟨QS, decEqS, S, hS_dec, hS_acc⟩ :=
    tmEnc.transducerComposition f hf_comp (R.flip Γ) hR'_dec

  exact ⟨QS, decEqS, S, hS_dec, by
    ext w
    simp only [TuringMachine.TM.language, Set.mem_setOf_eq]
    rw [hS_acc w]
    constructor
    · intro hacc
      have : f w ∈ @TuringMachine.TM.language QR Γ decEqR (R.flip Γ) := hacc
      rw [hR'_lang] at this
      exact (hf_correct w).mpr this
    · intro hw
      have : f w ∈ (ELBA.E_LBA lbaEnc)ᶜ := (hf_correct w).mp hw
      rw [← hR'_lang] at this
      exact this⟩

namespace ELBA

open TuringMachine

/-- **Theorem (Sipser Lecture 10).** The LBA emptiness problem
`E_LBA = {⟨B⟩ | L(B) = ∅}` is undecidable. -/
theorem E_LBA_not_decidable
    {Γ : Type}
    (tmEnc : TMEncoding Γ)
    (lbaEnc : LBAMachineEncoding Γ) :
    ¬IsTuringDecidable (E_LBA lbaEnc) := by
  intro hELBA
  exact A_TM_not_decidable tmEnc
    (A_TM_decidable_of_E_LBA_decidable tmEnc lbaEnc hELBA)

end ELBA

open TuringMachine in
/-- **Theorem.** `A_TM` is Turing-recognizable: the universal TM `U` provided by the encoding
serves as a recognizer. On input `⟨M, w⟩`, `U` simulates `M` on `w` and accepts iff `M` does. -/
theorem A_TM_recognizable
    {Γ : Type} (enc : TMEncoding Γ) :
    IsTuringRecognizable (A_TM enc) := by
  obtain ⟨QU, hQU, U, _hU_halts, hU_accepts, hU_valid⟩ := enc.universalSim
  refine ⟨QU, hQU, U, ?_⟩
  ext s
  simp only [TM.language, Set.mem_setOf_eq, A_TM]
  constructor
  ·
    exact hU_valid s
  ·
    rintro ⟨d, rfl, hd_acc⟩
    have hd_halts : d.halts := @TM.halts_of_accepts Γ d.Q d.decEq d.tm d.input hd_acc
    exact (hU_accepts d hd_halts).mpr hd_acc

namespace TuringMachine

/-- **Corollary (Sipser Lecture 8).** The complement `(A_TM)ᶜ` is *not* Turing-recognizable.
For if both `A_TM` and its complement were recognizable, then by the previous theorem `A_TM`
would be decidable, contradicting the diagonal argument. -/
theorem A_TM_complement_not_recognizable
    {Γ : Type} (enc : TMEncoding Γ) :
    ¬IsTuringRecognizable (A_TM enc)ᶜ := by
  intro hAc
  have hA : IsTuringRecognizable (A_TM enc) := A_TM_recognizable enc
  exact A_TM_not_decidable enc (recognizable_complement_decidable hA hAc)

end TuringMachine

open TuringMachine in
/-- Restatement of the previous corollary in the root namespace: `(A_TM)ᶜ` is
T-unrecognizable. -/
theorem A_TM_complement_not_TuringRecognizable
    {Γ : Type} (enc : TMEncoding Γ) :
    ¬IsTuringRecognizable (A_TM enc)ᶜ :=
  TuringMachine.A_TM_complement_not_recognizable enc

namespace AllCFG

open TuringMachine

/-- An injective encoding/decoding scheme that turns context-free grammars over `Γ` into
strings over `Γ`. Used to formulate `ALL_CFG`. -/
structure CFGEncoding (Γ : Type) where
  encode : ContextFreeGrammar Γ → List Γ
  decode : List Γ → Option (ContextFreeGrammar Γ)
  encode_injective : Function.Injective encode
  decode_encode : ∀ g, decode (encode g) = some g


/-- **Computation-history reduction for `ALL_CFG`.** There is a computable function `f`
mapping TM encodings to CFG encodings such that, for any TM `d`, the CFG `f(⟨d⟩)` generates
*all* strings iff `d` does *not* accept (so the strings *not* generated correspond to
accepting computation histories of `d`), and on invalid inputs `f` outputs a universal CFG. -/
theorem computationHistoryCFGExists
    {Γ : Type}
    (tmEnc : TuringMachine.TMEncoding Γ)
    (cfgEnc : CFGEncoding Γ) :
    ∃ (f : List Γ → List Γ),
      TuringMachine.IsComputableFunction f ∧
      (∀ d : TuringMachine.TMDesc Γ, ∃ g : ContextFreeGrammar Γ,
        f (tmEnc.encode d) = cfgEnc.encode g ∧
        (g.language = Set.univ ↔ ¬d.accepts)) ∧
      (∀ w : List Γ, (∀ d : TuringMachine.TMDesc Γ, tmEnc.encode d ≠ w) →
        ∃ g : ContextFreeGrammar Γ, f w = cfgEnc.encode g ∧ g.language = Set.univ) := by sorry

variable {Γ : Type}

/-- The universality problem for CFGs: `ALL_CFG = {⟨G⟩ | G is a CFG and L(G) = Σ*}`. By
Sipser's Lecture 10 theorem, this language is undecidable. -/
def ALL_CFG (enc : CFGEncoding Γ) : Set (List Γ) :=
  {s | ∃ g : ContextFreeGrammar Γ, enc.encode g = s ∧ g.language = Set.univ}

end AllCFG


/-- Re-export of the computation-history CFG construction at the top level. -/
theorem AllCFG.computationHistoryCFGConstruction
    {Γ : Type}
    (tmEnc : TuringMachine.TMEncoding Γ)
    (cfgEnc : AllCFG.CFGEncoding Γ) :
    ∃ (f : List Γ → List Γ),
      TuringMachine.IsComputableFunction f ∧
      (∀ d : TuringMachine.TMDesc Γ, ∃ g : ContextFreeGrammar Γ,
        f (tmEnc.encode d) = cfgEnc.encode g ∧
        (g.language = Set.univ ↔ ¬d.accepts)) ∧
      (∀ w : List Γ, (∀ d : TuringMachine.TMDesc Γ, tmEnc.encode d ≠ w) →
        ∃ g : ContextFreeGrammar Γ, f w = cfgEnc.encode g ∧ g.language = Set.univ) :=
  AllCFG.computationHistoryCFGExists tmEnc cfgEnc

/-- **Mapping reduction `A_TM ≤ₘ (ALL_CFG)ᶜ`.** Via the computation-history CFG construction,
the acceptance problem reduces to the complement of CFG universality. -/
theorem AllCFG.A_TM_mapping_reduces_to_compl_ALL_CFG
    {Γ : Type}
    (tmEnc : TuringMachine.TMEncoding Γ)
    (cfgEnc : AllCFG.CFGEncoding Γ) :
    TuringMachine.MappingReducible (TuringMachine.A_TM tmEnc) (AllCFG.ALL_CFG cfgEnc)ᶜ := by
  obtain ⟨f, hf_comp, hf_desc, hf_none⟩ :=
    AllCFG.computationHistoryCFGConstruction tmEnc cfgEnc
  refine ⟨f, hf_comp, fun w => ?_⟩
  constructor
  ·
    intro ⟨d, henc, hacc⟩
    obtain ⟨g, hfg, hg_spec⟩ := hf_desc d
    rw [Set.mem_compl_iff]
    intro ⟨g', hg'_enc, hg'_lang⟩
    have hfw : f w = cfgEnc.encode g := by rw [← henc]; exact hfg
    have heq : g = g' := cfgEnc.encode_injective (hfw.symm.trans hg'_enc.symm)
    rw [heq] at hg_spec
    exact absurd hacc (hg_spec.mp hg'_lang)
  ·
    intro hfw_compl
    rw [Set.mem_compl_iff] at hfw_compl
    by_cases h : ∃ d : TuringMachine.TMDesc Γ, tmEnc.encode d = w
    · obtain ⟨d, henc⟩ := h
      obtain ⟨g, hfg, hg_spec⟩ := hf_desc d
      have hfw : f w = cfgEnc.encode g := by rw [← henc]; exact hfg
      have hg_not_univ : g.language ≠ Set.univ := by
        intro huniv
        exact hfw_compl ⟨g, hfw.symm, huniv⟩
      have hacc : d.accepts := by
        by_contra hna
        exact hg_not_univ (hg_spec.mpr hna)
      exact ⟨d, henc, hacc⟩
    · push Not at h
      obtain ⟨g, hfg, hg_lang⟩ := hf_none w h
      exact absurd ⟨g, hfg.symm, hg_lang⟩ hfw_compl

/-- If `ALL_CFG` were decidable, so would `A_TM` be: flip the `ALL_CFG`-decider and compose
with the reduction `f`. -/
theorem AllCFG.A_TM_decidable_of_ALL_CFG_decidable
    {Γ : Type}
    (tmEnc : TuringMachine.TMEncoding Γ)
    (cfgEnc : AllCFG.CFGEncoding Γ)
    (hALL : TuringMachine.IsTuringDecidable (AllCFG.ALL_CFG cfgEnc)) :
    TuringMachine.IsTuringDecidable (TuringMachine.A_TM tmEnc) := by

  obtain ⟨QR, decEqR, R, hR_dec, hR_lang⟩ := hALL

  have hR'_dec : @TuringMachine.TM.isDecider QR Γ decEqR (R.flip Γ) := by
    intro w
    obtain ⟨n, hn⟩ := hR_dec w
    refine ⟨n, ?_⟩
    have hrun_eq : (R.flip Γ).runOnInput w n = R.runOnInput w n := by
      simp only [TuringMachine.TM.runOnInput]
      have hinit : (R.flip Γ).initConfig w = R.initConfig w := by
        simp only [TuringMachine.TM.initConfig, TuringMachine.TM.flip]
      rw [hinit, R.flip_run]
    rcases hn with h | h
    · exact Or.inr (by rwa [TuringMachine.TM.isRejectConfig, hrun_eq,
        show (R.flip Γ).qReject = R.qAccept from rfl])
    · exact Or.inl (by rwa [TuringMachine.TM.isAcceptConfig, hrun_eq,
        show (R.flip Γ).qAccept = R.qReject from rfl])
  have hR'_lang : @TuringMachine.TM.language QR Γ decEqR (R.flip Γ) =
      (AllCFG.ALL_CFG cfgEnc)ᶜ := by
    ext w
    simp only [TuringMachine.TM.language, Set.mem_setOf_eq, Set.mem_compl_iff]
    rw [TuringMachine.TM.flip_accepts_iff R hR_dec w]
    constructor
    · intro hnacc hw
      exact hnacc (by rwa [← hR_lang] at hw)
    · intro hw
      rw [show @TuringMachine.TM.accepts QR Γ decEqR R w ↔
          w ∈ AllCFG.ALL_CFG cfgEnc from by
        change w ∈ @TuringMachine.TM.language QR Γ decEqR R ↔ _; rw [hR_lang]]
      exact hw

  obtain ⟨f, hf_comp, hf_correct⟩ :=
    AllCFG.A_TM_mapping_reduces_to_compl_ALL_CFG tmEnc cfgEnc

  obtain ⟨QS, decEqS, S, hS_dec, hS_acc⟩ :=
    tmEnc.transducerComposition f hf_comp (R.flip Γ) hR'_dec

  exact ⟨QS, decEqS, S, hS_dec, by
    ext w
    simp only [TuringMachine.TM.language, Set.mem_setOf_eq]
    rw [hS_acc w]
    constructor
    · intro hacc
      have : f w ∈ @TuringMachine.TM.language QR Γ decEqR (R.flip Γ) := hacc
      rw [hR'_lang] at this
      exact (hf_correct w).mpr this
    · intro hw
      have : f w ∈ (AllCFG.ALL_CFG cfgEnc)ᶜ := (hf_correct w).mp hw
      rw [← hR'_lang] at this
      exact this⟩

namespace AllCFG

open TuringMachine

/-- **Theorem (Sipser Lecture 10).** `ALL_CFG = {⟨G⟩ | L(G) = Σ*}` is undecidable. -/
theorem ALL_CFG_not_decidable
    {Γ : Type}
    (tmEnc : TMEncoding Γ)
    (cfgEnc : CFGEncoding Γ) :
    ¬IsTuringDecidable (ALL_CFG cfgEnc) := by
  intro hALL
  exact A_TM_not_decidable tmEnc
    (A_TM_decidable_of_ALL_CFG_decidable tmEnc cfgEnc hALL)

end AllCFG

open TuringMachine in
/-- Restatement of `ALL_CFG_not_decidable` at the root namespace level. -/
theorem ALL_CFG_undecidable
    {Γ : Type}
    (tmEnc : TuringMachine.TMEncoding Γ)
    (cfgEnc : AllCFG.CFGEncoding Γ) :
    ¬IsTuringDecidable (AllCFG.ALL_CFG cfgEnc) :=
  AllCFG.ALL_CFG_not_decidable tmEnc cfgEnc

/-- **Sipser Lecture 9 (mapping reductions preserve decidability).** If `A ≤ₘ B` and `B` is
decidable, then so is `A`: compose the reduction transducer with the decider for `B`. -/
theorem TuringMachine.isTuringDecidable_of_mappingReducible
    {Γ : Type} (enc : TuringMachine.TMEncoding Γ)
    {A B : Set (List Γ)}
    (hAB : TuringMachine.MappingReducible A B)
    (hB : TuringMachine.IsTuringDecidable B) :
    TuringMachine.IsTuringDecidable A := by
  obtain ⟨f, hf_comp, hf_red⟩ := hAB
  obtain ⟨Q_B, decEq_B, M_B, hDec_B, hLang_B⟩ := hB
  obtain ⟨Q_S, decEq_S, S, hDec_S, hAcc_S⟩ := enc.transducerComposition f hf_comp M_B hDec_B
  exact ⟨Q_S, decEq_S, S, hDec_S, by
    ext w
    simp only [TuringMachine.TM.language, Set.mem_setOf_eq]
    rw [hAcc_S w]
    constructor
    · intro hacc
      have : f w ∈ @TuringMachine.TM.language Q_B Γ decEq_B M_B := hacc
      rw [hLang_B] at this
      exact (hf_red w).mpr this
    · intro hw
      have : f w ∈ B := (hf_red w).mp hw
      rw [← hLang_B] at this
      exact this⟩


open Classical in
/-- **Sipser's PCP construction.** There is a map `pcpFor` from TM descriptions to PCP
instances such that the constructed instance has a match iff the TM accepts its input, and the
overall input-to-encoding map is TM-computable. This is the technical heart of the reduction
`A_TM ≤ₘ PCP`. -/
theorem PostCorrespondence.dominoConstructionIsComputable
    {Γ : Type}
    (tmEnc : TuringMachine.TMEncoding Γ)
    (pcpEnc : PostCorrespondence.PCPEncoding Γ) :
    ∃ (pcpFor : TuringMachine.TMDesc Γ → PostCorrespondence.PCPInstance Γ),
      (∀ d, PostCorrespondence.hasMatch (pcpFor d) ↔ d.accepts) ∧
      TuringMachine.IsComputableFunction (fun w =>
        if h : ∃ d : TuringMachine.TMDesc Γ, tmEnc.encode d = w then
          pcpEnc.encode (pcpFor h.choose)
        else
          pcpEnc.encode ([] : PostCorrespondence.PCPInstance Γ)) := by sorry

/-- **Computation-history PCP construction.** A computable function `f` maps any TM encoding
to a PCP-instance encoding so that the PCP instance has a match iff the TM accepts its input,
and on inputs that are not TM encodings the resulting PCP instance has no match. Combined with
the empty-list lemma, this yields the mapping reduction `A_TM ≤ₘ PCP`. -/
theorem PostCorrespondence.computationHistoryPCPConstruction
    {Γ : Type}
    (tmEnc : TuringMachine.TMEncoding Γ)
    (pcpEnc : PostCorrespondence.PCPEncoding Γ) :
    ∃ (f : List Γ → List Γ),
      TuringMachine.IsComputableFunction f ∧
      (∀ d : TuringMachine.TMDesc Γ, ∃ P : PostCorrespondence.PCPInstance Γ,
        f (tmEnc.encode d) = pcpEnc.encode P ∧
        (PostCorrespondence.hasMatch P ↔ d.accepts)) ∧
      (∀ w : List Γ, (∀ d : TuringMachine.TMDesc Γ, tmEnc.encode d ≠ w) →
        ∃ P : PostCorrespondence.PCPInstance Γ, f w = pcpEnc.encode P ∧ ¬PostCorrespondence.hasMatch P) := by
  classical

  obtain ⟨pcpFor, h_pcpFor_spec, hf_comp⟩ :=
    PostCorrespondence.dominoConstructionIsComputable tmEnc pcpEnc

  have h_emptyPCP : ¬PostCorrespondence.hasMatch ([] : PostCorrespondence.PCPInstance Γ) := by
    intro ⟨indices, hne, _⟩
    have : indices = [] := by
      cases indices with
      | nil => rfl
      | cons hd _ => exact absurd hd.isLt (by simp [PostCorrespondence.PCPInstance, List.length])
    exact hne this

  let f : List Γ → List Γ := fun w =>
    if h : ∃ d : TuringMachine.TMDesc Γ, tmEnc.encode d = w then
      pcpEnc.encode (pcpFor h.choose)
    else
      pcpEnc.encode ([] : PostCorrespondence.PCPInstance Γ)
  refine ⟨f, hf_comp, ?_, ?_⟩
  ·
    intro d
    have hd : ∃ d' : TuringMachine.TMDesc Γ, tmEnc.encode d' = tmEnc.encode d := ⟨d, rfl⟩
    refine ⟨pcpFor (hd.choose), ?_, ?_⟩
    · show f (tmEnc.encode d) = pcpEnc.encode (pcpFor hd.choose)
      simp only [f, dif_pos hd]
    · have heq : hd.choose = d := tmEnc.encode_injective hd.choose_spec
      rw [heq]
      exact h_pcpFor_spec d
  ·
    intro w hw
    have hne : ¬∃ d : TuringMachine.TMDesc Γ, tmEnc.encode d = w := by
      push_neg
      exact hw
    refine ⟨[], ?_, h_emptyPCP⟩
    show f w = pcpEnc.encode ([] : PostCorrespondence.PCPInstance Γ)
    simp only [f, dif_neg hne]

/-- **Mapping reduction `A_TM ≤ₘ PCP`.** Using the computation-history PCP construction, the
acceptance problem many-one reduces to PCP. -/
theorem PostCorrespondence.A_TM_reduces_to_PCP
    {Γ : Type}
    (tmEnc : TuringMachine.TMEncoding Γ)
    (pcpEnc : PostCorrespondence.PCPEncoding Γ) :
    TuringMachine.MappingReducible (TuringMachine.A_TM tmEnc) (PostCorrespondence.PCP pcpEnc) := by
  obtain ⟨f, hf_comp, hf_desc, hf_none⟩ :=
    PostCorrespondence.computationHistoryPCPConstruction tmEnc pcpEnc
  refine ⟨f, hf_comp, fun w => ?_⟩
  constructor
  ·
    intro ⟨d, henc, hacc⟩
    obtain ⟨P, hfP, hP_spec⟩ := hf_desc d
    have hfw : f w = pcpEnc.encode P := by rw [← henc]; exact hfP
    exact ⟨P, hfw.symm, hP_spec.mpr hacc⟩
  ·
    intro ⟨P', hP'_enc, hP'_match⟩
    by_cases h : ∃ d : TuringMachine.TMDesc Γ, tmEnc.encode d = w
    · obtain ⟨d, henc⟩ := h
      obtain ⟨P, hfP, hP_spec⟩ := hf_desc d
      have hfw : f w = pcpEnc.encode P := by rw [← henc]; exact hfP
      have heq : P = P' := pcpEnc.encode_injective (hfw.symm.trans hP'_enc.symm)
      rw [heq] at hP_spec
      exact ⟨d, henc, hP_spec.mp hP'_match⟩
    · push Not at h
      obtain ⟨P, hfP, hP_no_match⟩ := hf_none w h
      have heq : P = P' := pcpEnc.encode_injective (hfP.symm.trans hP'_enc.symm)
      rw [heq] at hP_no_match
      exact absurd hP'_match hP_no_match

/-- If PCP were decidable, so would `A_TM` be (immediate consequence of the mapping reduction
and decidability transferring along mapping reductions). -/
theorem PostCorrespondence.A_TM_decidable_of_PCP_decidable
    {Γ : Type}
    (tmEnc : TuringMachine.TMEncoding Γ)
    (pcpEnc : PostCorrespondence.PCPEncoding Γ)
    (hPCP : TuringMachine.IsTuringDecidable (PostCorrespondence.PCP pcpEnc)) :
    TuringMachine.IsTuringDecidable (TuringMachine.A_TM tmEnc) :=
  TuringMachine.isTuringDecidable_of_mappingReducible tmEnc
    (PostCorrespondence.A_TM_reduces_to_PCP tmEnc pcpEnc) hPCP

namespace PostCorrespondence

/-- **Theorem (Sipser Lecture 10).** The Post Correspondence Problem
`PCP = {⟨P⟩ | P has a match}` is undecidable, by reduction from `A_TM`. -/
theorem PCP_not_decidable
    {Γ : Type}
    (tmEnc : TuringMachine.TMEncoding Γ)
    (pcpEnc : PCPEncoding Γ) :
    ¬TuringMachine.IsTuringDecidable (PCP pcpEnc) := by
  intro hPCP
  exact TuringMachine.A_TM_not_decidable tmEnc
    (A_TM_decidable_of_PCP_decidable tmEnc pcpEnc hPCP)

end PostCorrespondence
