/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Computability.DFA
import Atlas.TheoryOfComputation.code.Complexity
import Atlas.TheoryOfComputation.code.SpaceComplexity

namespace HierarchyTheorems

open TuringMachine

/--
A function `f : ℕ → ℕ` is **time constructible** if there exists a Turing machine `M`
which is a decider, runs in some time `t'`, with `t' = O(f)`. This is the standard
hypothesis under which the Time Hierarchy Theorem is stated.
-/
def IsTimeConstructible (f : ℕ → ℕ) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (Γ : Type) (M : TM Q Γ) (t' : ℕ → ℕ),
    M.isDecider ∧ M.runsInTime t' ∧ IsBigO t' f

/--
`IsLittleO g f` says `g(n) = o(f(n))`: for every positive constant `c`, there is
some `n₀` such that `c · g(n) < f(n)` for all `n ≥ n₀`.
-/
def IsLittleO (g f : ℕ → ℕ) : Prop :=
  ∀ c : ℕ, 0 < c → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → c * g n < f n

/-- Little-`o` implies big-`O`: if `g = o(f)` then `g = O(f)`. -/
theorem IsLittleO.isBigO {g f : ℕ → ℕ} (h : IsLittleO g f) : IsBigO g f := by
  obtain ⟨n₀, hn₀⟩ := h 1 Nat.one_pos
  exact ⟨1, n₀, Nat.one_pos, fun n hn => by
    simp only [one_mul]
    exact Nat.le_of_lt (by simpa using hn₀ n hn)⟩

end HierarchyTheorems

namespace TuringMachine


/--
For any `f : ℕ → ℕ`, the function `n ↦ f(n) / log₂(f(n))` is `O(f)`. This is the
ratio that appears in the Time Hierarchy Theorem's lower bound
`TIME(o(f(n)/log(f(n)))) ⊊ TIME(f(n))`.
-/
theorem isBigO_div_log (f : ℕ → ℕ) : IsBigO (fun n => f n / Nat.log 2 (f n)) f :=
  ⟨1, 0, Nat.one_pos, fun n _ => by simp only [one_mul]; exact Nat.div_le_self _ _⟩

end TuringMachine

open TuringMachine HierarchyTheorems


/--
**Universal simulation with logarithmic overhead.** Given a time-constructible bound
`f`, there is a single universal simulator TM `sim` that runs in time `O(f)` and
correctly decides membership in `M.language` for every decider `M` whose running
time `s` satisfies `s = O(f(n)/log(f(n)))`. This is the key ingredient powering the
Time Hierarchy Theorem: the `log` factor accounts for the overhead of simulating an
arbitrary machine `M` on a fixed universal machine.
-/
theorem universal_simulation_overhead {Γ : Type} (f : ℕ → ℕ)
    (hf : IsTimeConstructible f) :
    ∃ (QS : Type) (_ : Fintype QS) (_ : DecidableEq QS)
      (enc : (Q' : Type) → [DecidableEq Q'] → TM Q' Γ → List Γ)
      (sim : TM QS Γ) (tSim : ℕ → ℕ),
      sim.isDecider ∧ sim.runsInTime tSim ∧ IsBigO tSim f ∧
      ∀ (Q' : Type) [DecidableEq Q'] (M : TM Q' Γ) (s : ℕ → ℕ),
        M.isDecider → M.runsInTime s → IsBigO s (fun n => f n / Nat.log 2 (f n)) →
          (enc Q' M ∈ sim.language ↔ enc Q' M ∈ M.language) := by sorry

/--
Running a deterministic TM for `n + m` steps is the same as running it for `n`
steps and then `m` more steps from the resulting configuration.
-/
theorem TM.run_add {Q Γ : Type} [DecidableEq Q] (M : TM Q Γ)
    (c : Config Q Γ) (n m : ℕ) :
    M.run c (n + m) = M.run (M.run c n) m := by
  induction m with
  | zero => simp [TM.run]
  | succ m ih => simp [TM.run, ih]

/--
Swapping the accept and reject states of a TM does not change how the next
configuration is computed (the step function only consults `δ`, not the
accept/reject labels). Used to build the diagonalizer machine which complements
the language of the universal simulator.
-/
theorem tm_swap_step_eq {Q Γ : Type} [DecidableEq Q] (sim : TM Q Γ)
    (c : Config Q Γ) :
    let D : TM Q Γ := { sim with
      qAccept := sim.qReject
      qReject := sim.qAccept
      qReject_ne_qAccept := Ne.symm sim.qReject_ne_qAccept }
    D.step c = sim.step c := by
  simp only [TM.step]
  congr 1
  exact propext Or.comm

/--
Iterated version of `tm_swap_step_eq`: swapping the accept/reject states of a TM
leaves every `n`-step run identical to that of the original machine.
-/
theorem tm_swap_run_eq {Q Γ : Type} [DecidableEq Q] (sim : TM Q Γ)
    (c : Config Q Γ) (n : ℕ) :
    let D : TM Q Γ := { sim with
      qAccept := sim.qReject
      qReject := sim.qAccept
      qReject_ne_qAccept := Ne.symm sim.qReject_ne_qAccept }
    D.run c n = sim.run c n := by
  induction n with
  | zero => simp [TM.run]
  | succ n ih =>
    simp only [TM.run]
    rw [ih]
    exact tm_swap_step_eq sim (sim.run c n)

/--
**Existence of a time-diagonalizer.** From a time-constructible bound `f` we
construct a decider `D` running in time `O(f)` whose language differs from the
language of every decider `M` running in time `O(f(n)/log(f(n)))`. `D` is built by
swapping accept/reject on the universal simulator from
`universal_simulation_overhead`, so that it accepts exactly the encodings rejected
by the simulator — a Cantor-style diagonalization within `TIME(f)`.
-/
theorem time_diagonalizer_exists {Γ : Type} (f : ℕ → ℕ) (hf : IsTimeConstructible f) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (D : TM Q Γ),
      (D.decides D.language ∧ ∃ t' : ℕ → ℕ, D.runsInTime t' ∧ IsBigO t' f) ∧
      ∀ (Q' : Type) (_ : DecidableEq Q') (M : TM Q' Γ)
        (t' : ℕ → ℕ), M.decides M.language →
          M.runsInTime t' → IsBigO t' (fun n => f n / Nat.log 2 (f n)) →
            D.language ≠ M.language := by

  obtain ⟨QS, _, hQS, enc, sim, tSim, hSimDec, hSimRuns, hSimBigO, hSimCorrect⟩ :=
    universal_simulation_overhead f hf (Γ := Γ)

  let D : TM QS Γ := { sim with
    qAccept := sim.qReject
    qReject := sim.qAccept
    qReject_ne_qAccept := Ne.symm sim.qReject_ne_qAccept }
  refine ⟨QS, inferInstance, hQS, D, ⟨⟨?_, rfl⟩, tSim, ?_, hSimBigO⟩, ?_⟩

  · intro w
    obtain ⟨n, hn⟩ := hSimDec w
    refine ⟨n, ?_⟩
    simp only [TM.isHaltConfig, TM.isAcceptConfig, TM.isRejectConfig, TM.runOnInput] at *
    rw [tm_swap_run_eq sim _ n]
    exact hn.symm

  · intro w
    have h := hSimRuns w
    simp only [TM.isHaltConfig, TM.isAcceptConfig, TM.isRejectConfig, TM.runOnInput] at *
    rw [tm_swap_run_eq sim _ _]
    exact h.symm

  · intro Q' hQ' M s hMdec hMruns hBigOs

    have hSimM := hSimCorrect Q' M s hMdec.1 hMruns hBigOs

    have hFlip : enc Q' M ∈ D.language ↔ enc Q' M ∉ sim.language := by
      simp only [TM.language, TM.accepts, TM.isAcceptConfig, Set.mem_setOf_eq, TM.runOnInput]

      have hInitEq : D.initConfig (enc Q' M) = sim.initConfig (enc Q' M) := rfl
      have hRunEq : ∀ n, D.run (D.initConfig (enc Q' M)) n =
          sim.run (sim.initConfig (enc Q' M)) n := by
        intro n; rw [hInitEq]; exact tm_swap_run_eq sim _ n
      have hAccEq : D.qAccept = sim.qReject := rfl
      simp_rw [hRunEq, hAccEq]

      constructor
      ·
        intro ⟨n, hn⟩ ⟨m, hm⟩

        have hRunAdd := TM.run_add sim (sim.initConfig (enc Q' M))
        rcases Nat.le_total n m with h | h
        ·
          have hHalt : sim.isHaltConfig (sim.run (sim.initConfig (enc Q' M)) n) :=
            Or.inr hn
          have := sim.run_of_isHaltConfig _ (m - n) hHalt
          have hEq : sim.run (sim.initConfig (enc Q' M)) m =
              sim.run (sim.initConfig (enc Q' M)) n := by
            conv_lhs => rw [show m = n + (m - n) from (Nat.add_sub_cancel' h).symm]
            rw [hRunAdd, this]
          rw [hEq] at hm
          exact absurd (hn.symm.trans hm) sim.qReject_ne_qAccept
        ·
          have hHalt : sim.isHaltConfig (sim.run (sim.initConfig (enc Q' M)) m) :=
            Or.inl hm
          have := sim.run_of_isHaltConfig _ (n - m) hHalt
          have hEq : sim.run (sim.initConfig (enc Q' M)) n =
              sim.run (sim.initConfig (enc Q' M)) m := by
            conv_lhs => rw [show n = m + (n - m) from (Nat.add_sub_cancel' h).symm]
            rw [hRunAdd, this]
          rw [hEq] at hn
          exact absurd (hm.symm.trans hn) (Ne.symm sim.qReject_ne_qAccept)
      ·
        intro hNotAcc
        obtain ⟨n, hn⟩ := hSimDec (enc Q' M)
        simp only [TM.isHaltConfig, TM.isAcceptConfig, TM.isRejectConfig,
          TM.runOnInput] at hn
        cases hn with
        | inl h => exact absurd ⟨n, h⟩ hNotAcc
        | inr h => exact ⟨n, h⟩

    have hDiag : enc Q' M ∈ D.language ↔ enc Q' M ∉ M.language :=
      hFlip.trans (not_congr hSimM)

    intro hEq
    have hcontra : enc Q' M ∈ M.language ↔ enc Q' M ∉ M.language := by
      constructor
      · intro h; exact hDiag.mp (hEq ▸ h)
      · intro h; rw [hEq] at hDiag; exact absurd (hDiag.mpr h) h
    exact hcontra.mp (hcontra.mpr (fun h => hcontra.mp h h))
      (hcontra.mpr (fun h => hcontra.mp h h))

/--
**Time Hierarchy Theorem.** For any time-constructible `f`, there is a language `A`
which is decidable in `TIME(f(n))` but is not decidable in `TIME(g(n))` for any
`g = o(f(n)/log(f(n)))`. Equivalently,
`TIME(o(f(n)/log(f(n)))) ⊊ TIME(f(n))`. Proved by diagonalizing against all
faster machines using `time_diagonalizer_exists`.
-/
theorem time_hierarchy_theorem (f : ℕ → ℕ) (hf : IsTimeConstructible f) :
    ∃ (Γ : Type) (A : Set (List Γ)),
      InTIME f A ∧
      ∀ g : ℕ → ℕ, IsLittleO g (fun n => f n / Nat.log 2 (f n)) → ¬InTIME g A := by

  obtain ⟨Q, _, hQ, D, ⟨hDdec, t', hDruns, hBigO⟩, hdiag⟩ :=
    time_diagonalizer_exists (Γ := Bool) f hf
  refine ⟨Bool, D.language, ?_, ?_⟩
  ·
    exact ⟨Q, inferInstance, hQ, D, t', hDdec, hDruns, hBigO⟩
  ·
    intro g hgo ⟨Q', _, hQ', M, t'', hMdec, hMruns, hBigOt''g⟩

    have hBigOt''flog : IsBigO t'' (fun n => f n / Nat.log 2 (f n)) :=
      hBigOt''g.trans hgo.isBigO


    have hMdecSelf : M.decides M.language := by rwa [hMdec.2]
    exact hdiag Q' hQ' M t'' hMdecSelf hMruns hBigOt''flog hMdec.2.symm

open Computability

namespace SpaceComplexity

/--
`IsAsympDominated g f` is the little-`o` relation on `ℕ → ℕ`: for every constant
`c > 0` there exists `n₀` such that `c · g(n) < f(n)` for all `n ≥ n₀`.
Used to express `g = o(f)` in the Space Hierarchy Theorem.
-/
def IsAsympDominated (g f : ℕ → ℕ) : Prop :=
  ∀ (c : ℕ), 0 < c → ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → c * g n < f n

/--
`InSPACEo f A` says the language `A` is decidable in space `o(f(n))`: some TM
recognizes `A` and runs in space `g` with `g = o(f)`. This is the class
`SPACE(o(f(n)))` appearing in the Space Hierarchy Theorem.
-/
def InSPACEo {Γ : Type} (f : ℕ → ℕ) (A : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (M : TM Q Γ),
    M.language = A ∧
    ∃ g : ℕ → ℕ, IsAsympDominated g f ∧ TMRunsInSpace M g

/--
A function `f : ℕ → ℕ` is **space constructible** if there is a TM decider `M`
whose space usage on every input of length `n` equals `f(n)` exactly once it
halts. This is the standard hypothesis for the Space Hierarchy Theorem.
-/
def SpaceConstructible (f : ℕ → ℕ) : Prop :=
  ∃ (Q Γ : Type) (_ : Fintype Q) (_ : DecidableEq Q) (M : TM Q Γ),
    M.isDecider ∧
    ∀ (w : List Γ) (n : ℕ), M.isHaltConfig (M.runOnInput w n) →
      TMSpaceUsed M w n = f w.length

/--
A **TM description** packages a Turing machine over alphabet `Γ` together with
its number of states. The state type `Fin (numStates + 3)` reserves three states
(start, accept, reject) on top of the working states, providing a uniform shape
for enumeration in the diagonalization construction.
-/
structure TMDesc (Γ : Type) where
  numStates : ℕ
  machine : TM (Fin (numStates + 3)) Γ

/--
The **diagonal language** with respect to an encoding `encode : TMDesc Γ → List Γ`:
the set of strings `w` such that whenever `w` encodes some machine description `d`,
`d.machine` does *not* accept `w`. By Cantor-style diagonalization, this language
differs from every machine's language on at least one encoding.
-/
def diagLang {Γ : Type} (encode : TMDesc Γ → List Γ) : Set (List Γ) :=
  {w : List Γ | ∀ (d : TMDesc Γ), w = encode d → ¬d.machine.accepts w}

/--
Under an injective encoding, membership of `encode d` in the diagonal language is
equivalent to `d.machine` not accepting its own encoding `encode d`.
-/
theorem diagLang_iff {Γ : Type} {encode : TMDesc Γ → List Γ}
    (h_inj : Function.Injective encode) (d : TMDesc Γ) :
    encode d ∈ diagLang encode ↔ ¬d.machine.accepts (encode d) := by
  simp only [diagLang, Set.mem_setOf_eq]
  constructor
  · intro h; exact h d rfl
  · intro hna d' heq
    have := h_inj heq; subst this; exact hna

/--
The diagonal language differs from the language of every machine `d.machine`.
This is the diagonalization core: on its own encoding `encode d`, the two
languages must disagree (whether or not `d.machine` accepts `encode d`).
-/
theorem diagLang_ne {Γ : Type} {encode : TMDesc Γ → List Γ}
    (h_inj : Function.Injective encode) (d : TMDesc Γ) :
    diagLang encode ≠ d.machine.language := by
  intro heq
  have hiff := diagLang_iff h_inj d
  have hmem : encode d ∈ diagLang encode ↔ d.machine.accepts (encode d) := by
    rw [heq]; exact Iff.rfl
  by_cases ha : d.machine.accepts (encode d)
  · exact (hiff.mp (hmem.mpr ha)) ha
  · exact ha (hmem.mp (hiff.mpr ha))

end SpaceComplexity


/--
**Space-bounded universal simulation.** Given a space-constructible bound `f`,
there exists an injective encoding of TM descriptions and a single decider `D`
whose language is the diagonal language `diagLang encode`, runs in space `O(f)`,
and such that every TM `M` running in space `o(f)` is represented (up to language)
by some description `d`. This is the space analogue of
`universal_simulation_overhead` and the engine of the Space Hierarchy Theorem.
-/
theorem SpaceComplexity.sim_overhead {Γ : Type} (f : ℕ → ℕ)
    (hf : SpaceComplexity.SpaceConstructible f) :
    ∃ (encode : SpaceComplexity.TMDesc Γ → List Γ)
      (_ : Function.Injective encode)
      (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q)
      (D : TuringMachine.TM Q Γ),
      D.language = SpaceComplexity.diagLang encode ∧
      (∃ g : ℕ → ℕ, SpaceComplexity.IsAsympBoundedBy g f ∧
        SpaceComplexity.TMRunsInSpace D g) ∧
      (∀ (Q' : Type) (_ : DecidableEq Q') (M : TuringMachine.TM Q' Γ)
        (g : ℕ → ℕ), SpaceComplexity.IsAsympDominated g f →
          SpaceComplexity.TMRunsInSpace M g →
            ∃ (d : SpaceComplexity.TMDesc Γ), d.machine.language = M.language) := by sorry

namespace SpaceComplexity

/--
**Existence of a space-diagonalizer.** From a space-constructible bound `f` we
build a TM `D` that runs in space `O(f)` and whose language differs from the
language of every TM `M` running in space `g = o(f)`. Combines `sim_overhead`
with `diagLang_ne` to produce the witness used in the Space Hierarchy Theorem.
-/
theorem diagonalizer_exists {Γ : Type} (f : ℕ → ℕ) (hf : SpaceConstructible f) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (D : TM Q Γ),
      (∃ g : ℕ → ℕ, IsAsympBoundedBy g f ∧ TMRunsInSpace D g) ∧
      ∀ (Q' : Type) (_ : DecidableEq Q') (M : TM Q' Γ)
        (g : ℕ → ℕ), IsAsympDominated g f → TMRunsInSpace M g →
          D.language ≠ M.language := by
  obtain ⟨encode, h_inj, Q, _, hQ, D, hDlang, ⟨g, hgf, hDg⟩, h_reindex⟩ :=
    sim_overhead f hf (Γ := Γ)
  exact ⟨Q, inferInstance, hQ, D, ⟨g, hgf, hDg⟩, fun Q' hQ' M g' hg'o hMg' => by
    obtain ⟨d, hd⟩ := h_reindex Q' hQ' M g' hg'o hMg'
    rw [hDlang]
    exact fun heq => diagLang_ne h_inj d (heq.trans hd.symm)⟩

/--
**Space Hierarchy Theorem.** For any space-constructible `f`, there exists a
language `A` decidable in `SPACE(f(n))` but not in `SPACE(o(f(n)))`. In other
words, `SPACE(o(f(n))) ⊊ SPACE(f(n))`. Proved by exhibiting the diagonalizer
machine from `diagonalizer_exists`.
-/
theorem space_hierarchy_theorem {Γ : Type}
    (f : ℕ → ℕ) (hf : SpaceConstructible f) :
    ∃ A : Set (List Γ), InSPACE f A ∧ ¬InSPACEo f A := by
  obtain ⟨Q, _, hQ, D, ⟨g, hgf, hDg⟩, hdiag⟩ := diagonalizer_exists f hf (Γ := Γ)
  refine ⟨D.language, ?_, ?_⟩
  ·
    exact ⟨Q, inferInstance, hQ, D, rfl, g, hgf, hDg⟩
  ·
    intro ⟨Q', _, hQ', M, hML, g', hg'f, hMg'⟩
    exact hdiag Q' hQ' M g' hg'f hMg' hML.symm

end SpaceComplexity

open SpaceComplexity

namespace OracleComputation

open TuringMachine

/--
A **deterministic oracle Turing machine** over state set `Q` and tape alphabet `Γ`.
Beyond the usual TM data (blank symbol, input alphabet, transition `δ`, start state,
accept/reject states), the machine has a distinguished query state `qQuery` and an
oracle `oracle ⊆ List Γ`. The transition function takes an extra `Bool` reading the
oracle's answer to the current query tape, so the machine can consult oracle
membership in a single step.
-/
structure OracleTM (Q : Type) (Γ : Type) where
  blank : Γ
  inputAlpha : Set Γ
  blank_not_in_inputAlpha : blank ∉ inputAlpha
  δ : Q → Γ → Bool → Q × Γ × Direction
  q₀ : Q
  qAccept : Q
  qReject : Q
  qReject_ne_qAccept : qReject ≠ qAccept
  qQuery : Q
  oracle : Set (List Γ)

/--
A configuration of an oracle TM: the current state, head position on the
two-way infinite tape, the tape contents, and the contents of the auxiliary
**query tape** which holds the string to be tested against the oracle.
-/
structure OracleConfig (Q : Type) (Γ : Type) where
  state : Q
  headPos : ℤ
  tape : ℤ → Γ
  queryTape : List Γ

variable {Q : Type} {Γ : Type} [DecidableEq Q]

/--
One computation step of a deterministic oracle TM. If the current state is
`qAccept` or `qReject`, the configuration is left unchanged (halted). Otherwise
the oracle answer is computed (as `queryTape ∈ oracle` when in `qQuery`, else
`false`), `δ` is consulted, and the head, state, and tape are updated.
-/
noncomputable def OracleTM.step (M : OracleTM Q Γ) (c : OracleConfig Q Γ) :
    OracleConfig Q Γ :=
  if c.state = M.qAccept ∨ c.state = M.qReject then c
  else
    let oracleAnswer : Bool :=
      if c.state = M.qQuery then
        Classical.propDecidable (c.queryTape ∈ M.oracle) |>.decide
      else false
    let (q', b, d) := M.δ c.state (c.tape c.headPos) oracleAnswer
    { state := q'
      headPos := match d with
        | Direction.L => c.headPos - 1
        | Direction.R => c.headPos + 1
      tape := Function.update c.tape c.headPos b
      queryTape := c.queryTape }

/-- `M.run c n` applies `M.step` exactly `n` times starting from configuration `c`. -/
noncomputable def OracleTM.run (M : OracleTM Q Γ) (c : OracleConfig Q Γ) :
    ℕ → OracleConfig Q Γ
  | 0 => c
  | n + 1 => M.step (M.run c n)

/--
The initial oracle TM configuration on input `w`: state is `q₀`, head at position
`0`, tape contains `w` on cells `0, …, w.length - 1` and `blank` elsewhere, and the
query tape is empty.
-/
def OracleTM.initConfig (M : OracleTM Q Γ) (w : List Γ) : OracleConfig Q Γ where
  state := M.q₀
  headPos := 0
  tape := fun i =>
    if h : 0 ≤ i ∧ i < w.length then
      w.get ⟨i.toNat, by omega⟩
    else M.blank
  queryTape := []

/-- Run `M` for `n` steps starting from its initial configuration on input `w`. -/
noncomputable def OracleTM.runOnInput (M : OracleTM Q Γ) (w : List Γ) (n : ℕ) :
    OracleConfig Q Γ :=
  M.run (M.initConfig w) n

/-- `M.accepts w` if some finite-step run of `M` on input `w` ends in `qAccept`. -/
noncomputable def OracleTM.accepts (M : OracleTM Q Γ) (w : List Γ) : Prop :=
  ∃ n : ℕ, (M.runOnInput w n).state = M.qAccept

/-- `M.halts w` if some finite-step run of `M` on `w` reaches `qAccept` or `qReject`. -/
noncomputable def OracleTM.halts (M : OracleTM Q Γ) (w : List Γ) : Prop :=
  ∃ n : ℕ, (M.runOnInput w n).state = M.qAccept ∨
            (M.runOnInput w n).state = M.qReject

/-- The **language** of an oracle TM `M` is the set of strings it accepts. -/
noncomputable def OracleTM.language (M : OracleTM Q Γ) : Set (List Γ) :=
  {w | M.accepts w}

/-- An oracle TM `M` is a **decider** if it halts on every input. -/
noncomputable def OracleTM.isDecider (M : OracleTM Q Γ) : Prop :=
  ∀ w : List Γ, M.halts w

/-- `M.decides B` means `M` is a decider and `L(M) = B`. -/
noncomputable def OracleTM.decides (M : OracleTM Q Γ) (B : Set (List Γ)) : Prop :=
  M.isDecider ∧ M.language = B

/--
`M.runsInTime t` if on every input `w`, `M` reaches an accept or reject state
within `t(|w|)` steps.
-/
noncomputable def OracleTM.runsInTime (M : OracleTM Q Γ) (t : ℕ → ℕ) : Prop :=
  ∀ w : List Γ,
    (M.runOnInput w (t w.length)).state = M.qAccept ∨
    (M.runOnInput w (t w.length)).state = M.qReject

/--
A **nondeterministic oracle Turing machine**: like `OracleTM` but the transition
function `δ` returns a *set* of possible next moves at each step. Used to define
NP-with-oracle complexity classes.
-/
structure OracleNTM (Q : Type) (Γ : Type) where
  blank : Γ
  inputAlpha : Set Γ
  blank_not_in_inputAlpha : blank ∉ inputAlpha
  δ : Q → Γ → Bool → Set (Q × Γ × Direction)
  q₀ : Q
  qAccept : Q
  qReject : Q
  qReject_ne_qAccept : qReject ≠ qAccept
  qQuery : Q
  oracle : Set (List Γ)

/--
Single-step relation for an oracle NTM: `M.step c₁ c₂` holds when `c₂` is one of
the configurations reachable from `c₁` in one step (or `c₂ = c₁` if `c₁` is a
halt configuration). Membership of `queryTape` in `oracle` is consulted whenever
the state is `qQuery`.
-/
noncomputable def OracleNTM.step (M : OracleNTM Q Γ) (c₁ c₂ : OracleConfig Q Γ) : Prop :=
  if c₁.state = M.qAccept ∨ c₁.state = M.qReject then c₂ = c₁
  else
    let oracleAnswer : Bool :=
      if c₁.state = M.qQuery then
        Classical.propDecidable (c₁.queryTape ∈ M.oracle) |>.decide
      else false
    ∃ q' b d, (q', b, d) ∈ M.δ c₁.state (c₁.tape c₁.headPos) oracleAnswer ∧
      let newHeadPos := match d with
        | Direction.L => c₁.headPos - 1
        | Direction.R => c₁.headPos + 1
      c₂ = ⟨q', newHeadPos, Function.update c₁.tape c₁.headPos b, c₁.queryTape⟩

/-- Initial configuration of an oracle NTM on input `w` (analogous to `OracleTM.initConfig`). -/
def OracleNTM.initConfig (M : OracleNTM Q Γ) (w : List Γ) : OracleConfig Q Γ where
  state := M.q₀
  headPos := 0
  tape := fun i =>
    if h : 0 ≤ i ∧ i < w.length then
      w.get ⟨i.toNat, by omega⟩
    else M.blank
  queryTape := []

/-- A configuration is a **halt configuration** if its state is `qAccept` or `qReject`. -/
def OracleNTM.isHaltConfig (M : OracleNTM Q Γ) (c : OracleConfig Q Γ) : Prop :=
  c.state = M.qAccept ∨ c.state = M.qReject

/-- A configuration is an **accept configuration** if its state equals `qAccept`. -/
def OracleNTM.isAcceptConfig (M : OracleNTM Q Γ) (c : OracleConfig Q Γ) : Prop :=
  c.state = M.qAccept

/--
`M.accepts w` if there exists some nondeterministic computation **branch** of `M`
on `w` (a finite sequence of valid step-related configurations starting from
`M.initConfig w`) ending in an accept configuration.
-/
noncomputable def OracleNTM.accepts (M : OracleNTM Q Γ) (w : List Γ) : Prop :=
  ∃ (n : ℕ) (branch : Fin (n + 1) → OracleConfig Q Γ),
    branch ⟨0, Nat.zero_lt_succ n⟩ = M.initConfig w ∧
    (∀ (i : Fin n), M.step (branch i.castSucc) (branch i.succ)) ∧
    M.isAcceptConfig (branch ⟨n, Nat.lt_succ_of_le le_rfl⟩)

/-- The language of an oracle NTM `M` is the set of strings it accepts. -/
noncomputable def OracleNTM.language (M : OracleNTM Q Γ) : Set (List Γ) :=
  {w | M.accepts w}

/--
An oracle NTM `M` is a **decider** if every nondeterministic branch from the
initial configuration eventually reaches a halt configuration.
-/
noncomputable def OracleNTM.isDecider (M : OracleNTM Q Γ) : Prop :=
  ∀ w : List Γ, ∀ (n : ℕ) (branch : Fin (n + 1) → OracleConfig Q Γ),
    0 < n →
    branch ⟨0, Nat.zero_lt_succ n⟩ = M.initConfig w →
    (∀ (i : Fin n), M.step (branch i.castSucc) (branch i.succ)) →
    ∃ k : Fin (n + 1), M.isHaltConfig (branch k)

/-- `M.decides B` if `M` is a decider whose language is `B`. -/
noncomputable def OracleNTM.decides (M : OracleNTM Q Γ) (B : Set (List Γ)) : Prop :=
  M.isDecider ∧ M.language = B

/--
`M.runsInTime t` if on every input `w` and every valid branch of length
`k ≤ t(|w|)`, the configuration at step `k` is a halt configuration.
-/
noncomputable def OracleNTM.runsInTime (M : OracleNTM Q Γ) (t : ℕ → ℕ) : Prop :=
  ∀ w : List Γ,
    ∀ (k : ℕ) (branch : Fin (k + 1) → OracleConfig Q Γ),
      0 < k →
      branch ⟨0, Nat.zero_lt_succ k⟩ = M.initConfig w →
      (∀ (i : Fin k), M.step (branch i.castSucc) (branch i.succ)) →
      k ≤ t w.length →
      M.isHaltConfig (branch ⟨k, Nat.lt_succ_of_le le_rfl⟩)

/--
`InPWithOracle A B` says `B ∈ P^A`: some deterministic oracle TM with oracle `A`
decides `B` in polynomial time `n^k`.
-/
def InPWithOracle {Γ : Type} (A B : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : DecidableEq Q) (M : OracleTM Q Γ),
    M.oracle = A ∧ M.decides B ∧ ∃ k : ℕ, M.runsInTime (fun n => n ^ k)

/--
`InNPWithOracle A B` says `B ∈ NP^A`: some nondeterministic oracle TM with
oracle `A` decides `B` in polynomial time `n^k`.
-/
def InNPWithOracle {Γ : Type} (A B : Set (List Γ)) : Prop :=
  ∃ (Q : Type) (_ : DecidableEq Q) (M : OracleNTM Q Γ),
    M.oracle = A ∧ M.decides B ∧ ∃ k : ℕ, M.runsInTime (fun n => n ^ k)

/-- The complexity class `P^A`: all languages decidable in P with oracle `A`. -/
def ClassPWithOracle {Γ : Type} (A : Set (List Γ)) : Set (Set (List Γ)) :=
  {B | InPWithOracle A B}

/-- The complexity class `NP^A`: all languages decidable in NP with oracle `A`. -/
def ClassNPWithOracle {Γ : Type} (A : Set (List Γ)) : Set (Set (List Γ)) :=
  {B | InNPWithOracle A B}

/-- `InPSPACE A` (in this namespace) reuses the definition `SpaceComplexity.InPSPACE`. -/
def InPSPACE {Γ : Type} (A : Set (List Γ)) : Prop :=
  SpaceComplexity.InPSPACE A

/-- `InNPSPACE A` (in this namespace) reuses the definition `SpaceComplexity.InNPSPACE`. -/
def InNPSPACE {Γ : Type} (A : Set (List Γ)) : Prop :=
  SpaceComplexity.InNPSPACE A

/--
`TQBF` is the language of *true* quantified Boolean formulae under encoding `enc`
(a wrapper over `SpaceComplexity.tqbfLanguage`). `TQBF` is the canonical
PSPACE-complete language used here as an oracle.
-/
def TQBF {Γ : Type} [Inhabited Γ] (enc : SpaceComplexity.QBFEncoding Γ) :
    Set (List Γ) :=
  SpaceComplexity.tqbfLanguage enc

end OracleComputation


/-- `PSPACE ⊆ NPSPACE`: any deterministic PSPACE machine is a (trivial) nondeterministic one. -/
theorem pspace_subset_npspace_helper
  {Γ : Type} (A : Set (List Γ)) : OracleComputation.InPSPACE A → OracleComputation.InNPSPACE A := by sorry

/--
**Savitch's Theorem at the PSPACE level**: `NPSPACE = PSPACE`. Forward direction
is the standard Savitch simulation `NSPACE(s) ⊆ SPACE(s²)`; the reverse direction
is trivial inclusion.
-/
theorem savitch_theorem_pspace
    {Γ : Type} (A : Set (List Γ)) :
    OracleComputation.InNPSPACE A ↔ OracleComputation.InPSPACE A := by
  constructor
  ·
    exact SpaceComplexity.npspace_subset_pspace A
  ·
    exact pspace_subset_npspace_helper A

/--
`NP^TQBF ⊆ NPSPACE`: any nondeterministic polynomial-time machine using a TQBF
oracle can be simulated in nondeterministic polynomial space, since each oracle
query can be answered in PSPACE.
-/
theorem np_tqbf_sub_npspace
  {Γ : Type} [Inhabited Γ] (enc : SpaceComplexity.QBFEncoding Γ)
  (B : Set (List Γ)) :
  OracleComputation.InNPWithOracle (OracleComputation.TQBF enc) B →
  OracleComputation.InNPSPACE B := by sorry

/--
If `B ≤_P A` then `B ∈ P^A`: a polynomial-time reduction can be carried out by a
P machine that calls the oracle `A` once on the reduced input.
-/
theorem poly_reducible_implies_in_P_oracle
  {Γ : Type} (A B : Set (List Γ)) :
  TuringMachine.PolyReducible B A →
  OracleComputation.InPWithOracle A B := by sorry

/--
`PSPACE ⊆ P^TQBF`: every PSPACE language polynomial-time reduces to TQBF (since
TQBF is PSPACE-complete), so it is in `P` with a TQBF oracle.
-/
theorem pspace_sub_p_tqbf
  {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
  (enc : SpaceComplexity.QBFEncoding Γ)
  (B : Set (List Γ)) :
  OracleComputation.InPSPACE B →
  OracleComputation.InPWithOracle (OracleComputation.TQBF enc) B := by
  intro hB
  have hRed : TuringMachine.PolyReducible B (SpaceComplexity.tqbfLanguage enc) :=
    SpaceComplexity.tqbf_pspace_hard enc B hB
  exact poly_reducible_implies_in_P_oracle (SpaceComplexity.tqbfLanguage enc) B hRed

/-- `P^A ⊆ NP^A` for every oracle `A`: a deterministic oracle machine is a (trivial) nondeterministic one. -/
theorem p_oracle_sub_np_oracle
  {Γ : Type} (A B : Set (List Γ)) :
  OracleComputation.InPWithOracle A B → OracleComputation.InNPWithOracle A B := by sorry

namespace OracleComputation

/--
**There exists an oracle `A` such that `P^A = NP^A`.** Take `A = TQBF`. Then both
`P^TQBF` and `NP^TQBF` collapse to `PSPACE`: the containments
`P^TQBF ⊆ NP^TQBF ⊆ NPSPACE = PSPACE ⊆ P^TQBF` together with Savitch's theorem
give equality. This is the classic "relativization barrier" result for P vs NP.
-/
theorem exists_oracle_P_eq_NP {Γ : Type} [Inhabited Γ] [DecidableEq Γ] [Fintype Γ]
    (enc : SpaceComplexity.QBFEncoding Γ) :
    ∃ A : Set (List Γ), ClassPWithOracle A = ClassNPWithOracle A := by
  use TQBF enc
  ext B
  simp only [ClassPWithOracle, ClassNPWithOracle, Set.mem_setOf_eq]
  constructor
  · exact p_oracle_sub_np_oracle (TQBF enc) B
  · intro hB
    have h1 : InNPSPACE B := np_tqbf_sub_npspace enc B hB
    have h2 : InPSPACE B := (savitch_theorem_pspace B).mp h1
    exact pspace_sub_p_tqbf enc B h2

end OracleComputation
