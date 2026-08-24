/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfComputation.code.InteractiveProofs
import Atlas.TheoryOfComputation.code.SharpSAT
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

namespace NPCompleteness

/--
Arithmetization of a Boolean formula: lifts a Boolean formula `φ` to a polynomial
expression over a commutative ring `R` using the standard encoding
`true ↦ 1`, `false ↦ 0`, `¬x ↦ 1 - x`, `x ∧ y ↦ x * y`, `x ∨ y ↦ x + y - x*y`.
This is the foundation of the sum-check protocol used to show `#SAT ∈ IP`.
-/
noncomputable def BoolFormula.arithEval {R : Type*} [CommRing R]
    (σ : ℕ → R) : BoolFormula → R
  | .var n => σ n
  | .trueConst => 1
  | .falseConst => 0
  | .not φ => 1 - φ.arithEval σ
  | .and φ ψ => φ.arithEval σ * ψ.arithEval σ
  | .or φ ψ => φ.arithEval σ + ψ.arithEval σ - φ.arithEval σ * ψ.arithEval σ

/--
Partial count: number of satisfying assignments of `φ` over `m` variables, where
the first `i` variables are fixed by `presets` and the remaining `m - i` are
quantified. Used to express intermediate sums in the sum-check protocol.
-/
noncomputable def BoolFormula.partialCount
    (φ : BoolFormula) (m i : ℕ) (presets : Fin i → Bool) : ℕ :=
  Finset.card (Finset.univ.filter (fun (σ : Fin (m - i) → Bool) =>
    φ.eval (fun k =>
      if h : k < i then presets ⟨k, h⟩
      else if h2 : k < m then σ ⟨k - i, by omega⟩
      else false) = true))

/--
Count of satisfying assignments of `φ` indexed by the first `m` Boolean
variables. Equivalent to `#SAT` for the formula `φ` when `m` bounds its
variable indices.
-/
noncomputable def BoolFormula.countSatFin (φ : BoolFormula) (m : ℕ) : ℕ :=
  Finset.card (Finset.univ.filter (fun (σ : Fin m → Bool) =>
    φ.eval (fun i => if h : i < m then σ ⟨i, h⟩ else false) = true))

end NPCompleteness

namespace SharpSATInIP

open InteractiveProofs NPCompleteness TuringMachine

/--
An encoding of `#SAT` instances `⟨φ, k⟩` (a Boolean formula together with a count)
as strings over the tape alphabet `Γ`. The roundtripping laws `decode_encode`
and `encode_decode` make the encoding a bijection onto its image.
-/
structure SharpSATEncoding (Γ : Type) where
  encode : BoolFormula × ℕ → List Γ
  decode : List Γ → Option (BoolFormula × ℕ)
  decode_encode : ∀ p, decode (encode p) = some p
  encode_decode : ∀ w p, decode w = some p → encode p = w

/--
The language `#SAT` realised over the alphabet `Γ` via `enc`:
`{w | enc(w) = ⟨φ, k⟩ and k = #sat(φ)}`, i.e. encodings of `⟨φ, k⟩` where `φ`
has exactly `k` satisfying assignments.
-/
def SharpSAT_enc {Γ : Type} (enc : SharpSATEncoding Γ) : Set (List Γ) :=
  {w | ∃ φ k, enc.decode w = some (φ, k) ∧ k = φ.sharpSat}

/--
A `SumCheckEncoding` extends a `SharpSATEncoding` with the auxiliary data needed
to run the sum-check protocol:

* a finite field `ZMod q` (with `q ≠ 0`),
* a fixed number of random bits per field element (`bitsPerField`) with a
  conversion `coinsToField`,
* encode/decode functions for both a single field element and a triple of field
  elements (used by the verifier to send a challenge and by the prover to send
  the three values `v₀`, `v₁`, `v_r` per round).
-/
structure SumCheckEncoding (Γ : Type) extends SharpSATEncoding Γ where
  q : ℕ
  hq_ne : NeZero q
  bitsPerField : ℕ
  hbits_pos : 0 < bitsPerField
  coinsToField : (Fin bitsPerField → Bool) → ZMod q
  encodeTriple : ZMod q → ZMod q → ZMod q → List Γ
  decodeTriple : List Γ → Option (ZMod q × ZMod q × ZMod q)
  decode_encodeTriple : ∀ a b c, decodeTriple (encodeTriple a b c) = some (a, b, c)
  encodeField : ZMod q → List Γ
  decodeField : List Γ → Option (ZMod q)
  decode_encodeField : ∀ x, decodeField (encodeField x) = some x

/--
The univariate polynomial that the honest prover sends in round `i` of the
sum-check protocol, evaluated at point `z`: with the first `i` variables fixed
to the previously chosen field challenges, variable `x_i` set to `z`, sum over
all Boolean assignments of the remaining `m - i - 1` variables of `arithEval φ`.
-/
noncomputable def arithPartialSum {q : ℕ} [NeZero q]
    (φ : BoolFormula) (m : ℕ) (challenges : ℕ → ZMod q)
    (i : ℕ) (z : ZMod q) : ZMod q :=
  if _h : i < m then
    Finset.sum (Finset.univ : Finset (Fin (m - i - 1) → Bool))
      (fun σ => φ.arithEval (fun j =>
        if j < i then challenges j
        else if j = i then z
        else if h2 : j - i - 1 < m - i - 1 then
          if σ ⟨j - i - 1, h2⟩ then 1 else 0
        else 0))
  else 0

/--
The verifier in the sum-check protocol for `#SAT`. In each of the `m` rounds it
extracts random field-element challenges from its coin tape and sends them to
the prover. After all rounds it checks (i) that each prover-message triple
`(v₀, v₁, v_r)` satisfies `v₀ + v₁ = ` previously claimed value, and (ii) that
the final claim equals `arithEval φ` at the chosen random point.
-/
noncomputable def sumCheckVerifier {Γ : Type} (enc : SumCheckEncoding Γ) :
    Verifier Unit Γ where
  sendMessage := fun w n coins transcript =>
    match enc.toSharpSATEncoding.decode w with
    | none => []
    | some (φ, _) =>
      let m := φ.numVars
      let roundIdx := transcript.length / 2
      if _h : roundIdx < m then

        let startBit := roundIdx * enc.bitsPerField
        let bits : Fin enc.bitsPerField → Bool := fun j =>
          if h2 : startBit + j.val < n then coins ⟨startBit + j.val, h2⟩ else false
        enc.encodeField (enc.coinsToField bits)
      else []
  decide := fun w n coins transcript =>
    match enc.toSharpSATEncoding.decode w with
    | none => false
    | some (φ, k) =>
      haveI := enc.hq_ne
      let m := φ.numVars
      if transcript.length ≠ 2 * m then false
      else

        let getChallenge : ℕ → ZMod enc.q := fun i =>
          let startBit := i * enc.bitsPerField
          let bits : Fin enc.bitsPerField → Bool := fun j =>
            if h2 : startBit + j.val < n then coins ⟨startBit + j.val, h2⟩ else false
          enc.coinsToField bits

        let getProverMsg : ℕ → Option (ZMod enc.q × ZMod enc.q × ZMod enc.q) := fun i =>
          match transcript[2 * i + 1]? with
          | none => none
          | some msg => enc.decodeTriple msg


        let result := List.range m |>.foldl (fun acc i =>
          match acc with
          | none => none
          | some claimedVal =>
            match getProverMsg i with
            | none => none
            | some (v0, v1, vr) =>
              if v0 + v1 = claimedVal then some vr
              else none)
          (some (k : ZMod enc.q))
        match result with
        | none => false
        | some finalClaimed =>


          let finalEval := φ.arithEval (fun j =>
            if j < m then getChallenge j else 0)
          finalClaimed == finalEval

/--
The honest prover for the sum-check protocol on `#SAT`. In round `i` it sends
the triple `(v₀, v₁, v_r)` where `v_b = Σ_{x_{i+1},…,x_{m-1}} arithEval φ` with
`x_0,…,x_{i-1}` set to past challenges and `x_i = b` (or `b = r`, the current
verifier challenge).
-/
noncomputable def sumCheckHonestProver {Γ : Type} (enc : SumCheckEncoding Γ) :
    Prover Γ :=
  fun w transcript =>
    match enc.toSharpSATEncoding.decode w with
    | none => []
    | some (φ, _) =>
      haveI := enc.hq_ne
      let m := φ.numVars
      let roundIdx := transcript.length / 2
      if roundIdx ≥ m then [] else

      let getChallenge : ℕ → ZMod enc.q := fun j =>
        match transcript[2 * j]? with
        | none => 0
        | some msg => match enc.decodeField msg with
          | some r => r
          | none => 0
      let currentR : ZMod enc.q := getChallenge roundIdx

      let v0 := arithPartialSum φ m getChallenge roundIdx 0
      let v1 := arithPartialSum φ m getChallenge roundIdx 1
      let vr := arithPartialSum φ m getChallenge roundIdx currentR
      enc.encodeTriple v0 v1 vr

/--
If the verifier accepts on every coin sequence then the acceptance probability
is `1 ≥ 2/3`. Used as the completeness side of the `IP` membership argument.
-/
theorem acceptProb_ge_of_all_accept {Q Γ : Type} [DecidableEq Γ]
    (V : Verifier Q Γ) (P : Prover Γ) (w : List Γ) (n : ℕ) (numRounds : ℕ)
    (h : ∀ coins : Fin n → Bool, runProtocol V P w n coins numRounds = true) :
    V.acceptProb P w n numRounds ≥ 2 / 3 := by
  simp only [Verifier.acceptProb, Verifier.numAccepting]
  rw [Finset.filter_eq_self.mpr (fun c _ => h c), Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin,
      Nat.cast_pow, Nat.cast_ofNat,
      div_self (pow_ne_zero _ (by norm_num : (2 : ℚ) ≠ 0))]
  norm_num

/--
If the verifier rejects on every coin sequence then the acceptance probability
is `0 ≤ 1/3`. Used to handle the degenerate (decode-failure) branch of the
sum-check soundness argument.
-/
theorem acceptProb_le_of_all_reject {Q Γ : Type} [DecidableEq Γ]
    (V : Verifier Q Γ) (P : Prover Γ) (w : List Γ) (n : ℕ) (numRounds : ℕ)
    (h : ∀ coins : Fin n → Bool, runProtocol V P w n coins numRounds = false) :
    V.acceptProb P w n numRounds ≤ 1 / 3 := by
  simp only [Verifier.acceptProb, Verifier.numAccepting]
  rw [Finset.filter_eq_empty_iff.mpr
    (fun c _ => by rw [h c]; exact Bool.false_ne_true),
    Finset.card_empty, Nat.cast_zero, zero_div]
  norm_num


/--
Completeness of the sum-check protocol: if `w` encodes `⟨φ, k⟩` with
`k = #sat(φ)`, then for every coin tape the verifier accepts when run against
the honest prover. This is the easy direction of `#SAT ∈ IP`.
-/
theorem sumCheck_completeness
    {Γ : Type} [DecidableEq Γ]
    (enc : SumCheckEncoding Γ) (w : List Γ) (φ : BoolFormula) (k : ℕ)
    (hdec : enc.toSharpSATEncoding.decode w = some (φ, k))
    (hk : k = φ.sharpSat)
    (coins : Fin (w.length * enc.bitsPerField) → Bool) :
    runProtocol (sumCheckVerifier enc) (sumCheckHonestProver enc) w
      (w.length * enc.bitsPerField) coins w.length = true := by sorry


/--
Soundness bound via Schwartz–Zippel: if `w` encodes `⟨φ, k⟩` with `k ≠ #sat(φ)`,
then for any (possibly dishonest) prover `P'`, the number of coin sequences on
which the sum-check verifier accepts is at most `2^(n)/3` where `n` is the
length of the coin tape. This is the quantitative form of the soundness
guarantee `Pr[V accepts] ≤ 1/3`.
-/
theorem schwartz_zippel_numAccepting_bound
    {Γ : Type} [DecidableEq Γ]
    (enc : SumCheckEncoding Γ) (w : List Γ) (φ : BoolFormula) (k : ℕ)
    (hdec : enc.toSharpSATEncoding.decode w = some (φ, k))
    (hk : k ≠ φ.sharpSat)
    (P' : Prover Γ) :
    (sumCheckVerifier enc).numAccepting P' w (w.length * enc.bitsPerField) w.length * 3
      ≤ 2 ^ (w.length * enc.bitsPerField) := by sorry

/--
Soundness of the sum-check protocol: if `w` is not in `#SAT` (either it fails
to decode or it decodes to `⟨φ, k⟩` with `k ≠ #sat(φ)`), then no prover can make
the verifier accept with probability greater than `1/3`.
-/
theorem sumCheck_soundness
    {Γ : Type} [DecidableEq Γ]
    (enc : SumCheckEncoding Γ) (w : List Γ)
    (hw : ∀ φ k, enc.toSharpSATEncoding.decode w = some (φ, k) → k ≠ φ.sharpSat)
    (P' : Prover Γ) :
    (sumCheckVerifier enc).acceptProb P' w (w.length * enc.bitsPerField) w.length ≤ 1 / 3 := by
  cases hdec : enc.toSharpSATEncoding.decode w with
  | none =>

    apply acceptProb_le_of_all_reject
    intro coins
    simp only [runProtocol]
    unfold runRounds
    simp only [sumCheckVerifier, hdec]
  | some p =>
    obtain ⟨φ, k⟩ := p
    have hk : k ≠ φ.sharpSat := hw φ k hdec

    have hbound := schwartz_zippel_numAccepting_bound enc w φ k hdec hk P'

    simp only [Verifier.acceptProb]
    have h2n_pos : (0 : ℚ) < 2 ^ (w.length * enc.bitsPerField) :=
      pow_pos (by norm_num : (0 : ℚ) < 2) _
    rw [div_le_div_iff₀ h2n_pos (by norm_num : (0 : ℚ) < 3)]
    rw [one_mul]
    exact_mod_cast hbound

/--
The main theorem of this file: `#SAT ∈ IP`. Given any `SumCheckEncoding` of
`⟨φ, k⟩` instances, the sum-check protocol (verifier + honest prover) is an
interactive proof system for the language `SharpSAT_enc` with polynomially many
rounds and coins, completeness ≥ 2/3 and soundness ≤ 1/3.
-/
theorem sharpSAT_in_IP {Γ : Type} [DecidableEq Γ]
    (enc : SumCheckEncoding Γ) : InIP (SharpSAT_enc enc.toSharpSATEncoding) := by
  refine ⟨Unit, inferInstance,
    sumCheckVerifier enc,
    sumCheckHonestProver enc,
    2, fun n => n * enc.bitsPerField,
    1, fun n => n,
    ?_, ?_, ?_⟩
  ·
    exact ⟨enc.bitsPerField, 1, enc.hbits_pos, fun n hn => by
      simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
      calc n * enc.bitsPerField
          = enc.bitsPerField * n := Nat.mul_comm n enc.bitsPerField
        _ ≤ enc.bitsPerField * (n * n) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.lt_of_lt_of_le Nat.one_pos hn))⟩
  ·
    exact ⟨1, 0, Nat.one_pos, fun n _ => by simp⟩
  ·
    constructor
    ·
      intro w ⟨φ, k, hdec, hk⟩
      apply acceptProb_ge_of_all_accept
      intro coins
      exact sumCheck_completeness enc w φ k hdec hk coins
    ·
      intro w hw P'
      simp only [SharpSAT_enc, Set.mem_setOf_eq] at hw
      push_neg at hw
      exact sumCheck_soundness enc w hw P'

end SharpSATInIP
