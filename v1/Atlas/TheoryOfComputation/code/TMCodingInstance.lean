/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TheoryOfComputation.code.RecursionTheorem
import Atlas.TheoryOfComputation.code.SelfReference

/-- A fixed binary encoding `⟨·⟩ : ℕ → List Bool` of natural-number TM indices. -/
noncomputable instance TMCodingInstance.stdEncode : ℕ → List Bool := by sorry
/-- A partial decoder for `stdEncode`, returning the natural number whose
encoding equals the given bit string (if any). -/
noncomputable instance TMCodingInstance.stdDecode : List Bool → Option ℕ := by sorry
/-- The decoder is a left inverse of the encoder: `stdDecode ∘ stdEncode = some`. -/
theorem TMCodingInstance.stdDecode_encode :
  ∀ n : ℕ, TMCodingInstance.stdDecode (TMCodingInstance.stdEncode n) = some n := by sorry

/-- The standard semantics of a TM index: on input `w` it returns the
`TMResult` of running the encoded machine on `w` (accept, reject, or loop). -/
noncomputable instance TMCodingInstance.stdBehavior : ℕ → List Bool → RecursionTheorem.TMResult := by sorry

/-- The language recognized by TM index `M`: the set of strings accepted by
the standard behavior. -/
def TMCodingInstance.stdLanguageOf (M : ℕ) : Set (List Bool) :=
  {w | TMCodingInstance.stdBehavior M w = RecursionTheorem.TMResult.accept}

/-- A computable injective pairing function on bit strings, used to encode a
pair `⟨a,b⟩` as a single bit string. -/
noncomputable instance TMCodingInstance.stdPair : List Bool → List Bool → List Bool := by sorry
/-- The pairing function is injective in both arguments simultaneously. -/
theorem TMCodingInstance.stdPair_injective :
  ∀ a b c d, TMCodingInstance.stdPair a b = TMCodingInstance.stdPair c d → a = c ∧ b = d := by sorry
/-- The s-m-n function: `stdSmn e x` is an index of the TM obtained from index `e`
by hard-coding `x` as the first argument. -/
noncomputable instance TMCodingInstance.stdSmn : ℕ → ℕ → ℕ := by sorry

/-- s-m-n specification at the behavior level: running `stdSmn e x` on `w`
behaves exactly like running `e` on the paired input `⟨w, ⟨x⟩⟩`. -/
theorem TMCodingInstance.stdSmn_spec_behavior :
  ∀ (e x : ℕ) (w : List Bool),
    TMCodingInstance.stdBehavior (TMCodingInstance.stdSmn e x) w =
    TMCodingInstance.stdBehavior e (TMCodingInstance.stdPair w (TMCodingInstance.stdEncode x)) := by sorry

/-- s-m-n specification at the language level: `w` is in `L(stdSmn e x)` iff
`⟨w, ⟨x⟩⟩` is in `L(e)`. -/
theorem TMCodingInstance.stdSmn_spec
    (e x : ℕ) (w : List Bool) :
    w ∈ TMCodingInstance.stdLanguageOf (TMCodingInstance.stdSmn e x) ↔
    (TMCodingInstance.stdPair w (TMCodingInstance.stdEncode x)) ∈
      TMCodingInstance.stdLanguageOf e := by
  simp only [stdLanguageOf, Set.mem_setOf_eq, stdSmn_spec_behavior]

/-- A function `f : ℕ → ℕ` on TM indices is computable (behavior version):
there is a single index `e` such that `stdSmn e x` and `f x` define
extensionally equal behaviors for every `x`. -/
def TMCodingInstance.stdIsComputable (f : ℕ → ℕ) : Prop :=
  ∃ e : ℕ, ∀ (x : ℕ) (w : List Bool),
    TMCodingInstance.stdBehavior (TMCodingInstance.stdSmn e x) w =
    TMCodingInstance.stdBehavior (f x) w

/-- A function `f : ℕ → ℕ` on TM indices is computable (language version):
there is an index `e` such that `stdSmn e x` and `f x` recognize the same
language for every `x`. -/
def TMCodingInstance.stdIsComputableLang (f : ℕ → ℕ) : Prop :=
  ∃ e : ℕ, ∀ x : ℕ,
    TMCodingInstance.stdLanguageOf (TMCodingInstance.stdSmn e x) =
    TMCodingInstance.stdLanguageOf (f x)

/-- Representability: every behavior-computable function `h` has an index `e`
witnessing its computability. (Restatement of the definition.) -/
theorem TMCodingInstance.stdRepresentable :
  ∀ (h : ℕ → ℕ), TMCodingInstance.stdIsComputable h →
    ∃ e : ℕ, ∀ (x : ℕ) (w : List Bool),
      TMCodingInstance.stdBehavior (TMCodingInstance.stdSmn e x) w =
      TMCodingInstance.stdBehavior (h x) w := by sorry
/-- The diagonal s-m-n function `x ↦ stdSmn x x` is computable. -/
theorem TMCodingInstance.stdIsComputable_smn_diag :
  TMCodingInstance.stdIsComputable (fun x => TMCodingInstance.stdSmn x x) := by sorry
/-- Computable functions on indices are closed under composition (behavior version). -/
theorem TMCodingInstance.stdIsComputable_comp :
  ∀ (f g : ℕ → ℕ),
    TMCodingInstance.stdIsComputable f → TMCodingInstance.stdIsComputable g →
    TMCodingInstance.stdIsComputable (f ∘ g) := by sorry
/-- For every index `e`, partial application `x ↦ stdSmn e x` is computable. -/
theorem TMCodingInstance.stdIsComputable_smn_apply :
  ∀ (e : ℕ), TMCodingInstance.stdIsComputable (TMCodingInstance.stdSmn e) := by sorry

/-- Representability for the language version: any `IsComputableLang` function
is witnessed by an index. -/
theorem TMCodingInstance.stdRepresentableLang :
    ∀ (h : ℕ → ℕ), TMCodingInstance.stdIsComputableLang h →
      ∃ e : ℕ, ∀ x : ℕ,
        TMCodingInstance.stdLanguageOf (TMCodingInstance.stdSmn e x) =
        TMCodingInstance.stdLanguageOf (h x) :=
  fun _ hh => hh

/-- The diagonal s-m-n function is computable at the language level. -/
theorem TMCodingInstance.stdIsComputableLang_smn_diag :
  TMCodingInstance.stdIsComputableLang (fun x => TMCodingInstance.stdSmn x x) := by sorry
/-- Composition closure for language-computability. -/
theorem TMCodingInstance.stdIsComputableLang_comp :
  ∀ (f g : ℕ → ℕ),
    TMCodingInstance.stdIsComputableLang f → TMCodingInstance.stdIsComputableLang g →
    TMCodingInstance.stdIsComputableLang (f ∘ g) := by sorry
/-- For every `e`, partial application `x ↦ stdSmn e x` is language-computable. -/
theorem TMCodingInstance.stdIsComputableLang_smn_apply :
  ∀ (e : ℕ), TMCodingInstance.stdIsComputableLang (TMCodingInstance.stdSmn e) := by sorry

/-- For any bound `n`, there exists a TM `M` whose language is different from the
language of every TM whose encoding is shorter than `n`. (Used to construct
"large" TMs in the MIN_TM proof.) -/
theorem TMCodingInstance.stdLanguages_beyond_length :
  ∀ n : ℕ, ∃ M : ℕ, ∀ M' : ℕ,
    (TMCodingInstance.stdEncode M').length < n →
    TMCodingInstance.stdLanguageOf M' ≠ TMCodingInstance.stdLanguageOf M := by sorry
/-- Enumeration-search principle: if the set of encodings of indices satisfying
`P` is Turing-recognizable and `t` selects, for every `M`, a strictly longer
encoded index with `P (t M)`, then `t` is language-computable. -/
theorem TMCodingInstance.stdRecognizable_enumSearch_computable :
  ∀ (P : ℕ → Prop),
    TuringMachine.IsTuringRecognizable
      {s : List Bool | ∃ M : ℕ, TMCodingInstance.stdEncode M = s ∧ P M} →
    ∀ (t : ℕ → ℕ),
      (∀ M, P (t M) ∧ (TMCodingInstance.stdEncode M).length <
        (TMCodingInstance.stdEncode (t M)).length) →
      TMCodingInstance.stdIsComputableLang t := by sorry

namespace RecursionTheorem

/-- The standard `TMCoding` instance for `RecursionTheorem`, packaging the
behavior-level encoding, pairing, s-m-n, and computability operations into the
abstract `TMCoding Bool` structure used by the recursion theorem development. -/
noncomputable def standardTMCoding : TMCoding Bool where
  TMIndex := ℕ
  encode := TMCodingInstance.stdEncode
  behavior := TMCodingInstance.stdBehavior
  decode := TMCodingInstance.stdDecode
  decode_encode := TMCodingInstance.stdDecode_encode
  pair := TMCodingInstance.stdPair
  pair_injective := TMCodingInstance.stdPair_injective
  smn := TMCodingInstance.stdSmn
  smn_spec := TMCodingInstance.stdSmn_spec_behavior
  IsComputable := TMCodingInstance.stdIsComputable
  representable := TMCodingInstance.stdRepresentable
  isComputable_smn_diag := TMCodingInstance.stdIsComputable_smn_diag
  isComputable_comp := TMCodingInstance.stdIsComputable_comp
  isComputable_smn_apply := TMCodingInstance.stdIsComputable_smn_apply

end RecursionTheorem

namespace TuringMachine

/-- The standard `TMCoding` instance for `TuringMachine`, packaging the
language-level data (`languageOf`, language-computability, `enumSearch`, etc.)
into a single coding used by the general TM theory. -/
noncomputable def standardTMCoding : TMCoding Bool where
  TMIndex := ℕ
  encode := TMCodingInstance.stdEncode
  languageOf := TMCodingInstance.stdLanguageOf
  decode := TMCodingInstance.stdDecode
  decode_encode := TMCodingInstance.stdDecode_encode
  pair := TMCodingInstance.stdPair
  pair_injective := TMCodingInstance.stdPair_injective
  smn := TMCodingInstance.stdSmn
  smn_spec := TMCodingInstance.stdSmn_spec
  IsComputable := TMCodingInstance.stdIsComputableLang
  representable := TMCodingInstance.stdRepresentableLang
  isComputable_smn_diag := TMCodingInstance.stdIsComputableLang_smn_diag
  isComputable_comp := TMCodingInstance.stdIsComputableLang_comp
  isComputable_smn_apply := TMCodingInstance.stdIsComputableLang_smn_apply
  languages_beyond_length := TMCodingInstance.stdLanguages_beyond_length
  recognizable_enumSearch_computable := TMCodingInstance.stdRecognizable_enumSearch_computable

end TuringMachine
