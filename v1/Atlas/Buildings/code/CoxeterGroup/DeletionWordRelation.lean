/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.Buildings.code.CoxeterGroup.DeletionInjectivityHelpers
import Atlas.Buildings.code.CoxeterGroup.UnluckyCase
import Atlas.Buildings.code.CoxeterGroup.CyclicRotation
import Mathlib.GroupTheory.Coxeter.Basic

open CoxeterSystemFromDeletion

namespace CoxeterSystemFromDeletion

variable {B : Type*} {W : Type*} [Group W]

/-- A family of involutions $\mathtt{gen}$ with $\mathtt{gen}\,s \cdot
\mathtt{gen}\,t \ne 1$ for $s \ne t$ is necessarily injective. -/
lemma gen_injective_of_involution_ne
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1) :
    Function.Injective gen := by
  intro s t hst
  by_contra h
  have := hgen_ne s t h
  rw [hst, hgen_inv] at this
  exact this rfl

/-- Cyclic rotation dichotomy: for a length-$2m$ word with trivial product
($m \ge 2$), either there is a strictly shorter word with the same product in
both $W$ and the abstract Coxeter group (the "lucky" case), or the cyclic
generators satisfy the $L$-type identity governing alternation. -/
theorem cycling_rotation_gives_lucky_or_Ltype
    {B : Type*} {W : Type*} [Group W]
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1)
    (hDel : SatisfiesDeletionConditionGen gen)
    (word : List B) (hw : (word.map gen).prod = 1)
    (m : ℕ) (hlen : word.length = 2 * m) (hm : m ≥ 2) :
    let M := deletionCoxeterMatrix gen hgen_inv hgen_ne

    (∃ (word' : List B), word'.length < word.length ∧
      (word.map gen).prod = (word'.map gen).prod ∧
      (word.map M.simple).prod = (word'.map M.simple).prod) ∨

    (∀ k,
      consecProd (wordCyclicGen gen word (2 * m) hlen (by omega)) k m =
      wordCyclicGen gen word (2 * m) hlen (by omega) (k + 2) *
      wordCyclicGen gen word (2 * m) hlen (by omega) (k + 1) *
      consecProd (wordCyclicGen gen word (2 * m) hlen (by omega)) (k + 2) (m - 2)) := by sorry

/-- Cleaner version of the cyclic dichotomy: either we can shorten the word in
the relevant senses, or the word is two-step periodic, i.e. of alternating form
$s t s t \cdots$. -/
theorem cycling_dichotomy
    {B : Type*} {W : Type*} [Group W]
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1)
    (hDel : SatisfiesDeletionConditionGen gen)
    (word : List B) (hw : (word.map gen).prod = 1)
    (m : ℕ) (hlen : word.length = 2 * m) (hm : m ≥ 2) :
    let M := deletionCoxeterMatrix gen hgen_inv hgen_ne

    (∃ (word' : List B), word'.length < word.length ∧
      (word.map gen).prod = (word'.map gen).prod ∧
      (word.map M.simple).prod = (word'.map M.simple).prod) ∨

    (∀ (k : ℕ) (hk : k + 2 < word.length),
      word.get ⟨k, by omega⟩ = word.get ⟨k + 2, hk⟩) := by
  intro M

  rcases cycling_rotation_gives_lucky_or_Ltype gen hgen_inv hgen_ne hDel word hw m hlen hm with
    hlucky | hLtype
  ·
    exact Or.inl hlucky
  ·
    right

    have hgen_alt := cycling_forces_alternating gen word m hlen hm hLtype

    have hinj := gen_injective_of_involution_ne gen hgen_inv hgen_ne
    intro k hk
    exact hinj (hgen_alt k hk)

/-- If a word of length $2m$ is two-step periodic with first two letters $s, t$,
then its image-product under any $f : B \to G$ equals
$(f(s) \cdot f(t))^m$. -/
lemma alternating_word_prod_eq_pow {G : Type*} [Group G]
    (f : B → G) (s t : B) :
    ∀ (m : ℕ) (word : List B) (_ : word.length = 2 * m) (_ : m ≥ 1)
    (_ : ∀ (k : ℕ) (hk : k + 2 < word.length),
      word.get ⟨k, by omega⟩ = word.get ⟨k + 2, hk⟩)
    (_ : word.get ⟨0, by omega⟩ = s)
    (_ : word.get ⟨1, by omega⟩ = t),
    (word.map f).prod = (f s * f t) ^ m := by
  intro m
  induction m using Nat.strongRecOn with
  | ind n ih =>
    intro word hlen hm halt hs ht
    obtain ⟨a, b, rest, rfl⟩ : ∃ a b rest, word = a :: b :: rest := by
      match word, show word.length ≥ 2 by omega with
      | a :: b :: rest, _ => exact ⟨a, b, rest, rfl⟩
    have ha : a = s := by simpa using hs
    have hb : b = t := by simpa using ht
    subst ha; subst hb
    simp only [List.map_cons, List.prod_cons]
    by_cases hn1 : n = 1
    · subst hn1
      simp only [List.length_cons] at hlen
      have : rest = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; simp [pow_one]
    · have hrest_len : rest.length = 2 * (n - 1) := by
        simp only [List.length_cons] at hlen; omega
      have hge : n - 1 ≥ 1 := by omega
      have hrest0 : rest.get ⟨0, by omega⟩ = a := by
        have := halt 0 (by simp only [List.length_cons]; omega)
        simpa using this.symm
      have hrest1 : rest.get ⟨1, by omega⟩ = b := by
        have := halt 1 (by simp only [List.length_cons]; omega)
        simpa using this.symm
      have halt_rest : ∀ (k : ℕ) (hk : k + 2 < rest.length),
          rest.get ⟨k, by omega⟩ = rest.get ⟨k + 2, hk⟩ := by
        intro k hk
        have := halt (k + 2) (by simp only [List.length_cons]; omega)
        simp only [List.get_cons_succ] at this; exact this
      have ih_rest := ih (n - 1) (by omega) rest hrest_len hge halt_rest hrest0 hrest1
      rw [ih_rest]
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hm]

/-- An alternating word with trivial product under $\mathtt{gen}$ also has
trivial product under the canonical simple-generator map of the deletion
Coxeter matrix. -/
lemma alternating_word_trivial_in_coxeter
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1)
    (word : List B) (hw : (word.map gen).prod = 1)
    (m : ℕ) (hlen : word.length = 2 * m) (hm : m ≥ 1)
    (halt : ∀ (k : ℕ) (hk : k + 2 < word.length),
      word.get ⟨k, by omega⟩ = word.get ⟨k + 2, hk⟩) :
    let M := deletionCoxeterMatrix gen hgen_inv hgen_ne
    (word.map M.simple).prod = 1 := by
  intro M
  set s := word.get ⟨0, by omega⟩
  set t := word.get ⟨1, by omega⟩

  have hgen_prod := alternating_word_prod_eq_pow gen s t m word hlen hm halt rfl rfl

  rw [hgen_prod] at hw

  have hcox := alternating_word_maps_to_one gen hgen_inv hgen_ne s t m hw

  have hsimp_prod := alternating_word_prod_eq_pow M.simple s t m word hlen hm halt rfl rfl
  rw [hsimp_prod]
  exact hcox

/-- Key theorem: every word relation in $W$ already holds in the abstract
Coxeter group generated by $B$ with the deletion Coxeter matrix. This is what
allows the canonical homomorphism to be injective. -/
theorem word_relation_trivial_in_coxeter_group
    {B : Type*} {W : Type*} [Group W]
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1)
    (hDel : SatisfiesDeletionConditionGen gen) :
    let M := deletionCoxeterMatrix gen hgen_inv hgen_ne
    ∀ (word : List B), (word.map gen).prod = 1 → (word.map M.simple).prod = 1 := by
  intro M

  suffices key : ∀ (n : ℕ) (word : List B) (_ : word.length = n),
      (word.map gen).prod = 1 → (word.map M.simple).prod = 1 by
    intro word hw
    exact key word.length word rfl hw
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro word hlen hw

    have heven := deletion_relation_even_length gen hgen_inv hDel word hw
    obtain ⟨m, hm_eq⟩ := heven
    rw [hlen] at hm_eq

    by_cases hm0 : m = 0
    ·
      subst hm0; simp at hm_eq
      have : word = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst this; simp
    · by_cases hm1 : m = 1
      ·
        subst hm1
        have hlen2 : word.length = 2 := by omega
        match word, hlen2 with
        | [a, b], _ =>
          simp only [List.map, List.prod_cons, List.prod_nil, mul_one] at hw ⊢
          by_cases hab : a = b
          · subst hab

            have h := M.toCoxeterSystem.simple_mul_simple_pow a a
            simp only [CoxeterMatrix.diagonal] at h
            simpa using h
          · exact absurd hw (hgen_ne a b hab)
      ·
        have hm_ge2 : m ≥ 2 := by omega
        have hlen_eq : word.length = 2 * m := by omega
        rcases cycling_dichotomy gen hgen_inv hgen_ne hDel word hw m hlen_eq hm_ge2 with
          ⟨word', hlt, htransfer_gen, htransfer_simple⟩ | halt
        ·
          rw [htransfer_gen] at hw
          have ih_word' := ih word'.length (by omega) word' rfl hw
          rw [htransfer_simple, ih_word']
        ·
          exact alternating_word_trivial_in_coxeter gen hgen_inv hgen_ne
            word hw m hlen_eq (by omega) halt

end CoxeterSystemFromDeletion
