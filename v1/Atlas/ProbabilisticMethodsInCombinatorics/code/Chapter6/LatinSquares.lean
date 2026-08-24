/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.SpecialFunctions.Exp
set_option maxHeartbeats 400000

open Function

namespace LatinSquares

/-- An $n \times n$ array $L : \text{Fin}\ n \to \text{Fin}\ n \to \text{Fin}\ n$ is a Latin square if every row and every column is a permutation of $\{0,1,\dots,n-1\}$, equivalently if every row map and every column map is injective. -/
structure IsLatinSquare {n : ℕ} (L : Fin n → Fin n → Fin n) : Prop where
  row_injective : ∀ i : Fin n, Injective (L i)
  col_injective : ∀ j : Fin n, Injective (fun i => L i j)

/-- An $n \times n$ array $L$ has a Latin transversal if there exists a permutation $\sigma$ of $\text{Fin}\ n$ such that the diagonal entries $L_{i,\sigma(i)}$ are all distinct. -/
def HasLatinTransversal {n : ℕ} (L : Fin n → Fin n → Fin n) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), Injective (fun i => L i (σ i))

end LatinSquares

open LatinSquares


/-- Ryser's conjecture: every $n \times n$ Latin square with $n$ odd has a Latin transversal. -/
theorem ryser_conjecture
  {n : ℕ} (hn : Odd n) (L : Fin n → Fin n → Fin n) (hL : IsLatinSquare L) :
  HasLatinTransversal L := by sorry

namespace LatinSquares

/-- The set of symbols appearing on the diagonal selected by the permutation $\sigma$, i.e. $\{L_{i,\sigma(i)} : i \in \text{Fin}\ n\}$. -/
noncomputable def transversalSymbols {n : ℕ} (L : Fin n → Fin n → Fin n)
    (σ : Equiv.Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.image (fun i => L i (σ i))

end LatinSquares

open LatinSquares in


/-- Ryser–Brualdi–Stein conjecture: every $n \times n$ Latin square with $n$ even admits a permutation $\sigma$ such that the diagonal $\{L_{i,\sigma(i)}\}$ contains at least $n-1$ distinct symbols (a near-transversal). -/
theorem ryser_brualdi_stein_conjecture
    {n : ℕ} {L : Fin n → Fin n → Fin n}
    (hL : IsLatinSquare L) (hn : Even n) :
    ∃ σ : Equiv.Perm (Fin n), n - 1 ≤ (transversalSymbols L σ).card := by sorry

namespace ErdosSpencer

open Finset Real

/-- The number of cells of the array $L$ whose entry equals the symbol $c$, i.e. $|\{(i,j) : L_{i,j} = c\}|$. -/
def symbolCount {n : ℕ} {α : Type*} [DecidableEq α]
    (L : Fin n → Fin n → α) (c : α) : ℕ :=
  ((Finset.univ ×ˢ Finset.univ).filter (fun p : Fin n × Fin n => L p.1 p.2 = c)).card

/-- Generalised notion of a Latin transversal for an array with entries in an arbitrary type $\alpha$: a permutation $\sigma$ such that the selected diagonal entries $L_{i,\sigma(i)}$ are all distinct. -/
def HasLatinTransversalGen {n : ℕ} {α : Type*} (L : Fin n → Fin n → α) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), Injective (fun i => L i (σ i))

/-- The finite set of permutations $\sigma$ that yield a Latin transversal of $L$: distinct rows pick distinct symbols. -/
def goodPerms {n : ℕ} {α : Type*} [DecidableEq α] (L : Fin n → Fin n → α) :
    Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun σ => ∀ i₁ i₂ : Fin n, i₁ ≠ i₂ → L i₁ (σ i₁) ≠ L i₂ (σ i₂))

/-- Membership in `goodPerms L` is equivalent to the diagonal map $i \mapsto L_{i,\sigma(i)}$ being injective. -/
lemma mem_goodPerms_iff {n : ℕ} {α : Type*} [DecidableEq α]
    (L : Fin n → Fin n → α) (σ : Equiv.Perm (Fin n)) :
    σ ∈ goodPerms L ↔ Injective (fun i => L i (σ i)) := by
  simp only [goodPerms, mem_filter, mem_univ, true_and]
  exact ⟨fun h a b hab => by_contra (fun hne => h a b hne hab),
         fun hinj i₁ i₂ hne heq => hne (hinj heq)⟩

end ErdosSpencer

/-- Lopsided LLL application underlying Erdős–Spencer: for $n \ge 2$, if every symbol of the $n \times n$ array $L$ appears at most $n/(4e)$ times, then the set of permutations producing a Latin transversal is nonempty. -/
theorem ErdosSpencer.lll_latin_transversal_nonempty
    {n : ℕ} {α : Type*} [DecidableEq α]
    (hn : 2 ≤ n) (L : Fin n → Fin n → α)
    (hL : ∀ c : α, (ErdosSpencer.symbolCount L c : ℝ) ≤ ↑n / (4 * Real.exp 1)) :
    (ErdosSpencer.goodPerms L).Nonempty := by sorry

namespace ErdosSpencer

open Real

/-- Erdős–Spencer 1991 (Theorem 6.5.11): if $L$ is an $n \times n$ array (with $n \ge 1$) in which every symbol appears at most $n/(4e)$ times, then $L$ has a Latin transversal. -/
theorem erdos_spencer_latin_transversal {n : ℕ} {α : Type*} [DecidableEq α]
    (hn : 0 < n) (L : Fin n → Fin n → α)
    (hL : ∀ c : α, (symbolCount L c : ℝ) ≤ ↑n / (4 * rexp 1)) :
    HasLatinTransversalGen L := by
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · have h1 : n = 1 := by omega
    subst h1
    exact ⟨Equiv.refl _, fun {a b} _ => Fin.ext (by omega)⟩
  · obtain ⟨σ, hσ⟩ := lll_latin_transversal_nonempty hn2 L hL
    exact ⟨σ, (mem_goodPerms_iff L σ).mp hσ⟩

end ErdosSpencer
