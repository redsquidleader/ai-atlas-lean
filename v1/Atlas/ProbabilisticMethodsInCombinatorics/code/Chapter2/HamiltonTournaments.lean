/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option maxHeartbeats 800000

open Finset Fintype

namespace SzeleTournament

/-- The set of unordered edge positions on $n$ labeled vertices, encoded as ordered
pairs $(i, j)$ with $i < j$. -/
abbrev EdgeSet (n : ℕ) := { p : Fin n × Fin n // p.1 < p.2 }

/-- A tournament on $n$ vertices: an orientation assigning a Boolean direction to each
unordered edge in `EdgeSet n`. -/
abbrev Tournament (n : ℕ) := EdgeSet n → Bool

/-- The directed edge from $i$ to $j$ in tournament $T$: true if $T$ orients the edge
in the direction $i \to j$, false otherwise (including the diagonal). -/
def tournamentEdge {n : ℕ} (T : Tournament n) (i j : Fin n) : Bool :=
  if h : i < j then T ⟨(i, j), h⟩
  else if h2 : j < i then !T ⟨(j, i), h2⟩
  else false

/-- A permutation $\sigma$ of $\mathrm{Fin}\,n$ is a Hamilton path in tournament $T$
if every consecutive pair $(\sigma(i), \sigma(i+1))$ is a directed edge of $T$. -/
def IsHamiltonPath {n : ℕ} (T : Tournament n) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, (h : i.val + 1 < n) →
    tournamentEdge T (σ i) (σ ⟨i.val + 1, h⟩) = true

/-- Decidability instance for `IsHamiltonPath`, used for counting. -/
instance instDecIsHP {n : ℕ} (T : Tournament n) (σ : Equiv.Perm (Fin n)) :
    Decidable (IsHamiltonPath T σ) := by
  unfold IsHamiltonPath; exact inferInstance

/-- The number of Hamilton paths in a tournament $T$, defined as the cardinality of the
set of permutations $\sigma$ for which `IsHamiltonPath T σ` holds. -/
noncomputable def numHamiltonPaths {n : ℕ} (T : Tournament n) : ℕ :=
  (Finset.univ.filter (IsHamiltonPath T)).card

/-- For a fixed permutation $\sigma$, the number of tournaments in which $\sigma$ is a
Hamilton path equals $2^{|E| - (n-1)}$, since the $n-1$ consecutive edges along $\sigma$
must be oriented in a unique direction while the remaining edges are free. -/
theorem card_fiber_hp {n : ℕ} (σ : Equiv.Perm (Fin n)) (hn : n ≥ 1) :
    (Finset.univ.filter (fun T : Tournament n => IsHamiltonPath T σ)).card =
    2 ^ (Fintype.card (EdgeSet n) - (n - 1)) := by sorry

/-- For $n \geq 1$, the edge count of `EdgeSet n` is at least $n - 1$,
exhibited by the path $(0,1), (1,2), \dots, (n-2, n-1)$. -/
lemma n_sub_one_le_card_edgeset (n : ℕ) (hn : n ≥ 1) :
    n - 1 ≤ Fintype.card (EdgeSet n) := by
  have hinj : Function.Injective (fun k : Fin (n - 1) =>
    (⟨(⟨k.val, by omega⟩, ⟨k.val + 1, by omega⟩), by
      exact Fin.mk_lt_mk.mpr (by omega)⟩ : EdgeSet n)) := by
    intro a b hab
    have h := congrArg (fun x => (x : EdgeSet n).val.1.val) hab
    exact Fin.ext h
  have := Fintype.card_le_of_injective _ hinj
  rwa [Fintype.card_fin] at this

/-- Total count via double counting: summing the number of Hamilton paths over all
tournaments equals $n! \cdot 2^{|E| - (n-1)}$, because for each of the $n!$ permutations
exactly $2^{|E| - (n-1)}$ tournaments admit it as a Hamilton path. -/
lemma total_sum_hp (n : ℕ) (hn : n ≥ 1) :
    ∑ T : Tournament n, numHamiltonPaths T =
    n.factorial * 2 ^ (Fintype.card (EdgeSet n) - (n - 1)) := by
  classical
  have h1 : ∑ T : Tournament n, numHamiltonPaths T =
      ∑ T : Tournament n, ∑ σ : Equiv.Perm (Fin n),
        if IsHamiltonPath T σ then 1 else 0 := by
    congr 1; ext T; simp only [numHamiltonPaths]; rw [Finset.card_filter]
  rw [h1, Finset.sum_comm]
  have h2 : ∀ σ : Equiv.Perm (Fin n),
      ∑ T : Tournament n, (if IsHamiltonPath T σ then 1 else 0) =
      (2 : ℕ) ^ (Fintype.card (EdgeSet n) - (n - 1)) := by
    intro σ; rw [← Finset.card_filter]; exact card_fiber_hp σ hn
  simp_rw [h2, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, smul_eq_mul]

/-- **Szele's theorem (Theorem 2.1.2, 1943).** For every $n \geq 1$ there exists a
tournament on $n$ vertices with at least $n! / 2^{n-1}$ Hamilton paths. -/
theorem szele_hamilton_paths (n : ℕ) (hn : n ≥ 1) :
    ∃ T : Tournament n, n.factorial ≤ numHamiltonPaths T * 2 ^ (n - 1) := by
  classical
  by_contra h_all
  push_neg at h_all

  have h_sum_bound : ∑ T : Tournament n, numHamiltonPaths T * 2 ^ (n - 1) <
      Fintype.card (Tournament n) * n.factorial := by
    calc ∑ T : Tournament n, numHamiltonPaths T * 2 ^ (n - 1)
        < ∑ _T : Tournament n, n.factorial := by
          apply Finset.sum_lt_sum
          · intro T _; exact Nat.le_of_lt (h_all T)
          · exact ⟨fun _ => false, Finset.mem_univ _, h_all _⟩
      _ = Fintype.card (Tournament n) * n.factorial := by
          simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]

  have h_factor : ∑ T : Tournament n, numHamiltonPaths T * 2 ^ (n - 1) =
      (∑ T : Tournament n, numHamiltonPaths T) * 2 ^ (n - 1) := by
    rw [← Finset.sum_mul]

  have h_total := total_sum_hp n hn

  have h_card_tourn : Fintype.card (Tournament n) = 2 ^ Fintype.card (EdgeSet n) := by
    simp [Fintype.card_bool]

  have hm := n_sub_one_le_card_edgeset n hn

  have h_eq : (∑ T : Tournament n, numHamiltonPaths T) * 2 ^ (n - 1) =
      Fintype.card (Tournament n) * n.factorial := by
    rw [h_total, h_card_tourn, Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel hm, Nat.mul_comm]

  exact absurd (h_factor ▸ h_eq ▸ h_sum_bound) (Nat.lt_irrefl _)

end SzeleTournament
