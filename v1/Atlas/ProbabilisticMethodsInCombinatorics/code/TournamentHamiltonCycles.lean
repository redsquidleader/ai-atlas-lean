/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.LinearAlgebra.Matrix.Permanent

open Finset Real

noncomputable section

namespace TournamentHamiltonCycles

/-- A tournament on $n$ vertices: an irreflexive Boolean edge relation such that exactly one
of $\mathrm{edge}(i, j)$ or $\mathrm{edge}(j, i)$ is true for $i \ne j$. -/
structure Tournament (n : ℕ) where
  edge : Fin n → Fin n → Bool
  irrefl : ∀ i, edge i i = false
  tournament : ∀ i j, i ≠ j → (edge i j = true ↔ edge j i = false)

/-- A permutation $\sigma$ encodes a Hamilton cycle of $T$ iff every directed edge
$i \to \sigma(i)$ exists in $T$ and $\sigma$ is a single $n$-cycle. -/
def IsHamiltonCycle {n : ℕ} (T : Tournament n) (σ : Equiv.Perm (Fin n)) : Prop :=
  (∀ i : Fin n, T.edge i (σ i) = true) ∧ σ.IsCycle ∧ σ.support = Finset.univ

/-- The number of Hamilton cycles of $T$, counted as cycle-permutations on $\mathrm{Fin}\, n$. -/
noncomputable def Tournament.numHamiltonCycles {n : ℕ} (T : Tournament n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
    (∀ i : Fin n, T.edge i (σ i) = true) ∧ σ.IsCycle ∧ σ.support = Finset.univ)).card

/-- Out-degree of vertex $i$ in $T$: the number of $j$ with $T.\mathrm{edge}(i, j)$ true. -/
def Tournament.outDeg {n : ℕ} (T : Tournament n) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j : Fin n => T.edge i j = true)).card
/-- Brégman's theorem on the permanent of a $0/1$-matrix: if row $i$ has exactly $d_i$ ones,
then $\mathrm{perm}(A) \le \prod_i (d_i!)^{1/d_i}$. -/
theorem bregman_theorem
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1)
    (d : Fin n → ℕ)
    (hd : ∀ i, (Finset.univ.filter (fun j => A i j = 1)).card = d i)
    (hd_pos : ∀ i, d i > 0) :
    Matrix.permanent A ≤ ∏ i : Fin n, ((↑(Nat.factorial (d i)) : ℝ) ^ ((1 : ℝ) / ↑(d i))) := by sorry


/-- The sequence $m \mapsto (m!)^{1/m}$ is log-concave: $a_m \cdot a_{m+2} \ge a_{m+1}^2$.
Used in the smoothing step of the proof of Alon's Hamilton-cycle bound. -/
theorem factorial_rpow_log_concave
    (m : ℕ) (hm : m ≥ 1) :
    ((↑(Nat.factorial m) : ℝ) ^ ((1 : ℝ) / ↑m)) *
    ((↑(Nat.factorial (m + 2)) : ℝ) ^ ((1 : ℝ) / ↑(m + 2))) ≥
    ((↑(Nat.factorial (m + 1)) : ℝ) ^ ((1 : ℝ) / ↑(m + 1))) ^ 2 := by sorry


/-- Smoothing + Stirling bound: for positive degrees $d_i$ summing to $\binom{n}{2}$,
$\prod_i (d_i!)^{1/d_i} \le C \sqrt{n} \cdot n! / 2^n$ for some absolute constant $C$. -/
theorem smoothing_stirling_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 3 →
    ∀ d : Fin n → ℕ, (∀ i, d i > 0) → (∑ i : Fin n, d i = n * (n - 1) / 2) →
    ∏ i : Fin n, ((↑(Nat.factorial (d i)) : ℝ) ^ ((1 : ℝ) / ↑(d i))) ≤
      C * Real.sqrt ↑n * (↑(Nat.factorial n) / (2 : ℝ) ^ n) := by sorry


/-- Brégman bound applied to the adjacency matrix of a tournament: the number of Hamilton
cycles is bounded by $\prod_i (\mathrm{outDeg}(i)!)^{1/\mathrm{outDeg}(i)}$. -/
theorem bregman_bound_for_tournament
    {n : ℕ} (T : Tournament n) (hn : n ≥ 3) :
    (T.numHamiltonCycles : ℝ) ≤
      ∏ i : Fin n, ((↑(Nat.factorial (T.outDeg i)) : ℝ) ^ ((1 : ℝ) / ↑(T.outDeg i))) := by sorry


/-- Handshake identity for tournaments: $\sum_i \mathrm{outDeg}(i) = \binom{n}{2}$. -/
theorem tournament_sum_outDeg
    {n : ℕ} (T : Tournament n) :
    ∑ i : Fin n, T.outDeg i = n * (n - 1) / 2 := by sorry


/-- If $T$ contains at least one Hamilton cycle, then every vertex has positive out-degree
(it has at least one outgoing edge along the cycle). -/
theorem outDeg_pos_of_numHamiltonCycles_pos
    {n : ℕ} (T : Tournament n) (h : T.numHamiltonCycles > 0) (i : Fin n) :
    T.outDeg i > 0 := by
  classical
  unfold Tournament.numHamiltonCycles at h
  have hne : (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
    (∀ i : Fin n, T.edge i (σ i) = true) ∧ σ.IsCycle ∧ σ.support = Finset.univ)).Nonempty :=
    Finset.card_pos.mp h
  obtain ⟨σ, hσ⟩ := hne
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
  obtain ⟨hedge, _, _⟩ := hσ
  unfold Tournament.outDeg
  exact Finset.card_pos.mpr ⟨σ i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hedge i⟩⟩

/-- Theorem 10.2.6 (Alon 1990 for cycles). There exists $C > 0$ such that every $n$-vertex
tournament has at most $C \sqrt{n} \cdot n! / 2^n$ Hamilton cycles. -/
theorem tournament_hamilton_cycles_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 3 → ∀ T : Tournament n,
      (T.numHamiltonCycles : ℝ) ≤ C * Real.sqrt ↑n * (↑(Nat.factorial n) / (2 : ℝ) ^ n) := by
  obtain ⟨C, hC_pos, hC_bound⟩ := smoothing_stirling_bound
  refine ⟨C, hC_pos, fun n hn T => ?_⟩
  by_cases h_pos : T.numHamiltonCycles > 0
  · have h_bregman := bregman_bound_for_tournament T hn
    have h_stirling := hC_bound n hn T.outDeg
      (fun i => outDeg_pos_of_numHamiltonCycles_pos T h_pos i)
      (tournament_sum_outDeg T)
    linarith
  · push_neg at h_pos
    have h_zero : T.numHamiltonCycles = 0 := Nat.eq_zero_of_le_zero h_pos
    simp only [h_zero, Nat.cast_zero]
    apply mul_nonneg
    · apply mul_nonneg (le_of_lt hC_pos) (Real.sqrt_nonneg _)
    · apply div_nonneg (Nat.cast_nonneg' _) (by positivity)

end TournamentHamiltonCycles
