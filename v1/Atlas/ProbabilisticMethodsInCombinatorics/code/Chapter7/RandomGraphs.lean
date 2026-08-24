/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

noncomputable section

open Finset BigOperators

namespace RandomGraphs

/-- An (unordered) edge of $K_n$ encoded as an ordered pair $\text{src} < \text{dst}$
of vertices in $\text{Fin } n$. -/
structure Edge (n : ℕ) where
  src : Fin n
  dst : Fin n
  hlt : src < dst
  deriving DecidableEq

/-- A configuration of $G(n, p)$: a Boolean assignment to each edge indicating
whether it is present. -/
abbrev Config (n : ℕ) := Edge n → Bool

/-- An ordered triple of vertices $i < j < k$ in $\text{Fin } n$, used to index
potential triangles in $K_n$. -/
structure Triple (n : ℕ) where
  i : Fin n
  j : Fin n
  k : Fin n
  hij : i < j
  hjk : j < k
  deriving DecidableEq

/-- The edge $\{i, j\}$ of the triple $\{i, j, k\}$. -/
def Triple.eij {n : ℕ} (t : Triple n) : Edge n := ⟨t.i, t.j, t.hij⟩
/-- The edge $\{i, k\}$ of the triple $\{i, j, k\}$. -/
def Triple.eik {n : ℕ} (t : Triple n) : Edge n := ⟨t.i, t.k, lt_trans t.hij t.hjk⟩
/-- The edge $\{j, k\}$ of the triple $\{i, j, k\}$. -/
def Triple.ejk {n : ℕ} (t : Triple n) : Edge n := ⟨t.j, t.k, t.hjk⟩

/-- Pointwise containment of edge configurations: $G \leq H$ iff every edge of $G$ is in $H$. -/
def ConfigLE {n : ℕ} (G H : Config n) : Prop :=
  ∀ e : Edge n, G e = true → H e = true

/-- An event $A$ on configurations is decreasing (monotone-down) if removing edges
preserves membership: $G \in A$ and $H \leq G$ implies $H \in A$. -/
def IsDecreasing {n : ℕ} (A : Set (Config n)) : Prop :=
  ∀ G H : Config n, G ∈ A → ConfigLE H G → H ∈ A

/-- The event that the triangle on the triple $t = \{i, j, k\}$ is absent in $G$. -/
def notTriangleEvent {n : ℕ} (t : Triple n) : Set (Config n) :=
  { G | ¬ (G t.eij = true ∧ G t.eik = true ∧ G t.ejk = true) }

/-- The event that $G$ is triangle-free: no triple $\{i, j, k\}$ spans a triangle. -/
def triangleFreeEvent (n : ℕ) : Set (Config n) :=
  { G | ∀ t : Triple n, G ∈ notTriangleEvent t }

/-- The event "the triangle on $t$ is absent" is decreasing in $G$. -/
theorem notTriangleEvent_isDecreasing {n : ℕ} (t : Triple n) :
    IsDecreasing (notTriangleEvent t) := by
  intro G H hG hHG
  simp only [notTriangleEvent, Set.mem_setOf_eq] at *
  intro ⟨h1, h2, h3⟩
  exact hG ⟨hHG _ h1, hHG _ h2, hHG _ h3⟩

/-- Weight assigned to a configuration $G$ under $G(n, p)$:
$\prod_{e} p^{G_e} (1 - p)^{1 - G_e}$. -/
def bernoulliWeight {n : ℕ} [Fintype (Edge n)] (p : ℝ) (G : Config n) : ℝ :=
  ∏ e : Edge n, if G e = true then p else (1 - p)

/-- Probability of an event $A$ under the $G(n, p)$ Bernoulli product measure:
$\mathbb{P}_p(A) = \sum_{G \in A} \text{bernoulliWeight}(p, G)$. -/
def BProb {n : ℕ} [Fintype (Edge n)] [Fintype (Config n)] (p : ℝ)
    (A : Set (Config n)) [DecidablePred (· ∈ A)] : ℝ :=
  ∑ G ∈ (Finset.univ : Finset (Config n)).filter (· ∈ A), bernoulliWeight p G


/-- Corollary 7.1.6 (decreasing form): For finitely many decreasing events
$A_i$ in $G(n, p)$, $\mathbb{P}_p\!\left(\bigcap_i A_i\right) \geq \prod_i \mathbb{P}_p(A_i)$. -/
theorem harris_inequality_decreasing
    {n : ℕ} [Fintype (Edge n)] [Fintype (Config n)] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {ι : Type*} [Fintype ι] (A : ι → Set (Config n))
    [∀ i, DecidablePred (· ∈ A i)]
    [DecidablePred (· ∈ ⋂ i, A i)]
    (hA : ∀ i, IsDecreasing (A i)) :
    BProb p (⋂ i, A i) ≥ ∏ i : ι, BProb p (A i) := by sorry


/-- The probability that a specific triple of vertices does not form a triangle in
$G(n, p)$ is exactly $1 - p^3$. -/
theorem prob_notTriangle_eq
    {n : ℕ} [Fintype (Edge n)] [Fintype (Config n)] (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (t : Triple n) [DecidablePred (· ∈ notTriangleEvent t)] :
    BProb p (notTriangleEvent t) = 1 - p ^ 3 := by sorry


/-- The number of ordered triples $i < j < k$ in $\text{Fin } n$ equals $\binom{n}{3}$. -/
theorem card_triple_eq_choose (n : ℕ) [Fintype (Triple n)] :
    Fintype.card (Triple n) = Nat.choose n 3 := by sorry

/-- Theorem 7.2.2: For the Erdős-Rényi random graph $G(n, p)$,
$\mathbb{P}(G(n, p) \text{ is triangle-free}) \geq (1 - p^3)^{\binom{n}{3}}$. -/
theorem theorem_7_2_2 (n : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (_hn : 3 ≤ n)
    [Fintype (Edge n)] [Fintype (Config n)] [Fintype (Triple n)]
    [DecidablePred (· ∈ triangleFreeEvent n)]
    [∀ t : Triple n, DecidablePred (· ∈ notTriangleEvent t)]
    [DecidablePred (· ∈ ⋂ t : Triple n, notTriangleEvent t)] :
    BProb p (triangleFreeEvent n) ≥ (1 - p ^ 3) ^ Nat.choose n 3 := by

  have h_eq : triangleFreeEvent n = ⋂ t : Triple n, notTriangleEvent t := by
    ext G
    simp only [triangleFreeEvent, notTriangleEvent, Set.mem_setOf_eq, Set.mem_iInter]

  have h_harris := harris_inequality_decreasing p hp0 hp1
    (fun t : Triple n => notTriangleEvent t)
    (fun t => notTriangleEvent_isDecreasing t)

  have h_each : ∀ t : Triple n, BProb p (notTriangleEvent t) = 1 - p ^ 3 :=
    fun t => prob_notTriangle_eq p hp0 hp1 t

  have h_prod : ∏ t : Triple n, BProb p (notTriangleEvent t) =
      (1 - p ^ 3) ^ Fintype.card (Triple n) := by
    simp only [h_each, prod_const, card_univ]

  have h_card := card_triple_eq_choose n

  have h_ge : BProb p (triangleFreeEvent n) ≥ ∏ t : Triple n, BProb p (notTriangleEvent t) := by
    have : BProb p (triangleFreeEvent n) = BProb p (⋂ t : Triple n, notTriangleEvent t) := by
      congr 1
    rw [this]
    exact h_harris

  linarith [h_ge, h_prod.symm ▸ h_ge, h_card ▸ h_prod]

end RandomGraphs
