/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Lattice.Fold
set_option maxHeartbeats 800000

open Finset Real

namespace HypergraphContainers

/-- A 3-uniform hypergraph on a finite vertex type $V$: a finite family of 3-element
subsets of $V$. -/
structure ThreeUniformHypergraph (V : Type*) [Fintype V] [DecidableEq V] where
  edges : Finset (Finset V)
  edges_card : ∀ e ∈ edges, e.card = 3

namespace ThreeUniformHypergraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of vertices of a 3-uniform hypergraph, equal to the cardinality of $V$. -/
noncomputable def vertexCount (_ : ThreeUniformHypergraph V) : ℕ := Fintype.card V

/-- The degree of a vertex $v$ in a 3-uniform hypergraph $H$: the number of edges of $H$
that contain $v$. -/
noncomputable def vertexDegree (H : ThreeUniformHypergraph V) (v : V) : ℕ :=
  (H.edges.filter (fun e => v ∈ e)).card

/-- The average vertex degree of a 3-uniform hypergraph, $\bar d(H) = 3|E(H)|/|V|$. -/
noncomputable def averageDegree (H : ThreeUniformHypergraph V) : ℝ :=
  (3 * H.edges.card : ℝ) / (Fintype.card V : ℝ)

/-- The maximum vertex degree $\Delta_1(H)$ of a 3-uniform hypergraph. -/
noncomputable def maxDegree (H : ThreeUniformHypergraph V) : ℕ :=
  Finset.univ.sup (fun v => H.vertexDegree v)

/-- The pair codegree $d_H(u,v)$: the number of edges of $H$ containing both $u$ and $v$. -/
noncomputable def pairCodegree (H : ThreeUniformHypergraph V) (u v : V) : ℕ :=
  (H.edges.filter (fun e => u ∈ e ∧ v ∈ e)).card

/-- The maximum pair codegree $\Delta_2(H) = \max_{u \neq v} d_H(u, v)$. -/
noncomputable def maxPairCodegree (H : ThreeUniformHypergraph V) : ℕ :=
  Finset.univ.sup (fun u => Finset.univ.sup (fun v =>
    if u ≠ v then H.pairCodegree u v else 0))

/-- A set $I \subseteq V$ is independent in a 3-uniform hypergraph $H$ if no edge of $H$
is contained in $I$. -/
def IsIndependentSet (H : ThreeUniformHypergraph V) (I : Finset V) : Prop :=
  ∀ e ∈ H.edges, ¬(e ⊆ I)

end ThreeUniformHypergraph

/-- $\sum_{i=0}^{k} \binom{n}{i}$, an upper bound for the number of subsets of an
$n$-element set of size at most $k$. -/
def Nat.chooseLe (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), n.choose i

open ThreeUniformHypergraph

/-- **Theorem 11.3.1 (Container theorem for 3-uniform hypergraphs).** For every $c > 0$
there exists $\delta > 0$ such that for every 3-uniform hypergraph $H$ with average degree
$d \geq \delta^{-1}$, maximum vertex degree $\Delta_1 \leq c d$ and maximum pair codegree
$\Delta_2 \leq c \sqrt{d}$, there is a family $\mathcal{C}$ of containers with
* $|\mathcal{C}| \leq \sum_{i \leq n/\sqrt{d}} \binom{n}{i}$;
* every independent set $I$ of $H$ is contained in some $S \in \mathcal{C}$;
* every container satisfies $|S| \leq (1 - \delta) n$. -/
theorem container_theorem_three_uniform (c : ℝ) (hc : c > 0) :
    ∃ δ : ℝ, δ > 0 ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (H : ThreeUniformHypergraph V)
        (d : ℝ) (hd_eq : H.averageDegree = d) (hd_large : d ≥ δ⁻¹)
        (hΔ₁ : (H.maxDegree : ℝ) ≤ c * d)
        (hΔ₂ : (H.maxPairCodegree : ℝ) ≤ c * Real.sqrt d),
        ∃ C : Finset (Finset V),
          (C.card ≤ Nat.chooseLe (Fintype.card V) ⌊(Fintype.card V : ℝ) / Real.sqrt d⌋₊) ∧
          (∀ I : Finset V, H.IsIndependentSet I → ∃ S ∈ C, I ⊆ S) ∧
          (∀ S ∈ C, (S.card : ℝ) ≤ (1 - δ) * (Fintype.card V : ℝ)) := by sorry

end HypergraphContainers
