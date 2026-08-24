/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Hasse
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.SuccPred

set_option maxHeartbeats 400000

open SimpleGraph Finset BigOperators

namespace Sidorenko

/-- The homomorphism density $t(F,G) = \mathrm{hom}(F,G) / |W|^{|V|}$ of a graph homomorphism
from $F$ into $G$, where $V = V(F)$ and $W = V(G)$. -/
noncomputable def homDensity {V : Type*} {W : Type*}
    (F : SimpleGraph V) (G : SimpleGraph W) : ℝ :=
  (Nat.card (F →g G) : ℝ) / (Nat.card W : ℝ) ^ (Nat.card V)

end Sidorenko


/-- The Sidorenko conjecture (Conjecture 10.3.2): for any bipartite graph $F$ and any graph $G$,
the homomorphism density satisfies $t(F,G) \ge t(K_2,G)^{e(F)}$. -/
theorem sidorenko_conjecture
    {V : Type*} {W : Type*} [Fintype V] [Fintype W]
    (F : SimpleGraph V) (G : SimpleGraph W) [DecidableRel F.Adj] [DecidableRel G.Adj]
    (hF : F.IsBipartite) :
    Sidorenko.homDensity F G ≥
      (Sidorenko.homDensity (⊤ : SimpleGraph (Fin 2)) G) ^ F.edgeFinset.card := by sorry

namespace BlakleyRoy

/-- Decidability of adjacency in the path graph $P_4$ on four vertices. -/
instance pathGraph4_decidableAdj : DecidableRel (SimpleGraph.pathGraph 4).Adj := by
  intro a b
  unfold SimpleGraph.pathGraph
  rw [SimpleGraph.hasse_adj, Fin.covBy_iff, Fin.covBy_iff,
      Nat.covBy_iff_add_one_eq, Nat.covBy_iff_add_one_eq]
  exact instDecidableOr

/-- Case analysis on adjacency in the path graph $P_4$: the only adjacent pairs are
$(0,1), (1,2), (2,3)$ and their reverses. -/
lemma pathGraph4_adj_cases {x y : Fin 4} (h : (pathGraph 4).Adj x y) :
    (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) ∨
    (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 1) ∨
    (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 2) := by
  simp only [pathGraph, hasse_adj, Fin.covBy_iff, Nat.covBy_iff_add_one_eq] at h
  omega

/-- Number of length-3 walks in $G$ counted as $\sum_b \deg(b) \sum_{c \sim b} \deg(c)$, used
to express homomorphism counts from $P_4$ into $G$. -/
noncomputable def walkCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  ∑ b : V, G.degree b * ∑ c ∈ G.neighborFinset b, G.degree c

/-- The number of graph homomorphisms $P_4 \to G$ equals the walk count
$\sum_b \deg(b) \sum_{c \sim b} \deg(c)$. -/
lemma nat_card_hom_eq_walkCount {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Nat.card (pathGraph 4 →g G) = walkCount G := by
  rw [Nat.card_eq_fintype_card, walkCount]
  have equiv : (pathGraph 4 →g G) ≃
      (Σ b : V, Σ c : ↥(G.neighborFinset b),
        ↥(G.neighborFinset b) × ↥(G.neighborFinset c.val)) := {
    toFun := fun φ =>
      have h12 : G.Adj (φ 1) (φ 2) := φ.map_rel' (by
        show (pathGraph 4).Adj 1 2
        rw [pathGraph, hasse_adj, Fin.covBy_iff, Nat.covBy_iff_add_one_eq]; left; norm_num)
      have h01 : G.Adj (φ 0) (φ 1) := φ.map_rel' (by
        show (pathGraph 4).Adj 0 1
        rw [pathGraph, hasse_adj, Fin.covBy_iff, Nat.covBy_iff_add_one_eq]; left; norm_num)
      have h23 : G.Adj (φ 2) (φ 3) := φ.map_rel' (by
        show (pathGraph 4).Adj 2 3
        rw [pathGraph, hasse_adj, Fin.covBy_iff, Nat.covBy_iff_add_one_eq]; left; norm_num)
      ⟨φ 1, ⟨φ 2, (G.mem_neighborFinset (φ 1) (φ 2)).mpr h12⟩,
       ⟨φ 0, (G.mem_neighborFinset (φ 1) (φ 0)).mpr h01.symm⟩,
       ⟨φ 3, (G.mem_neighborFinset (φ 2) (φ 3)).mpr h23⟩⟩
    invFun := fun ⟨b, ⟨c, hc⟩, ⟨a, ha⟩, ⟨d, hd⟩⟩ => {
      toFun := fun i => match i with | 0 => a | 1 => b | 2 => c | 3 => d
      map_rel' := fun {x y} hxy => by
        have ha' : G.Adj a b := ((G.mem_neighborFinset b a).mp ha).symm
        have hc' : G.Adj b c := (G.mem_neighborFinset b c).mp hc
        have hd' : G.Adj c d := (G.mem_neighborFinset c d).mp hd
        rcases pathGraph4_adj_cases hxy with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ha'
        · exact ha'.symm
        · exact hc'
        · exact hc'.symm
        · exact hd'
        · exact hd'.symm
    }
    left_inv := fun φ => by
      ext i
      match i with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
      | ⟨2, _⟩ => rfl
      | ⟨3, _⟩ => rfl
    right_inv := fun ⟨_, ⟨_, _⟩, ⟨_, _⟩, ⟨_, _⟩⟩ => rfl
  }
  rw [Fintype.card_congr equiv, Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro b _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_coe]
  rw [← Finset.mul_sum]
  congr 1
  exact Finset.sum_coe_sort (G.neighborFinset b) (fun c => (G.neighborFinset c).card)

/-- Cauchy-Schwarz-type bound: $(\sum_v \deg v)(\sum_v \deg^2 v) \le |V| \cdot W(G)$ where
$W(G)$ is the walk count. A key step in proving Blakey-Roy for $P_4$. -/
theorem sum_deg_mul_sum_sq_le_card_mul_walkCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, (G.degree v : ℤ)) * (∑ v : V, (G.degree v : ℤ) ^ 2) ≤
      (Fintype.card V : ℤ) * (walkCount G : ℤ) := by sorry

/-- The Blakey-Roy inequality (Theorem 10.3.3, Sidorenko for the three-edge path):
$(2 e(G))^3 \le |V(G)|^2 \cdot \mathrm{hom}(P_4, G)$. -/
theorem blakley_roy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (∑ v : V, (G.degree v : ℤ)) ^ 3 ≤
      (Fintype.card V : ℤ) ^ 2 * (Nat.card (pathGraph 4 →g G) : ℤ) := by
  have hW : (Nat.card (pathGraph 4 →g G) : ℤ) = (walkCount G : ℤ) := by
    exact_mod_cast congrArg Nat.cast (nat_card_hom_eq_walkCount G)
  rw [hW]
  set S := ∑ v : V, (G.degree v : ℤ)
  set Q := ∑ v : V, (G.degree v : ℤ) ^ 2
  set n := (Fintype.card V : ℤ)
  set W := (walkCount G : ℤ)
  have hCS : S ^ 2 ≤ n * Q := sq_sum_le_card_mul_sum_sq
  have hCov : S * Q ≤ n * W := sum_deg_mul_sum_sq_le_card_mul_walkCount G
  have hS : (0 : ℤ) ≤ S := Finset.sum_nonneg (fun v _ => Int.natCast_nonneg _)
  have hn : (0 : ℤ) ≤ n := Int.natCast_nonneg _
  calc S ^ 3 = S * S ^ 2 := by ring
    _ ≤ S * (n * Q) := mul_le_mul_of_nonneg_left hCS hS
    _ = n * (S * Q) := by ring
    _ ≤ n * (n * W) := mul_le_mul_of_nonneg_left hCov hn
    _ = n ^ 2 * W := by ring

end BlakleyRoy
