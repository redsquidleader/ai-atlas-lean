/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.Finset.Powerset

set_option maxHeartbeats 400000

open Set Topology

namespace HypergraphColoring

variable {V : Type*}

/-- Set of 2-colorings of `V` that properly color every hyperedge `e ∈ edges` contained in the
finite vertex set `X` (no edge entirely monochromatic). Used in the compactness step of
Theorem 6.2.4. -/
def goodColorings624 (edges : Set (Finset V)) (X : Finset V) : Set (V → Bool) :=
  {c | ∀ e ∈ edges, (↑e : Set V) ⊆ ↑X →
    ¬(∀ v ∈ e, c v = true) ∧ ¬(∀ v ∈ e, c v = false)}

/-- For a finite edge `e` and a Boolean `b`, the set of colorings that are NOT identically `b`
on `e` is closed in the product (discrete) topology on `V → Bool`. -/
lemma isClosed_not_all_eq624 (e : Finset V) (b : Bool) :
    IsClosed {c : V → Bool | ¬(∀ v ∈ e, c v = b)} := by
  have heq : {c : V → Bool | ¬(∀ v ∈ e, c v = b)} = (Set.pi (↑e) (fun _ => {b}))ᶜ := by
    ext c; simp [Set.mem_pi]
  rw [heq]
  exact (isOpen_set_pi e.finite_toSet (fun _ _ => @isOpen_discrete Bool _ _ {b})).isClosed_compl

/-- The set `goodColorings624 edges X` of proper 2-colorings is closed in `V → Bool`. -/
lemma isClosed_goodColorings624 (edges : Set (Finset V)) (X : Finset V) :
    IsClosed (goodColorings624 edges X) := by
  have heq : goodColorings624 edges X =
      ⋂ (e : Finset V) (_ : e ∈ edges) (_ : (↑e : Set V) ⊆ ↑X),
        ({c : V → Bool | ¬(∀ v ∈ e, c v = true)} ∩
         {c | ¬(∀ v ∈ e, c v = false)}) := by
    ext c; simp only [goodColorings624, mem_setOf_eq, mem_iInter, mem_inter_iff]
  rw [heq]
  apply isClosed_iInter; intro e
  apply isClosed_iInter; intro _
  apply isClosed_iInter; intro _
  exact IsClosed.inter (isClosed_not_all_eq624 e true) (isClosed_not_all_eq624 e false)

/-- Antitonicity: enlarging the vertex set `X` shrinks the set of good colorings, since more
edges must be properly colored. -/
lemma goodColorings624_anti (edges : Set (Finset V)) {X Y : Finset V} (hYX : Y ⊆ X) :
    goodColorings624 edges X ⊆ goodColorings624 edges Y := by
  intro c hc e he hes
  exact hc e he (hes.trans (Finset.coe_subset.mpr hYX))

/-- Finite-vertex version of Corollary 6.1.10 applied to hypergraph 2-coloring: if every edge
has size $\ge 3$ and the LLL weight bound $\sum_{f \in S} 2^{-|f|} \le 1/8$ holds for every
finite collection of intersecting neighboring edges, then there is a proper 2-coloring of every
finite vertex set `X`. -/
theorem lll_cor_6_1_10_finite
    (V : Type*) (edges : Set (Finset V)) (X : Finset V)
    (hedge_size : ∀ e ∈ edges, 3 ≤ e.card)
    (hedge_weight : ∀ e ∈ edges,
      ∀ (S : Finset (Finset V)),
        (↑S : Set (Finset V)) ⊆ {f ∈ edges | f ≠ e ∧ (↑e ∩ ↑f : Set V).Nonempty} →
        ∑ f ∈ S, (2 : ℝ)⁻¹ ^ f.card ≤ 1 / 8) :
    (goodColorings624 edges X).Nonempty := by sorry

/-- Theorem 6.2.4: a (possibly non-uniform, possibly infinite) hypergraph in which every edge
has size at least $3$ and satisfies the LLL weight bound $\sum_{f} 2^{-|f|} \le 1/8$ over its
intersecting neighbors admits a proper 2-coloring. Proven by combining `lll_cor_6_1_10_finite`
on each finite vertex restriction with a compactness argument. -/
theorem hypergraph_two_coloring_6_2_4
    [DecidableEq V] (edges : Set (Finset V))
    (hedge_size : ∀ e ∈ edges, 3 ≤ e.card)
    (hedge_weight : ∀ e ∈ edges,
      ∀ (S : Finset (Finset V)),
        (↑S : Set (Finset V)) ⊆ {f ∈ edges | f ≠ e ∧ (↑e ∩ ↑f : Set V).Nonempty} →
        ∑ f ∈ S, (2 : ℝ)⁻¹ ^ f.card ≤ 1 / 8) :
    ∃ c : V → Bool, ∀ e ∈ edges,
      ¬(∀ v ∈ e, c v = true) ∧ ¬(∀ v ∈ e, c v = false) := by
  haveI : Nonempty (Finset V) := ⟨∅⟩

  have hne : ∀ X : Finset V, (goodColorings624 edges X).Nonempty :=
    fun X => lll_cor_6_1_10_finite V edges X hedge_size hedge_weight

  have hcl : ∀ X : Finset V, IsClosed (goodColorings624 edges X) :=
    isClosed_goodColorings624 edges

  have hdir : Directed (· ⊇ ·) (goodColorings624 edges) := by
    intro X Y
    refine ⟨X ∪ Y, ?_, ?_⟩
    · exact goodColorings624_anti edges Finset.subset_union_left
    · exact goodColorings624_anti edges Finset.subset_union_right

  have hcpt : ∀ X : Finset V, IsCompact (goodColorings624 edges X) := by
    intro X
    haveI : CompactSpace (V → Bool) := Pi.compactSpace
    exact (hcl X).isCompact

  have hinter := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    (goodColorings624 edges) hdir hne hcpt hcl

  obtain ⟨c, hc⟩ := hinter
  refine ⟨c, fun e he => ?_⟩

  have hmem : c ∈ goodColorings624 edges e := mem_iInter.mp hc e
  exact hmem e he (Subset.refl _)

end HypergraphColoring
