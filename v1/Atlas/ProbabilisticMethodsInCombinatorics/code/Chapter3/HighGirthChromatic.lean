/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

open SimpleGraph Finset

namespace HighGirthChromatic

/-- If every short cycle of $G$ (length $\leq g$) passes through some vertex of $S$, then
the subgraph induced on $V \setminus S$ has girth strictly greater than $g$. -/
lemma induce_compl_no_short_cycles {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (S : Finset (Fin n)) (g : ℕ)
    (hS : ∀ (v : Fin n) (w : G.Walk v v), w.IsCycle → w.length ≤ g →
      ∃ u, u ∈ S ∧ u ∈ w.support.toFinset) :
    ∀ (v : ↑(↑(Finset.univ \ S) : Set (Fin n)))
      (w : (G.induce (↑(Finset.univ \ S) : Set (Fin n))).Walk v v),
      w.IsCycle → g < w.length := by
  set T : Set (Fin n) := ↑(Finset.univ \ S)
  set ι := Embedding.induce (G := G) T
  intro v w hw
  by_contra hle
  push Not at hle
  have hw_mapped : (w.map ι.toHom).IsCycle := hw.map ι.injective
  have hlen : (w.map ι.toHom).length = w.length := Walk.length_map _ _
  obtain ⟨u, hu_S, hu_supp⟩ := hS _ _ hw_mapped (hlen ▸ hle)
  have huT : u ∈ T := by
    have hx : u ∈ (w.map ι.toHom).support := List.mem_toFinset.mp hu_supp
    rw [Walk.support_map] at hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    have hι_eq : ι.toHom y = (y : Fin n) := by
      show ι y = (y : Fin n)
      simp only [ι, Embedding.comap, RelEmbedding.coe_mk, Function.Embedding.subtype_apply]
    rw [hι_eq]
    exact y.prop
  have hunotS : u ∉ S := by
    simp only [T, Finset.coe_sdiff, Finset.coe_univ, Set.mem_diff, Set.mem_univ,
               true_and, Finset.mem_coe] at huT
    exact huT
  exact hunotS hu_S

/-- The probabilistic step of Erdős' construction: for every $k$ and every $g > 2$, there
is a finite graph $G$ that is not $k$-colorable and has girth greater than $g$. -/
theorem erdos_probabilistic_argument (k g : ℕ) (hg : 2 < g) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      ¬G.Colorable k ∧ g < G.girth := by sorry

/-- For any $k$ and $g$, there exists a finite graph that is not $k$-colorable and whose
girth exceeds $g$. The small-girth case ($g \leq 2$) is handled by a complete graph; the
generic case reduces to `erdos_probabilistic_argument`. -/
theorem exists_not_colorable_high_girth (k g : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V) (_ : DecidableRel G.Adj),
      ¬G.Colorable k ∧ g < G.girth := by
  classical
  by_cases hg : g ≤ 2
  ·
    refine ⟨Fin (k + 3), inferInstance, ⊤, inferInstance, ?_, ?_⟩
    · rw [← chromaticNumber_le_iff_colorable]
      simp only [chromaticNumber_top, Fintype.card_fin, not_le]
      exact_mod_cast (show (k : ℕ) < k + 3 from by omega)
    · have hna : ¬(⊤ : SimpleGraph (Fin (k + 3))).IsAcyclic := by
        intro hacyclic
        have h2 := hacyclic.colorable_two
        rw [← chromaticNumber_le_iff_colorable] at h2
        simp only [chromaticNumber_top, Fintype.card_fin] at h2
        exact absurd h2 (by exact_mod_cast (show ¬ (k + 3 ≤ 2) from by omega))
      linarith [three_le_girth hna]
  ·
    push Not at hg
    exact erdos_probabilistic_argument k g hg

/-- **Theorem 3.4.1 (Erdős 1959).** For all natural numbers $k$ and $g$, there exists a
finite graph $G$ with girth strictly greater than $g$ and chromatic number strictly greater
than $k$. -/
theorem exists_high_girth_high_chromatic (k g : ℕ) :
    ∃ (V : Type) (_ : Fintype V) (G : SimpleGraph V),
      (↑k : ℕ∞) < G.chromaticNumber ∧ g < G.girth := by
  obtain ⟨V, hFin, G, hDec, hncol, hgirth⟩ := exists_not_colorable_high_girth k g
  exact ⟨V, hFin, G, (by rwa [← not_le, chromaticNumber_le_iff_colorable]), hgirth⟩

end HighGirthChromatic
