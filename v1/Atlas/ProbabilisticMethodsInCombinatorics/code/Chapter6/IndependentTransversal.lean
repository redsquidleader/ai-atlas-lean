/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic

set_option maxHeartbeats 400000

open SimpleGraph Finset

namespace IndependentTransversal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A function `f : Fin r → V` is an *independent transversal* for the partition
`parts : Fin r → Finset V` of $V$ in the graph $G$ if it picks one vertex from each part
($f i \in $ `parts i`) and its image is an independent set in $G$. -/
def IsIndependentTransversal (G : SimpleGraph V) (parts : Fin r → Finset V)
    (f : Fin r → V) : Prop :=
  (∀ i, f i ∈ parts i) ∧ G.IsIndepSet (Set.range f)

omit [Fintype V] [DecidableEq V] in
/-- An independent transversal for smaller parts `parts'` is also one for any enlargement
`parts ⊇ parts'`. -/
lemma IsIndependentTransversal.of_subset {G : SimpleGraph V} {r : ℕ}
    {parts parts' : Fin r → Finset V}
    (h_sub : ∀ i, parts' i ⊆ parts i) {f : Fin r → V}
    (hf : IsIndependentTransversal G parts' f) :
    IsIndependentTransversal G parts f :=
  ⟨fun i => h_sub i (hf.1 i), hf.2⟩

/-- LLL-based existence of an independent transversal in the *equal-part* case: if every part
has the same size $k$ and $2 e \Delta(G) \le k$, then there is an independent transversal,
obtained by sampling each $f(i)$ uniformly from `parts i` and applying the LLL. -/
theorem lll_independent_transversal_equal_parts
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (parts : Fin r → Finset V)
    (k : ℕ) (hk : 0 < k)
    (h_card : ∀ i, (parts i).card = k)
    (h_disjoint : ∀ i j : Fin r, i ≠ j → Disjoint (parts i) (parts j))
    (h_lll : 2 * Real.exp 1 * (G.maxDegree : ℝ) ≤ (k : ℝ)) :
    ∃ f : Fin r → V, IsIndependentTransversal G parts f := by sorry

/-- Theorem 6.3.1 (Independent Transversal): if $V$ is partitioned into disjoint parts each of
size at least $2 e \Delta(G)$, then there is an independent transversal selecting one vertex per
part with pairwise non-adjacent images. Proven by trimming each part to size exactly
$\lceil 2 e \Delta \rceil$ and invoking the equal-parts LLL version. -/
theorem independent_transversal_exists
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (parts : Fin r → Finset V)
    (h_nonempty : ∀ i, (parts i).Nonempty)
    (h_disjoint : ∀ i j : Fin r, i ≠ j → Disjoint (parts i) (parts j))
    (h_size : ∀ i, 2 * Real.exp 1 * (G.maxDegree : ℝ) ≤ ((parts i).card : ℝ)) :
    ∃ f : Fin r → V, IsIndependentTransversal G parts f := by
  classical

  rcases Nat.eq_zero_or_pos r with hr0 | hr_pos
  · subst hr0
    exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun _ ha => absurd ha (by simp)⟩

  set k := ⌈2 * Real.exp 1 * (G.maxDegree : ℝ)⌉₊

  have h_card_ge : ∀ i, k ≤ (parts i).card := fun i => Nat.ceil_le.mpr (h_size i)

  rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
  ·
    have hΔ0 : G.maxDegree = 0 := by
      have h2e_pos : (0 : ℝ) < 2 * Real.exp 1 := by positivity
      have hle : 2 * Real.exp 1 * (G.maxDegree : ℝ) ≤ 0 := Nat.ceil_eq_zero.mp hk0
      have hΔ_le : (G.maxDegree : ℝ) ≤ 0 := by nlinarith
      exact Nat.eq_zero_of_le_zero (by exact_mod_cast hΔ_le)

    choose f hf using h_nonempty
    refine ⟨f, fun i => hf i, ?_⟩
    intro a _ b _ _ hadj
    have h1 := G.degree_le_maxDegree a
    rw [hΔ0] at h1
    have h2 : 0 < G.degree a := by
      simp only [SimpleGraph.degree]
      exact Finset.card_pos.mpr ⟨b, by simpa using hadj⟩
    omega
  ·

    have h_trim : ∀ i, ∃ t : Finset V, t ⊆ parts i ∧ t.card = k :=
      fun i => Finset.exists_subset_card_eq (h_card_ge i)
    choose trimmed h_trimmed_sub h_trimmed_card using h_trim

    have h_trim_disjoint : ∀ i j : Fin r, i ≠ j → Disjoint (trimmed i) (trimmed j) :=
      fun i j hij => Disjoint.mono (h_trimmed_sub i) (h_trimmed_sub j) (h_disjoint i j hij)

    have h_lll : 2 * Real.exp 1 * (G.maxDegree : ℝ) ≤ (k : ℝ) := Nat.le_ceil _

    obtain ⟨f, hf⟩ := lll_independent_transversal_equal_parts G r trimmed k hk_pos
      h_trimmed_card h_trim_disjoint h_lll

    exact ⟨f, hf.of_subset h_trimmed_sub⟩

end IndependentTransversal
