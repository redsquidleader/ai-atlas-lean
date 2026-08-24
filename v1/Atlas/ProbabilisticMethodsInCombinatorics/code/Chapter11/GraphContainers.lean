/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open SimpleGraph Finset

namespace GraphContainers

/-- The average degree of a finite simple graph, $\bar d(G) = 2|E(G)|/|V(G)|$. -/
noncomputable def avgDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  2 * (G.edgeFinset.card : ℝ) / (Fintype.card V : ℝ)

/-- The partial binomial sum $\sum_{i=0}^{k} \binom{n}{i}$, bounding the number of subsets
of an $n$-element set of size at most $k$. -/
def binomialSum (n k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (k + 1), n.choose i

/-- **Container algorithm (fingerprint version, Theorem 11.2.3).** For every $c > 0$ there
exists $0 < \delta < 1$ such that for every graph $G$ with $\Delta(G) \leq c \, \bar d(G)$
there is a function `container` mapping each small "fingerprint" $S$ to a vertex set with
$|container(S)| \leq (1 - \delta) |V|$, and every independent set $I$ has a fingerprint
$S \subseteq I$ of size $\leq 2\delta |V|/\bar d(G)$ with $I \subseteq container(S)$. -/
theorem container_algorithm_claim :
    ∀ c : ℝ, 0 < c →
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (G.maxDegree : ℝ) ≤ c * avgDegree G →
    ∃ (container : Finset V → Finset V),

      (∀ S : Finset V, (S.card : ℝ) ≤ 2 * δ * (Fintype.card V : ℝ) / avgDegree G →
        ((container S).card : ℝ) ≤ (1 - δ) * (Fintype.card V : ℝ)) ∧

      (∀ I : Finset V, G.IsIndepSet (↑I : Set V) →
        ∃ S : Finset V,
          S ⊆ I ∧
          I ⊆ container S ∧
          ((S.card : ℝ) ≤ 2 * δ * (Fintype.card V : ℝ) / avgDegree G)) := by sorry

/-- **Theorem 11.2.1 (Container theorem for independent sets in graphs).** For every
$c > 0$ there exists $\delta > 0$ such that for every finite graph $G$ with
$\Delta(G) \leq c \, \bar d(G)$, there is a family $\mathcal{C}$ of "containers" such that
* $|\mathcal{C}| \leq \sum_{i \leq 2\delta n / \bar d(G)} \binom{n}{i}$;
* every independent set of $G$ is contained in some $C \in \mathcal{C}$;
* every container has $|C| \leq (1 - \delta) n$. -/
theorem independent_set_container :
    ∀ c : ℝ, 0 < c →
    ∃ δ : ℝ, 0 < δ ∧
    ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
    (G.maxDegree : ℝ) ≤ c * avgDegree G →
    ∃ 𝒞 : Finset (Finset V),
      (𝒞.card : ℝ) ≤ ↑(binomialSum (Fintype.card V)
        ⌊2 * δ * (Fintype.card V : ℝ) / avgDegree G⌋₊) ∧
      (∀ I : Finset V, G.IsIndepSet (↑I : Set V) → ∃ C ∈ 𝒞, I ⊆ C) ∧
      (∀ C ∈ 𝒞, (C.card : ℝ) ≤ (1 - δ) * (Fintype.card V : ℝ)) := by
  intro c hc
  obtain ⟨δ, hδ_pos, hδ_lt_one, hAlg⟩ := container_algorithm_claim c hc
  refine ⟨δ, hδ_pos, fun V _ _ G _ hDeg => ?_⟩
  classical
  obtain ⟨container, hCsize, hCcontain⟩ := hAlg V G hDeg
  set k := ⌊2 * δ * (Fintype.card V : ℝ) / avgDegree G⌋₊

  set 𝒞 := (Finset.univ.filter (fun S : Finset V => S.card ≤ k)).image container
  refine ⟨𝒞, ?_, ?_, ?_⟩
  ·
    have h1 : 𝒞.card ≤ (Finset.univ.filter (fun S : Finset V => S.card ≤ k)).card :=
      Finset.card_image_le
    suffices h2 : (Finset.univ.filter (fun S : Finset V => S.card ≤ k)).card ≤
        binomialSum (Fintype.card V) k by
      exact_mod_cast h1.trans h2
    calc (Finset.univ.filter (fun S : Finset V => S.card ≤ k)).card
        ≤ (Finset.univ.biUnion (fun i : Fin (k + 1) =>
            (Finset.univ : Finset V).powersetCard ↑i)).card := by
          apply Finset.card_le_card
          intro S hS
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
          simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
          exact ⟨⟨S.card, Nat.lt_succ_of_le hS⟩,
            Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩
      _ ≤ ∑ i : Fin (k + 1), ((Finset.univ : Finset V).powersetCard ↑i).card :=
          Finset.card_biUnion_le
      _ = ∑ i : Fin (k + 1), (Fintype.card V).choose ↑i := by
          congr 1; ext ⟨i, _⟩; simp [Finset.card_powersetCard]
      _ = binomialSum (Fintype.card V) k := by
          simp only [binomialSum]; rw [← Fin.sum_univ_eq_sum_range]
  ·
    intro I hI
    obtain ⟨S, hSI, hIC, hScard⟩ := hCcontain I hI
    have hSk : S.card ≤ k := Nat.le_floor hScard
    have hSmem : S ∈ Finset.univ.filter (fun S : Finset V => S.card ≤ k) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hSk⟩
    exact ⟨container S, Finset.mem_image.mpr ⟨S, hSmem, rfl⟩, hIC⟩
  ·
    intro C hC
    obtain ⟨S, hSmem, rfl⟩ := Finset.mem_image.mp hC
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hSmem

    have havg_nn : (0 : ℝ) ≤ avgDegree G := by
      unfold avgDegree
      apply div_nonneg
      · apply mul_nonneg (by norm_num) (Nat.cast_nonneg _)
      · exact Nat.cast_nonneg _
    have hScard : (S.card : ℝ) ≤ 2 * δ * (Fintype.card V : ℝ) / avgDegree G := by
      exact (Nat.cast_le.mpr hSmem).trans (Nat.floor_le (by
        apply div_nonneg
        · apply mul_nonneg (mul_nonneg (by linarith) (by linarith)) (Nat.cast_nonneg _)
        · exact havg_nn))
    exact hCsize S hScard

end GraphContainers
