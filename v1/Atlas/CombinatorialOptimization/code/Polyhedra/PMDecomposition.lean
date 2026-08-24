/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.CombinatorialOptimization.code.Polyhedra.EdmondsPolytope

open SimpleGraph Finset BigOperators Classical

noncomputable section

namespace SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem edmonds_polytope_perturbation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : G.edgeSet → ℝ)
    (hnn : ∀ e : G.edgeSet, 0 ≤ x e)
    (hdeg : ∀ v : V, ∑ e ∈ incidentEdgeFinset G v, x e = 1)
    (hodd : ∀ S : Finset V, Odd S.card → ∑ e ∈ edgeCutFinset G S, x e ≥ 1)
    (e₀ : G.edgeSet)
    (he₀ : x e₀ ≠ 0 ∧ x e₀ ≠ 1) :
    ∃ (y z : G.edgeSet → ℝ) (t : ℝ),
      0 < t ∧ t < 1 ∧
      y ∈ edmondsPolytope G ∧
      z ∈ edmondsPolytope G ∧
      (∀ e, x e = t * y e + (1 - t) * z e) ∧
      (Finset.univ.filter (fun e : G.edgeSet => y e ≠ 0 ∧ y e ≠ 1)).card <
        (Finset.univ.filter (fun e : G.edgeSet => x e ≠ 0 ∧ x e ≠ 1)).card ∧
      (Finset.univ.filter (fun e : G.edgeSet => z e ≠ 0 ∧ z e ≠ 1)).card <
        (Finset.univ.filter (fun e : G.edgeSet => x e ≠ 0 ∧ x e ≠ 1)).card := by sorry

lemma edmondsPolytope_pm_decomposition_aux
    (n : ℕ)
    (x : G.edgeSet → ℝ)
    (hx : x ∈ edmondsPolytope G)
    (hn : (Finset.univ.filter (fun e : G.edgeSet => x e ≠ 0 ∧ x e ≠ 1)).card = n) :
    ∃ (k : ℕ) (M : Fin k → G.Subgraph) (_ : ∀ i, (M i).IsPerfectMatching)
      (w : Fin k → ℝ),
      (∀ i, 0 ≤ w i) ∧
      (∑ i : Fin k, w i = 1) ∧
      (∀ e : G.edgeSet, x e = ∑ i : Fin k,
        w i * if (e : Sym2 V) ∈ (M i).edgeSet then 1 else 0) := by
  induction n using Nat.strongRecOn generalizing x with
  | _ n ih =>
  obtain ⟨hnn, hdeg, hodd⟩ := hx
  by_cases hint : ∀ e : G.edgeSet, x e = 0 ∨ x e = 1
  ·
    obtain ⟨M, hM, hx_eq⟩ := integral_edmondsPolytope_mem_pm G x hdeg hint
    refine ⟨1, fun _ => M, fun _ => hM, fun _ => 1, fun _ => by norm_num, by simp, ?_⟩
    intro e
    simp only [Fin.sum_univ_one, one_mul]
    exact congr_fun hx_eq e
  ·
    push_neg at hint
    obtain ⟨e₀, he₀⟩ := hint
    have hn_pos : 0 < n := by
      rw [← hn]
      exact Finset.card_pos.mpr ⟨e₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he₀⟩⟩

    obtain ⟨y, z, t, ht_pos, ht_lt_one, hy_mem, hz_mem, hx_combo, hy_fewer, hz_fewer⟩ :=
      edmonds_polytope_perturbation G x hnn hdeg hodd e₀ he₀

    have hy_card : (Finset.univ.filter (fun e : G.edgeSet => y e ≠ 0 ∧ y e ≠ 1)).card < n := by
      omega
    obtain ⟨k₁, M₁, hM₁, w₁, hw₁_nn, hw₁_sum, hy_decomp⟩ :=
      ih _ hy_card y hy_mem rfl

    have hz_card : (Finset.univ.filter (fun e : G.edgeSet => z e ≠ 0 ∧ z e ≠ 1)).card < n := by
      omega
    obtain ⟨k₂, M₂, hM₂, w₂, hw₂_nn, hw₂_sum, hz_decomp⟩ :=
      ih _ hz_card z hz_mem rfl

    refine ⟨k₁ + k₂,
      fun i => Fin.addCases M₁ M₂ i,
      fun i => by refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp only [Fin.addCases_left, Fin.addCases_right] <;> [exact hM₁ j; exact hM₂ j],
      fun i => Fin.addCases (fun j => t * w₁ j) (fun j => (1 - t) * w₂ j) i,
      ?_, ?_, ?_⟩
    ·
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.addCases_left]
        exact mul_nonneg (le_of_lt ht_pos) (hw₁_nn j)
      · simp only [Fin.addCases_right]
        exact mul_nonneg (by linarith) (hw₂_nn j)
    ·
      rw [Fin.sum_univ_add]
      simp only [Fin.addCases_left, Fin.addCases_right]
      rw [← Finset.mul_sum, ← Finset.mul_sum, hw₁_sum, hw₂_sum]
      ring
    ·
      intro e
      rw [Fin.sum_univ_add]
      simp only [Fin.addCases_left, Fin.addCases_right]
      rw [hx_combo e, hy_decomp e, hz_decomp e]
      rw [Finset.mul_sum, Finset.mul_sum]
      congr 1 <;> (apply Finset.sum_congr rfl; intro i _; ring)

private theorem tight_oddset_pm_decomposition
    (x : G.edgeSet → ℝ)
    (hx : x ∈ edmondsPolytope G)
    (W : Finset V)
    (hW_odd : Odd W.card)
    (hW_tight : ∑ e ∈ edgeCutFinset G W, x e = 1) :
    ∃ (k : ℕ) (M : Fin k → G.Subgraph) (_ : ∀ i, (M i).IsPerfectMatching)
      (w : Fin k → ℝ),
      (∀ i, 0 ≤ w i) ∧
      (∑ i : Fin k, w i = 1) ∧
      (∀ e : G.edgeSet, x e = ∑ i : Fin k,
        w i * if (e : Sym2 V) ∈ (M i).edgeSet then 1 else 0) :=
  edmondsPolytope_pm_decomposition_aux G _ x hx rfl

end SimpleGraph

end
