/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace TournamentHamilton

/-- A tournament on an arbitrary vertex type $V$: an irreflexive, asymmetric, and complete
Boolean edge relation (between distinct vertices exactly one direction holds). -/
structure Tournament (V : Type*) where
  edge : V → V → Bool
  edge_irrefl : ∀ v, edge v v = false
  edge_complete : ∀ u v, u ≠ v → (edge u v = true ∨ edge v u = true)
  edge_asymm : ∀ u v, edge u v = true → edge v u = false

variable {n : ℕ}

/-- A permutation $\sigma$ of $\mathrm{Fin}\, n$ encodes a Hamilton path of $T$ if each
consecutive directed edge $\sigma(i) \to \sigma(i+1)$ lies in $T$. -/
def Tournament.IsHamiltonPath (T : Tournament (Fin n)) (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i : Fin n, (h : i.val + 1 < n) → T.edge (σ i) (σ ⟨i.val + 1, h⟩) = true

/-- A permutation $\sigma$ encodes a Hamilton cycle of $T$ if every cyclic directed edge
$\sigma(i) \to \sigma((i+1) \bmod n)$ lies in $T$. -/
def Tournament.IsHamiltonCycle (T : Tournament (Fin n)) (σ : Equiv.Perm (Fin n)) : Prop :=
  (hn : n ≥ 1) → ∀ i : Fin n, T.edge (σ i) (σ ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩) = true

/-- Decidability of being a Hamilton path. -/
instance (T : Tournament (Fin n)) : DecidablePred T.IsHamiltonPath := by
  intro σ; unfold Tournament.IsHamiltonPath; exact inferInstance

/-- Decidability of being a Hamilton cycle. -/
instance (T : Tournament (Fin n)) : DecidablePred T.IsHamiltonCycle := by
  intro σ; unfold Tournament.IsHamiltonCycle; exact inferInstance

/-- The finset of all Hamilton-path permutations of $T$. -/
noncomputable def Tournament.hamiltonPaths (T : Tournament (Fin n)) :
    Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter T.IsHamiltonPath

/-- The finset of all Hamilton-cycle permutations of $T$. -/
noncomputable def Tournament.hamiltonCycles (T : Tournament (Fin n)) :
    Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter T.IsHamiltonCycle

/-- Number of Hamilton paths of $T$. -/
noncomputable def numHamiltonPaths (T : Tournament (Fin n)) : ℕ :=
  T.hamiltonPaths.card

/-- Number of Hamilton cycles of $T$. -/
noncomputable def numHamiltonCycles (T : Tournament (Fin n)) : ℕ :=
  T.hamiltonCycles.card

/-- Extension of a tournament on $\mathrm{Fin}\, n$ to one on $\mathrm{Fin}(n+1)$ by adding
a new vertex whose incoming/outgoing edges are dictated by a Boolean function $f$:
$f(v) = \mathrm{true}$ means new vertex beats $v$. -/
def extendTournament (T : Tournament (Fin n)) (f : Fin n → Bool) :
    Tournament (Fin (n + 1)) where
  edge u v :=
    if hu : u.val < n then
      if hv : v.val < n then
        T.edge ⟨u.val, hu⟩ ⟨v.val, hv⟩
      else
        !(f ⟨u.val, hu⟩)
    else
      if hv : v.val < n then
        f ⟨v.val, hv⟩
      else
        false
  edge_irrefl v := by
    split_ifs with hu hv
    · exact T.edge_irrefl ⟨v.val, hu⟩
    · rfl
  edge_complete u v huv := by
    by_cases hu : u.val < n <;> by_cases hv : v.val < n
    · simp only [dif_pos hu, dif_pos hv]
      have hne : (⟨u.val, hu⟩ : Fin n) ≠ ⟨v.val, hv⟩ := by
        intro h; apply huv; exact Fin.ext (by simpa using congrArg Fin.val h)
      exact T.edge_complete _ _ hne
    · simp only [dif_pos hu, dif_neg hv, dif_pos hu]
      cases f ⟨u.val, hu⟩ <;> simp
    · simp only [dif_neg hu, dif_pos hv, dif_neg hu]
      cases f ⟨v.val, hv⟩ <;> simp
    · exfalso; apply huv; exact Fin.ext (by omega)
  edge_asymm u v := by
    by_cases hu : u.val < n <;> by_cases hv : v.val < n
    · simp only [dif_pos hu, dif_pos hv]
      exact T.edge_asymm _ _
    · simp only [dif_pos hu, dif_neg hv, dif_neg hv, dif_pos hu]
      intro h; simp [Bool.not_eq_true'] at h; exact h
    · simp only [dif_neg hu, dif_pos hv, dif_pos hv, dif_neg hu]
      intro h; simp [h]
    · simp only [dif_neg hu, dif_neg hv]
      intro h; exact absurd h Bool.false_ne_true

/-- The number of Boolean functions $f : \mathrm{Fin}\, n \to \{\bot, \top\}$ with
$f(a) = \top$ and $f(b) = \bot$ is exactly $2^{n-2}$. -/
lemma card_filter_two_constraints (a b : Fin n) (hab : a ≠ b) (hn : n ≥ 2) :
    (Finset.univ.filter (fun f : Fin n → Bool => f a = true ∧ f b = false)).card =
    2 ^ (n - 2) := by
  classical
  have h1 : (Finset.univ.filter (fun f : Fin n → Bool => f a = true ∧ f b = false)).card =
      Fintype.card {f : Fin n → Bool // f a = true ∧ f b = false} := by
    rw [Fintype.card_subtype]
  rw [h1]
  have h2 : Fintype.card {f : Fin n → Bool // f a = true ∧ f b = false} =
      Fintype.card ({i : Fin n // i ≠ a ∧ i ≠ b} → Bool) := by
    apply Fintype.card_of_bijective
    show Function.Bijective (fun (p : {f : Fin n → Bool // f a = true ∧ f b = false}) =>
        fun (i : {i : Fin n // i ≠ a ∧ i ≠ b}) => p.val i.val)
    constructor
    · intro ⟨f₁, hf₁⟩ ⟨f₂, hf₂⟩ h
      simp only [Subtype.mk.injEq]
      ext i
      by_cases hia : i = a
      · subst hia; rw [hf₁.1, hf₂.1]
      · by_cases hib : i = b
        · subst hib; rw [hf₁.2, hf₂.2]
        · have := congr_fun h ⟨i, hia, hib⟩
          simpa using this
    · intro g
      refine ⟨⟨fun i => if h : i = a then true else if h2 : i = b then false else g ⟨i, h, h2⟩,
              ?_, ?_⟩, ?_⟩
      · simp
      · simp [hab.symm]
      · ext ⟨i, hi⟩; simp [hi.1, hi.2]
  rw [h2, Fintype.card_fun, Fintype.card_bool]
  congr 1
  rw [Fintype.card_subtype]
  have h_eq : (Finset.univ.filter (fun i : Fin n => i ≠ a ∧ i ≠ b)) =
      ((Finset.univ : Finset (Fin n)).erase a).erase b := by
    ext x; simp [Finset.mem_erase, ne_eq]; tauto
  rw [h_eq, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

/-- For a permutation $\sigma$, the number of orientation functions $f$ making the new
vertex compatible with $\sigma$ (i.e. $f(\sigma(0)) = \top$ and $f(\sigma(n-1)) = \bot$)
is $2^{n-2}$. -/
lemma card_good_orientations (σ : Equiv.Perm (Fin n)) (hn : n ≥ 2) :
    (Finset.univ.filter (fun f : Fin n → Bool =>
      f (σ ⟨0, by omega⟩) = true ∧ f (σ ⟨n - 1, by omega⟩) = false)).card = 2 ^ (n - 2) := by
  apply card_filter_two_constraints
  · exact σ.injective.ne (by intro h; have := congrArg Fin.val h; simp at this; omega)
  · exact hn


/-- Injection from Hamilton paths compatible with $f$ into Hamilton cycles of the
extended tournament: each such path can be closed into a cycle via the new vertex. -/
theorem good_paths_le_cycles (n : ℕ) (hn : n ≥ 2) (T : Tournament (Fin n))
    (f : Fin n → Bool) :
    (T.hamiltonPaths.filter (fun σ =>
      f (σ ⟨0, by omega⟩) = true ∧ f (σ ⟨n - 1, by omega⟩) = false)).card ≤
    numHamiltonCycles (extendTournament T f) := by sorry

/-- Double-counting bound: summing the number of Hamilton cycles of each extension
$T[f]$ over all orientation functions $f : \mathrm{Fin}\, n \to \{\bot, \top\}$ gives at
least $\mathrm{numHamiltonPaths}(T) \cdot 2^{n-2}$. -/
lemma sum_cycles_lower_bound (n : ℕ) (hn : n ≥ 2) (T : Tournament (Fin n)) :
    numHamiltonPaths T * 2 ^ (n - 2) ≤
    ∑ f : Fin n → Bool, numHamiltonCycles (extendTournament T f) := by
  classical
  let good (σ : Equiv.Perm (Fin n)) (f : Fin n → Bool) : ℕ :=
    if f (σ ⟨0, by omega⟩) = true ∧ f (σ ⟨n - 1, by omega⟩) = false then 1 else 0
  have h1 : numHamiltonPaths T * 2 ^ (n - 2) =
      ∑ σ ∈ T.hamiltonPaths, ∑ f : Fin n → Bool, good σ f := by
    have h_each : ∀ σ ∈ T.hamiltonPaths,
        ∑ f : Fin n → Bool, good σ f = 2 ^ (n - 2) := by
      intro σ _
      simp only [good]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, Nat.smul_one_eq_cast,
          Nat.cast_id]
      exact card_good_orientations σ hn
    rw [Finset.sum_congr rfl h_each]
    simp [numHamiltonPaths, Finset.sum_const]
  have h2 : ∑ σ ∈ T.hamiltonPaths, ∑ f : Fin n → Bool, good σ f =
      ∑ f : Fin n → Bool, ∑ σ ∈ T.hamiltonPaths, good σ f := Finset.sum_comm
  have h3 : ∀ f : Fin n → Bool,
      ∑ σ ∈ T.hamiltonPaths, good σ f ≤ numHamiltonCycles (extendTournament T f) := by
    intro f


    have h_sum_eq : ∑ σ ∈ T.hamiltonPaths, good σ f =
        (T.hamiltonPaths.filter (fun σ =>
          f (σ ⟨0, by omega⟩) = true ∧ f (σ ⟨n - 1, by omega⟩) = false)).card := by
      simp only [good]
      rw [← Finset.card_filter]
    rw [h_sum_eq]
    exact good_paths_le_cycles n hn T f
  calc numHamiltonPaths T * 2 ^ (n - 2)
      = ∑ σ ∈ T.hamiltonPaths, ∑ f : Fin n → Bool, good σ f := h1
    _ = ∑ f : Fin n → Bool, ∑ σ ∈ T.hamiltonPaths, good σ f := h2
    _ ≤ ∑ f : Fin n → Bool, numHamiltonCycles (extendTournament T f) :=
        Finset.sum_le_sum (fun f _ => h3 f)

/-- Averaging argument (key step in Alon's bound for Hamilton paths): for any tournament
$T$ on $n \ge 2$ vertices, there exists a one-vertex extension $T'$ on $n + 1$ vertices
with $4 \cdot \mathrm{numHamiltonCycles}(T') \ge \mathrm{numHamiltonPaths}(T)$. -/
theorem tournament_add_vertex_hamilton_cycles (n : ℕ) (hn : n ≥ 2)
    (T : Tournament (Fin n)) :
    ∃ T' : Tournament (Fin (n + 1)),
      4 * numHamiltonCycles T' ≥ numHamiltonPaths T := by
  classical
  suffices h : ∃ f : Fin n → Bool,
      4 * numHamiltonCycles (extendTournament T f) ≥ numHamiltonPaths T from by
    obtain ⟨f, hf⟩ := h
    exact ⟨extendTournament T f, hf⟩
  by_contra h_all
  push_neg at h_all
  have h_sum_lt : 4 * ∑ f : Fin n → Bool, numHamiltonCycles (extendTournament T f) <
      numHamiltonPaths T * 2 ^ n := by
    calc 4 * ∑ f : Fin n → Bool, numHamiltonCycles (extendTournament T f)
        = ∑ f : Fin n → Bool, 4 * numHamiltonCycles (extendTournament T f) := by
            rw [Finset.mul_sum]
      _ < ∑ _f : Fin n → Bool, numHamiltonPaths T := by
            apply Finset.sum_lt_sum
            · intro f _; exact Nat.le_of_lt (h_all f)
            · exact ⟨Function.const _ true, Finset.mem_univ _, h_all _⟩
      _ = numHamiltonPaths T * 2 ^ n := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fun,
                  Fintype.card_bool, Fintype.card_fin]; ring
  have h_sum_ge : numHamiltonPaths T * 2 ^ n ≤
      4 * ∑ f : Fin n → Bool, numHamiltonCycles (extendTournament T f) := by
    have h_lower := sum_cycles_lower_bound n hn T
    have h_pow : 4 * 2 ^ (n - 2) = 2 ^ n := by
      calc 4 * 2 ^ (n - 2) = 2 ^ 2 * 2 ^ (n - 2) := by norm_num
        _ = 2 ^ (2 + (n - 2)) := by rw [pow_add]
        _ = 2 ^ n := by congr 1; omega
    calc numHamiltonPaths T * 2 ^ n
        = numHamiltonPaths T * (4 * 2 ^ (n - 2)) := by rw [h_pow]
      _ = 4 * (numHamiltonPaths T * 2 ^ (n - 2)) := by ring
      _ ≤ 4 * ∑ f : Fin n → Bool, numHamiltonCycles (extendTournament T f) :=
          Nat.mul_le_mul_left 4 h_lower
  linarith

end TournamentHamilton
