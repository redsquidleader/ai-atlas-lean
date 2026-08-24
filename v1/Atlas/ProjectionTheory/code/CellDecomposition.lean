/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset Set MvPolynomial

namespace CellDecomposition

/--
A line in `ℝ²`: a one-dimensional affine subspace, packaged with a proof that
its direction has rank `1` and that its carrier set is nonempty.
-/
structure Line2 where
  carrier : AffineSubspace ℝ (Fin 2 → ℝ)
  dim_eq : Module.finrank ℝ carrier.direction = 1
  nonempty : (carrier : Set (Fin 2 → ℝ)).Nonempty

/-- Membership of a point in a `Line2`: belongs to the underlying affine subspace. -/
instance : Membership (Fin 2 → ℝ) Line2 where
  mem l p := p ∈ l.carrier


/--
Polynomial ham-sandwich theorem for finite sets in `ℝ²`. Given at most `D²`
finite sets `S_i ⊆ ℝ²`, there is a nonzero polynomial `p` of total degree at
most `D` such that for each `i`, both `{x ∈ S_i : p(x) > 0}` and
`{x ∈ S_i : p(x) < 0}` contain at most half of `S_i`.
-/
theorem polynomial_ham_sandwich_finite :
    ∀ {ι : Type} [Fintype ι] (D : ℕ)
      (_ : Fintype.card ι ≤ D ^ 2)
      (S : ι → Finset (Fin 2 → ℝ)),
    ∃ (p : MvPolynomial (Fin 2) ℝ),
      p ≠ 0 ∧
      p.totalDegree ≤ D ∧
      (∀ i, (S i |>.filter (fun x => eval x p > 0)).card ≤ (S i).card / 2) ∧
      (∀ i, (S i |>.filter (fun x => eval x p < 0)).card ≤ (S i).card / 2) := by sorry


/--
Bézout-type bound: the intersection of a line `ℓ ⊂ ℝ²` with the zero set of a
nonzero polynomial `p` is finite and has at most `deg p` points.
-/
theorem bezout_line_polynomial :
    ∀ (p : MvPolynomial (Fin 2) ℝ) (ℓ : Line2),
      p ≠ 0 →
      Set.Finite ((↑ℓ.carrier : Set (Fin 2 → ℝ)) ∩ {x | eval x p = 0}) ∧
      ((↑ℓ.carrier : Set (Fin 2 → ℝ)) ∩ {x | eval x p = 0}).ncard ≤ p.totalDegree := by sorry

/--
The open cell `{x : ∀ i, sign(polys i (x)) = σ i}` cut out by a sign pattern
`σ : Fin k → Bool` (with `true` meaning positive sign and `false` meaning
negative sign).
-/
noncomputable def polyCell {k : ℕ} (polys : Fin k → MvPolynomial (Fin 2) ℝ)
    (σ : Fin k → Bool) : Set (Fin 2 → ℝ) :=
  ⋂ i, if σ i then {x | eval x (polys i) > 0}
              else {x | eval x (polys i) < 0}

/--
The "wall" `⋃_i Z(polys i)`: the union of the zero sets of the polynomials,
separating the open cells `polyCell polys σ`.
-/
def polyWall {k : ℕ} (polys : Fin k → MvPolynomial (Fin 2) ℝ) : Set (Fin 2 → ℝ) :=
  ⋃ i, {x | eval x (polys i) = 0}

/--
The points of a finite set `X ⊆ ℝ²` lying in the open cell `polyCell polys σ`,
returned as a `Finset`.
-/
noncomputable def signPatternCell (X : Finset (Fin 2 → ℝ))
    {k : ℕ} (polys : Fin k → MvPolynomial (Fin 2) ℝ) (σ : Fin k → Bool) :
    Finset (Fin 2 → ℝ) :=
  X.filter (fun x => ∀ i, if σ i then eval x (polys i) > 0 else eval x (polys i) < 0)

/-- Every `polyCell` is open, being a finite intersection of open half-spaces
defined by polynomial inequalities. -/
lemma polyCell_isOpen {k : ℕ} (polys : Fin k → MvPolynomial (Fin 2) ℝ) (σ : Fin k → Bool) :
    IsOpen (polyCell polys σ) := by
  apply isOpen_iInter_of_finite; intro i
  split_ifs
  · exact isOpen_lt continuous_const (continuous_eval _)
  · exact isOpen_lt (continuous_eval _) continuous_const

/-- The polynomial wall is closed, being a finite union of polynomial zero sets. -/
lemma polyWall_isClosed {k : ℕ} (polys : Fin k → MvPolynomial (Fin 2) ℝ) :
    IsClosed (polyWall polys) := by
  apply isClosed_iUnion_of_finite; intro i
  exact isClosed_eq (continuous_eval _) continuous_const

/-- The wall together with the union of all sign-pattern open cells covers `ℝ²`. -/
lemma polyWall_union_cells {k : ℕ} (polys : Fin k → MvPolynomial (Fin 2) ℝ) :
    polyWall polys ∪ ⋃ σ : Fin k → Bool, polyCell polys σ = univ := by
  ext x; simp only [mem_union, mem_iUnion, mem_univ, iff_true]
  by_cases h : ∃ i, eval x (polys i) = 0
  · left; exact mem_iUnion.mpr (h.imp fun i hi => hi)
  · right; push_neg at h
    refine ⟨fun i => decide (eval x (polys i) > 0), ?_⟩
    simp only [polyCell, mem_iInter, decide_eq_true_eq]
    intro i; have hi := h i
    split_ifs with hpos
    · exact hpos
    · push_neg at hpos; exact lt_of_le_of_ne hpos hi

/-- Distinct sign patterns give disjoint open cells. -/
lemma polyCell_pairwise_disjoint {k : ℕ} (polys : Fin k → MvPolynomial (Fin 2) ℝ) :
    Pairwise fun σ τ : Fin k → Bool => Disjoint (polyCell polys σ) (polyCell polys τ) := by
  intro σ τ hne; rw [Set.disjoint_left]
  intro x hx hτ
  simp only [polyCell, mem_iInter] at hx hτ
  apply hne; funext i
  have hxi := hx i; have hτi := hτ i
  cases hσ : σ i <;> cases hτ' : τ i <;> simp_all <;> linarith

/-- Each open cell is disjoint from the wall. -/
lemma polyCell_disjoint_wall {k : ℕ} (polys : Fin k → MvPolynomial (Fin 2) ℝ)
    (σ : Fin k → Bool) : Disjoint (polyCell polys σ) (polyWall polys) := by
  rw [Set.disjoint_left]; intro x hx hw
  simp only [polyCell, mem_iInter] at hx
  simp only [polyWall, mem_iUnion] at hw
  obtain ⟨i, hi⟩ := hw
  have hxi := hx i
  cases hσi : σ i <;> simp_all <;> linarith

/--
The intersection of a line with the wall of nonzero polynomials is finite, by
Bézout applied to each polynomial.
-/
lemma polyWall_line_finite {k : ℕ} (polys : Fin k → MvPolynomial (Fin 2) ℝ)
    (hne : ∀ i, polys i ≠ 0) (ℓ : Line2) :
    Set.Finite ((↑ℓ.carrier : Set (Fin 2 → ℝ)) ∩ polyWall polys) := by
  rw [polyWall, Set.inter_iUnion]
  exact Set.finite_iUnion fun i => (bezout_line_polynomial (polys i) ℓ (hne i)).1

/--
Bézout bound: the number of intersection points of a line with the polynomial
wall is at most `∑_i deg(polys i)`.
-/
lemma polyWall_line_ncard {k : ℕ} (polys : Fin k → MvPolynomial (Fin 2) ℝ)
    (hne : ∀ i, polys i ≠ 0) (ℓ : Line2) :
    ((↑ℓ.carrier : Set (Fin 2 → ℝ)) ∩ polyWall polys).ncard ≤
      ∑ i : Fin k, (polys i).totalDegree := by
  rw [polyWall, Set.inter_iUnion]
  calc (⋃ i, (↑ℓ.carrier : Set (Fin 2 → ℝ)) ∩ {x | eval x (polys i) = 0}).ncard
      ≤ ∑ i : Fin k, ((↑ℓ.carrier : Set (Fin 2 → ℝ)) ∩ {x | eval x (polys i) = 0}).ncard :=
        Set.ncard_iUnion_le_of_fintype _
    _ ≤ ∑ i : Fin k, (polys i).totalDegree := by
        apply Finset.sum_le_sum; intro i _
        exact (bezout_line_polynomial (polys i) ℓ (hne i)).2

/--
Inductive step: after appending a polynomial `p` and the sign `true`, the
sign-pattern cell sits inside the previous cell intersected with `{x : p(x) > 0}`.
-/
lemma signPatternCell_snoc_true_subset (X : Finset (Fin 2 → ℝ)) {k : ℕ}
    (polys : Fin k → MvPolynomial (Fin 2) ℝ) (p : MvPolynomial (Fin 2) ℝ)
    (σ : Fin k → Bool) :
    signPatternCell X (Fin.snoc polys p) (Fin.snoc σ true) ⊆
      (signPatternCell X polys σ).filter (fun x => eval x p > 0) := by
  intro x hx; simp only [signPatternCell, Finset.mem_filter] at hx ⊢
  refine ⟨⟨hx.1, fun i => ?_⟩, ?_⟩
  · have := hx.2 (Fin.castSucc i); simp [Fin.snoc_castSucc] at this; exact this
  · have := hx.2 (Fin.last k); simp [Fin.snoc_last] at this; exact this

/--
Inductive step: after appending a polynomial `p` and the sign `false`, the
sign-pattern cell sits inside the previous cell intersected with `{x : p(x) < 0}`.
-/
lemma signPatternCell_snoc_false_subset (X : Finset (Fin 2 → ℝ)) {k : ℕ}
    (polys : Fin k → MvPolynomial (Fin 2) ℝ) (p : MvPolynomial (Fin 2) ℝ)
    (σ : Fin k → Bool) :
    signPatternCell X (Fin.snoc polys p) (Fin.snoc σ false) ⊆
      (signPatternCell X polys σ).filter (fun x => eval x p < 0) := by
  intro x hx; simp only [signPatternCell, Finset.mem_filter] at hx ⊢
  refine ⟨⟨hx.1, fun i => ?_⟩, ?_⟩
  · have := hx.2 (Fin.castSucc i); simp [Fin.snoc_castSucc] at this; exact this
  · have := hx.2 (Fin.last k); simp [Fin.snoc_last] at this; exact this

/-- Arithmetic estimate `2^j ≤ (2^{⌊(j+1)/2⌋})²` used to control degrees at each
bisection step. -/
lemma degree_bound_step (j : ℕ) : 2 ^ j ≤ (2 ^ ((j + 1) / 2)) ^ 2 := by
  have h : j ≤ 2 * ((j + 1) / 2) := by omega
  calc 2 ^ j ≤ 2 ^ (2 * ((j + 1) / 2)) := Nat.pow_le_pow_right (by norm_num) h
    _ = (2 ^ ((j + 1) / 2)) ^ 2 := by ring

/-- There are `2^k` sign patterns in `Fin k → Bool`. -/
lemma card_fin_bool_fun (k : ℕ) : Fintype.card (Fin k → Bool) = 2 ^ k := by
  simp [Fintype.card_fin, Fintype.card_bool]

/-- Closed-form for the cumulative degree sum at an even number of bisection
steps: `∑_{j<2m} 2^{⌊(j+1)/2⌋} = 3(2^m − 1)`. -/
lemma degree_sum_bound_even (m : ℕ) :
    ∑ j ∈ Finset.range (2 * m), 2 ^ ((j + 1) / 2) = 3 * (2 ^ m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 from by ring,
        Finset.sum_range_succ, Finset.sum_range_succ, ih]
    have h1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have h2 : (2 * m + 0 + 1) / 2 = m := by omega
    rw [h1, h2]; ring_nf; omega

/-- Cumulative degree bound after `k` bisection steps:
`∑_{j<k} 2^{⌊(j+1)/2⌋} ≤ 4 · 2^{⌊k/2⌋}`. -/
lemma degree_sum_bound (k : ℕ) :
    ∑ j ∈ Finset.range k, 2 ^ ((j + 1) / 2) ≤ 4 * 2 ^ (k / 2) := by
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hk : k = 2 * m := by omega
    rw [hk, degree_sum_bound_even]
    have h : 2 * m / 2 = m := by omega
    rw [h]; omega
  · have hk : k = 2 * m + 1 := by omega
    rw [hk, show 2 * m + 1 = (2 * m) + 1 from by ring,
        Finset.sum_range_succ, degree_sum_bound_even]
    have h1 : (2 * m + 0 + 1) / 2 = m := by omega
    have h2 : (2 * m + 1) / 2 = m := by omega
    rw [h1]; omega

/-- For `s ≥ 1`, `s² ≤ 2^{2 log₂ s + 2}`. Used to relate the target parameter
`s` to the chosen number of bisection steps `k = 2 log₂ s + 2`. -/
lemma two_pow_log_bound (s : ℕ) (hs : 1 ≤ s) : s ^ 2 ≤ 2 ^ (2 * Nat.log 2 s + 2) := by
  have h1 : s ≤ 2 ^ (Nat.log 2 s + 1) := (Nat.lt_pow_succ_log_self (by norm_num) s).le
  calc s ^ 2 ≤ (2 ^ (Nat.log 2 s + 1)) ^ 2 := Nat.pow_le_pow_left h1 _
    _ = 2 ^ (2 * Nat.log 2 s + 2) := by ring

/-- For `s ≥ 1`, `2^{⌊(2 log₂ s + 2) / 2⌋} ≤ 2s`. Used to convert the
`O(2^{k/2})` degree bound into an `O(s)` bound. -/
lemma two_pow_half_log_bound (s : ℕ) (hs : 1 ≤ s) :
    2 ^ ((2 * Nat.log 2 s + 2) / 2) ≤ 2 * s := by
  have h : (2 * Nat.log 2 s + 2) / 2 = Nat.log 2 s + 1 := by omega
  rw [h]
  have : 2 ^ Nat.log 2 s ≤ s := Nat.pow_log_le_self 2 (by omega : s ≠ 0)
  calc 2 ^ (Nat.log 2 s + 1) = 2 * 2 ^ Nat.log 2 s := by ring
    _ ≤ 2 * s := by linarith

/--
Iterated polynomial ham-sandwich bisection. For any finite `X ⊆ ℝ²` and any
`k`, there exist polynomials `polys₀, …, polys_{k−1}` (all nonzero) with
`deg(polys i) ≤ 2^{⌊(i+1)/2⌋}` such that each of the `2^k` sign-pattern cells
contains at most `|X| / 2^k` points of `X`.
-/
theorem iterative_bisection (X : Finset (Fin 2 → ℝ)) :
    ∀ k : ℕ, ∃ (polys : Fin k → MvPolynomial (Fin 2) ℝ),
      (∀ i, polys i ≠ 0) ∧
      (∀ i : Fin k, (polys i).totalDegree ≤ 2 ^ ((i.val + 1) / 2)) ∧
      (∀ σ : Fin k → Bool, (signPatternCell X polys σ).card ≤ X.card / 2 ^ k) := by
  intro k
  induction k with
  | zero =>
    refine ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun σ => ?_⟩
    simp only [signPatternCell, Nat.pow_zero, Nat.div_one]
    exact Finset.card_filter_le _ _
  | succ k ih =>
    obtain ⟨polys_k, hne_k, hdeg_k, hsize_k⟩ := ih
    have hcard : Fintype.card (Fin k → Bool) ≤ (2 ^ ((k + 1) / 2)) ^ 2 := by
      rw [card_fin_bool_fun]; exact degree_bound_step k
    obtain ⟨p, hp_ne, hp_deg, hp_pos, hp_neg⟩ :=
      polynomial_ham_sandwich_finite (2 ^ ((k + 1) / 2)) hcard
        (fun σ => signPatternCell X polys_k σ)
    refine ⟨Fin.snoc polys_k p, ?_, ?_, ?_⟩
    · intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, hj⟩ | hi
      · subst hj; simp [Fin.snoc_castSucc]; exact hne_k j
      · subst hi; simp [Fin.snoc_last]; exact hp_ne
    · intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, hj⟩ | hi
      · subst hj; simp only [Fin.snoc_castSucc]
        calc (polys_k j).totalDegree ≤ 2 ^ ((j.val + 1) / 2) := hdeg_k j
          _ ≤ 2 ^ (((Fin.castSucc j).val + 1) / 2) := by simp [Fin.val_castSucc]
      · subst hi; simp only [Fin.snoc_last]
        calc p.totalDegree ≤ 2 ^ ((k + 1) / 2) := hp_deg
          _ ≤ 2 ^ (((Fin.last k).val + 1) / 2) := by simp [Fin.val_last]
    · intro σ
      set τ := Fin.init σ; set b := σ (Fin.last k)
      rw [show σ = Fin.snoc τ b from (Fin.snoc_init_self σ).symm]
      cases b
      · calc (signPatternCell X (Fin.snoc polys_k p) (Fin.snoc τ false)).card
            ≤ ((signPatternCell X polys_k τ).filter (fun x => eval x p < 0)).card :=
              Finset.card_le_card (signPatternCell_snoc_false_subset X polys_k p τ)
          _ ≤ (signPatternCell X polys_k τ).card / 2 := hp_neg τ
          _ ≤ (X.card / 2 ^ k) / 2 := Nat.div_le_div_right (hsize_k τ)
          _ = X.card / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul]; ring_nf
      · calc (signPatternCell X (Fin.snoc polys_k p) (Fin.snoc τ true)).card
            ≤ ((signPatternCell X polys_k τ).filter (fun x => eval x p > 0)).card :=
              Finset.card_le_card (signPatternCell_snoc_true_subset X polys_k p τ)
          _ ≤ (signPatternCell X polys_k τ).card / 2 := hp_pos τ
          _ ≤ (X.card / 2 ^ k) / 2 := Nat.div_le_div_right (hsize_k τ)
          _ = X.card / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul]; ring_nf

/--
Cell decomposition lemma (Szemerédi–Trotter). For any finite `X ⊆ ℝ²` and
integer `s ≥ 1`, the plane decomposes as `ℝ² = W ∪ ⋃ᵢ Oᵢ`, with the `Oᵢ`
pairwise disjoint open sets, `W` closed and disjoint from each `Oᵢ`, such that
every line meets `W` in at most `C s` points and each `Oᵢ` contains at most
`C |X| / s²` points of `X`. Obtained via iterated polynomial bisection.
-/
theorem cell_decomposition_lemma :
    ∃ (C : ℝ) (_ : C > 0), ∀ (X : Finset (Fin 2 → ℝ)) (s : ℕ) (_ : 1 ≤ s),
    ∃ (n : ℕ) (O : Fin n → Set (Fin 2 → ℝ)) (W : Set (Fin 2 → ℝ)),
      (∀ i, IsOpen (O i)) ∧
      IsClosed W ∧
      (W ∪ ⋃ i, O i = univ) ∧
      (Pairwise fun i j => Disjoint (O i) (O j)) ∧
      (∀ i, Disjoint (O i) W) ∧
      (∀ ℓ : Line2, Set.Finite ((↑ℓ.carrier : Set (Fin 2 → ℝ)) ∩ W) ∧
        (((↑ℓ.carrier : Set (Fin 2 → ℝ)) ∩ W).ncard : ℝ) ≤ C * s) ∧
      (∀ i, (((↑X : Set (Fin 2 → ℝ)) ∩ O i).ncard : ℝ) ≤ C * X.card / s ^ 2) := by

  refine ⟨8, by norm_num, fun X s hs => ?_⟩

  set k := 2 * Nat.log 2 s + 2

  obtain ⟨polys, hne, hdeg, hsize⟩ := iterative_bisection X k


  set n := 2 ^ k
  have hcard_eq : Fintype.card (Fin k → Bool) = n := card_fin_bool_fun k
  set equiv := (Fintype.equivFin (Fin k → Bool)).trans (finCongr hcard_eq)

  let O' := fun (σ : Fin k → Bool) => polyCell polys σ
  set W := polyWall polys
  set O := fun i : Fin n => O' (equiv.symm i)
  refine ⟨n, O, W, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro i; exact polyCell_isOpen polys (equiv.symm i)
  ·
    exact polyWall_isClosed polys
  ·
    have h := polyWall_union_cells polys
    ext x; constructor
    · intro _; exact mem_univ x
    · intro _
      have hx : x ∈ polyWall polys ∪ ⋃ σ : Fin k → Bool, polyCell polys σ := h ▸ mem_univ x
      rcases hx with hw | hc
      · left; exact hw
      · right
        rw [mem_iUnion] at hc ⊢
        obtain ⟨σ', hσ'⟩ := hc
        exact ⟨equiv σ', by simp [O, O', Equiv.symm_apply_apply]; exact hσ'⟩
  ·
    intro i j hij
    have hne_ij : equiv.symm i ≠ equiv.symm j := by
      intro h; exact hij (equiv.symm.injective h)
    exact polyCell_pairwise_disjoint polys hne_ij
  ·
    intro i; exact polyCell_disjoint_wall polys (equiv.symm i)
  ·
    intro ℓ
    constructor
    · exact polyWall_line_finite polys hne ℓ
    ·
      have h1 := polyWall_line_ncard polys hne ℓ
      have h2 : ∑ i : Fin k, (polys i).totalDegree ≤
          ∑ j ∈ Finset.range k, 2 ^ ((j + 1) / 2) := by
        rw [← Fin.sum_univ_eq_sum_range]
        exact Finset.sum_le_sum (fun i _ => hdeg i)
      have h3 := degree_sum_bound k
      have h4 := two_pow_half_log_bound s hs
      have h5 : 4 * 2 ^ (k / 2) ≤ 8 * s := by
        calc 4 * 2 ^ (k / 2) ≤ 4 * (2 * s) := by linarith [h4]
          _ = 8 * s := by ring
      calc (((↑ℓ.carrier : Set (Fin 2 → ℝ)) ∩ W).ncard : ℝ)
          ≤ (∑ i : Fin k, (polys i).totalDegree : ℝ) := by exact_mod_cast h1
        _ ≤ (∑ j ∈ Finset.range k, 2 ^ ((j + 1) / 2) : ℝ) := by exact_mod_cast h2
        _ ≤ (4 * 2 ^ (k / 2) : ℝ) := by exact_mod_cast h3
        _ ≤ (8 * s : ℝ) := by exact_mod_cast h5
        _ = 8 * (s : ℝ) := by push_cast; ring
  ·
    intro i
    have hσ := hsize (equiv.symm i)


    have hcell_eq : ((↑X : Set (Fin 2 → ℝ)) ∩ O i).ncard =
        (signPatternCell X polys (equiv.symm i)).card := by
      have : (↑X : Set (Fin 2 → ℝ)) ∩ O i =
          ↑(signPatternCell X polys (equiv.symm i)) := by
        ext x
        simp only [O, O', Set.mem_inter_iff, Finset.mem_coe, signPatternCell,
          Finset.mem_filter, polyCell, Set.mem_iInter]
        constructor
        · intro ⟨hx, hcell⟩; exact ⟨hx, fun j => by have := hcell j; split_ifs at this ⊢ <;> exact this⟩
        · intro ⟨hx, hcond⟩; exact ⟨hx, fun j => by have := hcond j; split_ifs at this ⊢ <;> exact this⟩
      rw [this, Set.ncard_coe_finset]
    rw [hcell_eq]

    have hs2 := two_pow_log_bound s hs
    have hdiv : X.card / 2 ^ k ≤ X.card / s ^ 2 := Nat.div_le_div_left hs2 (by positivity)
    have hs_pos : (s : ℝ) ^ 2 > 0 := by positivity
    have hXnn : (X.card : ℝ) ≥ 0 := Nat.cast_nonneg _
    have hnat_bound : (signPatternCell X polys (equiv.symm i)).card ≤ X.card / s ^ 2 := by
      exact le_trans hσ hdiv
    calc ((signPatternCell X polys (equiv.symm i)).card : ℝ)
        ≤ (↑(X.card / s ^ 2) : ℝ) := by exact_mod_cast hnat_bound
      _ ≤ (↑X.card : ℝ) / (↑s ^ 2 : ℝ) := by
          rw [le_div_iff₀ (by exact_mod_cast (show 0 < s ^ 2 from by positivity : 0 < s ^ 2))]
          exact_mod_cast Nat.div_mul_le_self X.card (s ^ 2)
      _ ≤ 8 * (↑X.card : ℝ) / (↑s) ^ 2 := by
          have h : (↑X.card : ℝ) / (↑s ^ 2 : ℝ) ≥ 0 := div_nonneg hXnn.le hs_pos.le
          rw [mul_div_assoc]
          exact le_mul_of_one_le_left h (by norm_num : (8 : ℝ) ≥ 1)

section
open Classical

end

end CellDecomposition
