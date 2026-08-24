/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset Real

namespace SzemerediTrotter

/-- A line in $\mathbb{R}^2$: a $1$-dimensional non-empty affine subspace of $\mathbb{R}^2$. -/
structure Line2 where
  carrier : AffineSubspace ℝ (Fin 2 → ℝ)
  dim_eq : Module.finrank ℝ carrier.direction = 1
  nonempty : (carrier : Set (Fin 2 → ℝ)).Nonempty

/-- Membership of a point in a `Line2`: $p \in \ell$ iff $p$ belongs to the underlying
affine subspace. -/
instance : Membership (Fin 2 → ℝ) Line2 where
  mem l p := p ∈ l.carrier

/-- The incidence count $I(X, L) = \#\{(x, \ell) \in X \times L : x \in \ell\}$ between
a finite set of points $X \subset \mathbb{R}^2$ and a finite set of lines $L$. -/
noncomputable def incidenceCount (X : Finset (Fin 2 → ℝ)) (L : Finset Line2) : ℕ := by
  classical
  exact ((X ×ˢ L).filter fun p => p.1 ∈ p.2).card

/-- Two distinct points determine a unique line: if $p \ne q$ and both lie on two
lines $\ell_1, \ell_2$, then $\ell_1$ and $\ell_2$ have the same underlying affine
subspace. -/
lemma two_points_unique_line (p q : Fin 2 → ℝ) (hpq : p ≠ q)
    (ℓ₁ ℓ₂ : Line2) (hp1 : p ∈ ℓ₁) (hq1 : q ∈ ℓ₁) (hp2 : p ∈ ℓ₂) (hq2 : q ∈ ℓ₂) :
    ℓ₁.carrier = ℓ₂.carrier := by
  have hspan_le1 : affineSpan ℝ {p, q} ≤ ℓ₁.carrier :=
    affineSpan_pair_le_of_mem_of_mem hp1 hq1
  have hspan_le2 : affineSpan ℝ {p, q} ≤ ℓ₂.carrier :=
    affineSpan_pair_le_of_mem_of_mem hp2 hq2
  have hne : p -ᵥ q ≠ (0 : Fin 2 → ℝ) := vsub_ne_zero.mpr hpq
  have hfinrank_span : Module.finrank ℝ (affineSpan ℝ ({p, q} : Set (Fin 2 → ℝ))).direction = 1 := by
    rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton hne]
  have hnonempty : (affineSpan ℝ ({p, q} : Set (Fin 2 → ℝ)) : Set (Fin 2 → ℝ)).Nonempty :=
    ⟨p, subset_affineSpan ℝ _ (Set.mem_insert p {q})⟩
  have hdir_eq1 : (affineSpan ℝ ({p, q} : Set (Fin 2 → ℝ))).direction = ℓ₁.carrier.direction := by
    have h_le := AffineSubspace.direction_le hspan_le1
    exact le_antisymm h_le (Submodule.eq_of_le_of_finrank_le h_le
      (by rw [hfinrank_span, ℓ₁.dim_eq])).ge
  have h1 := AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir_eq1 hnonempty hspan_le1
  have hdir_eq2 : (affineSpan ℝ ({p, q} : Set (Fin 2 → ℝ))).direction = ℓ₂.carrier.direction := by
    have h_le := AffineSubspace.direction_le hspan_le2
    exact le_antisymm h_le (Submodule.eq_of_le_of_finrank_le h_le
      (by rw [hfinrank_span, ℓ₂.dim_eq])).ge
  have h2 := AffineSubspace.eq_of_direction_eq_of_nonempty_of_le hdir_eq2 hnonempty hspan_le2
  rw [← h1, ← h2]

/-- Extensionality for `Line2`: two lines are equal iff their carrier affine subspaces
are equal. -/
lemma Line2.ext' (ℓ₁ ℓ₂ : Line2) (h : ℓ₁.carrier = ℓ₂.carrier) : ℓ₁ = ℓ₂ := by
  cases ℓ₁; cases ℓ₂; simp at h; subst h; rfl

/-- **Weak incidence bound.** For any finite set of points $X$ and lines $L$ in
$\mathbb{R}^2$, the incidence count satisfies $I(X, L) \le |X| |L|^{1/2} + |L|$,
obtained by Cauchy--Schwarz together with the uniqueness of the line through two points. -/
theorem weak_bound_incidence (X : Finset (Fin 2 → ℝ)) (L : Finset Line2) :
    (incidenceCount X L : ℝ) ≤
      (X.card : ℝ) * (L.card : ℝ) ^ ((1 : ℝ) / 2) + (L.card : ℝ) := by
  classical

  have hI_eq : incidenceCount X L = ∑ l ∈ L, (X.filter (fun x => x ∈ l)).card := by
    unfold incidenceCount; simp only [Finset.card_filter]; rw [← Finset.sum_product_right']

  have hsum_sq : ∑ l ∈ L, (X.filter (fun x => x ∈ l)).card ^ 2 =
      incidenceCount X L + ∑ l ∈ L, ((X.filter (fun x => x ∈ l)).card *
        ((X.filter (fun x => x ∈ l)).card - 1)) := by
    rw [hI_eq, ← Finset.sum_add_distrib]
    congr 1; ext l
    have : ∀ n : ℕ, n ^ 2 = n + n * (n - 1) := by
      intro n; cases n with
      | zero => simp
      | succ m => simp; ring
    exact this _

  have hoff_eq : ∀ l ∈ L, (X.filter (fun x => x ∈ l)).card *
      ((X.filter (fun x => x ∈ l)).card - 1) =
      (X.filter (fun x => x ∈ l)).offDiag.card := by
    intro l _
    rw [Finset.offDiag_card, Nat.mul_sub_one]

  have hoff_bound : ∑ l ∈ L, (X.filter (fun x => x ∈ l)).offDiag.card ≤ X.offDiag.card := by
    let A : Line2 → Finset ((Fin 2 → ℝ) × (Fin 2 → ℝ)) :=
      fun l => (X.filter (fun x => x ∈ l)).offDiag
    have hpd : Set.PairwiseDisjoint (↑L : Set Line2) A := by
      intro l₁ _ l₂ _ hne
      simp only [Function.onFun, A]
      rw [Finset.disjoint_left]
      intro ⟨p, q⟩ hp hq
      simp only [Finset.mem_offDiag, Finset.mem_filter] at hp hq
      exact absurd (Line2.ext' l₁ l₂
        (two_points_unique_line p q hp.2.2 l₁ l₂ hp.1.2 hp.2.1.2 hq.1.2 hq.2.1.2)) hne
    have hsub : ∀ l ∈ L, A l ⊆ X.offDiag := by
      intro l _ ⟨p, q⟩ hp
      simp only [A, Finset.mem_offDiag, Finset.mem_filter] at hp ⊢
      exact ⟨hp.1.1, hp.2.1.1, hp.2.2⟩
    calc ∑ l ∈ L, (A l).card
        = (L.biUnion A).card := (Finset.card_biUnion hpd).symm
      _ ≤ X.offDiag.card := Finset.card_le_card (Finset.biUnion_subset.mpr hsub)

  have hXoff : X.offDiag.card ≤ X.card ^ 2 := by
    rw [Finset.offDiag_card, sq]; omega

  have hsum_sq_bound : (∑ l ∈ L, (X.filter (fun x => x ∈ l)).card ^ 2 : ℕ) ≤
      incidenceCount X L + X.card ^ 2 := by
    rw [hsum_sq]
    gcongr
    calc ∑ l ∈ L, ((X.filter (fun x => x ∈ l)).card *
            ((X.filter (fun x => x ∈ l)).card - 1))
        = ∑ l ∈ L, (X.filter (fun x => x ∈ l)).offDiag.card :=
          Finset.sum_congr rfl hoff_eq
      _ ≤ X.offDiag.card := hoff_bound
      _ ≤ X.card ^ 2 := hXoff

  have hCS : (∑ l ∈ L, ((X.filter (fun x => x ∈ l)).card : ℝ)) ^ 2 ≤
      (L.card : ℝ) * ∑ l ∈ L, (((X.filter (fun x => x ∈ l)).card : ℝ)) ^ 2 :=
    sq_sum_le_card_mul_sum_sq

  have hI_cast : (∑ l ∈ L, ((X.filter (fun x => x ∈ l)).card : ℝ)) =
      (incidenceCount X L : ℝ) := by
    rw [hI_eq]; push_cast; rfl

  have hI_sq : (incidenceCount X L : ℝ) ^ 2 ≤
      (L.card : ℝ) * ((incidenceCount X L : ℝ) + (X.card : ℝ) ^ 2) := by
    calc (incidenceCount X L : ℝ) ^ 2
        = (∑ l ∈ L, ((X.filter (fun x => x ∈ l)).card : ℝ)) ^ 2 := by rw [hI_cast]
      _ ≤ (L.card : ℝ) * ∑ l ∈ L, (((X.filter (fun x => x ∈ l)).card : ℝ)) ^ 2 := hCS
      _ ≤ (L.card : ℝ) * ((incidenceCount X L : ℝ) + (X.card : ℝ) ^ 2) := by
          gcongr; exact_mod_cast hsum_sq_bound

  rw [← Real.sqrt_eq_rpow]
  set I := (incidenceCount X L : ℝ)
  set Lc := (L.card : ℝ)
  set Xc := (X.card : ℝ)
  have hLc_nn : Lc ≥ 0 := by positivity
  have hXc_nn : Xc ≥ 0 := by positivity
  have h_ineq : I ^ 2 ≤ Lc * Xc ^ 2 + Lc * I := by linarith [hI_sq]
  by_contra hlt
  push Not at hlt
  have hsqrt : Real.sqrt Lc * Real.sqrt Lc = Lc := Real.mul_self_sqrt hLc_nn
  have h1 : I * (I - Lc) ≤ Lc * Xc ^ 2 := by nlinarith
  have hIL : I - Lc > Xc * Real.sqrt Lc := by linarith
  have hXsL_nn : Xc * Real.sqrt Lc ≥ 0 := mul_nonneg hXc_nn (Real.sqrt_nonneg Lc)
  have h2 : I * (I - Lc) > (Xc * Real.sqrt Lc + Lc) * (Xc * Real.sqrt Lc) := by
    nlinarith [hlt, hIL, hXsL_nn]
  have h3 : (Xc * Real.sqrt Lc + Lc) * (Xc * Real.sqrt Lc) ≥ Lc * Xc ^ 2 := by
    nlinarith [hsqrt, hXsL_nn, mul_nonneg hLc_nn hXsL_nn]
  linarith

open Classical in
/-- **Parametric cell-decomposition bound.** For any parameter $s \ge 1$,
$I(X, L) \le |X|^{2/3} |L|^{2/3} + |X|/s + s|L|$. Optimizing in $s$ yields the
Szemerédi--Trotter bound. -/
theorem cell_parametric_bound_sharp (X : Finset (Fin 2 → ℝ)) (L : Finset Line2)
    (s : ℝ) (hs : s ≥ 1) :
    (incidenceCount X L : ℝ) ≤
      (X.card : ℝ) ^ ((2 : ℝ) / 3) * (L.card : ℝ) ^ ((2 : ℝ) / 3) +
        (X.card : ℝ) / s + s * (L.card : ℝ) := by sorry

/-- **Szemerédi--Trotter incidence theorem.** For any finite set of points
$X \subset \mathbb{R}^2$ and lines $L$, $I(X, L) \le |X| + |L| + |X|^{2/3} |L|^{2/3}$. -/
theorem szemeredi_trotter (X : Finset (Fin 2 → ℝ)) (L : Finset Line2) :
    (incidenceCount X L : ℝ) ≤
      (X.card : ℝ) + (L.card : ℝ) +
        (X.card : ℝ) ^ ((2 : ℝ) / 3) * (L.card : ℝ) ^ ((2 : ℝ) / 3) := by
  set Xc := (X.card : ℝ)
  set Lc := (L.card : ℝ)


  have _hweak := weak_bound_incidence X L

  by_cases hXL : Xc ≥ Lc
  case pos =>

    rcases Nat.eq_zero_or_pos L.card with hL0 | hL_pos
    ·
      have h := cell_parametric_bound_sharp X L 1 (by norm_num : (1:ℝ) ≥ 1)
      simp only [div_one, one_mul] at h
      linarith
    ·
      have hL : Lc > 0 := Nat.cast_pos.mpr hL_pos
      have hX : Xc > 0 := lt_of_lt_of_le hL hXL
      have hxl_pos : Xc / Lc > 0 := div_pos hX hL
      have hs_pos : Real.sqrt (Xc / Lc) > 0 := Real.sqrt_pos_of_pos hxl_pos
      have hs_ge : Real.sqrt (Xc / Lc) ≥ 1 := by
        rw [ge_iff_le, ← Real.sqrt_one]
        exact Real.sqrt_le_sqrt (le_div_iff₀ hL |>.mpr (by linarith))
      have h := cell_parametric_bound_sharp X L (Real.sqrt (Xc / Lc)) hs_ge

      suffices hsuff : Xc / Real.sqrt (Xc / Lc) +
          Real.sqrt (Xc / Lc) * Lc ≤ Xc + Lc by linarith

      have h1 : Xc / Real.sqrt (Xc / Lc) = Real.sqrt (Xc * Lc) := by
        rw [div_eq_iff hs_pos.ne']; symm
        calc Real.sqrt (Xc * Lc) * Real.sqrt (Xc / Lc)
            = Real.sqrt (Xc * Lc * (Xc / Lc)) :=
              (Real.sqrt_mul (mul_nonneg hX.le hL.le) _).symm
          _ = Real.sqrt (Xc ^ 2) := by congr 1; field_simp
          _ = Xc := Real.sqrt_sq hX.le

      have h2 : Real.sqrt (Xc / Lc) * Lc = Real.sqrt (Xc * Lc) := by
        have h_sq : (Real.sqrt (Xc / Lc) * Lc) ^ 2 = Xc * Lc := by
          rw [mul_pow, Real.sq_sqrt hxl_pos.le]; field_simp
        nlinarith [Real.sqrt_nonneg (Xc * Lc),
                   Real.sq_sqrt (mul_nonneg hX.le hL.le),
                   sq_nonneg (Real.sqrt (Xc / Lc) * Lc - Real.sqrt (Xc * Lc)),
                   mul_nonneg (Real.sqrt_nonneg (Xc / Lc)) hL.le]
      rw [h1, h2]

      nlinarith [sq_nonneg (Real.sqrt Xc - Real.sqrt Lc),
                 Real.mul_self_sqrt hX.le, Real.mul_self_sqrt hL.le,
                 Real.sqrt_mul hX.le Lc, Real.sqrt_nonneg Xc, Real.sqrt_nonneg Lc]
  case neg =>

    push_neg at hXL
    have h := cell_parametric_bound_sharp X L 1 (by norm_num : (1:ℝ) ≥ 1)
    simp only [div_one, one_mul] at h
    linarith

/-- The subset of *$R$-rich lines*: lines $\ell \in L$ containing at least $R$ points of $X$. -/
noncomputable def rRichLines (X : Finset (Fin 2 → ℝ)) (L : Finset Line2) (R : ℕ) :
    Finset Line2 := by
  classical
  exact L.filter (fun l => R ≤ (X.filter (fun x => x ∈ l)).card)

/-- Lower bound: the total incidence count restricted to $R$-rich lines is at least
$R \cdot |L_R(X)|$, since each rich line contributes at least $R$ incidences. -/
lemma incidence_ge_R_mul_rRichLines (X : Finset (Fin 2 → ℝ)) (L : Finset Line2) (R : ℕ) :
    R * (rRichLines X L R).card ≤ incidenceCount X (rRichLines X L R) := by
  classical
  have hI_eq : incidenceCount X (rRichLines X L R) =
      ∑ l ∈ (rRichLines X L R), (X.filter (fun x => x ∈ l)).card := by
    unfold incidenceCount
    simp only [Finset.card_filter]
    rw [← Finset.sum_product_right']
  rw [hI_eq]
  have h : ∀ l ∈ rRichLines X L R, R ≤ (X.filter (fun x => x ∈ l)).card := by
    intro l hl; simp only [rRichLines, Finset.mem_filter] at hl; exact hl.2
  calc R * (rRichLines X L R).card
      = ∑ _l ∈ rRichLines X L R, R := by rw [Finset.sum_const]; ring
    _ ≤ ∑ l ∈ rRichLines X L R, (X.filter (fun x => x ∈ l)).card :=
        Finset.sum_le_sum h

set_option maxHeartbeats 800000 in
/-- **Bound on the number of $R$-rich lines.** As a corollary of Szemerédi--Trotter:
for $R \ge 2$, $|L_R(X)| \lesssim |X|^2/R^3 + |X|/R$. Here the constant is explicit ($C = 64$). -/
theorem r_rich_lines_bound (X : Finset (Fin 2 → ℝ)) (L : Finset Line2) (R : ℕ) (hR : 2 ≤ R) :
    ∃ C : ℝ, C > 0 ∧
    ((rRichLines X L R).card : ℝ) ≤
      C * ((X.card : ℝ) ^ 2 / (R : ℝ) ^ 3 + (X.card : ℝ) / (R : ℝ)) := by
  refine ⟨64, by norm_num, ?_⟩
  set LR := rRichLines X L R
  set N := (X.card : ℝ)
  set M := (LR.card : ℝ)
  set Rr := (R : ℝ)
  have hRr : Rr ≥ 2 := by change (R : ℝ) ≥ 2; exact_mod_cast hR
  have hN_nn : N ≥ 0 := by positivity
  have hM_nn : M ≥ 0 := by positivity

  have hlow := incidence_ge_R_mul_rRichLines X L R
  have hlow_r : Rr * M ≤ (incidenceCount X LR : ℝ) := by
    have : (↑(R * LR.card) : ℝ) ≤ ↑(incidenceCount X LR) := by exact_mod_cast hlow
    push_cast at this; linarith

  have hST := szemeredi_trotter X LR

  have hcomb : Rr * M ≤ N + M + N ^ ((2:ℝ)/3) * M ^ ((2:ℝ)/3) := by linarith
  have hR1_pos : Rr - 1 > 0 := by linarith
  have hRp : Rr > 0 := by linarith
  have hR3_pos : Rr ^ 3 > 0 := by positivity
  have h1 : (Rr - 1) * M ≤ N + N ^ ((2:ℝ)/3) * M ^ ((2:ℝ)/3) := by linarith
  rcases eq_or_lt_of_le hM_nn with hM0 | hM_pos
  · simp [show M = 0 from hM0.symm]; positivity

  suffices hsuff : M * Rr ^ 3 ≤ 64 * (N ^ 2 + N * Rr ^ 2) by
    have hgoal : 64 * (N ^ 2 / Rr ^ 3 + N / Rr) = 64 * (N ^ 2 + N * Rr ^ 2) / Rr ^ 3 := by
      field_simp
    rw [hgoal, le_div_iff₀ hR3_pos]; linarith

  by_cases hcase : N ^ ((2:ℝ)/3) * M ^ ((2:ℝ)/3) ≥ N
  ·
    have h2 : (Rr - 1) * M ≤ 2 * (N ^ ((2:ℝ)/3) * M ^ ((2:ℝ)/3)) := by linarith

    have hM_split : M = M ^ ((2:ℝ)/3) * M ^ ((1:ℝ)/3) := by
      rw [← rpow_add hM_pos]; norm_num
    have hM23_pos : M ^ ((2:ℝ)/3) > 0 := rpow_pos_of_pos hM_pos _
    have h3 : (Rr - 1) * M ^ ((1:ℝ)/3) ≤ 2 * N ^ ((2:ℝ)/3) := by
      rw [hM_split] at h2; nlinarith

    have hM13_nn : M ^ ((1:ℝ)/3) ≥ 0 := rpow_nonneg hM_nn _
    have hcube := pow_le_pow_left₀ (mul_nonneg hR1_pos.le hM13_nn) h3 3
    have hcube_lhs : ((Rr - 1) * M ^ ((1:ℝ)/3)) ^ (3:ℕ) = (Rr-1)^3 * M := by
      rw [mul_pow, ← rpow_natCast (M ^ ((1:ℝ)/3)) 3, ← rpow_mul hM_nn]; norm_num
    have hcube_rhs : (2 * N ^ ((2:ℝ)/3)) ^ (3:ℕ) = 8 * N ^ 2 := by
      rw [mul_pow, ← rpow_natCast (N ^ ((2:ℝ)/3)) 3, ← rpow_mul hN_nn]; norm_num
    have h4 : (Rr-1)^3 * M ≤ 8 * N^2 := by linarith [hcube, hcube_lhs, hcube_rhs]

    have hR_half : Rr - 1 ≥ Rr / 2 := by linarith
    have hR1_3 : (Rr-1)^3 ≥ Rr^3 / 8 := by
      have : (Rr/2)^3 ≤ (Rr-1)^3 := pow_le_pow_left₀ (by linarith) hR_half 3
      linarith [show (Rr/2)^3 = Rr^3/8 from by ring]
    have h5 : Rr^3 * M ≤ 64 * N ^ 2 := by nlinarith
    nlinarith [sq_nonneg N, sq_nonneg Rr]
  ·
    push Not at hcase
    have h2 : (Rr - 1) * M ≤ 2 * N := by linarith
    have h3 : M * Rr ≤ 4 * N := by nlinarith
    nlinarith [sq_nonneg N, sq_nonneg Rr, sq_nonneg (N*Rr)]

/-- The finite set of all lines spanned by pairs of distinct points of $X$. -/
noncomputable def allLinesFromPairs (X : Finset (Fin 2 → ℝ)) : Finset Line2 := by
  classical
  exact (X.offDiag.attach).image (fun ⟨pq, hpq⟩ =>
    { carrier := affineSpan ℝ {pq.1, pq.2}
      dim_eq := by
        have hne : pq.1 ≠ pq.2 := (Finset.mem_offDiag.mp hpq).2.2
        rw [direction_affineSpan, vectorSpan_pair, finrank_span_singleton (vsub_ne_zero.mpr hne)]
      nonempty := ⟨pq.1, subset_affineSpan ℝ _ (Set.mem_insert pq.1 {pq.2})⟩ })

/-- The set of $R$-rich lines among all lines spanned by pairs of points of $X$. -/
noncomputable def allRichLines (X : Finset (Fin 2 → ℝ)) (R : ℕ) : Finset Line2 :=
  rRichLines X (allLinesFromPairs X) R

/-- Bound on the number of $R$-rich lines (among all lines through point pairs of $X$):
$|L_R(X)| \lesssim |X|^2/R^3 + |X|/R$. -/
theorem r_rich_lines_bound_all (X : Finset (Fin 2 → ℝ)) (R : ℕ) (hR : 2 ≤ R) :
    ∃ C : ℝ, C > 0 ∧
    ((allRichLines X R).card : ℝ) ≤
      C * ((X.card : ℝ) ^ 2 / (R : ℝ) ^ 3 + (X.card : ℝ) / (R : ℝ)) :=
  r_rich_lines_bound X (allLinesFromPairs X) R hR

end SzemerediTrotter

noncomputable section

namespace ProjectionTheory

/-- The orthogonal projection of $p \in \mathbb{R}^2$ in the direction $\theta$,
i.e. $\pi_\theta(p) = p_0 \cos\theta + p_1 \sin\theta$. -/
def projR2 (θ : ℝ) (p : Fin 2 → ℝ) : ℝ :=
  p 0 * Real.cos θ + p 1 * Real.sin θ

/-- The image $\pi_\theta(X) \subset \mathbb{R}$ of a finite point set $X$ under the
direction-$\theta$ projection. -/
def projImageR2 (θ : ℝ) (X : Finset (Fin 2 → ℝ)) : Finset ℝ :=
  X.image (projR2 θ)

/-- The direction-$\theta$ projection $\pi_\theta : \mathbb{R}^2 \to \mathbb{R}$ packaged
as a linear map. -/
def projR2Lin (θ : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ where
  toFun := projR2 θ
  map_add' := fun x y => by simp [projR2]; ring
  map_smul' := fun c x => by simp [projR2]; ring

/-- The projection map $\pi_\theta : \mathbb{R}^2 \to \mathbb{R}$ is surjective. -/
lemma projR2Lin_surjective (θ : ℝ) : Function.Surjective (projR2Lin θ) := by
  intro y
  refine ⟨![y * Real.cos θ, y * Real.sin θ], ?_⟩
  simp only [projR2Lin, projR2, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  have key : y * Real.cos θ * Real.cos θ + y * Real.sin θ * Real.sin θ = y := by
    have : y * Real.cos θ * Real.cos θ + y * Real.sin θ * Real.sin θ
        = y * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
    rw [this, Real.cos_sq_add_sin_sq, mul_one]
  linarith [key]

/-- For $\theta \in [0, \pi)$, the kernel of $\pi_\theta$ is a $1$-dimensional subspace
of $\mathbb{R}^2$, so its fibers are honest lines. -/
lemma projR2Lin_ker_finrank (θ : ℝ) (hθ : 0 ≤ θ ∧ θ < Real.pi) :
    Module.finrank ℝ (LinearMap.ker (projR2Lin θ)) = 1 := by
  have h_rank_ker := (projR2Lin θ).finrank_range_add_finrank_ker
  have h_total : Module.finrank ℝ (Fin 2 → ℝ) = 2 := by simp
  rw [h_total] at h_rank_ker
  suffices h_range : Module.finrank ℝ (LinearMap.range (projR2Lin θ)) = 1 by omega
  have h_surj : LinearMap.range (projR2Lin θ) = ⊤ :=
    LinearMap.range_eq_top.mpr (projR2Lin_surjective θ)
  rw [h_surj]; simp [Module.finrank_self]

/-- The line through $p_0$ in direction $\theta \in [0, \pi)$: the fiber of $\pi_\theta$
passing through $p_0$, packaged as a `Line2`. -/
def mkProjLine (θ : ℝ) (hθ : 0 ≤ θ ∧ θ < Real.pi) (p₀ : Fin 2 → ℝ) :
    SzemerediTrotter.Line2 where
  carrier := AffineSubspace.mk' p₀ (LinearMap.ker (projR2Lin θ))
  dim_eq := by rw [AffineSubspace.direction_mk']; exact projR2Lin_ker_finrank θ hθ
  nonempty := ⟨p₀, by simp [AffineSubspace.mem_mk', sub_self]⟩

/-- A point $q$ lies on the line `mkProjLine θ p₀` iff $\pi_\theta(q) = \pi_\theta(p_0)$,
i.e. iff $q$ is on the same projection fiber as $p_0$. -/
lemma mem_mkProjLine_iff (θ : ℝ) (hθ : 0 ≤ θ ∧ θ < Real.pi) (p₀ q : Fin 2 → ℝ) :
    q ∈ (mkProjLine θ hθ p₀).carrier ↔ projR2 θ q = projR2 θ p₀ := by
  simp only [mkProjLine, AffineSubspace.mem_mk', LinearMap.mem_ker,
    projR2Lin, LinearMap.coe_mk, AddHom.coe_mk, projR2, Pi.sub_apply, vsub_eq_sub]
  constructor <;> intro h <;> linarith

/-- Two projection lines through $p_0$ and $q_0$ in direction $\theta$ coincide iff
$\pi_\theta(p_0) = \pi_\theta(q_0)$. -/
lemma mkProjLine_eq_iff (θ : ℝ) (hθ : 0 ≤ θ ∧ θ < Real.pi) (p₀ q₀ : Fin 2 → ℝ) :
    mkProjLine θ hθ p₀ = mkProjLine θ hθ q₀ ↔ projR2 θ p₀ = projR2 θ q₀ := by
  constructor
  · intro h
    have hq : q₀ ∈ (mkProjLine θ hθ p₀).carrier := by
      rw [h]; exact (mem_mkProjLine_iff θ hθ q₀ q₀).mpr rfl
    exact ((mem_mkProjLine_iff θ hθ p₀ q₀).mp hq).symm
  · intro h
    suffices h_carrier : (mkProjLine θ hθ p₀).carrier = (mkProjLine θ hθ q₀).carrier by
      exact match mkProjLine θ hθ p₀, mkProjLine θ hθ q₀, h_carrier with
      | ⟨c₁, d₁, n₁⟩, ⟨c₂, d₂, n₂⟩, hc => by simp_all
    simp only [mkProjLine]
    have hvsub : q₀ -ᵥ p₀ ∈ LinearMap.ker (projR2Lin θ) := by
      simp only [LinearMap.mem_ker, projR2Lin, LinearMap.coe_mk, AddHom.coe_mk,
        projR2, vsub_eq_sub, Pi.sub_apply]
      have : projR2 θ q₀ - projR2 θ p₀ =
          (q₀ 0 - p₀ 0) * Real.cos θ + (q₀ 1 - p₀ 1) * Real.sin θ := by
        simp [projR2]; ring
      linarith [this]
    have hq_in_p : q₀ ∈ (AffineSubspace.mk' p₀ (LinearMap.ker (projR2Lin θ)) :
        AffineSubspace ℝ (Fin 2 → ℝ)) := by
      rw [AffineSubspace.mem_mk']; exact hvsub
    calc AffineSubspace.mk' p₀ (LinearMap.ker (projR2Lin θ))
        = AffineSubspace.mk' q₀
            (AffineSubspace.mk' p₀ (LinearMap.ker (projR2Lin θ))).direction :=
          (AffineSubspace.mk'_eq hq_in_p).symm
      _ = AffineSubspace.mk' q₀ (LinearMap.ker (projR2Lin θ)) := by
          rw [AffineSubspace.direction_mk']

/-- General image-counting lemma: if $g(a_1) = g(a_2)$ implies $f(a_1) = f(a_2)$ on
$s$, then $|f(s)| \le |g(s)|$. Used to compare the cardinality of two images via a
factoring through one of them. -/
lemma card_image_le_of_eq_imp {α β γ : Type*} [DecidableEq β] [DecidableEq γ]
    (s : Finset α) (f : α → β) (g : α → γ)
    (h : ∀ a₁ ∈ s, ∀ a₂ ∈ s, g a₁ = g a₂ → f a₁ = f a₂)
    (hs : s.Nonempty) :
    (s.image f).card ≤ (s.image g).card := by
  classical
  obtain ⟨a₀, ha₀⟩ := hs
  let φ : γ → β := fun c => if hc : ∃ a ∈ s, g a = c then f hc.choose else f a₀
  suffices hsub : s.image f ⊆ (s.image g).image φ by
    calc (s.image f).card ≤ ((s.image g).image φ).card := Finset.card_le_card hsub
      _ ≤ (s.image g).card := Finset.card_image_le
  intro b hb
  obtain ⟨a, ha_s, ha_f⟩ := Finset.mem_image.mp hb
  rw [Finset.mem_image]
  refine ⟨g a, Finset.mem_image.mpr ⟨a, ha_s, rfl⟩, ?_⟩
  show φ (g a) = b
  simp only [φ]
  have hex : ∃ a' ∈ s, g a' = g a := ⟨a, ha_s, rfl⟩
  rw [dif_pos hex]
  have := h _ hex.choose_spec.1 _ ha_s hex.choose_spec.2
  rw [this, ha_f]

set_option maxHeartbeats 400000 in
/-- Algebraic key lemma: from the Szemerédi--Trotter incidence inequality
$X D \le X + S D + X^{2/3} (SD)^{2/3}$ with $2S < X$ and $D \ge 2$, deduce the
projection bound $D \le 144 \cdot S^2 / X + 1$. -/
lemma proj_bound_of_st_ineq (Xr Sr Dr : ℝ)
    (hXr : Xr > 0) (hSr : Sr ≥ 1) (hDr : Dr ≥ 2)
    (h2S : 2 * Sr < Xr)
    (hST : Xr * Dr ≤ Xr + Sr * Dr + Xr ^ ((2 : ℝ) / 3) * (Sr * Dr) ^ ((2 : ℝ) / 3)) :
    Dr ≤ 144 * Sr ^ 2 * Xr⁻¹ + 1 := by
  have hDr_pos : Dr > 0 := by linarith
  have hSr_pos : Sr > 0 := by linarith
  have hSDr_pos : Sr * Dr > 0 := mul_pos hSr_pos hDr_pos
  have hSDr_nn : Sr * Dr ≥ 0 := hSDr_pos.le
  have h_cube_R : (Xr ^ ((2:ℝ)/3) * (Sr * Dr) ^ ((2:ℝ)/3)) ^ 3 = Xr ^ 2 * (Sr * Dr) ^ 2 := by
    rw [mul_pow, ← Real.rpow_natCast (Xr ^ ((2:ℝ)/3)) 3, ← Real.rpow_mul hXr.le]
    norm_num
    rw [← Real.rpow_natCast ((Sr * Dr) ^ ((2:ℝ)/3)) 3, ← Real.rpow_mul hSDr_nn]
    norm_num
  have hR_nn : Xr ^ ((2:ℝ)/3) * (Sr * Dr) ^ ((2:ℝ)/3) ≥ 0 :=
    mul_nonneg (Real.rpow_nonneg hXr.le _) (Real.rpow_nonneg hSDr_nn _)
  have hXm2S_le_R : Xr - 2 * Sr ≤ Xr ^ ((2:ℝ)/3) * (Sr * Dr) ^ ((2:ℝ)/3) := by nlinarith
  have hXm2S_pos : Xr - 2 * Sr > 0 := by linarith
  have h_cube_exp : (Xr - 2 * Sr) ^ 3 ≤ Xr ^ 2 * Sr ^ 2 * Dr ^ 2 :=
    calc (Xr - 2 * Sr) ^ 3
        ≤ (Xr ^ ((2:ℝ)/3) * (Sr * Dr) ^ ((2:ℝ)/3)) ^ 3 :=
          pow_le_pow_left₀ hXm2S_pos.le hXm2S_le_R 3
      _ = Xr ^ 2 * (Sr * Dr) ^ 2 := h_cube_R
      _ = Xr ^ 2 * Sr ^ 2 * Dr ^ 2 := by ring
  have hR_bound : Xr * (Dr - 2) / 2 ≤ Xr ^ ((2:ℝ)/3) * (Sr * Dr) ^ ((2:ℝ)/3) := by nlinarith
  have hLHS_nn : Xr * (Dr - 2) / 2 ≥ 0 :=
    div_nonneg (mul_nonneg hXr.le (by linarith : Dr - 2 ≥ 0)) (by norm_num : (2:ℝ) ≥ 0)
  have h_simp : Xr * (Dr - 2) ^ 3 ≤ 8 * Sr ^ 2 * Dr ^ 2 := by
    have h_cubed : (Xr * (Dr - 2) / 2) ^ 3 ≤ Xr ^ 2 * Sr ^ 2 * Dr ^ 2 :=
      calc (Xr * (Dr - 2) / 2) ^ 3
          ≤ (Xr ^ ((2:ℝ)/3) * (Sr * Dr) ^ ((2:ℝ)/3)) ^ 3 :=
            pow_le_pow_left₀ hLHS_nn hR_bound 3
        _ = Xr ^ 2 * (Sr * Dr) ^ 2 := h_cube_R
        _ = Xr ^ 2 * Sr ^ 2 * Dr ^ 2 := by ring
    have h_exp : (Xr * (Dr - 2) / 2) ^ 3 = Xr ^ 3 * (Dr - 2) ^ 3 / 8 := by ring
    have h1 : Xr ^ 3 * (Dr - 2) ^ 3 ≤ 8 * (Xr ^ 2 * Sr ^ 2 * Dr ^ 2) := by linarith [h_exp]
    have hXr2 : (0 : ℝ) < Xr ^ 2 := by positivity
    have h1' : Xr ^ 2 * (Xr * (Dr - 2) ^ 3) ≤ Xr ^ 2 * (8 * Sr ^ 2 * Dr ^ 2) := by
      ring_nf; ring_nf at h1; linarith
    linarith [le_of_mul_le_mul_of_pos_left h1' hXr2]
  suffices h : (Dr - 1) * Xr ≤ 144 * Sr ^ 2 by
    nlinarith [mul_inv_cancel₀ (ne_of_gt hXr), inv_pos.mpr hXr]
  by_cases hDr4 : Dr ≥ 4
  · have h1 : (Dr / 2) ^ 3 ≤ (Dr - 2) ^ 3 :=
      pow_le_pow_left₀ (by linarith : (0:ℝ) ≤ Dr / 2) (by linarith : Dr / 2 ≤ Dr - 2) 3
    have h5 : Xr * Dr ≤ 64 * Sr ^ 2 := by
      have hDr2_pos : Dr ^ 2 > 0 := by positivity
      nlinarith [h1, h_simp]
    nlinarith
  · simp only [not_le] at hDr4
    have h_cube_small : (Xr - 2 * Sr) ^ 3 ≤ 16 * Sr ^ 2 * Xr ^ 2 := by
      have hDr2 : Dr ^ 2 < 16 := by nlinarith [sq_nonneg (4 - Dr)]
      nlinarith [sq_nonneg (Xr * Sr)]
    by_contra h_neg
    simp only [not_le] at h_neg
    have hXr_large : Xr > 48 * Sr ^ 2 := by nlinarith
    have h4 : 2 * Sr < Xr / 24 := by nlinarith [sq_nonneg (Sr - 1)]
    have h6 : (23 * Xr / 24) ^ 3 ≤ 16 * Sr ^ 2 * Xr ^ 2 :=
      calc (23 * Xr / 24) ^ 3
          ≤ (Xr - 2 * Sr) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
        _ ≤ 16 * Sr ^ 2 * Xr ^ 2 := h_cube_small
    have h_exp6 : (23 * Xr / 24) ^ 3 = 12167 * Xr ^ 3 / 13824 := by ring
    have h7 : 12167 * Xr ^ 3 ≤ 221184 * Sr ^ 2 * Xr ^ 2 := by nlinarith [h_exp6]
    have hXr2_pos : (0 : ℝ) < Xr ^ 2 := by positivity
    have h7' : Xr ^ 2 * (12167 * Xr) ≤ Xr ^ 2 * (221184 * Sr ^ 2) := by
      ring_nf; ring_nf at h7; linarith
    have h8 : 12167 * Xr ≤ 221184 * Sr ^ 2 :=
      le_of_mul_le_mul_of_pos_left h7' hXr2_pos
    nlinarith [sq_nonneg Sr]

/-- **Fiber lines construction.** Given a set $X \subset \mathbb{R}^2$, a set of
directions $D \subset [0, \pi)$, and an upper bound $|\pi_\theta(X)| \le S$ for every
$\theta \in D$, one can construct a set of lines $L$ with $|L| \le S |D|$ and
$|X| \cdot |D| \le I(X, L)$ (each point lies on exactly $|D|$ fibers). -/
lemma fiber_lines_st_bound (X : Finset (Fin 2 → ℝ)) (S : ℕ) (D : Finset ℝ)
    (hDr : ∀ θ ∈ D, 0 ≤ θ ∧ θ < Real.pi)
    (hSb : ∀ θ ∈ D, (projImageR2 θ X).card ≤ S)
    (hX : X.Nonempty) :
    ∃ L : Finset SzemerediTrotter.Line2,
      L.card ≤ S * D.card ∧
      X.card * D.card ≤ SzemerediTrotter.incidenceCount X L := by
  classical

  let L : Finset SzemerediTrotter.Line2 :=
    D.biUnion (fun θ => if h : 0 ≤ θ ∧ θ < Real.pi then X.image (mkProjLine θ h) else ∅)
  refine ⟨L, ?_, ?_⟩
  ·
    calc L.card
        ≤ ∑ θ ∈ D, (if h : 0 ≤ θ ∧ θ < Real.pi
            then X.image (mkProjLine θ h) else ∅).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _θ ∈ D, S := by
          apply Finset.sum_le_sum
          intro θ hθD
          simp only [hDr θ hθD]
          calc (X.image (mkProjLine θ (hDr θ hθD))).card
              ≤ (X.image (projR2 θ)).card := by
                apply card_image_le_of_eq_imp X (mkProjLine θ (hDr θ hθD)) (projR2 θ)
                · intro a₁ _ a₂ _ heq
                  exact (mkProjLine_eq_iff θ (hDr θ hθD) a₁ a₂).mpr heq
                · exact hX
            _ ≤ S := hSb θ hθD
      _ = S * D.card := by simp [Finset.sum_const, mul_comm]
  ·

    show X.card * D.card ≤ SzemerediTrotter.incidenceCount X L
    unfold SzemerediTrotter.incidenceCount
    rw [show X.card * D.card = (X ×ˢ D).card from (Finset.card_product X D).symm]
    let f : (Fin 2 → ℝ) × ℝ → (Fin 2 → ℝ) × SzemerediTrotter.Line2 :=
      fun p => if h : p.2 ∈ D then (p.1, mkProjLine p.2 (hDr p.2 h) p.1)
        else (p.1, mkProjLine 0 ⟨le_refl 0, Real.pi_pos⟩ p.1)
    apply Finset.card_le_card_of_injOn f
    ·
      intro p hp
      have hmem := Finset.mem_product.mp hp
      simp only [f, hmem.2, dite_true, Finset.mem_coe, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hmem.1, Finset.mem_biUnion.mpr ⟨p.2, hmem.2,
        by simp [hDr p.2 hmem.2, Finset.mem_image]; exact ⟨p.1, hmem.1, rfl⟩⟩⟩,
        (mem_mkProjLine_iff p.2 (hDr p.2 hmem.2) p.1 p.1).mpr rfl⟩
    ·
      intro p₁ hp₁ p₂ hp₂ heq
      have hmem₁ := Finset.mem_product.mp hp₁
      have hmem₂ := Finset.mem_product.mp hp₂
      simp only [f, hmem₁.2, hmem₂.2, dite_true, Prod.mk.injEq] at heq
      have hx_eq := heq.1
      have hline_eq := heq.2

      have hcarr : (mkProjLine p₁.2 (hDr p₁.2 hmem₁.2) p₁.1).carrier =
          (mkProjLine p₂.2 (hDr p₂.2 hmem₂.2) p₂.1).carrier := congr_arg _ hline_eq
      simp only [mkProjLine] at hcarr
      rw [hx_eq] at hcarr
      have hdir : LinearMap.ker (projR2Lin p₁.2) = LinearMap.ker (projR2Lin p₂.2) := by
        have hd := AffineSubspace.direction_mk' p₂.1 (LinearMap.ker (projR2Lin p₁.2))
        rw [hcarr] at hd
        rw [← hd, AffineSubspace.direction_mk']
      have hv_ker1 : (![- Real.sin p₁.2, Real.cos p₁.2] : Fin 2 → ℝ) ∈
          LinearMap.ker (projR2Lin p₁.2) := by
        simp [LinearMap.mem_ker, projR2Lin, projR2, Matrix.cons_val_zero,
          Matrix.cons_val_one]; ring
      have hv_ker2 := hdir ▸ hv_ker1
      simp only [LinearMap.mem_ker, projR2Lin, projR2, LinearMap.coe_mk, AddHom.coe_mk,
        Matrix.cons_val_zero, Matrix.cons_val_one] at hv_ker2
      have hsin : Real.sin (p₂.2 - p₁.2) = 0 := by rw [Real.sin_sub]; linarith
      have hθ₁ := hDr p₁.2 hmem₁.2
      have hθ₂ := hDr p₂.2 hmem₂.2
      have hdiff := (Real.sin_eq_zero_iff_of_lt_of_lt
        (by linarith [hθ₁.1, hθ₁.2, hθ₂.1, hθ₂.2] : -Real.pi < p₂.2 - p₁.2)
        (by linarith [hθ₁.1, hθ₁.2, hθ₂.1, hθ₂.2] : p₂.2 - p₁.2 < Real.pi)).mp hsin
      exact Prod.ext hx_eq (by linarith)

set_option maxHeartbeats 800000 in
/-- **Szemerédi--Trotter projection theorem.** There exists a universal constant $C > 0$
such that for any finite point set $X \subset \mathbb{R}^2$, set of directions
$D \subset [0, \pi)$, and bound $|\pi_\theta(X)| \le S$ for $\theta \in D$, if $2S < |X|$
then $|D| \le C \cdot S^2 / |X| + 1$. -/
theorem szemeredi_trotter_proj :
    ∃ C : ℝ, C > 0 ∧ ∀ (X : Finset (Fin 2 → ℝ)) (S : ℕ) (D : Finset ℝ),
      (∀ θ ∈ D, 0 ≤ θ ∧ θ < Real.pi) →
      (∀ θ ∈ D, (projImageR2 θ X).card ≤ S) →
      2 * S < X.card →
      (D.card : ℝ) ≤ C * (S : ℝ) ^ 2 * (X.card : ℝ)⁻¹ + 1 := by
  refine ⟨144, by norm_num, fun X S D hDr hSb h2S => ?_⟩

  rcases Finset.eq_empty_or_nonempty X with hXe | hXne
  · simp [hXe] at h2S

  by_cases hD1 : D.card ≤ 1
  · have h1 : (D.card : ℝ) ≤ 1 := by exact_mod_cast hD1
    linarith [mul_nonneg (mul_nonneg (by norm_num : (144:ℝ) ≥ 0) (sq_nonneg (S:ℝ)))
                          (inv_nonneg.mpr (Nat.cast_nonneg' X.card))]
  · push_neg at hD1
    have hDge2 : D.card ≥ 2 := by omega

    obtain ⟨L, hLcard, hIncid⟩ := fiber_lines_st_bound X S D hDr hSb hXne

    have hST := SzemerediTrotter.szemeredi_trotter X L

    have hXpos : (X.card : ℝ) > 0 := by exact_mod_cast Finset.card_pos.mpr hXne
    have hSge1 : (S : ℝ) ≥ 1 := by
      have hDne : D.Nonempty := Finset.card_pos.mp (by omega : 0 < D.card)
      obtain ⟨θ, hθD⟩ := hDne
      have himg_ne : (projImageR2 θ X).Nonempty := Finset.image_nonempty.mpr hXne
      have : 1 ≤ S := le_trans (Finset.card_pos.mpr himg_ne) (hSb θ hθD)
      exact_mod_cast this
    have hDr2 : (D.card : ℝ) ≥ 2 := by exact_mod_cast hDge2
    have h2Sr : 2 * (S : ℝ) < (X.card : ℝ) := by exact_mod_cast h2S

    have hI_le : (X.card : ℝ) * (D.card : ℝ) ≤
        (X.card : ℝ) + (S : ℝ) * (D.card : ℝ) +
        (X.card : ℝ) ^ ((2:ℝ)/3) * ((S : ℝ) * (D.card : ℝ)) ^ ((2:ℝ)/3) := by
      have hIncid_r : (X.card : ℝ) * (D.card : ℝ) ≤
          (SzemerediTrotter.incidenceCount X L : ℝ) := by
        exact_mod_cast hIncid
      have hLcard_r : (L.card : ℝ) ≤ (S : ℝ) * (D.card : ℝ) := by exact_mod_cast hLcard
      calc (X.card : ℝ) * (D.card : ℝ)
          ≤ (SzemerediTrotter.incidenceCount X L : ℝ) := hIncid_r
        _ ≤ (X.card : ℝ) + (L.card : ℝ) +
            (X.card : ℝ) ^ ((2:ℝ)/3) * (L.card : ℝ) ^ ((2:ℝ)/3) := hST
        _ ≤ (X.card : ℝ) + (S : ℝ) * (D.card : ℝ) +
            (X.card : ℝ) ^ ((2:ℝ)/3) * ((S : ℝ) * (D.card : ℝ)) ^ ((2:ℝ)/3) := by
          gcongr

    exact proj_bound_of_st_ineq (X.card : ℝ) (S : ℝ) (D.card : ℝ)
      hXpos hSge1 hDr2 h2Sr hI_le

end ProjectionTheory
