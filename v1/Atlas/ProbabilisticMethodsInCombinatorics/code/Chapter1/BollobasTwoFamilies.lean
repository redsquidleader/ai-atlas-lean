/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SetFamily.LYM
import Mathlib.Data.Fintype.Perm
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.Order.Field.Basic

open Finset Nat BigOperators

namespace BollobasTwoFamilies

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- `goodPerms S T` is the set of permutations `σ` of `α` such that every element of `S`
appears before every element of `T` in the linear ordering induced by `σ`. -/
noncomputable def goodPerms (S T : Finset α) : Finset (Equiv.Perm α) :=
  Finset.univ.filter (fun σ =>
    ∀ s ∈ S, ∀ t ∈ T, (Fintype.equivFin α (σ s) : ℕ) < (Fintype.equivFin α (σ t) : ℕ))

/-- If `S₁ ∩ T₂` and `S₂ ∩ T₁` are both nonempty, the sets of good permutations
for `(S₁, T₁)` and `(S₂, T₂)` are disjoint, since a common permutation would force a
cyclic ordering contradiction. -/
lemma disjoint_goodPerms {S₁ T₁ S₂ T₂ : Finset α}
    (h₁ : (S₁ ∩ T₂).Nonempty) (h₂ : (S₂ ∩ T₁).Nonempty) :
    Disjoint (goodPerms S₁ T₁) (goodPerms S₂ T₂) := by
  simp only [goodPerms]
  apply Finset.disjoint_filter.mpr
  intro σ _ hσ₁ hσ₂
  obtain ⟨x, hx⟩ := h₁
  obtain ⟨y, hy⟩ := h₂
  rw [Finset.mem_inter] at hx hy
  have hxy := hσ₁ x hx.1 y hy.2
  have hyx := hσ₂ y hy.1 x hx.2
  exact absurd (lt_trans hxy hyx) (lt_irrefl _)

/-- For disjoint sets `S, T ⊆ α`, the number of permutations placing `S` before `T`
times $\binom{|S|+|T|}{|S|}$ equals $|\alpha|!$. -/
theorem card_goodPerms_mul_choose (S T : Finset α) (hST : Disjoint S T) :
    (goodPerms S T).card * (S.card + T.card).choose S.card =
      (Fintype.card α).factorial := by sorry

/-- The binomial coefficient $\binom{a+b}{a}$ is positive. -/
lemma choose_pos_of_add (a b : ℕ) : 0 < (a + b).choose a :=
  Nat.choose_pos (Nat.le_add_right a b)

/-- (Theorem 1.2.4, Bollobás Two Families Theorem, weighted form) Given families
$(A_i)_{i < m}$ and $(B_i)_{i < m}$ with $A_i \cap B_j = \varnothing$ iff $i = j$, then
$$\sum_{i < m} \binom{|A_i| + |B_i|}{|A_i|}^{-1} \le 1.$$ -/
theorem bollobas_two_families {m : ℕ} (A B : Fin m → Finset α)
    (cross : ∀ i j : Fin m, (A i) ∩ (B j) = ∅ ↔ i = j) :
    ∑ i : Fin m, (((A i).card + (B i).card).choose (A i).card : ℚ)⁻¹ ≤ 1 := by
  have hAB_disj : ∀ i : Fin m, Disjoint (A i) (B i) := by
    intro i; rw [Finset.disjoint_iff_inter_eq_empty]; exact (cross i i).mpr rfl
  have hAB_nonempty : ∀ i j : Fin m, i ≠ j → (A i ∩ B j).Nonempty := by
    intro i j hij; rw [Finset.nonempty_iff_ne_empty]; intro h; exact hij ((cross i j).mp h)
  have hpd : Pairwise (fun i j => Disjoint (goodPerms (A i) (B i)) (goodPerms (A j) (B j))) := by
    intro i j hij
    exact disjoint_goodPerms (hAB_nonempty i j hij) (hAB_nonempty j i (Ne.symm hij))
  have hsum_le : ∑ i : Fin m, (goodPerms (A i) (B i)).card ≤ (Fintype.card α).factorial := by
    have hle : (Finset.univ.biUnion (fun i => goodPerms (A i) (B i))).card ≤
        (Fintype.card α).factorial := by
      calc (Finset.univ.biUnion (fun i => goodPerms (A i) (B i))).card
          ≤ Fintype.card (Equiv.Perm α) := Finset.card_le_univ _
        _ = (Fintype.card α).factorial := Fintype.card_perm
    rw [Finset.card_biUnion (fun i _ j _ hij => hpd hij)] at hle; exact hle
  have hfact_pos : (0 : ℚ) < (Fintype.card α).factorial := by
    exact_mod_cast Nat.factorial_pos (Fintype.card α)
  have hkey : ∀ i : Fin m,
      (((A i).card + (B i).card).choose (A i).card : ℚ)⁻¹ =
      (goodPerms (A i) (B i)).card / (Fintype.card α).factorial := by
    intro i
    have hchoose := card_goodPerms_mul_choose (A i) (B i) (hAB_disj i)
    have hchoose_pos : (0 : ℚ) < ((A i).card + (B i).card).choose (A i).card :=
      by exact_mod_cast choose_pos_of_add _ _
    rw [inv_eq_one_div, div_eq_div_iff hchoose_pos.ne' hfact_pos.ne']
    rw [one_mul]; exact_mod_cast hchoose.symm
  have hfact_ne : (↑(Fintype.card α).factorial : ℚ) ≠ 0 := hfact_pos.ne'
  have hmain : (∑ i : Fin m, (((A i).card + (B i).card).choose (A i).card : ℚ)⁻¹) *
      ↑(Fintype.card α).factorial ≤ ↑(Fintype.card α).factorial := by
    calc (∑ i : Fin m, (((A i).card + (B i).card).choose (A i).card : ℚ)⁻¹) *
          ↑(Fintype.card α).factorial
        = ∑ i : Fin m, (((A i).card + (B i).card).choose (A i).card : ℚ)⁻¹ *
          ↑(Fintype.card α).factorial := by rw [Finset.sum_mul]
      _ = ∑ i : Fin m, (↑(goodPerms (A i) (B i)).card : ℚ) := by
          congr 1; ext i; rw [hkey i, div_mul_cancel₀ _ hfact_ne]
      _ ≤ ↑(Fintype.card α).factorial := by exact_mod_cast hsum_le
  exact (mul_le_iff_le_one_left hfact_pos).mp hmain

/-- (Theorem 1.2.6, Bollobás Two Families Theorem, uniform form) If all `A i` have size
`a` and all `B i` have size `b`, the cross condition implies $m \le \binom{a+b}{a}$. -/
theorem bollobas_two_families_uniform {m a b : ℕ} (A B : Fin m → Finset α)
    (hA : ∀ i, (A i).card = a) (hB : ∀ i, (B i).card = b)
    (cross : ∀ i j : Fin m, (A i) ∩ (B j) = ∅ ↔ i = j) :
    m ≤ (a + b).choose a := by
  have hgen := bollobas_two_families A B cross
  have hsimp : ∀ i : Fin m,
      (((A i).card + (B i).card).choose (A i).card : ℚ)⁻¹ =
      ((a + b).choose a : ℚ)⁻¹ := by
    intro i; rw [hA i, hB i]
  rw [show ∑ i : Fin m, (((A i).card + (B i).card).choose (A i).card : ℚ)⁻¹ =
      ∑ _i : Fin m, ((a + b).choose a : ℚ)⁻¹ from
      Finset.sum_congr rfl (fun i _ => hsimp i)] at hgen
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hgen
  have hchoose_pos : (0 : ℚ) < ((a + b).choose a : ℚ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_add_right a b)
  rw [nsmul_eq_mul] at hgen
  have hm_le : (m : ℚ) ≤ ((a + b).choose a : ℚ) := by
    calc (m : ℚ) = ↑m * 1 := (mul_one _).symm
      _ ≤ ↑m * (((a + b).choose a : ℚ)⁻¹ * ((a + b).choose a : ℚ)) := by
          rw [inv_mul_cancel₀ hchoose_pos.ne']
      _ = ↑m * ((a + b).choose a : ℚ)⁻¹ * ((a + b).choose a : ℚ) := by ring
      _ ≤ 1 * ((a + b).choose a : ℚ) := by
          apply mul_le_mul_of_nonneg_right hgen (le_of_lt hchoose_pos)
      _ = ((a + b).choose a : ℚ) := one_mul _
  exact_mod_cast hm_le

end BollobasTwoFamilies
