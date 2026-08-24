/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProjectionTheory.code.PolyKGrowth
import Atlas.ProjectionTheory.code.ContagiousStructure
import Atlas.ProjectionTheory.code.DoubleCountingFF

open Pointwise

namespace ProjectionTheory

/--
Contagious-structure lower bound underlying the dilated sumset expansion. For
exponents `0 < s_A < 1` and `0 < s_D`, there exist `r, c > 0` such that for any
prime `p`, any `A, D ⊆ 𝔽_p` with `|A| = p^{s_A}` and `|D| = p^{s_D}`, and any
`K ≥ 1` with `|A + t·A| ≤ K|A|` for all `t ∈ D`, one has `K^c ≥ p^r`. That is,
small dilated sumsets across a sufficiently large set of directions force `K`
itself to grow like a power of `p`.
-/
theorem sum_product_contagious_lower_bound
    (s_A s_D : ℝ) (hs_A_pos : 0 < s_A) (hs_A_lt : s_A < 1) (hs_D_pos : 0 < s_D) :
    ∃ (r c : ℝ), 0 < r ∧ 0 < c ∧
      ∀ (p : ℕ) [Fact (Nat.Prime p)] (A D : Finset (ZMod p)),
        A.Nonempty → D.Nonempty →
        (A.card : ℝ) = (p : ℝ) ^ s_A →
        (D.card : ℝ) = (p : ℝ) ^ s_D →
        ∀ (K : ℝ), K ≥ 1 →
        (∀ t ∈ D, ((A + t • A).card : ℝ) ≤ K * (A.card : ℝ)) →
        K ^ c ≥ (p : ℝ) ^ r := by sorry

/--
Dilated sumset expansion (Bourgain–Katz–Tao, finite field version). For
exponents `0 < s_A < 1` and `0 < s_D`, there exists `ε₁ > 0` such that for any
prime `p`, any `A, D ⊆ 𝔽_p` with `|A| = p^{s_A}` and `|D| = p^{s_D}`, there is
some direction `t ∈ D` for which `|A + t·A| ≥ p^{ε₁} |A|`. In other words, one
cannot have all dilated sumsets `A + t·A` simultaneously close in size to `A`.
-/
theorem exists_eps_dilated_sumset_expansion
    (s_A s_D : ℝ) (hs_A_pos : 0 < s_A) (hs_A_lt : s_A < 1) (hs_D_pos : 0 < s_D) :
    ∃ ε₁ : ℝ, ε₁ > 0 ∧
      ∀ (p : ℕ) [Fact (Nat.Prime p)] (A D : Finset (ZMod p)),
        A.Nonempty → D.Nonempty →
        (A.card : ℝ) = (p : ℝ) ^ s_A →
        (D.card : ℝ) = (p : ℝ) ^ s_D →
        ∃ t ∈ D, ((A + t • A).card : ℝ) ≥ (p : ℝ) ^ ε₁ * (A.card : ℝ) := by

  obtain ⟨r, c, hr_pos, hc_pos, hrc⟩ :=
    sum_product_contagious_lower_bound s_A s_D hs_A_pos hs_A_lt hs_D_pos

  refine ⟨r / (2 * c), by positivity, ?_⟩
  intro p _inst A D hA hD hAcard hDcard

  by_contra h_neg
  push Not at h_neg

  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime p).pos
  have hp_one : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt

  have h_le : ∀ t ∈ D, ((A + t • A).card : ℝ) ≤ (p : ℝ) ^ (r / (2 * c)) * (A.card : ℝ) :=
    fun t ht => le_of_lt (h_neg t ht)

  have hK_ge : (p : ℝ) ^ (r / (2 * c)) ≥ 1 :=
    Real.one_le_rpow hp_one.le (by positivity)

  have h_bound := hrc p A D hA hD hAcard hDcard ((p : ℝ) ^ (r / (2 * c))) hK_ge h_le


  have h_simp : ((p : ℝ) ^ (r / (2 * c))) ^ c = (p : ℝ) ^ (r / 2) := by
    rw [← Real.rpow_mul hp_pos.le]
    congr 1
    field_simp
  rw [h_simp] at h_bound


  have h_lt : (p : ℝ) ^ (r / 2) < (p : ℝ) ^ r :=
    Real.rpow_lt_rpow_of_exponent_lt hp_one (by linarith)
  linarith

/--
The sum-product set `A + A·A = {a + b·c : a, b, c ∈ A}` of a finite subset
`A ⊆ 𝔽_p`.
-/
noncomputable def sumProductSet {p : ℕ} [Fact (Nat.Prime p)]
    (A : Finset (ZMod p)) : Finset (ZMod p) :=
  A.biUnion (fun a => A.biUnion (fun b => A.image (fun c => a + b * c)))

/--
For any `t ∈ A`, the dilated sumset `A + t·A` is contained in the sum-product
set `A + A·A`.
-/
lemma dilated_sumset_subset_sumProductSet {p : ℕ} [Fact (Nat.Prime p)]
    (A : Finset (ZMod p)) (t : ZMod p) (ht : t ∈ A) :
    A + t • A ⊆ sumProductSet A := by
  intro x hx
  simp only [Finset.mem_add, Finset.mem_smul_finset] at hx
  obtain ⟨a, ha, y, ⟨c, hc, rfl⟩, rfl⟩ := hx
  simp only [sumProductSet, Finset.mem_biUnion, Finset.mem_image]
  exact ⟨a, ha, t, ht, c, hc, rfl⟩

/--
Specialization of `exists_eps_dilated_sumset_expansion` to the case `D = A`:
for `|A| = p^{s_A}` with `0 < s_A < 1`, there exists `ε > 0` and some `t ∈ A`
with `|A + t·A| ≥ p^ε |A|`.
-/
theorem sum_product_expansion
    (s_A : ℝ) (hs_A_pos : 0 < s_A) (hs_A_lt : s_A < 1) :
    ∃ ε : ℝ, ε > 0 ∧
      ∀ (p : ℕ) [Fact (Nat.Prime p)] (A : Finset (ZMod p)),
        A.Nonempty →
        (A.card : ℝ) = (p : ℝ) ^ s_A →
        ∃ t ∈ A, ((A + t • A).card : ℝ) ≥ (p : ℝ) ^ ε * (A.card : ℝ) := by

  obtain ⟨ε₁, hε₁_pos, hε₁⟩ :=
    exists_eps_dilated_sumset_expansion s_A s_A hs_A_pos hs_A_lt hs_A_pos
  exact ⟨ε₁, hε₁_pos, fun p _inst A hA hAcard =>
    hε₁ p A A hA hA hAcard hAcard⟩

/--
Sum-product expansion in `𝔽_p`: if `A ⊆ 𝔽_p` with `|A| = p^{s_A}` for
`0 < s_A < 1`, then `|A + A·A| ≥ p^{s_A + ε}` for some `ε = ε(s_A) > 0`.
This is the corollary `|A + A·A| ≥ p^{s_A + ε}` of the contagious-structure
analysis.
-/
theorem sum_product_set_expansion
    (s_A : ℝ) (hs_A_pos : 0 < s_A) (hs_A_lt : s_A < 1) :
    ∃ ε : ℝ, ε > 0 ∧
      ∀ (p : ℕ) [Fact (Nat.Prime p)] (A : Finset (ZMod p)),
        A.Nonempty →
        (A.card : ℝ) = (p : ℝ) ^ s_A →
        ((sumProductSet A).card : ℝ) ≥ (p : ℝ) ^ (s_A + ε) := by
  obtain ⟨ε, hε_pos, hε⟩ := sum_product_expansion s_A hs_A_pos hs_A_lt
  refine ⟨ε, hε_pos, fun p _inst A hA hAcard => ?_⟩
  obtain ⟨t, ht, htbound⟩ := hε p A hA hAcard
  have hsub := dilated_sumset_subset_sumProductSet A t ht
  have hcard_le : (A + t • A).card ≤ (sumProductSet A).card := Finset.card_le_card hsub
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime p).pos
  calc ((sumProductSet A).card : ℝ)
      ≥ ((A + t • A).card : ℝ) := by exact_mod_cast hcard_le
    _ ≥ (p : ℝ) ^ ε * (A.card : ℝ) := htbound
    _ = (p : ℝ) ^ ε * (p : ℝ) ^ s_A := by rw [hAcard]
    _ = (p : ℝ) ^ (s_A + ε) := by rw [← Real.rpow_add hp_pos]; ring_nf

end ProjectionTheory
