/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.FiniteTensorCategory

open Finset CategoryTheory

namespace CategoryTheory.FiniteTensorCategoryData

variable (D : FiniteTensorCategoryData)

/-- Extract the absorption identity at the Grothendieck-ring level from a
left-`Hom`-level absorption hypothesis by specialising `homDim` to a Kronecker
delta. -/
theorem absorption_identity_K0_level
    (fpDimZ : ℝ)
    (tensorDecomp : D.ι → D.ι → ℝ)
    (h_hom_level : ∀ (homDim : D.ι → D.ι → ℝ),
      ∀ j : D.ι,
        (∑ i : D.ι, D.fpDimSimple i *
          (∑ k : D.ι, tensorDecomp i k * homDim k j)) =
          fpDimZ * (∑ i : D.ι, D.fpDimSimple i * homDim i j)) :
    ∀ j : D.ι,
      (∑ i : D.ι, D.fpDimSimple i * tensorDecomp i j) =
        fpDimZ * D.fpDimSimple j := by
  intro j
  have h := h_hom_level (fun k j' => if k = j' then 1 else 0) j
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at h
  exact h

/-- The right-handed analogue of `absorption_identity_K0_level`: extract the
absorption identity at the Grothendieck-ring level from a right-`Hom`-level
absorption hypothesis. -/
theorem absorption_identity_K0_level_right
    (fpDimZ : ℝ)
    (tensorDecompRight : D.ι → D.ι → ℝ)
    (h_hom_level_right : ∀ (homDim : D.ι → D.ι → ℝ),
      ∀ j : D.ι,
        (∑ i : D.ι, D.fpDimSimple i *
          (∑ k : D.ι, tensorDecompRight i k * homDim k j)) =
          fpDimZ * (∑ i : D.ι, D.fpDimSimple i * homDim i j)) :
    ∀ j : D.ι,
      (∑ i : D.ι, D.fpDimSimple i * tensorDecompRight i j) =
        fpDimZ * D.fpDimSimple j := by
  intro j
  have h := h_hom_level_right (fun k j' => if k = j' then 1 else 0) j
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at h
  exact h

/-- Absorption identity on the Grothendieck ring: the regular object satisfies the
expected eigenvalue relation with respect to the fusion coefficients. -/
theorem regularObject_absorption_Gr
    (N : D.ι → D.ι → D.ι → ℕ)
    (h_N : ∀ (j i : D.ι),
      (∑ k : D.ι, (N j i k : ℝ) * D.fpDimSimple k) =
        D.fpDimSimple j * D.fpDimSimple i) :
    ∀ (j : D.ι) (k : D.ι),
      (∑ i : D.ι, (N j i k : ℝ) * D.fpDimSimple i) =
        D.fpDimSimple j * D.fpDimSimple k := by sorry

/-- Proposition 1.47.7 (Etingof–Gelaki–Nikshych–Ostrik): The regular object of a
finite tensor category is absorbing for the Frobenius–Perron pairing both on the
left and on the right, the two absorption identities agree, and the absorption
identity holds at the Grothendieck-ring level. -/
theorem Proposition_1_47_7_regular_absorption
    (N : D.ι → D.ι → D.ι → ℕ)
    (h_N : ∀ (j i : D.ι),
      (∑ k : D.ι, (N j i k : ℝ) * D.fpDimSimple k) =
        D.fpDimSimple j * D.fpDimSimple i) :

    (∀ (fpDimZ : ℝ) (tensorDecomp : D.ι → D.ι → ℝ),
      (∀ (homDim : D.ι → D.ι → ℝ), ∀ j : D.ι,
        (∑ i : D.ι, D.fpDimSimple i *
          (∑ k : D.ι, tensorDecomp i k * homDim k j)) =
          fpDimZ * (∑ i : D.ι, D.fpDimSimple i * homDim i j)) →
      ∀ j : D.ι,
        (∑ i : D.ι, D.fpDimSimple i * tensorDecomp i j) =
          fpDimZ * D.fpDimSimple j) ∧

    (∀ (fpDimZ : ℝ) (tensorDecompRight : D.ι → D.ι → ℝ),
      (∀ (homDim : D.ι → D.ι → ℝ), ∀ j : D.ι,
        (∑ i : D.ι, D.fpDimSimple i *
          (∑ k : D.ι, tensorDecompRight i k * homDim k j)) =
          fpDimZ * (∑ i : D.ι, D.fpDimSimple i * homDim i j)) →
      ∀ j : D.ι,
        (∑ i : D.ι, D.fpDimSimple i * tensorDecompRight i j) =
          fpDimZ * D.fpDimSimple j) ∧

    (∀ (fpDimZ : ℝ) (tensorDecompLeft tensorDecompRight : D.ι → D.ι → ℝ),
      (∀ (homDim : D.ι → D.ι → ℝ), ∀ j : D.ι,
        (∑ i : D.ι, D.fpDimSimple i *
          (∑ k : D.ι, tensorDecompLeft i k * homDim k j)) =
          fpDimZ * (∑ i : D.ι, D.fpDimSimple i * homDim i j)) →
      (∀ (homDim : D.ι → D.ι → ℝ), ∀ j : D.ι,
        (∑ i : D.ι, D.fpDimSimple i *
          (∑ k : D.ι, tensorDecompRight i k * homDim k j)) =
          fpDimZ * (∑ i : D.ι, D.fpDimSimple i * homDim i j)) →
      ∀ j : D.ι,
        (∑ i : D.ι, D.fpDimSimple i * tensorDecompLeft i j) =
        (∑ i : D.ι, D.fpDimSimple i * tensorDecompRight i j)) ∧

    (∀ (j : D.ι) (k : D.ι),
      (∑ i : D.ι, (N j i k : ℝ) * D.fpDimSimple i) =
        D.fpDimSimple j * D.fpDimSimple k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    exact fun fpDimZ td h => D.absorption_identity_K0_level fpDimZ td h
  ·
    exact fun fpDimZ td h => D.absorption_identity_K0_level_right fpDimZ td h
  ·
    intro fpDimZ tdL tdR hL hR j
    rw [D.absorption_identity_K0_level fpDimZ tdL hL j,
        D.absorption_identity_K0_level_right fpDimZ tdR hR j]
  ·
    exact D.regularObject_absorption_Gr N h_N

end CategoryTheory.FiniteTensorCategoryData
