/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Matrix

theorem isClosed_nonneg_cone_image {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    IsClosed {b : Fin m → ℝ | ∃ x : Fin n → ℝ, (∀ j, 0 ≤ x j) ∧ A *ᵥ x = b} := by sorry

lemma clm_repr {m : ℕ} (f : (Fin m → ℝ) →L[ℝ] ℝ) (v : Fin m → ℝ) :
    f v = dotProduct (fun i => f (Pi.single i 1 : Fin m → ℝ)) v := by
  simp only [dotProduct]
  have hv : v = ∑ i : Fin m, (v i) • (Pi.single i (1 : ℝ) : Fin m → ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, Finset.mem_univ]
  conv_lhs => rw [hv]
  rw [map_sum]; congr 1; ext i; rw [map_smul, smul_eq_mul, mul_comm]

theorem farkas_lemma {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x : Fin n → ℝ, (∀ j, 0 ≤ x j) ∧ A *ᵥ x = b) ↔
    ¬ (∃ y : Fin m → ℝ, (∀ j, 0 ≤ (Aᵀ *ᵥ y) j) ∧ dotProduct b y < 0) := by
  constructor
  ·
    rintro ⟨x, hx_nn, hAx⟩ ⟨y, hAty_nn, hby⟩
    have h1 : dotProduct b y = dotProduct x (Aᵀ *ᵥ y) := by
      rw [← hAx, dotProduct_comm (A *ᵥ x) y, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]
    have h2 : 0 ≤ dotProduct x (Aᵀ *ᵥ y) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hx_nn i) (hAty_nn i)
    linarith
  ·

    intro hno_cert
    by_contra h_not_in_cone
    apply hno_cert

    set S := {b : Fin m → ℝ | ∃ x : Fin n → ℝ, (∀ j, 0 ≤ x j) ∧ A *ᵥ x = b}
    have hS_convex : Convex ℝ S := by
      intro x ⟨ux, hux_nn, hux_eq⟩ y ⟨uy, huy_nn, huy_eq⟩ a c ha hc _hac
      exact ⟨a • ux + c • uy,
        fun j => add_nonneg (mul_nonneg ha (hux_nn j)) (mul_nonneg hc (huy_nn j)),
        by simp [mulVec_add, Matrix.mulVec_smul, ← hux_eq, ← huy_eq]⟩
    have hS_closed : IsClosed S := isClosed_nonneg_cone_image A

    obtain ⟨f, u, hf_lt, hu_lt⟩ :=
      geometric_hahn_banach_closed_point hS_convex hS_closed h_not_in_cone

    have h0_in_S : (0 : Fin m → ℝ) ∈ S :=
      ⟨0, fun _ => le_refl _, by simp [mulVec_zero]⟩
    have hu_pos : 0 < u := by have := hf_lt 0 h0_in_S; simpa using this

    have hf_nonpos : ∀ s ∈ S, f s ≤ 0 := by
      intro s hs; by_contra h_pos; push_neg at h_pos
      have hs_cone : ∀ t : ℝ, 0 ≤ t → t • s ∈ S := by
        intro t ht; obtain ⟨x, hx_nn, hAx⟩ := hs
        exact ⟨t • x, fun j => mul_nonneg ht (hx_nn j), by rw [Matrix.mulVec_smul, hAx]⟩
      have := hf_lt _ (hs_cone (u / f s) (div_nonneg hu_pos.le h_pos.le))
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ u (ne_of_gt h_pos)] at this
      linarith

    have hfb_pos : 0 < f b := lt_trans hu_pos hu_lt

    set y_rep := fun i => f (Pi.single i (1 : ℝ) : Fin m → ℝ)
    refine ⟨-y_rep, fun j => ?_, ?_⟩
    ·

      have hej_in_S : A *ᵥ (Pi.single j (1 : ℝ) : Fin n → ℝ) ∈ S :=
        ⟨Pi.single j 1, fun k => by simp [Pi.single_apply]; split_ifs <;> norm_num, rfl⟩
      have hf_ej : f (A *ᵥ (Pi.single j (1 : ℝ) : Fin n → ℝ)) ≤ 0 :=
        hf_nonpos _ hej_in_S
      simp only [Pi.neg_apply, mulVec, dotProduct, transpose_apply]
      have hsum_neg : ∑ i : Fin m, A i j * (-y_rep i) = -(∑ i : Fin m, A i j * y_rep i) := by
        simp [mul_neg, Finset.sum_neg_distrib]
      rw [hsum_neg]
      suffices h : ∑ i : Fin m, A i j * y_rep i ≤ 0 by linarith

      have hrepr : (∑ i : Fin m, A i j * y_rep i) =
          f (A *ᵥ (Pi.single j (1 : ℝ) : Fin n → ℝ)) := by
        rw [clm_repr f]; simp [dotProduct, mulVec, y_rep]
        congr 1; ext i
        simp [Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ, mul_comm]
      linarith
    ·

      simp only [dotProduct, Pi.neg_apply]
      have hsum_neg : ∑ i : Fin m, b i * (-y_rep i) = -(∑ i : Fin m, b i * y_rep i) := by
        simp [mul_neg, Finset.sum_neg_distrib]
      rw [hsum_neg]
      suffices h : 0 < ∑ i : Fin m, b i * y_rep i by linarith
      have hrepr : f b = ∑ i : Fin m, y_rep i * b i := by
        rw [clm_repr f b]; simp [dotProduct, y_rep]
      have heq : ∑ i : Fin m, y_rep i * b i = ∑ i : Fin m, b i * y_rep i := by
        congr 1; ext; ring
      linarith
