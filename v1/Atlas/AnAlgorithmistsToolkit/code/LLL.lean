/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

noncomputable section

open InnerProductSpace Finset

namespace LLL

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def gramSchmidtVec (b : Fin n → E) : Fin n → E :=
  gramSchmidt ℝ b

def gramSchmidtCoeff (b : Fin n → E) (i j : Fin n) : ℝ :=
  @inner ℝ E _ (gramSchmidtVec b j) (b i) / (‖gramSchmidtVec b j‖ ^ 2)

def IsSizeReduced (b : Fin n → E) : Prop :=
  ∀ i j : Fin n, j < i → |gramSchmidtCoeff b i j| ≤ 1 / 2

def SatisfiesLovász (b : Fin n → E) : Prop :=
  ∀ i : Fin n, ∀ hi : (i : ℕ) + 1 < n,
    ‖gramSchmidtVec b ⟨i + 1, hi⟩ +
      gramSchmidtCoeff b ⟨i + 1, hi⟩ i • gramSchmidtVec b i‖ ^ 2 ≥
    3 / 4 * ‖gramSchmidtVec b i‖ ^ 2

structure IsLLLReduced (b : Fin n → E) : Prop where
  size_reduced : IsSizeReduced b
  lovász : SatisfiesLovász b

theorem gramSchmidtVec_norm_sq_half (b : Fin n → E) (hred : IsLLLReduced b)
    (i : Fin n) (hi : (i : ℕ) + 1 < n) :
    ‖gramSchmidtVec b ⟨i + 1, hi⟩‖ ^ 2 ≥ 1 / 2 * ‖gramSchmidtVec b i‖ ^ 2 := by
  have hlov := hred.lovász i hi
  set bstar_i := gramSchmidtVec b i
  set bstar_next := gramSchmidtVec b ⟨i + 1, hi⟩
  set μ := gramSchmidtCoeff b ⟨i + 1, hi⟩ i

  have hne : (⟨(i : ℕ) + 1, hi⟩ : Fin n) ≠ i := by
    intro h; have := congr_arg Fin.val h; simp at this
  have hortho : ⟪bstar_next, bstar_i⟫_ℝ = 0 :=
    gramSchmidt_orthogonal ℝ b hne

  have hexpand : ‖bstar_next + μ • bstar_i‖ ^ 2 =
      ‖bstar_next‖ ^ 2 + μ ^ 2 * ‖bstar_i‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, hortho, mul_zero, mul_zero, add_zero,
        norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

  have hsize : |μ| ≤ 1 / 2 :=
    hred.size_reduced _ _ (Fin.mk_lt_mk.mpr (Nat.lt_succ_of_le le_rfl))
  have hmu_sq : μ ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs μ, abs_nonneg μ]

  rw [hexpand] at hlov

  nlinarith [sq_nonneg (‖bstar_i‖)]

theorem gramSchmidtVec_norm_sq_geometric {n : ℕ} (b : Fin (n + 1) → E)
    (hred : IsLLLReduced b) (j : ℕ) (hj : j < n + 1) :
    ‖gramSchmidtVec b ⟨j, hj⟩‖ ^ 2 ≥
      (1 / 2 : ℝ) ^ j * ‖gramSchmidtVec b 0‖ ^ 2 := by
  induction j with
  | zero => simp
  | succ k ih =>
    have hk : k < n + 1 := by omega
    have h_half := gramSchmidtVec_norm_sq_half b hred ⟨k, hk⟩ (by omega)
    have h_ih := ih hk
    calc ‖gramSchmidtVec b ⟨k + 1, hj⟩‖ ^ 2
        ≥ 1 / 2 * ‖gramSchmidtVec b ⟨k, hk⟩‖ ^ 2 := h_half
      _ ≥ 1 / 2 * ((1 / 2 : ℝ) ^ k * ‖gramSchmidtVec b 0‖ ^ 2) := by gcongr
      _ = (1 / 2 : ℝ) ^ (k + 1) * ‖gramSchmidtVec b 0‖ ^ 2 := by rw [pow_succ]; ring

lemma gramSchmidtVec_zero {n : ℕ} (b : Fin (n + 1) → E) :
    gramSchmidtVec b 0 = b 0 := by
  unfold gramSchmidtVec
  exact gramSchmidt_bot ℝ b


theorem lattice_norm_ge_min_gramSchmidt_norm
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (b : Fin (n + 1) → E) (v : E) (hv : v ≠ 0)
    (hv_in : ∃ c : Fin (n + 1) → ℤ, v = ∑ i, (c i : ℝ) • b i) :
    ∃ i : Fin (n + 1), ‖gramSchmidtVec b i‖ ≤ ‖v‖ := by sorry

theorem lll_short_vector_bound {n : ℕ} (b : Fin (n + 1) → E)
    (hred : IsLLLReduced b)
    (v : E) (hv : v ≠ 0) (hv_in : ∃ c : Fin (n + 1) → ℤ, v = ∑ i, (c i : ℝ) • b i) :
    ‖b 0‖ ^ 2 ≤ 2 ^ n * ‖v‖ ^ 2 := by

  obtain ⟨i, hi_bound⟩ := lattice_norm_ge_min_gramSchmidt_norm b v hv hv_in

  have h_geom := gramSchmidtVec_norm_sq_geometric b hred (i : ℕ) i.isLt

  rw [gramSchmidtVec_zero] at h_geom

  have h_b0 : ‖b 0‖ ^ 2 ≤ 2 ^ (i : ℕ) * ‖gramSchmidtVec b ⟨i, i.isLt⟩‖ ^ 2 := by
    have h_pos : (1 / 2 : ℝ) ^ (i : ℕ) * (2 : ℝ) ^ (i : ℕ) = 1 := by
      rw [← mul_pow]; norm_num
    calc ‖b 0‖ ^ 2
        = 1 * ‖b 0‖ ^ 2 := (one_mul _).symm
      _ = (1 / 2 : ℝ) ^ (i : ℕ) * (2 : ℝ) ^ (i : ℕ) * ‖b 0‖ ^ 2 := by rw [h_pos]
      _ = (2 : ℝ) ^ (i : ℕ) * ((1 / 2 : ℝ) ^ (i : ℕ) * ‖b 0‖ ^ 2) := by ring
      _ ≤ (2 : ℝ) ^ (i : ℕ) * ‖gramSchmidtVec b ⟨↑i, i.isLt⟩‖ ^ 2 := by gcongr

  have h_vi : ‖gramSchmidtVec b ⟨i, i.isLt⟩‖ ^ 2 ≤ ‖v‖ ^ 2 :=
    sq_le_sq' (by linarith [norm_nonneg (gramSchmidtVec b ⟨i, i.isLt⟩)]) hi_bound

  have h_exp : (2 : ℝ) ^ (i : ℕ) ≤ 2 ^ n := by gcongr; norm_num; omega
  calc ‖b 0‖ ^ 2
      ≤ 2 ^ (i : ℕ) * ‖gramSchmidtVec b ⟨↑i, i.isLt⟩‖ ^ 2 := h_b0
    _ ≤ 2 ^ (i : ℕ) * ‖v‖ ^ 2 := by gcongr
    _ ≤ 2 ^ n * ‖v‖ ^ 2 := by gcongr

theorem lll_shortest_vector_approx {n : ℕ} (b : Fin (n + 1) → E)
    (hred : IsLLLReduced b)
    (lam₁ : ℝ) (hlam₁ : lam₁ > 0)
    (hlam₁_achieved : ∃ v : E, v ≠ 0 ∧
      (∃ c : Fin (n + 1) → ℤ, v = ∑ i, (c i : ℝ) • b i) ∧ ‖v‖ = lam₁) :
    ‖b 0‖ ≤ 2 ^ ((n : ℝ) / 2) * lam₁ := by
  obtain ⟨v, hv_ne, hv_in, hv_norm⟩ := hlam₁_achieved
  have h_sq := lll_short_vector_bound b hred v hv_ne hv_in
  rw [hv_norm] at h_sq


  have hb : (0 : ℝ) ≤ ‖b 0‖ := norm_nonneg _
  have key : 2 ^ ((n : ℝ) / 2) * lam₁ = Real.sqrt (2 ^ n * lam₁ ^ 2) := by
    rw [Real.sqrt_mul (by positivity : (2 : ℝ) ^ n ≥ 0)]
    rw [Real.sqrt_sq (le_of_lt hlam₁)]
    congr 1
    rw [show (2 : ℝ) ^ n = (2 : ℝ) ^ (n : ℝ) from by rw [Real.rpow_natCast]]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (2 : ℝ) ≥ 0)]
    ring_nf
  rw [key, ← Real.sqrt_sq hb]
  exact Real.sqrt_le_sqrt h_sq


theorem reduced_basis_bounds_lemma5 {n : ℕ} (hn : 0 < n)
    (b : Fin n → E)
    (hb_reduced : IsLLLReduced b)
    (det_L : ℝ) (hdet : det_L > 0)
    (hdet_eq : det_L = ∏ i : Fin n, ‖gramSchmidtVec b i‖) :
    (∏ i : Fin n, ‖b i‖ ≤ (2 : ℝ) ^ (((n : ℝ) * ((n : ℝ) - 1)) / 4) * det_L) ∧
    (let H : Set E := ↑(Submodule.span ℝ (b '' {i : Fin n | (i : ℕ) < n - 1}))
     let last : Fin n := ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩
     (2 : ℝ) ^ (-(((n : ℝ) * ((n : ℝ) - 1)) / 4)) * ‖b last‖ ≤
       Metric.infDist (b last) H ∧
     Metric.infDist (b last) H ≤ ‖b last‖) := by sorry

def SatisfiesLovászOriginal (b : Fin n → E) : Prop :=
  ∀ i : Fin n, ∀ hi : (i : ℕ) + 1 < n,
    ‖gramSchmidtVec b i‖ ^ 2 ≤
    4 / 3 * ‖gramSchmidtVec b ⟨i + 1, hi⟩ +
      gramSchmidtCoeff b ⟨i + 1, hi⟩ i • gramSchmidtVec b i‖ ^ 2

structure IsReducedBasis (b : Fin n → E) : Prop where
  size_reduced : IsSizeReduced b
  lovász_original : SatisfiesLovászOriginal b

end LLL

end
