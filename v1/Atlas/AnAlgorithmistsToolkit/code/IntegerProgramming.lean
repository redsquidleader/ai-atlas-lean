/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators
import Atlas.AnAlgorithmistsToolkit.code.Lattices
noncomputable section

open Matrix Finset InnerProductSpace

namespace IntegerProgramming

def IP.IsFeasible {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) : Prop :=
  ∃ x : Fin n → ℤ, A *ᵥ ((↑) ∘ x) ≤ b

def Lattice (n : ℕ) (b : Fin n → EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | ∃ c : Fin n → ℤ, y = ∑ i : Fin n, (c i : ℝ) • b i}

theorem lattice_approx_bound_sum
    {n : ℕ}
    (b : Fin n → EuclideanSpace ℝ (Fin n))
    (h_sorted : ∀ i j : Fin n, i ≤ j → ‖b i‖ ^ 2 ≤ ‖b j‖ ^ 2)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∃ y ∈ Lattice n b, ‖x - y‖ ^ 2 ≤ (1 / 4) * ∑ i : Fin n, ‖b i‖ ^ 2 := by sorry

theorem lattice_approx_bound_chain
    {n : ℕ} (hn : 0 < n)
    (b : Fin n → EuclideanSpace ℝ (Fin n))
    (h_sorted : ∀ i j : Fin n, i ≤ j → ‖b i‖ ^ 2 ≤ ‖b j‖ ^ 2)
    (x : EuclideanSpace ℝ (Fin n)) :
    ∃ y ∈ Lattice n b,
      ‖x - y‖ ^ 2 ≤ (1 / 4) * ∑ i : Fin n, ‖b i‖ ^ 2 ∧
      ‖x - y‖ ^ 2 ≤ (↑n / 4 : ℝ) * ‖b ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩‖ ^ 2 := by
  obtain ⟨y, hy_mem, hy_bound⟩ := lattice_approx_bound_sum b h_sorted x
  refine ⟨y, hy_mem, ?_, ?_⟩
  · exact hy_bound
  · have h_sum_le : ∑ i : Fin n, ‖b i‖ ^ 2 ≤ ↑n * ‖b ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩‖ ^ 2 := by
      have hlast : ∀ i : Fin n, ‖b i‖ ^ 2 ≤ ‖b ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩‖ ^ 2 := by
        intro i
        have hi := i.isLt
        exact h_sorted i ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩ (Fin.mk_le_mk.mpr (by omega))
      calc ∑ i : Fin n, ‖b i‖ ^ 2
          ≤ ∑ _i : Fin n, ‖b ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩‖ ^ 2 :=
            Finset.sum_le_sum (fun i _ => hlast i)
        _ = ↑n * ‖b ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩‖ ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc ‖x - y‖ ^ 2
        ≤ (1 / 4) * ∑ i : Fin n, ‖b i‖ ^ 2 := hy_bound
      _ ≤ (1 / 4) * (↑n * ‖b ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_left h_sum_le (by norm_num : (0:ℝ) ≤ 1/4)
      _ = (↑n / 4) * ‖b ⟨n - 1, Nat.sub_lt hn Nat.one_pos⟩‖ ^ 2 := by ring

variable {n : ℕ}

def layerSpacingBound (m : ℕ) : ℝ :=
  (2 : ℝ) ^ (-((m : ℝ) * ((m : ℝ) - 1)) / 4) * (2 / Real.sqrt m)

theorem layerSpacingBound_pos {m : ℕ} (hm : 0 < m) : 0 < layerSpacingBound m := by
  unfold layerSpacingBound
  apply mul_pos
  · exact Real.rpow_pos_of_pos (by norm_num : (2:ℝ) > 0) _
  · apply div_pos (by norm_num : (0:ℝ) < 2)
    exact Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm)

def fritzJohnRadius (n : ℕ) : ℝ := (n : ℝ) * Real.sqrt n

def layerCountBound (k : ℕ) : ℕ :=
  if k = 0 then 1
  else ⌈2 * fritzJohnRadius k / layerSpacingBound k⌉₊ + 1

theorem layerCountBound_pos : ∀ k, 0 < layerCountBound k := by
  intro k; unfold layerCountBound; split <;> omega

def lenstraBound : ℕ → ℕ
  | 0 => 1
  | n + 1 => layerCountBound (n + 1) * lenstraBound n

theorem lenstraBound_pos : ∀ n, 0 < lenstraBound n := by
  intro n
  induction n with
  | zero => simp [lenstraBound]
  | succ n ih =>
    unfold lenstraBound
    exact Nat.mul_pos (layerCountBound_pos _) ih

theorem layerCountBound_ge_ceil_ratio (k : ℕ) (hk : 0 < k) :
    (layerCountBound k : ℝ) ≥ 2 * fritzJohnRadius k / layerSpacingBound k := by
  unfold layerCountBound
  simp [show k ≠ 0 from Nat.pos_iff_ne_zero.mp hk]
  have h1 : 2 * fritzJohnRadius k / layerSpacingBound k ≤
      (↑⌈2 * fritzJohnRadius k / layerSpacingBound k⌉₊ : ℝ) := Nat.le_ceil _
  linarith

def candidateBox (n : ℕ) : Finset (Fin n → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(lenstraBound n : ℤ)) (lenstraBound n : ℤ))

theorem candidateBox_card (n : ℕ) :
    (candidateBox n).card = (2 * lenstraBound n + 1) ^ n := by
  unfold candidateBox
  rw [Fintype.card_piFinset_const]
  congr 1; simp [Int.card_Icc]; omega

theorem fritz_john_lll_geometric_containment
    {n : ℕ} (hn : 0 < n)
    {m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hfeas : IP.IsFeasible A b) :
    ∃ (basis : Fin n → EuclideanSpace ℝ (Fin n))
      (P : EuclideanSpace ℝ (Fin n)),
      IsLLLReduced basis ∧
      (∀ i j : Fin n, i ≤ j → ‖basis i‖ ^ 2 ≤ ‖basis j‖ ^ 2) ∧
      (‖basis ⟨n - 1, by omega⟩‖ ≥ 2 / Real.sqrt n) ∧
      (∀ x : Fin n → ℤ, A *ᵥ ((↑) ∘ x) ≤ b →
        (∑ i : Fin n, (x i : ℝ) • basis i) ∈
          Metric.ball P (fritzJohnRadius n)) := by sorry

theorem layerCountBound_le_lenstraBound (k n : ℕ) (hk : k ≤ n) :
    layerCountBound k ≤ lenstraBound n := by
  induction n with
  | zero =>
    have : k = 0 := by omega
    subst this
    simp [layerCountBound, lenstraBound]
  | succ n ih =>
    simp only [lenstraBound]
    by_cases hkn : k ≤ n
    · calc layerCountBound k ≤ lenstraBound n := ih hkn
        _ ≤ layerCountBound (n + 1) * lenstraBound n :=
            Nat.le_mul_of_pos_left _ (layerCountBound_pos _)
    · have : k = n + 1 := by omega
      subst this
      exact Nat.le_mul_of_pos_right _ (lenstraBound_pos n)

theorem lattice_coord_projection_bound
    {n : ℕ} (hn : 0 < n)
    (basis : Fin n → EuclideanSpace ℝ (Fin n))
    (P : EuclideanSpace ℝ (Fin n))
    (hred : IsLLLReduced basis)
    (hsorted : ∀ i j : Fin n, i ≤ j → ‖basis i‖ ^ 2 ≤ ‖basis j‖ ^ 2)
    (hbn : ‖basis ⟨n - 1, by omega⟩‖ ≥ 2 / Real.sqrt n)
    (c : Fin n → ℤ)
    (hball : (∑ i : Fin n, (c i : ℝ) • basis i) ∈ Metric.ball P (fritzJohnRadius n))
    (i : Fin n) :
    (|c i| : ℝ) * layerSpacingBound n ≤ fritzJohnRadius n := by sorry

theorem lattice_coord_bound_in_ball
    {n : ℕ} (hn : 0 < n)
    (basis : Fin n → EuclideanSpace ℝ (Fin n))
    (P : EuclideanSpace ℝ (Fin n))
    (hred : IsLLLReduced basis)
    (hsorted : ∀ i j : Fin n, i ≤ j → ‖basis i‖ ^ 2 ≤ ‖basis j‖ ^ 2)
    (hbn : ‖basis ⟨n - 1, by omega⟩‖ ≥ 2 / Real.sqrt n)
    (c : Fin n → ℤ)
    (hball : (∑ i : Fin n, (c i : ℝ) • basis i) ∈ Metric.ball P (fritzJohnRadius n)) :
    ∀ i, |c i| ≤ (lenstraBound n : ℤ) := by
  intro i

  have hproj := lattice_coord_projection_bound (n := n) hn basis P hred hsorted hbn c hball i

  have hspacing_pos := @layerSpacingBound_pos n hn
  have hR_pos : (0 : ℝ) < fritzJohnRadius n := by
    unfold fritzJohnRadius
    exact mul_pos (Nat.cast_pos.mpr hn) (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn))

  have h_ci_real : (|c i| : ℝ) ≤ fritzJohnRadius n / layerSpacingBound n := by
    have h1 : (0 : ℝ) ≤ |↑(c i)| := abs_nonneg _
    have h2 := hproj
    have h3 := hspacing_pos
    nlinarith [mul_div_cancel₀ (fritzJohnRadius n) (ne_of_gt h3)]

  have h_ratio : fritzJohnRadius n / layerSpacingBound n ≤
      2 * fritzJohnRadius n / layerSpacingBound n := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hspacing_pos)
    linarith

  have h_lcb := layerCountBound_ge_ceil_ratio n hn

  have h_lcb_le := layerCountBound_le_lenstraBound n n (le_refl n)

  have h_ci_le_lcb : (|c i| : ℝ) ≤ (layerCountBound n : ℝ) :=
    le_trans (le_trans h_ci_real h_ratio) h_lcb
  have h_ci_le_lb : (|c i| : ℝ) ≤ (lenstraBound n : ℝ) :=
    le_trans h_ci_le_lcb (Nat.cast_le.mpr h_lcb_le)

  exact_mod_cast h_ci_le_lb

theorem lenstra_solution_in_candidateBox
    (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    IP.IsFeasible A b → ∃ x ∈ candidateBox n, A *ᵥ ((↑) ∘ x) ≤ b := by
  intro hfeas
  by_cases hn : n = 0
  ·
    subst hn
    obtain ⟨x, hx⟩ := hfeas
    exact ⟨x, Fintype.mem_piFinset.mpr (fun i => Fin.elim0 i), hx⟩
  ·
    have hn' : 0 < n := Nat.pos_of_ne_zero hn

    obtain ⟨basis, P, hred, hsorted, hbn_large, hcontain⟩ :=
      fritz_john_lll_geometric_containment hn' A b hfeas

    obtain ⟨x₀, hx₀⟩ := hfeas
    have hx₀_ball := hcontain x₀ hx₀

    have hcoord := lattice_coord_bound_in_ball (n := n) hn' basis P hred hsorted hbn_large x₀ hx₀_ball

    refine ⟨x₀, ?_, hx₀⟩
    simp only [candidateBox, Fintype.mem_piFinset, Finset.mem_Icc]
    exact fun i => abs_le.mp (hcoord i)

theorem lenstra_ip_fpt :
    ∀ (n m : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ),
    (candidateBox n).card ≤ (2 * lenstraBound n + 1) ^ n ∧
    (IP.IsFeasible A b → ∃ x ∈ candidateBox n, A *ᵥ ((↑) ∘ x) ≤ b) := by
  intro n m A b
  exact ⟨le_of_eq (candidateBox_card n), lenstra_solution_in_candidateBox n m A b⟩

end IntegerProgramming
