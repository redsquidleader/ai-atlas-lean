/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.MvPolynomial.Basic
import Atlas.DifferentialAnalysis.code.TemperedDistributions
import Atlas.DifferentialAnalysis.code.TestFunctions
import Atlas.DifferentialAnalysis.code.SobolevEmbedding

noncomputable section

open scoped BigOperators SchwartzMap LineDeriv

namespace DistributionalKernels

variable {n : ℕ}

/-- The size `|γ| = ∑ γ i` of a multi-index `γ : Fin n → ℕ`. -/
def multiIndexSize (γ : Fin n → ℕ) : ℕ := ∑ i, γ i

/-- The finite set of multi-indices `α` that are componentwise at most `γ`. -/
def multiIndexLeqFinset (γ : Fin n → ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset fun i => Finset.range (γ i + 1)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The `m`-fold distributional partial derivative in coordinate `j`, acting on a tempered distribution. -/
def iterCoordDeriv (j : Fin n) (m : ℕ)
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    𝓢'(EuclideanSpace ℝ (Fin n), F) :=
  (fun u => TemperedDistributions.distribDerivCLM
    (EuclideanSpace.single j (1 : ℝ)) u)^[m] v

/-- The multi-index distributional derivative `D^γ v`, taken coordinate by coordinate. -/
def multiIndexDistribDeriv (γ : Fin n → ℕ)
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    𝓢'(EuclideanSpace ℝ (Fin n), F) :=
  (List.finRange n).foldl (fun w j => iterCoordDeriv j (γ j) w) v

/-- Multiplication of a tempered distribution by the power `⟨x⟩^k` of the Japanese bracket. -/
def distribMulBracketPow (k : ℤ)
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    𝓢'(EuclideanSpace ℝ (Fin n), F) :=
  TemperedDistributions.distribMulCLM
    (fun (x : EuclideanSpace ℝ (Fin n)) =>
      ((TestFunctions.japaneseBracket n x : ℝ) : ℂ) ^ k) v

/-- Multiplication of a tempered distribution by a real polynomial evaluated at `x`. -/
def distribMulPoly (p : MvPolynomial (Fin n) ℝ)
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    𝓢'(EuclideanSpace ℝ (Fin n), F) :=
  TemperedDistributions.distribMulCLM
    (fun (x : EuclideanSpace ℝ (Fin n)) =>
      ((MvPolynomial.eval (fun i => x i) p : ℝ) : ℂ)) v

/-- The right-hand side of the Leibniz expansion `D^γ (p ⟨x⟩^k v)`: a sum over `α ≤ γ` of `D^{γ-α}` applied to polynomial-times-bracket-power multiples of `v`. -/
def weightedDerivRHS (γ : Fin n → ℕ) (k : ℤ)
    (coeffs : (Fin n → ℕ) → MvPolynomial (Fin n) ℝ)
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    𝓢'(EuclideanSpace ℝ (Fin n), F) :=
  ∑ α ∈ multiIndexLeqFinset γ,
    multiIndexDistribDeriv (γ - α)
      (distribMulPoly (coeffs α)
        (distribMulBracketPow (k - 2 * ↑(multiIndexSize (γ - α))) v))

/-- `D^0 v = v`: the zero multi-index derivative is the identity. -/
lemma multiIndexDistribDeriv_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    multiIndexDistribDeriv 0 v = v := by
  simp [multiIndexDistribDeriv, iterCoordDeriv]

/-- Multiplication by the constant polynomial `1` leaves a tempered distribution unchanged. -/
lemma distribMulPoly_one {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    distribMulPoly (1 : MvPolynomial (Fin n) ℝ) v = v := by
  unfold distribMulPoly
  ext φ
  simp only [TemperedDistributions.distribMulCLM_apply]
  congr 1; ext x
  simp [map_one, one_smul]

/-- For `γ = 0`, the set of multi-indices `α ≤ γ` is the singleton `{0}`. -/
lemma multiIndexLeqFinset_zero :
    multiIndexLeqFinset (0 : Fin n → ℕ) = {0} := by
  ext α
  simp only [multiIndexLeqFinset, Fintype.mem_piFinset, Finset.mem_range,
    Finset.mem_singleton]
  constructor
  · intro h; ext i; have := h i; simp at this; omega
  · intro h; subst h; intro i; simp

/-- Zero iterations of a coordinate derivative leave the distribution unchanged. -/
lemma iterCoordDeriv_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (j : Fin n) (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    iterCoordDeriv j 0 v = v := by
  simp [iterCoordDeriv]

/-- Inductive step: `(m + 1)` iterations equal one iteration applied to `m` iterations. -/
lemma iterCoordDeriv_succ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (j : Fin n) (m : ℕ) (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    iterCoordDeriv j (m + 1) v =
      iterCoordDeriv j 1 (iterCoordDeriv j m v) := by
  simp only [iterCoordDeriv, Function.iterate_succ_apply',
    Function.iterate_zero, Function.id_def]

/-- The zero multi-index has size zero. -/
lemma multiIndexSize_zero : multiIndexSize (0 : Fin n → ℕ) = 0 := by
  simp [multiIndexSize]

/-- For `γ = 0`, the weighted derivative RHS reduces to plain polynomial-times-bracket multiplication. -/
lemma weightedDerivRHS_zero_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (k : ℤ) (p : MvPolynomial (Fin n) ℝ)
    (coeffs : (Fin n → ℕ) → MvPolynomial (Fin n) ℝ)
    (hc : coeffs 0 = p)
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    weightedDerivRHS (0 : Fin n → ℕ) k coeffs v =
      distribMulPoly p (distribMulBracketPow k v) := by
  unfold weightedDerivRHS
  rw [multiIndexLeqFinset_zero]
  simp only [Finset.sum_singleton]
  have h0 : (0 : Fin n → ℕ) - (0 : Fin n → ℕ) = 0 := by ext i; simp
  rw [h0, multiIndexDistribDeriv_zero, hc]
  congr 1
  have : multiIndexSize (0 : Fin n → ℕ) = 0 := multiIndexSize_zero
  simp [this]


/-- Directional distributional derivatives commute on `F`-valued tempered distributions. -/
lemma distribDeriv_comm_general {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (v w : EuclideanSpace ℝ (Fin n))
    (T : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    TemperedDistributions.distribDerivCLM v (TemperedDistributions.distribDerivCLM w T) =
    TemperedDistributions.distribDerivCLM w (TemperedDistributions.distribDerivCLM v T) := by
  ext φ
  simp only [TemperedDistributions.distribDerivCLM_apply, map_neg, neg_neg]
  congr 1
  exact (SchwartzRepresentation.schwartz_lineDerivOp_comm v w φ).symm

/-- Single applications of `∂_{j₀}` and `∂_j` commute. -/
lemma iterCoordDeriv_one_comm_one {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (j₀ j : Fin n) (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    iterCoordDeriv j₀ 1 (iterCoordDeriv j 1 v) =
    iterCoordDeriv j 1 (iterCoordDeriv j₀ 1 v) := by
  simp only [iterCoordDeriv, Function.iterate_one]
  exact distribDeriv_comm_general _ _ _

/-- `∂_{j₀}` commutes with `∂_j^m` for any `m`. -/
lemma iterCoordDeriv_one_comm {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (j₀ j : Fin n) (m : ℕ) (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    iterCoordDeriv j₀ 1 (iterCoordDeriv j m v) =
    iterCoordDeriv j m (iterCoordDeriv j₀ 1 v) := by
  induction m generalizing v with
  | zero => simp [iterCoordDeriv_zero]
  | succ m ih =>
    rw [iterCoordDeriv_succ j m v, iterCoordDeriv_succ j m (iterCoordDeriv j₀ 1 v)]
    rw [iterCoordDeriv_one_comm_one j₀ j (iterCoordDeriv j m v)]
    congr 1
    exact ih v

/-- `∂_{j₀}` commutes with any foldl of iterated coordinate derivatives. -/
lemma iterCoordDeriv_one_comm_foldl {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (j₀ : Fin n) (γ : Fin n → ℕ) (l : List (Fin n))
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    iterCoordDeriv j₀ 1 (l.foldl (fun w j => iterCoordDeriv j (γ j) w) v) =
    l.foldl (fun w j => iterCoordDeriv j (γ j) w) (iterCoordDeriv j₀ 1 v) := by
  induction l generalizing v with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [ih (iterCoordDeriv i (γ i) v)]
    congr 1
    exact iterCoordDeriv_one_comm j₀ i (γ i) v

/-- Recursive step: peel off one factor of `∂_{j₀}` from `D^γ`, reducing `γ_{j₀}` by one. -/
theorem multiIndexDistribDeriv_step {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (γ : Fin n → ℕ) (j₀ : Fin n) (hj₀ : 0 < γ j₀)
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    multiIndexDistribDeriv γ v =
      iterCoordDeriv j₀ 1
        (multiIndexDistribDeriv (Function.update γ j₀ (γ j₀ - 1)) v) := by
  unfold multiIndexDistribDeriv
  suffices h : ∀ (l : List (Fin n)) (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)),
    l.Nodup →
    l.foldl (fun w j => iterCoordDeriv j (γ j) w) v =
    if j₀ ∈ l then
      iterCoordDeriv j₀ 1
        (l.foldl (fun w j => iterCoordDeriv j (Function.update γ j₀ (γ j₀ - 1) j) w) v)
    else
      l.foldl (fun w j => iterCoordDeriv j (Function.update γ j₀ (γ j₀ - 1) j) w) v by
    have hmem : j₀ ∈ List.finRange n := List.mem_finRange j₀
    rw [h (List.finRange n) v (List.nodup_finRange n)]
    simp only [hmem, if_true]
  intro l
  induction l with
  | nil => intro v _; simp
  | cons i l ih =>
    intro v hnd
    simp only [List.foldl_cons]
    obtain ⟨hni, hndl⟩ := List.nodup_cons.mp hnd
    by_cases hij : i = j₀
    · subst hij
      simp only [List.mem_cons_self, if_true, Function.update_self]
      have hγ_eq : γ i = (γ i - 1) + 1 := by omega
      rw [hγ_eq, iterCoordDeriv_succ]
      rw [ih (iterCoordDeriv i 1 (iterCoordDeriv i (γ i - 1) v)) hndl]
      simp only [hni, if_false]
      rw [iterCoordDeriv_one_comm_foldl]
      have : γ i - 1 + 1 - 1 = γ i - 1 := by omega
      simp only [this]

    · have hne : i ≠ j₀ := hij
      rw [Function.update_of_ne hne]
      rw [ih (iterCoordDeriv i (γ i) v) hndl]
      by_cases hmem : j₀ ∈ l
      · simp only [List.mem_cons_of_mem i hmem, if_true, hmem, if_true]
      · simp only [show ¬ (j₀ ∈ i :: l) from fun h => by
            rcases List.mem_cons.mp h with h | h
            · exact hne h.symm
            · exact hmem h, if_false, hmem, if_false]


/-- Schwartz product rule for `p · ⟨x⟩^k · ∂_{j₀} u`: derivative is split between the polynomial-bracket factor and `u`. -/
theorem schwartz_product_rule_poly_bracket {n : ℕ}
    (j₀ : Fin n) (p : MvPolynomial (Fin n) ℝ) (k : ℤ)
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    distribMulPoly p (distribMulBracketPow k (iterCoordDeriv j₀ 1 u)) =
    iterCoordDeriv j₀ 1 (distribMulPoly p (distribMulBracketPow k u)) -
    distribMulPoly (MvPolynomial.X j₀ * p) (distribMulBracketPow (k - 2) u) := by sorry

/-- Expansion of `p · ⟨x⟩^k · ∂_{j₀} u` via the polynomial-bracket Schwartz product rule, with an explicit degree bound. -/
theorem distribMulPoly_bracketPow_deriv_expand {n : ℕ}
    (j₀ : Fin n) (p : MvPolynomial (Fin n) ℝ) (j : ℕ)
    (_hp : p.totalDegree ≤ j) (k : ℤ)
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), F)) :
    distribMulPoly p (distribMulBracketPow k (iterCoordDeriv j₀ 1 u)) =
    iterCoordDeriv j₀ 1 (distribMulPoly p (distribMulBracketPow k u)) -
    distribMulPoly (MvPolynomial.X j₀ * p) (distribMulBracketPow (k - 2) u) :=
  schwartz_product_rule_poly_bracket j₀ p k F u


/-- Combine two `weightedDerivRHS` expansions for `γ' = γ`-with-`γ_{j₀}-1` into a single expansion for `γ`. -/
theorem weightedDerivRHS_combine {n : ℕ}
    (γ γ' : Fin n → ℕ) (j₀ : Fin n) (hj₀ : 0 < γ j₀)
    (hγ' : γ' = Function.update γ j₀ (γ j₀ - 1))
    (j : ℕ)
    (c₁ : (Fin n → ℕ) → MvPolynomial (Fin n) ℝ)
    (hd₁ : ∀ α, α ≤ γ' → (c₁ α).totalDegree ≤ j + multiIndexSize (γ' - α))
    (hz₁ : ∀ α, ¬ (α ≤ γ') → c₁ α = 0)
    (c₂ : (Fin n → ℕ) → MvPolynomial (Fin n) ℝ)
    (hd₂ : ∀ α, α ≤ γ' → (c₂ α).totalDegree ≤ (j + 1) + multiIndexSize (γ' - α))
    (hz₂ : ∀ α, ¬ (α ≤ γ') → c₂ α = 0) :
    ∃ (coeffs : (Fin n → ℕ) → MvPolynomial (Fin n) ℝ),
      (∀ α, α ≤ γ → (coeffs α).totalDegree ≤ j + multiIndexSize (γ - α)) ∧
      (∀ α, ¬ (α ≤ γ) → coeffs α = 0) ∧
      (∀ (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
         (k : ℤ) (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)),
        iterCoordDeriv j₀ 1 (weightedDerivRHS γ' k c₁ v) -
          weightedDerivRHS γ' (k - 2) c₂ v =
          weightedDerivRHS γ k coeffs v) := by sorry

/-- Assembly of the inductive step for the weighted derivative expansion (just `weightedDerivRHS_combine` repackaged with the polynomial hypothesis). -/
theorem weighted_deriv_expansion_assemble {n : ℕ}
    (γ : Fin n → ℕ) (j : ℕ) (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ j)
    (j₀ : Fin n) (hj₀ : 0 < γ j₀)
    (γ' : Fin n → ℕ) (hγ'_def : γ' = Function.update γ j₀ (γ j₀ - 1))
    (c₁ : (Fin n → ℕ) → MvPolynomial (Fin n) ℝ)
    (hd₁ : ∀ α, α ≤ γ' → (c₁ α).totalDegree ≤ j + multiIndexSize (γ' - α))
    (hz₁ : ∀ α, ¬ (α ≤ γ') → c₁ α = 0)
    (c₂ : (Fin n → ℕ) → MvPolynomial (Fin n) ℝ)
    (hd₂ : ∀ α, α ≤ γ' → (c₂ α).totalDegree ≤ (j + 1) + multiIndexSize (γ' - α))
    (hz₂ : ∀ α, ¬ (α ≤ γ') → c₂ α = 0) :
    ∃ (coeffs : (Fin n → ℕ) → MvPolynomial (Fin n) ℝ),
      (∀ α, α ≤ γ → (coeffs α).totalDegree ≤ j + multiIndexSize (γ - α)) ∧
      (∀ α, ¬ (α ≤ γ) → coeffs α = 0) ∧
      (∀ (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
         (k : ℤ) (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)),
        iterCoordDeriv j₀ 1 (weightedDerivRHS γ' k c₁ v) -
          weightedDerivRHS γ' (k - 2) c₂ v =
          weightedDerivRHS γ k coeffs v) := by
  exact weightedDerivRHS_combine γ γ' j₀ hj₀ hγ'_def j c₁ hd₁ hz₁ c₂ hd₂ hz₂


/-- Full Leibniz-type expansion `p · ⟨x⟩^k · D^γ v = ∑_{α ≤ γ} D^{γ-α} (coeffs α · ⟨x⟩^{k - 2|γ-α|} v)` with polynomial degree bounds. -/
theorem weighted_deriv_expansion {n : ℕ} (γ : Fin n → ℕ) (j : ℕ)
    (p : MvPolynomial (Fin n) ℝ) (hp : p.totalDegree ≤ j) :
    ∃ (coeffs : (Fin n → ℕ) → MvPolynomial (Fin n) ℝ),
      (∀ α, α ≤ γ → (coeffs α).totalDegree ≤ j + multiIndexSize (γ - α)) ∧
      (∀ α, ¬ (α ≤ γ) → coeffs α = 0) ∧
      (∀ (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
         (k : ℤ) (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)),
        distribMulPoly p (distribMulBracketPow k (multiIndexDistribDeriv γ v)) =
          weightedDerivRHS γ k coeffs v) := by
  induction h_size : multiIndexSize γ using Nat.strongRecOn generalizing γ j p with
  | ind N ih =>
    by_cases hγ : γ = 0
    ·
      subst hγ
      refine ⟨fun α => if α = 0 then p else 0, ?_, ?_, ?_⟩
      · intro α hα
        have hα_eq : α = 0 := le_antisymm hα (Pi.le_def.mpr (fun i => Nat.zero_le _))
        subst hα_eq
        simp only [ite_true]
        rw [show multiIndexSize ((0 : Fin n → ℕ) - 0) = 0 from by simp [multiIndexSize]]
        omega
      · intro α hα
        have : α ≠ 0 := fun h => hα (h ▸ le_refl _)
        simp [this]
      · intro F' _ _ k v
        rw [multiIndexDistribDeriv_zero]
        exact (weightedDerivRHS_zero_eq k p _ (by simp) v).symm
    ·
      have hγ' : ∃ j₀ : Fin n, γ j₀ ≠ 0 := by
        by_contra hall; simp only [not_exists, not_not] at hall
        exact hγ (funext hall)
      obtain ⟨j₀, hj₀⟩ := hγ'
      have hj₀_pos : 0 < γ j₀ := Nat.pos_of_ne_zero hj₀
      set γ' := Function.update γ j₀ (γ j₀ - 1) with hγ'_def
      have hγ'_lt : multiIndexSize γ' < N := by
        rw [← h_size]; simp only [multiIndexSize, hγ'_def]
        apply Finset.sum_lt_sum
        · intro i _
          by_cases h : i = j₀
          · subst h; rw [Function.update_self]; omega
          · rw [Function.update_of_ne h]
        · exact ⟨j₀, Finset.mem_univ _, by rw [Function.update_self]; omega⟩

      obtain ⟨c₁, hd₁, hz₁, hi₁⟩ := ih _ hγ'_lt γ' j p hp rfl
      have hp' : (MvPolynomial.X j₀ * p).totalDegree ≤ j + 1 := by
        calc (MvPolynomial.X j₀ * p).totalDegree
            ≤ (MvPolynomial.X j₀).totalDegree + p.totalDegree :=
              MvPolynomial.totalDegree_mul _ _
          _ ≤ 1 + j := by rw [MvPolynomial.totalDegree_X]; omega
          _ = j + 1 := by omega
      obtain ⟨c₂, hd₂, hz₂, hi₂⟩ := ih _ hγ'_lt γ' (j + 1)
        (MvPolynomial.X j₀ * p) hp' rfl

      obtain ⟨coeffs, h_deg, h_zero, h_comb⟩ :=
        weighted_deriv_expansion_assemble γ j p hp j₀ hj₀_pos γ' hγ'_def
          c₁ hd₁ hz₁ c₂ hd₂ hz₂
      refine ⟨coeffs, h_deg, h_zero, ?_⟩
      intro F' inst1 inst2 k v

      rw [@multiIndexDistribDeriv_step n F' inst1 inst2 γ j₀ hj₀_pos v, hγ'_def.symm,
          distribMulPoly_bracketPow_deriv_expand j₀ p j hp k F'
            (multiIndexDistribDeriv γ' v)]
      have eq1 : distribMulPoly p (distribMulBracketPow k
          (multiIndexDistribDeriv γ' v)) = weightedDerivRHS γ' k c₁ v :=
        hi₁ _ k _
      have eq2 : distribMulPoly (MvPolynomial.X j₀ * p) (distribMulBracketPow (k - 2)
          (multiIndexDistribDeriv γ' v)) = weightedDerivRHS γ' (k - 2) c₂ v :=
        hi₂ _ (k - 2) _
      rw [eq1, eq2]
      exact @h_comb F' inst1 inst2 k v

/-- Base case `p = 1`: `⟨x⟩^k · D^γ v = ∑_{α ≤ γ} D^{γ-α}(coeffs α · ⟨x⟩^{k - 2|γ-α|} v)`. -/
theorem weighted_deriv_expansion_base {n : ℕ} (γ : Fin n → ℕ) :
    ∃ (coeffs : (Fin n → ℕ) → MvPolynomial (Fin n) ℝ),
      (∀ α, α ≤ γ → (coeffs α).totalDegree ≤ multiIndexSize (γ - α)) ∧
      (∀ α, ¬ (α ≤ γ) → coeffs α = 0) ∧
      (∀ (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
         (k : ℤ) (v : 𝓢'(EuclideanSpace ℝ (Fin n), F)),
        distribMulBracketPow k (multiIndexDistribDeriv γ v) =
          weightedDerivRHS γ k coeffs v) := by
  obtain ⟨coeffs, h_deg, h_zero, h_id⟩ :=
    weighted_deriv_expansion γ 0 1 (by simp [MvPolynomial.totalDegree_one])
  refine ⟨coeffs, ?_, h_zero, ?_⟩
  · intro α hα; simpa using h_deg α hα
  · intro F' _ _ k v
    have hid := h_id F' k v
    rwa [distribMulPoly_one] at hid

end DistributionalKernels

end
