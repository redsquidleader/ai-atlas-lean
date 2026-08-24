/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Data.Fintype.Powerset
set_option maxHeartbeats 800000

open MvPolynomial Finset

namespace UnbalancingLights

/-- The linear monomial $x_0 x_1 \cdots x_{k-1}$, encoded as the exponent vector that is
$1$ on every coordinate. -/
noncomputable def linearMonomial (k : ℕ) : Fin k →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => 1)

/-- The class $\mathcal{P}_k$ of multivariate real polynomials in $k$ variables of total
degree at most $k$, with all coefficients bounded by $1$ in absolute value, and whose
coefficient at the linear monomial $x_1 \cdots x_k$ equals $1$. -/
def P_k (k : ℕ) : Set (MvPolynomial (Fin k) ℝ) :=
  { g | g.totalDegree ≤ k ∧
        (∀ m : Fin k →₀ ℕ, |g.coeff m| ≤ 1) ∧
        g.coeff (linearMonomial k) = 1 }

/-- Inclusion–exclusion identity: for a polynomial $g$ of total degree at most $k$ in
$k$ variables, the alternating sum
$\sum_{S \subseteq [k]} (-1)^{k - |S|} g(\mathbf{1}_S)$ equals the coefficient of
$x_1 \cdots x_k$ in $g$. -/
theorem inclusion_exclusion_identity {k : ℕ} (g : MvPolynomial (Fin k) ℝ)
    (hdeg : g.totalDegree ≤ k) :
    ∑ S ∈ (univ : Finset (Finset (Fin k))),
      ((-1 : ℝ) ^ (k - S.card) * MvPolynomial.eval (fun i => if i ∈ S then 1 else 0) g) =
    g.coeff (linearMonomial k) := by sorry

/-- **Lemma 2.5.3.** For every $k \geq 1$ there is a constant $c > 0$ (here $c = 2^{-k}$)
such that every polynomial $g \in \mathcal{P}_k$ attains absolute value at least $c$ at
some point of $[0,1]^k$ (in fact at a vertex of the cube). -/
theorem exists_pos_lower_bound_eval_P_k (k : ℕ) (_hk : k ≥ 1) :
    ∃ c : ℝ, c > 0 ∧ ∀ g ∈ P_k k,
      ∃ p : Fin k → ℝ, (∀ i, p i ∈ Set.Icc 0 1) ∧
        |MvPolynomial.eval p g| ≥ c := by
  classical
  use (2 : ℝ)⁻¹ ^ k
  refine ⟨by positivity, fun g hg => ?_⟩
  let vertexOf : Finset (Fin k) → (Fin k → ℝ) := fun S i => if i ∈ S then 1 else 0
  have hvertex_mem : ∀ S : Finset (Fin k), ∀ i : Fin k,
      vertexOf S i ∈ Set.Icc (0 : ℝ) 1 := by
    intro S i
    simp only [vertexOf]
    split_ifs <;> constructor <;> norm_num
  suffices h : ∃ S : Finset (Fin k), |MvPolynomial.eval (vertexOf S) g| ≥ (2 : ℝ)⁻¹ ^ k by
    obtain ⟨S, hS⟩ := h
    exact ⟨vertexOf S, hvertex_mem S, hS⟩
  by_contra h
  push_neg at h

  have hsum_lt : ∑ S ∈ (univ : Finset (Finset (Fin k))),
      |MvPolynomial.eval (vertexOf S) g| < 1 := by
    calc ∑ S ∈ (univ : Finset (Finset (Fin k))), |MvPolynomial.eval (vertexOf S) g|
        < ∑ _S ∈ (univ : Finset (Finset (Fin k))), (2 : ℝ)⁻¹ ^ k := by
          apply Finset.sum_lt_sum
          · intro S _
            exact le_of_lt (h S)
          · exact ⟨∅, mem_univ _, h ∅⟩
      _ = (univ : Finset (Finset (Fin k))).card • ((2 : ℝ)⁻¹ ^ k) := by
          rw [Finset.sum_const]
      _ = (2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ k := by
          rw [Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
          simp [nsmul_eq_mul]
      _ = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ (two_ne_zero' ℝ), one_pow]
  have hcoeff : g.coeff (linearMonomial k) = 1 := hg.2.2
  have hie := inclusion_exclusion_identity g hg.1
  rw [hcoeff] at hie
  have hone_le : (1 : ℝ) ≤ ∑ S ∈ (univ : Finset (Finset (Fin k))),
      |MvPolynomial.eval (vertexOf S) g| := by
    have h1 : (1 : ℝ) = |∑ S ∈ (univ : Finset (Finset (Fin k))),
        ((-1 : ℝ) ^ (k - S.card) * MvPolynomial.eval (vertexOf S) g)| := by
      rw [hie, abs_one]
    rw [h1]
    calc |∑ S ∈ (univ : Finset (Finset (Fin k))),
          ((-1 : ℝ) ^ (k - S.card) * MvPolynomial.eval (vertexOf S) g)|
        ≤ ∑ S ∈ (univ : Finset (Finset (Fin k))),
          |(-1 : ℝ) ^ (k - S.card) * MvPolynomial.eval (vertexOf S) g| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ S ∈ (univ : Finset (Finset (Fin k))),
          |MvPolynomial.eval (vertexOf S) g| := by
          congr 1
          ext S
          simp [abs_mul, abs_pow, abs_neg]
  linarith

end UnbalancingLights
