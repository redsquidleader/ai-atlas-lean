/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Sqrt

open Finset Matrix BigOperators

namespace BregmanMinc

/-- The row sum $d_i$ of row $i$ of a $0/1$-matrix $A$: the number of columns $j$ with $A_{ij}=1$. -/
noncomputable def rowSum (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℕ :=
  (Finset.univ.filter (fun j => A i j = 1)).card

/-- Logarithmic form of the Brégman-Minc inequality (Theorem 10.2.1): for a $0/1$-matrix $A$
with positive permanent, $\log \operatorname{per} A \le \sum_i \frac{1}{d_i} \log(d_i!)$. -/
theorem bregman_minc_log_bound (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1)
    (hP : 0 < A.permanent) :
    Real.log A.permanent ≤ ∑ i : Fin n,
      (1 : ℝ) / (rowSum n A i : ℝ) * Real.log (Nat.factorial (rowSum n A i)) := by sorry

/-- The Brégman-Minc inequality (Theorem 10.2.1): for any $n \times n$ matrix $A$ with $0/1$
entries, $\operatorname{per} A \le \prod_i (d_i!)^{1/d_i}$ where $d_i$ is the $i$-th row sum. -/
theorem bregman_minc_inequality (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, A i j = 0 ∨ A i j = 1) :
    A.permanent ≤ ∏ i : Fin n,
      ((Nat.factorial (rowSum n A i) : ℝ)) ^ ((1 : ℝ) / (rowSum n A i : ℝ)) := by
  by_cases hP : A.permanent ≤ 0
  · exact le_trans hP (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · push Not at hP
    have hlog := bregman_minc_log_bound n A hA hP
    have h1 := Real.exp_le_exp.mpr hlog
    rw [Real.exp_log hP] at h1
    rw [Real.exp_sum] at h1
    convert h1 using 1
    congr 1; ext i
    rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr (Nat.factorial_pos _))]
    ring

/-- Row sum of a $0/1$-matrix indexed by an arbitrary finite type $V$: the number of $j$ with
$A_{ij}=1$. -/
noncomputable def rowSumGen {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (i : V) : ℕ :=
  (Finset.univ.filter (fun j => A i j = 1)).card

/-- Brégman-Minc inequality for matrices indexed by an arbitrary finite type $V$:
$\operatorname{per} A \le \prod_{i \in V} (d_i!)^{1/d_i}$ for $0/1$-matrices $A$. -/
theorem bregman_minc_inequality_gen {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : ∀ i j, A i j = 0 ∨ A i j = 1) :
    A.permanent ≤ ∏ i : V,
      ((Nat.factorial (rowSumGen A i) : ℝ)) ^ ((1 : ℝ) / (rowSumGen A i : ℝ)) := by sorry

end BregmanMinc

namespace KahnLovasz

open SimpleGraph Finset BigOperators

/-- The number of perfect matchings of a simple graph $G$. -/
noncomputable def numPerfectMatchings {V : Type*} (G : SimpleGraph V) : ℕ :=
  Nat.card {M : G.Subgraph // M.IsPerfectMatching}

/-- Bridge step toward the Kahn-Lovász bound: the squared count of perfect matchings is at most
the permanent of the adjacency matrix, i.e. $|\mathcal{M}(G)|^2 \le \operatorname{per}(A_G)$. -/
theorem matching_sq_le_permanent
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (numPerfectMatchings G : ℝ) ^ 2 ≤ (G.adjMatrix ℝ).permanent := by sorry

/-- The row sum of the adjacency matrix of $G$ at vertex $v$ equals the graph-theoretic degree
$\deg_G(v)$. -/
lemma adjMatrix_rowSumGen_eq_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    BregmanMinc.rowSumGen (G.adjMatrix ℝ) v = G.degree v := by
  unfold BregmanMinc.rowSumGen SimpleGraph.degree
  congr 1
  ext w
  simp only [SimpleGraph.adjMatrix_apply, Finset.mem_filter, Finset.mem_univ, true_and,
             SimpleGraph.mem_neighborFinset]
  constructor
  · intro h
    split_ifs at h with hadj
    · exact hadj
    · norm_num at h
  · intro hadj
    simp [hadj]

/-- The Kahn-Lovász inequality (Corollary 10.2.2): the number of perfect matchings of $G$
satisfies $|\mathcal{M}(G)| \le \prod_v (\deg(v)!)^{1/(2\deg(v))}$. -/
theorem kahn_lovasz_inequality
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    (numPerfectMatchings G : ℝ) ≤
      ∏ v : V, ((Nat.factorial (G.degree v) : ℝ)) ^ ((1 : ℝ) / (2 * (G.degree v : ℝ))) := by
  classical
  have h_pm_nonneg : (0 : ℝ) ≤ (numPerfectMatchings G : ℝ) := Nat.cast_nonneg _

  have h_prod_nonneg : (0 : ℝ) ≤ ∏ v : V,
      ((Nat.factorial (G.degree v) : ℝ)) ^ ((1 : ℝ) / (2 * (G.degree v : ℝ))) :=
    Finset.prod_nonneg (fun v _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)

  suffices h : (numPerfectMatchings G : ℝ) ^ 2 ≤
      (∏ v : V, ((Nat.factorial (G.degree v) : ℝ)) ^
        ((1 : ℝ) / (2 * (G.degree v : ℝ)))) ^ 2 by
    nlinarith [sq_nonneg ((numPerfectMatchings G : ℝ) -
      ∏ v : V, ((Nat.factorial (G.degree v) : ℝ)) ^ ((1 : ℝ) / (2 * (G.degree v : ℝ))))]


  have h_sq_prod : (∏ v : V, ((Nat.factorial (G.degree v) : ℝ)) ^
      ((1 : ℝ) / (2 * (G.degree v : ℝ)))) ^ 2 =
      ∏ v : V, ((Nat.factorial (G.degree v) : ℝ)) ^
        ((1 : ℝ) / (G.degree v : ℝ)) := by
    rw [← Finset.prod_pow]
    congr 1
    ext v
    rw [← Real.rpow_natCast (((Nat.factorial (G.degree v) : ℝ)) ^
        ((1 : ℝ) / (2 * (G.degree v : ℝ)))) 2,
      ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    ring
  rw [h_sq_prod]


  calc (numPerfectMatchings G : ℝ) ^ 2
      ≤ (G.adjMatrix ℝ).permanent := matching_sq_le_permanent G
    _ ≤ ∏ v : V, ((Nat.factorial (G.degree v) : ℝ)) ^ ((1 : ℝ) / (G.degree v : ℝ)) := by

        have hBregman := BregmanMinc.bregman_minc_inequality_gen (G.adjMatrix ℝ)
          (fun i j => by
            simp only [SimpleGraph.adjMatrix_apply]
            split_ifs <;> simp)
        convert hBregman using 1
        congr 1
        ext v
        rw [adjMatrix_rowSumGen_eq_degree]

end KahnLovasz
