/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProbabilisticMethodsInCombinatorics.code.SpaceFillingCurve
set_option maxHeartbeats 800000

open scoped Classical

namespace EuclideanTSP

/-- The two-dimensional Euclidean plane $\mathbb{R}^2$, the ambient space for the
Euclidean travelling salesman problem. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

variable {n : ℕ} [NeZero n]

/-- Length of the cyclic tour visiting the points $x$ in the order given by the
permutation $\sigma$: the sum of distances between consecutive points (mod $n$). -/
noncomputable def tourLength (x : Fin n → E2) (σ : Equiv.Perm (Fin n)) : ℝ :=
  ∑ i : Fin n, dist (x (σ i)) (x (σ (i + 1)))

/-- Length of the shortest tour through the points $x$: the infimum of `tourLength x σ`
over all permutations $\sigma$. -/
noncomputable def shortestTour (x : Fin n → E2) : ℝ :=
  ⨅ σ : Equiv.Perm (Fin n), tourLength x σ

/-- A point $p \in \mathbb{R}^2$ lies in the unit square $[0,1]^2$. -/
def InUnitSquare (p : E2) : Prop := ∀ j : Fin 2, 0 ≤ p j ∧ p j ≤ 1

/-- All points of the configuration $x$ lie in the unit square $[0,1]^2$. -/
def AllInUnitSquare (x : Fin n → E2) : Prop := ∀ i, InUnitSquare (x i)

/-- Certificate weights $\alpha_i$ in the Rhee–Talagrand TSP concentration argument:
twice the sum of the distances from $x_i$ to its successor and predecessor in the tour
$\sigma$. -/
noncomputable def cert (x : Fin n → E2) (σ : Equiv.Perm (Fin n)) (i : Fin n) : ℝ :=
  2 * (dist (x i) (x (σ (σ.symm i + 1))) + dist (x i) (x (σ (σ.symm i - 1))))

/-- The length of any tour is non-negative, as a sum of non-negative distances. -/
lemma tourLength_nonneg (x : Fin n → E2) (σ : Equiv.Perm (Fin n)) :
    0 ≤ tourLength x σ :=
  Finset.sum_nonneg fun _ _ => dist_nonneg

/-- The shortest tour length is at most the length of any specific tour. -/
lemma shortestTour_le_tourLength (x : Fin n → E2) (σ : Equiv.Perm (Fin n)) :
    shortestTour x ≤ tourLength x σ :=
  ciInf_le ⟨0, fun _ ⟨_, h⟩ => h ▸ tourLength_nonneg x _⟩ σ

/-- The length of the shortest tour is non-negative. -/
lemma shortestTour_nonneg (x : Fin n → E2) : 0 ≤ shortestTour x :=
  le_ciInf fun σ => tourLength_nonneg x σ

/-- Each certificate weight $\alpha_i = $ `cert x σ i` is non-negative. -/
lemma cert_nonneg (x : Fin n → E2) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    0 ≤ cert x σ i := by
  unfold cert; positivity

/-- Summing $\mathrm{dist}(x_i, x_{\sigma(\sigma^{-1}(i)+1)})$ over all $i$ recovers the
tour length, by reindexing through $\sigma^{-1}$. -/
lemma sum_dist_succ_eq_tourLength (x : Fin n → E2) (σ : Equiv.Perm (Fin n)) :
    ∑ i : Fin n, dist (x i) (x (σ (σ.symm i + 1))) = tourLength x σ := by
  unfold tourLength
  exact Finset.sum_equiv σ.symm (fun _ => by simp) (fun i _ => by simp [Equiv.apply_symm_apply])

/-- Analogous to `sum_dist_succ_eq_tourLength`: the sum of distances from each $x_i$ to
its predecessor in the tour also recovers the tour length. -/
lemma sum_dist_pred_eq_tourLength (x : Fin n → E2) (σ : Equiv.Perm (Fin n)) :
    ∑ i : Fin n, dist (x i) (x (σ (σ.symm i - 1))) = tourLength x σ := by
  unfold tourLength
  calc ∑ i, dist (x i) (x (σ (σ.symm i - 1)))
      = ∑ j, dist (x (σ j)) (x (σ (j - 1))) :=
        Finset.sum_equiv σ.symm (fun _ => by simp) (fun i _ => by simp [Equiv.apply_symm_apply])
    _ = ∑ j, dist (x (σ (j - 1))) (x (σ j)) := by congr 1; ext j; exact dist_comm _ _
    _ = ∑ k, dist (x (σ k)) (x (σ (k + 1))) := by
        refine Finset.sum_equiv (Equiv.addRight (-1 : Fin n)) (fun _ => by simp) (fun j _ => ?_)
        rw [show (Equiv.addRight (-1 : Fin n)) j = j - 1 from
          show j + (-1) = j - 1 from (sub_eq_add_neg j 1).symm, sub_add_cancel]

/-- The total certificate weight equals four times the tour length. -/
lemma sum_cert_eq_four_mul_tourLength (x : Fin n → E2) (σ : Equiv.Perm (Fin n)) :
    ∑ i : Fin n, cert x σ i = 4 * tourLength x σ := by
  simp only [cert, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_dist_succ_eq_tourLength, sum_dist_pred_eq_tourLength]
  ring

/-- The tour length is bounded above by the sum of certificate weights (which equals four
times the tour length). -/
lemma tourLength_le_sum_cert (x : Fin n → E2) (σ : Equiv.Perm (Fin n)) :
    tourLength x σ ≤ ∑ i : Fin n, cert x σ i := by
  rw [sum_cert_eq_four_mul_tourLength]; linarith [tourLength_nonneg x σ]

/-- The cyclic successor in `Fin m` agrees with adding one (mod $m$). -/
lemma cyclicSucc_eq_add_one {m : ℕ} [NeZero m] (i : Fin m) :
    SpaceFillingCurve.cyclicSucc i = i + 1 := by
  ext; simp [SpaceFillingCurve.cyclicSucc, Fin.val_add]

/-- Space-filling curve heuristic. There is a universal constant $C$ such that for any
point set in $[0,1]^2$ one can find a tour whose squared-edge-lengths sum to at most $C$. -/
theorem space_filling_curve_heuristic :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) [NeZero m] (x : Fin m → E2),
    AllInUnitSquare x →
    ∃ σ : Equiv.Perm (Fin m),
      ∑ i : Fin m, dist (x (σ i)) (x (σ (i + 1))) ^ 2 ≤ C := by
  obtain ⟨C, hC⟩ := SpaceFillingCurve.space_filling_curve_heuristic
  refine ⟨max C 1, by positivity, fun m _ x hx => ?_⟩
  have hx' : ∀ i, x i ∈ SpaceFillingCurve.unitSquare := by
    intro i j
    exact Set.mem_Icc.mpr (hx i j)
  obtain ⟨σ, hσ⟩ := hC m x hx'
  refine ⟨σ, ?_⟩
  have heq : ∀ i : Fin m, dist (x (σ i)) (x (σ (i + 1))) ^ 2 =
      ‖x (σ i) - x (σ (SpaceFillingCurve.cyclicSucc i))‖ ^ 2 := by
    intro i
    rw [← cyclicSucc_eq_add_one, dist_eq_norm]
  simp_rw [heq]
  linarith [le_max_left C 1]

/-- Excursion bound: if $x$ and $y$ agree on some coordinate, then the shortest tour of
$x$ exceeds that of $y$ by at most the total certificate weight on the disagreement set. -/
theorem tourLength_excursion_bound (x y : Fin n → E2) (σ : Equiv.Perm (Fin n))
    (hne : Finset.univ.filter (fun i => x i ≠ y i) ≠ Finset.univ) :
    shortestTour x ≤ shortestTour y +
      ∑ i ∈ Finset.univ.filter (fun i => x i ≠ y i), cert x σ i := by sorry

/-- Unconditional form of the excursion bound: dropping the hypothesis that $x$ and $y$
share a coordinate by using $\sum \alpha_i \ge T(x)$ when they disagree everywhere. -/
lemma shortestTour_le_shortestTour_add_cert (x y : Fin n → E2)
    (σ : Equiv.Perm (Fin n)) :
    shortestTour x ≤ shortestTour y +
      ∑ i ∈ Finset.univ.filter (fun i => x i ≠ y i), cert x σ i := by
  by_cases hT : Finset.univ.filter (fun i => x i ≠ y i) = Finset.univ
  ·
    rw [hT]
    calc shortestTour x
        ≤ tourLength x σ := shortestTour_le_tourLength x σ
      _ ≤ ∑ i : Fin n, cert x σ i := tourLength_le_sum_cert x σ
      _ ≤ shortestTour y + ∑ i : Fin n, cert x σ i :=
          le_add_of_nonneg_left (shortestTour_nonneg y)
  ·
    exact tourLength_excursion_bound x y σ hT

/-- Sum-of-squares control on the certificate weights: if a tour $\sigma$ has bounded
squared-edge sum $\le C$, then $\sum_i \alpha_i^2 \le 16 C$. -/
lemma sum_sq_cert_le {C : ℝ} (x : Fin n → E2)
    (σ : Equiv.Perm (Fin n))
    (hσ : ∑ i : Fin n, dist (x (σ i)) (x (σ (i + 1))) ^ 2 ≤ C) :
    ∑ i : Fin n, (cert x σ i) ^ 2 ≤ 16 * C := by
  have key : ∀ i : Fin n, (cert x σ i) ^ 2 ≤
      8 * (dist (x i) (x (σ (σ.symm i + 1))) ^ 2 +
           dist (x i) (x (σ (σ.symm i - 1))) ^ 2) := by
    intro i
    unfold cert
    nlinarith [sq_nonneg (dist (x i) (x (σ (σ.symm i + 1))) -
                          dist (x i) (x (σ (σ.symm i - 1))))]
  have sum_succ : ∑ i : Fin n, dist (x i) (x (σ (σ.symm i + 1))) ^ 2 =
      ∑ j : Fin n, dist (x (σ j)) (x (σ (j + 1))) ^ 2 :=
    Finset.sum_equiv σ.symm (fun _ => by simp) (fun i _ => by simp [Equiv.apply_symm_apply])
  have sum_pred : ∑ i : Fin n, dist (x i) (x (σ (σ.symm i - 1))) ^ 2 =
      ∑ j : Fin n, dist (x (σ j)) (x (σ (j + 1))) ^ 2 := by
    calc ∑ i, dist (x i) (x (σ (σ.symm i - 1))) ^ 2
        = ∑ j, dist (x (σ j)) (x (σ (j - 1))) ^ 2 :=
          Finset.sum_equiv σ.symm (fun _ => by simp) (fun i _ => by simp [Equiv.apply_symm_apply])
      _ = ∑ j, dist (x (σ (j - 1))) (x (σ j)) ^ 2 := by
          congr 1; ext j; rw [dist_comm]
      _ = ∑ k, dist (x (σ k)) (x (σ (k + 1))) ^ 2 := by
          refine Finset.sum_equiv (Equiv.addRight (-1 : Fin n)) (fun _ => by simp) (fun j _ => ?_)
          rw [show (Equiv.addRight (-1 : Fin n)) j = j - 1 from
            show j + (-1) = j - 1 from (sub_eq_add_neg j 1).symm, sub_add_cancel]
  calc ∑ i : Fin n, (cert x σ i) ^ 2
      ≤ ∑ i, 8 * (dist (x i) (x (σ (σ.symm i + 1))) ^ 2 +
           dist (x i) (x (σ (σ.symm i - 1))) ^ 2) :=
        Finset.sum_le_sum fun i _ => key i
    _ = 8 * ((∑ i, dist (x i) (x (σ (σ.symm i + 1))) ^ 2) +
             (∑ i, dist (x i) (x (σ (σ.symm i - 1))) ^ 2)) := by
        simp [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    _ = 16 * ∑ j, dist (x (σ j)) (x (σ (j + 1))) ^ 2 := by
        rw [sum_succ, sum_pred]; ring
    _ ≤ 16 * C := by linarith

/-- Theorem 9.6.1 / 9.6.3 (Rhee–Talagrand TSP concentration, certificate form). For every
configuration $x$ in the unit square, there exist non-negative weights $\alpha_i$ such
that the shortest tour is `1`-Lipschitz with respect to changes on a subset of indices
bounded by $\sum_{i : x_i \ne y_i} \alpha_i$, and the weights satisfy $\sum_i \alpha_i^2 \le C$
for a universal constant $C$. -/
theorem shortestTour_certificate_exists :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) [NeZero m] (x : Fin m → E2),
    AllInUnitSquare x →
    ∃ α : Fin m → ℝ,
      (∀ i, 0 ≤ α i) ∧
      (∀ (y : Fin m → E2), AllInUnitSquare y →
        shortestTour x ≤ shortestTour y +
          ∑ i ∈ Finset.univ.filter (fun i => x i ≠ y i), α i) ∧
      (∑ i : Fin m, (α i) ^ 2 ≤ C) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := space_filling_curve_heuristic
  refine ⟨16 * C₀, by positivity, fun m _ x hx => ?_⟩
  obtain ⟨σ, hσ⟩ := hC₀ m x hx
  exact ⟨fun i => cert x σ i, fun i => cert_nonneg x σ i,
    fun y _ => shortestTour_le_shortestTour_add_cert x y σ,
    sum_sq_cert_le x σ hσ⟩

end EuclideanTSP
