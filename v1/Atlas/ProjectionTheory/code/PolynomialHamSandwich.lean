/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProjectionTheory.code.BorsukUlam

open MeasureTheory MvPolynomial

noncomputable section

namespace PolynomialHamSandwich

/-- A polynomial `P : ℝ[x₁, …, x_d]` *bisects* a measurable set `U ⊆ ℝ^d` if the
parts of `U` where `P > 0` and where `P < 0` have equal Lebesgue volume. -/
def Bisects (d : ℕ) (P : MvPolynomial (Fin d) ℝ) (U : Set (Fin d → ℝ)) : Prop :=
  volume ({x ∈ U | eval x P > 0}) =
    volume ({x ∈ U | eval x P < 0})

/-- The signed volume `vol{P > 0 in U} − vol{P < 0 in U}` as a real number; this
function is zero exactly when `P` bisects `U` (assuming `U` is bounded). -/
def signedVol (d : ℕ) (P : MvPolynomial (Fin d) ℝ) (U : Set (Fin d → ℝ)) : ℝ :=
  (volume ({x ∈ U | eval x P > 0})).toReal -
    (volume ({x ∈ U | eval x P < 0})).toReal

/-- Negating the polynomial flips the sign of the signed volume:
`signedVol(−P, U) = −signedVol(P, U)`. -/
lemma signedVol_neg (d : ℕ) (P : MvPolynomial (Fin d) ℝ) (U : Set (Fin d → ℝ)) :
    signedVol d (-P) U = -(signedVol d P U) := by
  simp only [signedVol, eval_neg, neg_pos, neg_lt_zero, neg_sub]

/-- For a bounded set `U`, vanishing of the signed volume `signedVol d P U` implies
that `P` bisects `U`. -/
lemma bisects_of_signedVol_zero (d : ℕ) (P : MvPolynomial (Fin d) ℝ) (U : Set (Fin d → ℝ))
    (hU_bounded : Bornology.IsBounded U) (h : signedVol d P U = 0) : Bisects d P U := by
  unfold Bisects signedVol at *
  have hfp : volume ({x ∈ U | eval x P > 0}) ≠ ⊤ :=
    (Bornology.IsBounded.measure_lt_top (μ := volume)
      (hU_bounded.subset (Set.sep_subset U _))).ne
  have hfn : volume ({x ∈ U | eval x P < 0}) ≠ ⊤ :=
    (Bornology.IsBounded.measure_lt_top (μ := volume)
      (hU_bounded.subset (Set.sep_subset U _))).ne
  exact (ENNReal.toReal_eq_toReal_iff' hfp hfn).mp (by linarith)

/-- A nontrivial linear combination of linearly independent polynomials is nonzero. -/
lemma combo_ne_zero {d m : ℕ} (basis : Fin m → MvPolynomial (Fin d) ℝ)
    (hbasis : LinearIndependent ℝ basis) (v : Fin m → ℝ) (hv : v ≠ 0) :
    ∑ i, v i • basis i ≠ 0 := by
  intro h; rw [linearIndependent_iff'] at hbasis
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hall; push Not at hall; exact hv (funext hall)
  exact hj (hbasis Finset.univ v h j (Finset.mem_univ j))

/-- Any real-linear combination of polynomials of total degree at most `D` itself
has total degree at most `D`. -/
lemma combo_totalDegree_le {d D m : ℕ} (basis : Fin m → MvPolynomial (Fin d) ℝ)
    (hbasis_deg : ∀ i, (basis i).totalDegree ≤ D) (v : Fin m → ℝ) :
    (∑ i, v i • basis i).totalDegree ≤ D :=
  le_trans (totalDegree_finset_sum _ _)
    (Finset.sup_le (fun i _ => le_trans (totalDegree_smul_le _ _) (hbasis_deg i)))

/-- A point on the unit sphere `S^n ⊆ ℝ^{n+1}` has, in particular, a nonzero
coordinate vector. -/
lemma sphere_vec_ne_zero {n : ℕ} (x : ↥(BorsukUlam.Sphere n)) :
    (fun i => (x : EuclideanSpace ℝ (Fin (n + 1))) i) ≠ 0 := by
  intro h
  have hx := x.property
  simp only [BorsukUlam.Sphere, Metric.mem_sphere, dist_zero_right] at hx
  have : (x : EuclideanSpace ℝ (Fin (n + 1))) = 0 := by ext i; exact congr_fun h i
  rw [this, norm_zero] at hx; exact one_ne_zero hx.symm


/-- The space of polynomials in `d` variables of total degree at most `D` has
dimension `binom(D + d, d)`; in particular it admits a linearly independent
family of that size all of whose elements have total degree `≤ D`. -/
theorem exists_linearIndependent_polynomials (d D : ℕ) :
    ∃ (basis : Fin ((D + d).choose d) → MvPolynomial (Fin d) ℝ),
      LinearIndependent ℝ basis ∧ ∀ i, (basis i).totalDegree ≤ D := by sorry


/-- Continuity of the signed-volume map. For a fixed basis of polynomials of bounded
degree and bounded open sets `U_i`, the map sending a coefficient vector `x` on
the sphere to the tuple of signed volumes `(signedVol d (∑ x_j basis_j) U_i)_i` is
continuous as a map `S^n → ℝ^n`. -/
theorem signedVol_map_continuous (d n : ℕ) (basis : Fin (n + 1) → MvPolynomial (Fin d) ℝ)
    (U : Fin n → Set (Fin d → ℝ)) (hU_open : ∀ i, IsOpen (U i))
    (hU_bounded : ∀ i, Bornology.IsBounded (U i)) :
    Continuous (fun (x : ↥(BorsukUlam.Sphere n)) =>
      (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i =>
        signedVol d (∑ j : Fin (n + 1), (x : EuclideanSpace ℝ (Fin (n + 1))) j • basis j) (U i))) := by sorry


/-- **Polynomial Ham Sandwich Theorem.** Given `n` bounded open sets `U_1, …, U_n`
in `ℝ^d` and a degree bound `D` with `n ≤ binom(D + d, d) − 1`, there exists a
nonzero polynomial `P` of total degree `≤ D` whose zero set bisects every `U_i`.
This is the polynomial generalization of the classical Ham Sandwich theorem,
proved via Borsuk–Ulam applied to signed volumes. -/
theorem polynomial_ham_sandwich
    (d : ℕ) (D : ℕ) (n : ℕ)
    (U : Fin n → Set (Fin d → ℝ))
    (hU_open : ∀ i, IsOpen (U i))
    (hU_bounded : ∀ i, Bornology.IsBounded (U i))
    (hn : n ≤ (D + d).choose d - 1) :
    ∃ P : MvPolynomial (Fin d) ℝ,
      P ≠ 0 ∧ P.totalDegree ≤ D ∧ ∀ i, Bisects d P (U i) := by

  obtain ⟨fullBasis, hfull_indep, hfull_deg⟩ := exists_linearIndependent_polynomials d D

  have hn1 : n + 1 ≤ (D + d).choose d := by
    have := Nat.choose_pos (Nat.le_add_left d D); omega

  let basis : Fin (n + 1) → MvPolynomial (Fin d) ℝ := fun i => fullBasis (Fin.castLE hn1 i)
  have hbasis_indep : LinearIndependent ℝ basis :=
    hfull_indep.comp (Fin.castLE hn1) (Fin.castLE_injective hn1)
  have hbasis_deg : ∀ i, (basis i).totalDegree ≤ D := fun i => hfull_deg _


  let F : ↥(BorsukUlam.Sphere n) → EuclideanSpace ℝ (Fin n) := fun x =>
    (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i =>
      signedVol d (∑ j, (x : EuclideanSpace ℝ (Fin (n + 1))) j • basis j) (U i))
  let f : C(↥(BorsukUlam.Sphere n), EuclideanSpace ℝ (Fin n)) :=
    ⟨F, signedVol_map_continuous d n basis U hU_open hU_bounded⟩


  have hf_antipodal : ∀ x : ↥(BorsukUlam.Sphere n),
      f x = -f ⟨-x.val, BorsukUlam.neg_mem_sphere x.property⟩ := by
    intro x; ext i
    change ((EuclideanSpace.equiv (Fin n) ℝ).symm _).ofLp i =
      (-((EuclideanSpace.equiv (Fin n) ℝ).symm _)).ofLp i
    show signedVol d (∑ j, (x : EuclideanSpace ℝ (Fin (n + 1))) j • basis j) (U i) =
      -(signedVol d (∑ j, (-(x : EuclideanSpace ℝ (Fin (n + 1)))) j • basis j) (U i))
    have heq : ∑ j, (-(x : EuclideanSpace ℝ (Fin (n + 1)))) j • basis j =
        -(∑ j, (x : EuclideanSpace ℝ (Fin (n + 1))) j • basis j) := by
      simp [neg_smul, Finset.sum_neg_distrib]
    rw [heq, signedVol_neg]; ring

  obtain ⟨x, hx⟩ := BorsukUlam.borsuk_ulam n f hf_antipodal

  let P := ∑ j : Fin (n + 1), (x : EuclideanSpace ℝ (Fin (n + 1))) j • basis j
  refine ⟨P, combo_ne_zero basis hbasis_indep _ (sphere_vec_ne_zero x),
    combo_totalDegree_le basis hbasis_deg _, fun i => ?_⟩

  apply bisects_of_signedVol_zero d P (U i) (hU_bounded i)
  have hcoord : ((EuclideanSpace.equiv (Fin n) ℝ).symm
      (fun i => signedVol d P (U i))).ofLp i = (0 : EuclideanSpace ℝ (Fin n)).ofLp i :=
    congr_arg (fun v => v.ofLp i) hx
  simpa using hcoord

end PolynomialHamSandwich
