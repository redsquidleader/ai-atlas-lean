/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.CompletenessValuationCriterion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

universe u

open AlgebraicGeometry

/-- (Lemma 16.32) Given a valuation subring $R \subseteq F$ and finitely many nonzero $x_0, \dots, x_n \in F$, there exists $\lambda \in F^\times$ such that $\lambda x_i \in R$ for all $i$ and some $\lambda x_i$ is a unit in $R$ (this normalises projective coordinates with respect to a valuation). -/
theorem lemma_16_32 {F : Type*} [Field F] (R : ValuationSubring F)
    (n : ℕ) (x : Fin (n + 1) → F) (hx : ∀ i, x i ≠ 0) :
    ∃ (l : F), l ≠ 0 ∧ (∀ i, l * x i ∈ (R : Set F)) ∧
      (∃ i, (l * x i)⁻¹ ∈ (R : Set F)) := by
  induction n with
  | zero =>
    refine ⟨(x 0)⁻¹, inv_ne_zero (hx 0), ?_, ⟨0, ?_⟩⟩
    · intro i
      have hi : i = 0 := by ext; omega
      subst hi; simp [inv_mul_cancel₀ (hx 0)]
    · simp [inv_mul_cancel₀ (hx 0)]
  | succ m ih =>
    let x' : Fin (m + 1) → F := fun i => x (Fin.castSucc i)
    have hx' : ∀ i, x' i ≠ 0 := fun i => hx (Fin.castSucc i)
    obtain ⟨l, hl_ne, hl_mem, ⟨j, hj_inv⟩⟩ := ih x' hx'
    by_cases hlast : l * x (Fin.last (m + 1)) ∈ (R : Set F)
    ·
      refine ⟨l, hl_ne, ?_, ⟨Fin.castSucc j, hj_inv⟩⟩
      intro i
      by_cases hi : (i : ℕ) < m + 1
      · rw [show i = Fin.castSucc (⟨i, hi⟩ : Fin (m + 1)) from by ext; simp]
        exact hl_mem ⟨i, hi⟩
      · rw [show i = Fin.last (m + 1) from by ext; simp; omega]; exact hlast
    ·

      have hlast_inv : (l * x (Fin.last (m + 1)))⁻¹ ∈ (R : Set F) :=
        (R.mem_or_inv_mem _).resolve_left hlast
      refine ⟨(x (Fin.last (m + 1)))⁻¹, inv_ne_zero (hx _), ?_,
              ⟨Fin.last (m + 1), by simp [inv_mul_cancel₀ (hx _)]⟩⟩
      intro i
      by_cases hi : (i : ℕ) < m + 1
      ·
        rw [show i = Fin.castSucc (⟨i, hi⟩ : Fin (m + 1)) from by ext; simp]
        suffices h : (x (Fin.last (m + 1)))⁻¹ * x (Fin.castSucc ⟨i, hi⟩) =
            l * x (Fin.castSucc ⟨i, hi⟩) * (l * x (Fin.last (m + 1)))⁻¹ by
          rw [h]; exact R.toSubring.mul_mem (hl_mem ⟨i, hi⟩) hlast_inv
        field_simp
      ·
        rw [show i = Fin.last (m + 1) from by ext; simp; omega]
        rw [inv_mul_cancel₀ (hx _)]; exact R.one_mem'

namespace AlgebraicGeometry.CompletenessValuationCriterion

/-- A projective variety structure on $V$: a choice of dimension $n$ and homogeneous coordinates $X_0, \dots, X_n \in K(Z)^\times$ (none vanishing) on every subvariety $Z$ of $V$. -/
structure IsProjectiveVariety {k : Type u} [Field k] (V : AlgVariety k) where
  n : ℕ
  homogCoords : (Z : SubvarietyOf V) → Fin (n + 1) → Z.toVariety.functionField
  homogCoords_ne_zero : ∀ (Z : SubvarietyOf V) (i : Fin (n + 1)),
    homogCoords Z i ≠ 0

/-- If all ratios $X_i / X_j$ lie in the valuation ring, then the valuation is dominated by the local ring of some point of the affine chart $\{X_j \neq 0\}$. -/
theorem affineChartLocalRing {k : Type u} [Field k] {V : AlgVariety k}
    (hproj : IsProjectiveVariety V)
    (Z : SubvarietyOf V) (j : Fin (hproj.n + 1))
    (R : ValRingOver Z.toVariety)
    (hcoords : ∀ i, hproj.homogCoords Z i * (hproj.homogCoords Z j)⁻¹ ∈ R.valSub) :
    ∃ P : Z.toVariety.carrier, localRing_le P R := by sorry

/-- If some scaling $\lambda X_i$ of the homogeneous coordinates lies in $R$ with some $\lambda X_j$ a unit, then $R$ is dominated by a point of $Z$. -/
theorem pointFromScaledCoords_lemma {k : Type u} [Field k]
    {V : AlgVariety k} (hproj : IsProjectiveVariety V)
    (Z : SubvarietyOf V) (R : ValRingOver Z.toVariety)
    (l : Z.toVariety.functionField) (hl_ne : l ≠ 0)
    (hl_mem : ∀ i, l * hproj.homogCoords Z i ∈ R.valSub)
    (hl_unit : ∃ i, (l * hproj.homogCoords Z i)⁻¹ ∈ R.valSub) :
    ∃ P : Z.toVariety.carrier, localRing_le P R := by


  obtain ⟨j, hj_inv⟩ := hl_unit


  have hcoord_ratios : ∀ i, hproj.homogCoords Z i * (hproj.homogCoords Z j)⁻¹ ∈ R.valSub := by
    intro i

    have key : hproj.homogCoords Z i * (hproj.homogCoords Z j)⁻¹ =
        (l * hproj.homogCoords Z i) * (l * hproj.homogCoords Z j)⁻¹ := by
      field_simp
    rw [key]
    exact R.valSub.toSubring.mul_mem (hl_mem i) hj_inv


  exact affineChartLocalRing hproj Z j R hcoord_ratios

/-- A projective variety satisfies the valuation criterion of properness. -/
theorem projective_variety_satisfies_valuation_criterion
    {k : Type u} [Field k]
    (V : AlgVariety k) (hproj : IsProjectiveVariety V) :
    SatisfiesValuationCriterion V := by
  intro Z R


  obtain ⟨l, hl_ne, hl_mem, hl_unit⟩ :=
    lemma_16_32 R.valSub hproj.n (hproj.homogCoords Z) (hproj.homogCoords_ne_zero Z)

  exact pointFromScaledCoords_lemma hproj Z R l hl_ne hl_mem hl_unit

/-- Projective varieties are complete: over an algebraically closed field, every projective variety satisfies the topological completeness condition. -/
theorem projective_variety_isComplete
    {k : Type u} [Field k] [IsAlgClosed k]
    (V : AlgVariety k) (hproj : IsProjectiveVariety V) :
    IsCompleteVariety V.carrier :=
  completeness_valuation_criterion V (projective_variety_satisfies_valuation_criterion V hproj)

end AlgebraicGeometry.CompletenessValuationCriterion

/-- (Theorem 16.33) The structure morphism $\mathrm{Proj}\,\mathcal{A} \to \mathrm{Spec}\,\mathcal{A}_0$ from a finitely generated $\mathbb{N}$-graded ring is proper. -/
theorem theorem_16_33
    {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] [Algebra.FiniteType (𝒜 0) A] :
    IsProper (Proj.toSpecZero 𝒜) :=
  inferInstance
