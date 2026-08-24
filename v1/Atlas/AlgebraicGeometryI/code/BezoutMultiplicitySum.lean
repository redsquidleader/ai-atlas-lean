/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.AlgebraicGeometryI.code.BezoutLight
import Mathlib.RingTheory.Localization.AtPrime.Basic

noncomputable section

open MvPolynomial

variable (k : Type*) [Field k]

/-- The projective intersection number of two homogeneous polynomials `f, g` in three variables,
defined as the `k`-dimension of the degree-`n` piece of `k[x,y,z] / (⟨f⟩ + ⟨g⟩)`. -/
noncomputable def projectiveIntersectionNumber
    (f g : MvPolynomial (Fin 3) k) (n : ℕ) : ℕ :=
  Module.finrank k (homogQuotPiece k (Ideal.span {f} ⊔ Ideal.span {g}) n)

/-- Equal ideals give equal homogeneous quotient piece dimensions. -/
lemma homogQuotPiece_ideal_eq {I J : Ideal (MvPolynomial (Fin 3) k)} (h : I = J) (n : ℕ) :
    Module.finrank k (homogQuotPiece k I n) = Module.finrank k (homogQuotPiece k J n) := by
  subst h; rfl

/-- Bezout's theorem in multiplicity-sum form: for coprime homogeneous `f, g` of degrees `d, e`
and sufficiently large `n`, the projective intersection number equals `d * e`. -/
theorem bezout_theorem_multiplicity_sum
    (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (f g : MvPolynomial (Fin 3) k)
    (hf_homog : f.IsHomogeneous d)
    (hg_homog : g.IsHomogeneous e)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hcoprime : IsCoprime f g) :
    ∀ n, d + e - 2 ≤ n →
      projectiveIntersectionNumber k f g n = d * e := by
  intro n hn
  exact bezout_theorem k d e hd he f g hf_homog hg_homog hf_ne hg_ne hcoprime n hn

/-- Symmetry of the projective intersection number in its two homogeneous arguments. -/
theorem projectiveIntersectionNumber_comm
    (f g : MvPolynomial (Fin 3) k) (n : ℕ) :
    projectiveIntersectionNumber k f g n =
    projectiveIntersectionNumber k g f n := by
  unfold projectiveIntersectionNumber
  have h : Ideal.span {f} ⊔ Ideal.span {g} = Ideal.span {g} ⊔ Ideal.span {f} := by
    rw [sup_comm]
  exact homogQuotPiece_ideal_eq k h n

/-- Two distinct lines in `P²` intersect in exactly one point (counted with multiplicity). -/
theorem bezout_line_line
    (f g : MvPolynomial (Fin 3) k)
    (hf : f.IsHomogeneous 1) (hg : g.IsHomogeneous 1)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0) (hcop : IsCoprime f g)
    (n : ℕ) :
    projectiveIntersectionNumber k f g n = 1 := by
  have := bezout_theorem_multiplicity_sum k 1 1 one_pos one_pos f g
    hf hg hf_ne hg_ne hcop n (by omega)
  simp at this
  exact this

/-- A line meets a conic in `P²` in exactly `1 · 2 = 2` points (counted with multiplicity). -/
theorem bezout_line_conic
    (f g : MvPolynomial (Fin 3) k)
    (hf : f.IsHomogeneous 1) (hg : g.IsHomogeneous 2)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0) (hcop : IsCoprime f g)
    (n : ℕ) (hn : 1 ≤ n) :
    projectiveIntersectionNumber k f g n = 2 := by
  have := bezout_theorem_multiplicity_sum k 1 2 one_pos (by norm_num) f g
    hf hg hf_ne hg_ne hcop n (by omega)
  simpa using this

/-- Two distinct conics in `P²` intersect in `2 · 2 = 4` points (counted with multiplicity). -/
theorem bezout_conic_conic
    (f g : MvPolynomial (Fin 3) k)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0) (hcop : IsCoprime f g)
    (n : ℕ) (hn : 2 ≤ n) :
    projectiveIntersectionNumber k f g n = 4 := by
  have := bezout_theorem_multiplicity_sum k 2 2 (by norm_num) (by norm_num) f g
    hf hg hf_ne hg_ne hcop n (by omega)
  simpa using this

/-- A line meets a smooth cubic in `P²` in `1 · 3 = 3` points (counted with multiplicity). -/
theorem bezout_line_cubic
    (f g : MvPolynomial (Fin 3) k)
    (hf : f.IsHomogeneous 1) (hg : g.IsHomogeneous 3)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0) (hcop : IsCoprime f g)
    (n : ℕ) (hn : 2 ≤ n) :
    projectiveIntersectionNumber k f g n = 3 := by
  have := bezout_theorem_multiplicity_sum k 1 3 one_pos (by norm_num) f g
    hf hg hf_ne hg_ne hcop n (by omega)
  simpa using this

/-- A point of intersection of the projective varieties `V(f)` and `V(g)`, encoded as a prime
ideal of `k[x, y, z]` containing both `f` and `g`. -/
structure ProjectivePoint (k : Type*) [Field k]
    (f g : MvPolynomial (Fin 3) k) where
  P : Ideal (MvPolynomial (Fin 3) k)
  hP_prime : P.IsPrime
  hf_mem : f ∈ P
  hg_mem : g ∈ P

/-- Local intersection multiplicity at a projective intersection point `p` of `f` and `g`,
defined as the `k`-dimension of the localisation of `k[x, y, z] / (⟨f⟩ + ⟨g⟩)` at the image
of `p`. -/
noncomputable def projLocalIntersectionMultiplicity
    (f g : MvPolynomial (Fin 3) k)
    (p : ProjectivePoint k f g) : ℕ := by
  let I := Ideal.span {f} ⊔ Ideal.span {g}
  let Q := p.P.map (Ideal.Quotient.mk I)
  have hI_le_P : I ≤ p.P := by
    apply sup_le
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr p.hf_mem)
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr p.hg_mem)
  have hQ_prime : Q.IsPrime := by
    haveI := p.hP_prime
    apply Ideal.map_isPrime_of_surjective
    · exact Ideal.Quotient.mk_surjective
    · intro x hx
      rw [Ideal.mk_ker] at hx
      exact hI_le_P hx
  exact @Module.finrank k (@Localization.AtPrime _ _ Q hQ_prime) _ _ _

/-- For coprime homogeneous polynomials `f, g`, only finitely many projective points have a
nonzero local intersection multiplicity. -/
theorem projLocalIntersectionMultiplicity_finite
    (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (f g : MvPolynomial (Fin 3) k)
    (hf_homog : f.IsHomogeneous d)
    (hg_homog : g.IsHomogeneous e)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hcoprime : IsCoprime f g) :
    ∃ (S : Finset (ProjectivePoint k f g)),
      (∀ p, projLocalIntersectionMultiplicity k f g p ≠ 0 → p ∈ S) ∧
      (∀ p ∈ S, projLocalIntersectionMultiplicity k f g p ≠ 0) := by
  sorry

/-- Artinian decomposition for the homogeneous quotient: the sum of local multiplicities at the
intersection points equals the dimension of the stable graded piece. -/
theorem artinian_decomposition_sum
    (k : Type*) [Field k]
    (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (f g : MvPolynomial (Fin 3) k)
    (hf_homog : f.IsHomogeneous d)
    (hg_homog : g.IsHomogeneous e)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hcoprime : IsCoprime f g)
    (S : Finset (ProjectivePoint k f g))
    (hS : ∀ p, projLocalIntersectionMultiplicity k f g p ≠ 0 → p ∈ S)
    (hS' : ∀ p ∈ S, projLocalIntersectionMultiplicity k f g p ≠ 0)
    (n : ℕ) (hn : d + e - 2 ≤ n) :
    S.sum (fun p => projLocalIntersectionMultiplicity k f g p) =
    Module.finrank k (homogQuotPiece k (Ideal.span {f} ⊔ Ideal.span {g}) n) := by sorry

/-- Projective Bezout (multiplicity-sum form): for coprime homogeneous `f, g` of degrees `d, e`
the sum of local intersection multiplicities over all intersection points equals `d * e`. -/
theorem projective_bezout_multiplicity_sum
    (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (f g : MvPolynomial (Fin 3) k)
    (hf_homog : f.IsHomogeneous d)
    (hg_homog : g.IsHomogeneous e)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hcoprime : IsCoprime f g)
    (S : Finset (ProjectivePoint k f g))
    (hS : ∀ p, projLocalIntersectionMultiplicity k f g p ≠ 0 → p ∈ S)
    (hS' : ∀ p ∈ S, projLocalIntersectionMultiplicity k f g p ≠ 0) :
    S.sum (fun p => projLocalIntersectionMultiplicity k f g p) = d * e := by


  rw [artinian_decomposition_sum k d e hd he f g hf_homog hg_homog hf_ne hg_ne
      hcoprime S hS hS' (d + e - 2) le_rfl]


  exact bezout_theorem k d e hd he f g hf_homog hg_homog hf_ne hg_ne hcoprime
    (d + e - 2) le_rfl

end
