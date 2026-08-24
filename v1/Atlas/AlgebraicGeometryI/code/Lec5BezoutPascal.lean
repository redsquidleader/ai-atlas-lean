/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Atlas.AlgebraicGeometryI.code.BezoutMultiplicitySum

open MvPolynomial Classical

noncomputable section

namespace Lec5BezoutPascal

variable (k : Type*) [Field k]

/-- The projective plane `P^2` over `k`, identified with the projectivization of `k^3`. -/
abbrev P2 := Projectivization k (Fin 3 → k)

/-- A point `p ∈ P^2` lies on the curve defined by a polynomial `f` if `f` vanishes on a (any)
representative of `p`. -/
def P2.liesOn (p : P2 k) (f : MvPolynomial (Fin 3) k) : Prop :=
  MvPolynomial.eval (Projectivization.rep p) f = 0

/-- Translate of a polynomial `g` by a point `p`: the polynomial obtained by substituting
`x_i ↦ x_i + p_i`. -/
def translatePoly {n : ℕ} (g : MvPolynomial (Fin n) k) (p : Fin n → k) :
    MvPolynomial (Fin n) k :=
  MvPolynomial.aeval (fun i => X i + C (p i)) g

/-- Translation of polynomials by a fixed point is an injective operation, since translating by
`-p` is a left inverse. -/
lemma translatePoly_injective {n : ℕ} (p : Fin n → k) :
    Function.Injective (fun g => translatePoly k g p) := by
  suffices h : ∀ g : MvPolynomial (Fin n) k,
      translatePoly k (translatePoly k g p) (fun i => -p i) = g by
    exact Function.HasLeftInverse.injective
      ⟨fun g => translatePoly k g (fun i => -p i), h⟩
  intro g
  simp only [translatePoly]
  conv_rhs => rw [← AlgHom.id_apply (R := k) g]
  rw [← AlgHom.comp_apply]
  congr 1; ext i; simp [map_add, map_neg]

/-- Translating a nonzero polynomial yields a nonzero polynomial. -/
lemma translatePoly_ne_zero {n : ℕ} (g : MvPolynomial (Fin n) k) (p : Fin n → k)
    (hg : g ≠ 0) : translatePoly k g p ≠ 0 := by
  intro heq; apply hg
  have hinj := translatePoly_injective k p
  have h0 : translatePoly k (0 : MvPolynomial (Fin n) k) p = 0 := by
    simp [translatePoly, map_zero]
  have : (fun g => translatePoly k g p) g = (fun g => translatePoly k g p) 0 := by
    simp only; rw [heq, h0]
  exact hinj this

/-- A nonzero polynomial has a nonzero homogeneous component of some degree. -/
lemma exists_homogeneousComponent_ne_zero {n : ℕ}
    (φ : MvPolynomial (Fin n) k) (h : φ ≠ 0) :
    ∃ m : ℕ, MvPolynomial.homogeneousComponent m φ ≠ 0 := by
  by_contra hall; push Not at hall; apply h
  have := MvPolynomial.sum_homogeneousComponent φ
  simp only [hall, Finset.sum_const_zero] at this; exact this.symm

/-- Multiplicity of a hypersurface `V(g)` at a point `p`: the smallest degree at which the
translate `g(x + p)` has a nonzero homogeneous component. -/
def hypersurfaceMultiplicity {n : ℕ} (g : MvPolynomial (Fin n) k) (p : Fin n → k)
    (hg : g ≠ 0) : ℕ :=
  Nat.find (exists_homogeneousComponent_ne_zero k (translatePoly k g p)
    (translatePoly_ne_zero k g p hg))

/-- At the multiplicity, the corresponding homogeneous component of `g(x + p)` is nonzero. -/
lemma hypersurfaceMultiplicity_spec {n : ℕ} (g : MvPolynomial (Fin n) k) (p : Fin n → k)
    (hg : g ≠ 0) :
    MvPolynomial.homogeneousComponent (hypersurfaceMultiplicity k g p hg)
      (translatePoly k g p) ≠ 0 :=
  Nat.find_spec (exists_homogeneousComponent_ne_zero k (translatePoly k g p)
    (translatePoly_ne_zero k g p hg))

/-- Below the multiplicity, every homogeneous component of the translated polynomial vanishes. -/
lemma hypersurfaceMultiplicity_min {n : ℕ} (g : MvPolynomial (Fin n) k) (p : Fin n → k)
    (hg : g ≠ 0) (m : ℕ) (hm : m < hypersurfaceMultiplicity k g p hg) :
    MvPolynomial.homogeneousComponent m (translatePoly k g p) = 0 := by
  by_contra h
  exact Nat.lt_irrefl _ (lt_of_lt_of_le hm (Nat.find_min' _ h))

/-- The coordinate ring of the intersection scheme of two affine plane curves `V(f)` and `V(g)`:
the quotient `k[x, y] / (f, g)`. -/
abbrev CurveQuotient (f g : MvPolynomial (Fin 2) k) :=
  MvPolynomial (Fin 2) k ⧸ (Ideal.span {f, g})

/-- Multiplication-by-`x_i` operator on the curve quotient `k[x, y]/(f, g)`, viewed as a
`k`-linear endomorphism. -/
def mulByVarOperator (f g : MvPolynomial (Fin 2) k) (i : Fin 2) :
    Module.End k (CurveQuotient k f g) :=
  Algebra.lmul k _ (Ideal.Quotient.mk _ (X i))

/-- Intersection multiplicity of two affine plane curves at a point `p`: the dimension of the
joint generalized eigenspace of the multiplication-by-coordinate operators at the eigenvalue `p`. -/
def intersectionMultiplicity (f g : MvPolynomial (Fin 2) k) (p : Fin 2 → k)
    [Module.Finite k (CurveQuotient k f g)] : ℕ :=
  Module.finrank k ↥(
    (mulByVarOperator k f g 0).genEigenspace (p 0) ⊤ ⊓
    (mulByVarOperator k f g 1).genEigenspace (p 1) ⊤
      : Submodule k (CurveQuotient k f g))

/-- A plane projective curve in `P^2`: a nonzero homogeneous polynomial in three variables of a
given degree. -/
structure PlaneCurve where
  poly : MvPolynomial (Fin 3) k
  poly_ne_zero : poly ≠ 0
  deg : ℕ
  poly_homogeneous : poly.IsHomogeneous deg

/-- The vanishing locus of a plane curve `C` as a subset of `P^2`. -/
def PlaneCurve.vanishingLocus (C : PlaneCurve k) : Set (P2 k) :=
  {p | P2.liesOn k p C.poly}

/-- Two plane curves have no common irreducible component iff their defining polynomials are
coprime. -/
def PlaneCurve.noCommonComponent (C₁ C₂ : PlaneCurve k) : Prop :=
  IsCoprime C₁.poly C₂.poly

/-- The set of intersection points of two plane curves: the intersection of their vanishing loci
in `P^2`. -/
def PlaneCurve.intersectionPoints (C₁ C₂ : PlaneCurve k) : Set (P2 k) :=
  C₁.vanishingLocus k ∩ C₂.vanishingLocus k

/-- Finiteness part of Bezout: two plane curves with no common component meet in a finite set of
points in `P^2`. -/
theorem bezout_intersection_finite
    (k : Type*) [Field k] [IsAlgClosed k]
    (C₁ C₂ : PlaneCurve k)
    (hcoprime : C₁.noCommonComponent k C₂) :
    ∃ S : Finset (P2 k), ↑S = C₁.intersectionPoints k C₂ := by sorry

/-- Multiplicity-sum part of Bezout: counted with multiplicities, the intersection points of two
plane curves without common component sum to the product of their degrees. -/
theorem bezout_multiplicity_sum
    (k : Type*) [Field k] [IsAlgClosed k]
    (C₁ C₂ : PlaneCurve k)
    (hcoprime : C₁.noCommonComponent k C₂)
    (S : Finset (P2 k))
    (hS : ↑S = C₁.intersectionPoints k C₂) :
    ∃ mult : P2 k → ℕ,
      (∀ p ∈ S, 0 < mult p) ∧
      (∀ p, p ∉ S → mult p = 0) ∧
      (S.sum mult = C₁.deg * C₂.deg) := by sorry

/-- Lecture 5, Theorem 5.2 (Bezout): for two plane projective curves over an algebraically closed
field without common component, the intersection is a finite set whose multiplicities sum to the
product of the degrees. -/
theorem bezout_theorem_5_2 :
  ∀ (k : Type*) [Field k] [IsAlgClosed k]
    (C₁ C₂ : PlaneCurve k)
    (hcoprime : C₁.noCommonComponent k C₂),
  ∃ (S : Finset (P2 k)) (mult : P2 k → ℕ),
    (↑S = C₁.intersectionPoints k C₂) ∧
    (∀ p ∈ S, 0 < mult p) ∧
    (∀ p, p ∉ S → mult p = 0) ∧
    (S.sum mult = C₁.deg * C₂.deg) := by
  intro k _ _ C₁ C₂ hcoprime
  obtain ⟨S, hS⟩ := bezout_intersection_finite k C₁ C₂ hcoprime
  obtain ⟨mult, hpos, hzero, hsum⟩ := bezout_multiplicity_sum k C₁ C₂ hcoprime S hS
  exact ⟨S, mult, hS, hpos, hzero, hsum⟩

/-- Projective form of Bezout (multiplicity-sum statement): the sum of local intersection
multiplicities of two coprime homogeneous polynomials in three variables equals the product of
their degrees. -/
theorem bezout_projective
    (k : Type*) [Field k]
    (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (f g : MvPolynomial (Fin 3) k)
    (hf_homog : f.IsHomogeneous d)
    (hg_homog : g.IsHomogeneous e)
    (hf_ne : f ≠ 0) (hg_ne : g ≠ 0)
    (hcoprime : IsCoprime f g)
    (S : Finset (ProjectivePoint k f g))
    (hS : ∀ p, projLocalIntersectionMultiplicity k f g p ≠ 0 → p ∈ S)
    (hS' : ∀ p ∈ S, projLocalIntersectionMultiplicity k f g p ≠ 0) :
    S.sum (fun p => projLocalIntersectionMultiplicity k f g p) = d * e :=
  projective_bezout_multiplicity_sum k d e hd he f g hf_homog hg_homog hf_ne hg_ne hcoprime S hS hS'

/-- Three points in `P^2` are *collinear* if some nonzero linear form vanishes at all of them. -/
def P2Collinear (p q r : P2 k) : Prop :=
  ∃ (L : MvPolynomial (Fin 3) k),
    L ≠ 0 ∧ L.IsHomogeneous 1 ∧
    P2.liesOn k p L ∧ P2.liesOn k q L ∧ P2.liesOn k r L

/-- A plane curve is a *conic* if its degree is `2`. -/
def IsConic (C : PlaneCurve k) : Prop := C.deg = 2

/-- Defining linear form of the line through two points of `P^2`, given by the cross product of
their representatives. -/
def lineThroughPoints (p q : P2 k) : MvPolynomial (Fin 3) k :=
  let pv := Projectivization.rep p
  let qv := Projectivization.rep q
  C (pv 1 * qv 2 - pv 2 * qv 1) * X 0 +
  C (pv 2 * qv 0 - pv 0 * qv 2) * X 1 +
  C (pv 0 * qv 1 - pv 1 * qv 0) * X 2

/-- Data of a hexagon inscribed in a conic: the conic, six distinct vertices on it, indexed
cyclically by `Fin 6`. -/
structure PascalInscribedHexagon where
  conic : PlaneCurve k
  is_conic : IsConic k conic
  vertex : Fin 6 → P2 k
  vertices_on_conic : ∀ i, P2.liesOn k (vertex i) conic.poly
  vertices_distinct : Function.Injective vertex

/-- Cyclic successor on `Fin 6`, used to index the sides of an inscribed hexagon. -/
def hexNext (i : Fin 6) : Fin 6 := ⟨(i.val + 1) % 6, Nat.mod_lt _ (by omega)⟩

/-- Opposite vertex map on `Fin 6` (shift by 3), used to pair opposite sides of an inscribed
hexagon. -/
def hexOpposite (i : Fin 6) : Fin 6 := ⟨(i.val + 3) % 6, Nat.mod_lt _ (by omega)⟩

/-- The `i`-th side of an inscribed hexagon: the line through the `i`-th and `(i + 1)`-th
vertices. -/
def PascalInscribedHexagon.side (H : PascalInscribedHexagon k) (i : Fin 6) :
    MvPolynomial (Fin 3) k :=
  lineThroughPoints k (H.vertex i) (H.vertex (hexNext i))

/-- Consequence of Bezout: if an irreducible conic `q` and a cubic `f` share more than `6`
points, then `q` divides `f`. -/
theorem bezout_excess_intersection_implies_divisibility :
  ∀ (k : Type*) [Field k] [IsAlgClosed k]
    (q f : MvPolynomial (Fin 3) k)
    (_hq_irred : Irreducible q) (_hq_homog : q.IsHomogeneous 2)
    (_hf_ne : f ≠ 0) (_hf_homog : f.IsHomogeneous 3)
    (S : Finset (P2 k)) (_hS_card : 6 < S.card)
    (_hS_on_q : ∀ p ∈ S, P2.liesOn k p q)
    (_hS_on_f : ∀ p ∈ S, P2.liesOn k p f),
    q ∣ f := by sorry

/-- If `q` is homogeneous of degree `m` and `q * L` is homogeneous of degree `n ≥ m`, then `L`
is itself homogeneous of degree `n - m`. -/
theorem isHomogeneous_of_homogeneous_dvd :
  ∀ (k : Type*) [Field k] (σ : Type*) [DecidableEq σ]
    (q L : MvPolynomial σ k) (m n : ℕ),
    q ≠ 0 → q.IsHomogeneous m → (q * L).IsHomogeneous n → m ≤ n →
    L.IsHomogeneous (n - m) := by sorry

/-- If a conic divides a cubic, then the cubic factors as the conic times a linear form, and the
cubic vanishes at a point iff the conic or the line does. -/
theorem conic_divides_cubic_gives_line :
  ∀ (k : Type*) [Field k]
    (q f : MvPolynomial (Fin 3) k)
    (_hq_ne : q ≠ 0) (_hq_homog : q.IsHomogeneous 2)
    (_hf_homog : f.IsHomogeneous 3)
    (_hdvd : q ∣ f),
    ∃ L : MvPolynomial (Fin 3) k,
      L.IsHomogeneous 1 ∧ f = q * L ∧
      (∀ p : P2 k, P2.liesOn k p f ↔ (P2.liesOn k p q ∨ P2.liesOn k p L)) := by
  intro k inst q f hq_ne hq_hom hf_hom hdvd
  obtain ⟨L, hfL⟩ := hdvd
  refine ⟨L, ?_, hfL, ?_⟩
  ·
    have hqL_hom : (q * L).IsHomogeneous 3 := hfL ▸ hf_hom
    have := isHomogeneous_of_homogeneous_dvd k (Fin 3) q L 2 3 hq_ne hq_hom hqL_hom (by omega)
    simp at this; exact this
  ·
    intro p; simp only [P2.liesOn]
    constructor
    · intro heval; rw [hfL, map_mul (MvPolynomial.eval _)] at heval
      exact mul_eq_zero.mp heval
    · intro h; rcases h with h | h
      · rw [hfL, map_mul (MvPolynomial.eval _), h, zero_mul]
      · rw [hfL, map_mul (MvPolynomial.eval _), h, mul_zero]
/-- Auxiliary construction underlying the proof of Pascal's theorem: from a hexagon inscribed in
an irreducible conic, exhibit the three opposite-side intersection points, a cubic vanishing on
the six vertices and the three intersection points, and an additional seventh conic point witnessing
the divisibility argument. -/
theorem pascal_cubic_construction :
  ∀ (k : Type*) [Field k] [IsAlgClosed k]
    (H : PascalInscribedHexagon k)
    (_hconic_irred : Irreducible H.conic.poly),
    ∃ (P₁ P₂ P₃ : P2 k)
      (P_cubic : MvPolynomial (Fin 3) k)
      (p₇ : P2 k),
    (P2.liesOn k P₁ (H.side k 0) ∧ P2.liesOn k P₁ (H.side k 3)) ∧
    (P2.liesOn k P₂ (H.side k 1) ∧ P2.liesOn k P₂ (H.side k 4)) ∧
    (P2.liesOn k P₃ (H.side k 2) ∧ P2.liesOn k P₃ (H.side k 5)) ∧
    P_cubic ≠ 0 ∧
    P_cubic.IsHomogeneous 3 ∧
    (∀ i, P2.liesOn k (H.vertex i) P_cubic) ∧
    P2.liesOn k p₇ H.conic.poly ∧
    (∀ i, p₇ ≠ H.vertex i) ∧
    P2.liesOn k p₇ P_cubic ∧
    P2.liesOn k P₁ P_cubic ∧
    P2.liesOn k P₂ P_cubic ∧
    P2.liesOn k P₃ P_cubic ∧
    ¬ P2.liesOn k P₁ H.conic.poly ∧
    ¬ P2.liesOn k P₂ H.conic.poly ∧
    ¬ P2.liesOn k P₃ H.conic.poly := by sorry

/-- Lecture 5, Theorem 5.3 (Pascal): given a hexagon inscribed in an irreducible conic, the three
intersection points of opposite sides are collinear. -/
theorem pascal_hexagon_theorem [IsAlgClosed k]
    (H : PascalInscribedHexagon k) (hconic_irred : Irreducible H.conic.poly) :
    ∃ P₁ P₂ P₃ : P2 k,
      (P2.liesOn k P₁ (H.side k 0) ∧ P2.liesOn k P₁ (H.side k 3)) ∧
      (P2.liesOn k P₂ (H.side k 1) ∧ P2.liesOn k P₂ (H.side k 4)) ∧
      (P2.liesOn k P₃ (H.side k 2) ∧ P2.liesOn k P₃ (H.side k 5)) ∧
      P2Collinear k P₁ P₂ P₃ := by
  obtain ⟨P₁, P₂, P₃, P_cubic, p₇,
    hP₁_sides, hP₂_sides, hP₃_sides,
    hPc_ne, hPc_homog, hPc_vert,
    hp₇_on, hp₇_ne, hPc_p7,
    hPc_P1, hPc_P2, hPc_P3,
    hP₁_off, hP₂_off, hP₃_off⟩ :=
    pascal_cubic_construction k H hconic_irred
  refine ⟨P₁, P₂, P₃, hP₁_sides, hP₂_sides, hP₃_sides, ?_⟩
  set S := (Finset.univ.image H.vertex).cons p₇
    (by simp [Finset.mem_image]; push Not; exact fun i => (hp₇_ne i).symm)
    with hS_def
  have hS_card : 6 < S.card := by
    show 6 < ((Finset.univ.image H.vertex).cons p₇ _).card
    rw [Finset.card_cons, Finset.card_image_of_injective _ H.vertices_distinct,
      Finset.card_univ, Fintype.card_fin]
    omega
  have hS_on_conic : ∀ p ∈ S, P2.liesOn k p H.conic.poly := by
    intro p hp
    have := Finset.mem_cons.mp hp
    rcases this with rfl | hmem
    · exact hp₇_on
    · rw [Finset.mem_image] at hmem
      obtain ⟨i, _, rfl⟩ := hmem
      exact H.vertices_on_conic i
  have hS_on_cubic : ∀ p ∈ S, P2.liesOn k p P_cubic := by
    intro p hp
    have := Finset.mem_cons.mp hp
    rcases this with rfl | hmem
    · exact hPc_p7
    · rw [Finset.mem_image] at hmem
      obtain ⟨i, _, rfl⟩ := hmem
      exact hPc_vert i
  have hq_homog2 : H.conic.poly.IsHomogeneous 2 :=
    H.is_conic ▸ H.conic.poly_homogeneous
  have hdvd := bezout_excess_intersection_implies_divisibility k
    H.conic.poly P_cubic hconic_irred hq_homog2 hPc_ne hPc_homog
    S hS_card hS_on_conic hS_on_cubic
  obtain ⟨L, hL_hom, hPc_eq, hPc_iff⟩ := conic_divides_cubic_gives_line k
    H.conic.poly P_cubic H.conic.poly_ne_zero hq_homog2 hPc_homog hdvd
  have hL_ne : L ≠ 0 := by
    intro h; exact hPc_ne (by rw [hPc_eq, h, mul_zero])
  exact ⟨L, hL_ne, hL_hom,
    ((hPc_iff P₁).mp hPc_P1).resolve_left hP₁_off,
    ((hPc_iff P₂).mp hPc_P2).resolve_left hP₂_off,
    ((hPc_iff P₃).mp hPc_P3).resolve_left hP₃_off⟩

end Lec5BezoutPascal
