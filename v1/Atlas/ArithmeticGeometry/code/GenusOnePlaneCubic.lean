/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open MvPolynomial AlgebraicGeometry CategoryTheory

/-- A smooth projective curve over a field $k$ packaged as: an underlying scheme (with proofs of
integrality, Krull dimension one, nonemptiness), a structure morphism to $\mathrm{Spec}\,k$, and a
(declared) genus value. The smoothness is left implicit. -/
structure SmoothProjectiveCurveOverField (k : Type*) [Field k] where
  toScheme : Scheme
  isIntegral : AlgebraicGeometry.IsIntegral toScheme
  krullDim_eq : topologicalKrullDim toScheme = 1
  nonempty : Nonempty toScheme
  structureMorphism : toScheme ⟶ Spec (CommRingCat.of k)
  genusVal : ℕ

namespace SmoothProjectiveCurveOverField

/-- The genus of a smooth projective curve, given by the structural field `genusVal`. -/
def genus {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k) : ℕ := C.genusVal

/-- A smooth projective curve has a rational point if its structure morphism admits a section, i.e.
a morphism $\mathrm{Spec}\,k \to C$ that composes to the identity. -/
def HasRationalPoint {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k) : Prop :=
  ∃ s : Spec (CommRingCat.of k) ⟶ C.toScheme, s ≫ C.structureMorphism = 𝟙 _

end SmoothProjectiveCurveOverField

/-- A plane cubic over $k$: a nonzero homogeneous polynomial of degree $3$ in three variables. -/
structure PlaneCubic (k : Type*) [Field k] where
  poly : MvPolynomial (Fin 3) k
  isHomogeneous : poly.IsHomogeneous 3
  ne_zero : poly ≠ 0

/-- A plane cubic has a rational point if there is a nonzero $k$-tuple $p \in k^3$ with
$F(p) = 0$. -/
def PlaneCubic.HasRationalPoint {k : Type*} [Field k] (F : PlaneCubic k) : Prop :=
  ∃ p : Fin 3 → k, p ≠ 0 ∧ MvPolynomial.eval p F.poly = 0

/-- Axiomatized: the scheme attached to a plane cubic, namely $\mathrm{Proj}$ of
$k[X, Y, Z] / (F)$. -/
noncomputable def PlaneCubic.toScheme_ax {k : Type*} [Field k] (C : PlaneCubic k) :
    AlgebraicGeometry.Scheme := by sorry

/-- Axiomatized: the structure morphism of the scheme attached to a plane cubic. -/
noncomputable def PlaneCubic.toStructureMorphism_ax {k : Type*} [Field k] (C : PlaneCubic k) :
    PlaneCubic.toScheme_ax C ⟶ Spec (CommRingCat.of k) := by sorry

/-- The scheme associated to a plane cubic, wrapping `toScheme_ax`. -/
def PlaneCubic.toScheme {k : Type*} [Field k] (F : PlaneCubic k) :
    AlgebraicGeometry.Scheme :=
  PlaneCubic.toScheme_ax F

/-- The structure morphism of `PlaneCubic.toScheme`, wrapping `toStructureMorphism_ax`. -/
def PlaneCubic.toSchemeStructureMorphism {k : Type*} [Field k]
    (F : PlaneCubic k) : F.toScheme ⟶ Spec (CommRingCat.of k) :=
  PlaneCubic.toStructureMorphism_ax F

/-- Axiomatized: a plane cubic has a rational point in the polynomial sense if and only if its
scheme admits a $k$-section. -/
theorem PlaneCubic.hasRationalPoint_iff_section {k : Type*} [Field k] (F : PlaneCubic k) :
    F.HasRationalPoint ↔
      ∃ s : Spec (CommRingCat.of k) ⟶ F.toScheme,
        s ≫ F.toSchemeStructureMorphism = 𝟙 _ := by sorry

/-- The (declared) genus of a plane cubic, set to be $1$ in agreement with the genus formula for a
smooth plane curve of degree $3$. -/
def PlaneCubic.genus {k : Type*} [Field k] (_F : PlaneCubic k) : ℕ :=
  1

/-- Axiomatized: the scheme of a plane cubic is integral. -/
theorem PlaneCubic.toScheme_isIntegral {k : Type*} [Field k] (F : PlaneCubic k) :
    AlgebraicGeometry.IsIntegral F.toScheme := by sorry

/-- Axiomatized: the scheme of a plane cubic has Krull dimension one. -/
theorem PlaneCubic.toScheme_krullDim {k : Type*} [Field k] (F : PlaneCubic k) :
    topologicalKrullDim F.toScheme = 1 := by sorry

/-- Axiomatized: the scheme of a plane cubic is nonempty. -/
theorem PlaneCubic.toScheme_nonempty {k : Type*} [Field k] (F : PlaneCubic k) :
    Nonempty F.toScheme := by sorry

/-- Bundling a plane cubic into a `SmoothProjectiveCurveOverField`, combining the integrality,
Krull-dimension, nonemptiness, structure-morphism, and genus data. -/
def PlaneCubic.toSmoothProjectiveCurveOverField {k : Type*} [Field k]
    (F : PlaneCubic k) : SmoothProjectiveCurveOverField k :=
  { toScheme := F.toScheme
    isIntegral := F.toScheme_isIntegral
    krullDim_eq := F.toScheme_krullDim
    nonempty := F.toScheme_nonempty
    structureMorphism := F.toSchemeStructureMorphism
    genusVal := F.genus }

/-- Compatibility: the genus of the bundled curve equals the genus of the plane cubic. -/
theorem PlaneCubic.toSmoothProjectiveCurveOverField_genus {k : Type*} [Field k]
    (F : PlaneCubic k) : F.toSmoothProjectiveCurveOverField.genus = F.genus := rfl

/-- Axiomatized: the genus is invariant under $k$-isomorphism of schemes that are compatible with
the structure morphisms. -/
theorem genus_eq_of_scheme_iso
    {k : Type*} [Field k]
    (C₁ C₂ : SmoothProjectiveCurveOverField k)
    (φ : C₁.toScheme ≅ C₂.toScheme)
    (hφ : φ.hom ≫ C₂.structureMorphism = C₁.structureMorphism) :
    C₁.genus = C₂.genus := by sorry

namespace SmoothProjectiveCurveOverField

/-- The property that the smooth projective curve $C$ is $k$-isomorphic to (the scheme attached to)
a plane cubic $F$, compatibly with the structure morphisms to $\mathrm{Spec}\,k$. -/
def IsIsomorphicTo {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k) (F : PlaneCubic k) : Prop :=
  ∃ (φ : C.toScheme ≅ F.toScheme),
    φ.hom ≫ F.toSchemeStructureMorphism = C.structureMorphism

/-- Transport of rational points along a $k$-isomorphism: if $F$ has a rational point and
$C \simeq F$ over $k$, then $C$ has a rational point. -/
theorem hasRationalPoint_of_isIsomorphicTo
    {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k) (F : PlaneCubic k)
    (hiso : C.IsIsomorphicTo F) (hpt : F.HasRationalPoint) :
    C.HasRationalPoint := by
  obtain ⟨φ, hcompat⟩ := hiso
  obtain ⟨s, hs⟩ := F.hasRationalPoint_iff_section.mp hpt
  exact ⟨s ≫ φ.inv, by
    simp only [Category.assoc]
    rw [← hcompat, ← Category.assoc, ← Category.assoc]
    simp [Iso.inv_hom_id, hs]⟩

/-- Two-way invariance: under a $k$-isomorphism $C \simeq F$, the existence of a rational point is
preserved in both directions. -/
theorem hasRationalPoint_iff_of_isIsomorphicTo
    {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k) (F : PlaneCubic k)
    (hiso : C.IsIsomorphicTo F) :
    C.HasRationalPoint ↔ F.HasRationalPoint := by
  rw [PlaneCubic.hasRationalPoint_iff_section]
  constructor
  ·
    rintro ⟨s, hs⟩
    obtain ⟨φ, hcompat⟩ := hiso
    exact ⟨s ≫ φ.hom, by rw [Category.assoc, hcompat, hs]⟩
  ·
    rintro ⟨s, hs⟩
    obtain ⟨φ, hcompat⟩ := hiso
    exact ⟨s ≫ φ.inv, by
      simp only [Category.assoc]
      rw [← hcompat, ← Category.assoc, ← Category.assoc]
      simp [Iso.inv_hom_id, hs]⟩

end SmoothProjectiveCurveOverField

/-- The genus of $C$ equals the genus of $F$ whenever $C$ is $k$-isomorphic to the plane cubic
$F$. -/
theorem SmoothProjectiveCurveOverField.genus_eq_of_isIsomorphicTo
    {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k) (F : PlaneCubic k)
    (hiso : C.IsIsomorphicTo F) :
    C.genus = F.genus := by
  obtain ⟨φ, hφ⟩ := hiso
  have h := genus_eq_of_scheme_iso C F.toSmoothProjectiveCurveOverField φ hφ
  rw [h]
  exact F.toSmoothProjectiveCurveOverField_genus

/-- The plane cubic given by the (general) Weierstrass equation
$Y^2Z + a_1 XYZ + a_3 YZ^2 = X^3 + a_2 X^2 Z + a_4 XZ^2 + a_6 Z^3$, encoded as a homogeneous
polynomial of degree $3$ in three variables. -/
def WeierstrassCurve.toPlaneCubic {k : Type*} [Field k] (W : WeierstrassCurve k) :
    PlaneCubic k where
  poly :=
    let X := MvPolynomial.X (R := k) (0 : Fin 3)
    let Y := MvPolynomial.X (R := k) (1 : Fin 3)
    let Z := MvPolynomial.X (R := k) (2 : Fin 3)
    Y ^ 2 * Z + C W.a₁ * X * Y * Z + C W.a₃ * Y * Z ^ 2
      - X ^ 3 - C W.a₂ * X ^ 2 * Z - C W.a₄ * X * Z ^ 2 - C W.a₆ * Z ^ 3
  isHomogeneous := by
    have hX : (MvPolynomial.X (R := k) (0 : Fin 3)).IsHomogeneous 1 := isHomogeneous_X k 0
    have hY : (MvPolynomial.X (R := k) (1 : Fin 3)).IsHomogeneous 1 := isHomogeneous_X k 1
    have hZ : (MvPolynomial.X (R := k) (2 : Fin 3)).IsHomogeneous 1 := isHomogeneous_X k 2
    have h1 : ((MvPolynomial.X (1 : Fin 3)) ^ 2 * (MvPolynomial.X (2 : Fin 3)) :
        MvPolynomial (Fin 3) k).IsHomogeneous 3 := by
      have := (hY.pow 2).mul hZ; simpa using this
    have h2 : (C W.a₁ * MvPolynomial.X (0 : Fin 3) * MvPolynomial.X (1 : Fin 3) *
        MvPolynomial.X (2 : Fin 3) : MvPolynomial (Fin 3) k).IsHomogeneous 3 := by
      have := ((isHomogeneous_C (Fin 3) W.a₁).mul hX).mul hY |>.mul hZ; simpa using this
    have h3 : (C W.a₃ * MvPolynomial.X (1 : Fin 3) * (MvPolynomial.X (2 : Fin 3)) ^ 2 :
        MvPolynomial (Fin 3) k).IsHomogeneous 3 := by
      have := ((isHomogeneous_C (Fin 3) W.a₃).mul hY).mul (hZ.pow 2); simpa using this
    have h4 : ((MvPolynomial.X (0 : Fin 3)) ^ 3 :
        MvPolynomial (Fin 3) k).IsHomogeneous 3 := by
      have := hX.pow 3; simpa using this
    have h5 : (C W.a₂ * (MvPolynomial.X (0 : Fin 3)) ^ 2 * MvPolynomial.X (2 : Fin 3) :
        MvPolynomial (Fin 3) k).IsHomogeneous 3 := by
      have := ((isHomogeneous_C (Fin 3) W.a₂).mul (hX.pow 2)).mul hZ; simpa using this
    have h6 : (C W.a₄ * MvPolynomial.X (0 : Fin 3) * (MvPolynomial.X (2 : Fin 3)) ^ 2 :
        MvPolynomial (Fin 3) k).IsHomogeneous 3 := by
      have := ((isHomogeneous_C (Fin 3) W.a₄).mul hX).mul (hZ.pow 2); simpa using this
    have h7 : (C W.a₆ * (MvPolynomial.X (2 : Fin 3)) ^ 3 :
        MvPolynomial (Fin 3) k).IsHomogeneous 3 := by
      have := (isHomogeneous_C (Fin 3) W.a₆).mul (hZ.pow 3); simpa using this
    exact ((h1.add h2).add h3).sub h4 |>.sub h5 |>.sub h6 |>.sub h7
  ne_zero := by
    intro h
    have := congr_arg (MvPolynomial.eval (fun i : Fin 3 => if i = 0 then (1 : k) else 0)) h
    simp only [map_sub, map_add, map_mul, map_pow, eval_X, eval_C, map_zero] at this
    simp only [show (2 : Fin 3) ≠ 0 from by decide, show (1 : Fin 3) ≠ 0 from by decide,
      if_false, if_true] at this
    norm_num at this

/-- The point at infinity $[0 : 1 : 0]$ provides a rational point on the Weierstrass plane
cubic. -/
theorem WeierstrassCurve.toPlaneCubic_hasRationalPoint {k : Type*} [Field k]
    (W : WeierstrassCurve k) : W.toPlaneCubic.HasRationalPoint := by
  refine ⟨fun i => if i = 1 then 1 else 0, ?_, ?_⟩
  · intro h
    have : (fun i : Fin 3 => if i = 1 then (1 : k) else 0) 1 = 0 := congr_fun h 1
    simp at this
  · simp only [toPlaneCubic, map_sub, map_add, map_mul, map_pow, eval_X, eval_C]
    simp only [show (0 : Fin 3) ≠ 1 from by decide, show (2 : Fin 3) ≠ 1 from by decide,
      if_true, if_false]
    ring

/-- The genus of an elliptic Weierstrass curve, viewed as a plane cubic, is one. -/
theorem WeierstrassCurve.toPlaneCubic_genus {k : Type*} [Field k]
    (W : WeierstrassCurve k) (_hW : W.IsElliptic) :
    W.toPlaneCubic.genus = 1 := by


  rfl
open Polynomial in
/-- Axiomatized: a smooth projective curve of genus one with a rational point is $k$-isomorphic to
the plane cubic of some elliptic Weierstrass curve. -/
theorem weierstrass_model_of_genus_one {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k)
    (hg : C.genus = 1)
    (hP : C.HasRationalPoint) :
    ∃ (W : WeierstrassCurve k), W.IsElliptic ∧
      C.IsIsomorphicTo W.toPlaneCubic := by sorry

/-- Converse to `weierstrass_model_of_genus_one`: a curve $k$-isomorphic to an elliptic Weierstrass
plane cubic has genus one and a rational point. -/
theorem genus_one_of_weierstrass_model {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k)
    (W : WeierstrassCurve k) (hW : W.IsElliptic)
    (hiso : C.IsIsomorphicTo W.toPlaneCubic) :
    C.genus = 1 ∧ C.HasRationalPoint := by
  constructor
  ·
    rw [C.genus_eq_of_isIsomorphicTo W.toPlaneCubic hiso]
    exact W.toPlaneCubic_genus hW
  ·
    exact C.hasRationalPoint_of_isIsomorphicTo W.toPlaneCubic hiso
      W.toPlaneCubic_hasRationalPoint

/-- Iff form: assuming a rational point, $C$ has genus one if and only if $C$ admits a Weierstrass
elliptic model. -/
theorem weierstrass_model_iff_genus_one {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k)
    (hP : C.HasRationalPoint) :
    C.genus = 1 ↔
      ∃ (W : WeierstrassCurve k), W.IsElliptic ∧ C.IsIsomorphicTo W.toPlaneCubic := by
  constructor
  · exact fun hg => weierstrass_model_of_genus_one C hg hP
  · rintro ⟨W, hW, hiso⟩
    exact (genus_one_of_weierstrass_model C W hW hiso).1

/-- Strengthened statement: a smooth projective curve of genus one with a rational point is
$k$-isomorphic to an elliptic Weierstrass plane cubic that, in turn, has a rational point. -/
theorem genus_one_isomorphic_to_plane_cubic
    {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k)
    (hg : C.genus = 1)
    (hP : C.HasRationalPoint) :
    ∃ (W : WeierstrassCurve k),
      W.IsElliptic ∧ W.toPlaneCubic.HasRationalPoint ∧ C.IsIsomorphicTo W.toPlaneCubic := by
  obtain ⟨W, hW, hiso⟩ := weierstrass_model_of_genus_one C hg hP
  exact ⟨W, hW, W.toPlaneCubic_hasRationalPoint, hiso⟩


end
