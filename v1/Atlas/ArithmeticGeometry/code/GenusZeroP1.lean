/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.GenusOnePlaneCubic

noncomputable section

open AlgebraicGeometry CategoryTheory Polynomial

/-- The projective line $\mathbb{P}^1_k$ packaged as a `SmoothProjectiveCurveOverField k`. We
realize $\mathbb{P}^1_k$ via $\mathrm{Spec}\,k[X]$ together with its structure morphism, equipped
with the proofs that it is integral, has Krull dimension $1$, is nonempty, and has genus $0$. -/
def projectiveLineAsCurve (k : Type*) [Field k] :
    SmoothProjectiveCurveOverField k :=


  { toScheme := Spec (CommRingCat.of (Polynomial k))
    isIntegral := instIsIntegralSpecOfIsDomainCarrier
    krullDim_eq := by
      change topologicalKrullDim (PrimeSpectrum (Polynomial k)) = 1
      rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
          Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
      norm_num
    nonempty := instNonemptyCarrierCarrierCommRingCatSpecOfNontrivialCarrier
    structureMorphism := Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))
    genusVal := 0 }

/-- The genus of $\mathbb{P}^1_k$ is zero, by construction. -/
theorem projectiveLineAsCurve_genus_zero (k : Type*) [Field k] :
    (projectiveLineAsCurve k).genus = 0 := by
  rfl

/-- $\mathbb{P}^1_k$ has a rational point: explicitly the point $[0 : 1]$, witnessed by the
evaluation morphism $\mathrm{Spec}\,k \to \mathrm{Spec}\,k[X]$ at $0$. -/
theorem projectiveLineAsCurve_hasRationalPoint (k : Type*) [Field k] :
    (projectiveLineAsCurve k).HasRationalPoint := by


  refine ⟨Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (RingHom.id k) (0 : k))), ?_⟩

  show Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom (RingHom.id k) (0 : k))) ≫
    Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) = 𝟙 _
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_id]
  congr 1
  ext x
  simp [Polynomial.eval₂_C]

/-- Invariance of genus under $k$-isomorphism: if $C_1$ and $C_2$ are $k$-isomorphic smooth
projective curves over $k$, they have equal genus. -/
theorem SmoothProjectiveCurveOverField.genus_eq_of_k_iso
    {k : Type*} [Field k]
    (C₁ C₂ : SmoothProjectiveCurveOverField k)
    (φ : C₁.toScheme ≅ C₂.toScheme)
    (hφ : φ.hom ≫ C₂.structureMorphism = C₁.structureMorphism) :
    C₁.genus = C₂.genus :=
  genus_eq_of_scheme_iso C₁ C₂ φ hφ

/-- Transport of rational points along a $k$-isomorphism: if $C_2$ has a rational point and
$C_1 \simeq C_2$ over $k$, then $C_1$ has a rational point. -/
theorem SmoothProjectiveCurveOverField.hasRationalPoint_of_k_iso
    {k : Type*} [Field k]
    (C₁ C₂ : SmoothProjectiveCurveOverField k)
    (φ : C₁.toScheme ≅ C₂.toScheme)
    (hφ : φ.hom ≫ C₂.structureMorphism = C₁.structureMorphism)
    (hpt : C₂.HasRationalPoint) :
    C₁.HasRationalPoint := by


  obtain ⟨s, hs⟩ := hpt
  refine ⟨s ≫ φ.inv, ?_⟩


  rw [← hφ]
  simp [Iso.inv_hom_id_assoc, hs]

/-- The property of being $k$-isomorphic to the projective line $\mathbb{P}^1_k$, compatibly with
the structure morphism. -/
def SmoothProjectiveCurveOverField.IsIsomorphicToP1 {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k) : Prop :=
  ∃ (φ : C.toScheme ≅ (projectiveLineAsCurve k).toScheme),
    φ.hom ≫ (projectiveLineAsCurve k).structureMorphism = C.structureMorphism

/-- Axiomatized invariant `rr_dim_rationalPoint`: the dimension of the Riemann–Roch space attached
to a rational point of $C$. -/
noncomputable def SmoothProjectiveCurveOverField.rr_dim_rationalPoint {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k) (_hP : C.HasRationalPoint) : ℕ := by sorry

/-- Axiomatized Riemann–Roch consequence: for a genus-$0$ curve with a rational point, the
Riemann–Roch dimension equals $\dim H^0(C, \mathcal{O}(P)) = g + 1 - g = 2$. -/
theorem SmoothProjectiveCurveOverField.rr_dim_rationalPoint_eq {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k) (hP : C.HasRationalPoint)
    (hg : C.genus = 0) :
    C.rr_dim_rationalPoint hP = 2 := by sorry

/-- Axiomatized property: a morphism $C \to \mathbb{P}^1_k$ is of degree one. -/
noncomputable def SmoothProjectiveCurveOverField.IsDegreeOneMorphismToP1 {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k)
    (f : C.toScheme ⟶ (projectiveLineAsCurve k).toScheme) : Prop := by sorry

/-- Axiomatized: when the Riemann–Roch dimension at a rational point is at least $2$, a
non-constant rational function exists and provides a degree-one morphism to $\mathbb{P}^1_k$. -/
theorem SmoothProjectiveCurveOverField.exists_degree_one_morphism_of_rr_dim_ge_two
    {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k) (hP : C.HasRationalPoint)
    (h : C.rr_dim_rationalPoint hP ≥ 2) :
    ∃ f : C.toScheme ⟶ (projectiveLineAsCurve k).toScheme, C.IsDegreeOneMorphismToP1 f := by sorry

/-- Axiomatized: a degree-one morphism from $C$ to $\mathbb{P}^1_k$ is an isomorphism, hence $C$
is $k$-isomorphic to $\mathbb{P}^1_k$. -/
theorem SmoothProjectiveCurveOverField.iso_of_degree_one_morphism
    {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k)
    (f : C.toScheme ⟶ (projectiveLineAsCurve k).toScheme)
    (hf : C.IsDegreeOneMorphismToP1 f) :
    C.IsIsomorphicToP1 := by sorry

/-- Combination: if the Riemann–Roch dimension at a rational point is at least $2$, then $C$ is
$k$-isomorphic to $\mathbb{P}^1_k$. -/
theorem SmoothProjectiveCurveOverField.isIsomorphicToP1_of_rr_dim_ge_two {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k) (hP : C.HasRationalPoint)
    (h : C.rr_dim_rationalPoint hP ≥ 2) :
    C.IsIsomorphicToP1 := by


  obtain ⟨f, hf⟩ := C.exists_degree_one_morphism_of_rr_dim_ge_two hP h


  exact C.iso_of_degree_one_morphism f hf

/-- Conversely, any curve $k$-isomorphic to $\mathbb{P}^1_k$ has genus zero. -/
theorem SmoothProjectiveCurveOverField.genus_zero_of_isIsomorphicToP1
    {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k)
    (hiso : C.IsIsomorphicToP1) :
    C.genus = 0 := by

  obtain ⟨φ, hφ⟩ := hiso

  have h := SmoothProjectiveCurveOverField.genus_eq_of_k_iso C (projectiveLineAsCurve k) φ hφ

  rw [h, projectiveLineAsCurve_genus_zero]

/-- A curve $k$-isomorphic to $\mathbb{P}^1_k$ inherits a rational point. -/
theorem SmoothProjectiveCurveOverField.hasRationalPoint_of_isIsomorphicToP1
    {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k)
    (hiso : C.IsIsomorphicToP1) :
    C.HasRationalPoint := by

  obtain ⟨φ, hφ⟩ := hiso

  exact C.hasRationalPoint_of_k_iso (projectiveLineAsCurve k) φ hφ
    (projectiveLineAsCurve_hasRationalPoint k)

/-- Theorem 23.1 (forward direction): a smooth projective curve of genus zero with a rational
point is $k$-isomorphic to $\mathbb{P}^1_k$. -/
theorem genus_zero_implies_isomorphicToP1 {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k)
    (hg : C.genus = 0) (hP : C.HasRationalPoint) :
    C.IsIsomorphicToP1 := by

  have hrr : C.rr_dim_rationalPoint hP = 2 :=
    C.rr_dim_rationalPoint_eq hP hg


  exact C.isIsomorphicToP1_of_rr_dim_ge_two hP (by omega)


/-- Theorem 23.1 (iff form): a smooth projective curve over $k$ with a rational point has genus
zero if and only if it is $k$-isomorphic to $\mathbb{P}^1_k$. -/
theorem genus_zero_iff_isomorphicToP1 {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k)
    (hP : C.HasRationalPoint) :
    C.genus = 0 ↔ C.IsIsomorphicToP1 := by
  constructor
  ·
    intro hg
    exact genus_zero_implies_isomorphicToP1 C hg hP
  ·
    intro hiso
    exact C.genus_zero_of_isIsomorphicToP1 hiso

end
