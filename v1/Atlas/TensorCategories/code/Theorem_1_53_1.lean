/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

set_option maxHeartbeats 400000
set_option autoImplicit false

open CategoryTheory MonoidalCategory

universe u v w


section CartanMatrix

variable {k : Type w} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Coerce a Cartan matrix with natural-number entries to a matrix with entries in the
field `k`. -/
def cartanMatrixOverField (C_mat : ι → ι → ℕ) : Matrix ι ι k :=
  Matrix.of (fun i j => (C_mat i j : k))

/-- A square matrix with a nonzero vector in its kernel has zero determinant. -/
theorem det_eq_zero_of_mulVec_eq_zero_of_ne_zero
    (M : Matrix ι ι k) (d : ι → k) (hd : d ≠ 0) (hMd : M.mulVec d = 0) :
    M.det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  exact ⟨d, hd, hMd⟩

/-- If a Cartan matrix annihilates a nonzero dimension vector, then the matrix is
degenerate (its determinant in `k` vanishes). -/
theorem cartan_matrix_degenerate_of_dim_vanishes
    (C_mat : ι → ι → ℕ)
    (d : ι → k)
    (hd_ne : d ≠ 0)
    (hd_kernel : ∀ i : ι, ∑ j : ι, (C_mat i j : k) * d j = 0) :
    (cartanMatrixOverField C_mat : Matrix ι ι k).det = 0 := by
  apply det_eq_zero_of_mulVec_eq_zero_of_ne_zero _ d hd_ne
  ext i
  simp only [Matrix.mulVec, dotProduct, cartanMatrixOverField, Matrix.of_apply, Pi.zero_apply]
  exact hd_kernel i

end CartanMatrix


section PivotalDimensionTheorem

variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- Left quantum trace of a morphism `a : V → V**` in a rigid monoidal category,
defined via the coevaluation and evaluation as
`η_V ≫ (a ▷ Vᘁ) ≫ ε_(Vᘁ, V**)`. -/
noncomputable def leftQuantumTrace' {V : C} (a : V ⟶ (Vᘁ)ᘁ) : 𝟙_ C ⟶ 𝟙_ C :=
  η_ V (Vᘁ) ≫ (a ▷ Vᘁ) ≫ ε_ (Vᘁ) ((Vᘁ)ᘁ)

/-- Data of a pivotal structure on a rigid monoidal category: a natural family of
isomorphisms `V ≅ V**` compatible with morphisms via double duality. -/
structure PivotalStructureData (C : Type u)
    [Category.{v} C] [MonoidalCategory C] [RigidCategory C] where
  pivotalIso : ∀ (V : C), V ≅ (Vᘁ)ᘁ
  naturality : ∀ {V W : C} (f : V ⟶ W),
    f ≫ (pivotalIso W).hom = (pivotalIso V).hom ≫ (fᘁ)ᘁ

/-- Pivotal (categorical) dimension of `V`: the left quantum trace of the pivotal
isomorphism `V ≅ V**`. -/
noncomputable def pivotalDim (u : PivotalStructureData C) (V : C) : 𝟙_ C ⟶ 𝟙_ C :=
  leftQuantumTrace' C (u.pivotalIso V).hom

end PivotalDimensionTheorem


section DimProjZero

open CategoryTheory MonoidalCategory

variable {k : Type w} [Field k]
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

/-- If the unit object is not projective, any retract argument forces the pivotal
dimension of every projective object (evaluated through `φ`) to vanish. -/
theorem dim_proj_zero_of_not_semisimple
    (u : PivotalStructureData C)
    (φ : (𝟙_ C ⟶ 𝟙_ C) → k)
    (h_retract : ∀ (P : C) [Projective P],
      φ (pivotalDim C u P) ≠ 0 → Projective (𝟙_ C))
    (hns : ¬ Projective (𝟙_ C))
    (P : C) [Projective P] :
    φ (pivotalDim C u P) = 0 := by
  by_contra h
  exact hns (h_retract P h)

end DimProjZero


/-- Bundle of data abstracting the relevant features of a finite tensor category with
pivotal structure: simple objects, their projective covers, the Cartan matrix,
and pivotal-dimension data (with the extracted scalar `φ` and required identities). -/
structure FiniteTensorCategoryData (C : Type u)
    [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    (k : Type w) [Field k]
    (ι : Type*) [Fintype ι] [DecidableEq ι]
    (u : PivotalStructureData C) where
  simpleObj : ι → C
  unitIndex : ι
  unitIso : Nonempty (simpleObj unitIndex ≅ 𝟙_ C)
  projCover : ι → C
  projCover_projective : ∀ i, Projective (projCover i)
  cartanEntry : ι → ι → ℕ
  φ : (𝟙_ C ⟶ 𝟙_ C) → k
  retract_of_projective : ∀ (Q : C) [Projective Q],
    φ (pivotalDim C u Q) ≠ 0 → Projective (𝟙_ C)
  dim_unit_ne_zero : φ (pivotalDim C u (𝟙_ C)) ≠ 0
  dim_iso_invariant : ∀ (X Y : C), Nonempty (X ≅ Y) →
    pivotalDim C u X = pivotalDim C u Y
  additive_on_composition_series : ∀ i,
    ∑ j : ι, (cartanEntry i j : k) * φ (pivotalDim C u (simpleObj j)) =
      φ (pivotalDim C u (projCover i))


section Theorem1531

open CategoryTheory MonoidalCategory

/-- A vector is nonzero if one of its components is nonzero. -/
theorem dim_vec_ne_zero_of_component_ne_zero
    {k : Type*} [Field k] {ι : Type*}
    (d : ι → k) (i₀ : ι) (hi₀ : d i₀ ≠ 0) : d ≠ 0 := by
  intro h
  exact hi₀ (congr_fun h i₀)

/-- Lower-case form of Theorem 1.53.1: if a finite tensor category `C` is not
semisimple (the unit is not projective) and admits a pivotal structure, then its
Cartan matrix is degenerate over the ground field `k`. -/
theorem thm_1_53_1
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    {k : Type w} [Field k]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : PivotalStructureData C)
    (hns : ¬ Projective (𝟙_ C))
    (ftc : FiniteTensorCategoryData C k ι u) :
    (cartanMatrixOverField ftc.cartanEntry : Matrix ι ι k).det = 0 := by

  let d : ι → k := fun j => ftc.φ (pivotalDim C u (ftc.simpleObj j))

  have hdP : ∀ i, ftc.φ (pivotalDim C u (ftc.projCover i)) = 0 := by
    intro i
    exact @dim_proj_zero_of_not_semisimple k _ C _ _ _ u ftc.φ
      ftc.retract_of_projective hns (ftc.projCover i) (ftc.projCover_projective i)

  have hkernel : ∀ i, ∑ j : ι, (ftc.cartanEntry i j : k) * d j = 0 := by
    intro i
    rw [ftc.additive_on_composition_series i]
    exact hdP i

  have hdi₀ : d ftc.unitIndex ≠ 0 := by
    intro h
    apply ftc.dim_unit_ne_zero
    rw [← ftc.dim_iso_invariant (ftc.simpleObj ftc.unitIndex) (𝟙_ C) ftc.unitIso]
    exact h

  exact cartan_matrix_degenerate_of_dim_vanishes ftc.cartanEntry d
    (dim_vec_ne_zero_of_component_ne_zero d ftc.unitIndex hdi₀) hkernel

/-- Theorem 1.53.1: If a finite tensor category `C` is not semisimple and admits a
pivotal structure (an isomorphism of additive functors `u : Id ≃ **`), then its
Cartan matrix is degenerate over the ground field `k`. -/
theorem Theorem_1_53_1
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
    {k : Type w} [Field k]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : PivotalStructureData C)
    (hns : ¬ Projective (𝟙_ C))
    (ftc : FiniteTensorCategoryData C k ι u) :
    (cartanMatrixOverField ftc.cartanEntry : Matrix ι ι k).det = 0 :=
  thm_1_53_1 u hns ftc

end Theorem1531
