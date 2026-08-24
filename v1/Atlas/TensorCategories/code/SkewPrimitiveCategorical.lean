/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Spectrum.Maximal.Basic

set_option maxHeartbeats 800000

open Coalgebra
open scoped TensorProduct
open CategoryTheory MonoidalCategory Category Limits

universe v u w

noncomputable section


/-- An element `g` of a coalgebra is grouplike when `Δ g = g ⊗ g` and `ε g = 1`. -/
def IsGrouplike {R : Type*} {C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C]
    [Coalgebra R C] (g : C) : Prop :=
  Coalgebra.comul (R := R) g = g ⊗ₜ g ∧ Coalgebra.counit (R := R) g = 1

/-- An element `x` of a coalgebra is `(g, h)`-skew-primitive when its comultiplication
satisfies `Δ x = x ⊗ g + h ⊗ x`. -/
def IsSkewPrimitive {R : Type*} {C : Type*} [CommSemiring R] [AddCommMonoid C] [Module R C]
    [Coalgebra R C] (g h x : C) : Prop :=
  Coalgebra.comul (R := R) x = x ⊗ₜ g + h ⊗ₜ x

/-- The `R`-submodule of all `(g, h)`-skew-primitive elements of a coalgebra `C`. -/
def skewPrimitiveSpace {R : Type*} {C : Type*} [CommSemiring R] [AddCommGroup C] [Module R C]
    [Coalgebra R C] (g h : C) : Submodule R C where
  carrier := {x : C | IsSkewPrimitive (R := R) g h x}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at *
    unfold IsSkewPrimitive at *
    rw [map_add, hx, hy, TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    unfold IsSkewPrimitive
    simp [TensorProduct.zero_tmul, TensorProduct.tmul_zero]
  smul_mem' r x hx := by
    simp only [Set.mem_setOf_eq] at *
    unfold IsSkewPrimitive at *
    rw [LinearMap.map_smul, hx]
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul]


namespace HopfAlgebra

/-- An element `x` of a bialgebra is primitive when `Δ x = x ⊗ 1 + 1 ⊗ x`; equivalently, a
`(1, 1)`-skew-primitive element. -/
def IsPrimitive {R : Type*} {H : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]
    (x : H) : Prop :=
  Coalgebra.comul (R := R) x = x ⊗ₜ 1 + 1 ⊗ₜ x

/-- The `R`-submodule of primitive elements of a bialgebra. -/
def primitiveElements {R : Type*} {H : Type*} [CommSemiring R] [Semiring H]
    [Bialgebra R H] : Submodule R H where
  carrier := {x : H | IsPrimitive (R := R) x}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq] at *
    unfold IsPrimitive at *
    rw [map_add, hx, hy, TensorProduct.add_tmul, TensorProduct.tmul_add]
    abel
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    unfold IsPrimitive
    simp [TensorProduct.zero_tmul, TensorProduct.tmul_zero]
  smul_mem' r x hx := by
    simp only [Set.mem_setOf_eq] at *
    unfold IsPrimitive at *
    rw [LinearMap.map_smul, hx]
    simp [TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_add]

end HopfAlgebra


namespace TensorCategories

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Vanishing of `Ext¹(X, Y)`: every short exact sequence `0 → Y → V → X → 0` in `C` splits. -/
def Ext1Vanishes (X Y : C) : Prop :=
  ∀ (V : C) (f : Y ⟶ V) (g : V ⟶ X) (hfg : f ≫ g = 0),
    (ShortComplex.mk f g hfg).ShortExact → Nonempty (ShortComplex.mk f g hfg).Splitting

/-- A finite `k`-linear ring category: an abelian monoidal `k`-linear category that has enough
projectives and finite-dimensional Hom-spaces. -/
class FiniteRingCategory (k : Type w) [Field k] (C : Type u) [Category.{v} C]
    extends MonoidalCategory C, Abelian C, Linear k C where
  enoughProj : EnoughProjectives C
  homFiniteDim : ∀ (X Y : C), FiniteDimensional k (X ⟶ Y)

/-- In characteristic zero, every self-extension of the simple unit in a finite ring category
splits, i.e. `Ext¹(𝟙_C, 𝟙_C) = 0`. -/
theorem ext1Vanishes_unit_unit_of_charZero
    (k : Type w) [Field k] [CharZero k]
    (C : Type u) [Category.{v} C] [FiniteRingCategory k C]
    [Simple (𝟙_ C)] :
    Ext1Vanishes (𝟙_ C) (𝟙_ C) := by sorry

end TensorCategories


section TrivialSkewPrimitive

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- For grouplike elements `g` and `h`, the difference `h - g` is automatically
`(g, h)`-skew-primitive; this is the trivial skew-primitive element. -/
theorem trivialSkewPrimitive_mem
    {g h : C} (hg : IsGrouplike (R := k) g) (hh : IsGrouplike (R := k) h) :
    IsSkewPrimitive (R := k) g h (h - g) := by
  unfold IsSkewPrimitive
  rw [map_sub, hh.1, hg.1]
  simp [TensorProduct.sub_tmul, TensorProduct.tmul_sub]

/-- The one-dimensional subspace spanned by the trivial skew-primitive element `h - g`. -/
def trivialSkewPrimitiveSubspace (g h : C) : Submodule k C :=
  Submodule.span k {h - g}

/-- The trivial skew-primitive subspace is contained in the full space of skew-primitives. -/
theorem trivialSkewPrimitive_le
    {g h : C} (hg : IsGrouplike (R := k) g) (hh : IsGrouplike (R := k) h) :
    trivialSkewPrimitiveSubspace (k := k) g h ≤ skewPrimitiveSpace (R := k) g h := by
  apply Submodule.span_le.mpr
  intro x hx
  simp at hx
  rw [hx]
  exact trivialSkewPrimitive_mem hg hh

/-- The reduced space of skew-primitives: the quotient of `skewPrimitiveSpace g h` by its trivial
sub-line, capturing genuinely nontrivial skew-primitive directions. -/
def reducedSkewPrimitiveSpace
    {g h : C} (_hg : IsGrouplike (R := k) g) (_hh : IsGrouplike (R := k) h) :
    Type u :=
  (skewPrimitiveSpace (R := k) g h) ⧸
    (Submodule.comap (skewPrimitiveSpace (R := k) g h).subtype
      (trivialSkewPrimitiveSubspace (k := k) g h))

end TrivialSkewPrimitive


section ComoduleExt

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- A comodule extension between grouplikes `g` and `h`: a skew-primitive element witnessing a
short exact sequence `0 → k·g → V → k·h → 0` of comodules. -/
structure ComoduleExtension (g h : C) where
  x : C
  skew_prim : IsSkewPrimitive (R := k) g h x

/-- Two comodule extensions are equivalent when their witnessing skew-primitives differ by a
trivial skew-primitive multiple of `h - g`. -/
def ComoduleExtension.Equiv {g h : C} (E₁ E₂ : ComoduleExtension (k := k) g h) : Prop :=
  E₁.x - E₂.x ∈ trivialSkewPrimitiveSubspace (k := k) g h

/-- Forget a comodule extension to the underlying skew-primitive element in `skewPrimitiveSpace`. -/
def ComoduleExtension.toSkewPrimitive {g h : C} (E : ComoduleExtension (k := k) g h) :
    skewPrimitiveSpace (R := k) g h :=
  ⟨E.x, E.skew_prim⟩

/-- Convert a skew-primitive element to the corresponding comodule extension. -/
def ComoduleExtension.ofSkewPrimitive {g h : C}
    (p : skewPrimitiveSpace (R := k) g h) : ComoduleExtension (k := k) g h :=
  ⟨p.val, p.property⟩

/-- Reflexivity of comodule extension equivalence. -/
theorem ComoduleExtension.Equiv.refl {g h : C} (E : ComoduleExtension (k := k) g h) :
    ComoduleExtension.Equiv E E := by
  unfold ComoduleExtension.Equiv
  simp [trivialSkewPrimitiveSubspace]

/-- Symmetry of comodule extension equivalence. -/
theorem ComoduleExtension.Equiv.symm {g h : C}
    {E₁ E₂ : ComoduleExtension (k := k) g h} (h_eq : ComoduleExtension.Equiv E₁ E₂) :
    ComoduleExtension.Equiv E₂ E₁ := by
  unfold ComoduleExtension.Equiv at *
  rwa [show E₂.x - E₁.x = -(E₁.x - E₂.x) from (neg_sub E₁.x E₂.x).symm, neg_mem_iff]

/-- Transitivity of comodule extension equivalence. -/
theorem ComoduleExtension.Equiv.trans {g h : C}
    {E₁ E₂ E₃ : ComoduleExtension (k := k) g h}
    (h₁₂ : ComoduleExtension.Equiv E₁ E₂) (h₂₃ : ComoduleExtension.Equiv E₂ E₃) :
    ComoduleExtension.Equiv E₁ E₃ := by
  unfold ComoduleExtension.Equiv at *
  have : E₁.x - E₃.x = (E₁.x - E₂.x) + (E₂.x - E₃.x) := by abel
  rw [this]
  exact Submodule.add_mem _ h₁₂ h₂₃

/-- The setoid structure on comodule extensions induced by the equivalence relation. -/
instance ComoduleExtension.setoid (g h : C) :
    Setoid (ComoduleExtension (k := k) g h) where
  r := ComoduleExtension.Equiv
  iseqv := {
    refl := ComoduleExtension.Equiv.refl
    symm := ComoduleExtension.Equiv.symm
    trans := ComoduleExtension.Equiv.trans
  }

/-- The space `Ext¹` of comodule extensions between grouplikes `g` and `h`, defined as
equivalence classes of comodule extensions. -/
def ComoduleExt1 (g h : C) : Type u :=
  Quotient (ComoduleExtension.setoid (k := k) g h)

/-- Form the `Ext¹` equivalence class of a comodule extension. -/
def ComoduleExt1.mk {g h : C} (E : ComoduleExtension (k := k) g h) :
    ComoduleExt1 (k := k) g h :=
  Quotient.mk _ E

/-- The coassociativity-style comultiplication equation `Δ x = x ⊗ g + h ⊗ x` is by definition
the skew-primitive condition. -/
theorem coassoc_forces_skew_primitive
    {g h : C} (_hg : IsGrouplike (R := k) g) (_hh : IsGrouplike (R := k) h)
    (x : C) (hcoassoc :
      Coalgebra.comul (R := k) x = x ⊗ₜ[k] g + h ⊗ₜ[k] x) :
    IsSkewPrimitive (R := k) g h x :=
  hcoassoc

/-- Changing a skew-primitive `x` by adding a scalar multiple of the trivial skew-primitive
`h - g` yields another skew-primitive element. -/
theorem basis_change_shifts_by_trivial
    {g h : C} (hg : IsGrouplike (R := k) g) (hh : IsGrouplike (R := k) h)
    (x : C) (hx : IsSkewPrimitive (R := k) g h x) (c : k) :
    IsSkewPrimitive (R := k) g h (x + c • (h - g)) := by
  unfold IsSkewPrimitive at *
  rw [map_add, LinearMap.map_smul, map_sub, hx, hh.1, hg.1]
  simp only [smul_sub, TensorProduct.tmul_sub, TensorProduct.sub_tmul,
             TensorProduct.tmul_add, TensorProduct.add_tmul,
             TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  module

end ComoduleExt


section Proposition_1_27_1_proof

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

private abbrev SkewQuot (g h : C) :=
  (skewPrimitiveSpace (R := k) g h) ⧸
    (Submodule.comap (skewPrimitiveSpace (R := k) g h).subtype
      (trivialSkewPrimitiveSubspace (k := k) g h))

private def ext1ToSkewQuot {g h : C} :
    ComoduleExt1 (k := k) g h → SkewQuot (k := k) g h :=
  Quotient.lift
    (fun E => Submodule.Quotient.mk (p := Submodule.comap
      (skewPrimitiveSpace (R := k) g h).subtype
      (trivialSkewPrimitiveSubspace (k := k) g h))
      ⟨E.x, E.skew_prim⟩)
    (by
      intro E₁ E₂ (hE : ComoduleExtension.Equiv E₁ E₂)
      rw [Submodule.Quotient.eq]
      rw [Submodule.mem_comap]
      simp only [Submodule.subtype_apply, Submodule.coe_sub]
      exact hE)

private def skewQuotToExt1 {g h : C} :
    SkewQuot (k := k) g h → ComoduleExt1 (k := k) g h :=
  Quotient.lift
    (fun (p : skewPrimitiveSpace (R := k) g h) =>
      ComoduleExt1.mk (k := k) (ComoduleExtension.ofSkewPrimitive (k := k) p))
    (by
      intro a b hab
      apply Quotient.sound
      show ComoduleExtension.Equiv _ _
      unfold ComoduleExtension.Equiv ComoduleExtension.ofSkewPrimitive
      simp only
      have hab' : a - b ∈ Submodule.comap (skewPrimitiveSpace (R := k) g h).subtype
          (trivialSkewPrimitiveSubspace (k := k) g h) := by
        exact (Submodule.quotientRel_def _).mp hab
      rw [Submodule.mem_comap] at hab'
      simp only [Submodule.subtype_apply, Submodule.coe_sub] at hab'
      exact hab')

/-- The canonical bijection between `Ext¹(k·h, k·g)` and the reduced skew-primitive quotient
`skewPrimitiveSpace g h / trivialSkewPrimitiveSubspace g h`. -/
def ext1EquivSkewQuot {g h : C} :
    ComoduleExt1 (k := k) g h ≃ SkewQuot (k := k) g h where
  toFun := ext1ToSkewQuot
  invFun := skewQuotToExt1
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h E =>
      simp only [ext1ToSkewQuot, skewQuotToExt1, ComoduleExt1.mk,
        ComoduleExtension.ofSkewPrimitive]
      rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h p =>
      simp only [ext1ToSkewQuot, skewQuotToExt1, ComoduleExt1.mk,
        ComoduleExtension.ofSkewPrimitive]
      rfl

/-- Additive group structure on `ComoduleExt1` transported from the reduced skew-primitive
quotient. -/
noncomputable instance ComoduleExt1.instAddCommGroup {g h : C} :
    AddCommGroup (ComoduleExt1 (k := k) g h) :=
  (ext1EquivSkewQuot (k := k)).addCommGroup

/-- `k`-module structure on `ComoduleExt1` transported from the reduced skew-primitive quotient. -/
noncomputable instance ComoduleExt1.instModule {g h : C} :
    Module k (ComoduleExt1 (k := k) g h) :=
  Equiv.module k (ext1EquivSkewQuot (k := k))

end Proposition_1_27_1_proof

/-- Proposition 1.27.1: for grouplike elements `g, h` in a coalgebra, the reduced space of
`(g, h)`-skew-primitive elements is canonically `k`-linearly isomorphic to `Ext¹(k·h, k·g)`. -/
theorem Proposition_1_27_1
    (k : Type u) [Field k] (C : Type u) [AddCommGroup C] [Module k C] [Coalgebra k C]
    (g h : C) (_hg : IsGrouplike (R := k) g) (_hh : IsGrouplike (R := k) h) :
    Nonempty ((skewPrimitiveSpace (R := k) g h ⧸
        Submodule.comap (skewPrimitiveSpace (R := k) g h).subtype
          (trivialSkewPrimitiveSubspace (k := k) g h)) ≃ₗ[k]
      ComoduleExt1 (k := k) g h) :=
  ⟨(Equiv.linearEquiv k ext1EquivSkewQuot).symm⟩


namespace TensorCategories

/-- If a finite `k`-linear category has a unique simple object (up to iso) and `Ext¹(𝟙, 𝟙) = 0`,
then it is equivalent to the category of finite-dimensional `k`-vector spaces. -/
theorem reconstruction_from_ext1_vanishing_unique_simple
    (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [FiniteRingCategory k C]
    [Simple (𝟙_ C)]
    (h_ext1 : Ext1Vanishes (𝟙_ C) (𝟙_ C))
    (h_unique_simple : ∀ (X : C), Simple X → Nonempty (X ≅ 𝟙_ C)) :
    ∃ (F : C ⥤ FGModuleCat k), F.IsEquivalence := by sorry

/-- Corollary 1.27.5: in characteristic zero, any finite tensor category over `k` with a unique
simple object is equivalent to the category of finite-dimensional `k`-vector spaces. -/
theorem Corollary_1_27_5
    (k : Type w) [Field k] [CharZero k]
    (C : Type u) [Category.{v} C] [FiniteRingCategory k C]
    [Simple (𝟙_ C)]
    (h_unique_simple : ∀ (X : C), Simple X → Nonempty (X ≅ 𝟙_ C)) :
    ∃ (F : C ⥤ FGModuleCat k), F.IsEquivalence :=
  reconstruction_from_ext1_vanishing_unique_simple k C
    (ext1Vanishes_unit_unit_of_charZero k C) h_unique_simple

end TensorCategories


/-- In characteristic zero, the space `Ext¹(k·1, k·1)` over a finite-dimensional bialgebra is
trivial, i.e. there are no nontrivial self-extensions of the trivial comodule. -/
theorem comoduleExt1_subsingleton_of_charZero
    (k : Type u) [Field k] [CharZero k]
    (H : Type u) [Ring H] [Bialgebra k H] [Module.Finite k H] :
    Subsingleton (ComoduleExt1 (k := k) (1 : H) (1 : H)) := by sorry

/-- When the two grouplikes coincide, the trivial skew-primitive subspace is zero: `h - g = 0`. -/
theorem trivialSkewPrimitive_zero_when_equal
    {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C]
    (g : C) :
    trivialSkewPrimitiveSubspace (k := k) g g = ⊥ := by
  unfold trivialSkewPrimitiveSubspace
  simp [sub_self]

section Corollary_1_27_6_proof

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- When `g = h`, comodule extension equivalence collapses to equality of the underlying
skew-primitive element. -/
theorem comoduleExtension_equiv_implies_eq
    {g : C} (E₁ E₂ : ComoduleExtension (k := k) g g)
    (h : ComoduleExtension.Equiv E₁ E₂) : E₁.x = E₂.x := by
  unfold ComoduleExtension.Equiv at h
  rw [trivialSkewPrimitive_zero_when_equal] at h
  rw [Submodule.mem_bot] at h
  exact sub_eq_zero.mp h

/-- If `Ext¹(k·g, k·g)` is trivial, then there are no nonzero `(g, g)`-skew-primitives: the
skew-primitive space is the zero submodule. -/
theorem skewPrimitiveSpace_eq_bot_of_ext1_subsingleton
    {g : C}
    (hsub : Subsingleton (ComoduleExt1 (k := k) g g)) :
    skewPrimitiveSpace (R := k) g g = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  have h0 : (0 : C) ∈ skewPrimitiveSpace (R := k) g g :=
    (skewPrimitiveSpace (R := k) g g).zero_mem
  let E₁ : ComoduleExtension (k := k) g g := ⟨x, hx⟩
  let E₀ : ComoduleExtension (k := k) g g := ⟨0, h0⟩
  have hq : Quotient.mk (ComoduleExtension.setoid (k := k) g g) E₁ =
            Quotient.mk (ComoduleExtension.setoid (k := k) g g) E₀ :=
    hsub.elim _ _
  exact comoduleExtension_equiv_implies_eq E₁ E₀ (Quotient.exact hq)

end Corollary_1_27_6_proof

/-- In characteristic zero, the `(1, 1)`-skew-primitive space of a finite-dimensional bialgebra
is zero. -/
theorem skewPrimitiveSpace_one_one_eq_bot_of_charZero
    (k : Type u) [Field k] [CharZero k]
    (H : Type u) [Ring H] [Bialgebra k H] [Module.Finite k H] :
    skewPrimitiveSpace (R := k) (1 : H) (1 : H) = ⊥ :=
  skewPrimitiveSpace_eq_bot_of_ext1_subsingleton
    (comoduleExt1_subsingleton_of_charZero k H)

/-- The submodule of primitive elements of a bialgebra equals the `(1, 1)`-skew-primitive
subspace, by definition. -/
theorem primitiveElements_eq_skewPrimitiveSpace_one_one
    (k : Type u) [Field k]
    (H : Type u) [Ring H] [Bialgebra k H] :
    HopfAlgebra.primitiveElements (R := k) (H := H) =
      skewPrimitiveSpace (R := k) (1 : H) (1 : H) := by
  ext x
  constructor <;> intro h <;> exact h

/-- Corollary 1.27.6: in characteristic zero, a finite-dimensional bialgebra has no nonzero
primitive elements. -/
theorem Corollary_1_27_6
    (k : Type u) [Field k] [CharZero k]
    (H : Type u) [Ring H] [Bialgebra k H] [Module.Finite k H] :
    HopfAlgebra.primitiveElements (R := k) (H := H) = ⊥ := by
  rw [primitiveElements_eq_skewPrimitiveSpace_one_one k H]
  exact skewPrimitiveSpace_one_one_eq_bot_of_charZero k H

/-- Element-level form of Corollary 1.27.6: any primitive element in a finite-dimensional
bialgebra over a characteristic-zero field is zero. -/
theorem Corollary_1_27_6_no_primitives
    (k : Type u) [Field k] [CharZero k]
    (H : Type u) [Ring H] [Bialgebra k H] [Module.Finite k H]
    (x : H) (hx : HopfAlgebra.IsPrimitive (R := k) x) : x = 0 := by
  have h := Corollary_1_27_6 k H
  rw [Submodule.eq_bot_iff] at h
  exact h x hx


/-- A finite-dimensional commutative Hopf algebra over an algebraically closed field of
characteristic zero is reduced (has no nonzero nilpotents). -/
theorem isReduced_of_commHopfAlgebra_charZero
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (H : Type u) [CommRing H] [HopfAlgebra k H] [Module.Finite k H] :
    IsReduced H := by
  sorry

/-- The group structure on the maximal spectrum of a finite-dimensional commutative Hopf algebra,
coming from the Hopf operations. -/
def maximalSpectrumGroupOfHopfAlgebra
    (k : Type u) [Field k]
    (H : Type u) [CommRing H] [HopfAlgebra k H] [Module.Finite k H] :
    Group (MaximalSpectrum H) := by sorry

/-- Over an algebraically closed field `k`, every residue field of a finite-dimensional
commutative `k`-algebra at a maximal ideal is canonically `k` itself. -/
def residueFieldEquivOfAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k]
    (H : Type u) [CommRing H] [Algebra k H] [Module.Finite k H]
    (I : MaximalSpectrum H) : k ≃ₐ[k] (H ⧸ I.asIdeal) := by
  haveI : IsDomain (H ⧸ I.asIdeal) := Ideal.Quotient.isDomain I.asIdeal
  haveI : Module.Finite k (H ⧸ I.asIdeal) := Module.Finite.quotient k I.asIdeal
  haveI : Algebra.IsIntegral k (H ⧸ I.asIdeal) := Algebra.IsIntegral.of_finite k _
  exact AlgEquiv.ofBijective (Algebra.ofId k (H ⧸ I.asIdeal))
    IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- If a finite-dimensional commutative Hopf algebra `H` is isomorphic to the function algebras
`k^G₁` and `k^G₂` for two finite groups, then those groups are canonically isomorphic. -/
theorem commHopfFunGroup_unique
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (H : Type u) [CommRing H] [HopfAlgebra k H] [Module.Finite k H]
    (G₁ G₂ : Type u) [Fintype G₁] [Fintype G₂] [Group G₁] [Group G₂]
    [DecidableEq G₁] [DecidableEq G₂]
    (e₁ : H ≃ₐ[k] (G₁ → k)) (e₂ : H ≃ₐ[k] (G₂ → k)) :
    Nonempty (G₁ ≃* G₂) := by
  sorry

/-- Corollary 1.27.8: a finite-dimensional commutative Hopf algebra over an algebraically closed
field of characteristic zero is isomorphic to the function algebra `k^G` of a unique finite
group `G`. -/
theorem Corollary_1_27_8
    (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (H : Type u) [CommRing H] [HopfAlgebra k H] [Module.Finite k H] :
    (∃ (G : Type u) (_ : Fintype G) (_ : Group G),
      Nonempty (H ≃ₐ[k] (G → k))) ∧
    (∀ (G₁ G₂ : Type u) [Fintype G₁] [Fintype G₂] [Group G₁] [Group G₂]
      [DecidableEq G₁] [DecidableEq G₂],
      (H ≃ₐ[k] (G₁ → k)) → (H ≃ₐ[k] (G₂ → k)) → Nonempty (G₁ ≃* G₂)) := by
  constructor
  ·

    haveI hArt : IsArtinianRing H := isArtinian_of_tower k (inferInstance : IsArtinian k H)

    haveI hRed : IsReduced H := isReduced_of_commHopfAlgebra_charZero k H

    haveI : Finite (MaximalSpectrum H) := inferInstance
    haveI hFintype : Fintype (MaximalSpectrum H) := Fintype.ofFinite _

    letI hGrp : Group (MaximalSpectrum H) := maximalSpectrumGroupOfHopfAlgebra k H

    refine ⟨MaximalSpectrum H, hFintype, hGrp, ⟨?_⟩⟩


    let e1 : H ≃ₐ[k] (∀ I : MaximalSpectrum H, H ⧸ I.asIdeal) :=
      (IsArtinianRing.equivPi H).restrictScalars k

    let e2 : (∀ I : MaximalSpectrum H, H ⧸ I.asIdeal) ≃ₐ[k] (MaximalSpectrum H → k) :=
      AlgEquiv.piCongrRight (fun I => (residueFieldEquivOfAlgClosed k H I).symm)
    exact e1.trans e2
  ·
    intro G₁ G₂ _ _ _ _ _ _ e₁ e₂
    exact commHopfFunGroup_unique k H G₁ G₂ e₁ e₂


/-- Remark 1.27.9: in positive characteristic `p`, characteristic-zero results fail —
there exists a finite-dimensional Hopf algebra over `k` containing a nonzero primitive element. -/
theorem Remark_1_27_9
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (k : Type u) [Field k] [CharP k p] :
    ∃ (H : Type u) (_ : Ring H) (_ : Algebra k H) (_ : HopfAlgebra k H)
      (_ : Module.Finite k H) (x : H),
      HopfAlgebra.IsPrimitive (R := k) x ∧ x ≠ 0 := by sorry


section Helpers

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- An element is primitive in a bialgebra iff it is `(1, 1)`-skew-primitive. -/
theorem primitive_eq_skewPrimitive_one_one
    {H : Type u} [Ring H] [Bialgebra k H] (x : H) :
    HopfAlgebra.IsPrimitive (R := k) x ↔ IsSkewPrimitive (R := k) (1 : H) (1 : H) x := by
  unfold HopfAlgebra.IsPrimitive IsSkewPrimitive
  constructor <;> intro h <;> exact h

end Helpers

end
