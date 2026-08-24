/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.RingTheory.SimpleModule.Basic
import Atlas.TensorCategories.code.DistinguishedInvertible
import Mathlib.RingTheory.SimpleModule.Basic

set_option maxHeartbeats 400000

set_option autoImplicit false

open Coalgebra
open scoped TensorProduct

universe u v w


section IntegralDefs

variable (R : Type u) [CommSemiring R] (H : Type v) [Semiring H] [Algebra R H] [Coalgebra R H]

/-- A left integral in an algebra `H` with counit is an element `I` satisfying
`x * I = ε(x) • I` for all `x ∈ H` (Definition 1.52.1). -/
structure IsLeftIntegral (I : H) : Prop where
  left_integral : ∀ (x : H), x * I = Coalgebra.counit (R := R) x • I

/-- A right integral in an algebra `H` with counit is an element `I` satisfying
`I * x = ε(x) • I` for all `x ∈ H` (Definition 1.52.1). -/
structure IsRightIntegral (I : H) : Prop where
  right_integral : ∀ (x : H), I * x = Coalgebra.counit (R := R) x • I

/-- Unfolded form of Definition 1.52.1 for left integrals: `∀ x, x * I = ε(x) • I`. -/
def Def_1_52_1_IsLeftIntegral (I : H) : Prop :=
  ∀ x : H, x * I = Coalgebra.counit (R := R) x • I

/-- Unfolded form of Definition 1.52.1 for right integrals: `∀ x, I * x = ε(x) • I`. -/
def Def_1_52_1_IsRightIntegral (I : H) : Prop :=
  ∀ x : H, I * x = Coalgebra.counit (R := R) x • I

/-- The structured predicate `IsLeftIntegral` is equivalent to the unfolded form
`Def_1_52_1_IsLeftIntegral`. -/
theorem isLeftIntegral_iff_def_1_52_1 (I : H) :
    IsLeftIntegral R H I ↔ Def_1_52_1_IsLeftIntegral R H I :=
  ⟨fun h => h.left_integral, fun h => ⟨h⟩⟩

/-- The structured predicate `IsRightIntegral` is equivalent to the unfolded form
`Def_1_52_1_IsRightIntegral`. -/
theorem isRightIntegral_iff_def_1_52_1 (I : H) :
    IsRightIntegral R H I ↔ Def_1_52_1_IsRightIntegral R H I :=
  ⟨fun h => h.right_integral, fun h => ⟨h⟩⟩

end IntegralDefs

section IntegralProperties

variable {R : Type u} [CommSemiring R] {H : Type v} [Semiring H] [Algebra R H] [Coalgebra R H]

/-- The zero element is trivially a left integral. -/
theorem isLeftIntegral_zero : IsLeftIntegral R H (0 : H) :=
  ⟨fun _ => by simp⟩

/-- The zero element is trivially a right integral. -/
theorem isRightIntegral_zero : IsRightIntegral R H (0 : H) :=
  ⟨fun _ => by simp⟩

/-- The set of left integrals is closed under scalar multiplication by elements of `R`. -/
theorem IsLeftIntegral.smul {I : H} (hI : IsLeftIntegral R H I) (r : R) :
    IsLeftIntegral R H (r • I) :=
  ⟨fun x => by rw [mul_smul_comm, hI.left_integral x, smul_comm]⟩

/-- The set of right integrals is closed under scalar multiplication by elements of `R`. -/
theorem IsRightIntegral.smul {I : H} (hI : IsRightIntegral R H I) (r : R) :
    IsRightIntegral R H (r • I) :=
  ⟨fun x => by rw [smul_mul_assoc, hI.right_integral x, smul_comm]⟩

/-- The set of left integrals is closed under addition. -/
theorem IsLeftIntegral.add {I J : H}
    (hI : IsLeftIntegral R H I) (hJ : IsLeftIntegral R H J) :
    IsLeftIntegral R H (I + J) :=
  ⟨fun x => by rw [mul_add, hI.left_integral x, hJ.left_integral x, smul_add]⟩

/-- The set of right integrals is closed under addition. -/
theorem IsRightIntegral.add {I J : H}
    (hI : IsRightIntegral R H I) (hJ : IsRightIntegral R H J) :
    IsRightIntegral R H (I + J) :=
  ⟨fun x => by rw [add_mul, hI.right_integral x, hJ.right_integral x, smul_add]⟩

end IntegralProperties


section IntegralSubmodules

variable (k : Type u) [CommSemiring k] (H : Type v) [Semiring H] [Algebra k H] [Coalgebra k H]

/-- The `k`-submodule of left integrals in `H`. -/
def leftIntSubmodule : Submodule k H where
  carrier := { I : H | IsLeftIntegral k H I }
  add_mem' := by
    intro a b ha hb; exact ⟨fun x => by
      rw [mul_add, ha.left_integral x, hb.left_integral x, smul_add]⟩
  zero_mem' := ⟨fun _ => by simp⟩
  smul_mem' := by
    intro r I hI; exact ⟨fun x => by
      rw [mul_smul_comm, hI.left_integral x, smul_comm]⟩

/-- The `k`-submodule of right integrals in `H`. -/
def rightIntSubmodule : Submodule k H where
  carrier := { I : H | IsRightIntegral k H I }
  add_mem' := by
    intro a b ha hb; exact ⟨fun x => by
      rw [add_mul, ha.right_integral x, hb.right_integral x, smul_add]⟩
  zero_mem' := ⟨fun _ => by simp⟩
  smul_mem' := by
    intro r I hI; exact ⟨fun x => by
      rw [smul_mul_assoc, hI.right_integral x, smul_comm]⟩

/-- Membership in `leftIntSubmodule` is definitionally `IsLeftIntegral`. -/
@[simp]
theorem mem_leftIntSubmodule {I : H} :
    I ∈ leftIntSubmodule k H ↔ IsLeftIntegral k H I := Iff.rfl

/-- Membership in `rightIntSubmodule` is definitionally `IsRightIntegral`. -/
@[simp]
theorem mem_rightIntSubmodule {I : H} :
    I ∈ rightIntSubmodule k H ↔ IsRightIntegral k H I := Iff.rfl

end IntegralSubmodules


/-- A one dimensional submodule contains a nonzero generator: every element is
expressible as a scalar multiple of this generator. -/
theorem exists_nonzero_spanning_of_finrank_one {k : Type u} [Field k] {H : Type v}
    [AddCommGroup H] [Module k H] {S : Submodule k H}
    (hfr : Module.finrank k S = 1) :
    ∃ (I₀ : H), I₀ ∈ S ∧ I₀ ≠ 0 ∧
      ∀ (J : H), J ∈ S → ∃ (c : k), J = c • I₀ := by
  haveI : FiniteDimensional k S := Module.finite_of_finrank_pos (by omega)
  haveI : Nontrivial S := by rw [← Module.finrank_pos_iff (R := k)]; omega
  obtain ⟨⟨a, ha_mem⟩, ⟨b, hb_mem⟩, hab⟩ := (inferInstance : Nontrivial S)
  by_cases ha0 : a = 0
  · subst ha0
    have hb0 : b ≠ 0 := by intro hb0; apply hab; ext; simp [hb0]
    have hspan := (finrank_eq_one_iff_of_nonzero' (K := k)
      (⟨b, hb_mem⟩ : S) (by simp [hb0])).mp hfr
    refine ⟨b, hb_mem, hb0, fun J hJ => ?_⟩
    obtain ⟨c, hc⟩ := hspan ⟨J, hJ⟩
    exact ⟨c, by simpa using (congr_arg Subtype.val hc).symm⟩
  · have hspan := (finrank_eq_one_iff_of_nonzero' (K := k)
      (⟨a, ha_mem⟩ : S) (by simp [ha0])).mp hfr
    refine ⟨a, ha_mem, ha0, fun J hJ => ?_⟩
    obtain ⟨c, hc⟩ := hspan ⟨J, hJ⟩
    exact ⟨c, by simpa using (congr_arg Subtype.val hc).symm⟩


section Prop1523

variable (k : Type u) [Field k] (H : Type v) [Ring H] [Algebra k H] [Coalgebra k H]

/-- Frobenius theorem applied to integrals: the space of left integrals in a finite
dimensional quasi-Hopf algebra has dimension `1`. -/
theorem frobenius_leftIntSubmodule_finrank_one
    (k : Type u) [Field k] (H : Type v) [Ring H] [Algebra k H] [Coalgebra k H]
    [FiniteDimensional k H] :
    Module.finrank k (leftIntSubmodule k H) = 1 := by sorry

/-- Frobenius theorem applied to integrals: the space of right integrals in a finite
dimensional quasi-Hopf algebra has dimension `1`. -/
theorem frobenius_rightIntSubmodule_finrank_one
    (k : Type u) [Field k] (H : Type v) [Ring H] [Algebra k H] [Coalgebra k H]
    [FiniteDimensional k H] :
    Module.finrank k (rightIntSubmodule k H) = 1 := by sorry

/-- Left half of Proposition 1.52.3: there exists a nonzero left integral, unique up
to scaling, in any finite dimensional quasi-Hopf algebra. -/
theorem prop_1_52_3_left [FiniteDimensional k H] :
    ∃ (I₀ : H), IsLeftIntegral k H I₀ ∧ I₀ ≠ 0 ∧
      ∀ (J : H), IsLeftIntegral k H J → ∃ (c : k), J = c • I₀ := by
  obtain ⟨I₀, hI₀mem, hI₀ne, hI₀uniq⟩ :=
    exists_nonzero_spanning_of_finrank_one (frobenius_leftIntSubmodule_finrank_one k H)
  exact ⟨I₀, (mem_leftIntSubmodule k H).mp hI₀mem, hI₀ne,
    fun J hJ => hI₀uniq J ((mem_leftIntSubmodule k H).mpr hJ)⟩

/-- Right half of Proposition 1.52.3: there exists a nonzero right integral, unique up
to scaling, in any finite dimensional quasi-Hopf algebra. -/
theorem prop_1_52_3_right [FiniteDimensional k H] :
    ∃ (I₀ : H), IsRightIntegral k H I₀ ∧ I₀ ≠ 0 ∧
      ∀ (J : H), IsRightIntegral k H J → ∃ (c : k), J = c • I₀ := by
  obtain ⟨I₀, hI₀mem, hI₀ne, hI₀uniq⟩ :=
    exists_nonzero_spanning_of_finrank_one (frobenius_rightIntSubmodule_finrank_one k H)
  exact ⟨I₀, (mem_rightIntSubmodule k H).mp hI₀mem, hI₀ne,
    fun J hJ => hI₀uniq J ((mem_rightIntSubmodule k H).mpr hJ)⟩

/-- Typeclass packaging the existence of a distinguished, essentially unique nonzero
left integral in `H`. -/
class HasUniqueLeftIntegral where
  integral : H
  integral_isLeftIntegral : IsLeftIntegral k H integral
  integral_ne_zero : integral ≠ 0
  integral_unique : ∀ (J : H), IsLeftIntegral k H J → ∃ (c : k), J = c • integral

/-- Typeclass packaging the existence of a distinguished, essentially unique nonzero
right integral in `H`. -/
class HasUniqueRightIntegral where
  integral : H
  integral_isRightIntegral : IsRightIntegral k H integral
  integral_ne_zero : integral ≠ 0
  integral_unique : ∀ (J : H), IsRightIntegral k H J → ∃ (c : k), J = c • integral

/-- Every finite dimensional quasi-Hopf algebra has a distinguished left integral
extracted via choice from `prop_1_52_3_left`. -/
noncomputable instance hasUniqueLeftIntegral_of_finiteDim [FiniteDimensional k H] :
    HasUniqueLeftIntegral k H := by
  classical
  have h := prop_1_52_3_left k H
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2⟩

/-- Every finite dimensional quasi-Hopf algebra has a distinguished right integral
extracted via choice from `prop_1_52_3_right`. -/
noncomputable instance hasUniqueRightIntegral_of_finiteDim [FiniteDimensional k H] :
    HasUniqueRightIntegral k H := by
  classical
  have h := prop_1_52_3_right k H
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2.1, h.choose_spec.2.2⟩

end Prop1523

section Prop1525

variable {R : Type u} [CommSemiring R] {H : Type v} [Semiring H] [Algebra R H] [Coalgebra R H]

/-- For a left integral `I`, the square `I * I` equals `ε(I) • I`, obtained by
specializing the integral equation to `x = I`. -/
theorem IsLeftIntegral.sq_eq_counit_smul {I : H} (hI : IsLeftIntegral R H I) :
    I * I = Coalgebra.counit (R := R) I • I :=
  hI.left_integral I

/-- For a right integral `I`, the square `I * I` equals `ε(I) • I`. -/
theorem IsRightIntegral.sq_eq_counit_smul {I : H} (hI : IsRightIntegral R H I) :
    I * I = Coalgebra.counit (R := R) I • I :=
  hI.right_integral I

/-- If a left integral has nonzero square, then its counit `ε(I)` is also nonzero. -/
theorem counit_ne_zero_of_sq_ne_zero {I : H}
    (hI : IsLeftIntegral R H I) (hsq : I * I ≠ 0) :
    Coalgebra.counit (R := R) I ≠ 0 := by
  intro hε
  exact hsq (by rw [hI.sq_eq_counit_smul, hε, zero_smul])

/-- A nonzero idempotent has nonzero square (trivially, since `I * I = I`). -/
theorem sq_ne_zero_of_idempotent_ne_zero {I : H} (hI : I * I = I) (hne : I ≠ 0) :
    I * I ≠ 0 := by
  rwa [hI]

end Prop1525

section IntegralNormalization

variable {k : Type u} [Field k] {A : Type v} [Semiring A] [Algebra k A] [Coalgebra k A]

/-- If a left integral `I` has nonzero counit `ε(I)`, then `J := ε(I)⁻¹ • I` is a
left integral and is idempotent. -/
theorem isLeftIntegral_normalize {I : A}
    (hI : IsLeftIntegral k A I) (_hε : Coalgebra.counit (R := k) I ≠ 0) :
    let J := (Coalgebra.counit (R := k) I)⁻¹ • I
    IsLeftIntegral k A J ∧ J * J = J := by
  set c := Coalgebra.counit (R := k) I with hc_def
  refine ⟨⟨fun x => ?_⟩, ?_⟩
  ·
    show x * (c⁻¹ • I) = counit x • (c⁻¹ • I)
    rw [mul_smul_comm, hI.left_integral, smul_comm]
  ·
    show (c⁻¹ • I) * (c⁻¹ • I) = c⁻¹ • I
    rw [smul_mul_assoc, mul_smul_comm, hI.left_integral I, smul_smul, smul_smul]
    congr 1; rw [hc_def]; field_simp

end IntegralNormalization

section Prop1525_ii_implies_i

open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Auxiliary step in Proposition 1.52.5: after normalizing `I` by dividing by `ε(I)`,
the counit of the result equals `1`. -/
theorem prop_1_52_5_ii_implies_i
    {k : Type w} [Field k] {A : Type*} [Semiring A] [Algebra k A] [Coalgebra k A]
    {I : A} (_hI : IsLeftIntegral k A I)
    (hε : Coalgebra.counit (R := k) I ≠ 0)
    (_hne : I ≠ 0) :


    Coalgebra.counit (R := k) ((Coalgebra.counit (R := k) I)⁻¹ • I) =
      (1 : k) := by
  simp [map_smul, inv_mul_cancel₀ hε]

/-- For a nonzero left integral, the equivalence (iii) `I² ≠ 0` ↔ (ii) `ε(I) ≠ 0`
in Proposition 1.52.5. -/
theorem prop_1_52_5_iii_iff_ii {k : Type u} [Field k]
    {H : Type v} [Semiring H] [Algebra k H] [Coalgebra k H]
    {I : H} (hI : IsLeftIntegral k H I) (hne : I ≠ 0) :
    I * I ≠ 0 ↔ Coalgebra.counit (R := k) I ≠ 0 := by
  constructor
  · exact counit_ne_zero_of_sq_ne_zero hI
  · intro hε
    rw [hI.sq_eq_counit_smul]
    exact smul_ne_zero hε hne

end Prop1525_ii_implies_i


section DistinguishedCharacter

variable (R : Type u) [CommSemiring R] (H : Type v) [Semiring H] [Algebra R H] [Coalgebra R H]

/-- The distinguished character `χ : H →ₗ[R] R` associated to a left integral `I`,
characterized by the right multiplication law `I * x = χ(x) • I`. -/
structure DistinguishedCharacter (I : H) where
  χ : H →ₗ[R] R
  left_int : IsLeftIntegral R H I
  right_law : ∀ (x : H), I * x = χ x • I

/-- If `I` is a left integral, then `I * y` is also a left integral for any `y ∈ H`. -/
theorem IsLeftIntegral.right_mul_isLeftIntegral
    {R : Type u} [CommSemiring R] {H : Type v} [Semiring H] [Algebra R H] [Coalgebra R H]
    {I : H} (hI : IsLeftIntegral R H I) (y : H) :
    IsLeftIntegral R H (I * y) :=
  ⟨fun x => by
    rw [← mul_assoc, hI.left_integral x, smul_mul_assoc]⟩

/-- An algebra is unimodular when every left integral is also a right integral
(Definition 1.52.6 at the algebra level). -/
def IsUnimodularAlgebra : Prop :=
  ∀ (I : H), IsLeftIntegral R H I → IsRightIntegral R H I

end DistinguishedCharacter


section Proposition_1_52_4

open CategoryTheory

variable (k : Type u) [Field k] (H : Type v) [Ring H] [Algebra k H] [Coalgebra k H]

/-- Categorical data needed to state Proposition 1.52.4: a procedure constructing
the one dimensional representation associated to a character, plus the agreement
between the distinguished invertible object and that representation. -/
class Prop1524Data
    (C : Type*) [Category C] [MonoidalCategory C] [RigidCategory C]
    [HasDistinguishedInvertibleData C] [FiniteDimensional k H] where
  oneDimChar : (H →ₗ[k] k) → C
  lρ_iso_distinguishedChar :
    ∀ (I : H) (_hI : I ≠ 0) (dc : DistinguishedCharacter k H I),
      Nonempty (HasDistinguishedInvertibleData.distinguished (C := C) ≅ oneDimChar dc.χ)

/-- Alias for `Prop1524Data` used when `C = Rep(H)`. -/
abbrev Prop1524RepData := Prop1524Data

end Proposition_1_52_4


section Prop1524_consequences

variable (k : Type u) [Field k] (H : Type v) [Ring H] [Algebra k H] [Coalgebra k H]

/-- If `H` is unimodular, the distinguished character of any nonzero left integral
coincides with the counit on all of `H`. -/
theorem distinguished_char_eq_counit_of_unimodular
    (I : H) (dc : DistinguishedCharacter k H I) (hI_ne : I ≠ 0)
    (huni : IsUnimodularAlgebra k H) :
    ∀ x : H, dc.χ x = Coalgebra.counit (R := k) x := by
  intro x
  have hIright := huni I dc.left_int
  have h1 := dc.right_law x
  have h2 := hIright.right_integral x

  have h3 : dc.χ x • I = Coalgebra.counit (R := k) x • I := h1.symm.trans h2

  by_contra h
  apply hI_ne
  have hsub : (dc.χ x - Coalgebra.counit (R := k) x) • I = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact h3
  rcases smul_eq_zero.mp hsub with hab | hI_eq
  · exact absurd (sub_eq_zero.mp hab) h
  · exact hI_eq

/-- Converse: if the distinguished character equals the counit, then `I` is a right
integral as well. -/
theorem left_integral_is_right_of_char_eq_counit
    (I : H) (dc : DistinguishedCharacter k H I)
    (hχε : ∀ x : H, dc.χ x = Coalgebra.counit (R := k) x) :
    IsRightIntegral k H I :=
  ⟨fun x => by rw [dc.right_law x, hχε x]⟩

end Prop1524_consequences


section BialgebraIntegrals

variable {R : Type u} [CommSemiring R] {H : Type v} [Semiring H] [Bialgebra R H]

/-- Trivial restatement: multiplication of a left integral by the unit element returns
the integral. -/
theorem IsLeftIntegral.unit_mul {I : H} (_hI : IsLeftIntegral R H I) :
    (1 : H) * I = I :=
  one_mul I

/-- Symmetric form of `sq_eq_counit_smul`: `ε(I) • I = I * I` for a left integral `I`. -/
theorem IsLeftIntegral.counit_smul_self_eq_sq {I : H} (hI : IsLeftIntegral R H I) :
    Coalgebra.counit (R := R) I • I = I * I :=
  (hI.sq_eq_counit_smul).symm

end BialgebraIntegrals


section Prop1525Full

variable {k : Type u} [Field k] {H : Type v} [Ring H] [Algebra k H] [Coalgebra k H]

/-- Equivalence (i) ↔ (ii) of Proposition 1.52.5: `H` is semisimple iff `ε(I) ≠ 0`
for a nonzero left integral `I`. -/
theorem proposition_1_52_5_semisimple_iff_counit_ne_zero
    [FiniteDimensional k H]
    {I : H} (hI : IsLeftIntegral k H I) (hne : I ≠ 0) :
    IsSemisimpleRing H ↔ Coalgebra.counit (R := k) I ≠ 0 := by
  sorry

/-- Equivalence (i) ↔ (iii) of Proposition 1.52.5: `H` is semisimple iff `I * I ≠ 0`
for a nonzero left integral `I`. -/
theorem proposition_1_52_5_semisimple_iff_sq_ne_zero
    [FiniteDimensional k H]
    {I : H} (hI : IsLeftIntegral k H I) (hne : I ≠ 0) :
    IsSemisimpleRing H ↔ I * I ≠ 0 := by
  sorry

/-- Equivalence (i) ↔ (iv) of Proposition 1.52.5: `H` is semisimple iff there exists
a nonzero idempotent left integral. -/
theorem proposition_1_52_5_semisimple_iff_idempotent
    [FiniteDimensional k H]
    {I : H} (hI : IsLeftIntegral k H I) (hne : I ≠ 0) :
    IsSemisimpleRing H ↔
      (∃ J : H, IsLeftIntegral k H J ∧ J * J = J ∧ J ≠ 0) := by
  sorry

/-- Full statement of Proposition 1.52.5: the chained equivalences `(i) ↔ (ii)`,
`(ii) ↔ (iii)`, and `(iii) ↔ (iv)`. -/
theorem proposition_1_52_5
    [FiniteDimensional k H]
    {I : H} (hI : IsLeftIntegral k H I) (hne : I ≠ 0) :
    (IsSemisimpleRing H ↔ Coalgebra.counit (R := k) I ≠ 0) ∧
    (Coalgebra.counit (R := k) I ≠ 0 ↔ I * I ≠ 0) ∧
    (I * I ≠ 0 ↔ ∃ J : H, IsLeftIntegral k H J ∧ J * J = J ∧ J ≠ 0) := by
  refine ⟨proposition_1_52_5_semisimple_iff_counit_ne_zero hI hne,
         (prop_1_52_5_iii_iff_ii hI hne).symm, ?_⟩
  sorry

end Prop1525Full
