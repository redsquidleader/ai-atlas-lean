/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

noncomputable section

open Finsupp

variable {P : Type*}

/-- The group of divisors on a curve (with point type `P`): the free abelian
group on `P`, modeled as `P →₀ ℤ`. Cf. Definition 23.13 (Sutherland §23.2): a
divisor is a finite formal sum `D = ∑_P n_P [P]` of points with integer
coefficients. -/
abbrev CurveDiv (P : Type*) := P →₀ ℤ

namespace CurveDiv

/-- The divisor `[p]` consisting of a single point with multiplicity `1`. -/
def of (p : P) : CurveDiv P := Finsupp.single p 1

/-- The coefficient (valuation) of `D` at `p`: this is `v_P(D)` in the notation
of Definition 23.13. -/
def coeff (D : CurveDiv P) (p : P) : ℤ := D p

/-- The coefficient of `[p]` at `p` is `1`. -/
@[simp]
theorem coeff_of_same [DecidableEq P] (p : P) :
    (of p).coeff p = 1 := by
  simp [coeff, of]

/-- The coefficient of `[p]` at a different point `q` is `0`. -/
@[simp]
theorem coeff_of_ne [DecidableEq P] {p q : P} (h : p ≠ q) :
    (of p).coeff q = 0 := by
  simp [coeff, of, h]

/-- The support of a divisor `D`: the finite set of points where its coefficient
is nonzero. Cf. Definition 23.13. -/
def supp (D : CurveDiv P) : Finset P := D.support

/-- Characterization of the support: `p ∈ supp D` iff its coefficient is
nonzero. -/
@[simp]
theorem mem_supp_iff (D : CurveDiv P) (p : P) :
    p ∈ D.supp ↔ D.coeff p ≠ 0 := by
  simp [supp, coeff, Finsupp.mem_support_iff]

/-- The degree of a divisor: `deg D := ∑_P v_P(D)` (Definition 23.13). -/
def deg (D : CurveDiv P) : ℤ := D.sum (fun _ n => n)

/-- The degree of the zero divisor is zero. -/
@[simp]
theorem deg_zero : deg (0 : CurveDiv P) = 0 := by
  simp [deg, Finsupp.sum]

/-- The degree of a single-point divisor `n[p]` is `n`. -/
@[simp]
theorem deg_single [DecidableEq P] (p : P) (n : ℤ) :
    deg (Finsupp.single p n) = n := by
  simp [deg, Finsupp.sum_single_index]

/-- The degree of the divisor `[p]` is `1`. -/
@[simp]
theorem deg_of [DecidableEq P] (p : P) : deg (of p) = 1 := by
  simp [of, deg_single]

/-- Additivity of the degree: `deg(D₁ + D₂) = deg D₁ + deg D₂`. -/
theorem deg_add (D₁ D₂ : CurveDiv P) :
    (D₁ + D₂).deg = D₁.deg + D₂.deg := by
  classical
  simp only [deg]
  exact Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

/-- The degree map `Div C → ℤ` packaged as an additive group homomorphism. -/
def degHom (P : Type*) : CurveDiv P →+ ℤ where
  toFun := deg
  map_zero' := deg_zero
  map_add' := deg_add

/-- The subgroup `Div⁰ C` of divisors of degree zero, defined as the kernel of
the degree map. (Cf. Definition 23.13.) -/
def DivZero (P : Type*) : AddSubgroup (CurveDiv P) :=
  AddMonoidHom.ker (degHom P)

/-- Membership in `DivZero P` is equivalent to having degree zero. -/
theorem mem_divZero_iff (D : CurveDiv P) :
    D ∈ DivZero P ↔ D.deg = 0 := by
  simp [DivZero, degHom, AddMonoidHom.mem_ker]

/-- A "function-field-with-divisor-map" structure: a multiplicative group `F`
(intended to be the function field `k(C)^×`), a subgroup `kUnits` of constants
`k^×`, and a group homomorphism `divMap : (F, ·) → (Div C, +)` sending each
nonzero function to its principal divisor `div f`. -/
structure FunctionFieldDiv (P : Type*) where
  F : Type*
  [instCommGroup : CommGroup F]
  kUnits : Subgroup F
  divMap : Additive F →+ CurveDiv P

attribute [instance] FunctionFieldDiv.instCommGroup

/-- Every principal divisor has degree zero (Corollary 23.10 / Definition
23.13). -/
theorem principalDivisor_degree_zero {P : Type*}
    (Φ : FunctionFieldDiv P) (f : Additive Φ.F) : (Φ.divMap f).deg = 0 := by sorry

/-- The kernel of the `f ↦ div f` map consists exactly of the nonzero constants
`k^×` (Corollary 23.10). -/
theorem principalDivisor_kernel_eq_constants {P : Type*}
    (Φ : FunctionFieldDiv P) (f : Φ.F) :
    Φ.divMap (Additive.ofMul f) = 0 ↔ f ∈ Φ.kUnits := by sorry

variable (Φ : FunctionFieldDiv P)

/-- The subgroup `Princ C ⊆ Div C` of principal divisors, defined as the image
of the function-field divisor map. (Definition 23.13.) -/
def PrincDiv : AddSubgroup (CurveDiv P) :=
  AddMonoidHom.range Φ.divMap

/-- Principal divisors are divisors of degree zero. -/
theorem princDiv_le_divZero : PrincDiv Φ ≤ DivZero P := by
  intro D hD
  obtain ⟨f, rfl⟩ := hD
  show Φ.divMap f ∈ AddMonoidHom.ker (degHom P)
  rw [AddMonoidHom.mem_ker]
  exact principalDivisor_degree_zero Φ f

/-- The corestriction of the function-field divisor map to the subgroup of
degree-zero divisors. -/
def divMapToDivZero : Additive Φ.F →+ DivZero P :=
  AddMonoidHom.codRestrict Φ.divMap (DivZero P) (fun f =>
    princDiv_le_divZero Φ ⟨f, rfl⟩)

/-- The *Picard group* `Pic C := Div C / Princ C` of divisor classes. -/
abbrev PicardGroup : Type _ :=
  CurveDiv P ⧸ PrincDiv Φ

/-- Since principal divisors have degree zero, the degree map descends to a
homomorphism `Pic C → ℤ` from the Picard group. -/
def degHomPic : (CurveDiv P ⧸ PrincDiv Φ) →+ ℤ :=
  QuotientAddGroup.lift (PrincDiv Φ) (degHom P) (by
    intro x hx
    obtain ⟨f, rfl⟩ := hx
    simp only [degHom]
    exact principalDivisor_degree_zero Φ f)

/-- The group `Pic⁰ C := Div⁰ C / Princ C` of divisor classes of degree zero
(Definition 23.13). -/
abbrev PicardGroupZero : Type _ :=
  (DivZero P) ⧸ (PrincDiv Φ).addSubgroupOf (DivZero P)

section AbelJacobi

variable {P : Type*}

/-- The degree-zero divisor `[p] - [O]` for the Abel-Jacobi map with origin
`O` (Definition 23.15). -/
def abelJacobiDivAt (O : P) (p : P) : DivZero P :=
  ⟨Finsupp.single p 1 - Finsupp.single O 1,
   (mem_divZero_iff _).mpr (by
     classical
     show (degHom P) _ = 0
     simp [degHom, map_sub, deg_single])⟩

/-- Unfolding: the underlying divisor of `abelJacobiDivAt O p` is
`[p] - [O]`. -/
@[simp]
theorem abelJacobiDivAt_coe (O p : P) :
    (abelJacobiDivAt O p : CurveDiv P) = Finsupp.single p 1 - Finsupp.single O 1 := rfl

/-- `abelJacobiDivAt O O = 0`, since `[O] - [O] = 0`. -/
theorem abelJacobiDivAt_self (O : P) : abelJacobiDivAt O O = (0 : DivZero P) := by
  apply Subtype.ext; simp [abelJacobiDivAt_coe]

/-- The Abel-Jacobi map `P ↦ [p] - [O]` modulo principal divisors, as a function
`P → Pic⁰ C` (Definition 23.15). -/
def abelJacobiMapAt (Φ : FunctionFieldDiv P) (O : P) (p : P) : PicardGroupZero Φ :=
  QuotientAddGroup.mk (abelJacobiDivAt O p)

end AbelJacobi

/-- For `P` an abelian group, the *point sum* of a divisor `∑ n_P [P]` is
`∑ n_P · P`, interpreted in the group `P`. For elliptic curves this is the map
`Div E → E` induced by the group law. -/
def pointSum [AddCommGroup P] (D : CurveDiv P) : P :=
  D.sum (fun p n => n • p)

/-- `pointSum` packaged as an additive group homomorphism `Div C → P`. -/
def pointSumHom (P : Type*) [AddCommGroup P] : CurveDiv P →+ P where
  toFun := pointSum
  map_zero' := by simp [pointSum, Finsupp.sum]
  map_add' D₁ D₂ := by
    classical
    simp only [pointSum]
    exact Finsupp.sum_add_index' (fun _ => zero_zsmul _) (fun _ _ _ => add_zsmul _ _ _)

/-- Definitional unfolding: `pointSumHom P D = pointSum D`. -/
@[simp]
theorem pointSumHom_apply [AddCommGroup P] (D : CurveDiv P) :
    pointSumHom P D = D.pointSum := rfl

/-- The point sum of the zero divisor is `0`. -/
@[simp]
theorem pointSum_zero [AddCommGroup P] :
    pointSum (0 : CurveDiv P) = 0 :=
  (pointSumHom P).map_zero

/-- The point sum of a single-point divisor `n[p]` is `n • p`. -/
@[simp]
theorem pointSum_single [DecidableEq P] [AddCommGroup P] (p : P) (n : ℤ) :
    pointSum (Finsupp.single p n : CurveDiv P) = n • p := by
  simp [pointSum, Finsupp.sum_single_index, zero_zsmul]

/-- `pointSum` respects subtraction. -/
theorem pointSum_sub [AddCommGroup P] (D₁ D₂ : CurveDiv P) :
    (D₁ - D₂).pointSum = D₁.pointSum - D₂.pointSum :=
  map_sub (pointSumHom P) D₁ D₂

/-- The point sum of `[p]` is `p`. -/
@[simp]
theorem pointSum_of [DecidableEq P] [AddCommGroup P] (p : P) :
    (of p).pointSum = p := by
  simp [of, pointSum_single]

/-- A principal divisor sums (under the group law of `P`) to `0`. This is one
direction of the Abel-Jacobi isomorphism (Theorem 23.17) for elliptic curves. -/
theorem pointSum_principal_eq_zero {P : Type*} [AddCommGroup P]
    (Φ : FunctionFieldDiv P) (f : Additive Φ.F) :
    (Φ.divMap f).pointSum = 0 := by sorry

/-- Surjectivity content of Abel-Jacobi (Theorem 23.17): every divisor `D` of
degree zero is equivalent modulo principal divisors to `[D.pointSum] - [0]`. -/
theorem abelJacobi_surj {P : Type*} [AddCommGroup P]
    (Φ : FunctionFieldDiv P) (D : CurveDiv P) (hdeg : D.deg = 0) :
    D - (Finsupp.single D.pointSum 1 - Finsupp.single (0 : P) 1) ∈
      PrincDiv Φ := by sorry

variable {P : Type*} [AddCommGroup P] (Φ' : FunctionFieldDiv P)

/-- A divisor on an elliptic curve (group `P`) is principal iff it has degree
zero and its point-sum vanishes. This is the standard "sum-to-zero" criterion
for principal divisors (cf. Theorem 23.17). -/
theorem principal_iff_deg_zero_and_pointSum_zero (D : CurveDiv P) :
    D ∈ PrincDiv Φ' ↔ D.deg = 0 ∧ D.pointSum = 0 := by
  constructor
  ·
    intro hD
    obtain ⟨f, rfl⟩ := hD
    exact ⟨principalDivisor_degree_zero Φ' f, pointSum_principal_eq_zero Φ' f⟩
  ·
    intro ⟨hdeg, hsum⟩

    have hsurj := abelJacobi_surj Φ' D hdeg

    rw [hsum] at hsurj
    simp only [sub_self, sub_zero] at hsurj
    exact hsurj

/-- The Abel-Jacobi divisor with origin `0 : P`: `[p] - [0]`. -/
def abelJacobiDiv (p : P) : DivZero P := abelJacobiDivAt 0 p

/-- The underlying divisor of `abelJacobiDiv p` is `[p] - [0]`. -/
@[simp]
theorem abelJacobiDiv_coe (p : P) :
    (abelJacobiDiv p : CurveDiv P) = Finsupp.single p 1 - Finsupp.single (0 : P) 1 := rfl

/-- `abelJacobiDiv 0 = 0`. -/
theorem abelJacobiDiv_zero : abelJacobiDiv (0 : P) = (0 : DivZero P) :=
  abelJacobiDivAt_self 0

/-- The point-sum map restricted to degree-zero divisors, as an additive group
homomorphism `Div⁰ C → P`. -/
def pointSumHomDivZero : DivZero P →+ P :=
  (pointSumHom P).comp (DivZero P).subtype

/-- The point-sum map descends to `Pic⁰ C → P` since principal divisors have
zero point-sum; this is the *inverse* of the Abel-Jacobi isomorphism. -/
def pointSumHomPic : PicardGroupZero Φ' →+ P :=
  QuotientAddGroup.lift ((PrincDiv Φ').addSubgroupOf (DivZero P))
    pointSumHomDivZero (by
      intro ⟨D, hD_mem⟩ hD
      simp only [AddMonoidHom.mem_ker, pointSumHomDivZero, AddMonoidHom.coe_comp,
                 AddSubgroup.coe_subtype, Function.comp_apply, pointSumHom_apply]
      rw [AddSubgroup.mem_addSubgroupOf] at hD
      obtain ⟨f, hf⟩ := hD
      rw [show D = Φ'.divMap f from hf.symm ▸ rfl]
      exact pointSum_principal_eq_zero Φ' f)

/-- The Abel-Jacobi map `p ↦ [[p] - [0]]` as an additive group homomorphism
`P → Pic⁰ C` (Theorem 23.17 for elliptic curves). -/
def abelJacobiHom : P →+ PicardGroupZero Φ' where
  toFun p := QuotientAddGroup.mk (abelJacobiDiv p)
  map_zero' := by simp only [abelJacobiDiv_zero]; rfl
  map_add' p q := by
    classical
    rw [← QuotientAddGroup.mk_add, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    rw [principal_iff_deg_zero_and_pointSum_zero Φ']


    constructor
    ·
      show (degHom P) (↑(-(abelJacobiDiv (p + q)) + (abelJacobiDiv p + abelJacobiDiv q))) = 0
      simp [degHom, map_add, abelJacobiDiv_coe, map_sub]
    ·
      show (pointSumHom P) (↑(-(abelJacobiDiv (p + q)) + (abelJacobiDiv p + abelJacobiDiv q))) = 0
      simp [map_add, map_sub, abelJacobiDiv_coe, pointSumHom_apply,
            pointSum_single]

/-- One half of the Abel-Jacobi isomorphism: composing `abelJacobiHom` with the
inverse `pointSumHomPic` recovers the identity on points. -/
theorem pointSumHomPic_abelJacobiHom (p : P) :
    pointSumHomPic Φ' (abelJacobiHom Φ' p) = p := by
  classical
  simp only [abelJacobiHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, pointSumHomPic,
             QuotientAddGroup.lift_mk, pointSumHomDivZero, AddMonoidHom.coe_comp,
             AddSubgroup.coe_subtype, Function.comp_apply, pointSumHom_apply,
             abelJacobiDiv_coe, pointSum_sub, pointSum_single]
  simp

/-- Other half of the Abel-Jacobi isomorphism: composing in the other order
recovers the identity on `Pic⁰ C`. -/
theorem abelJacobiHom_pointSumHomPic (x : PicardGroupZero Φ') :
    abelJacobiHom Φ' (pointSumHomPic Φ' x) = x := by
  classical
  induction x using QuotientAddGroup.induction_on with
  | H D =>
    simp only [pointSumHomPic, QuotientAddGroup.lift_mk, pointSumHomDivZero,
               AddMonoidHom.coe_comp, AddSubgroup.coe_subtype, Function.comp_apply,
               abelJacobiHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, pointSumHom_apply]
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    rw [principal_iff_deg_zero_and_pointSum_zero Φ']
    obtain ⟨Dval, hD_mem⟩ := D
    have hdeg : Dval.deg = 0 := (mem_divZero_iff Dval).mp hD_mem
    constructor
    ·
      show (degHom P) (↑(-(abelJacobiDiv Dval.pointSum) + ⟨Dval, hD_mem⟩)) = 0
      simp [degHom, map_add, abelJacobiDiv_coe, map_sub, hdeg]
    ·
      show (pointSumHom P) (↑(-(abelJacobiDiv Dval.pointSum) + ⟨Dval, hD_mem⟩)) = 0
      simp [map_add, abelJacobiDiv_coe, pointSumHom_apply,
            pointSum_sub, pointSum_single]

/-- The Abel-Jacobi isomorphism `P ≃+ Pic⁰ C` for an elliptic curve, packaged as
an `AddEquiv` (Theorem 23.17 of Sutherland). -/
def picZeroEquivEC : P ≃+ PicardGroupZero Φ' where
  toFun := abelJacobiHom Φ'
  invFun := pointSumHomPic Φ'
  left_inv p := pointSumHomPic_abelJacobiHom Φ' p
  right_inv x := abelJacobiHom_pointSumHomPic Φ' x
  map_add' := (abelJacobiHom Φ').map_add'

end CurveDiv

noncomputable section

/-- A smooth projective curve, represented abstractly by a type of points
`Point`, a function field `FunctionField` (a field), and a discrete-valuation
map `val P : FunctionField → WithTop ℤ` at each point `P` satisfying the
standard axioms of a normalized valuation: `val P 0 = ⊤`, `val P 1 = 0`,
`val P (fg) = val P f + val P g`, `val P (f+g) ≥ min (val P f) (val P g)`,
finiteness at nonzero elements, and surjectivity onto `ℤ`. -/
structure SmoothProjectiveCurve where
  Point : Type*
  FunctionField : Type*
  [fieldInst : Field FunctionField]
  val : Point → FunctionField → WithTop ℤ
  val_zero : ∀ P, val P 0 = ⊤
  val_one : ∀ P, val P 1 = 0
  val_mul : ∀ P f g, val P (f * g) = val P f + val P g
  val_add : ∀ P f g, min (val P f) (val P g) ≤ val P (f + g)
  val_ne_top : ∀ P (f : FunctionField), f ≠ 0 → val P f ≠ ⊤
  val_surj : ∀ P (n : ℤ), ∃ f : FunctionField, f ≠ 0 ∧ val P f = ↑n

attribute [instance] SmoothProjectiveCurve.fieldInst

/-- A morphism `C → ℙ¹` from a smooth projective curve, recorded via a chosen
function `f`, its degree, and the (finite) fiber over each point of `ℙ¹`. The
`uniformizerComp Q` represents the uniformizer at `Q ∈ ℙ¹` pulled back to a
function on `C`. -/
structure MorphismToP1 (C : SmoothProjectiveCurve) where
  f : C.FunctionField
  f_ne_zero : f ≠ 0
  deg : ℤ
  deg_pos : 0 < deg
  P1Point : Type*
  uniformizerComp : P1Point → C.FunctionField
  uniformizerComp_ne_zero : ∀ Q, uniformizerComp Q ≠ 0
  fiber : P1Point → Finset C.Point
  mem_fiber_iff : ∀ Q (P : C.Point),
    P ∈ fiber Q ↔ (0 : WithTop ℤ) < C.val P (uniformizerComp Q)

/-- The degree of a morphism `φ : C → ℙ¹` equals the sum, over the points `P` in
the fiber over `Q`, of the valuation `v_P(uniformizerComp Q)`. This is the
content of the degree-fiber formula for morphisms to `ℙ¹`. -/
theorem deg_eq_sum_fiber_val (C : SmoothProjectiveCurve)
    (φ : MorphismToP1 C) (Q : φ.P1Point) :
    (φ.deg : ℤ) = (φ.fiber Q).sum (fun P =>
      WithTop.untopD 0 (C.val P (φ.uniformizerComp Q))) := by sorry

/-- A rational map `C → ℙ^{m-1}` represented by `m` rational functions on `C`,
not all of which are identically zero. -/
structure RationalMap (C : SmoothProjectiveCurve) (m : ℕ) where
  coords : Fin m → C.FunctionField
  not_all_zero : ∃ i, coords i ≠ 0

/-- A rational map is *defined at* a point `P` if there exists a rescaling
`c ∈ k(C)^×` so that every coordinate `c · coords i` has nonnegative valuation
at `P` and at least one has valuation zero. -/
def RationalMap.isDefinedAt {C : SmoothProjectiveCurve} {m : ℕ}
    (φ : RationalMap C m) (P : C.Point) : Prop :=
  ∃ (c : C.FunctionField), c ≠ 0 ∧
    (∀ i, (0 : WithTop ℤ) ≤ C.val P (c * φ.coords i)) ∧
    (∃ i, C.val P (c * φ.coords i) = 0)

/-- A rational map is a *morphism* if it is defined at every point. -/
def RationalMap.isMorphism {C : SmoothProjectiveCurve} {m : ℕ}
    (φ : RationalMap C m) : Prop :=
  ∀ P : C.Point, φ.isDefinedAt P

/-- Every rational map from a smooth projective curve to projective space is in
fact a morphism: at any point one can scale by a uniformizer chosen with the
correct order to clear poles and avoid common zeros. -/
theorem rational_map_is_morphism (C : SmoothProjectiveCurve)
    {m : ℕ} (hm : 0 < m) (φ : RationalMap C m) : φ.isMorphism := by
  intro P
  have hne : (Finset.univ : Finset (Fin m)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩

  obtain ⟨i₀, _, hi₀⟩ :=
    Finset.exists_mem_eq_inf' hne (fun i => C.val P (φ.coords i))

  obtain ⟨j, hj⟩ := φ.not_all_zero
  have hmin_ne_top : C.val P (φ.coords i₀) ≠ ⊤ := by
    intro h
    have hle : C.val P (φ.coords i₀) ≤ C.val P (φ.coords j) := by
      rw [← hi₀]; exact Finset.inf'_le _ (Finset.mem_univ j)
    rw [h] at hle
    exact C.val_ne_top P _ hj (WithTop.top_le_iff.mp hle)

  obtain ⟨n_min, hn_min⟩ := WithTop.ne_top_iff_exists.mp hmin_ne_top

  obtain ⟨c, hc_ne, hc_val⟩ := C.val_surj P (-n_min)
  refine ⟨c, hc_ne, fun i => ?_, ⟨i₀, ?_⟩⟩
  ·

    rw [C.val_mul, hc_val]
    have hi_le : C.val P (φ.coords i₀) ≤ C.val P (φ.coords i) := by
      rw [← hi₀]; exact Finset.inf'_le _ (Finset.mem_univ i)
    rw [← hn_min] at hi_le
    cases hv : C.val P (φ.coords i) with
    | top => exact le_top
    | coe k =>
      rw [hv] at hi_le
      simp only [WithTop.coe_le_coe] at hi_le
      rw [← WithTop.coe_add]
      exact WithTop.coe_le_coe.mpr (by omega)
  ·
    rw [C.val_mul, hc_val, ← hn_min, ← WithTop.coe_add]
    simp [neg_add_cancel]

end
