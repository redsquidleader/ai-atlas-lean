/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.TensorCategories.code.GrothendieckRingCategorical
import Atlas.TensorCategories.code.GradedVec
import Atlas.TensorCategories.code.TannakaReconstruction

open Finset

/-- The data of a `ℤ₊`-ring on a basis indexed by `ι`: structure constants
`N i j k`, a set `I₀ ⊂ ι` of unit basis elements, finiteness of the support of each
product, and associativity expressed via the finite sums of products of structure constants. -/
structure ZPlusRingDef (ι : Type*) [DecidableEq ι] where
  N : ι → ι → ι → ℕ
  I₀ : Finset ι
  finite_support : ∀ i j, Set.Finite {k | N i j k ≠ 0}
  sum_I₀_mul_left : ∀ j k, (∑ s ∈ I₀, N s j k) = if j = k then 1 else 0
  sum_I₀_mul_right : ∀ i k, (∑ s ∈ I₀, N i s k) = if i = k then 1 else 0
  assoc_finite : ∀ i j k l,
    Set.Finite {m | N i j m * N m k l ≠ 0} ∧
    Set.Finite {m | N j k m * N i m l ≠ 0} ∧
    ∑ᶠ m, N i j m * N m k l = ∑ᶠ m, N j k m * N i m l

/-- A `ℤ₊`-ring `A` is unital if `1` belongs to its basis, i.e. the unit set `I₀` is a
singleton. -/
def ZPlusRingDef.IsUnital {ι : Type*} [DecidableEq ι] (A : ZPlusRingDef ι) : Prop :=
  ∃ u : ι, A.I₀ = {u}

/-- The data of a based ring (Definition 1.42.2(1)): a `ℤ₊`-ring with an involution
`star : ι → ι` whose induced map `a ↦ a^*` is an anti-involution of the ring, such that
`τ(b_i b_j) = δ_{i, j^*}`. -/
structure BasedRingDef (ι : Type*) [DecidableEq ι] extends ZPlusRingDef ι where
  star : ι → ι
  star_star : ∀ i, star (star i) = i
  duality_trace : ∀ i j, (∑ k ∈ I₀, N i j k) = if i = star j then 1 else 0
  star_anti : ∀ i j k, N i j k = N (star j) (star i) (star k)

/-- A based ring is unital if the basis contains `1`, i.e. `I₀` is a singleton. -/
def BasedRingDef.IsUnital {ι : Type*} [DecidableEq ι] (B : BasedRingDef ι) : Prop :=
  ∃ u : ι, B.I₀ = {u}

/-- A multifusion ring (Definition 1.42.2(3)) is a based ring of finite rank. Encoded
as the full collection of structure constants `N`, the unit subset `I₀`, the duality
involution `star`, and the associativity, unit, and duality axioms, all stated over a
finite index type `ι`. -/
structure MultifusionRingDef (ι : Type*) [DecidableEq ι] [Fintype ι] where
  N : ι → ι → ι → ℕ
  I₀ : Finset ι
  star : ι → ι
  star_star : ∀ i, star (star i) = i
  assoc : ∀ i j k l, ∑ m : ι, N i j m * N m k l = ∑ m : ι, N j k m * N i m l
  sum_I₀_mul_left : ∀ j k, (∑ s ∈ I₀, N s j k) = if j = k then 1 else 0
  sum_I₀_mul_right : ∀ i k, (∑ s ∈ I₀, N i s k) = if i = k then 1 else 0
  duality_trace : ∀ i j, (∑ k ∈ I₀, N i j k) = if i = star j then 1 else 0
  star_anti : ∀ i j k, N i j k = N (star j) (star i) (star k)

/-- A multifusion ring is a fusion ring if it is unital, i.e. the unit set `I₀` is a
singleton. -/
def MultifusionRingDef.IsFusionRing {ι : Type*} [DecidableEq ι] [Fintype ι]
    (B : MultifusionRingDef ι) : Prop :=
  ∃ u : ι, B.I₀ = {u}

namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- In a fusion ring, the duality identity `τ(b_i b_j) = δ_{i, j^*}` specialised to the
singleton `{R.unit}` of unit basis elements. -/
theorem duality_trace_singleton (i j : ι) :
    (∑ k ∈ ({R.unit} : Finset ι), R.N i j k) = if i = R.star j then 1 else 0 := by
  simp only [Finset.sum_singleton]
  rw [R.duality]
  congr 1
  exact propext ⟨fun h => by rw [h, R.star_star],
    fun h => by rw [h, R.star_star]⟩

/-- In a fusion ring, the duality involution `star` is an anti-involution: the structure
constants satisfy `N i j k = N (star j) (star i) (star k)`. -/
theorem star_anti_involution (i j k : ι) :
    R.N i j k = R.N (R.star j) (R.star i) (R.star k) := by
  have step1 : R.N i j k = R.N j (R.star k) (R.star i) := by
    have assoc_eq := R.assoc i j (R.star k) R.unit
    have lhs_simp : (∑ m : ι, R.N i j m * R.N m (R.star k) R.unit) = R.N i j k := by
      have : ∀ m, R.N m (R.star k) R.unit = if m = k then 1 else 0 := by
        intro m
        rw [R.duality]
        congr 1
        exact propext ⟨fun h => by have := congr_arg R.star h; simp only [R.star_star] at this; exact this.symm,
          fun h => by rw [h]⟩
      simp_rw [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have rhs_simp : (∑ m : ι, R.N j (R.star k) m * R.N i m R.unit) =
        R.N j (R.star k) (R.star i) := by
      have : ∀ m, R.N i m R.unit = if m = R.star i then 1 else 0 := by
        intro m; exact R.duality i m
      simp_rw [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linarith [assoc_eq]
  have step2 : R.N j (R.star k) (R.star i) = R.N (R.star j) (R.star i) (R.star k) := by
    exact R.N_star_transpose j (R.star k) (R.star i)
  linarith [step1, step2]

/-- Bundle a `FusionRing` into a `MultifusionRingDef`: take `I₀ = {R.unit}` and propagate
the multiplication, duality, and associativity data. -/
def toMultifusionRingDef : MultifusionRingDef ι where
  N := R.N
  I₀ := {R.unit}
  star := R.star
  star_star := R.star_star
  assoc := R.assoc
  sum_I₀_mul_left := by
    intro j k; simp only [Finset.sum_singleton]; exact R.unit_mul j k
  sum_I₀_mul_right := by
    intro i k; simp only [Finset.sum_singleton]; exact R.mul_unit i k
  duality_trace := R.duality_trace_singleton
  star_anti := R.star_anti_involution

/-- The `MultifusionRingDef` arising from a `FusionRing` is a fusion ring, witnessed by the
unit basis element. -/
theorem toMultifusionRingDef_isFusionRing : R.toMultifusionRingDef.IsFusionRing :=
  ⟨R.unit, rfl⟩

end FusionRing

/-- Proposition 1.42.4 in the fusion case: if `C` is a fusion category (semisimple rigid
abelian monoidal `k`-linear category with finitely many simples), then its Grothendieck
ring `Gr(C)` is a fusion ring. -/
theorem Proposition_1_42_4_fusion
    {κ : Type*} [Field κ] {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Preadditive C] [CategoryTheory.Linear κ C]
    [CategoryTheory.Abelian C]
    [CategoryTheory.MonoidalCategory C]
    [CategoryTheory.MonoidalPreadditive C]
    [CategoryTheory.MonoidalLinear κ C]
    [CategoryTheory.RigidCategory C]
    [cfd : CategoricalFusionData κ C] :

    ∃ (B : MultifusionRingDef cfd.ι),

      B.N = cfd.N ∧

      B.I₀ = {cfd.unitIdx} ∧

      B.star = cfd.star ∧

      B.IsFusionRing :=
  ⟨(CategoricalFusionData.toFusionRing).toMultifusionRingDef,
   rfl, rfl, rfl,
   (CategoricalFusionData.toFusionRing).toMultifusionRingDef_isFusionRing⟩

/-- Proposition 1.42.4 (based ring portion): the Grothendieck ring of a semisimple
multitensor category with the prescribed data is a based ring. -/
theorem Proposition_1_42_4_based
    {κ : Type*} [Field κ] {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Preadditive C] [CategoryTheory.Linear κ C]
    [CategoryTheory.Abelian C]
    [CategoryTheory.MonoidalCategory C]
    [CategoryTheory.MonoidalPreadditive C]
    [CategoryTheory.MonoidalLinear κ C]
    [CategoryTheory.RigidCategory C]
    [cfd : CategoricalFusionData κ C] :
    ∃ (B : MultifusionRingDef cfd.ι),
      B.N = cfd.N ∧ B.star = cfd.star :=
  ⟨(CategoricalFusionData.toFusionRing).toMultifusionRingDef, rfl, rfl⟩

/-- Proposition 1.42.4 (unital portion): for a semisimple tensor category, the
Grothendieck ring is a unital based ring. -/
theorem Proposition_1_42_4_unital
    {κ : Type*} [Field κ] {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Preadditive C] [CategoryTheory.Linear κ C]
    [CategoryTheory.Abelian C]
    [CategoryTheory.MonoidalCategory C]
    [CategoryTheory.MonoidalPreadditive C]
    [CategoryTheory.MonoidalLinear κ C]
    [CategoryTheory.RigidCategory C]
    [cfd : CategoricalFusionData κ C] :
    ∃ (B : MultifusionRingDef cfd.ι),
      B.N = cfd.N ∧ B.star = cfd.star ∧

      ∃ u : cfd.ι, B.I₀ = {u} :=
  ⟨(CategoricalFusionData.toFusionRing).toMultifusionRingDef,
   rfl, rfl, (CategoricalFusionData.toFusionRing).toMultifusionRingDef_isFusionRing⟩

namespace FusionRing

/-- The group ring `ℤ[G]` of a finite group `G`, regarded as a fusion ring with basis
indexed by `G`: the structure constants encode multiplication in `G` and the duality
involution is inversion. -/
def groupRingFusionRing (G : Type*) [DecidableEq G] [Fintype G] [Group G] :
    FusionRing G where
  unit := 1
  N g h k := if g * h = k then 1 else 0
  star := fun g => g⁻¹
  star_star := by intro g; simp
  unit_mul := by intro j k; simp
  mul_unit := by intro i k; simp
  duality := by
    intro i j
    show (if i * j = 1 then 1 else 0) = (if j = i⁻¹ then 1 else 0)
    congr 1
    exact propext ⟨fun h => by rw [mul_eq_one_iff_eq_inv] at h; rw [h]; simp,
      fun h => by rw [h, mul_inv_cancel]⟩
  assoc := by
    intro i j k l
    have lhs_eq : (∑ m : G, (if i * j = m then 1 else 0) * (if m * k = l then 1 else 0)) =
        if i * j * k = l then 1 else 0 := by
      simp_rw [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have rhs_eq : (∑ m : G, (if j * k = m then 1 else 0) * (if i * m = l then 1 else 0)) =
        if i * (j * k) = l then 1 else 0 := by
      simp_rw [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [lhs_eq, rhs_eq, mul_assoc]
  N_star_transpose := by
    intro i j k
    show (if i * j = k then 1 else 0) = (if i⁻¹ * k = j then 1 else 0)
    congr 1
    exact propext ⟨fun h => by rw [← h]; group,
      fun h => by rw [← h]; group⟩

/-- The group ring fusion ring is, in particular, a fusion ring (its unit basis element is
the identity of `G`). -/
theorem groupRingFusionRing_isFusionRing (G : Type*) [DecidableEq G] [Fintype G] [Group G] :
    (groupRingFusionRing G).toMultifusionRingDef.IsFusionRing :=
  (groupRingFusionRing G).toMultifusionRingDef_isFusionRing

end FusionRing

/-- An isomorphism of fusion rings: a bijection of bases compatible with the unit element,
the structure constants, and the duality involution. -/
structure FusionRingIso
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    (R : FusionRing ι) (S : FusionRing κ) where
  toEquiv : ι ≃ κ
  map_unit : toEquiv R.unit = S.unit
  map_N : ∀ i j k, R.N i j k = S.N (toEquiv i) (toEquiv j) (toEquiv k)
  map_star : ∀ i, toEquiv (R.star i) = S.star (toEquiv i)

/-- A categorification of a fusion ring `R` over a field `k`: a `k`-linear abelian rigid
monoidal category `C` together with an isomorphism between its Grothendieck fusion ring
and `R`. -/
structure Categorification.{u, v}
    {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)
    (k : Type*) [Field k] where
  C : Type u
  [cat : CategoryTheory.Category.{v} C]
  [preadditive : CategoryTheory.Preadditive C]
  [linear : CategoryTheory.Linear k C]
  [abelian : CategoryTheory.Abelian C]
  [monoidal : CategoryTheory.MonoidalCategory C]
  [monoidalPreadditive : CategoryTheory.MonoidalPreadditive C]
  [monoidalLinear : CategoryTheory.MonoidalLinear k C]
  [rigid : CategoryTheory.RigidCategory C]
  cfd : @CategoricalFusionData k _ C cat preadditive linear abelian monoidal
    monoidalPreadditive monoidalLinear rigid
  grIso : FusionRingIso (@CategoricalFusionData.toFusionRing k _ C cat preadditive
    linear abelian monoidal monoidalPreadditive monoidalLinear rigid cfd) R

/-- Two normalized 3-cocycles `ω₁, ω₂ : G × G × G → A` are cohomologous if they differ by
the coboundary of some 2-cochain `f : G × G → A`. -/
def CocycleCohomologous {G : Type*} [Group G] {A : Type*} [CommGroup A]
    (ω₁ ω₂ : NormalizedGroupCocycle3 G A) : Prop :=
  ∃ f : G → G → A,
    ∀ a b c, ω₂.toFun a b c =
      ω₁.toFun a b c * (f b c * (f (a * b) c)⁻¹ * f a (b * c) * (f a b)⁻¹)

/-- Cohomology of 3-cocycles is reflexive (taking the trivial 2-cochain). -/
theorem cocycleCohomologous_refl {G : Type*} [Group G] {A : Type*} [CommGroup A]
    (ω : NormalizedGroupCocycle3 G A) : CocycleCohomologous ω ω :=
  ⟨fun _ _ => 1, fun _ _ _ => by simp⟩

/-- Cohomology of 3-cocycles is symmetric: invert the 2-cochain witnessing equivalence. -/
theorem cocycleCohomologous_symm {G : Type*} [Group G] {A : Type*} [CommGroup A]
    {ω₁ ω₂ : NormalizedGroupCocycle3 G A}
    (h : CocycleCohomologous ω₁ ω₂) : CocycleCohomologous ω₂ ω₁ := by
  obtain ⟨f, hf⟩ := h
  refine ⟨fun g h => (f g h)⁻¹, fun a b c => ?_⟩
  have h1 := hf a b c
  rw [h1, inv_inv, inv_inv]
  suffices hsuff : ∀ (x a1 a2 a3 a4 : A),
      x * (a1 * a2⁻¹ * a3 * a4⁻¹) * (a1⁻¹ * a2 * a3⁻¹ * a4) = x by
    exact (hsuff _ _ _ _ _).symm
  intro x a1 a2 a3 a4
  calc x * (a1 * a2⁻¹ * a3 * a4⁻¹) * (a1⁻¹ * a2 * a3⁻¹ * a4)
      = x * ((a1 * a1⁻¹) * (a2⁻¹ * a2) * (a3 * a3⁻¹) * (a4⁻¹ * a4)) := by
        simp only [mul_comm, mul_left_comm, mul_assoc]
    _ = x := by simp

/-- Cohomology of 3-cocycles is transitive: compose the witnessing 2-cochains by
multiplying pointwise. -/
theorem cocycleCohomologous_trans {G : Type*} [Group G] {A : Type*} [CommGroup A]
    {ω₁ ω₂ ω₃ : NormalizedGroupCocycle3 G A}
    (h₁₂ : CocycleCohomologous ω₁ ω₂) (h₂₃ : CocycleCohomologous ω₂ ω₃) :
    CocycleCohomologous ω₁ ω₃ := by
  obtain ⟨f, hf⟩ := h₁₂
  obtain ⟨g, hg⟩ := h₂₃
  refine ⟨fun x y => f x y * g x y, fun a b c => ?_⟩
  rw [hg a b c, hf a b c]
  simp only [mul_inv_rev]
  simp only [mul_comm, mul_left_comm, mul_assoc]

/-- The setoid on normalized 3-cocycles induced by cohomology equivalence. -/
instance cocycleCohomologousSetoid (G : Type*) [Group G] (A : Type*) [CommGroup A] :
    Setoid (NormalizedGroupCocycle3 G A) where
  r := CocycleCohomologous
  iseqv := ⟨cocycleCohomologous_refl,
            fun h => cocycleCohomologous_symm h,
            fun h₁ h₂ => cocycleCohomologous_trans h₁ h₂⟩

/-- The third group cohomology `H³(G, A)`, realized as the quotient of normalized 3-cocycles
by the cohomology equivalence relation. -/
def GroupCohomologyH3 (G : Type*) [Group G] (A : Type*) [CommGroup A] :=
  Quotient (cocycleCohomologousSetoid G A)

/-- The inner automorphism of `G` associated to an element `g`, given by conjugation
`x ↦ g x g⁻¹`. -/
def innerAut {G : Type*} [Group G] (g : G) : G ≃* G where
  toFun x := g * x * g⁻¹
  invFun x := g⁻¹ * x * g
  left_inv x := by group
  right_inv x := by group
  map_mul' x y := by group

/-- The subgroup of inner automorphisms of `G` inside `MulAut G`. -/
def InnerAutSubgroup (G : Type*) [Group G] : Subgroup (MulAut G) where
  carrier := { φ | ∃ g : G, φ = innerAut g }
  one_mem' := ⟨1, by ext x; simp [innerAut]⟩
  mul_mem' := by
    rintro φ ψ ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by ext x; simp [innerAut]; group⟩
  inv_mem' := by
    rintro φ ⟨g, rfl⟩
    exact ⟨g⁻¹, by ext x; simp [innerAut]⟩

/-- The inner automorphism subgroup is normal in `MulAut G`. -/
instance innerAutNormal (G : Type*) [Group G] : (InnerAutSubgroup G).Normal where
  conj_mem := by
    rintro φ ⟨g, rfl⟩ ψ
    refine ⟨ψ g, ?_⟩
    ext x
    simp only [innerAut, MulEquiv.coe_mk, Equiv.coe_fn_mk, MulAut.mul_apply]
    simp only [map_mul, map_inv, MulAut.apply_inv_self]

/-- The group of outer automorphisms `Out(G) = MulAut G / Inn(G)`. -/
def OuterAut (G : Type*) [Group G] := MulAut G ⧸ InnerAutSubgroup G

/-- Pullback of a normalized 3-cocycle along a group automorphism `φ : G ≃* G`. -/
def cocyclePullback {G : Type*} [Group G] {A : Type*} [CommGroup A]
    (φ : G ≃* G) (ω : NormalizedGroupCocycle3 G A) : NormalizedGroupCocycle3 G A where
  toFun a b c := ω.toFun (φ a) (φ b) (φ c)
  cocycle_cond g₁ g₂ g₃ g₄ := by
    simp only [map_mul]; exact ω.cocycle_cond (φ g₁) (φ g₂) (φ g₃) (φ g₄)
  normalized g h := by
    simp only [map_one]; exact ω.normalized (φ g) (φ h)

/-- Two normalized 3-cocycles are equivalent under the joint action of `MulAut G` and the
group of coboundaries (i.e. they have the same orbit in `H³(G, A)/Out(G)`). -/
def CocycleOutOrbitEquiv {G : Type*} [Group G] {A : Type*} [CommGroup A]
    (ω₁ ω₂ : NormalizedGroupCocycle3 G A) : Prop :=
  ∃ (φ : G ≃* G), CocycleCohomologous (cocyclePullback φ ω₁) ω₂

/-- Proposition 1.42.9 (one direction): for any 3-cocycle `ω`, the category `Vec_G^ω`
is a categorification of `ℤ[G]`, with tensor product, unit, and dual computed in the
group `G` (multiplication, identity, inversion). -/
theorem Proposition_1_42_9_VecGomega_is_categorification
    (G : Type*) [DecidableEq G] [Fintype G] [Group G]
    (k : Type*) [Field k]
    (ω : NormalizedGroupCocycle3 G kˣ) :


    (∀ g h : G,
      (CG.tensorObj' (⟨g⟩ : CG G kˣ ω) (⟨h⟩ : CG G kˣ ω)).val = g * h) ∧

    (CG.unit' : CG G kˣ ω).val = (1 : G) ∧

    (∀ g : G, (CG.dualObj (⟨g⟩ : CG G kˣ ω)).val =
      (FusionRing.groupRingFusionRing G).star g) := by
  exact ⟨fun g h => rfl, rfl, fun g => rfl⟩

/-- Proposition 1.42.9 (other direction): every categorification of the group ring `ℤ[G]`
of a finite group `G` over a field `k` is monoidally equivalent to `Vec_G^ω` for some
3-cocycle `ω : G × G × G → k^×`. -/
theorem Proposition_1_42_9_categorifications_are_VecGomega
    (G : Type*) [DecidableEq G] [Fintype G] [Group G]
    (k : Type*) [Field k]
    (categ : Categorification (FusionRing.groupRingFusionRing G) k) :
    ∃ (ω : NormalizedGroupCocycle3 G kˣ),
      Nonempty (@MonoidalEquiv categ.C categ.cat categ.monoidal (CG G kˣ ω) _ inferInstance) := by
  sorry

/-- Proposition 1.42.9 (parametrization): two 3-cocycles `ω₁, ω₂` give monoidally equivalent
categorifications `Vec_G^{ω₁} ≃ Vec_G^{ω₂}` iff their classes coincide in
`H³(G, k^×)/Out(G)`. -/
theorem Proposition_1_42_9_parametrization
    (G : Type*) [DecidableEq G] [Fintype G] [Group G]
    (k : Type*) [Field k]
    (ω₁ ω₂ : NormalizedGroupCocycle3 G kˣ) :
    CocycleOutOrbitEquiv ω₁ ω₂ ↔
      Nonempty (MonoidalEquiv (CG G kˣ ω₁) (CG G kˣ ω₂)) := by
  sorry

/-- Definition 1.42.2(1): a based ring, formalized as `BasedRingDef`. -/
abbrev def_1_42_2_based_ring := @BasedRingDef

/-- Definition 1.42.2(2): a unital `ℤ₊`-ring, formalized as the `IsUnital` predicate on
`ZPlusRingDef`. -/
abbrev def_1_42_2_unital_zplus_ring := @ZPlusRingDef.IsUnital

/-- Definition 1.42.2(3): a multifusion ring (a based ring of finite rank), formalized as
`MultifusionRingDef`. -/
abbrev def_1_42_2_multifusion_ring := @MultifusionRingDef

/-- Definition 1.42.2(4): a fusion ring (a unital multifusion ring), formalized as the
`IsFusionRing` predicate on `MultifusionRingDef`. -/
abbrev def_1_42_2_fusion_ring := @MultifusionRingDef.IsFusionRing
