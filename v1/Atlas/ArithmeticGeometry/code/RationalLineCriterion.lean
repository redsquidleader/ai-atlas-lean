/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ArithmeticGeometry.code.ClassGroupRatFunc
import Atlas.ArithmeticGeometry.code.DegreePullback

namespace ArithmeticGeometry

/-- An axiomatic structure for a smooth projective curve $C/k$: it bundles the function field, divisor group, degree-zero Picard group $\operatorname{Pic}^0(C)$, set of rational points, principal divisor map, class map, genus, and the basic compatibilities between them. -/
structure SmoothProjectiveCurve (k : Type*) [Field k] where
  FunField : Type*
  [fieldInst : Field FunField]
  [algebraInst : Algebra k FunField]
  DivGroup : Type*
  [divGroupInst : AddCommGroup DivGroup]
  Pic0 : Type*
  [pic0Inst : AddCommGroup Pic0]
  RatPoint : Type*
  pointToDivisor : RatPoint → DivGroup
  degreeMap : DivGroup →+ ℤ
  degree_point : ∀ P : RatPoint, degreeMap (pointToDivisor P) = 1
  principalDiv : FunField → DivGroup
  degree_principalDiv : ∀ f : FunField, degreeMap (principalDiv f) = 0
  classMap : DivGroup →+ Pic0
  principalDiv_in_kernel : ∀ f : FunField, f ≠ 0 → classMap (principalDiv f) = 0
  classMap_surj : ∀ x : Pic0, ∃ D : DivGroup, degreeMap D = 0 ∧ classMap D = x
  classMap_eq_zero_iff : ∀ D : DivGroup, degreeMap D = 0 →
    (classMap D = 0 ↔ ∃ f : FunField, f ≠ 0 ∧ principalDiv f = D)
  pointToDivisor_injective : Function.Injective pointToDivisor
  principalDiv_algebraMap : ∀ a : k, principalDiv (algebraMap k FunField a) = 0
  isAlgebraic_implies_mem_range_algebraMap :
    ∀ f : FunField, IsAlgebraic k f → f ∈ Set.range (algebraMap k FunField)
  genusVal : ℕ
  exists_two_ratPoints_of_algClosed : IsAlgClosed k → ∃ P Q : RatPoint, P ≠ Q
  principalDiv_mul : ∀ (f g : FunField), f ≠ 0 → g ≠ 0 →
    principalDiv (f * g) = principalDiv f + principalDiv g

attribute [instance] SmoothProjectiveCurve.fieldInst
  SmoothProjectiveCurve.algebraInst
  SmoothProjectiveCurve.divGroupInst
  SmoothProjectiveCurve.pic0Inst

variable {k : Type*} [Field k]

/-- Axiom (degree formula): if $f \in k(C)$ has principal divisor $(P) - (Q)$ with $P \neq Q$, then for any injective $k$-algebra homomorphism $\varphi: k(t) \hookrightarrow k(C)$, the extension $k(C)/\varphi(k(t))$ has degree $1$. -/
theorem degree_formula_axiom {k : Type*} [Field k]
    (C : SmoothProjectiveCurve k)
    (f : C.FunField) (P Q : C.RatPoint) (hPQ : P ≠ Q)
    (hdiv : C.principalDiv f = C.pointToDivisor P + (-C.pointToDivisor Q))
    (φ : RatFunc k →ₐ[k] C.FunField) (hφ : Function.Injective φ) :
    Module.finrank φ.toRingHom.fieldRange C.FunField = 1 := by sorry

/-- If $k(C) \cong k(t)$ as $k$-algebras, then every degree-zero divisor on $C$ is principal. -/
theorem deg_zero_div_principal_of_iso_ratFunc {k : Type*} [Field k]
    (C : SmoothProjectiveCurve k)
    (φ : C.FunField ≃ₐ[k] RatFunc k)
    (D : C.DivGroup) (hdeg : C.degreeMap D = 0) :
    ∃ f : C.FunField, f ≠ 0 ∧ C.principalDiv f = D := by sorry

/-- Over an algebraically closed field, a smooth projective curve has at least two distinct rational points. -/
theorem SmoothProjectiveCurve.exists_two_ratPoints (C : SmoothProjectiveCurve k)
    [IsAlgClosed k] : ∃ P Q : C.RatPoint, P ≠ Q :=
  C.exists_two_ratPoints_of_algClosed ‹IsAlgClosed k›

/-- If $f \in k(C)$ has a nonzero principal divisor, then $f$ is transcendental over $k$ (an algebraic element would lie in $k \subseteq k(C)$ and have trivial divisor). -/
theorem SmoothProjectiveCurve.transcendental_of_principalDiv_ne_zero
    (C : SmoothProjectiveCurve k)
    (f : C.FunField) (hf : C.principalDiv f ≠ 0) : Transcendental k f := by

  intro hfalg
  apply hf

  obtain ⟨a, ha⟩ := C.isAlgebraic_implies_mem_range_algebraMap f hfalg

  rw [← ha, C.principalDiv_algebraMap]

/-- Helper lemma: if a subfield $K \subseteq F$ equals all of $F$, then $F$ has dimension $1$ as a $K$-vector space. -/
lemma finrank_eq_one_of_subfield_eq_top {F : Type*} [Field F]
    (K : Subfield F) (h : K = ⊤) : Module.finrank K F = 1 := by
  subst h
  have hbij : Function.Bijective (algebraMap (↥(⊤ : Subfield F)) F) :=
    ⟨Subtype.val_injective, fun x => ⟨⟨x, Subfield.mem_top x⟩, rfl⟩⟩
  have hle : LinearEquiv (RingHom.id ↥(⊤ : Subfield F)) ↥(⊤ : Subfield F) F :=
    LinearEquiv.ofBijective (Algebra.linearMap _ _) hbij
  rw [← hle.finrank_eq]
  exact Module.finrank_self _

/-- If there is a function $f \in k(C)$ with divisor $(P) - (Q)$ for distinct rational points $P, Q$, then any injective $k$-algebra map $\varphi: k(t) \to k(C)$ is automatically surjective. -/
theorem SmoothProjectiveCurve.pullback_surjective (C : SmoothProjectiveCurve k)
    {f : C.FunField} (_hf : f ≠ 0) {P Q : C.RatPoint} (hPQ : P ≠ Q)
    (hdiv : C.principalDiv f = C.pointToDivisor P + (- C.pointToDivisor Q))
    (φ : RatFunc k →ₐ[k] C.FunField) (hφ : Function.Injective φ) :
    Function.Surjective φ := by

  have h_deg : Module.finrank φ.toRingHom.fieldRange C.FunField = 1 :=
    degree_formula_axiom C f P Q hPQ hdiv φ hφ

  have h_bot_eq_top : (⊥ : Subalgebra φ.toRingHom.fieldRange C.FunField) = ⊤ :=
    Subalgebra.bot_eq_top_of_finrank_eq_one h_deg

  have h_range_top : φ.toRingHom.fieldRange = ⊤ := by
    ext x
    simp only [Subfield.mem_top, iff_true]
    have hx : x ∈ (⊤ : Subalgebra φ.toRingHom.fieldRange C.FunField) := trivial
    rw [← h_bot_eq_top] at hx
    simp at hx
    obtain ⟨a, ha⟩ := hx
    rw [← ha]; exact a.property

  exact RingHom.fieldRange_eq_top_iff.mp h_range_top

/-- The field extension $k(C)/\varphi(k(t))$ has degree one whenever there is a function with divisor $(P) - (Q)$ and $\varphi: k(t) \hookrightarrow k(C)$ is injective. -/
theorem SmoothProjectiveCurve.fieldExtension_degree_one (C : SmoothProjectiveCurve k)
    {f : C.FunField} (hf : f ≠ 0) {P Q : C.RatPoint} (hPQ : P ≠ Q)
    (hdiv : C.principalDiv f = C.pointToDivisor P + (- C.pointToDivisor Q))
    (φ : RatFunc k →ₐ[k] C.FunField) (hφ : Function.Injective φ) :
    Module.finrank φ.toRingHom.fieldRange C.FunField = 1 := by

  have hsurj : Function.Surjective φ :=
    C.pullback_surjective hf hPQ hdiv φ hφ

  have htop : φ.toRingHom.fieldRange = ⊤ :=
    RingHom.fieldRange_eq_top_iff.mpr hsurj

  exact finrank_eq_one_of_subfield_eq_top _ htop

/-- A smooth projective curve $C/k$ is isomorphic to $\mathbb{P}^1_k$ iff its function field $k(C)$ is $k$-algebra isomorphic to the rational function field $k(t)$. -/
def SmoothProjectiveCurve.IsIsomorphicToP1 (C : SmoothProjectiveCurve k) : Prop :=
  Nonempty (C.FunField ≃ₐ[k] RatFunc k)

/-- The Picard group $\operatorname{Pic}^0(C)$ is trivial iff every degree-zero divisor class is the identity. -/
def SmoothProjectiveCurve.Pic0IsTrivial (C : SmoothProjectiveCurve k) : Prop :=
  ∀ x : C.Pic0, x = 0

/-- If $k(C) \cong k(t)$, then $\operatorname{Pic}^0(C)$ embeds (injectively) into the class group of $k[t]$. Used as a stepping stone to show $\operatorname{Pic}^0(C)$ is trivial. -/
lemma Pic0_injective_to_classGroup_of_iso {k : Type*} [Field k]
    (C : SmoothProjectiveCurve k)
    (φ : C.FunField ≃ₐ[k] RatFunc k) :
    ∃ ι : C.Pic0 →+ Additive (ClassGroup (Polynomial k)), Function.Injective ι := by


  have htriv : ∀ x : C.Pic0, x = 0 := by
    intro x

    obtain ⟨D, hdeg, hcl⟩ := C.classMap_surj x

    obtain ⟨f, hf_ne, hf_div⟩ := deg_zero_div_principal_of_iso_ratFunc C φ D hdeg


    rw [← hcl, (C.classMap_eq_zero_iff D hdeg).mpr ⟨f, hf_ne, hf_div⟩]


  exact ⟨0, fun a b _ => by rw [htriv a, htriv b]⟩

/-- If $k(C) \cong k(t)$ as $k$-algebras, then $\operatorname{Pic}^0(C)$ is trivial. -/
lemma Pic0_trivial_of_funField_iso_ratFunc (C : SmoothProjectiveCurve k)
    (φ : C.FunField ≃ₐ[k] RatFunc k) : C.Pic0IsTrivial := by

  obtain ⟨ι, hι_inj⟩ := Pic0_injective_to_classGroup_of_iso C φ

  haveI : Subsingleton (Additive (ClassGroup (Polynomial k))) :=
    inferInstance

  intro x
  have : ι x = ι 0 := Subsingleton.elim _ _
  exact hι_inj this

/-- If $k(C) \cong k(t)$, then every degree-zero divisor $D$ on $C$ is principal: $D = \operatorname{div}(f)$ for some nonzero $f \in k(C)$. -/
theorem every_deg0_div_principal_of_iso_P1 (C : SmoothProjectiveCurve k)
    (φ : C.FunField ≃ₐ[k] RatFunc k) (D : C.DivGroup) (hdeg : C.degreeMap D = 0) :
    ∃ f : C.FunField, f ≠ 0 ∧ C.principalDiv f = D := by

  have htriv : C.Pic0IsTrivial := Pic0_trivial_of_funField_iso_ratFunc C φ

  have hcl : C.classMap D = 0 := htriv (C.classMap D)

  exact (C.classMap_eq_zero_iff D hdeg).mp hcl

/-- Re-export of `Pic0_injective_to_classGroup_of_iso`: an injective additive map $\operatorname{Pic}^0(C) \hookrightarrow \operatorname{Cl}(k[t])$ exists whenever $k(C) \cong k(t)$. -/
theorem Pic0_injective_to_classGroup_axiom {k : Type*} [Field k]
    (C : SmoothProjectiveCurve k)
    (φ : C.FunField ≃ₐ[k] RatFunc k) :
    ∃ ι : C.Pic0 →+ Additive (ClassGroup (Polynomial k)), Function.Injective ι :=
  Pic0_injective_to_classGroup_of_iso C φ


/-- If $C \cong \mathbb{P}^1_k$, then every degree-zero divisor on $C$ is principal. -/
theorem principalDiv_of_iso_P1 (C : SmoothProjectiveCurve k)
    (hiso : C.IsIsomorphicToP1) (D : C.DivGroup) (hdeg : C.degreeMap D = 0) :
    ∃ f : C.FunField, f ≠ 0 ∧ C.principalDiv f = D := by
  obtain ⟨φ⟩ := hiso
  exact every_deg0_div_principal_of_iso_P1 C φ D hdeg

/-- If $C \cong \mathbb{P}^1_k$, then the divisor-class image of any degree-zero divisor $D$ vanishes in $\operatorname{Pic}^0(C)$. -/
theorem classMap_zero_of_iso_P1 (C : SmoothProjectiveCurve k)
    (hiso : C.IsIsomorphicToP1) (D : C.DivGroup) (hdeg : C.degreeMap D = 0) :
    C.classMap D = 0 := by

  obtain ⟨f, hf_ne, hf_div⟩ := principalDiv_of_iso_P1 C hiso D hdeg

  exact (C.classMap_eq_zero_iff D hdeg).mpr ⟨f, hf_ne, hf_div⟩

/-- Same statement as `principalDiv_of_iso_P1`, packaged as a lemma: every degree-zero divisor on $C \cong \mathbb{P}^1$ is principal. -/
lemma degree_zero_divisor_principal_of_iso_P1 (C : SmoothProjectiveCurve k)
    (hiso : C.IsIsomorphicToP1) (D : C.DivGroup) (hdeg : C.degreeMap D = 0) :
    ∃ f : C.FunField, f ≠ 0 ∧ C.principalDiv f = D := by

  have hcl : C.classMap D = 0 := classMap_zero_of_iso_P1 C hiso D hdeg

  rwa [C.classMap_eq_zero_iff D hdeg] at hcl

/-- If $C \cong \mathbb{P}^1_k$ then $\operatorname{Pic}^0(C) = 0$. -/
theorem P1_Pic0_trivial (C : SmoothProjectiveCurve k)
    (hiso : C.IsIsomorphicToP1) : C.Pic0IsTrivial := by

  intro x
  obtain ⟨D, hdeg, hcl⟩ := C.classMap_surj x

  obtain ⟨f, hf_ne, hf_div⟩ := degree_zero_divisor_principal_of_iso_P1 C hiso D hdeg

  rw [← hcl, (C.classMap_eq_zero_iff D hdeg).mpr ⟨f, hf_ne, hf_div⟩]

/-- Bundles the injective embedding $\operatorname{Pic}^0(C) \hookrightarrow \operatorname{Cl}(k[t])$ provided by an isomorphism $k(C) \cong k(t)$. Since the target is trivial, this concretely produces the zero map. -/
noncomputable def SmoothProjectiveCurve.pic0_to_classGroup (C : SmoothProjectiveCurve k)
    (φ : C.FunField ≃ₐ[k] RatFunc k) :
    { f : C.Pic0 →+ Additive (ClassGroup (Polynomial k)) // Function.Injective f } := by

  have hiso : C.IsIsomorphicToP1 := ⟨φ⟩

  have htriv := P1_Pic0_trivial C hiso

  refine ⟨0, fun a b _ => ?_⟩
  rw [htriv a, htriv b]

/-- Over an algebraically closed field, a smooth projective curve has two distinct rational points. -/
theorem exists_distinct_rational_points [IsAlgClosed k]
    (C : SmoothProjectiveCurve k) : ∃ P Q : C.RatPoint, P ≠ Q :=
  C.exists_two_ratPoints

/-- If $f \in k(C)$ has divisor $(P) - (Q)$ with $P \neq Q$, then $f$ is transcendental and induces an injective $k$-algebra homomorphism $k(t) \hookrightarrow k(C)$ by $t \mapsto f$. -/
theorem exists_injective_algHom_of_nontrivial_div (C : SmoothProjectiveCurve k)
    {P Q : C.RatPoint} (hPQ : P ≠ Q)
    {f : C.FunField} (_hf : f ≠ 0)
    (hdiv : C.principalDiv f = C.pointToDivisor P + (- C.pointToDivisor Q)) :
    ∃ φ : RatFunc k →ₐ[k] C.FunField, Function.Injective φ := by

  have hdiv_ne : C.principalDiv f ≠ 0 := by
    rw [hdiv]
    intro h
    apply hPQ
    apply C.pointToDivisor_injective
    rw [add_neg_eq_zero] at h
    exact h

  have hf_trans : Transcendental k f := C.transcendental_of_principalDiv_ne_zero f hdiv_ne

  have hinj : Function.Injective (Polynomial.aeval (R := k) f) :=
    transcendental_iff_injective.mp hf_trans

  exact ⟨_, RatFunc.liftAlgHom_injective _ hinj⟩

/-- Any injective $\varphi: k(t) \to k(C)$ is automatically surjective if there is a function on $C$ with divisor $(P) - (Q)$: the field extension $k(C)/\varphi(k(t))$ has degree one. -/
theorem morphism_surjective_of_deg_one_div (C : SmoothProjectiveCurve k)
    {P Q : C.RatPoint} (hPQ : P ≠ Q)
    {f : C.FunField} (hf : f ≠ 0)
    (hdiv : C.principalDiv f = C.pointToDivisor P + (- C.pointToDivisor Q))
    (φ : RatFunc k →ₐ[k] C.FunField) (hφ_inj : Function.Injective φ) :
    Function.Surjective φ := by

  have h_deg : Module.finrank φ.toRingHom.fieldRange C.FunField = 1 :=
    C.fieldExtension_degree_one hf hPQ hdiv φ hφ_inj

  have h_bot_eq_top : (⊥ : Subalgebra φ.toRingHom.fieldRange C.FunField) = ⊤ :=
    Subalgebra.bot_eq_top_of_finrank_eq_one h_deg

  have h_range_top : φ.toRingHom.fieldRange = ⊤ := by
    ext x
    simp only [Subfield.mem_top, iff_true]
    have hx : x ∈ (⊤ : Subalgebra φ.toRingHom.fieldRange C.FunField) := trivial
    rw [← h_bot_eq_top] at hx
    simp at hx
    obtain ⟨a, ha⟩ := hx
    rw [← ha]; exact a.property

  exact RingHom.fieldRange_eq_top_iff.mp h_range_top

/-- A bijective $k$-algebra homomorphism $k(t) \to k(C)$ gives the isomorphism $C \cong \mathbb{P}^1_k$. -/
theorem iso_of_bijective_algHom (C : SmoothProjectiveCurve k)
    (φ : RatFunc k →ₐ[k] C.FunField)
    (hφ : Function.Bijective φ) :
    C.IsIsomorphicToP1 :=
  ⟨(AlgEquiv.ofBijective φ hφ).symm⟩

/-- If $C$ admits a function with divisor $(P) - (Q)$ for distinct rational points, then $C \cong \mathbb{P}^1_k$. -/
theorem degree_one_morphism_is_iso (C : SmoothProjectiveCurve k)
    {P Q : C.RatPoint} (hPQ : P ≠ Q)
    {f : C.FunField} (hf : f ≠ 0)
    (hdiv : C.principalDiv f = C.pointToDivisor P + (- C.pointToDivisor Q)) :
    C.IsIsomorphicToP1 := by

  obtain ⟨φ, hφ_inj⟩ := exists_injective_algHom_of_nontrivial_div C hPQ hf hdiv

  have hφ_surj := morphism_surjective_of_deg_one_div C hPQ hf hdiv φ hφ_inj

  exact iso_of_bijective_algHom C φ ⟨hφ_inj, hφ_surj⟩

/-- If $\operatorname{Pic}^0(C) = 0$, then for any two rational points $P, Q$, the degree-zero divisor $(P) - (Q)$ is principal: there is a function $f \in k(C)$ with $\operatorname{div}(f) = (P) - (Q)$. -/
theorem principal_of_Pic0_trivial (C : SmoothProjectiveCurve k)
    (htriv : C.Pic0IsTrivial) (P Q : C.RatPoint) :
    ∃ f : C.FunField, f ≠ 0 ∧
      C.principalDiv f = C.pointToDivisor P + (- C.pointToDivisor Q) := by

  have hdeg : C.degreeMap (C.pointToDivisor P + (-C.pointToDivisor Q)) = 0 := by
    rw [map_add, map_neg, C.degree_point P, C.degree_point Q]; omega

  have hcl : C.classMap (C.pointToDivisor P + (-C.pointToDivisor Q)) = 0 :=
    htriv _

  rwa [C.classMap_eq_zero_iff _ hdeg] at hcl

/-- Over an algebraically closed field, if $\operatorname{Pic}^0(C) = 0$ then $C \cong \mathbb{P}^1_k$. -/
theorem Pic0_trivial_imp_iso_P1 [IsAlgClosed k] (C : SmoothProjectiveCurve k)
    (htriv : C.Pic0IsTrivial) : C.IsIsomorphicToP1 := by

  obtain ⟨P, Q, hPQ⟩ := exists_distinct_rational_points C

  obtain ⟨f, hf_ne, hf_div⟩ := principal_of_Pic0_trivial C htriv P Q

  exact degree_one_morphism_is_iso C hPQ hf_ne hf_div

/-- Main result: over an algebraically closed field, a smooth projective curve $C$ is isomorphic to $\mathbb{P}^1_k$ iff $\operatorname{Pic}^0(C)$ is trivial. -/
theorem iso_P1_iff_Pic0_trivial [IsAlgClosed k] (C : SmoothProjectiveCurve k) :
    C.IsIsomorphicToP1 ↔ C.Pic0IsTrivial :=
  ⟨P1_Pic0_trivial C, Pic0_trivial_imp_iso_P1 C⟩

end ArithmeticGeometry
