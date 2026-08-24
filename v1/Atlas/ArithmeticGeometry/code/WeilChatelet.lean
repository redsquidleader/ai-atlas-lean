/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.Torsors
import Atlas.ArithmeticGeometry.code.EllipticCurves
import Atlas.ArithmeticGeometry.code.Divisors

noncomputable section

universe u

/-- Abstract predicate: the type `C_pts` represents the points of a smooth curve of arithmetic
genus 1 over $k$. The concrete content is deferred via `sorry`. -/
noncomputable def IsArithGenus1 (k : Type u) [Field k] (C_pts : Type u) : Prop := by sorry

/-- A *genus-one curve points type* over $k$: `C_pts` is nonempty after base change to the
algebraic closure, and is of arithmetic genus one. -/
class IsGenusOneCurvePoints (k : Type u) [Field k] (C_pts : Type u) : Prop where
  nonempty_over_closure : Nonempty C_pts
  genus_one : IsArithGenus1 k C_pts


/-- Abstract predicate: the action of $E$ on $C$ defining a torsor is realised by a $k$-rational
morphism of varieties. -/
noncomputable def IsKActionMorphism (k : Type u) [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddGroup E_pts]
    (C_pts : Type u) [AddTorsor E_pts C_pts] : Prop := by sorry

/-- Class wrapping the `IsKActionMorphism` predicate as an instance argument; required for the
torsor structure to define an "elliptic curve torsor over $k$". -/
class IsActionMorphismOverk (k : Type u) [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (C_pts : Type u) [AddTorsor E_pts C_pts] : Prop where
  action_is_k_morphism : IsKActionMorphism k W E_pts C_pts


/-- Build an `AddTorsor G P` from any bijection $e \colon P \simeq G$, by transporting the
addition: $g +_v p := e^{-1}(g + e(p))$. -/
@[reducible] def addTorsorOfEquiv (G : Type*) [AddGroup G] (P : Type*) [Nonempty P]
    (e : P ≃ G) : AddTorsor G P where
  vadd g p := e.symm (g + e p)
  zero_vadd p := by
    show e.symm (0 + e p) = p
    rw [zero_add, Equiv.symm_apply_apply]
  add_vadd g₁ g₂ p := by
    show e.symm ((g₁ + g₂) + e p) = e.symm (g₁ + e (e.symm (g₂ + e p)))
    rw [Equiv.apply_symm_apply, add_assoc]
  vsub p₁ p₂ := e p₁ - e p₂
  vsub_vadd' p₁ p₂ := by
    show e.symm (e p₁ - e p₂ + e p₂) = p₁
    rw [sub_add_cancel, Equiv.symm_apply_apply]
  vadd_vsub' g p := by
    show e (e.symm (g + e p)) - e p = g
    rw [Equiv.apply_symm_apply, add_sub_cancel_right]

/-- The transported torsor obtained from `addTorsorOfEquiv` is automatically a $k$-action
morphism. -/
theorem isKActionMorphism_of_equiv (k : Type u) [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (C_pts : Type u) [_hne : Nonempty C_pts]
    (φ : C_pts ≃ E_pts) :
    @IsKActionMorphism k _ W _ E_pts _ C_pts (addTorsorOfEquiv E_pts C_pts φ) := by sorry

/-- The torsor obtained from a bijection $\varphi \colon C \simeq E$ satisfies the
`IsActionMorphismOverk` axiom. -/
theorem IsActionMorphismOverk.ofEquiv (k : Type u) [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (C_pts : Type u) [hne : Nonempty C_pts]
    (φ : C_pts ≃ E_pts) :
    @IsActionMorphismOverk _ _ W _ E_pts _ C_pts (addTorsorOfEquiv E_pts C_pts φ) := by
  letI : AddTorsor E_pts C_pts := addTorsorOfEquiv E_pts C_pts φ
  exact ⟨isKActionMorphism_of_equiv k W E_pts C_pts φ⟩

/-- An *$E$-torsor over $k$*: the data of an `AddTorsor` structure of $E_{\mathrm{pts}}$ on
$C_{\mathrm{pts}}$, a witness that $C$ is a genus-one curve points type, and a witness that the
action is a $k$-rational morphism. -/
structure IsETorsor (k : Type u) [Field k] (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (C_pts : Type u) where
  toAddTorsor : AddTorsor E_pts C_pts
  genusOne : IsGenusOneCurvePoints k C_pts
  actionMorphism : haveI := toAddTorsor; IsActionMorphismOverk k W E_pts C_pts

variable {k : Type u} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {E_pts : Type u} [AddCommGroup E_pts] {C_pts : Type u}


/-- An $E$-torsor over $k$ is nonempty (since `AddTorsor` requires nonemptiness). -/
theorem IsETorsor.nonempty (h : IsETorsor k W E_pts C_pts) : Nonempty C_pts := by
  letI := h.toAddTorsor
  exact AddTorsor.nonempty

/-- Choosing a base point $c_0 \in C$ in an $E$-torsor produces an equivalence
$E \simeq C$ via $g \mapsto g +_v c_0$. -/
noncomputable def IsETorsor.equivOfBasePoint
    (h : IsETorsor k W E_pts C_pts) (c₀ : C_pts) : E_pts ≃ C_pts := by
  letI := h.toAddTorsor
  exact Equiv.vaddConst c₀

/-- An $E$-torsor (over $k$) is in particular a torsor in the abstract sense. -/
@[reducible] def IsETorsor.toIsTorsor (h : IsETorsor k W E_pts C_pts) :
    haveI := h.toAddTorsor; IsTorsor E_pts C_pts := by
  letI := h.toAddTorsor
  exact ⟨⟩

/-- A $k$-rational map between two curve point types, encoded as an inductive closure under
identity, symmetry, and composition. -/
inductive IsKRationalMap (k : Type u) [Field k] :
    (C₁_pts C₂_pts : Type u) → (C₁_pts ≃ C₂_pts) → Prop where
  | refl_equiv (C_pts : Type u) :
      IsKRationalMap k C_pts C_pts (Equiv.refl C_pts)
  | symm_equiv {C₁_pts C₂_pts : Type u} {e : C₁_pts ≃ C₂_pts} :
      IsKRationalMap k C₁_pts C₂_pts e → IsKRationalMap k C₂_pts C₁_pts e.symm
  | trans_equiv {C₁_pts C₂_pts C₃_pts : Type u}
      {e₁₂ : C₁_pts ≃ C₂_pts} {e₂₃ : C₂_pts ≃ C₃_pts} :
      IsKRationalMap k C₁_pts C₂_pts e₁₂ → IsKRationalMap k C₂_pts C₃_pts e₂₃ →
      IsKRationalMap k C₁_pts C₃_pts (e₁₂.trans e₂₃)

/-- A $k$-isomorphism of curve points: a bijection $e$ that is $k$-rational as a map of
algebraic varieties. -/
class IsKIsomorphism (k : Type u) [Field k]
    (C₁_pts C₂_pts : Type u) (e : C₁_pts ≃ C₂_pts) : Prop where
  is_k_rational : IsKRationalMap k C₁_pts C₂_pts e


/-- The identity map is $k$-rational. -/
theorem IsKRationalMap.refl (k : Type u) [Field k] (C_pts : Type u) :
    IsKRationalMap k C_pts C_pts (Equiv.refl C_pts) := .refl_equiv C_pts

/-- The inverse of a $k$-rational equivalence is $k$-rational. -/
theorem IsKRationalMap.symm {k : Type u} [Field k]
    {C₁_pts C₂_pts : Type u} {e : C₁_pts ≃ C₂_pts}
    (h : IsKRationalMap k C₁_pts C₂_pts e) :
    IsKRationalMap k C₂_pts C₁_pts e.symm := .symm_equiv h

/-- The composition of two $k$-rational equivalences is $k$-rational. -/
theorem IsKRationalMap.trans {k : Type u} [Field k]
    {C₁_pts C₂_pts C₃_pts : Type u}
    {e₁₂ : C₁_pts ≃ C₂_pts} {e₂₃ : C₂_pts ≃ C₃_pts}
    (h₁ : IsKRationalMap k C₁_pts C₂_pts e₁₂)
    (h₂ : IsKRationalMap k C₂_pts C₃_pts e₂₃) :
    IsKRationalMap k C₁_pts C₃_pts (e₁₂.trans e₂₃) := .trans_equiv h₁ h₂

/-- If two torsor base points $q_1, q_2$ are cohomologous as cocycles, then the torsor
translation map between the corresponding base-pointed presentations is $k$-rational. -/
theorem IsKRationalMap.of_torsor_translation_of_cohomologous {k : Type u} [Field k]
    {G : Type u} [AddGroup G] {P₁ P₂ : Type u}
    [inst₁ : AddTorsor G P₁] [inst₂ : AddTorsor G P₂]
    (q₁ : P₁) (q₂ : P₂)
    {CocyclesAreCohomologous : Prop}


    (_heq_cocycles : CocyclesAreCohomologous)
    : IsKRationalMap k P₁ P₂ ((Equiv.vaddConst q₁).symm.trans (Equiv.vaddConst q₂)) := by sorry

/-- The torsor-translation map associated to two cohomologous cocycles is a $k$-isomorphism. -/
theorem IsKIsomorphism.of_torsor_translation_of_cohomologous {k : Type u} [Field k]
    {G : Type u} [AddGroup G] {P₁ P₂ : Type u}
    [inst₁ : AddTorsor G P₁] [inst₂ : AddTorsor G P₂]
    (q₁ : P₁) (q₂ : P₂)
    {CocyclesAreCohomologous : Prop}
    (heq_cocycles : CocyclesAreCohomologous) :
    IsKIsomorphism k P₁ P₂ ((Equiv.vaddConst q₁).symm.trans (Equiv.vaddConst q₂)) :=
  ⟨IsKRationalMap.of_torsor_translation_of_cohomologous q₁ q₂ heq_cocycles⟩

/-- Reflexivity of $k$-isomorphism. -/
theorem IsKIsomorphism.refl (k : Type u) [Field k] (C_pts : Type u) :
    IsKIsomorphism k C_pts C_pts (Equiv.refl C_pts) :=
  ⟨IsKRationalMap.refl k C_pts⟩

/-- The inverse of a $k$-isomorphism is a $k$-isomorphism. -/
theorem IsKIsomorphism.symm {k : Type u} [Field k]
    {C₁_pts C₂_pts : Type u} {e : C₁_pts ≃ C₂_pts}
    (h : IsKIsomorphism k C₁_pts C₂_pts e) :
    IsKIsomorphism k C₂_pts C₁_pts e.symm :=
  ⟨h.is_k_rational.symm⟩

/-- The composition of two $k$-isomorphisms is a $k$-isomorphism. -/
theorem IsKIsomorphism.trans {k : Type u} [Field k]
    {C₁_pts C₂_pts C₃_pts : Type u}
    {e₁₂ : C₁_pts ≃ C₂_pts} {e₂₃ : C₂_pts ≃ C₃_pts}
    (h₁ : IsKIsomorphism k C₁_pts C₂_pts e₁₂)
    (h₂ : IsKIsomorphism k C₂_pts C₃_pts e₂₃) :
    IsKIsomorphism k C₁_pts C₃_pts (e₁₂.trans e₂₃) :=
  ⟨h₁.is_k_rational.trans h₂.is_k_rational⟩

/-- A bundled $E$-torsor: a points type `C_pts` together with an `IsETorsor` proof. -/
structure ETorsor (k : Type u) [Field k] (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts] where
  C_pts : Type u
  torsor : IsETorsor k W E_pts C_pts

namespace ETorsor

variable {k : Type u} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {E_pts : Type u} [AddCommGroup E_pts]

/-- Two $E$-torsors $T_1, T_2$ are *equivalent* if there is a $k$-isomorphism $C_{T_1} \simeq C_{T_2}$
that intertwines the $E$-actions: $e(p +_v q) = p +_v e(q)$. -/
def Equiv (T₁ T₂ : ETorsor k W E_pts) : Prop :=
  ∃ (e : T₁.C_pts ≃ T₂.C_pts),
    IsKIsomorphism k T₁.C_pts T₂.C_pts e ∧
    (haveI := T₁.torsor.toAddTorsor
     haveI := T₂.torsor.toAddTorsor
     ∀ (p : E_pts) (q : T₁.C_pts), e (p +ᵥ q) = p +ᵥ (e q))

/-- Reflexivity: every torsor is equivalent to itself via the identity. -/
theorem Equiv.rfl (T : ETorsor k W E_pts) : Equiv T T := by
  refine ⟨_root_.Equiv.refl T.C_pts, IsKIsomorphism.refl k T.C_pts, ?_⟩
  intro p q
  rfl

/-- Symmetry of torsor equivalence. -/
theorem Equiv.symm {T₁ T₂ : ETorsor k W E_pts} (h : Equiv T₁ T₂) :
    Equiv T₂ T₁ := by
  obtain ⟨e, hk, hcompat⟩ := h
  refine ⟨e.symm, hk.symm, ?_⟩
  letI := T₁.torsor.toAddTorsor
  letI := T₂.torsor.toAddTorsor
  intro p q
  have h1 := hcompat p (e.symm q)
  rw [_root_.Equiv.apply_symm_apply] at h1
  rw [← h1, _root_.Equiv.symm_apply_apply]

/-- Transitivity of torsor equivalence. -/
theorem Equiv.trans {T₁ T₂ T₃ : ETorsor k W E_pts}
    (h₁₂ : Equiv T₁ T₂) (h₂₃ : Equiv T₂ T₃) : Equiv T₁ T₃ := by
  obtain ⟨e₁₂, hk₁₂, hcompat₁₂⟩ := h₁₂
  obtain ⟨e₂₃, hk₂₃, hcompat₂₃⟩ := h₂₃
  refine ⟨e₁₂.trans e₂₃, hk₁₂.trans hk₂₃, ?_⟩
  letI := T₁.torsor.toAddTorsor
  letI := T₂.torsor.toAddTorsor
  letI := T₃.torsor.toAddTorsor
  intro p q
  simp only [_root_.Equiv.trans_apply]
  rw [hcompat₁₂, hcompat₂₃]

/-- The setoid on `ETorsor` whose equivalence relation is torsor equivalence. -/
instance setoid : Setoid (ETorsor k W E_pts) where
  r := Equiv
  iseqv := ⟨Equiv.rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- An $E$-action-preserving equivalence of torsors is automatically $-_v$-preserving:
$e(P) -_v e(Q) = P -_v Q$. -/
theorem Equiv.vsub_preserving {T₁ T₂ : ETorsor k W E_pts}
    (e : T₁.C_pts ≃ T₂.C_pts)
    (hcompat : haveI := T₁.torsor.toAddTorsor
               haveI := T₂.torsor.toAddTorsor
               ∀ (p : E_pts) (q : T₁.C_pts), e (p +ᵥ q) = p +ᵥ (e q))
    (P Q : T₁.C_pts) :
    haveI := T₁.torsor.toAddTorsor
    haveI := T₂.torsor.toAddTorsor
    e P -ᵥ e Q = (P -ᵥ Q : E_pts) := by
  letI := T₁.torsor.toAddTorsor
  letI := T₂.torsor.toAddTorsor
  have h := hcompat (P -ᵥ Q) Q
  rw [vsub_vadd] at h
  rw [h, vadd_vsub]

/-- Conversely, a $-_v$-preserving map of torsors is automatically $+_v$-compatible. -/
theorem Equiv.vadd_compat_of_vsub {T₁ T₂ : ETorsor k W E_pts}
    (e : T₁.C_pts ≃ T₂.C_pts)
    (hvsub : haveI := T₁.torsor.toAddTorsor
             haveI := T₂.torsor.toAddTorsor
             ∀ (P Q : T₁.C_pts), e P -ᵥ e Q = (P -ᵥ Q : E_pts))
    (p : E_pts) (q : T₁.C_pts) :
    haveI := T₁.torsor.toAddTorsor
    haveI := T₂.torsor.toAddTorsor
    e (p +ᵥ q) = p +ᵥ (e q) := by
  letI := T₁.torsor.toAddTorsor
  letI := T₂.torsor.toAddTorsor
  have h := hvsub (p +ᵥ q) q
  rw [vadd_vsub] at h
  rw [eq_vadd_iff_vsub_eq]
  exact h

/-- An equivalence of $E$-torsors is $+_v$-compatible iff it is $-_v$-preserving. -/
theorem equiv_iff_vsub_preserving {T₁ T₂ : ETorsor k W E_pts}
    (e : T₁.C_pts ≃ T₂.C_pts) :
    (haveI := T₁.torsor.toAddTorsor
     haveI := T₂.torsor.toAddTorsor
     ∀ (p : E_pts) (q : T₁.C_pts), e (p +ᵥ q) = p +ᵥ (e q)) ↔
    (haveI := T₁.torsor.toAddTorsor
     haveI := T₂.torsor.toAddTorsor
     ∀ (P Q : T₁.C_pts), e P -ᵥ e Q = (P -ᵥ Q : E_pts)) := by
  letI := T₁.torsor.toAddTorsor
  letI := T₂.torsor.toAddTorsor
  exact ⟨fun h P Q => Equiv.vsub_preserving e h P Q,
         fun h p q => Equiv.vadd_compat_of_vsub e h p q⟩

end ETorsor

/-- The *Weil-Châtelet set* of $E/k$: the set of $E$-torsors over $k$ up to $k$-isomorphism,
realised as the quotient of `ETorsor` by the equivalence relation. -/
def WC (k : Type u) [Field k] (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts] : Type (u + 1) :=
  Quotient (ETorsor.setoid (k := k) (W := W) (E_pts := E_pts))


namespace ETorsorPic

section PiConstruction

variable {E_pts : Type u} [AddCommGroup E_pts]
  {C_pts : Type u} [AddTorsor E_pts C_pts]

/-- The scalar multiplication $n \mapsto n \cdot e$ packaged as an additive homomorphism
$\mathbb{Z} \to E$. -/
def zsmulHom (e : E_pts) : ℤ →+ E_pts where
  toFun n := n • e
  map_zero' := zero_smul ℤ e
  map_add' m n := add_smul m n e

/-- The Abel-Jacobi map at the level of free abelian groups: $\sum n_P [P] \mapsto
\sum n_P (P -_v Q_0)$, viewed as an additive homomorphism $(C \to_0 \mathbb{Z}) \to E$. -/
def piMap (Q₀ : C_pts) : (C_pts →₀ ℤ) →+ E_pts :=
  Finsupp.liftAddHom (fun P => zsmulHom (P -ᵥ Q₀ : E_pts))

/-- The degree homomorphism on the free abelian group on $C$: $\sum n_P [P] \mapsto \sum n_P$. -/
def piDegreeMap : (C_pts →₀ ℤ) →+ ℤ :=
  Finsupp.liftAddHom (fun _ => AddMonoidHom.id ℤ)

/-- Evaluation of `piMap` on a single basis element: $\mathrm{piMap}\,Q_0\,[P]_n = n \cdot (P -_v Q_0)$. -/
@[simp] theorem piMap_single (Q₀ P : C_pts) (n : ℤ) :
    piMap Q₀ (Finsupp.single P n) = n • (P -ᵥ Q₀ : E_pts) := by
  simp [piMap, zsmulHom]

/-- The degree map sends a single basis element $[P]_n$ to $n$. -/
@[simp] theorem piDegreeMap_single (P : C_pts) (n : ℤ) :
    piDegreeMap (Finsupp.single P n) = n := by
  simp [piDegreeMap]

/-- The Abel-Jacobi map `piMap Q₀` is surjective: every element of $E$ can be realised as the
image of a divisor of degree zero. -/
theorem piMap_surjective (Q₀ : C_pts) : Function.Surjective (piMap Q₀) := by
  intro P
  use Finsupp.single (P +ᵥ Q₀) 1 - Finsupp.single Q₀ 1
  simp only [map_sub, piMap_single, one_smul, vadd_vsub, vsub_self, sub_zero]


/-- Comparison of two base points: $\mathrm{piMap}\,Q_0(D) - \mathrm{piMap}\,Q_1(D) =
\deg(D) \cdot (Q_1 -_v Q_0)$. -/
theorem piMap_sub_eq_deg_smul (Q₀ Q₁ : C_pts) (D : C_pts →₀ ℤ) :
    piMap Q₀ D - piMap Q₁ D = piDegreeMap D • (Q₁ -ᵥ Q₀ : E_pts) := by
  induction D using Finsupp.induction_linear with
  | zero => simp [piMap, piDegreeMap]
  | add D₁ D₂ ih₁ ih₂ =>
    simp only [map_add]
    have : piMap Q₀ D₁ + piMap Q₀ D₂ - (piMap Q₁ D₁ + piMap Q₁ D₂) =
        (piMap Q₀ D₁ - piMap Q₁ D₁) + (piMap Q₀ D₂ - piMap Q₁ D₂) := by abel
    rw [this, ih₁, ih₂, ← add_smul]
  | single P n =>
    simp only [piMap_single, piDegreeMap_single]
    rw [← smul_sub, vsub_sub_vsub_cancel_left]

/-- On divisors of degree zero, the Abel-Jacobi map is independent of the chosen base point. -/
theorem piMap_independent (Q₀ Q₁ : C_pts) (D : C_pts →₀ ℤ)
    (hD : piDegreeMap D = 0) : piMap Q₀ D = piMap Q₁ D := by
  have h := piMap_sub_eq_deg_smul Q₀ Q₁ D
  rw [hD, zero_smul] at h
  exact sub_eq_zero.mp h


end PiConstruction

/-- Auxiliary data for the Abel-Jacobi isomorphism $\mathrm{Pic}^0(C) \simeq E$: a factorisation
of the Abel-Jacobi map $\pi$ through an intermediate group `DivZero_E`, together with the
inclusion of principal divisors and a "function field" compatibility condition. -/
structure EllipticCurveDivisorData
    (E_pts : Type u) [AddCommGroup E_pts]
    (DivZero : Type u) [AddCommGroup DivZero]
    (DivZero_E : Type u) [AddCommGroup DivZero_E]
    (PrincDiv : AddSubgroup DivZero) (π : DivZero →+ E_pts) where
  PrincDiv_E : AddSubgroup DivZero_E
  τ : DivZero →+ DivZero_E
  σ_E : DivZero_E →+ E_pts
  hπ_factor : ∀ D, π D = σ_E (τ D)
  abel_on_E : σ_E.ker ≤ PrincDiv_E
  func_field : ∀ D, τ D ∈ PrincDiv_E → D ∈ PrincDiv

section Pic0IsoE

variable {E_pts : Type u} [AddCommGroup E_pts]
  {C_pts : Type u} [AddTorsor E_pts C_pts]
  {DivZero : Type u} [AddCommGroup DivZero]
  (PrincDiv : AddSubgroup DivZero)
  (π : DivZero →+ E_pts)

/-- The kernel of the Abel-Jacobi map $\pi$ is contained in the principal divisors:
$\ker(\pi) \subseteq \mathrm{Princ}$. -/
theorem abel_jacobi_ker_le_princDiv
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts DivZero DivZero_E PrincDiv π) :
    π.ker ≤ PrincDiv := by
  intro D hD
  rw [AddMonoidHom.mem_ker] at hD

  have h1 : data.σ_E (data.τ D) = 0 := by rw [← data.hπ_factor]; exact hD
  have h2 : data.τ D ∈ data.σ_E.ker := by rwa [AddMonoidHom.mem_ker]

  have h3 : data.τ D ∈ data.PrincDiv_E := data.abel_on_E h2

  exact data.func_field D h3

/-- Conversely, principal divisors are contained in the kernel of $\pi$, provided the converse
versions of the `EllipticCurveDivisorData` axioms hold. -/
theorem princDiv_le_ker_pi
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts DivZero DivZero_E PrincDiv π)
    (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
    (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E) :
    PrincDiv ≤ π.ker := by
  intro D hD
  rw [AddMonoidHom.mem_ker]

  have h1 : data.τ D ∈ data.PrincDiv_E := hfunc_field_converse D hD

  have h2 : data.τ D ∈ data.σ_E.ker := habel_converse h1
  rw [AddMonoidHom.mem_ker] at h2

  rw [data.hπ_factor D, h2]

/-- Combining the two inclusions: $\ker(\pi) = \mathrm{Princ}$. -/
theorem piMap_ker_eq_princDiv
    (hπ_ker_le : π.ker ≤ PrincDiv) (hπ_principal_in_ker : PrincDiv ≤ π.ker) :
    π.ker = PrincDiv :=
  le_antisymm hπ_ker_le hπ_principal_in_ker

/-- The Abel-Jacobi isomorphism: assuming the abstract divisor data and surjectivity of $\pi$,
one has $\mathrm{Pic}^0(C) = \mathrm{Div}^0/\mathrm{Princ} \cong E$. -/
noncomputable def pic0_addEquiv_E
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts DivZero DivZero_E PrincDiv π)
    (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
    (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E)
    (hπ_surj : Function.Surjective π) : DivZero ⧸ PrincDiv ≃+ E_pts :=
  have hπ_ker_le : π.ker ≤ PrincDiv := abel_jacobi_ker_le_princDiv PrincDiv π data
  have hπ_principal_in_ker : PrincDiv ≤ π.ker :=
    princDiv_le_ker_pi PrincDiv π data habel_converse hfunc_field_converse
  (piMap_ker_eq_princDiv PrincDiv π hπ_ker_le hπ_principal_in_ker) ▸
    QuotientAddGroup.quotientKerEquivOfSurjective π hπ_surj

/-- Compatibility: the Abel-Jacobi isomorphism sends the class $[D]$ of a divisor $D$ to its image
$\pi(D)$ in $E$. -/
theorem pic0_addEquiv_E_mk
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts DivZero DivZero_E PrincDiv π)
    (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
    (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E)
    (hπ_surj : Function.Surjective π) (D : DivZero) :
    pic0_addEquiv_E PrincDiv π data habel_converse hfunc_field_converse hπ_surj
      (QuotientAddGroup.mk' PrincDiv D) = π D := by
  unfold pic0_addEquiv_E
  generalize piMap_ker_eq_princDiv PrincDiv π
    (abel_jacobi_ker_le_princDiv PrincDiv π data)
    (princDiv_le_ker_pi PrincDiv π data habel_converse hfunc_field_converse) = hk
  subst hk
  simp [QuotientAddGroup.quotientKerEquivOfSurjective,
        QuotientAddGroup.quotientKerEquivOfRightInverse]

/-- The Abel-Jacobi isomorphism is additive: $\Phi(x + y) = \Phi(x) + \Phi(y)$. -/
theorem pic0_addEquiv_E_map_add
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts DivZero DivZero_E PrincDiv π)
    (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
    (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E)
    (hπ_surj : Function.Surjective π) (x y : DivZero ⧸ PrincDiv) :
    pic0_addEquiv_E PrincDiv π data habel_converse hfunc_field_converse hπ_surj (x + y) =
    pic0_addEquiv_E PrincDiv π data habel_converse hfunc_field_converse hπ_surj x +
    pic0_addEquiv_E PrincDiv π data habel_converse hfunc_field_converse hπ_surj y :=
  map_add _ x y

/-- The Abel-Jacobi isomorphism sends $0$ to $0$. -/
theorem pic0_addEquiv_E_map_zero
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts DivZero DivZero_E PrincDiv π)
    (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
    (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E)
    (hπ_surj : Function.Surjective π) :
    pic0_addEquiv_E PrincDiv π data habel_converse hfunc_field_converse hπ_surj 0 = 0 :=
  map_zero _

/-- Inverse formula: $\Phi^{-1}(P)$ is the class of any preimage of $P$ under $\pi$, chosen via
the surjectivity hypothesis. -/
theorem pic0_addEquiv_E_symm_apply
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts DivZero DivZero_E PrincDiv π)
    (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
    (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E)
    (hπ_surj : Function.Surjective π) (P : E_pts) :
    (pic0_addEquiv_E PrincDiv π data habel_converse hfunc_field_converse hπ_surj).symm P =
    QuotientAddGroup.mk' PrincDiv ((hπ_surj P).choose) := by
  apply (pic0_addEquiv_E PrincDiv π data habel_converse hfunc_field_converse hπ_surj).injective
  rw [AddEquiv.apply_symm_apply, pic0_addEquiv_E_mk]
  exact (hπ_surj P).choose_spec.symm

end Pic0IsoE

section ConcretePic0Iso

variable {E_pts : Type u} [AddCommGroup E_pts]
  {C_pts : Type u} [AddTorsor E_pts C_pts]
  (PrincDiv : AddSubgroup (C_pts →₀ ℤ))
  (Q₀ : C_pts)

/-- Theorem 26.17 (concrete form): the Abel-Jacobi isomorphism
$\mathrm{Pic}^0(C) \cong E$ obtained from the concrete `piMap` and a divisor data. -/
noncomputable def theorem_26_17_pic0_iso
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts (C_pts →₀ ℤ) DivZero_E PrincDiv (piMap Q₀))
    (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
    (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E) :
    (C_pts →₀ ℤ) ⧸ PrincDiv ≃+ E_pts :=
  pic0_addEquiv_E PrincDiv (piMap Q₀) data habel_converse hfunc_field_converse
    (piMap_surjective Q₀)

/-- Surjectivity statement from Theorem 26.17: `piMap Q₀` is surjective. -/
theorem theorem_26_17_surjective :
    Function.Surjective (piMap Q₀ : (C_pts →₀ ℤ) →+ E_pts) :=
  piMap_surjective Q₀

/-- Kernel-containment statement from Theorem 26.17: $\ker(\mathrm{piMap}\,Q_0) \subseteq \mathrm{Princ}$. -/
theorem theorem_26_17_ker_le_princDiv
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts (C_pts →₀ ℤ) DivZero_E PrincDiv (piMap Q₀)) :
    (piMap Q₀).ker ≤ PrincDiv :=
  abel_jacobi_ker_le_princDiv PrincDiv (piMap Q₀) data

/-- Reverse containment from Theorem 26.17: $\mathrm{Princ} \subseteq \ker(\mathrm{piMap}\,Q_0)$. -/
theorem theorem_26_17_princDiv_le_ker
    {DivZero_E : Type u} [AddCommGroup DivZero_E]
    (data : EllipticCurveDivisorData E_pts (C_pts →₀ ℤ) DivZero_E PrincDiv (piMap Q₀))
    (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
    (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E) :
    PrincDiv ≤ (piMap Q₀).ker :=
  princDiv_le_ker_pi PrincDiv (piMap Q₀) data habel_converse hfunc_field_converse

/-- Base-point independence from Theorem 26.17: for divisors of degree zero, `piMap` does not
depend on the chosen base point. -/
theorem theorem_26_17_independent (Q₁ : C_pts) (D : C_pts →₀ ℤ)
    (hD : piDegreeMap D = 0) : piMap Q₀ D = piMap Q₁ D :=
  piMap_independent Q₀ Q₁ D hD

end ConcretePic0Iso

end ETorsorPic

end
