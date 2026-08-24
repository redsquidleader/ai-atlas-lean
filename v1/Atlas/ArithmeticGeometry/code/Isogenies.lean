/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.GroupTheory.Torsion
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Atlas.ArithmeticGeometry.code.EllipticCurves
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Atlas.ArithmeticGeometry.code.PadicElliptic
import Atlas.ArithmeticGeometry.code.WeierstrassValBound

open WeierstrassCurve

noncomputable def IsMorphismOfCurves {F : Type*} [Field F] [DecidableEq F]
    {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    (f : W₁.toAffine.Point → W₂.toAffine.Point) : Prop := by sorry

theorem isMorphismOfCurves_id {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve F} [W.IsElliptic] :
    IsMorphismOfCurves (_root_.id : W.toAffine.Point → W.toAffine.Point) := by sorry

theorem isMorphismOfCurves_comp {F : Type*} [Field F] [DecidableEq F]
    {W₁ W₂ W₃ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic] [W₃.IsElliptic]
    {f : W₁.toAffine.Point → W₂.toAffine.Point}
    {g : W₂.toAffine.Point → W₃.toAffine.Point}
    (hf : IsMorphismOfCurves f) (hg : IsMorphismOfCurves g) :
    IsMorphismOfCurves (g ∘ f) := by sorry

theorem isMorphismOfCurves_add {F : Type*} [Field F] [DecidableEq F]
    {W : WeierstrassCurve F} [W.IsElliptic]
    {f g : W.toAffine.Point → W.toAffine.Point}
    (hf : IsMorphismOfCurves f) (hg : IsMorphismOfCurves g) :
    IsMorphismOfCurves (fun P => f P + g P) := by sorry

structure EllipticCurveIsogeny {F : Type*} [Field F] [DecidableEq F]
    (W₁ W₂ : WeierstrassCurve F) [W₁.IsElliptic] [W₂.IsElliptic] where
  toFun : W₁.toAffine.Point → W₂.toAffine.Point
  is_morphism : IsMorphismOfCurves toFun
  surjective : Function.Surjective toFun
  map_zero : toFun 0 = 0

namespace EllipticCurveIsogeny

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    [W₁.IsElliptic] [W₂.IsElliptic]

instance : FunLike (EllipticCurveIsogeny W₁ W₂) W₁.toAffine.Point W₂.toAffine.Point where
  coe := toFun
  coe_injective' f g h := by
    rcases f with ⟨f_fun, _, _, _⟩
    rcases g with ⟨g_fun, _, _, _⟩
    have : f_fun = g_fun := h
    subst this
    rfl

@[simp]
theorem coe_toFun (φ : EllipticCurveIsogeny W₁ W₂) : φ.toFun = φ := rfl

@[simp]
theorem map_zero' (φ : EllipticCurveIsogeny W₁ W₂) : φ 0 = 0 := φ.map_zero

end EllipticCurveIsogeny

theorem EllipticCurveIsogeny.hasMapOnPoints {F : Type*} [Field F] [DecidableEq F]
    {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : EllipticCurveIsogeny W₁ W₂) :
    ∀ (A : Type*) [Field A] [DecidableEq A] (f : F →+* A),
      ∃ (g : (W₁.map f).toAffine.Point → (W₂.map f).toAffine.Point),
        IsMorphismOfCurves g ∧ Function.Surjective g ∧ g 0 = 0 := by sorry

namespace EllipticCurveIsogeny

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    [W₁.IsElliptic] [W₂.IsElliptic]

noncomputable def Pic0Type :
    {F : Type*} → [Field F] → [DecidableEq F] →
    (W : WeierstrassCurve F) → [W.IsElliptic] → Type := by sorry

noncomputable def Pic0AddCommGroup :
    {F : Type*} → [Field F] → [DecidableEq F] →
    (W : WeierstrassCurve F) → [W.IsElliptic] →
    AddCommGroup (Pic0Type W) := by sorry

noncomputable def Pic0Equiv :
    {F : Type*} → [Field F] → [DecidableEq F] →
    (W : WeierstrassCurve F) → [W.IsElliptic] →
    letI := Pic0AddCommGroup W
    W.toAffine.Point ≃+ Pic0Type W := by sorry

noncomputable def Pic0Pushforward :
    {F : Type*} → [Field F] → [DecidableEq F] →
    {W₁ W₂ : WeierstrassCurve F} → [W₁.IsElliptic] → [W₂.IsElliptic] →
    (φ : EllipticCurveIsogeny W₁ W₂) →
    letI := Pic0AddCommGroup W₁
    letI := Pic0AddCommGroup W₂
    Pic0Type W₁ →+ Pic0Type W₂ := by sorry

theorem Pic0Pushforward_naturality :
    {F : Type*} → [Field F] → [DecidableEq F] →
    {W₁ W₂ : WeierstrassCurve F} → [W₁.IsElliptic] → [W₂.IsElliptic] →
    (φ : EllipticCurveIsogeny W₁ W₂) →
    letI := Pic0AddCommGroup W₁
    letI := Pic0AddCommGroup W₂
    ∀ P Q : W₁.toAffine.Point,
      (Pic0Pushforward φ) ((Pic0Equiv W₁) P - (Pic0Equiv W₁) Q) =
        (Pic0Equiv W₂) (φ.toFun P) - (Pic0Equiv W₂) (φ.toFun Q) := by sorry

theorem Pic0Pushforward_compat
    (φ : EllipticCurveIsogeny W₁ W₂) :
    letI := Pic0AddCommGroup W₁
    letI := Pic0AddCommGroup W₂
    ∀ P : W₁.toAffine.Point,
      (Pic0Equiv W₂) (φ.toFun P) = (Pic0Pushforward φ) ((Pic0Equiv W₁) P) := by
  letI inst₁ := Pic0AddCommGroup W₁
  letI inst₂ := Pic0AddCommGroup W₂
  intro P


  have nat := Pic0Pushforward_naturality φ P 0


  simp only [AddEquiv.map_zero, sub_zero, φ.map_zero] at nat

  exact nat.symm

theorem isogeny_additivity_from_rigidity
    {F : Type*} [Field F] [DecidableEq F]
    {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : EllipticCurveIsogeny W₁ W₂) :
    ∀ (P Q : W₁.toAffine.Point), φ.toFun (P + Q) = φ.toFun P + φ.toFun Q := by

  letI inst₁ := Pic0AddCommGroup W₁
  letI inst₂ := Pic0AddCommGroup W₂
  let e₁ := Pic0Equiv W₁
  let e₂ := Pic0Equiv W₂
  let push := Pic0Pushforward φ
  have compat : ∀ P, e₂ (φ.toFun P) = push (e₁ P) := Pic0Pushforward_compat φ

  have factor : ∀ X : W₁.toAffine.Point, φ.toFun X = e₂.symm (push (e₁ X)) := by
    intro X
    have h := compat X


    have : e₂.symm (e₂ (φ.toFun X)) = e₂.symm (push (e₁ X)) := congrArg e₂.symm h
    rwa [e₂.symm_apply_apply] at this

  intro P Q
  rw [factor (P + Q), factor P, factor Q]
  simp only [map_add]

theorem isogeny_map_add (φ : EllipticCurveIsogeny W₁ W₂)
    (P Q : W₁.toAffine.Point) :
    φ (P + Q) = φ P + φ Q :=
  isogeny_additivity_from_rigidity φ P Q
attribute [simp] isogeny_map_add

def toAddMonoidHom (φ : EllipticCurveIsogeny W₁ W₂) :
    W₁.toAffine.Point →+ W₂.toAffine.Point where
  toFun := φ
  map_zero' := φ.map_zero'
  map_add' := φ.isogeny_map_add

@[simp]
theorem toAddMonoidHom_apply (φ : EllipticCurveIsogeny W₁ W₂)
    (P : W₁.toAffine.Point) :
    φ.toAddMonoidHom P = φ P := rfl

def id (W : WeierstrassCurve F) [W.IsElliptic] : EllipticCurveIsogeny W W where
  toFun := _root_.id
  is_morphism := isMorphismOfCurves_id
  surjective := Function.surjective_id
  map_zero := rfl

def comp {W₃ : WeierstrassCurve F} [W₃.IsElliptic]
    (ψ : EllipticCurveIsogeny W₂ W₃) (φ : EllipticCurveIsogeny W₁ W₂) :
    EllipticCurveIsogeny W₁ W₃ where
  toFun := ψ.toFun ∘ φ.toFun
  is_morphism := isMorphismOfCurves_comp φ.is_morphism ψ.is_morphism
  surjective := ψ.surjective.comp φ.surjective
  map_zero := by simp [Function.comp]

def ker (φ : EllipticCurveIsogeny W₁ W₂) : AddSubgroup W₁.toAffine.Point :=
  φ.toAddMonoidHom.ker

theorem mem_ker (φ : EllipticCurveIsogeny W₁ W₂) (P : W₁.toAffine.Point) :
    P ∈ φ.ker ↔ φ P = 0 := by
  simp [ker, AddMonoidHom.mem_ker, toAddMonoidHom_apply]

end EllipticCurveIsogeny

namespace EllipticCurveIsogeny

noncomputable def deg_axiom : {F : Type*} → [Field F] → [DecidableEq F] →
    {W₁ W₂ : WeierstrassCurve F} → [W₁.IsElliptic] → [W₂.IsElliptic] →
    EllipticCurveIsogeny W₁ W₂ → ℕ := by sorry

noncomputable def deg {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    [W₁.IsElliptic] [W₂.IsElliptic] (φ : EllipticCurveIsogeny W₁ W₂) : ℕ := deg_axiom φ

theorem deg_pos_axiom : {F : Type*} → [Field F] → [DecidableEq F] →
    {W₁ W₂ : WeierstrassCurve F} → [W₁.IsElliptic] → [W₂.IsElliptic] →
    (φ : EllipticCurveIsogeny W₁ W₂) → 0 < deg_axiom φ := by sorry

theorem deg_pos {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    [W₁.IsElliptic] [W₂.IsElliptic] (φ : EllipticCurveIsogeny W₁ W₂) : 0 < φ.deg :=
  deg_pos_axiom φ

variable {F : Type*} [Field F] [DecidableEq F] {W₁ W₂ : WeierstrassCurve F}
    [W₁.IsElliptic] [W₂.IsElliptic]

theorem ker_injects_into_aut_dvd_deg_axiom :
    {F : Type*} → [Field F] → [DecidableEq F] →
    {W₁ W₂ : WeierstrassCurve F} → [W₁.IsElliptic] → [W₂.IsElliptic] →
    (φ : EllipticCurveIsogeny W₁ W₂) →
    ∃ (G : Type) (_ : AddCommGroup G),
      (∃ (f : φ.ker →+ G), Function.Injective f) ∧
      Nat.card G ∣ deg_axiom φ := by sorry

theorem isogeny_kernel_divides_deg (φ : EllipticCurveIsogeny W₁ W₂) :
    Nat.card ↑(φ.toFun ⁻¹' {0}) ∣ φ.deg := by


  obtain ⟨G, hGrp, ⟨f, hInj⟩, hDvd⟩ := ker_injects_into_aut_dvd_deg_axiom φ


  have hLag : Nat.card φ.ker ∣ Nat.card G := AddSubgroup.card_dvd_of_injective f hInj


  have hEq : Nat.card ↑(φ.ker : Set W₁.toAffine.Point) = Nat.card ↑(φ.toFun ⁻¹' {0}) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquiv (Equiv.refl _) (fun P => by
      simp only [SetLike.mem_coe, ker, AddMonoidHom.mem_ker, Set.mem_preimage,
        Set.mem_singleton_iff, toAddMonoidHom_apply, coe_toFun, Equiv.refl_apply])
  rw [← hEq]

  exact hLag.trans hDvd

/-- Corollary: the kernel preimage $\varphi^{-1}\{0\}$ of an isogeny is a finite set. -/
theorem isogeny_finite_kernel (φ : EllipticCurveIsogeny W₁ W₂) :
    Set.Finite (φ.toFun ⁻¹' {0}) := by
  have hdvd := isogeny_kernel_divides_deg φ
  have hpos : 0 < Nat.card ↑(φ.toFun ⁻¹' {0}) :=
    Nat.pos_of_ne_zero (fun h => by rw [h] at hdvd; have := deg_pos φ; omega)
  haveI : Finite ↑(φ.toFun ⁻¹' {0}) := (Nat.card_pos_iff.mp hpos).2
  exact Set.toFinite _

/-- The kernel subgroup $\ker \varphi$, viewed as a set in $E_1(F)$, is finite. -/
theorem ker_finite (φ : EllipticCurveIsogeny W₁ W₂) : Set.Finite (φ.ker : Set W₁.toAffine.Point) := by
  have h : (φ.ker : Set W₁.toAffine.Point) = φ.toFun ⁻¹' {0} := by
    ext P
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact Iff.rfl
  rw [h]
  exact isogeny_finite_kernel φ

end EllipticCurveIsogeny

namespace EllipticCurveIsogeny

variable {k : Type*} [Field k] [DecidableEq k]
    {W₁ W₂ : WeierstrassCurve k} [W₁.IsElliptic] [W₂.IsElliptic]

/-- The function-field extension data associated to an isogeny $\varphi$: a pair of
fields $k(E_1) \supseteq \varphi^* k(E_2)$ with the inclusion as an algebra map. -/
structure FunctionFieldExtension (φ : EllipticCurveIsogeny W₁ W₂) where
  FunctionField : Type
  PullbackField : Type
  [field_top : Field FunctionField]
  [field_bot : Field PullbackField]
  [algebra_inst : Algebra PullbackField FunctionField]

namespace FunctionFieldExtension

variable {φ : EllipticCurveIsogeny W₁ W₂} (ext : φ.FunctionFieldExtension)

/-- The "top" field $k(E_1)$ is a field. -/
instance : Field ext.FunctionField := ext.field_top
/-- The "bottom" field $\varphi^* k(E_2)$ is a field. -/
instance : Field ext.PullbackField := ext.field_bot
/-- $k(E_1)$ is an algebra over the pullback field $\varphi^* k(E_2)$. -/
instance : Algebra ext.PullbackField ext.FunctionField := ext.algebra_inst

end FunctionFieldExtension

/-- An isogeny is separable if the induced function-field extension is separable. -/
def IsSeparableIsogeny (φ : EllipticCurveIsogeny W₁ W₂)
    (ext : φ.FunctionFieldExtension) : Prop :=
  Algebra.IsSeparable ext.PullbackField ext.FunctionField

/-- An isogeny is inseparable if it fails to be separable. -/
def IsInseparableIsogeny (φ : EllipticCurveIsogeny W₁ W₂)
    (ext : φ.FunctionFieldExtension) : Prop :=
  ¬ φ.IsSeparableIsogeny ext

/-- An isogeny is purely inseparable if the induced function-field extension is
purely inseparable. -/
def IsPurelyInseparableIsogeny (φ : EllipticCurveIsogeny W₁ W₂)
    (ext : φ.FunctionFieldExtension) : Prop :=
  IsPurelyInseparable ext.PullbackField ext.FunctionField

end EllipticCurveIsogeny

namespace EllipticCurveIsogeny

universe u


/-- An isogeny respects negation: $\varphi(-P) = -\varphi(P)$ (corollary of being
a group homomorphism). -/
theorem map_neg {F : Type*} [Field F] [DecidableEq F]
    {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : EllipticCurveIsogeny W₁ W₂) (P : W₁.toAffine.Point) :
    φ (-P) = -φ P :=
  φ.toAddMonoidHom.map_neg P

/-- Auxiliary: the underlying isogeny built by base-changing $\varphi$ along
$k \to L$, packaged from `hasMapOnPoints`. -/
noncomputable def baseChangeIsogeny_val {k : Type*} [Field k] [DecidableEq k]
    {W₁ W₂ : WeierstrassCurve k} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : EllipticCurveIsogeny W₁ W₂)
    (L : Type*) [Field L] [DecidableEq L] [Algebra k L] :
    EllipticCurveIsogeny (W₁.baseChange L) (W₂.baseChange L) :=
  have h := hasMapOnPoints φ L (algebraMap k L)
  { toFun := h.choose
    is_morphism := h.choose_spec.1
    surjective := h.choose_spec.2.1
    map_zero := h.choose_spec.2.2 }

/-- The base change $\varphi_L : E_{1,L} \to E_{2,L}$ of an isogeny $\varphi$ along
a field extension $k \to L$. -/
noncomputable def baseChangeIsogeny {k : Type*} [Field k] [DecidableEq k]
    {W₁ W₂ : WeierstrassCurve k} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : EllipticCurveIsogeny W₁ W₂)
    (L : Type*) [Field L] [DecidableEq L] [Algebra k L] :
    EllipticCurveIsogeny (W₁.baseChange L) (W₂.baseChange L) :=
  baseChangeIsogeny_val φ L

/-- The base-changed isogeny is also additive on points over the extension. -/
theorem map_add_over_extension {k : Type*} [Field k] [DecidableEq k]
    {W₁ W₂ : WeierstrassCurve k} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : EllipticCurveIsogeny W₁ W₂)
    (L : Type*) [Field L] [DecidableEq L] [Algebra k L] [Algebra.IsAlgebraic k L]
    (P Q : (W₁.baseChange L).toAffine.Point) :
    (φ.baseChangeIsogeny L) (P + Q) =
      (φ.baseChangeIsogeny L) P + (φ.baseChangeIsogeny L) Q :=
  (φ.baseChangeIsogeny L).isogeny_map_add P Q

/-- The base-changed isogeny as a group homomorphism over $L$. -/
noncomputable def toAddMonoidHom_over_extension {k : Type*} [Field k] [DecidableEq k]
    {W₁ W₂ : WeierstrassCurve k} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : EllipticCurveIsogeny W₁ W₂)
    (L : Type*) [Field L] [DecidableEq L] [Algebra k L] [Algebra.IsAlgebraic k L] :
    (W₁.baseChange L).toAffine.Point →+ (W₂.baseChange L).toAffine.Point where
  toFun := φ.baseChangeIsogeny L
  map_zero' := (φ.baseChangeIsogeny L).map_zero'
  map_add' := fun P Q => (φ.baseChangeIsogeny L).isogeny_map_add P Q

end EllipticCurveIsogeny

section PointFinite

variable {R : Type*} [CommRing R] [Fintype R] (W : WeierstrassCurve R)

/-- Encode an affine Weierstrass point as `Option (R × R)`: the point at infinity is
`none`, and an affine point $(x, y)$ is `some (x, y)`. -/
noncomputable def WeierstrassCurve.Affine.Point.toOption
    (P : W.toAffine.Point) : Option (R × R) :=
  match P with
  | .zero => Option.none
  | .some x y _ => Option.some (x, y)

omit [Fintype R] in
/-- The encoding `toOption` is injective: distinct affine points have distinct
encodings. -/
lemma WeierstrassCurve.Affine.Point.toOption_injective :
    Function.Injective (WeierstrassCurve.Affine.Point.toOption W) := by
  intro a b hab
  simp only [WeierstrassCurve.Affine.Point.toOption] at hab
  cases a <;> cases b <;> simp_all

/-- If the base ring is finite, then the set of points of an affine Weierstrass curve
is also finite. -/
noncomputable instance WeierstrassCurve.Affine.Point.finite :
    Finite W.toAffine.Point :=
  Finite.of_injective _ (WeierstrassCurve.Affine.Point.toOption_injective W)

end PointFinite

/-- In a torsion-free abelian group, an element of finite additive order must be zero. -/
lemma eq_zero_of_isOfFinAddOrder_of_torsionFree
    {G : Type*} [AddCommGroup G] [IsAddTorsionFree G]
    (g : G) (h : IsOfFinAddOrder g) : g = 0 := by
  rw [isOfFinAddOrder_iff_nsmul_eq_zero] at h
  obtain ⟨n, hn, hng⟩ := h
  exact (IsAddTorsionFree.nsmul_right_injective hn.ne') (hng.trans (smul_zero n).symm)


/-- An elliptic curve over $\mathbb{Q}$ has good reduction at a prime $p$ if it
admits a model that reduces mod $p$ to an elliptic curve over $\mathbb{F}_p$. -/
structure HasGoodReduction (W : WeierstrassCurve ℚ) (p : ℕ) [Fact (Nat.Prime p)] where
  reducedCurve : WeierstrassCurve (ZMod p)
  isElliptic : reducedCurve.IsElliptic


/-- Theorem 24.14: the reduction-mod-$p$ map $E(\mathbb{Q}) \to \tilde E(\mathbb{F}_p)$
on points, as a group homomorphism, for an elliptic curve with good reduction at $p$. -/
noncomputable def thm_24_14_reduction_hom
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (p : ℕ) [Fact (Nat.Prime p)]
    (Wred : WeierstrassCurve (ZMod p)) [Wred.IsElliptic] :
    W.toAffine.Point →+ Wred.toAffine.Point := by sorry


/-- Corollary 24.18: the kernel of the reduction-mod-$p$ map is torsion-free, hence
contains no nontrivial finite-order points. -/
theorem cor_24_18_kernel_torsion_free
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (p : ℕ) [Fact (Nat.Prime p)]
    (Wred : WeierstrassCurve (ZMod p)) [Wred.IsElliptic] :
    IsAddTorsionFree (thm_24_14_reduction_hom W p Wred).ker := by sorry


/-- Combined statement: existence of a reduction-mod-$p$ map whose kernel is
torsion-free. -/
theorem exists_reduction_hom_torsionFree_ker
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (p : ℕ) [Fact (Nat.Prime p)]
    (Wred : WeierstrassCurve (ZMod p)) [Wred.IsElliptic] :
    ∃ (red : W.toAffine.Point →+ Wred.toAffine.Point), IsAddTorsionFree red.ker :=
  ⟨thm_24_14_reduction_hom W p Wred, cor_24_18_kernel_torsion_free W p Wred⟩


/-- Corollary: the reduction map restricted to the torsion subgroup of $E(\mathbb{Q})$
is injective into $\tilde E(\mathbb{F}_p)$ for any prime $p$ of good reduction. -/
theorem torsion_injection
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (p : ℕ) [Fact (Nat.Prime p)] (hgr : HasGoodReduction W p) :
    ∃ f : (AddCommGroup.torsion W.toAffine.Point) →+ (hgr.reducedCurve).toAffine.Point,
      Function.Injective f := by
  haveI := hgr.isElliptic
  let red := thm_24_14_reduction_hom W p hgr.reducedCurve
  have hK := cor_24_18_kernel_torsion_free W p hgr.reducedCurve
  refine ⟨red.comp (AddCommGroup.torsion W.toAffine.Point).subtype, ?_⟩
  intro ⟨a, ha⟩ ⟨b, hb⟩ hab
  simp only [AddMonoidHom.comp_apply, AddSubgroup.coe_subtype] at hab
  rw [Subtype.mk_eq_mk]
  have hmem : a - b ∈ red.ker := by
    rw [AddMonoidHom.mem_ker]; simp [map_sub, hab]
  rw [AddCommGroup.mem_torsion] at ha hb
  have hab_torsion : IsOfFinAddOrder (a - b) := by
    rw [sub_eq_add_neg]; exact ha.add hb.neg
  have hab_in_ker : IsOfFinAddOrder (⟨a - b, hmem⟩ : red.ker) :=
    (AddSubmonoid.isOfFinAddOrder_coe (H := red.ker.toAddSubmonoid)).mp hab_torsion
  have h0 : (⟨a - b, hmem⟩ : red.ker) = 0 := by
    rw [isOfFinAddOrder_iff_nsmul_eq_zero] at hab_in_ker
    obtain ⟨n, hn, hng⟩ := hab_in_ker
    exact (IsAddTorsionFree.nsmul_right_injective hn.ne') (hng.trans (smul_zero n).symm)
  exact sub_eq_zero.mp (congr_arg Subtype.val h0)


/-- A nonsingular point $(x_0, y_0)$ on a short Weierstrass curve $y^2 = x^3 + a_4 x + a_6$
satisfies the curve equation. -/
lemma curve_equation_short_weierstrass
    (W : WeierstrassCurve ℚ)
    (hW1 : W.a₁ = 0) (hW2 : W.a₂ = 0) (hW3 : W.a₃ = 0)
    {x₀ y₀ : ℚ} (hns : W.toAffine.Nonsingular x₀ y₀) :
    y₀ ^ 2 = x₀ ^ 3 + W.a₄ * x₀ + W.a₆ := by
  have heq := hns.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  simp only [WeierstrassCurve.toAffine] at heq
  simp only [hW1, hW2, hW3, zero_mul] at heq
  linarith

/-- A rational number with nonnegative $p$-adic valuation at every prime is an integer. -/
lemma rat_is_int_of_nonneg_padic_val (q : ℚ)
    (h : ∀ p : ℕ, Nat.Prime p → padicValRat p q ≥ 0) :
    ∃ z : ℤ, (z : ℚ) = q := by
  suffices hd : q.den = 1 by
    exact ⟨q.num, by rw [← Rat.num_divInt_den q, hd]; simp⟩
  by_contra hne
  have hd_pos := q.den_pos
  obtain ⟨p, hp, hpdiv⟩ := Nat.exists_prime_and_dvd (by omega : q.den ≠ 1)
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hge := h p hp
  simp only [padicValRat] at hge
  have hpd : 1 ≤ padicValNat p q.den := one_le_padicValNat_of_dvd (by omega) hpdiv
  have hcop : Nat.Coprime q.num.natAbs q.den := q.reduced
  have hpn : ¬ (p ∣ q.num.natAbs) := by
    intro hpa
    have h1 : p ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd hpa hpdiv
    rw [hcop] at h1
    have : p ≤ 1 := Nat.le_of_dvd Nat.one_pos h1
    exact absurd this (Nat.not_le.mpr hp.one_lt)
  have hpn0 : padicValNat p q.num.natAbs = 0 := padicValNat.eq_zero_of_not_dvd hpn
  simp only [padicValInt, hpn0] at hge
  omega

/-- If a rational $q$ has $q^2 \in \mathbb{Z}$, then $q \in \mathbb{Z}$. -/
lemma rat_sq_int_imp_int (q : ℚ) (h : ∃ z : ℤ, (z : ℚ) = q ^ 2) :
    ∃ z : ℤ, (z : ℚ) = q := by
  obtain ⟨z, hz⟩ := h
  suffices hd : q.den = 1 by
    exact ⟨q.num, by rw [← Rat.num_divInt_den q, hd]; simp⟩
  have hq2_den : (q * q).den = 1 := by
    have : q * q = q ^ 2 := by ring
    rw [this, ← hz]; exact Rat.den_intCast z
  have hmul := Rat.mul_den q q
  rw [hq2_den] at hmul
  rw [show q.num * q.num = (q.num : ℤ) ^ 2 from by ring] at hmul
  rw [show q.den * q.den = q.den ^ 2 from by ring] at hmul
  rw [Int.natAbs_pow] at hmul
  rw [q.reduced.pow 2 2] at hmul
  simp at hmul
  nlinarith [sq_nonneg q.den]

/-- If a torsion point on a short Weierstrass curve over $\mathbb{Q}$ with integral
coefficients has rational coordinates, then its $x$-coordinate has nonnegative
$p$-adic valuation at every prime $p$. -/
theorem torsion_point_nonneg_padic_val
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hW1 : W.a₁ = 0) (hW2 : W.a₂ = 0) (hW3 : W.a₃ = 0)
    (a₄_int : ℤ) (ha4 : (a₄_int : ℚ) = W.a₄)
    (a₆_int : ℤ) (ha6 : (a₆_int : ℚ) = W.a₆)
    {x₀ y₀ : ℚ} (hns : W.toAffine.Nonsingular x₀ y₀)
    (hfin : IsOfFinAddOrder (WeierstrassCurve.Affine.Point.some x₀ y₀ hns))
    (p : ℕ) (hp : Nat.Prime p) :
    padicValRat p x₀ ≥ 0 := by sorry

/-- First part of Nagell-Lutz: any rational torsion point on a short Weierstrass curve
$E/\mathbb{Q}$ with integer coefficients has integer coordinates $(x_0, y_0) \in
\mathbb{Z}^2$. -/
theorem nagell_lutz_integrality
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hW1 : W.a₁ = 0) (hW2 : W.a₂ = 0) (hW3 : W.a₃ = 0)
    (a₄_int : ℤ) (ha4 : (a₄_int : ℚ) = W.a₄)
    (a₆_int : ℤ) (ha6 : (a₆_int : ℚ) = W.a₆)
    {x₀ y₀ : ℚ} (hns : W.toAffine.Nonsingular x₀ y₀)
    (hfin : IsOfFinAddOrder (WeierstrassCurve.Affine.Point.some x₀ y₀ hns)) :
    (∃ x₀' : ℤ, (x₀' : ℚ) = x₀) ∧ (∃ y₀' : ℤ, (y₀' : ℚ) = y₀) := by

  have hx : ∃ x₀' : ℤ, (x₀' : ℚ) = x₀ := by
    apply rat_is_int_of_nonneg_padic_val
    intro p hp
    exact torsion_point_nonneg_padic_val W hW1 hW2 hW3 a₄_int ha4 a₆_int ha6 hns hfin p hp

  have hcurve := curve_equation_short_weierstrass W hW1 hW2 hW3 hns
  obtain ⟨x₀', hx0⟩ := hx
  have hy2 : ∃ z : ℤ, (z : ℚ) = y₀ ^ 2 := by
    refine ⟨x₀' ^ 3 + a₄_int * x₀' + a₆_int, ?_⟩
    push_cast
    rw [hx0, ha4, ha6]
    linarith

  exact ⟨⟨x₀', hx0⟩, rat_sq_int_imp_int y₀ hy2⟩

/-- Slope-divisibility step of Nagell-Lutz: if $(x_0, y_0)$ is an integral torsion
point on the short Weierstrass curve with $y_0 \neq 0$, then $y_0^2 \mid
(3 x_0^2 + a_4)^2$. -/
theorem nagell_lutz_slope_div
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hW1 : W.a₁ = 0) (hW2 : W.a₂ = 0) (hW3 : W.a₃ = 0)
    (a₄_int : ℤ) (ha4 : (a₄_int : ℚ) = W.a₄)
    (a₆_int : ℤ) (ha6 : (a₆_int : ℚ) = W.a₆)
    {x₀ y₀ : ℚ} (hns : W.toAffine.Nonsingular x₀ y₀)
    (hfin : IsOfFinAddOrder (WeierstrassCurve.Affine.Point.some x₀ y₀ hns))
    (x₀' : ℤ) (hx0 : (x₀' : ℚ) = x₀)
    (y₀' : ℤ) (hy0 : (y₀' : ℚ) = y₀) (hy0_ne : y₀ ≠ 0) :
    (y₀' ^ 2 : ℤ) ∣ (3 * x₀' ^ 2 + a₄_int) ^ 2 := by

  have hWa1 : W.toAffine.a₁ = 0 := by simp [WeierstrassCurve.toAffine, hW1]
  have hWa2 : W.toAffine.a₂ = 0 := by simp [WeierstrassCurve.toAffine, hW2]
  have hWa3 : W.toAffine.a₃ = 0 := by simp [WeierstrassCurve.toAffine, hW3]

  have hy_ne_neg : y₀ ≠ W.toAffine.negY x₀ y₀ := by
    simp only [Affine.negY, hWa1, hWa3, zero_mul, sub_zero]
    intro heq; exact hy0_ne (by linarith)
  have hnotxy : ¬(x₀ = x₀ ∧ y₀ = W.toAffine.negY x₀ y₀) := fun h => hy_ne_neg h.2

  have hns2 := Affine.nonsingular_add hns hns hnotxy
  have h2P := Affine.Point.add_some hnotxy (h₁ := hns) (h₂ := hns)

  have hfin2 : IsOfFinAddOrder
      (Affine.Point.some x₀ y₀ hns + Affine.Point.some x₀ y₀ hns) := hfin.add hfin
  rw [h2P] at hfin2

  obtain ⟨⟨x2_int, hx2_eq⟩, _⟩ :=
    nagell_lutz_integrality W hW1 hW2 hW3 a₄_int ha4 a₆_int ha6 hns2 hfin2


  have hx2_formula : (x2_int : ℚ) = ((3 * x₀ ^ 2 + W.a₄) / (2 * y₀)) ^ 2 - 2 * x₀ := by
    rw [hx2_eq]
    simp only [Affine.addX, hWa1, hWa2]
    have hne : ¬y₀ = -y₀ - W.toAffine.a₁ * x₀ - W.toAffine.a₃ := by
      simp [hWa1, hWa3]; intro heq; exact hy0_ne (by linarith)
    rw [Affine.slope_of_Y_ne' hne]
    simp [hWa1, hWa2, hWa3, WeierstrassCurve.toAffine]
    ring

  rw [← ha4, ← hx0, ← hy0] at hx2_formula

  have h2y0_ne : (2 * (y₀' : ℚ)) ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, false_or]; rwa [hy0]
  have h1 : ((3 * (x₀' : ℚ) ^ 2 + (a₄_int : ℚ)) / (2 * (y₀' : ℚ))) ^ 2 =
      (x2_int : ℚ) + 2 * (x₀' : ℚ) := by linarith
  have h2 : (3 * (x₀' : ℚ) ^ 2 + (a₄_int : ℚ)) ^ 2 =
      ((x2_int : ℚ) + 2 * (x₀' : ℚ)) * (2 * (y₀' : ℚ)) ^ 2 := by
    rw [← h1, div_pow, div_mul_cancel₀]
    exact pow_ne_zero 2 h2y0_ne

  have h3 : (3 * x₀' ^ 2 + a₄_int) ^ 2 = (x2_int + 2 * x₀') * (4 * y₀' ^ 2) := by
    exact_mod_cast (by linarith :
      ((3 * x₀' ^ 2 + a₄_int) ^ 2 : ℚ) = ((x2_int + 2 * x₀') * (4 * y₀' ^ 2) : ℚ))
  rw [h3]
  exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _

/-- Theorem 24.21 (Nagell-Lutz): any rational torsion point $(x_0, y_0)$ on the
short Weierstrass curve $y^2 = x^3 + a_4 x + a_6$ over $\mathbb{Q}$ (with
$a_4, a_6 \in \mathbb{Z}$) satisfies $x_0, y_0 \in \mathbb{Z}$, and either $y_0 = 0$
or $y_0^2 \mid (4 a_4^3 + 27 a_6^2)$. -/
theorem nagell_lutz
    (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (hW1 : W.a₁ = 0) (hW2 : W.a₂ = 0) (hW3 : W.a₃ = 0)
    (a₄_int : ℤ) (ha4 : (a₄_int : ℚ) = W.a₄)
    (a₆_int : ℤ) (ha6 : (a₆_int : ℚ) = W.a₆)
    {x₀ y₀ : ℚ} (hns : W.toAffine.Nonsingular x₀ y₀)
    (hfin : IsOfFinAddOrder (WeierstrassCurve.Affine.Point.some x₀ y₀ hns)) :
    (∃ x₀' : ℤ, (x₀' : ℚ) = x₀) ∧
    (∃ y₀' : ℤ, (y₀' : ℚ) = y₀) ∧
    (y₀ = 0 ∨ ∃ y₀' : ℤ, (y₀' : ℚ) = y₀ ∧
      (y₀' ^ 2 : ℤ) ∣ (4 * a₄_int ^ 3 + 27 * a₆_int ^ 2)) := by

  obtain ⟨⟨x₀', hx0⟩, ⟨y₀', hy0⟩⟩ :=
    nagell_lutz_integrality W hW1 hW2 hW3 a₄_int ha4 a₆_int ha6 hns hfin
  refine ⟨⟨x₀', hx0⟩, ⟨y₀', hy0⟩, ?_⟩

  by_cases hy : y₀ = 0
  · exact Or.inl hy
  · right
    refine ⟨y₀', hy0, ?_⟩

    have hdiv := nagell_lutz_slope_div W hW1 hW2 hW3 a₄_int ha4 a₆_int ha6
      hns hfin x₀' hx0 y₀' hy0 hy

    have hcurve := curve_equation_short_weierstrass W hW1 hW2 hW3 hns
    rw [← ha4, ← ha6] at hcurve
    have hcurve_q : (y₀' : ℚ) ^ 2 = (x₀' : ℚ) ^ 3 + (a₄_int : ℚ) * (x₀' : ℚ) + (a₆_int : ℚ) :=
      by rw [hy0, hx0]; exact hcurve
    have hcurve_int : y₀' ^ 2 = x₀' ^ 3 + a₄_int * x₀' + a₆_int := by exact_mod_cast hcurve_q


    have hcub : x₀' ^ 3 + a₄_int * x₀' = y₀' ^ 2 - a₆_int := by linarith
    have hdiv_lhs : (y₀' ^ 2) ∣ ((3 * x₀' ^ 2 + 4 * a₄_int) * (3 * x₀' ^ 2 + a₄_int) ^ 2) :=
      dvd_mul_of_dvd_right hdiv _
    have hident : (3 * x₀' ^ 2 + 4 * a₄_int) * (3 * x₀' ^ 2 + a₄_int) ^ 2 =
      27 * (x₀' ^ 3 + a₄_int * x₀') ^ 2 + 4 * a₄_int ^ 3 := by ring
    rw [hident, hcub] at hdiv_lhs

    have key : 27 * (y₀' ^ 2 - a₆_int) ^ 2 + 4 * a₄_int ^ 3 =
      y₀' ^ 2 * (27 * y₀' ^ 2 - 54 * a₆_int) + (4 * a₄_int ^ 3 + 27 * a₆_int ^ 2) := by ring
    rw [key] at hdiv_lhs
    exact (dvd_add_right (dvd_mul_right _ _)).mp hdiv_lhs

section MultiplicationByN

variable {G : Type*} [AddCommGroup G]


end MultiplicationByN

/-- Axiom: a nonconstant morphism of curves $f : E \to E$ sending $0$ to $0$ is
surjective (a curve of genus one has no nontrivial subvariety of dimension one). -/
theorem isMorphismOfCurves_nonconstant_surjective :
    {F : Type*} → [Field F] → [DecidableEq F] →
    (W : WeierstrassCurve F) → [W.IsElliptic] →
    (f : W.toAffine.Point → W.toAffine.Point) →
    IsMorphismOfCurves f →
    f 0 = 0 →
    (∃ P : W.toAffine.Point, f P ≠ 0) →
    Function.Surjective f := by sorry

/-- Axiom: for any $n > 0$, the multiplication-by-$n$ map on an elliptic curve has a
nonzero image, i.e. it is not the zero map. -/
theorem mulByN_nonconstant :
    {F : Type*} → [Field F] → [DecidableEq F] →
    (W : WeierstrassCurve F) → [W.IsElliptic] →
    (n : ℕ) → 0 < n →
    ∃ P : W.toAffine.Point, (multiplicationByN (G := W.toAffine.Point) n) P ≠ 0 := by sorry

/-- For any $n > 0$, multiplication-by-$n$ is a morphism of curves $E \to E$
(proved by induction using `isMorphismOfCurves_add`). -/
theorem mulByN_isMorphism_axiom :
    {F : Type*} → [Field F] → [DecidableEq F] →
    (W : WeierstrassCurve F) → [W.IsElliptic] →
    (n : ℕ) → 0 < n →
    IsMorphismOfCurves (multiplicationByN (G := W.toAffine.Point) n) := by
  intro F _ _ W _ n hn
  induction n with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>

      have h : (⇑(multiplicationByN (G := W.toAffine.Point) 1) : W.toAffine.Point → W.toAffine.Point) = id := by
        funext P
        simp [multiplicationByN, nsmulAddMonoidHom]
      rw [h]
      exact isMorphismOfCurves_id
    | succ k =>

      have h1 : 0 < k + 1 := Nat.succ_pos k
      have hmor : IsMorphismOfCurves (multiplicationByN (G := W.toAffine.Point) (k + 1)) := ih h1
      have key : (⇑(multiplicationByN (G := W.toAffine.Point) (k + 2)) : W.toAffine.Point → W.toAffine.Point) =
          fun P => (multiplicationByN (G := W.toAffine.Point) (k + 1)) P + id P := by
        funext P
        simp only [multiplicationByN, nsmulAddMonoidHom_apply, id]
        rw [show k + 2 = (k + 1) + 1 from rfl, add_smul, one_smul]
      rw [key]
      exact isMorphismOfCurves_add hmor isMorphismOfCurves_id

/-- Multiplication-by-$n$ on $E$ is surjective for $n > 0$ (combining nonconstancy
and `isMorphismOfCurves_nonconstant_surjective`). -/
theorem mulByN_surjective_axiom :
    {F : Type*} → [Field F] → [DecidableEq F] →
    (W : WeierstrassCurve F) → [W.IsElliptic] →
    (n : ℕ) → 0 < n →
    Function.Surjective (multiplicationByN (G := W.toAffine.Point) n) := by
  intro F _ _ W _ n hn
  exact isMorphismOfCurves_nonconstant_surjective W
    (multiplicationByN n)
    (mulByN_isMorphism_axiom W n hn)
    (map_zero _)
    (mulByN_nonconstant W n hn)

section Theorem248

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} [W.IsElliptic]

/-- Restatement of `mulByN_surjective_axiom` for use inside the
`Theorem248` section. -/
theorem multiplicationByN_surjective (n : ℕ) (hn : 0 < n) :
    Function.Surjective (multiplicationByN (G := W.toAffine.Point) n) :=
  mulByN_surjective_axiom W n hn

/-- Theorem 24.8: the multiplication-by-$n$ map $[n] : E \to E$ is an isogeny of
elliptic curves for every $n > 0$. -/
noncomputable def multiplicationByN_isogeny (n : ℕ) (hn : 0 < n) :
    EllipticCurveIsogeny W W where
  toFun := multiplicationByN n
  is_morphism := mulByN_isMorphism_axiom W n hn
  surjective := multiplicationByN_surjective n hn
  map_zero := map_zero _

end Theorem248

section Corollary2410

variable {F : Type*} [Field F] [DecidableEq F] {W : WeierstrassCurve F} [W.IsElliptic]

/-- Corollary 24.10: the $n$-torsion subgroup $E[n] \subseteq E(F)$ is finite. -/
theorem nTorsion_finite (n : ℕ) (hn : 0 < n) :
    Set.Finite ((nTorsionSubgroup (G := W.toAffine.Point) n : Set W.toAffine.Point)) := by
  have h := EllipticCurveIsogeny.ker_finite (@multiplicationByN_isogeny _ _ _ W _ n hn)
  apply h.subset
  intro P hP
  rw [SetLike.mem_coe] at hP ⊢
  rw [EllipticCurveIsogeny.mem_ker]
  simp only [multiplicationByN_isogeny]
  change (multiplicationByN n) P = 0
  rw [nTorsionSubgroup, AddMonoidHom.mem_ker] at hP
  simp [multiplicationByN, hP]

end Corollary2410
open scoped Classical in
/-- Variant of Corollary 24.10 over an algebraic closure: $E(\bar k)[n]$ is finite. -/
theorem nTorsion_finite_algClosure {k : Type*} [Field k]
    {W : WeierstrassCurve k} [W.IsElliptic] (n : ℕ) (hn : 0 < n) :
    Set.Finite ((nTorsionSubgroup
      (G := (W.baseChange (AlgebraicClosure k)).toAffine.Point) n :
      Set (W.baseChange (AlgebraicClosure k)).toAffine.Point)) :=
  nTorsion_finite (W := W.baseChange (AlgebraicClosure k)) n hn

/-- The base change of an elliptic curve $E/\mathbb{Q}$ to $\mathbb{Q}_p$ remains
elliptic (its discriminant remains a unit). -/
noncomputable instance baseChange_padic_isElliptic
    {p : ℕ} [Fact (Nat.Prime p)]
    {W : WeierstrassCurve ℚ} [W.IsElliptic] :
    (W.baseChange ℚ_[p]).IsElliptic := by
  constructor
  rw [show (W.baseChange ℚ_[p]).Δ = algebraMap ℚ ℚ_[p] W.Δ by
    simp [WeierstrassCurve.baseChange, WeierstrassCurve.Δ]]
  exact (algebraMap ℚ ℚ_[p]).isUnit_map ‹W.IsElliptic›.isUnit

/-- Membership in the $n$-th piece of the $p$-adic filtration on $E(\mathbb{Q}_p)$:
the point $O$ is always in, and an affine point $(x, y)$ lies in $E_n$ when $n = 0$
or when $y \neq 0$ and $v_p(x) - v_p(y) \geq n$. -/
def PadicFiltrationMem (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ)
    (P : (W.baseChange ℚ_[p]).toAffine.Point) : Prop :=
  match P with
  | .zero => True
  | .some x y _ => n = 0 ∨ (y ≠ 0 ∧ (n : ℤ) ≤ Padic.valuation x - Padic.valuation y)


/-- The identity point lies in every piece $E_n$ of the $p$-adic filtration. -/
theorem PadicFiltrationMem.zero (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    PadicFiltrationMem W p n (.zero) :=
  trivial

/-- The filtration is monotone: if $P \in E_n$ and $m \leq n$, then $P \in E_m$. -/
theorem PadicFiltrationMem.of_le {W : WeierstrassCurve ℚ} [W.IsElliptic]
    {p : ℕ} [Fact (Nat.Prime p)] {n m : ℕ}
    {P : (W.baseChange ℚ_[p]).toAffine.Point}
    (h : PadicFiltrationMem W p n P) (hmn : m ≤ n) :
    PadicFiltrationMem W p m P := by
  match P with
  | .zero => trivial
  | .some x y hxy =>
    simp only [PadicFiltrationMem] at h ⊢
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact Or.inl rfl
    · right
      rcases h with rfl | ⟨hy, hv⟩
      · omega
      · exact ⟨hy, le_trans (by exact_mod_cast hmn) hv⟩

noncomputable section

open Classical

/-- The $p$-adic filtration on $E(\mathbb{Q}_p)$: a decreasing family of
subgroups $E = E_0 \supseteq E_1 \supseteq E_2 \supseteq \cdots$ defined via
the $p$-adic valuation, together with the (mild) assumptions
$a_1 = a_2 = a_3 = 0$ required for the addition-formula computations. -/
structure PadicFiltration (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (p : ℕ) [Fact (Nat.Prime p)] where
  group : ℕ → AddSubgroup (W.baseChange ℚ_[p]).toAffine.Point
  antitone : Antitone group
  mem_iff : ∀ n P, P ∈ group n ↔ PadicFiltrationMem W p n P
  zero_eq_top : group 0 = ⊤
  ha₁ : W.a₁ = 0
  ha₂ : W.a₂ = 0
  ha₃ : W.a₃ = 0

/-- The $p$-adic valuation is invariant under negation: $v_p(-x) = v_p(x)$. -/
lemma padic_valuation_neg {p : ℕ} [Fact (Nat.Prime p)] (x : ℚ_[p]) (hx : x ≠ 0) :
    Padic.valuation (-x) = Padic.valuation x := by
  have hx' : -x ≠ 0 := neg_ne_zero.mpr hx
  have h1 := Padic.norm_eq_zpow_neg_valuation hx
  have h2 := Padic.norm_eq_zpow_neg_valuation hx'
  rw [norm_neg] at h2
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : Nat.Prime p).one_lt
  exact neg_injective ((zpow_right_strictMono₀ hp).injective (h2.symm.trans h1))


/-- Strict (non-Archimedean) triangle inequality: if $v_p(x) \neq v_p(y)$,
then $v_p(x+y) = \min(v_p(x), v_p(y))$. -/
lemma padic_valuation_add_eq_min {p : ℕ} [Fact (Nat.Prime p)] {x y : ℚ_[p]}
    (hxy : x + y ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hv : Padic.valuation x ≠ Padic.valuation y) :
    Padic.valuation (x + y) = min (Padic.valuation x) (Padic.valuation y) := by
  have h1 := Padic.le_valuation_add hxy
  have h2 : min (Padic.valuation (x + y)) (Padic.valuation y) ≤ Padic.valuation x := by
    have h := Padic.le_valuation_add (show (x + y) + (-y) ≠ 0 by rwa [add_neg_cancel_right])
    rwa [padic_valuation_neg y hy, add_neg_cancel_right] at h
  have h3 : min (Padic.valuation (x + y)) (Padic.valuation x) ≤ Padic.valuation y := by
    have h := Padic.le_valuation_add (show (x + y) + (-x) ≠ 0 by
      rwa [show (x + y) + (-x) = y from by ring])
    rwa [padic_valuation_neg x hx, show (x + y) + (-x) = y from by ring] at h
  omega


/-- Subtractive form of the strict triangle inequality: if $v_p(x) \neq v_p(y)$,
then $v_p(x - y) = \min(v_p(x), v_p(y))$. -/
lemma padic_valuation_sub_eq_min {p : ℕ} [Fact (Nat.Prime p)] {x y : ℚ_[p]}
    (hxy : x - y ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hv : Padic.valuation x ≠ Padic.valuation y) :
    Padic.valuation (x - y) = min (Padic.valuation x) (Padic.valuation y) := by
  rw [sub_eq_add_neg] at hxy ⊢
  rw [padic_valuation_add_eq_min hxy hx (neg_ne_zero.mpr hy)
      (by rwa [padic_valuation_neg y hy]),
    padic_valuation_neg y hy]


/-- The $n$-th level $E_n$ of the $p$-adic filtration is closed under addition:
if $P, Q \in E_n$ then $P + Q \in E_n$. -/
theorem PadicFiltrationMem.add_mem {W : WeierstrassCurve ℚ} [W.IsElliptic]
    (ha₁ : W.a₁ = 0) (ha₂ : W.a₂ = 0) (ha₃ : W.a₃ = 0)
    {p : ℕ} [Fact (Nat.Prime p)] {n : ℕ}
    {P Q : (W.baseChange ℚ_[p]).toAffine.Point}
    (hP : PadicFiltrationMem W p n P) (hQ : PadicFiltrationMem W p n Q) :
    PadicFiltrationMem W p n (P + Q) := by

  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    match P + Q with
    | .zero => trivial
    | .some _ _ _ => exact Or.inl rfl
  ·
    match P, Q with
    | .zero, _ =>

      exact hQ
    | _, .zero =>

      convert hP using 1
      exact add_zero _
    | .some x₁ y₁ h₁, .some x₂ y₂ h₂ =>


      simp only [PadicFiltrationMem] at hP hQ
      have hP' : y₁ ≠ 0 ∧ (n : ℤ) ≤ Padic.valuation x₁ - Padic.valuation y₁ := by
        rcases hP with rfl | h
        · omega
        · exact h
      have hQ' : y₂ ≠ 0 ∧ (n : ℤ) ≤ Padic.valuation x₂ - Padic.valuation y₂ := by
        rcases hQ with rfl | h
        · omega
        · exact h

      by_cases hxy : x₁ = x₂ ∧ y₁ = (W.baseChange ℚ_[p]).toAffine.negY x₂ y₂
      ·
        rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2]
        trivial
      ·
        rw [WeierstrassCurve.Affine.Point.add_some hxy]
        simp only [PadicFiltrationMem]
        right


        exact PadicElliptic.addition_formula_preserves_valuation W ha₁ ha₂ ha₃ n h₁ h₂ hxy hP' hQ'

/-- The $n$-th level $E_n$ of the $p$-adic filtration is closed under negation:
if $P \in E_n$ then $-P \in E_n$. -/
theorem PadicFiltrationMem.neg_mem {W : WeierstrassCurve ℚ} [W.IsElliptic]
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0)
    {p : ℕ} [Fact (Nat.Prime p)] {n : ℕ}
    {P : (W.baseChange ℚ_[p]).toAffine.Point}
    (hP : PadicFiltrationMem W p n P) :
    PadicFiltrationMem W p n (-P) := by
  match P with
  | .zero => trivial
  | .some x y hxy =>
    show n = 0 ∨ ((W.baseChange ℚ_[p]).toAffine.negY x y ≠ 0 ∧
      (n : ℤ) ≤ Padic.valuation x - Padic.valuation ((W.baseChange ℚ_[p]).toAffine.negY x y))
    have ha₁' : (W.baseChange ℚ_[p]).toAffine.a₁ = 0 := by
      simp [WeierstrassCurve.toAffine, WeierstrassCurve.baseChange, ha₁]
    have ha₃' : (W.baseChange ℚ_[p]).toAffine.a₃ = 0 := by
      simp [WeierstrassCurve.toAffine, WeierstrassCurve.baseChange, ha₃]
    have hneq : (W.baseChange ℚ_[p]).toAffine.negY x y = -y := by
      simp only [WeierstrassCurve.Affine.negY, ha₁', ha₃', zero_mul, sub_zero]
    rw [hneq]
    simp only [PadicFiltrationMem] at hP
    rcases hP with rfl | ⟨hy, hv⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨neg_ne_zero.mpr hy, by rw [padic_valuation_neg y hy]; exact hv⟩

/-- The $n$-th level $E_n$ of the $p$-adic filtration, packaged as an additive
subgroup of $E(\mathbb{Q}_p)$. -/
def padicFiltrationGroup (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (ha₁ : W.a₁ = 0) (ha₂ : W.a₂ = 0) (ha₃ : W.a₃ = 0)
    (p : ℕ) [Fact (Nat.Prime p)] (n : ℕ) :
    AddSubgroup (W.baseChange ℚ_[p]).toAffine.Point where
  carrier := {P | PadicFiltrationMem W p n P}
  zero_mem' := PadicFiltrationMem.zero W p n
  add_mem' ha hb := PadicFiltrationMem.add_mem ha₁ ha₂ ha₃ ha hb
  neg_mem' ha := PadicFiltrationMem.neg_mem ha₁ ha₃ ha

/-- Existence of the $p$-adic filtration on $E(\mathbb{Q}_p)$ for a Weierstrass
curve with $a_1 = a_2 = a_3 = 0$. -/
theorem PadicFiltration.exists (W : WeierstrassCurve ℚ) [W.IsElliptic]
    (ha₁ : W.a₁ = 0) (ha₂ : W.a₂ = 0) (ha₃ : W.a₃ = 0)
    (p : ℕ) [Fact (Nat.Prime p)] : Nonempty (PadicFiltration W p) := by
  exact ⟨{
    group := padicFiltrationGroup W ha₁ ha₂ ha₃ p

    antitone := by
      intro m n hmn P hP
      show PadicFiltrationMem W p m P
      have hPn : PadicFiltrationMem W p n P := hP
      exact PadicFiltrationMem.of_le hPn hmn
    mem_iff := by
      intro n P
      exact Iff.rfl
    zero_eq_top := by
      ext P
      simp only [AddSubgroup.mem_top, iff_true]
      show PadicFiltrationMem W p 0 P
      match P with
      | .zero => trivial
      | .some x y _ => exact Or.inl rfl
    ha₁ := ha₁
    ha₂ := ha₂
    ha₃ := ha₃
  }⟩

namespace PadicFiltration

variable {W : WeierstrassCurve ℚ} [W.IsElliptic]
variable {p : ℕ} [Fact (Nat.Prime p)]
variable (F : PadicFiltration W p)


/-- If reduction modulo $p$ is surjective on $E(\mathbb{Q}_p)$, then it remains
surjective when restricted to $E_0 = E(\mathbb{Q}_p)$. -/
lemma hensel_reduction_surjective
    (Wred : WeierstrassCurve (ZMod p)) [Wred.IsElliptic]
    (red : (W.baseChange ℚ_[p]).toAffine.Point →+ Wred.toAffine.Point)
    (hred_surj : Function.Surjective red) :
    Function.Surjective (red.comp (F.group 0).subtype) := by
  intro q
  obtain ⟨x, hx⟩ := hred_surj q
  have hx_mem : x ∈ F.group 0 := by rw [F.zero_eq_top]; exact AddSubgroup.mem_top x
  exact ⟨⟨x, hx_mem⟩, hx⟩

/-- The reduction map $\rho: E_0 \to \widetilde{E}(\mathbb{F}_p)$ is surjective
with kernel $E_1$. -/
theorem reduction_surjective_with_kernel
    (Wred : WeierstrassCurve (ZMod p)) [Wred.IsElliptic]
    (red : (W.baseChange ℚ_[p]).toAffine.Point →+ Wred.toAffine.Point)
    (hred_surj : Function.Surjective red)
    (hred_ker : red.ker = F.group 1) :
    ∃ (ρ : ↥(F.group 0) →+ Wred.toAffine.Point),
      Function.Surjective ρ ∧ ρ.ker = (F.group 1).addSubgroupOf (F.group 0) := by
  refine ⟨red.comp (F.group 0).subtype,
    F.hensel_reduction_surjective Wred red hred_surj, ?_⟩
  ext ⟨x, hx⟩
  simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply,
    AddSubgroup.mem_addSubgroupOf, ← hred_ker, AddMonoidHom.mem_ker,
    AddSubgroup.coe_subtype]

/-- The first isomorphism theorem applied to the reduction map gives
$E_0/E_1 \cong \widetilde{E}(\mathbb{F}_p)$. -/
theorem quotient_zero_one_iso
    (Wred : WeierstrassCurve (ZMod p)) [Wred.IsElliptic]
    (red : (W.baseChange ℚ_[p]).toAffine.Point →+ Wred.toAffine.Point)
    (hred_surj : Function.Surjective red)
    (hred_ker : red.ker = F.group 1) :
    Nonempty (↥(F.group 0) ⧸ (F.group 1).addSubgroupOf (F.group 0) ≃+ Wred.toAffine.Point) := by
  obtain ⟨ρ, hρ_surj, hρ_ker⟩ := F.reduction_surjective_with_kernel Wred red hred_surj hred_ker
  rw [← hρ_ker]
  exact ⟨QuotientAddGroup.quotientKerEquivOfSurjective ρ hρ_surj⟩

/-- For $n > 0$, the predicate `PadicFiltrationMem` agrees with the
`PadicElliptic.InPadicFiltration` predicate from the formal-group development. -/
lemma padicFiltrationMem_iff_inPadicFiltration (n : ℕ) (hn : 0 < n)
    (P : (W.baseChange ℚ_[p]).toAffine.Point) :
    PadicFiltrationMem W p n P ↔ PadicElliptic.InPadicFiltration W n P := by
  match P with
  | .zero => simp [PadicFiltrationMem, PadicElliptic.InPadicFiltration]
  | .some x y _ =>
    simp only [PadicFiltrationMem, PadicElliptic.InPadicFiltration]
    constructor
    · intro h
      rcases h with rfl | h
      · omega
      · exact h
    · exact Or.inr

/-- For $n > 0$, the subgroup $E_n$ of the filtration coincides with the
$n$-th level of `PadicElliptic.padicFiltration`. -/
lemma group_eq_padicFiltration (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0)
    (n : ℕ) (hn : 0 < n) :
    F.group n = PadicElliptic.padicFiltration W ha1 ha2 ha3 n := by
  ext P
  rw [F.mem_iff n P, padicFiltrationMem_iff_inPadicFiltration n hn P]
  rfl

/-- For $n > 0$, the formal logarithm provides a surjective homomorphism
$E_n \to \mathbb{F}_p$ with kernel $E_{n+1}$. -/
theorem formal_group_surjective_with_kernel (n : ℕ) (hn : 0 < n) :
    ∃ (logMap : ↥(F.group n) →+ ZMod p),
      Function.Surjective logMap ∧ logMap.ker = (F.group (n + 1)).addSubgroupOf (F.group n) := by
  have heqn := F.group_eq_padicFiltration F.ha₁ F.ha₂ F.ha₃ n hn
  have heqn1 := F.group_eq_padicFiltration F.ha₁ F.ha₂ F.ha₃ (n + 1) (by omega)
  rw [heqn, heqn1]
  exact PadicElliptic.exists_surjective_reduction_hom W F.ha₁ F.ha₂ F.ha₃ n hn

/-- For $n > 0$, the successive quotient of the filtration is isomorphic to
$\mathbb{F}_p$: $E_n / E_{n+1} \cong \mathbb{F}_p$. -/
theorem quotient_succ_iso (n : ℕ) (hn : 0 < n) :
    Nonempty (↥(F.group n) ⧸ (F.group (n + 1)).addSubgroupOf (F.group n) ≃+ ZMod p) := by
  obtain ⟨logMap, hlog_surj, hlog_ker⟩ := F.formal_group_surjective_with_kernel n hn
  rw [← hlog_ker]
  exact ⟨QuotientAddGroup.quotientKerEquivOfSurjective logMap hlog_surj⟩

/-- The $p$-adic filtration is separated: $\bigcap_{n \geq 0} E_n = 0$. -/
theorem iInf_eq_bot :
    ⨅ n, F.group n = ⊥ := by
  rw [eq_bot_iff]
  intro P hP
  rw [AddSubgroup.mem_iInf] at hP
  rw [AddSubgroup.mem_bot]
  match P with
  | .zero => rfl
  | .some x y hxy =>
    exfalso
    have hmem : ∀ n : ℕ, PadicFiltrationMem W p n (.some x y hxy) := fun n =>
      (F.mem_iff n _).mp (hP n)
    have hval : ∀ k : ℕ, (k.succ : ℤ) ≤ Padic.valuation x - Padic.valuation y := by
      intro k
      rcases hmem k.succ with h | ⟨_, hv⟩
      · exact absurd h (Nat.succ_ne_zero k)
      · exact hv
    have : ¬ (∀ k : ℕ, (k.succ : ℤ) ≤ Padic.valuation x - Padic.valuation y) := by
      push Not
      exact ⟨(Padic.valuation x - Padic.valuation y).toNat, by omega⟩
    exact this hval

/-- Theorem 24.14 (Reduction theorem for the $p$-adic filtration).
The successive quotients of $E_0 \supseteq E_1 \supseteq E_2 \supseteq \cdots$
are:
\begin{itemize}
  \item $E_0/E_1 \cong \widetilde{E}(\mathbb{F}_p)$ (reduction modulo $p$),
  \item $E_n/E_{n+1} \cong \mathbb{F}_p$ for all $n \geq 1$ (via the formal logarithm),
  \item $\bigcap_n E_n = 0$ (the filtration is separated).
\end{itemize} -/
theorem theorem_24_14
    (Wred : WeierstrassCurve (ZMod p)) [Wred.IsElliptic]
    (red : (W.baseChange ℚ_[p]).toAffine.Point →+ Wred.toAffine.Point)
    (hred_surj : Function.Surjective red)
    (hred_ker : red.ker = F.group 1) :

    (Nonempty (↥(F.group 0) ⧸ (F.group 1).addSubgroupOf (F.group 0) ≃+ Wred.toAffine.Point)) ∧

    (∀ n : ℕ, 0 < n →
      Nonempty (↥(F.group n) ⧸ (F.group (n + 1)).addSubgroupOf (F.group n) ≃+ ZMod p)) ∧

    (⨅ n, F.group n = ⊥) :=
  ⟨F.quotient_zero_one_iso Wred red hred_surj hred_ker,
   fun n hn => F.quotient_succ_iso n hn,
   F.iInf_eq_bot⟩

end PadicFiltration

end

noncomputable section

open Classical

/-- If $p$ is prime, $\gcd(m, p) = 1$, and $m \cdot x = 0$ in $\mathbb{F}_p$,
then $x = 0$. (Multiplication by an integer coprime to $p$ is injective on
$\mathbb{F}_p$.) -/
lemma nsmul_eq_zero_in_zmod_prime {p : ℕ} (hp : Nat.Prime p)
    (m : ℕ) (hm : Nat.Coprime m p) (x : ZMod p) (h : m • x = 0) : x = 0 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  rw [nsmul_eq_mul] at h
  rcases mul_eq_zero.mp h with hm0 | hx0
  · rw [ZMod.natCast_eq_zero_iff m p] at hm0
    have : p ∣ Nat.gcd m p := Nat.dvd_gcd hm0 (dvd_refl p)
    rw [hm] at this
    exact absurd this (Nat.Prime.not_dvd_one hp)
  · exact hx0

/-- Predicate: an affine point $P = (x, y) \in E(\mathbb{Q}_p)$ has
$p$-adically integral coordinates, i.e. $v_p(x) \geq 0$ and $v_p(y) \geq 0$
(the point at infinity is vacuously integral). -/
def CoordinatesPadicIntegral {W : WeierstrassCurve ℚ} [W.IsElliptic]
    {p : ℕ} [Fact (Nat.Prime p)]
    (P : (W.baseChange ℚ_[p]).toAffine.Point) : Prop :=
  match P with
  | .zero => True
  | .some x y _ => 0 ≤ Padic.valuation x ∧ 0 ≤ Padic.valuation y

/-- Valuation bound from the Weierstrass equation: if the coefficients $a_i$
are $p$-integral and the point $(x, y)$ on $E$ does not have integral
coordinates, then $y \neq 0$ and $v_p(x) - v_p(y) \geq 1$. -/
theorem weierstrass_valuation_bound
    {W : WeierstrassCurve ℚ} [W.IsElliptic]
    {p : ℕ} [Fact (Nat.Prime p)]
    (h_coeff : 0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₁) ∧
               0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₂) ∧
               0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₃) ∧
               0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₄) ∧
               0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₆))
    {x y : ℚ_[p]} (h : (W.baseChange ℚ_[p]).toAffine.Nonsingular x y)
    (h_not_int : ¬ (0 ≤ Padic.valuation x ∧ 0 ≤ Padic.valuation y)) :
    y ≠ 0 ∧ (1 : ℤ) ≤ Padic.valuation x - Padic.valuation y :=
  weierstrass_valuation_bound_proof h_coeff h h_not_int

/-- A point with non-integral coordinates lies in $E_1$ (in fact in some $E_n$
with $n > 0$) but does not lie in every $E_k$, since the filtration is
separated. -/
theorem non_integral_implies_in_filtration
    {W : WeierstrassCurve ℚ} [W.IsElliptic]
    {p : ℕ} [Fact (Nat.Prime p)]
    (h_coeff : 0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₁) ∧
               0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₂) ∧
               0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₃) ∧
               0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₄) ∧
               0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₆))
    (F : PadicFiltration W p)
    (P : (W.baseChange ℚ_[p]).toAffine.Point)
    (h_not_integral : ¬ CoordinatesPadicIntegral P) :
    ∃ n : ℕ, 0 < n ∧ P ∈ F.group n ∧ ¬ (∀ k : ℕ, P ∈ F.group k) := by
  match P with
  | .zero => exact absurd trivial h_not_integral
  | .some x y hxy =>

    have hval := weierstrass_valuation_bound h_coeff hxy h_not_integral
    have h_in_1 : WeierstrassCurve.Affine.Point.some x y hxy ∈ F.group 1 := by
      rw [F.mem_iff]
      show PadicFiltrationMem W p 1 (.some x y hxy)
      exact Or.inr hval

    have h_ne_zero : WeierstrassCurve.Affine.Point.some x y hxy ≠ 0 :=
      WeierstrassCurve.Affine.Point.some_ne_zero hxy
    have h_not_all : ¬ (∀ k, WeierstrassCurve.Affine.Point.some x y hxy ∈ F.group k) := by
      intro hall
      have h_in_bot : WeierstrassCurve.Affine.Point.some x y hxy ∈
          (⊥ : AddSubgroup (W.baseChange ℚ_[p]).toAffine.Point) := by
        rw [← F.iInf_eq_bot]
        exact AddSubgroup.mem_iInf.mpr hall
      rw [AddSubgroup.mem_bot] at h_in_bot
      exact h_ne_zero h_in_bot
    exact ⟨1, Nat.one_pos, h_in_1, h_not_all⟩

/-- Corollary 24.16. Let $E$ be an elliptic curve over $\mathbb{Q}$ with
$p$-integral Weierstrass coefficients, and let $P \in E(\mathbb{Q}_p)$. If
$m \cdot P = 0$ for some integer $m$ with $\gcd(m, p) = 1$, then the
coordinates of $P$ are $p$-adically integral. -/
theorem cor_24_16_padic_integrality
    {W : WeierstrassCurve ℚ} [W.IsElliptic]
    {p : ℕ} [hp : Fact (Nat.Prime p)]
    (h_coeff : 0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₁) ∧
               0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₂) ∧
               0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₃) ∧
               0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₄) ∧
               0 ≤ Padic.valuation (algebraMap ℚ ℚ_[p] W.a₆))
    (F : PadicFiltration W p)
    (P : (W.baseChange ℚ_[p]).toAffine.Point)
    (m : ℕ) (hm_coprime : Nat.Coprime m p)
    (hmP : m • P = 0)
    : CoordinatesPadicIntegral P := by

  by_contra h_not_integral


  obtain ⟨n₀, hn₀_pos, hPn₀, h_not_all⟩ :=
    non_integral_implies_in_filtration h_coeff F P h_not_integral
  push Not at h_not_all
  obtain ⟨k₀, hk₀⟩ := h_not_all

  have hne : ∃ i, P ∉ F.group i := ⟨k₀, hk₀⟩
  have i₀_spec := Nat.find_spec hne

  have hP_in_E0 : P ∈ F.group 0 := by rw [F.zero_eq_top]; exact AddSubgroup.mem_top P
  have i₀_ge2 : 2 ≤ Nat.find hne := by
    by_contra h; push Not at h
    interval_cases (Nat.find hne)
    · exact i₀_spec hP_in_E0
    · exact i₀_spec (F.antitone (by omega : 1 ≤ n₀) hPn₀)

  set j := Nat.find hne - 1 with hj_def
  have hj_pos : 0 < j := by omega
  have hPj : P ∈ F.group j := by
    by_contra h; exact Nat.find_min hne (by omega) h
  have hPj1 : P ∉ F.group (j + 1) := by
    rwa [show j + 1 = Nat.find hne from by omega]

  have hiso := F.quotient_succ_iso j hj_pos
  let φ := hiso.some

  let Psub : ↥(F.group j) := ⟨P, hPj⟩

  let q : ↥(F.group j) ⧸ (F.group (j + 1)).addSubgroupOf (F.group j) :=
    QuotientAddGroup.mk Psub

  let z : ZMod p := φ q

  have hz_ne : z ≠ 0 := by
    intro hz
    have hq_zero : q = 0 := by
      have := φ.injective
      rw [show (0 : ZMod p) = φ 0 from (map_zero φ).symm] at hz
      exact this hz
    rw [QuotientAddGroup.eq_zero_iff] at hq_zero
    exact hPj1 (AddSubgroup.mem_addSubgroupOf.mp hq_zero)

  have hPsub_killed : m • Psub = 0 := by
    apply Subtype.ext
    show m • P = 0
    exact hmP
  have hq_killed : m • q = 0 := by
    have := map_nsmul (QuotientAddGroup.mk' ((F.group (j + 1)).addSubgroupOf (F.group j))) m Psub
    rw [hPsub_killed, map_zero] at this
    exact this.symm
  have hz_killed : m • z = 0 := by
    have := map_nsmul φ m q
    rw [hq_killed, map_zero] at this
    exact this.symm

  exact hz_ne (nsmul_eq_zero_in_zmod_prime hp.out m hm_coprime z hz_killed)

end
