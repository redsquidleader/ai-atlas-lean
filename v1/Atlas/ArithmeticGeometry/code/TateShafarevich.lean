/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ArithmeticGeometry.code.WeilChatelet
import Atlas.ArithmeticGeometry.code.GaloisCohomology
import Atlas.ArithmeticGeometry.code.WCGroupH1

noncomputable section

universe u

open NumberField GaloisCohomology

/-- An elliptic curve over a field $k$: a Weierstrass curve together with the (instance)
witness that it is elliptic, i.e. that its discriminant is invertible. -/
structure EllipticCurveOver (k : Type u) [Field k] where
  curve : WeierstrassCurve k
  [isElliptic : curve.IsElliptic]

/-- A genus-one curve over $k$ together with its Jacobian (an elliptic curve over $k$) and a
chosen Weierstrass model over the algebraic closure. -/
structure GenusOneCurve (k : Type u) [Field k] where
  Jacobian : EllipticCurveOver k
  weierstrassModel :
    (Jacobian.curve.baseChange (AlgebraicClosure k)).toAffine.Point →
    WeierstrassCurve.VariableChange (AlgebraicClosure k)

/-- A *place* of a number field $k$ is either an infinite place (an archimedean valuation) or a
finite place (a nonarchimedean valuation), packaged as a sum type. -/
def NumberFieldPlace (k : Type u) [Field k] [NumberField k] : Type u :=
  NumberField.InfinitePlace k ⊕ NumberField.FinitePlace k

/-- Inject an infinite place into the disjoint union `NumberFieldPlace k`. -/
def NumberFieldPlace.infinite {k : Type u} [Field k] [NumberField k]
    (v : NumberField.InfinitePlace k) : NumberFieldPlace k :=
  Sum.inl v

/-- Inject a finite place into the disjoint union `NumberFieldPlace k`. -/
def NumberFieldPlace.finite {k : Type u} [Field k] [NumberField k]
    (v : NumberField.FinitePlace k) : NumberFieldPlace k :=
  Sum.inr v

/-- The Weil-Châtelet group $\mathrm{WC}(E/k)$ of an elliptic curve $E/k$: the set of
$E$-torsors modulo $k$-isomorphism. -/
abbrev WeilChateletGroup {k : Type u} [Field k] (E : EllipticCurveOver k) : Type (u + 1) :=
  haveI := E.isElliptic
  WC k E.curve (ECurvePointsAlgClosure k E.curve)

/-- The transported additive commutative group structure on the Weil-Châtelet group, coming from
its bijection with the first Galois cohomology group $H^1$. -/
noncomputable instance instAddCommGroupWeilChateletGroup {k : Type u} [Field k]
    (E : EllipticCurveOver k) : AddCommGroup (WeilChateletGroup E) :=
  haveI := E.isElliptic
  WC.addCommGroupOfData (WCH1Data.mk' k E.curve (ECurvePointsAlgClosure k E.curve)
    (AbsGaloisGroup k))

/-- The first Galois cohomology group
$H^1(\mathrm{Gal}(\bar k/k), E(\bar k))$ realising the Weil-Châtelet group of $E/k$. -/
abbrev GaloisCohomologyH1 (k : Type u) [Field k] (E : EllipticCurveOver k) : Type u :=
  WeilChateletGroupReal k E.curve

/-- The Galois cohomology group inherits its additive commutative group structure from the
underlying $H^1$ construction. -/
instance GaloisCohomologyH1.instAddCommGroup (k : Type u) [Field k]
    (E : EllipticCurveOver k) : AddCommGroup (GaloisCohomologyH1 k E) :=
  inferInstance

/-- The isomorphism between the Weil-Châtelet group of $E/k$ (torsors mod $k$-isomorphism) and
the first Galois cohomology group $H^1(\mathrm{Gal}(\bar k/k), E(\bar k))$. -/
noncomputable def WeilChatelet_iso_H1 {k : Type u} [Field k] (E : EllipticCurveOver k) :
    WeilChateletGroup E ≃+ GaloisCohomologyH1 k E :=
  haveI := E.isElliptic
  wc_h1_equiv (WCH1Data.mk' k E.curve (ECurvePointsAlgClosure k E.curve)
    (AbsGaloisGroup k))


/-- The class in the Weil-Châtelet group $\mathrm{WC}(\mathrm{Jac}(C)/k)$ associated to a
genus-one curve $C$ over $k$. -/
noncomputable def GenusOneCurve.wcClass {k : Type u} [Field k]
    (C : GenusOneCurve k) : WeilChateletGroup C.Jacobian := by sorry

/-- The local Weil-Châtelet group $\mathrm{WC}(E/k_v)$ obtained by base change of $E$ to the
completion of $k$ at the place $v$. -/
noncomputable def WeilChateletGroupLocal {k : Type u} [Field k] [NumberField k]
    (E : EllipticCurveOver k) (v : NumberFieldPlace k) : Type (u + 1) := by sorry

/-- The local Weil-Châtelet group carries an additive commutative group structure. -/
noncomputable instance instAddCommGroupWeilChateletGroupLocal {k : Type u} [Field k] [NumberField k]
    (E : EllipticCurveOver k) (v : NumberFieldPlace k) :
    AddCommGroup (WeilChateletGroupLocal E v) := by sorry

attribute [instance] instAddCommGroupWeilChateletGroupLocal

/-- Localization map $\mathrm{WC}(E/k) \to \mathrm{WC}(E/k_v)$ sending each torsor over $k$ to
its base change over the completion $k_v$. -/
noncomputable def localizationMap {k : Type u} [Field k] [NumberField k]
    (E : EllipticCurveOver k) (v : NumberFieldPlace k) :
    WeilChateletGroup E →+ WeilChateletGroupLocal E v := by sorry

/-- A genus-one curve has a rational point iff its Weil-Châtelet class vanishes, i.e.
$[C] = 0 \in \mathrm{WC}(\mathrm{Jac}(C)/k)$. -/
def GenusOneCurve.HasRationalPoint {k : Type u} [Field k] (C : GenusOneCurve k) : Prop :=
  C.wcClass = 0

/-- A genus-one curve has a local point at the place $v$ iff its localized Weil-Châtelet class
vanishes in $\mathrm{WC}(\mathrm{Jac}(C)/k_v)$. -/
def GenusOneCurve.HasLocalPoint {k : Type u} [Field k] [NumberField k]
    (C : GenusOneCurve k) (v : NumberFieldPlace k) : Prop :=
  localizationMap C.Jacobian v C.wcClass = 0

/-- A genus-one curve $C/k$ is *locally trivial* (has a point everywhere locally) if it has a
local point at every place $v$ of the number field $k$. -/
def GenusOneCurve.IsLocallyTrivial {k : Type u} [Field k] [NumberField k]
    (C : GenusOneCurve k) : Prop :=
  ∀ v : NumberFieldPlace k, C.HasLocalPoint v

/-- The Hasse local-global principle holds for $C$ if local triviality implies the existence of a
global rational point. -/
def SatisfiesLocalGlobalPrinciple {k : Type u} [Field k] [NumberField k]
    (C : GenusOneCurve k) : Prop :=
  C.IsLocallyTrivial → C.HasRationalPoint

/-- The local-global principle *fails* for $C$ if $C$ is locally trivial but has no global rational
point — a counterexample witnessing nontriviality of Шafarevich-Tate. -/
def FailsLocalGlobalPrinciple {k : Type u} [Field k] [NumberField k]
    (C : GenusOneCurve k) : Prop :=
  C.IsLocallyTrivial ∧ ¬C.HasRationalPoint

/-- Unfolding lemma: $C$ has a rational point iff $[C] = 0$ in the Weil-Châtelet group. -/
theorem GenusOneCurve.hasRationalPoint_iff_trivial {k : Type u} [Field k]
    (C : GenusOneCurve k) :
    C.HasRationalPoint ↔ C.wcClass = 0 :=
  Iff.rfl

/-- Unfolding lemma: $C$ has a local point at $v$ iff its localization vanishes at $v$. -/
theorem GenusOneCurve.hasLocalPoint_iff_localization_trivial {k : Type u} [Field k]
    [NumberField k] (C : GenusOneCurve k) (v : NumberFieldPlace k) :
    C.HasLocalPoint v ↔ localizationMap C.Jacobian v C.wcClass = 0 :=
  Iff.rfl

/-- Definition 26.26: the *Tate-Shafarevich group* $\Sha(E/k)$ is the kernel of the product of
localization maps; equivalently, $\Sha(E/k) = \bigcap_v \ker(\mathrm{WC}(E/k) \to \mathrm{WC}(E/k_v))$. -/
def TateShafarevich {k : Type u} [Field k] [NumberField k]
    (E : EllipticCurveOver k) : AddSubgroup (WeilChateletGroup E) :=
  ⨅ v : NumberFieldPlace k, (localizationMap E v).ker

/-- Membership criterion: $x \in \Sha(E/k)$ iff $x$ becomes trivial in every local Weil-Châtelet
group. -/
theorem TateShafarevich.mem_iff {k : Type u} [Field k] [NumberField k]
    (E : EllipticCurveOver k) (x : WeilChateletGroup E) :
    x ∈ TateShafarevich E ↔ ∀ v : NumberFieldPlace k, localizationMap E v x = 0 := by
  simp only [TateShafarevich, AddSubgroup.mem_iInf, AddMonoidHom.mem_ker]

/-- The inclusion $\Sha(E/k) \hookrightarrow \mathrm{WC}(E/k)$ as a group homomorphism. -/
def TateShafarevich.toWC {k : Type u} [Field k] [NumberField k]
    (E : EllipticCurveOver k) : TateShafarevich E →+ WeilChateletGroup E :=
  (TateShafarevich E).subtype


/-- If a genus-one curve $C/k$ is locally trivial, then its Weil-Châtelet class lies in
$\Sha(\mathrm{Jac}(C)/k)$. -/
theorem GenusOneCurve.wcClass_mem_sha {k : Type u} [Field k] [NumberField k]
    (C : GenusOneCurve k) (h : C.IsLocallyTrivial) :
    C.wcClass ∈ TateShafarevich C.Jacobian := by
  rw [TateShafarevich.mem_iff]
  intro v
  exact (C.hasLocalPoint_iff_localization_trivial v).mp (h v)

/-- The Шa-class of a locally trivial genus-one curve: its Weil-Châtelet class, packaged as an
element of $\Sha(\mathrm{Jac}(C)/k)$. -/
def GenusOneCurve.shaClass {k : Type u} [Field k] [NumberField k]
    (C : GenusOneCurve k) (h : C.IsLocallyTrivial) :
    TateShafarevich C.Jacobian :=
  ⟨C.wcClass, C.wcClass_mem_sha h⟩


/-- The local-global principle fails for $C$ iff its Weil-Châtelet class is a nontrivial element
of the Tate-Shafarevich group $\Sha$. -/
theorem fails_local_global_iff_nontrivial_sha {k : Type u} [Field k] [NumberField k]
    (C : GenusOneCurve k) :
    FailsLocalGlobalPrinciple C ↔
    (C.wcClass ∈ TateShafarevich C.Jacobian ∧ C.wcClass ≠ 0) := by
  constructor
  ·
    intro ⟨h_loc, h_no_rat⟩
    exact ⟨C.wcClass_mem_sha h_loc, fun h_eq => h_no_rat (C.hasRationalPoint_iff_trivial.mpr h_eq)⟩
  ·
    intro ⟨h_mem, h_ne⟩
    refine ⟨fun v => ?_, fun h_rat => h_ne (C.hasRationalPoint_iff_trivial.mp h_rat)⟩
    exact (C.hasLocalPoint_iff_localization_trivial v).mpr
      ((TateShafarevich.mem_iff C.Jacobian C.wcClass).mp h_mem v)

end
