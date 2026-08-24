/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.AffineVarieties
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Opposites

open MvPolynomial

set_option autoImplicit false
set_option linter.unusedSectionVars false

variable (k : Type*) [Field k]

section Evaluation

/-- Evaluation of an element of the $\bar k$-coordinate ring $\bar k[X]$ at a point $P \in X$.
Given a class $[f] \in \bar k[X] = \bar k[X_1, \dots, X_n]/I(X)$ and a point $P \in X$, this
yields $f(P) \in \bar k$. Well-defined because $I(X)$ vanishes on $X$. -/
noncomputable def evalBarAtPoint {n : ℕ} (X : Set (Fin n → AlgebraicClosure k))
    (P : Fin n → AlgebraicClosure k) (hP : P ∈ X) :
    AffineCoordinateRingBar X →+* AlgebraicClosure k :=
  Ideal.Quotient.lift (idealOfAlgebraicSet X) (eval P) (fun _f hf => hf P hP)

/-- Compatibility of `evalBarAtPoint` with the quotient map: evaluating the class of a
polynomial $f$ at $P$ equals the ordinary polynomial evaluation $f(P)$. -/
@[simp]
theorem evalBarAtPoint_mk {n : ℕ} (X : Set (Fin n → AlgebraicClosure k))
    (P : Fin n → AlgebraicClosure k) (hP : P ∈ X)
    (f : MvPolynomial (Fin n) (AlgebraicClosure k)) :
    evalBarAtPoint k X P hP (Ideal.Quotient.mk _ f) = eval P f :=
  Ideal.Quotient.lift_mk _ _ _

end Evaluation

section RegularFunctions

variable {k}
variable {n : ℕ} {X : Set (Fin n → AlgebraicClosure k)}
variable [hdom : IsDomain (AffineCoordinateRingBar X)]

/-- Definition 15.2 (regularity at a point). A rational function
$r \in \bar k(X) = \mathrm{Frac}(\bar k[X])$ is *regular at* $P \in X$ if it can be
written as a fraction $r = f/g$ with $f, g \in \bar k[X]$ and $g(P) \neq 0$.
Equivalently: there exists $g \in \bar k[X]$ with $g(P) \neq 0$ such that $g \cdot r$
lies in the image of $\bar k[X]$ in the fraction field. -/
def IsRegularAt
    (r : FractionRing (AffineCoordinateRingBar X))
    (P : Fin n → AlgebraicClosure k)
    (hP : P ∈ X) : Prop :=
  ∃ g : AffineCoordinateRingBar X,
    evalBarAtPoint k X P hP g ≠ 0 ∧
    algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X)) g * r ∈
      Set.range (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X)))

/-- The *denominator ideal* of a rational function $r \in \bar k(X)$: the ideal of
elements $g \in \bar k[X]$ such that $g \cdot r$ lies in $\bar k[X]$. Its non-vanishing
locus is the regular locus of $r$. -/
noncomputable def denominatorIdeal
    (r : FractionRing (AffineCoordinateRingBar X)) :
    Ideal (AffineCoordinateRingBar X) where
  carrier := {g : AffineCoordinateRingBar X |
    algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X)) g * r ∈
      Set.range (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X)))}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, map_zero, zero_mul]
    exact ⟨0, map_zero _⟩
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add, add_mul] at ha hb ⊢
    obtain ⟨fa, hfa⟩ := ha
    obtain ⟨fb, hfb⟩ := hb
    exact ⟨fa + fb, by rw [map_add, hfa, hfb]⟩
  smul_mem' := by
    intro c g hg
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at hg ⊢
    rw [mul_assoc]
    obtain ⟨fg, hfg⟩ := hg
    exact ⟨c * fg, by rw [map_mul, hfg]⟩

/-- Unfolding lemma: $g \in \text{denominatorIdeal}\, r$ iff $g \cdot r$ lies in the image of
$\bar k[X]$ in $\bar k(X)$. -/
@[simp]
theorem mem_denominatorIdeal_iff
    (r : FractionRing (AffineCoordinateRingBar X))
    (g : AffineCoordinateRingBar X) :
    g ∈ denominatorIdeal r ↔
    algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X)) g * r ∈
      Set.range (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))) :=
  Iff.rfl


/-- The *regular domain* (or *regular locus*) of $r \in \bar k(X)$: the set of points
$P \in X$ at which $r$ is regular. -/
def regularDomain
    (r : FractionRing (AffineCoordinateRingBar X)) :
    Set (Fin n → AlgebraicClosure k) :=
  {P : Fin n → AlgebraicClosure k | ∃ (hP : P ∈ X), IsRegularAt r P hP}

/-- Membership in `regularDomain`: $P$ lies in the regular domain of $r$ iff $P \in X$
and $r$ is regular at $P$. -/
theorem mem_regularDomain_iff
    (r : FractionRing (AffineCoordinateRingBar X))
    (P : Fin n → AlgebraicClosure k) :
    P ∈ regularDomain r ↔ ∃ (hP : P ∈ X), IsRegularAt r P hP :=
  Iff.rfl


/-- Polynomial functions are regular everywhere: if $r = f$ comes from $\bar k[X]$, then
$r$ is regular at every point $P \in X$ (take denominator $1$). -/
theorem isRegularAt_algebraMap
    (f : AffineCoordinateRingBar X)
    (P : Fin n → AlgebraicClosure k) (hP : P ∈ X) :
    IsRegularAt (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X)) f) P hP := by
  refine ⟨1, ?_, ?_⟩
  · simp only [map_one, ne_eq, one_ne_zero, not_false_eq_true]
  · simp only [map_one, one_mul]
    exact Set.mem_range_self f

/-- The regular domain of a polynomial function $f \in \bar k[X]$, viewed as an element
of $\bar k(X)$, is all of $X$. -/
theorem regularDomain_algebraMap
    (f : AffineCoordinateRingBar X) :
    regularDomain (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X)) f) = X := by
  ext P
  simp only [regularDomain, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hP, _⟩
    exact hP
  · intro hP
    exact ⟨hP, isRegularAt_algebraMap f P hP⟩

/-- Evaluation of a rational function $r \in \bar k(X)$ at a point $P$ where $r$ is
regular: choose a representation $r = f/g$ with $g(P) \neq 0$ and return
$f(P)/g(P) \in \bar k$. The value is independent of the choice of representation
(though that is not proven here). -/
noncomputable def evalRatFunAt
    (r : FractionRing (AffineCoordinateRingBar X))
    (P : Fin n → AlgebraicClosure k) (hP : P ∈ X)
    (hreg : IsRegularAt r P hP) : AlgebraicClosure k :=
  let g := hreg.choose
  let hg := hreg.choose_spec
  let f := hg.2.choose
  evalBarAtPoint k X P hP f / evalBarAtPoint k X P hP g

/-- Key application of the Nullstellensatz: if $X$ is an algebraic subset and $J$ is an
ideal of $\bar k[X]$ with no common zero on $X$ (i.e. for every $P \in X$ there exists
$g \in J$ with $g(P) \neq 0$), then $J = \bar k[X]$ (the unit ideal). -/
theorem denominatorIdeal_eq_top_of_no_common_zero
    {k : Type*} [Field k]
    {n : ℕ} {X : Set (Fin n → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    (hAlg : IsAlgebraicSubset k n X)
    (J : Ideal (AffineCoordinateRingBar X))
    (hJ : ∀ (P : Fin n → AlgebraicClosure k) (hP : P ∈ X),
      ∃ g ∈ J, evalBarAtPoint k X P hP g ≠ 0) :
    J = ⊤ := by

  by_contra hJne

  set J' := Ideal.comap (Ideal.Quotient.mk (idealOfAlgebraicSet X)) J with hJ'_def

  have hJ'ne : J' ≠ ⊤ := by
    intro h
    apply hJne
    rw [Ideal.eq_top_iff_one] at h ⊢
    have : Ideal.Quotient.mk (idealOfAlgebraicSet X) 1 ∈ J := h
    rwa [map_one] at this

  obtain ⟨P, hPzero⟩ := weak_nullstellensatz k J' hJ'ne

  have hIX_le_J' : idealOfAlgebraicSet X ≤ J' := by
    intro x hx
    show Ideal.Quotient.mk (idealOfAlgebraicSet X) x ∈ J
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact J.zero_mem
  have hP_in_ZIX : P ∈ AlgebraicSet k n ((idealOfAlgebraicSet X) : Set _) := by
    intro f hf
    exact hPzero f (hIX_le_J' hf)

  rw [algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset (k := k) hAlg] at hP_in_ZIX

  obtain ⟨g, hgJ, hgne⟩ := hJ P hP_in_ZIX

  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective g

  have hfJ' : f ∈ J' := by
    simp only [hJ'_def, Ideal.mem_comap]
    exact hgJ

  have heval_zero : eval P f = 0 := hPzero f hfJ'

  simp only [evalBarAtPoint_mk] at hgne
  exact hgne heval_zero

/-- If $1$ lies in the denominator ideal of $r$ (equivalently, the denominator ideal is
the unit ideal), then $r$ itself is a polynomial function. -/
theorem inRange_of_one_mem_denominatorIdeal
    (r : FractionRing (AffineCoordinateRingBar X))
    (h : (1 : AffineCoordinateRingBar X) ∈ denominatorIdeal r) :
    r ∈ Set.range (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))) := by
  rw [mem_denominatorIdeal_iff] at h
  rwa [map_one, one_mul] at h

/-- If $r \in \bar k(X)$ is regular on all of $X$, then its denominator ideal equals
$\bar k[X]$ (the unit ideal). Combines `denominatorIdeal_eq_top_of_no_common_zero` with
the definition of `regularDomain`. -/
theorem denominatorIdeal_eq_top_of_regularDomain_eq
    (hAlg : IsAlgebraicSubset k n X)
    (r : FractionRing (AffineCoordinateRingBar X))
    (hdom : regularDomain r = X) :
    denominatorIdeal r = ⊤ := by
  apply denominatorIdeal_eq_top_of_no_common_zero hAlg
  intro P hP
  have hPreg : P ∈ regularDomain r := by rw [hdom]; exact hP
  obtain ⟨_, hreg⟩ := hPreg
  obtain ⟨g, hne, hmem⟩ := hreg
  exact ⟨g, hmem, hne⟩

/-- Theorem 15.5 (regular everywhere equals polynomial). A rational function $r \in
\bar k(X)$ is regular on all of $X$ if and only if it comes from a polynomial function
in $\bar k[X]$. This is a key consequence of the Nullstellensatz. -/
theorem regular_iff_polynomial
    (hAlg : IsAlgebraicSubset k n X)
    (r : FractionRing (AffineCoordinateRingBar X)) :
    r ∈ Set.range (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))) ↔
    regularDomain r = X := by
  constructor
  ·
    rintro ⟨f, rfl⟩
    exact regularDomain_algebraMap f
  ·
    intro hdom
    have h1 : denominatorIdeal r = ⊤ :=
      denominatorIdeal_eq_top_of_regularDomain_eq hAlg r hdom
    have h1mem : (1 : AffineCoordinateRingBar X) ∈ denominatorIdeal r := by
      rw [h1]; exact Submodule.mem_top
    exact inRange_of_one_mem_denominatorIdeal r h1mem

end RegularFunctions

section RationalMaps

variable {k : Type*} [Field k]
variable {m n_cod : ℕ}
variable {X : Set (Fin m → AlgebraicClosure k)}
variable [hdom : IsDomain (AffineCoordinateRingBar X)]

open MvPolynomial

/-- A tuple $(\varphi_1, \dots, \varphi_{n_\mathrm{cod}})$ of rational functions in
$\bar k(X)$ is *regular at $P \in X$* if each component $\varphi_i$ is regular at $P$. -/
def IsTupleRegularAt
    (φ : Fin n_cod → FractionRing (AffineCoordinateRingBar X))
    (P : Fin m → AlgebraicClosure k)
    (hP : P ∈ X) : Prop :=
  ∀ i : Fin n_cod, IsRegularAt (φ i) P hP

/-- Componentwise evaluation of a tuple of rational functions at a point of common
regularity: produces a point of $\bar k^{n_\mathrm{cod}}$. -/
noncomputable def evalTupleAt
    (φ : Fin n_cod → FractionRing (AffineCoordinateRingBar X))
    (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
    (hreg : IsTupleRegularAt φ P hP) :
    Fin n_cod → AlgebraicClosure k :=
  fun j => evalRatFunAt (φ j) P hP (hreg j)

/-- Definition 15.4 (affine rational map). A *rational map* $\varphi : X \dashrightarrow Y$
between affine algebraic sets is a tuple of components $(\varphi_1, \dots, \varphi_{n_\mathrm{cod}})$
with each $\varphi_i \in \bar k(X)$, together with the requirement that whenever the tuple
is regular at $P \in X$, the resulting point $(\varphi_1(P), \dots, \varphi_{n_\mathrm{cod}}(P))$
lies in the target $Y$. -/
structure AffineRationalMap
    (X : Set (Fin m → AlgebraicClosure k))
    (Y : Set (Fin n_cod → AlgebraicClosure k))
    [IsDomain (AffineCoordinateRingBar X)] where
  components : Fin n_cod → FractionRing (AffineCoordinateRingBar X)
  image_mem : ∀ (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
    (hreg : IsTupleRegularAt components P hP),
    evalTupleAt components P hP hreg ∈ Y

/-- The *domain of definition* of a rational map (as a tuple of rational functions):
the set of points of $X$ where every component is regular. -/
def rationalMapDomain
    (φ : Fin n_cod → FractionRing (AffineCoordinateRingBar X)) :
    Set (Fin m → AlgebraicClosure k) :=
  {P : Fin m → AlgebraicClosure k | ∃ (hP : P ∈ X), IsTupleRegularAt φ P hP}


/-- Lemma 15.3 (description of domain). The domain of definition of a rational map
$\varphi : X \dashrightarrow Y$ is the intersection $X \cap \bigcap_i \mathrm{dom}(\varphi_i)$
of the regular domains of its components. -/
theorem rationalMapDomain_eq_inter_iInter
    (φ : Fin n_cod → FractionRing (AffineCoordinateRingBar X)) :
    rationalMapDomain φ = X ∩ ⋂ i, regularDomain (φ i) := by
  ext P
  simp only [rationalMapDomain, Set.mem_setOf_eq, Set.mem_inter_iff,
    Set.mem_iInter, mem_regularDomain_iff, IsTupleRegularAt]
  constructor
  · rintro ⟨hP, hall⟩
    exact ⟨hP, fun i => ⟨hP, hall i⟩⟩
  · rintro ⟨hP, hall⟩
    exact ⟨hP, fun i => (hall i).2⟩


/-- A rational map $\varphi$ is *regular* (a morphism of affine varieties) if it is
regular at every point of $X$. -/
def IsRegularRationalMap
    (φ : Fin n_cod → FractionRing (AffineCoordinateRingBar X)) : Prop :=
  ∀ (P : Fin m → AlgebraicClosure k) (hP : P ∈ X), IsTupleRegularAt φ P hP


end RationalMaps

section DominantAndBirational

variable {k : Type*} [Field k]

open MvPolynomial

/-- The *Zariski closure* of a subset $S \subseteq \bar k^n$: the smallest algebraic
set containing $S$, namely $\mathcal{V}(\mathcal{I}(S))$. -/
def zariskiClosure {n : ℕ}
    (S : Set (Fin n → AlgebraicClosure k)) :
    Set (Fin n → AlgebraicClosure k) :=
  AlgebraicSet k n ((idealOfAlgebraicSet S : Ideal _) : Set _)


/-- The set-theoretic image of a rational map (defined on its domain): the set of all
$Q \in \bar k^{n_\mathrm{cod}}$ that arise as the value of $\varphi$ at some point of
$\mathrm{dom}(\varphi)$. -/
def rationalMapImage {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    (φ : Fin n_cod → FractionRing (AffineCoordinateRingBar X)) :
    Set (Fin n_cod → AlgebraicClosure k) :=
  {Q : Fin n_cod → AlgebraicClosure k |
    ∃ (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
      (hreg : IsTupleRegularAt φ P hP),
      evalTupleAt φ P hP hreg = Q}

/-- Definition 15.7 (dominant rational map). A rational map $\varphi : X \dashrightarrow Y$
is *dominant* if its image is Zariski-dense in $Y$, i.e. the Zariski closure of the image
equals $Y$. -/
def IsDominantRationalMap {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    (Y : Set (Fin n_cod → AlgebraicClosure k))
    (φ : AffineRationalMap X Y) : Prop :=
  zariskiClosure (rationalMapImage φ.components) = Y

/-- The *composition domain* of $\psi \circ \varphi$ where $\varphi : X \dashrightarrow Y$
and $\psi : Y \dashrightarrow X$: the set of points $P \in X$ where $\varphi$ is regular
at $P$, $\varphi(P) \in Y$, and $\psi$ is regular at $\varphi(P)$. -/
def compositionDomain {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y)
    (ψ : AffineRationalMap Y X) :
    Set (Fin m → AlgebraicClosure k) :=
  {P : Fin m → AlgebraicClosure k |
    ∃ (hP : P ∈ X) (hregφ : IsTupleRegularAt φ.components P hP),
      ∃ (hQ : evalTupleAt φ.components P hP hregφ ∈ Y),
        IsTupleRegularAt ψ.components
          (evalTupleAt φ.components P hP hregφ) hQ}

/-- Pointwise evaluation of the composition $\psi \circ \varphi$ at $P \in
\mathrm{compositionDomain}(\varphi, \psi)$: returns $\psi(\varphi(P)) \in \bar k^m$. -/
noncomputable def evalCompositionAt {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y)
    (ψ : AffineRationalMap Y X)
    (P : Fin m → AlgebraicClosure k)
    (hcomp : P ∈ compositionDomain φ ψ) :
    Fin m → AlgebraicClosure k :=
  let hP := hcomp.choose
  let hregφ := hcomp.choose_spec.choose
  let hQ := hcomp.choose_spec.choose_spec.choose
  let hregψ := hcomp.choose_spec.choose_spec.choose_spec
  evalTupleAt ψ.components
    (evalTupleAt φ.components P hP hregφ) hQ hregψ

/-- Definition 15.10 (birational equivalence). Two affine algebraic sets $X$ and $Y$
are *birationally equivalent* if there exist dominant rational maps
$\varphi : X \dashrightarrow Y$ and $\psi : Y \dashrightarrow X$ whose compositions (on
their composition domains) agree with the respective identities. -/
def AreBirationallyEquivalent {m n_cod : ℕ}
    (X : Set (Fin m → AlgebraicClosure k))
    (Y : Set (Fin n_cod → AlgebraicClosure k))
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)] : Prop :=
  ∃ (φ : AffineRationalMap X Y) (ψ : AffineRationalMap Y X),
    IsDominantRationalMap Y φ ∧
    IsDominantRationalMap X ψ ∧
    (∀ (P : Fin m → AlgebraicClosure k)
       (hcomp : P ∈ compositionDomain φ ψ),
       evalCompositionAt φ ψ P hcomp = P) ∧
    (∀ (Q : Fin n_cod → AlgebraicClosure k)
       (hcomp : Q ∈ compositionDomain ψ φ),
       evalCompositionAt ψ φ Q hcomp = Q)

end DominantAndBirational

section Theorem158

variable {k : Type*} [Field k]

open MvPolynomial

/-- A ring homomorphism $\theta : \bar k(Y) \to \bar k(X)$ is a *$\bar k$-algebra
homomorphism of function fields* if it fixes the scalars from $\bar k$ (under the
canonical inclusions $\bar k \hookrightarrow \bar k[Y] \hookrightarrow \bar k(Y)$). -/
def IsKbarFunctionFieldHom {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X)) : Prop :=
  ∀ r : AlgebraicClosure k,
    θ ((algebraMap (AffineCoordinateRingBar Y)
      (FractionRing (AffineCoordinateRingBar Y)))
      (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.C r))) =
    (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X)))
      (Ideal.Quotient.mk (idealOfAlgebraicSet X) (MvPolynomial.C r))

/-- The substitution homomorphism $\bar k[Y_1, \dots, Y_{n_\mathrm{cod}}] \to \bar k(X)$
sending each coordinate $Y_i$ to the corresponding component $\varphi_i \in \bar k(X)$.
This is the first step in building the pullback induced by a rational map. -/
noncomputable def dominantPullbackSubstHom
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    (φ : Fin n_cod → FractionRing (AffineCoordinateRingBar X)) :
    MvPolynomial (Fin n_cod) (AlgebraicClosure k) →+*
    FractionRing (AffineCoordinateRingBar X) :=
  MvPolynomial.eval₂Hom
    ((algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))).comp
      ((Ideal.Quotient.mk (idealOfAlgebraicSet X)).comp MvPolynomial.C))
    φ

/-- Key technical lemma: the substitution homomorphism associated to a rational map
$\varphi : X \dashrightarrow Y$ kills the ideal $\mathcal{I}(Y)$. Combines the
Nullstellensatz with the property that the values of $\varphi$ land in $Y$. This is what
allows the substitution map to descend to $\bar k[Y] \to \bar k(X)$. -/
theorem dominantPullbackSubstHom_kills_ideal
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y)
    (f : MvPolynomial (Fin n_cod) (AlgebraicClosure k))
    (hf : f ∈ idealOfAlgebraicSet Y) :
    dominantPullbackSubstHom φ.components f = 0 := by


  by_contra hr

  obtain ⟨⟨a_r, ⟨b_r, hb_r⟩⟩, hab_r⟩ := IsLocalization.surj
    (nonZeroDivisors (AffineCoordinateRingBar X))
    (dominantPullbackSubstHom φ.components f)
  simp only at hab_r

  have ha_ne : a_r ≠ 0 := by
    intro ha0; apply hr
    have h1 : dominantPullbackSubstHom φ.components f *
        (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))) b_r = 0 := by
      rw [hab_r, ha0, map_zero]
    have hb_ne_frac : (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))) b_r ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
      exact mem_nonZeroDivisors_iff_ne_zero.mp hb_r
    exact (mul_eq_zero.mp h1).resolve_right hb_ne_frac
  have hb_ne : b_r ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb_r

  choose cd_j hcd_j using
    (fun j => IsLocalization.surj (nonZeroDivisors (AffineCoordinateRingBar X)) (φ.components j))

  set product := a_r * (b_r * ∏ j : Fin n_cod, ((cd_j j).2 : AffineCoordinateRingBar X))
    with hprod_def

  have hprod_ne : product ≠ 0 := by
    apply mul_ne_zero ha_ne (mul_ne_zero hb_ne _)
    exact Finset.prod_ne_zero_iff.mpr (fun j _ =>
      mem_nonZeroDivisors_iff_ne_zero.mp (cd_j j).2.property)


  have h_clearing : ∀ (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
      (hreg_comp : IsTupleRegularAt φ.components P hP)
      (p : MvPolynomial (Fin n_cod) (AlgebraicClosure k)),
      ∃ (g₀ : AffineCoordinateRingBar X) (f₀ : AffineCoordinateRingBar X),
        evalBarAtPoint k X P hP g₀ ≠ 0 ∧
        (algebraMap (AffineCoordinateRingBar X)
          (FractionRing (AffineCoordinateRingBar X))) f₀ =
        (algebraMap (AffineCoordinateRingBar X)
          (FractionRing (AffineCoordinateRingBar X))) g₀ *
          (dominantPullbackSubstHom φ.components) p ∧
        MvPolynomial.eval (evalTupleAt φ.components P hP hreg_comp) p *
          evalBarAtPoint k X P hP g₀ = evalBarAtPoint k X P hP f₀ := by
    intro P hP hreg_comp p
    induction p using MvPolynomial.induction_on with
    | C c =>
      refine ⟨1, Ideal.Quotient.mk _ (MvPolynomial.C c), ?_, ?_, ?_⟩
      · simp [map_one]
      · simp only [dominantPullbackSubstHom, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
          map_one, one_mul]
        rfl
      · simp only [MvPolynomial.eval_C, map_one, mul_one, evalBarAtPoint_mk]
    | add p q ihp ihq =>
      obtain ⟨gp, fp, hgp_ne, hfp_eq, hfp_eval⟩ := ihp
      obtain ⟨gq, fq, hgq_ne, hfq_eq, hfq_eval⟩ := ihq
      refine ⟨gp * gq, gq * fp + gp * fq, ?_, ?_, ?_⟩
      · rw [map_mul]; exact mul_ne_zero hgp_ne hgq_ne
      · simp only [map_mul, map_add]
        rw [mul_add]
        congr 1
        · rw [hfp_eq]; ring
        · rw [hfq_eq]; ring
      · simp only [map_mul, map_add]
        linear_combination (evalBarAtPoint k X P hP gq) * hfp_eval +
          (evalBarAtPoint k X P hP gp) * hfq_eval
    | mul_X p j ihp =>
      obtain ⟨gp, fp, hgp_ne, hfp_eq, hfp_eval⟩ := ihp
      obtain ⟨gj, hgj_ne, hgj_mem⟩ := hreg_comp j
      obtain ⟨aj, haj_eq⟩ := hgj_mem
      refine ⟨gp * gj, fp * aj, ?_, ?_, ?_⟩
      · rw [map_mul]; exact mul_ne_zero hgp_ne hgj_ne
      · simp only [map_mul]
        rw [show (dominantPullbackSubstHom φ.components) (MvPolynomial.X j) =
          φ.components j by
          simp only [dominantPullbackSubstHom, MvPolynomial.eval₂Hom_X']]
        rw [hfp_eq, haj_eq]
        ring
      · simp only [MvPolynomial.eval_X, map_mul]
        have hσj : evalTupleAt φ.components P hP hreg_comp j *
            evalBarAtPoint k X P hP gj = evalBarAtPoint k X P hP aj := by
          set g₀ := (hreg_comp j).choose with hg₀_def
          set f₀ := (hreg_comp j).choose_spec.2.choose with hf₀_def
          have hg₀_ne : evalBarAtPoint k X P hP g₀ ≠ 0 := (hreg_comp j).choose_spec.1
          have hf₀_eq : (algebraMap (AffineCoordinateRingBar X)
            (FractionRing (AffineCoordinateRingBar X))) f₀ =
            (algebraMap (AffineCoordinateRingBar X)
            (FractionRing (AffineCoordinateRingBar X))) g₀ * φ.components j :=
            (hreg_comp j).choose_spec.2.choose_spec
          have h_cross : f₀ * gj = aj * g₀ := by
            apply IsFractionRing.injective (AffineCoordinateRingBar X)
              (FractionRing (AffineCoordinateRingBar X))
            simp only [map_mul]
            rw [hf₀_eq, haj_eq]
            ring
          show evalRatFunAt (φ.components j) P hP (hreg_comp j) *
            evalBarAtPoint k X P hP gj = evalBarAtPoint k X P hP aj
          simp only [evalRatFunAt]
          rw [div_mul_eq_mul_div, div_eq_iff hg₀_ne]
          rw [← map_mul, ← map_mul, h_cross]
        calc (MvPolynomial.eval _ p) *
              (evalTupleAt φ.components P hP hreg_comp j) *
              ((evalBarAtPoint k X P hP gp) * (evalBarAtPoint k X P hP gj))
            = ((MvPolynomial.eval _ p) * (evalBarAtPoint k X P hP gp)) *
              ((evalTupleAt φ.components P hP hreg_comp j) *
               (evalBarAtPoint k X P hP gj)) := by ring
          _ = (evalBarAtPoint k X P hP fp) * (evalBarAtPoint k X P hP aj) := by
              rw [hfp_eval, hσj]

  have hprod_vanishes : ∀ (P : Fin m → AlgebraicClosure k) (hP : P ∈ X),
      evalBarAtPoint k X P hP product = 0 := by
    intro P hP
    simp only [hprod_def, map_mul, map_prod]
    by_cases hbP : evalBarAtPoint k X P hP b_r = 0
    · simp [hbP]
    by_cases hdP : ∃ j, evalBarAtPoint k X P hP ((cd_j j).2 : AffineCoordinateRingBar X) = 0
    · obtain ⟨j, hjP⟩ := hdP
      have : (∏ i : Fin n_cod,
          evalBarAtPoint k X P hP ((cd_j i).2 : AffineCoordinateRingBar X)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) hjP
      simp [this]
    push Not at hdP

    have hreg_comp : IsTupleRegularAt φ.components P hP := by
      intro j
      exact ⟨((cd_j j).2 : AffineCoordinateRingBar X), hdP j,
        ⟨(cd_j j).1, ((hcd_j j).symm.trans (mul_comm _ _))⟩⟩

    have hf_vanish : MvPolynomial.eval (evalTupleAt φ.components P hP hreg_comp) f = 0 :=
      hf _ (φ.image_mem P hP hreg_comp)

    obtain ⟨g₀, f₀, hg₀_ne, hf₀_eq, hf₀_eval⟩ := h_clearing P hP hreg_comp f

    rw [hf_vanish, zero_mul] at hf₀_eval


    have h_cross : f₀ * b_r = g₀ * a_r := by
      apply IsFractionRing.injective (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))
      simp only [map_mul]
      calc _ = (algebraMap _ _ g₀ * dominantPullbackSubstHom φ.components f) *
                algebraMap _ _ b_r := by rw [hf₀_eq]
        _ = algebraMap _ _ g₀ * (dominantPullbackSubstHom φ.components f *
                algebraMap _ _ b_r) := by ring
        _ = algebraMap _ _ g₀ * algebraMap _ _ a_r := by rw [hab_r]
    have h_eval_cross : evalBarAtPoint k X P hP f₀ * evalBarAtPoint k X P hP b_r =
        evalBarAtPoint k X P hP g₀ * evalBarAtPoint k X P hP a_r := by
      rw [← map_mul, ← map_mul, h_cross]

    rw [hf₀_eval.symm, zero_mul] at h_eval_cross
    have haP : evalBarAtPoint k X P hP a_r = 0 := by
      rcases mul_eq_zero.mp h_eval_cross.symm with hg₀P | haP
      · exact absurd hg₀P hg₀_ne
      · exact haP
    simp [haP]

  have hprod_zero : product = 0 := by
    obtain ⟨f_poly, hf_poly⟩ := Ideal.Quotient.mk_surjective product
    suffices h_mem : f_poly ∈ idealOfAlgebraicSet X by
      rw [← hf_poly]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h_mem
    rw [mem_idealOfAlgebraicSet_iff]
    intro P hP
    have := hprod_vanishes P hP
    rw [← hf_poly, evalBarAtPoint_mk] at this
    exact this
  exact hprod_ne hprod_zero

/-- Descent of the substitution homomorphism to a ring map $\bar k[Y] \to \bar k(X)$:
since the substitution kills $\mathcal{I}(Y)$, it factors through the quotient
$\bar k[Y_1,\dots,Y_{n_\mathrm{cod}}]/\mathcal{I}(Y) = \bar k[Y]$. -/
noncomputable def dominantPullbackToFractionRing
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y) :
    AffineCoordinateRingBar Y →+* FractionRing (AffineCoordinateRingBar X) :=
  Ideal.Quotient.lift (idealOfAlgebraicSet Y)
    (dominantPullbackSubstHom φ.components)
    (dominantPullbackSubstHom_kills_ideal φ)

/-- Compatibility of the descended map with the quotient: evaluating on the class of $f$
gives the substitution applied to $f$. -/
@[simp]
lemma dominantPullbackToFractionRing_mk
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y)
    (f : MvPolynomial (Fin n_cod) (AlgebraicClosure k)) :
    dominantPullbackToFractionRing φ (Ideal.Quotient.mk _ f) =
    dominantPullbackSubstHom φ.components f :=
  Ideal.Quotient.lift_mk _ _ _

/-- Each coordinate $\varphi_i = \varphi^*(Y_i)$ lies in $\bar k[X] \subseteq \bar k(X)$,
viewed via the substitution homomorphism. (This is the form needed for the pullback to
descend to coordinate rings; the proof uses regularity of the rational map.) -/
theorem dominantPullbackSubstHom_component_mem_range
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y)
    (i : Fin n_cod) :
    dominantPullbackSubstHom φ.components (MvPolynomial.X i) ∈
      Set.range (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))) := by sorry

/-- Generalization to all of $\bar k[Y]$: every element $g \in \bar k[Y]$ is sent into
$\bar k[X] \subseteq \bar k(X)$ by `dominantPullbackToFractionRing`. Proved by induction
using the previous component-wise lemma. -/
lemma dominantPullback_mem_range
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y)
    (g : AffineCoordinateRingBar Y) :
    dominantPullbackToFractionRing φ g ∈
      Set.range (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))) := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective g
  rw [dominantPullbackToFractionRing_mk]
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [dominantPullbackSubstHom, MvPolynomial.eval₂Hom_C]
    exact ⟨_, rfl⟩
  | add p q hp hq =>
    rw [map_add]
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨a + b, by rw [map_add, ha, hb]⟩
  | mul_X p i hp =>
    rw [map_mul]
    obtain ⟨a, ha⟩ := hp
    have hcomp := dominantPullbackSubstHom_component_mem_range φ i
    obtain ⟨b, hb⟩ := hcomp
    exact ⟨a * b, by rw [map_mul, ha, hb]⟩

/-- Defining property of the chosen preimage: the chosen element of $\bar k[X]$ maps to
$\varphi^*(g) \in \bar k(X)$. -/
lemma dominantPullbackOnCoordRing_spec
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y)
    (g : AffineCoordinateRingBar Y) :
    (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X)))
      (dominantPullback_mem_range φ g).choose =
    dominantPullbackToFractionRing φ g :=
  (dominantPullback_mem_range φ g).choose_spec

/-- The *pullback* ring homomorphism $\varphi^* : \bar k[Y] \to \bar k[X]$ on coordinate
rings induced by a dominant rational map $\varphi : X \dashrightarrow Y$. Built using the
choice function from `dominantPullback_mem_range` together with the injectivity of
$\bar k[X] \hookrightarrow \bar k(X)$. -/
noncomputable def dominantPullbackOnCoordRing
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y) :
    AffineCoordinateRingBar Y →+* AffineCoordinateRingBar X where
  toFun g := (dominantPullback_mem_range φ g).choose
  map_one' := by
    apply IsFractionRing.injective (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))
    rw [dominantPullbackOnCoordRing_spec]
    simp only [map_one]
  map_mul' x y := by
    apply IsFractionRing.injective (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))
    rw [dominantPullbackOnCoordRing_spec]
    rw [(algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))).map_mul]
    rw [dominantPullbackOnCoordRing_spec, dominantPullbackOnCoordRing_spec]
    exact (dominantPullbackToFractionRing φ).map_mul x y
  map_zero' := by
    apply IsFractionRing.injective (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))
    rw [dominantPullbackOnCoordRing_spec]
    simp only [map_zero]
  map_add' x y := by
    apply IsFractionRing.injective (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))
    rw [dominantPullbackOnCoordRing_spec]
    rw [(algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))).map_add]
    rw [dominantPullbackOnCoordRing_spec, dominantPullbackOnCoordRing_spec]
    exact (dominantPullbackToFractionRing φ).map_add x y

/-- Compatibility square: the diagram of $\varphi^* : \bar k[Y] \to \bar k[X]$ followed
by $\bar k[X] \hookrightarrow \bar k(X)$ commutes with the descended substitution
homomorphism $\bar k[Y] \to \bar k(X)$. -/
lemma algebraMap_dominantPullbackOnCoordRing
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y)
    (g : AffineCoordinateRingBar Y) :
    (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X)))
      (dominantPullbackOnCoordRing φ g) =
    dominantPullbackToFractionRing φ g :=
  dominantPullbackOnCoordRing_spec φ g

/-- The pullback $\varphi^* : \bar k[Y] \to \bar k[X]$ fixes the scalars: it sends the
class of a constant polynomial $C(r)$ in $\bar k[Y]$ to the class of $C(r)$ in $\bar k[X]$.
This is the coordinate-ring version of `IsKbarFunctionFieldHom` for $\varphi^*$. -/
theorem dominantPullbackOnCoordRing_preserves_C
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y)
    (r : AlgebraicClosure k) :
    dominantPullbackOnCoordRing φ
      (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.C r)) =
    Ideal.Quotient.mk (idealOfAlgebraicSet X) (MvPolynomial.C r) := by
  apply IsFractionRing.injective (AffineCoordinateRingBar X)
    (FractionRing (AffineCoordinateRingBar X))
  rw [algebraMap_dominantPullbackOnCoordRing]
  rw [dominantPullbackToFractionRing_mk]
  simp only [dominantPullbackSubstHom, MvPolynomial.eval₂Hom_C]
  rfl

/-- Theorem 15.8(i) (injectivity of pullback). If $\varphi : X \dashrightarrow Y$ is
dominant, then the composite $\bar k[Y] \xrightarrow{\varphi^*} \bar k[X] \hookrightarrow
\bar k(X)$ is injective. The proof combines the Nullstellensatz with the density of the
image of $\varphi$ in $Y$. -/
theorem dominant_pullback_injective
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y)
    (hdom : IsDominantRationalMap Y φ) :
    Function.Injective
      ((algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))).comp
        (dominantPullbackOnCoordRing φ)) := by

  rw [show ((algebraMap (AffineCoordinateRingBar X)
    (FractionRing (AffineCoordinateRingBar X))).comp
    (dominantPullbackOnCoordRing φ)) = dominantPullbackToFractionRing φ from
    RingHom.ext (algebraMap_dominantPullbackOnCoordRing φ)]
  intro a b hab

  rw [← sub_eq_zero]
  obtain ⟨f_poly, hf⟩ := Ideal.Quotient.mk_surjective (a - b)
  rw [← hf]
  change (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f_poly : _ ⧸ _) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]

  have h_diff : (dominantPullbackSubstHom φ.components) f_poly = 0 := by
    have : dominantPullbackToFractionRing φ (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    rw [← hf, dominantPullbackToFractionRing_mk] at this
    exact this

  rw [mem_idealOfAlgebraicSet_iff]
  intro Q hQ

  have hQ_clos : Q ∈ zariskiClosure (rationalMapImage φ.components) := by rw [hdom]; exact hQ

  simp only [zariskiClosure, AlgebraicSet, Set.mem_setOf_eq, SetLike.mem_coe,
    mem_idealOfAlgebraicSet_iff] at hQ_clos
  apply hQ_clos

  intro R hR
  obtain ⟨P, hP, hreg, hR_eq⟩ := hR
  rw [← hR_eq]


  suffices h_clearing : ∀ (p : MvPolynomial (Fin n_cod) (AlgebraicClosure k)),
      ∃ (g₀ : AffineCoordinateRingBar X) (f₀ : AffineCoordinateRingBar X),
        evalBarAtPoint k X P hP g₀ ≠ 0 ∧
        (algebraMap (AffineCoordinateRingBar X)
          (FractionRing (AffineCoordinateRingBar X))) f₀ =
        (algebraMap (AffineCoordinateRingBar X)
          (FractionRing (AffineCoordinateRingBar X))) g₀ *
          (dominantPullbackSubstHom φ.components) p ∧
        MvPolynomial.eval (evalTupleAt φ.components P hP hreg) p *
          evalBarAtPoint k X P hP g₀ = evalBarAtPoint k X P hP f₀ by
    obtain ⟨g₀, f₀, hg₀_ne, hf₀_eq, hf₀_eval⟩ := h_clearing f_poly
    rw [h_diff, mul_zero] at hf₀_eq
    have hf₀_zero : f₀ = 0 := by
      have hinj := IsFractionRing.injective (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))
      exact hinj (hf₀_eq.trans (map_zero _).symm)
    rw [hf₀_zero, map_zero] at hf₀_eval
    exact (mul_eq_zero.mp hf₀_eval).resolve_right hg₀_ne

  intro p
  induction p using MvPolynomial.induction_on with
  | C c =>
    refine ⟨1, Ideal.Quotient.mk _ (MvPolynomial.C c), ?_, ?_, ?_⟩
    · simp [map_one]
    · simp only [dominantPullbackSubstHom, MvPolynomial.eval₂Hom_C, RingHom.comp_apply,
        map_one, one_mul]
      rfl
    · simp only [MvPolynomial.eval_C, map_one, mul_one, evalBarAtPoint_mk]
  | add p q ihp ihq =>
    obtain ⟨gp, fp, hgp_ne, hfp_eq, hfp_eval⟩ := ihp
    obtain ⟨gq, fq, hgq_ne, hfq_eq, hfq_eval⟩ := ihq
    refine ⟨gp * gq, gq * fp + gp * fq, ?_, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero hgp_ne hgq_ne
    · simp only [map_mul, map_add]
      rw [mul_add]
      congr 1
      · rw [hfp_eq]; ring
      · rw [hfq_eq]; ring
    · simp only [map_mul, map_add]
      linear_combination (evalBarAtPoint k X P hP gq) * hfp_eval +
        (evalBarAtPoint k X P hP gp) * hfq_eval
  | mul_X p j ihp =>
    obtain ⟨gp, fp, hgp_ne, hfp_eq, hfp_eval⟩ := ihp
    obtain ⟨gj, hgj_ne, hgj_mem⟩ := hreg j
    obtain ⟨aj, haj_eq⟩ := hgj_mem
    refine ⟨gp * gj, fp * aj, ?_, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero hgp_ne hgj_ne
    ·


      simp only [map_mul]
      rw [show (dominantPullbackSubstHom φ.components) (MvPolynomial.X j) =
        φ.components j by
        simp only [dominantPullbackSubstHom, MvPolynomial.eval₂Hom_X']]
      rw [hfp_eq, haj_eq]
      ring
    · simp only [MvPolynomial.eval_X, map_mul]
      have hσj : evalTupleAt φ.components P hP hreg j *
          evalBarAtPoint k X P hP gj = evalBarAtPoint k X P hP aj := by
        set g₀ := (hreg j).choose with hg₀_def
        set f₀ := (hreg j).choose_spec.2.choose with hf₀_def
        have hg₀_ne : evalBarAtPoint k X P hP g₀ ≠ 0 := (hreg j).choose_spec.1
        have hf₀_eq : (algebraMap (AffineCoordinateRingBar X)
          (FractionRing (AffineCoordinateRingBar X))) f₀ =
          (algebraMap (AffineCoordinateRingBar X)
          (FractionRing (AffineCoordinateRingBar X))) g₀ * φ.components j :=
          (hreg j).choose_spec.2.choose_spec
        have h_cross : f₀ * gj = aj * g₀ := by
          apply IsFractionRing.injective (AffineCoordinateRingBar X)
            (FractionRing (AffineCoordinateRingBar X))
          simp only [map_mul]
          rw [hf₀_eq, haj_eq]
          ring


        show evalRatFunAt (φ.components j) P hP (hreg j) *
          evalBarAtPoint k X P hP gj = evalBarAtPoint k X P hP aj
        simp only [evalRatFunAt]
        rw [div_mul_eq_mul_div, div_eq_iff hg₀_ne]
        rw [← map_mul, ← map_mul, h_cross]
      calc (MvPolynomial.eval _ p) *
            (evalTupleAt φ.components P hP hreg j) *
            ((evalBarAtPoint k X P hP gp) * (evalBarAtPoint k X P hP gj))
          = ((MvPolynomial.eval _ p) * (evalBarAtPoint k X P hP gp)) *
            ((evalTupleAt φ.components P hP hreg j) *
             (evalBarAtPoint k X P hP gj)) := by ring
        _ = (evalBarAtPoint k X P hP fp) * (evalBarAtPoint k X P hP aj) := by
            rw [hfp_eval, hσj]

/-- The *function-field pullback* $\varphi^* : \bar k(Y) \to \bar k(X)$ induced by a
dominant rational map. Obtained by extending the coordinate-ring pullback to fraction
fields using `IsFractionRing.lift` and the injectivity result. -/
noncomputable def dominantRationalMapPullback {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y)
    (hdom : IsDominantRationalMap Y φ) :
    FractionRing (AffineCoordinateRingBar Y) →+*
    FractionRing (AffineCoordinateRingBar X) :=
  IsFractionRing.lift
    (g := (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))).comp
      (dominantPullbackOnCoordRing φ))
    (dominant_pullback_injective φ hdom)

/-- Commutative diagram linking the coordinate-ring pullback to the function-field
pullback: the diagram of $\bar k[Y] \hookrightarrow \bar k(Y) \xrightarrow{\varphi^*}
\bar k(X)$ and $\bar k[Y] \xrightarrow{\varphi^*} \bar k[X] \hookrightarrow \bar k(X)$
commutes. -/
theorem dominantPullbackOnCoordRing_comm
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y)
    (hdom : IsDominantRationalMap Y φ)
    (g : AffineCoordinateRingBar Y) :
    dominantRationalMapPullback φ hdom
      (algebraMap (AffineCoordinateRingBar Y)
        (FractionRing (AffineCoordinateRingBar Y)) g) =
    algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))
        (dominantPullbackOnCoordRing φ g) := by
  exact IsFractionRing.lift_algebraMap (dominant_pullback_injective φ hdom) g

/-- Given an abstract ring homomorphism $\theta : \bar k(Y) \to \bar k(X)$, the
*components* of the rational map it induces: for each coordinate $j$, the image
$\theta(Y_j) \in \bar k(X)$. This is the data used to recover a rational map from a
function-field homomorphism in Theorem 15.8(iii). -/
noncomputable def functionFieldMorphismComponents {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X)) :
    Fin n_cod → FractionRing (AffineCoordinateRingBar X) :=
  fun j => θ (algebraMap (AffineCoordinateRingBar Y)
    (FractionRing (AffineCoordinateRingBar Y))
    (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.X j)))

/-- Independence of representation for `evalRatFunAt`: any representation $r = f/g$ with
$g(P) \neq 0$ gives the same value $f(P)/g(P)$ for the evaluation of $r$ at $P$. -/
lemma evalRatFunAt_eq {k : Type*} [Field k] {n : ℕ}
    {X : Set (Fin n → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    (r : FractionRing (AffineCoordinateRingBar X))
    (P : Fin n → AlgebraicClosure k) (hP : P ∈ X)
    (hreg : IsRegularAt r P hP)
    (g f_val : AffineCoordinateRingBar X)
    (hg_ne : evalBarAtPoint k X P hP g ≠ 0)
    (hgr : algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X)) g * r =
      algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X)) f_val) :
    evalRatFunAt r P hP hreg = evalBarAtPoint k X P hP f_val /
      evalBarAtPoint k X P hP g := by
  show evalBarAtPoint k X P hP hreg.choose_spec.2.choose /
    evalBarAtPoint k X P hP hreg.choose =
    evalBarAtPoint k X P hP f_val / evalBarAtPoint k X P hP g
  set g₀ := hreg.choose with hg₀_def
  set f₀ := hreg.choose_spec.2.choose with hf₀_def
  have hg₀_ne : evalBarAtPoint k X P hP g₀ ≠ 0 := hreg.choose_spec.1
  have hf₀_eq : (algebraMap (AffineCoordinateRingBar X)
    (FractionRing (AffineCoordinateRingBar X))) f₀ =
    (algebraMap (AffineCoordinateRingBar X)
    (FractionRing (AffineCoordinateRingBar X))) g₀ * r :=
    hreg.choose_spec.2.choose_spec
  have h_cross : f₀ * g = g₀ * f_val := by
    apply IsFractionRing.injective (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))
    simp only [map_mul]
    calc _ = (algebraMap _ _ g₀ * r) * algebraMap _ _ g := by rw [hf₀_eq]
      _ = algebraMap _ _ g₀ * (algebraMap _ _ g * r) := by ring
      _ = algebraMap _ _ g₀ * algebraMap _ _ f_val := by rw [hgr]
  have h_eval_cross : evalBarAtPoint k X P hP f₀ * evalBarAtPoint k X P hP g =
      evalBarAtPoint k X P hP g₀ * evalBarAtPoint k X P hP f_val := by
    rw [← map_mul, ← map_mul, h_cross]
  rw [div_eq_div_iff hg₀_ne hg_ne]
  rw [mul_comm (evalBarAtPoint k X P hP f_val)]
  exact h_eval_cross

/-- Technical "clearing denominators" lemma used in the proof of Theorem 15.8(iii): for
any polynomial $f \in \bar k[Y_1, \dots, Y_{n_\mathrm{cod}}]$ and any point $P$ at which
the components $(\theta(Y_1), \dots, \theta(Y_{n_\mathrm{cod}}))$ are all regular, there
exist $g_0, f_0 \in \bar k[X]$ with $g_0(P) \neq 0$ such that
$\theta_*(f) = f_0 / g_0$ in $\bar k(X)$ and $f(\theta(P)) \cdot g_0(P) = f_0(P)$. -/
lemma eval₂_clearing_denominators
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X))
    (hθ : IsKbarFunctionFieldHom θ)
    (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
    (hreg : IsTupleRegularAt (functionFieldMorphismComponents θ) P hP)
    (f : MvPolynomial (Fin n_cod) (AlgebraicClosure k)) :
    ∃ (g₀ : AffineCoordinateRingBar X) (f₀ : AffineCoordinateRingBar X),
      evalBarAtPoint k X P hP g₀ ≠ 0 ∧
      (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))) f₀ =
      (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))) g₀ *
        MvPolynomial.eval₂
          ((algebraMap (AffineCoordinateRingBar X)
            (FractionRing (AffineCoordinateRingBar X))).comp
            ((Ideal.Quotient.mk (idealOfAlgebraicSet X)).comp MvPolynomial.C))
          (functionFieldMorphismComponents θ) f ∧
      MvPolynomial.eval (evalTupleAt (functionFieldMorphismComponents θ) P hP hreg) f *
        evalBarAtPoint k X P hP g₀ = evalBarAtPoint k X P hP f₀ := by
  induction f using MvPolynomial.induction_on with
  | C c =>

    refine ⟨1, Ideal.Quotient.mk _ (MvPolynomial.C c), ?_, ?_, ?_⟩
    · simp [map_one]
    · simp [MvPolynomial.eval₂_C, RingHom.comp_apply, map_one, one_mul]; rfl
    · simp [MvPolynomial.eval_C, map_one, mul_one, evalBarAtPoint_mk]
  | add p q ihp ihq =>

    obtain ⟨gp, fp, hgp_ne, hfp_eq, hfp_eval⟩ := ihp
    obtain ⟨gq, fq, hgq_ne, hfq_eq, hfq_eval⟩ := ihq
    refine ⟨gp * gq, gq * fp + gp * fq, ?_, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero hgp_ne hgq_ne
    · simp only [map_mul, map_add, MvPolynomial.eval₂_add]
      rw [mul_add]
      congr 1
      · rw [hfp_eq]; ring
      · rw [hfq_eq]; ring
    · simp only [map_mul, map_add]
      linear_combination (evalBarAtPoint k X P hP gq) * hfp_eval +
        (evalBarAtPoint k X P hP gp) * hfq_eval

  | mul_X p j ihp =>

    obtain ⟨gp, fp, hgp_ne, hfp_eq, hfp_eval⟩ := ihp

    obtain ⟨gj, hgj_ne, hgj_mem⟩ := hreg j
    obtain ⟨aj, haj_eq⟩ := hgj_mem

    refine ⟨gp * gj, fp * aj, ?_, ?_, ?_⟩
    · rw [map_mul]; exact mul_ne_zero hgp_ne hgj_ne
    · simp only [map_mul, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X]
      rw [mul_comm (algebraMap _ _ gp) (algebraMap _ _ gj), mul_assoc (algebraMap _ _ gj),
          ← mul_assoc (algebraMap _ _ gp)]
      rw [hfp_eq]
      rw [mul_assoc, mul_comm (MvPolynomial.eval₂ _ _ p), ← mul_assoc, haj_eq]
      ring
    · simp only [MvPolynomial.eval_X, map_mul]
      have hσj : evalTupleAt (functionFieldMorphismComponents θ) P hP hreg j *
          evalBarAtPoint k X P hP gj = evalBarAtPoint k X P hP aj := by
        unfold evalTupleAt
        rw [evalRatFunAt_eq (functionFieldMorphismComponents θ j) P hP (hreg j) gj aj hgj_ne haj_eq.symm]
        rw [div_mul_cancel₀ _ hgj_ne]


      calc (MvPolynomial.eval _ p) *
            (evalTupleAt (functionFieldMorphismComponents θ) P hP hreg j) *
            ((evalBarAtPoint k X P hP gp) * (evalBarAtPoint k X P hP gj))
          = ((MvPolynomial.eval _ p) * (evalBarAtPoint k X P hP gp)) *
            ((evalTupleAt (functionFieldMorphismComponents θ) P hP hreg j) *
             (evalBarAtPoint k X P hP gj)) := by ring
        _ = (evalBarAtPoint k X P hP fp) * (evalBarAtPoint k X P hP aj) := by
            rw [hfp_eval, hσj]

/-- Compatibility of a $\bar k$-algebra hom $\theta$ with the substitution homomorphism:
applying $\theta$ to the class of $f \in \bar k[Y]$ in $\bar k(Y)$ equals evaluating $f$
via substitution at the components $\theta(Y_i)$. -/
lemma theta_algebraMap_mk_eq_eval₂
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X))
    (hθ : IsKbarFunctionFieldHom θ)
    (f : MvPolynomial (Fin n_cod) (AlgebraicClosure k)) :
    θ ((algebraMap (AffineCoordinateRingBar Y)
        (FractionRing (AffineCoordinateRingBar Y)))
        (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)) =
    MvPolynomial.eval₂
      ((algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))).comp
        ((Ideal.Quotient.mk (idealOfAlgebraicSet X)).comp MvPolynomial.C))
      (functionFieldMorphismComponents θ) f := by

  let ϕ : MvPolynomial (Fin n_cod) (AlgebraicClosure k) →+*
    FractionRing (AffineCoordinateRingBar X) :=
    θ.comp ((algebraMap (AffineCoordinateRingBar Y)
      (FractionRing (AffineCoordinateRingBar Y))).comp
      (Ideal.Quotient.mk (idealOfAlgebraicSet Y)))

  have h := MvPolynomial.map_mvPolynomial_eq_eval₂ ϕ f


  change θ _ = _ at h

  rw [show (ϕ.comp MvPolynomial.C) =
    (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))).comp
        ((Ideal.Quotient.mk (idealOfAlgebraicSet X)).comp MvPolynomial.C) from
    RingHom.ext (fun c => hθ c)] at h
  rw [show (fun s => ϕ (MvPolynomial.X s)) = functionFieldMorphismComponents θ from
    funext (fun j => rfl)] at h
  exact h

/-- Characterizing property of the induced rational map: evaluating a polynomial $f$
in the target coordinates at the image point $\theta(P)$ equals the value of $\theta(f)$
at the point $P$. This is the key step proving compatibility of $\theta$ with point
evaluation. -/
theorem characterizing_property
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X))
    (hθ : IsKbarFunctionFieldHom θ)
    (f : MvPolynomial (Fin n_cod) (AlgebraicClosure k))
    (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
    (hreg : IsTupleRegularAt (functionFieldMorphismComponents θ) P hP)
    (hreg_θf : IsRegularAt
      (θ ((algebraMap (AffineCoordinateRingBar Y)
        (FractionRing (AffineCoordinateRingBar Y)))
        (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)))
      P hP) :
    MvPolynomial.eval (evalTupleAt (functionFieldMorphismComponents θ) P hP hreg) f =
    evalRatFunAt
      (θ ((algebraMap (AffineCoordinateRingBar Y)
        (FractionRing (AffineCoordinateRingBar Y)))
        (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)))
      P hP hreg_θf := by

  obtain ⟨g₀, f₀, hg₀_ne, hf₀_eq, hf₀_eval⟩ :=
    eval₂_clearing_denominators θ hθ P hP hreg f


  have h_eval₂ := theta_algebraMap_mk_eq_eval₂ θ hθ f


  have hgr : (algebraMap (AffineCoordinateRingBar X)
    (FractionRing (AffineCoordinateRingBar X))) g₀ *
    θ ((algebraMap (AffineCoordinateRingBar Y)
      (FractionRing (AffineCoordinateRingBar Y)))
      (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)) =
    (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))) f₀ := by
    rw [h_eval₂]; exact hf₀_eq.symm

  rw [evalRatFunAt_eq _ P hP hreg_θf g₀ f₀ hg₀_ne hgr]

  rw [eq_div_iff hg₀_ne]

  exact hf₀_eval

/-- Any ring homomorphism $\theta : \bar k(Y) \to \bar k(X)$ kills the ideal $\mathcal{I}(Y)$:
the polynomial $f \in \mathcal{I}(Y)$ becomes zero in $\bar k[Y]$ (since the quotient is
the coordinate ring), so its image in $\bar k(Y)$ is zero, hence $\theta(f) = 0$. -/
lemma θ_kills_ideal {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X))
    (f : MvPolynomial (Fin n_cod) (AlgebraicClosure k))
    (hf : f ∈ idealOfAlgebraicSet Y) :
    θ ((algebraMap (AffineCoordinateRingBar Y)
      (FractionRing (AffineCoordinateRingBar Y)))
      (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)) = 0 := by
  have hmk : (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f : AffineCoordinateRingBar Y) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hf
  have : (Ideal.Quotient.mk (idealOfAlgebraicSet Y)) f = (0 : AffineCoordinateRingBar Y) :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hf
  rw [this, map_zero, map_zero]

/-- The zero rational function is regular at every point: with denominator $g = 1$ (which
satisfies $g(P) = 1 \neq 0$), we have $g \cdot 0 = 0$ in the image of $\bar k[X]$. -/
lemma isRegularAt_zero {m : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    (P : Fin m → AlgebraicClosure k) (hP : P ∈ X) :
    IsRegularAt (0 : FractionRing (AffineCoordinateRingBar X)) P hP := by
  refine ⟨1, ?_, ?_⟩
  · simp [evalBarAtPoint, ne_eq, one_ne_zero, not_false_eq_true]
  · simp only [map_one, one_mul]
    exact ⟨0, by simp⟩

/-- The value of the zero rational function at any point is zero. -/
lemma evalRatFunAt_zero {m : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
    (hreg : IsRegularAt (0 : FractionRing (AffineCoordinateRingBar X)) P hP) :
    evalRatFunAt 0 P hP hreg = 0 := by


  unfold evalRatFunAt
  have hmem := hreg.choose_spec.2
  have h_eq : (algebraMap (AffineCoordinateRingBar X)
    (FractionRing (AffineCoordinateRingBar X))) hmem.choose =
    (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))) hreg.choose * 0 := hmem.choose_spec
  have h_zero : hmem.choose = 0 := by
    have : (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))) hmem.choose = 0 := by
      rw [h_eq]; ring
    rwa [map_eq_zero_iff _ (IsFractionRing.injective _ _)] at this
  simp [evalBarAtPoint]

/-- The image of the rational map induced by a $\bar k$-algebra homomorphism $\theta$
lands in $Y$: at any point $P$ where the components are regular, the evaluated tuple
$(\theta(Y_1)(P), \dots, \theta(Y_{n_\mathrm{cod}})(P))$ satisfies every equation of
$\mathcal{I}(Y)$, hence lies in $Y$. -/
theorem functionFieldMorphism_image_mem {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X))
    (hθ : IsKbarFunctionFieldHom θ)
    (hY : IsAlgebraicSubset k n_cod Y)
    (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
    (hreg : IsTupleRegularAt (functionFieldMorphismComponents θ) P hP) :
    evalTupleAt (functionFieldMorphismComponents θ) P hP hreg ∈ Y := by


  suffices h : evalTupleAt (functionFieldMorphismComponents θ) P hP hreg ∈
      AlgebraicSet k n_cod ((idealOfAlgebraicSet Y) : Set _) by
    rwa [algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset k hY] at h
  intro f hf


  have hθf_zero := θ_kills_ideal θ f hf
  have hreg_0 : IsRegularAt
      (θ ((algebraMap (AffineCoordinateRingBar Y)
        (FractionRing (AffineCoordinateRingBar Y)))
        (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)))
      P hP := by
    rw [hθf_zero]; exact isRegularAt_zero P hP
  rw [characterizing_property θ hθ f P hP hreg hreg_0]


  have hreg_0' : IsRegularAt (0 : FractionRing (AffineCoordinateRingBar X)) P hP :=
    hθf_zero ▸ hreg_0
  have : evalRatFunAt (θ ((algebraMap (AffineCoordinateRingBar Y)
        (FractionRing (AffineCoordinateRingBar Y)))
        (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f))) P hP hreg_0 =
    evalRatFunAt 0 P hP hreg_0' := by
    congr 1
  rw [this]
  exact evalRatFunAt_zero P hP hreg_0'

/-- The *rational map induced* by a $\bar k$-algebra homomorphism $\theta : \bar k(Y) \to
\bar k(X)$: its components are $\theta(Y_1), \dots, \theta(Y_{n_\mathrm{cod}})$, and the
image-membership condition is provided by `functionFieldMorphism_image_mem`. This is the
construction of Theorem 15.8(iii) producing $\varphi$ from $\theta$. -/
noncomputable def functionFieldMorphismInducedMap {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X))
    (hθ : IsKbarFunctionFieldHom θ)
    (hY : IsAlgebraicSubset k n_cod Y) :
    AffineRationalMap X Y where
  components := functionFieldMorphismComponents θ
  image_mem := functionFieldMorphism_image_mem θ hθ hY

/-- If a rational function $r \in \bar k(X)$ vanishes wherever it is regular together
with a given tuple $\varphi$, then $r = 0$. The proof uses the Nullstellensatz to show
that the corresponding numerator must be in $\mathcal{I}(X)$. -/
lemma fractionRing_element_zero_of_eval_zero_on_tupleRegular
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    (r : FractionRing (AffineCoordinateRingBar X))
    (φ : Fin n_cod → FractionRing (AffineCoordinateRingBar X))
    (h : ∀ (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
      (hreg_comp : IsTupleRegularAt φ P hP)
      (hreg : IsRegularAt r P hP),
      evalRatFunAt r P hP hreg = 0) :
    r = 0 := by
  by_contra hr

  obtain ⟨⟨a_r, ⟨b_r, hb_r⟩⟩, hab_r⟩ := IsLocalization.surj
    (nonZeroDivisors (AffineCoordinateRingBar X)) r

  simp only at hab_r

  have ha_ne : a_r ≠ 0 := by
    intro ha0; apply hr
    have h1 : r * (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))) b_r = 0 := by
      rw [hab_r, ha0, map_zero]
    have hb_ne_frac : (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))) b_r ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
      exact mem_nonZeroDivisors_iff_ne_zero.mp hb_r
    exact (mul_eq_zero.mp h1).resolve_right hb_ne_frac
  have hb_ne : b_r ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb_r

  choose cd_j hcd_j using
    (fun j => IsLocalization.surj (nonZeroDivisors (AffineCoordinateRingBar X)) (φ j))


  set product := a_r * (b_r * ∏ j : Fin n_cod, ((cd_j j).2 : AffineCoordinateRingBar X))
    with hprod_def

  have hprod_ne : product ≠ 0 := by
    apply mul_ne_zero ha_ne (mul_ne_zero hb_ne _)
    exact Finset.prod_ne_zero_iff.mpr (fun j _ =>
      mem_nonZeroDivisors_iff_ne_zero.mp (cd_j j).2.property)

  have hprod_vanishes : ∀ (P : Fin m → AlgebraicClosure k) (hP : P ∈ X),
      evalBarAtPoint k X P hP product = 0 := by
    intro P hP
    simp only [hprod_def, map_mul, map_prod]
    by_cases hbP : evalBarAtPoint k X P hP b_r = 0
    · simp [hbP]
    by_cases hdP : ∃ j, evalBarAtPoint k X P hP ((cd_j j).2 : AffineCoordinateRingBar X) = 0
    · obtain ⟨j, hjP⟩ := hdP
      have : (∏ i : Fin n_cod,
          evalBarAtPoint k X P hP ((cd_j i).2 : AffineCoordinateRingBar X)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) hjP
      simp [this]
    push_neg at hdP


    have hab_comm : (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))) b_r * r =
        (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))) a_r := by rw [mul_comm]; exact hab_r
    have hreg : IsRegularAt r P hP :=
      ⟨b_r, hbP, ⟨a_r, hab_comm.symm⟩⟩
    have hreg_comp : IsTupleRegularAt φ P hP := by
      intro j
      exact ⟨((cd_j j).2 : AffineCoordinateRingBar X), hdP j,
        ⟨(cd_j j).1, ((hcd_j j).symm.trans (mul_comm _ _))⟩⟩

    have h_eval_zero := h P hP hreg_comp hreg
    have h_eq := evalRatFunAt_eq r P hP hreg b_r a_r hbP hab_comm
    rw [h_eq] at h_eval_zero
    have haP : evalBarAtPoint k X P hP a_r = 0 := by
      rcases div_eq_zero_iff.mp h_eval_zero with haP | hbP'
      · exact haP
      · exact absurd hbP' hbP
    simp [haP]


  have hprod_zero : product = 0 := by
    obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective product
    suffices h_mem : f ∈ idealOfAlgebraicSet X by
      rw [← hf]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr h_mem
    rw [mem_idealOfAlgebraicSet_iff]
    intro P hP
    have := hprod_vanishes P hP
    rw [← hf, evalBarAtPoint_mk] at this
    exact this

  exact hprod_ne hprod_zero

/-- The rational map induced by a $\bar k$-algebra homomorphism of function fields is
*dominant*: the image of the resulting rational map is Zariski-dense in $Y$. This is one
of the key conclusions of Theorem 15.8(iii). -/
theorem functionFieldMorphismInducedMap_isDominant
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X))
    (hθ : IsKbarFunctionFieldHom θ)
    (hY : IsAlgebraicSubset k n_cod Y) :
    IsDominantRationalMap Y (functionFieldMorphismInducedMap θ hθ hY) := by


  unfold IsDominantRationalMap

  apply Set.Subset.antisymm


  · intro Q hQ


    simp only [zariskiClosure, AlgebraicSet, Set.mem_setOf_eq, SetLike.mem_coe,
      mem_idealOfAlgebraicSet_iff] at hQ


    rw [← algebraicSet_idealOfAlgebraicSet_of_isAlgebraicSubset k hY]
    intro f hf

    apply hQ
    intro R hR

    obtain ⟨P, hP, hreg, rfl⟩ := hR

    exact hf _ (functionFieldMorphism_image_mem θ hθ hY P hP hreg)


  · intro Q hQ


    simp only [zariskiClosure, AlgebraicSet, Set.mem_setOf_eq, SetLike.mem_coe,
      mem_idealOfAlgebraicSet_iff]
    intro f hf_vanishes_on_image


    have hθf_zero : θ ((algebraMap (AffineCoordinateRingBar Y)
        (FractionRing (AffineCoordinateRingBar Y)))
        (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)) = 0 := by
      apply fractionRing_element_zero_of_eval_zero_on_tupleRegular
        _ (functionFieldMorphismComponents θ)
      intro P hP hreg_comp hreg_θf

      rw [← characterizing_property θ hθ f P hP hreg_comp hreg_θf]


      apply hf_vanishes_on_image
      exact ⟨P, hP, hreg_comp, rfl⟩

    have hf_bar_zero : (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f :
        AffineCoordinateRingBar Y) = 0 := by
      have h_alg_zero : (algebraMap (AffineCoordinateRingBar Y)
          (FractionRing (AffineCoordinateRingBar Y)))
          (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f) = 0 := by
        have h_inj := θ.injective
        exact h_inj (by rw [hθf_zero, map_zero])
      rwa [map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h_alg_zero

    have hf_mem : f ∈ idealOfAlgebraicSet Y :=
      Ideal.Quotient.eq_zero_iff_mem.mp hf_bar_zero
    exact hf_mem Q hQ


/-- Compatibility of coordinate-ring pullbacks with composition: if $\psi \circ \varphi$
is a rational map matching the formal composition of pullbacks on coordinates, then
$(\psi \circ \varphi)^* = \varphi^* \circ \psi^*$ as ring maps $\bar k[Z] \to \bar k[X]$. -/
theorem dominantPullbackOnCoordRing_comp

    {k : Type*} [Field k]
    {m n p : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n → AlgebraicClosure k)}
    {Z : Set (Fin p → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    [IsDomain (AffineCoordinateRingBar Z)]
    (φ : AffineRationalMap X Y)
    (ψ : AffineRationalMap Y Z)
    (ψφ : AffineRationalMap X Z)
    (hcomp : ∀ (i : Fin p),
      (ψφ).components i =
        (algebraMap (AffineCoordinateRingBar X)
          (FractionRing (AffineCoordinateRingBar X)))
          (dominantPullbackOnCoordRing φ
            (dominantPullbackOnCoordRing ψ
              (Ideal.Quotient.mk (idealOfAlgebraicSet Z) (MvPolynomial.X i))))) :
    dominantPullbackOnCoordRing ψφ =
      (dominantPullbackOnCoordRing φ).comp (dominantPullbackOnCoordRing ψ) := by


  suffices h : (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))).comp (dominantPullbackOnCoordRing ψφ) =
    (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))).comp
        ((dominantPullbackOnCoordRing φ).comp (dominantPullbackOnCoordRing ψ)) by
    ext g
    exact IsFractionRing.injective (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X)) (RingHom.congr_fun h g)

  have hLHS : (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))).comp (dominantPullbackOnCoordRing ψφ) =
    dominantPullbackToFractionRing ψφ :=
    RingHom.ext (algebraMap_dominantPullbackOnCoordRing ψφ)
  rw [hLHS]

  have hRHS : (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))).comp
        ((dominantPullbackOnCoordRing φ).comp (dominantPullbackOnCoordRing ψ)) =
    (dominantPullbackToFractionRing φ).comp (dominantPullbackOnCoordRing ψ) := by
    ext g
    simp only [RingHom.comp_apply]
    exact algebraMap_dominantPullbackOnCoordRing φ _
  rw [hRHS]


  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  ·
    intro r
    show (dominantPullbackToFractionRing ψφ) (Ideal.Quotient.mk _ (MvPolynomial.C r)) =
      ((dominantPullbackToFractionRing φ).comp (dominantPullbackOnCoordRing ψ))
        (Ideal.Quotient.mk _ (MvPolynomial.C r))
    rw [dominantPullbackToFractionRing_mk]
    simp only [dominantPullbackSubstHom, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    rw [dominantPullbackOnCoordRing_preserves_C]
    rw [dominantPullbackToFractionRing_mk]
    simp only [dominantPullbackSubstHom, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
  ·
    intro i
    show (dominantPullbackToFractionRing ψφ) (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      ((dominantPullbackToFractionRing φ).comp (dominantPullbackOnCoordRing ψ))
        (Ideal.Quotient.mk _ (MvPolynomial.X i))
    rw [dominantPullbackToFractionRing_mk]
    simp only [dominantPullbackSubstHom, MvPolynomial.eval₂Hom_X', RingHom.comp_apply]


    rw [← algebraMap_dominantPullbackOnCoordRing]
    exact hcomp i

/-- Theorem 15.8(iii) (functoriality of the function-field pullback). For composable
dominant rational maps $\varphi : X \dashrightarrow Y$ and $\psi : Y \dashrightarrow Z$
with composite $\psi \circ \varphi$, the function-field pullbacks compose contravariantly:
$(\psi \circ \varphi)^* = \varphi^* \circ \psi^*$. -/
theorem theorem_15_8_iii
    {k : Type*} [Field k]
    {m n p : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n → AlgebraicClosure k)}
    {Z : Set (Fin p → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    [IsDomain (AffineCoordinateRingBar Z)]
    (φ : AffineRationalMap X Y)
    (ψ : AffineRationalMap Y Z)
    (hdomφ : IsDominantRationalMap Y φ)
    (hdomψ : IsDominantRationalMap Z ψ)
    (ψφ : AffineRationalMap X Z)
    (hdomψφ : IsDominantRationalMap Z ψφ)
    (hcomp : ∀ (i : Fin p),
      (ψφ).components i =
        (algebraMap (AffineCoordinateRingBar X)
          (FractionRing (AffineCoordinateRingBar X)))
          (dominantPullbackOnCoordRing φ
            (dominantPullbackOnCoordRing ψ
              (Ideal.Quotient.mk (idealOfAlgebraicSet Z) (MvPolynomial.X i))))) :
    dominantRationalMapPullback ψφ hdomψφ =
      (dominantRationalMapPullback φ hdomφ).comp
        (dominantRationalMapPullback ψ hdomψ) := by


  apply IsLocalization.ringHom_ext (nonZeroDivisors (AffineCoordinateRingBar Z))
  ext z
  simp only [RingHom.comp_apply]

  show dominantRationalMapPullback ψφ hdomψφ
      (algebraMap (AffineCoordinateRingBar Z)
        (FractionRing (AffineCoordinateRingBar Z)) z) =
    dominantRationalMapPullback φ hdomφ
      (dominantRationalMapPullback ψ hdomψ
        (algebraMap (AffineCoordinateRingBar Z)
          (FractionRing (AffineCoordinateRingBar Z)) z))

  rw [dominantPullbackOnCoordRing_comm ψφ hdomψφ z]
  rw [dominantPullbackOnCoordRing_comm ψ hdomψ z]
  rw [dominantPullbackOnCoordRing_comm φ hdomφ (dominantPullbackOnCoordRing ψ z)]


  congr 1

  have hcoord := dominantPullbackOnCoordRing_comp φ ψ ψφ hcomp
  rw [hcoord, RingHom.comp_apply]

set_option maxHeartbeats 800000 in
/-- Corollary 15.9 (roundtrip on maps). Starting from a dominant rational map $\varphi$,
forming its function-field pullback $\varphi^*$, and then taking the rational map induced
by $\varphi^*$ recovers $\varphi$. This is one direction of the equivalence in
Corollary 15.9. -/
theorem corollary_15_9_roundtrip_maps_eq
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y)
    (hdom : IsDominantRationalMap Y φ)
    (hθ : IsKbarFunctionFieldHom (dominantRationalMapPullback φ hdom))
    (hY : IsAlgebraicSubset k n_cod Y) :
    functionFieldMorphismInducedMap
      (dominantRationalMapPullback φ hdom) hθ hY = φ := by

  have hcomp : (functionFieldMorphismInducedMap
      (dominantRationalMapPullback φ hdom) hθ hY).components = φ.components := by
    ext j


    show (dominantRationalMapPullback φ hdom)
      (algebraMap (AffineCoordinateRingBar Y)
        (FractionRing (AffineCoordinateRingBar Y))
        (Ideal.Quotient.mk (idealOfAlgebraicSet Y) (MvPolynomial.X j))) = φ.components j

    rw [dominantPullbackOnCoordRing_comm φ hdom]

    rw [algebraMap_dominantPullbackOnCoordRing]

    rw [dominantPullbackToFractionRing_mk]

    simp only [dominantPullbackSubstHom, MvPolynomial.eval₂Hom_X']


  rcases φ with ⟨comps, img⟩
  simp only [functionFieldMorphismInducedMap, AffineRationalMap.mk.injEq] at hcomp ⊢
  exact hcomp
set_option maxHeartbeats 800000 in
/-- Coordinate-ring version of the roundtrip on morphisms: a $\bar k$-algebra hom $\theta$
restricted to the image of $\bar k[Y]$ equals the function-field pullback of the rational
map induced by $\theta$. -/
theorem corollary_15_9_roundtrip_morphisms_coordRing
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X))
    (hθ : IsKbarFunctionFieldHom θ)
    (hY : IsAlgebraicSubset k n_cod Y)
    (g : AffineCoordinateRingBar Y) :
    θ ((algebraMap (AffineCoordinateRingBar Y)
        (FractionRing (AffineCoordinateRingBar Y))) g) =
    (algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X)))
      (dominantPullbackOnCoordRing (functionFieldMorphismInducedMap θ hθ hY) g) := by


  rw [algebraMap_dominantPullbackOnCoordRing]


  revert g
  refine Quotient.ind ?_
  intro f


  change θ ((algebraMap (AffineCoordinateRingBar Y)
      (FractionRing (AffineCoordinateRingBar Y)))
      (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)) =
    dominantPullbackToFractionRing (functionFieldMorphismInducedMap θ hθ hY)
      (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)

  rw [theta_algebraMap_mk_eq_eval₂ θ hθ f]

  rw [dominantPullbackToFractionRing_mk]


  simp only [dominantPullbackSubstHom, MvPolynomial.coe_eval₂Hom]


  rfl
set_option maxHeartbeats 800000 in
/-- Corollary 15.9 (roundtrip on morphisms). Starting from a $\bar k$-algebra hom
$\theta : \bar k(Y) \to \bar k(X)$, forming the induced rational map and then taking its
function-field pullback recovers $\theta$. The other half of the equivalence in
Corollary 15.9. -/
theorem corollary_15_9_roundtrip_morphisms
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X))
    (hθ : IsKbarFunctionFieldHom θ)
    (hY : IsAlgebraicSubset k n_cod Y) :
    dominantRationalMapPullback
      (functionFieldMorphismInducedMap θ hθ hY)
      (functionFieldMorphismInducedMap_isDominant θ hθ hY) = θ := by


  unfold dominantRationalMapPullback
  exact IsFractionRing.lift_unique _ (fun g =>
    corollary_15_9_roundtrip_morphisms_coordRing θ hθ hY g)

/-- Theorem 15.8(ii). For every $\bar k$-algebra homomorphism $\theta : \bar k(Y) \to
\bar k(X)$ there exists a unique dominant rational map $\varphi : X \dashrightarrow Y$
whose function-field pullback is $\theta$, and which is characterized by
$f(\varphi(P)) = \theta(f)(P)$ at points where both sides are defined. -/
theorem theorem_15_8_ii {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (θ : FractionRing (AffineCoordinateRingBar Y) →+*
         FractionRing (AffineCoordinateRingBar X))
    (hθ : IsKbarFunctionFieldHom θ)
    (hY : IsAlgebraicSubset k n_cod Y) :
    ∃ (φ : AffineRationalMap X Y) (hdom : IsDominantRationalMap Y φ),

      dominantRationalMapPullback φ hdom = θ ∧


      (∀ (f : MvPolynomial (Fin n_cod) (AlgebraicClosure k))
        (P : Fin m → AlgebraicClosure k) (hP : P ∈ X)
        (hreg : IsTupleRegularAt φ.components P hP)
        (hreg_θf : IsRegularAt
          (θ ((algebraMap (AffineCoordinateRingBar Y)
            (FractionRing (AffineCoordinateRingBar Y)))
            (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)))
          P hP),
        MvPolynomial.eval (evalTupleAt φ.components P hP hreg) f =
        evalRatFunAt
          (θ ((algebraMap (AffineCoordinateRingBar Y)
            (FractionRing (AffineCoordinateRingBar Y)))
            (Ideal.Quotient.mk (idealOfAlgebraicSet Y) f)))
          P hP hreg_θf) :=
  ⟨functionFieldMorphismInducedMap θ hθ hY,
   functionFieldMorphismInducedMap_isDominant θ hθ hY,
   corollary_15_9_roundtrip_morphisms θ hθ hY,
   fun f P hP hreg hreg_θf => characterizing_property θ hθ f P hP hreg hreg_θf⟩

end Theorem158

section Corollary1512

variable {k : Type*} [Field k]

open MvPolynomial

/-- The natural ring homomorphism $k[X] \to \bar k[X]$ extending scalars from the base
field $k$ to its algebraic closure $\bar k$: descends the map induced on polynomials by
$k \hookrightarrow \bar k$ to the quotient defining $k[X]$. -/
noncomputable def coordRingToBar {n : ℕ}
    (X : Set (Fin n → AlgebraicClosure k)) :
    AffineCoordinateRing X →+* AffineCoordinateRingBar X :=
  Ideal.Quotient.lift (idealOverK X)
    ((Ideal.Quotient.mk (idealOfAlgebraicSet X)).comp
      (MvPolynomial.map (algebraMap k (AlgebraicClosure k))))
    (fun f hf => by
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (mem_idealOverK_iff.mp hf))

/-- The composite $k[X] \to \bar k[X] \hookrightarrow \bar k(X)$ is injective. Needed to
extend the scalar-extension map to the level of function fields. -/
theorem coordRingToBar_comp_algebraMap_injective
    {k : Type*} [Field k]
    {n : ℕ} (X : Set (Fin n → AlgebraicClosure k))
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRing X)] :
    Function.Injective
      ((algebraMap (AffineCoordinateRingBar X)
        (FractionRing (AffineCoordinateRingBar X))).comp
        (coordRingToBar X)) :=
  (IsFractionRing.injective (AffineCoordinateRingBar X)
    (FractionRing (AffineCoordinateRingBar X))).comp (fun a b hab => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hab' : Ideal.Quotient.mk (idealOfAlgebraicSet X)
        (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) a) =
      Ideal.Quotient.mk (idealOfAlgebraicSet X)
        (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) b) := by
      change coordRingToBar X (Ideal.Quotient.mk (idealOverK X) a) =
        coordRingToBar X (Ideal.Quotient.mk (idealOverK X) b) at hab
      simp only [coordRingToBar] at hab
      exact hab
    rw [Ideal.Quotient.eq] at hab'
    have hmem : a - b ∈ idealOverK X :=
      mem_idealOverK_iff.mpr (by rwa [map_sub])
    exact Ideal.Quotient.eq.mpr hmem)

/-- Scalar extension on function fields: the natural homomorphism $k(X) \to \bar k(X)$
obtained by extending the coordinate-ring map $k[X] \to \bar k[X]$ to fraction fields. -/
noncomputable def functionFieldToBar {n : ℕ}
    (X : Set (Fin n → AlgebraicClosure k))
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRing X)] :
    FractionRing (AffineCoordinateRing X) →+*
    FractionRing (AffineCoordinateRingBar X) :=
  IsFractionRing.lift
    (g := (algebraMap (AffineCoordinateRingBar X)
      (FractionRing (AffineCoordinateRingBar X))).comp
      (coordRingToBar X))
    (coordRingToBar_comp_algebraMap_injective X)

/-- A rational map $\varphi : X \dashrightarrow Y$ is *defined over $k$* if each of its
components lies in the image of $k(X) \to \bar k(X)$, i.e. can be represented by a tuple
of rational functions with coefficients in the base field $k$. -/
def AffineRationalMap.IsDefinedOverK {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRing X)]
    (φ : AffineRationalMap X Y) : Prop :=
  ∀ j : Fin n_cod, φ.components j ∈
    Set.range (functionFieldToBar X)

/-- The coordinate-ring pullback over $k$: for a dominant rational map defined over $k$
between $k$-defined varieties, the pullback descends to a ring map $k[Y] \to k[X]$ on
the $k$-coordinate rings. -/
noncomputable def pullbackOnCoordRingOverK
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    [IsDomain (AffineCoordinateRing X)]
    [IsDomain (AffineCoordinateRing Y)]
    (φ : AffineRationalMap X Y)
    (hdom : IsDominantRationalMap Y φ)
    (hdefX : IsDefinedOver (k := k) X)
    (hdefY : IsDefinedOver (k := k) Y)
    (hφk : φ.IsDefinedOverK) :
    AffineCoordinateRing Y →+* AffineCoordinateRing X := by sorry

/-- Compatibility square between the $k$-pullback and the $\bar k$-pullback on coordinate
rings: pulling back $g$ over $k$ and then extending scalars to $\bar k$ equals first
extending scalars and then pulling back over $\bar k$. -/
theorem pullbackOnCoordRingOverK_comm
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    [IsDomain (AffineCoordinateRing X)]
    [IsDomain (AffineCoordinateRing Y)]
    (φ : AffineRationalMap X Y)
    (hdom : IsDominantRationalMap Y φ)
    (hdefX : IsDefinedOver (k := k) X)
    (hdefY : IsDefinedOver (k := k) Y)
    (hφk : φ.IsDefinedOverK)
    (g : AffineCoordinateRing Y) :
    coordRingToBar X (pullbackOnCoordRingOverK φ hdom hdefX hdefY hφk g) =
      dominantPullbackOnCoordRing φ (coordRingToBar Y g) := by sorry

/-- Corollary 15.12 ($k$-rational function field pullback). For a dominant rational map
$\varphi : X \dashrightarrow Y$ defined over $k$ between $k$-defined varieties, there
exists a ring homomorphism $\psi : k(Y) \to k(X)$ compatible with the $\bar k$-pullback
under scalar extension: $\mathrm{ext} \circ \psi = \varphi^* \circ \mathrm{ext}$. -/
theorem corollary_15_12
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    [IsDomain (AffineCoordinateRing X)]
    [IsDomain (AffineCoordinateRing Y)]
    (φ : AffineRationalMap X Y)
    (hdom : IsDominantRationalMap Y φ)
    (hdefX : IsDefinedOver (k := k) X)
    (hdefY : IsDefinedOver (k := k) Y)
    (hφk : φ.IsDefinedOverK) :
    ∃ (ψ : FractionRing (AffineCoordinateRing Y) →+*
           FractionRing (AffineCoordinateRing X)),
      ∀ (r : FractionRing (AffineCoordinateRing Y)),
        functionFieldToBar X (ψ r) =
          dominantRationalMapPullback φ hdom (functionFieldToBar Y r) := by

  let ψ₀ := pullbackOnCoordRingOverK φ hdom hdefX hdefY hφk


  have hinj : Function.Injective
      ((algebraMap (AffineCoordinateRing X)
        (FractionRing (AffineCoordinateRing X))).comp ψ₀) := by


    apply Function.Injective.of_comp (f := functionFieldToBar X)


    show Function.Injective (fun a =>
      functionFieldToBar X
        (algebraMap (AffineCoordinateRing X)
          (FractionRing (AffineCoordinateRing X)) (ψ₀ a)))
    intro a b hab

    have ha : functionFieldToBar X
        (algebraMap (AffineCoordinateRing X)
          (FractionRing (AffineCoordinateRing X)) (ψ₀ a)) =
        algebraMap (AffineCoordinateRingBar X)
          (FractionRing (AffineCoordinateRingBar X))
          (dominantPullbackOnCoordRing φ (coordRingToBar Y a)) := by
      rw [show functionFieldToBar X
          (algebraMap (AffineCoordinateRing X)
            (FractionRing (AffineCoordinateRing X)) (ψ₀ a)) =
        ((algebraMap (AffineCoordinateRingBar X)
            (FractionRing (AffineCoordinateRingBar X))).comp
          (coordRingToBar X)) (ψ₀ a) from
        IsFractionRing.lift_algebraMap
          (coordRingToBar_comp_algebraMap_injective X) (ψ₀ a)]
      simp only [RingHom.comp_apply]
      rw [pullbackOnCoordRingOverK_comm]
    have hb : functionFieldToBar X
        (algebraMap (AffineCoordinateRing X)
          (FractionRing (AffineCoordinateRing X)) (ψ₀ b)) =
        algebraMap (AffineCoordinateRingBar X)
          (FractionRing (AffineCoordinateRingBar X))
          (dominantPullbackOnCoordRing φ (coordRingToBar Y b)) := by
      rw [show functionFieldToBar X
          (algebraMap (AffineCoordinateRing X)
            (FractionRing (AffineCoordinateRing X)) (ψ₀ b)) =
        ((algebraMap (AffineCoordinateRingBar X)
            (FractionRing (AffineCoordinateRingBar X))).comp
          (coordRingToBar X)) (ψ₀ b) from
        IsFractionRing.lift_algebraMap
          (coordRingToBar_comp_algebraMap_injective X) (ψ₀ b)]
      simp only [RingHom.comp_apply]
      rw [pullbackOnCoordRingOverK_comm]

    change functionFieldToBar X
        (algebraMap (AffineCoordinateRing X)
          (FractionRing (AffineCoordinateRing X)) (ψ₀ a)) =
      functionFieldToBar X
        (algebraMap (AffineCoordinateRing X)
          (FractionRing (AffineCoordinateRing X)) (ψ₀ b)) at hab
    rw [ha, hb] at hab


    have hinj_comp := dominant_pullback_injective φ hdom


    have hcr := hinj_comp hab

    have hcr_inj : Function.Injective (coordRingToBar Y) :=
      Function.Injective.of_comp (f := algebraMap (AffineCoordinateRingBar Y)
        (FractionRing (AffineCoordinateRingBar Y)))
        (coordRingToBar_comp_algebraMap_injective Y)
    exact hcr_inj hcr

  let ψ : FractionRing (AffineCoordinateRing Y) →+*
      FractionRing (AffineCoordinateRing X) :=
    IsFractionRing.lift hinj
  exact ⟨ψ, fun r => by


    have key : (functionFieldToBar X).comp ψ =
        (dominantRationalMapPullback φ hdom).comp (functionFieldToBar Y) := by


      let g_target : AffineCoordinateRing Y →+*
          FractionRing (AffineCoordinateRingBar X) :=
        ((algebraMap (AffineCoordinateRingBar X)
            (FractionRing (AffineCoordinateRingBar X))).comp
          (dominantPullbackOnCoordRing φ)).comp (coordRingToBar Y)
      have hg_inj : Function.Injective g_target := by
        exact (dominant_pullback_injective φ hdom).comp
          (Function.Injective.of_comp
            (f := algebraMap (AffineCoordinateRingBar Y)
              (FractionRing (AffineCoordinateRingBar Y)))
            (show Function.Injective
              ((algebraMap (AffineCoordinateRingBar Y)
                (FractionRing (AffineCoordinateRingBar Y))).comp
                (coordRingToBar Y)) from
              coordRingToBar_comp_algebraMap_injective Y))

      have hlhs : (functionFieldToBar X).comp ψ =
          IsFractionRing.lift hg_inj := by
        symm
        apply IsFractionRing.lift_unique
        intro x


        show functionFieldToBar X (ψ (algebraMap (AffineCoordinateRing Y)
          (FractionRing (AffineCoordinateRing Y)) x)) = g_target x

        rw [IsFractionRing.lift_algebraMap hinj x]


        change (IsFractionRing.lift (coordRingToBar_comp_algebraMap_injective X))
          (algebraMap (AffineCoordinateRing X)
            (FractionRing (AffineCoordinateRing X)) (ψ₀ x)) = g_target x
        rw [IsFractionRing.lift_algebraMap
            (coordRingToBar_comp_algebraMap_injective X) (ψ₀ x)]

        simp only [RingHom.comp_apply]
        rw [pullbackOnCoordRingOverK_comm φ hdom hdefX hdefY hφk x]

        rfl

      have hrhs : (dominantRationalMapPullback φ hdom).comp
          (functionFieldToBar Y) =
          IsFractionRing.lift hg_inj := by
        symm
        apply IsFractionRing.lift_unique
        intro x
        show ((dominantRationalMapPullback φ hdom).comp (functionFieldToBar Y))
          (algebraMap (AffineCoordinateRing Y)
            (FractionRing (AffineCoordinateRing Y)) x) =
          g_target x
        simp only [RingHom.comp_apply]

        rw [show functionFieldToBar Y
            (algebraMap (AffineCoordinateRing Y)
              (FractionRing (AffineCoordinateRing Y)) x) =
          ((algebraMap (AffineCoordinateRingBar Y)
              (FractionRing (AffineCoordinateRingBar Y))).comp
            (coordRingToBar Y)) x from
          IsFractionRing.lift_algebraMap
            (coordRingToBar_comp_algebraMap_injective Y) x]
        simp only [RingHom.comp_apply]


        exact dominantPullbackOnCoordRing_comm φ hdom (coordRingToBar Y x)
      rw [hlhs, hrhs]
    exact congr_fun (congr_arg DFunLike.coe key) r⟩

end Corollary1512

section Corollary159

variable (k : Type*) [Field k]

open MvPolynomial CategoryTheory

/-- The $\bar k$-algebra structure on $\bar k[Z]$ obtained from the natural map
$\bar k \hookrightarrow \bar k[x_1, \dots, x_n]$ followed by the quotient. -/
noncomputable instance instAlgebraAffineCoordinateRingBar {n : ℕ}
    (Z : Set (Fin n → AlgebraicClosure k)) :
    Algebra (AlgebraicClosure k) (AffineCoordinateRingBar Z) :=
  show Algebra (AlgebraicClosure k)
    (MvPolynomial (Fin n) (AlgebraicClosure k) ⧸ idealOfAlgebraicSet Z) from
    Ideal.Quotient.algebra (AlgebraicClosure k)

/-- Bundled object of the category of affine varieties (over $\bar k$) with domain
coordinate ring: packages a dimension, a carrier set, the algebraic-subset condition,
and the integral-domain property of $\bar k[X]$. -/
structure AffineVarietyDom where
  dim : ℕ
  carrier : Set (Fin dim → AlgebraicClosure k)
  isAlgebraic : IsAlgebraicSubset k dim carrier
  isDomain : IsDomain (AffineCoordinateRingBar carrier)

attribute [instance] AffineVarietyDom.isDomain

/-- A morphism in `AffineVarietyDom k`: a dominant rational map between the underlying
varieties, bundling a rational map and a proof that it is dominant. -/
@[ext]
structure AffineVarietyDom.Hom (V W : AffineVarietyDom k) where
  map : @AffineRationalMap k _ V.dim W.dim V.carrier W.carrier V.isDomain
  dominant : @IsDominantRationalMap k _ V.dim W.dim V.carrier
    V.isDomain W.carrier map

/-- The identity rational map on $V$: defined as the rational map induced by the
identity ring homomorphism on $\bar k(V)$, which is a $\bar k$-algebra homomorphism. -/
noncomputable def AffineVarietyDom.idMap
    {k : Type*} [Field k]
    (V : AffineVarietyDom k) :
    @AffineRationalMap k _ V.dim V.dim V.carrier V.carrier V.isDomain :=
  @functionFieldMorphismInducedMap k _ V.dim V.dim V.carrier V.carrier V.isDomain V.isDomain
    (RingHom.id _) (fun _ => rfl) V.isAlgebraic

/-- The identity rational map on $V$ is dominant: its image is all of $V$, hence
its Zariski closure is $V$. -/
theorem AffineVarietyDom.idMap_dominant
    {k : Type*} [Field k]
    (V : AffineVarietyDom k) :
    @IsDominantRationalMap k _ V.dim V.dim V.carrier
      V.isDomain V.carrier (AffineVarietyDom.idMap V) :=
  @functionFieldMorphismInducedMap_isDominant k _ V.dim V.dim V.carrier V.carrier V.isDomain V.isDomain
    (RingHom.id _) (fun _ => rfl) V.isAlgebraic

/-- The function-field pullback $\varphi^*$ is a morphism over $\bar k$: it fixes the
images of all constants $c \in \bar k$. (Primed variant used internally.) -/
theorem dominantRationalMapPullback_isKbarHom'
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y)
    (hdom : IsDominantRationalMap Y φ) :
    IsKbarFunctionFieldHom (dominantRationalMapPullback φ hdom) := by
  intro r

  rw [dominantPullbackOnCoordRing_comm φ hdom]

  rw [dominantPullbackOnCoordRing_preserves_C φ r]

/-- Composition of morphisms in `AffineVarietyDom`: defined by composing the
function-field pullbacks and then taking the induced rational map. -/
noncomputable def AffineVarietyDom.compMap
    {k : Type*} [Field k]
    {V W U : AffineVarietyDom k}
    (φ : AffineVarietyDom.Hom k V W)
    (ψ : AffineVarietyDom.Hom k W U) :
    @AffineRationalMap k _ V.dim U.dim V.carrier U.carrier V.isDomain :=
  let φ_star := @dominantRationalMapPullback k _ V.dim W.dim V.carrier W.carrier
    V.isDomain W.isDomain φ.map φ.dominant
  let ψ_star := @dominantRationalMapPullback k _ W.dim U.dim W.carrier U.carrier
    W.isDomain U.isDomain ψ.map ψ.dominant
  let θ := φ_star.comp ψ_star
  have hθ : @IsKbarFunctionFieldHom k _ V.dim U.dim V.carrier U.carrier V.isDomain U.isDomain θ := by
    intro r
    show φ_star (ψ_star _) = _
    rw [dominantRationalMapPullback_isKbarHom' ψ.map ψ.dominant r]
    exact dominantRationalMapPullback_isKbarHom' φ.map φ.dominant r
  @functionFieldMorphismInducedMap k _ V.dim U.dim V.carrier U.carrier V.isDomain U.isDomain
    θ hθ U.isAlgebraic

/-- The composition of two morphisms of `AffineVarietyDom` is itself dominant. -/
theorem AffineVarietyDom.compMap_dominant
    {k : Type*} [Field k]
    {V W U : AffineVarietyDom k}
    (φ : AffineVarietyDom.Hom k V W)
    (ψ : AffineVarietyDom.Hom k W U) :
    @IsDominantRationalMap k _ V.dim U.dim V.carrier
      V.isDomain U.carrier (AffineVarietyDom.compMap φ ψ) :=
  let φ_star := @dominantRationalMapPullback k _ V.dim W.dim V.carrier W.carrier
    V.isDomain W.isDomain φ.map φ.dominant
  let ψ_star := @dominantRationalMapPullback k _ W.dim U.dim W.carrier U.carrier
    W.isDomain U.isDomain ψ.map ψ.dominant
  let θ := φ_star.comp ψ_star
  have hθ : @IsKbarFunctionFieldHom k _ V.dim U.dim V.carrier U.carrier V.isDomain U.isDomain θ := by
    intro r
    show φ_star (ψ_star _) = _
    rw [dominantRationalMapPullback_isKbarHom' ψ.map ψ.dominant r]
    exact dominantRationalMapPullback_isKbarHom' φ.map φ.dominant r
  @functionFieldMorphismInducedMap_isDominant k _ V.dim U.dim V.carrier U.carrier V.isDomain U.isDomain
    θ hθ U.isAlgebraic

/-- Associativity of composition of morphisms in `AffineVarietyDom`, needed for the
category instance. -/
theorem AffineVarietyDom.comp_assoc
    {k : Type*} [Field k]
    {V W U T : AffineVarietyDom k}
    (f : AffineVarietyDom.Hom k V W)
    (g : AffineVarietyDom.Hom k W U)
    (h : AffineVarietyDom.Hom k U T) :
    (⟨AffineVarietyDom.compMap ⟨AffineVarietyDom.compMap f g,
        AffineVarietyDom.compMap_dominant f g⟩ h,
      AffineVarietyDom.compMap_dominant ⟨AffineVarietyDom.compMap f g,
        AffineVarietyDom.compMap_dominant f g⟩ h⟩ : AffineVarietyDom.Hom k V T) =
    ⟨AffineVarietyDom.compMap f ⟨AffineVarietyDom.compMap g h,
        AffineVarietyDom.compMap_dominant g h⟩,
      AffineVarietyDom.compMap_dominant f ⟨AffineVarietyDom.compMap g h,
        AffineVarietyDom.compMap_dominant g h⟩⟩ := by
  ext


  show AffineVarietyDom.compMap ⟨AffineVarietyDom.compMap f g,
    AffineVarietyDom.compMap_dominant f g⟩ h =
    AffineVarietyDom.compMap f ⟨AffineVarietyDom.compMap g h,
    AffineVarietyDom.compMap_dominant g h⟩
  unfold AffineVarietyDom.compMap
  simp only
  congr 1


  rw [corollary_15_9_roundtrip_morphisms, corollary_15_9_roundtrip_morphisms]
  exact RingHom.comp_assoc _ _ _

/-- Left identity law: composing with the identity morphism on $V$ gives $f$. -/
theorem AffineVarietyDom.id_comp
    {k : Type*} [Field k]
    {V W : AffineVarietyDom k}
    (f : AffineVarietyDom.Hom k V W) :
    (⟨AffineVarietyDom.compMap
        ⟨AffineVarietyDom.idMap V, AffineVarietyDom.idMap_dominant V⟩ f,
      AffineVarietyDom.compMap_dominant
        ⟨AffineVarietyDom.idMap V, AffineVarietyDom.idMap_dominant V⟩ f⟩ :
        AffineVarietyDom.Hom k V W) = f := by


  ext
  show AffineVarietyDom.compMap
    ⟨AffineVarietyDom.idMap V, AffineVarietyDom.idMap_dominant V⟩ f =
    f.map
  unfold AffineVarietyDom.compMap AffineVarietyDom.idMap
  simp only


  simp only [corollary_15_9_roundtrip_morphisms, RingHom.id_comp]
  exact corollary_15_9_roundtrip_maps_eq f.map f.dominant
    (dominantRationalMapPullback_isKbarHom' f.map f.dominant) W.isAlgebraic

/-- Right identity law: composing $f$ with the identity morphism on $W$ gives $f$. -/
theorem AffineVarietyDom.comp_id
    {k : Type*} [Field k]
    {V W : AffineVarietyDom k}
    (f : AffineVarietyDom.Hom k V W) :
    (⟨AffineVarietyDom.compMap f
        ⟨AffineVarietyDom.idMap W, AffineVarietyDom.idMap_dominant W⟩,
      AffineVarietyDom.compMap_dominant f
        ⟨AffineVarietyDom.idMap W, AffineVarietyDom.idMap_dominant W⟩⟩ :
        AffineVarietyDom.Hom k V W) = f := by

  ext
  show AffineVarietyDom.compMap f
    ⟨AffineVarietyDom.idMap W, AffineVarietyDom.idMap_dominant W⟩ =
    f.map
  unfold AffineVarietyDom.compMap AffineVarietyDom.idMap
  simp only

  simp only [corollary_15_9_roundtrip_morphisms, RingHom.comp_id]
  exact corollary_15_9_roundtrip_maps_eq f.map f.dominant
    (dominantRationalMapPullback_isKbarHom' f.map f.dominant) W.isAlgebraic

/-- Category structure on `AffineVarietyDom k`: objects are affine varieties (with
domain coordinate ring) and morphisms are dominant rational maps. Identities and
composition come from `idMap` and `compMap`, with the category laws established by
`id_comp`, `comp_id`, and `comp_assoc`. -/
noncomputable instance : Category (AffineVarietyDom k) where
  Hom V W := AffineVarietyDom.Hom k V W
  id V := ⟨AffineVarietyDom.idMap V, AffineVarietyDom.idMap_dominant V⟩
  comp f g := ⟨AffineVarietyDom.compMap f g,
    AffineVarietyDom.compMap_dominant f g⟩
  id_comp f := AffineVarietyDom.id_comp f
  comp_id f := AffineVarietyDom.comp_id f
  assoc f g h := AffineVarietyDom.comp_assoc f g h

/-- Bundled function field over $\bar k$: a field which is a finitely generated
$\bar k$-algebra. Used as the object type of the category of function fields. -/
structure FunctionFieldObj where
  carrier : Type*
  [fieldInst : Field carrier]
  [algInst : Algebra (AlgebraicClosure k) carrier]
  finitelyGenerated : Algebra.FiniteType (AlgebraicClosure k) carrier

attribute [instance] FunctionFieldObj.fieldInst FunctionFieldObj.algInst

/-- Coerce a `FunctionFieldObj` to its underlying field. -/
instance : CoeSort (FunctionFieldObj k) (Type*) := ⟨FunctionFieldObj.carrier⟩

/-- A morphism $F \to G$ in the category of function fields is a $\bar k$-algebra
homomorphism $G \to F$ on the underlying fields (note the direction: the category is
contravariant relative to the algebra-homomorphism direction). -/
@[ext]
structure FunctionFieldObj.Hom (F G : FunctionFieldObj k) where
  toAlgHom : G.carrier →ₐ[AlgebraicClosure k] F.carrier

/-- Category structure on `FunctionFieldObj k`: objects are finitely generated function
fields over $\bar k$ and morphisms are $\bar k$-algebra homomorphisms in the reversed
direction (so the resulting equivalence with `AffineVarietyDom` is covariant in this
formalisation). -/
noncomputable instance : Category (FunctionFieldObj k) where
  Hom F G := FunctionFieldObj.Hom k F G
  id F := ⟨AlgHom.id (AlgebraicClosure k) F.carrier⟩
  comp f g := ⟨f.toAlgHom.comp g.toAlgHom⟩

/-- The function field $\bar k(V) = \mathrm{Frac}(\bar k[V])$ of an affine variety
$V$ is a finitely generated $\bar k$-algebra. -/
theorem functionField_finitelyGenerated
    {k : Type*} [Field k]
    (V : AffineVarietyDom k) :
    Algebra.FiniteType (AlgebraicClosure k) (FractionRing (AffineCoordinateRingBar V.carrier)) := by sorry

/-- Object-level map for the function-field functor: an affine variety $V$ is sent to
the bundled function field $\bar k(V)$. -/
noncomputable def AffineVarietyDom.toFunctionFieldObj (V : AffineVarietyDom k) :
    FunctionFieldObj k where
  carrier := FractionRing (AffineCoordinateRingBar V.carrier)
  finitelyGenerated := functionField_finitelyGenerated V

/-- The function-field pullback $\varphi^*$ is $\bar k$-linear in the sense that
$\varphi^*(c \cdot x) = c \cdot \varphi^*(x)$ for any constant $c \in \bar k$ and
$x \in \bar k(W)$. -/
theorem pullback_isAlgHom
    {k : Type*} [Field k]
    (V W : AffineVarietyDom k)
    (f : AffineVarietyDom.Hom k V W) :
    ∀ (c : AlgebraicClosure k) (x : FractionRing (AffineCoordinateRingBar W.carrier)),
      @dominantRationalMapPullback k _ V.dim W.dim
        V.carrier W.carrier V.isDomain W.isDomain f.map f.dominant (c • x) =
      c • @dominantRationalMapPullback k _ V.dim W.dim
        V.carrier W.carrier V.isDomain W.isDomain f.map f.dominant x := by
  intro c x
  let φ := @dominantRationalMapPullback k _ V.dim W.dim
    V.carrier W.carrier V.isDomain W.isDomain f.map f.dominant

  rw [Algebra.smul_def, Algebra.smul_def, map_mul]


  congr 1

  rw [IsScalarTower.algebraMap_apply (AlgebraicClosure k) (AffineCoordinateRingBar W.carrier)
    (FractionRing (AffineCoordinateRingBar W.carrier))]
  rw [IsScalarTower.algebraMap_apply (AlgebraicClosure k) (AffineCoordinateRingBar V.carrier)
    (FractionRing (AffineCoordinateRingBar V.carrier))]


  have hkbar := dominantRationalMapPullback_isKbarHom' f.map f.dominant c


  exact hkbar

/-- The function-field pullback morphism, packaged as a `FunctionFieldObj.Hom`: a
$\bar k$-algebra homomorphism $\bar k(W) \to \bar k(V)$ obtained from a dominant
rational map $f : V \dashrightarrow W$. This is the morphism part of the
function-field functor. -/
noncomputable def dominantMapToPullbackHom
    (V W : AffineVarietyDom k)
    (f : AffineVarietyDom.Hom k V W) :
    FunctionFieldObj.Hom k (V.toFunctionFieldObj k) (W.toFunctionFieldObj k) where
  toAlgHom :=
    show (FractionRing (AffineCoordinateRingBar W.carrier)) →ₐ[AlgebraicClosure k]
      (FractionRing (AffineCoordinateRingBar V.carrier)) from
    AlgHom.mk'
      (@dominantRationalMapPullback k _ V.dim W.dim
        V.carrier W.carrier V.isDomain W.isDomain f.map f.dominant)
      (pullback_isAlgHom V W f)

/-- The function-field pullback of the identity rational map on $V$ is the identity
on $\bar k(V)$ (functoriality of the pullback on identities). -/
theorem pullback_id
    {k : Type*} [Field k]
    (V : AffineVarietyDom k) :
    @dominantRationalMapPullback k _ V.dim V.dim
      V.carrier V.carrier V.isDomain V.isDomain
      (AffineVarietyDom.idMap V) (AffineVarietyDom.idMap_dominant V) =
    RingHom.id _ := by
  exact corollary_15_9_roundtrip_morphisms _ _ V.isAlgebraic

/-- Contravariant functoriality of the function-field pullback: the pullback of the
composition $g \circ f$ equals the composition $f^* \circ g^*$ of the pullbacks. -/
theorem pullback_comp
    {k : Type*} [Field k]
    {V W U : AffineVarietyDom k}
    (f : AffineVarietyDom.Hom k V W)
    (g : AffineVarietyDom.Hom k W U) :
    @dominantRationalMapPullback k _ V.dim U.dim
      V.carrier U.carrier V.isDomain U.isDomain
      (AffineVarietyDom.compMap f g)
      (AffineVarietyDom.compMap_dominant f g) =
    ((@dominantRationalMapPullback k _ V.dim W.dim
        V.carrier W.carrier V.isDomain W.isDomain f.map f.dominant).comp
      (@dominantRationalMapPullback k _ W.dim U.dim
        W.carrier U.carrier W.isDomain U.isDomain g.map g.dominant)) := by
  have hθ : @IsKbarFunctionFieldHom k _ V.dim U.dim V.carrier U.carrier V.isDomain U.isDomain
      ((@dominantRationalMapPullback k _ V.dim W.dim V.carrier W.carrier
        V.isDomain W.isDomain f.map f.dominant).comp
      (@dominantRationalMapPullback k _ W.dim U.dim W.carrier U.carrier
        W.isDomain U.isDomain g.map g.dominant)) := by
    intro r
    show (dominantRationalMapPullback f.map f.dominant)
      ((dominantRationalMapPullback g.map g.dominant) _) = _
    rw [dominantRationalMapPullback_isKbarHom' g.map g.dominant r]
    exact dominantRationalMapPullback_isKbarHom' f.map f.dominant r
  show dominantRationalMapPullback (AffineVarietyDom.compMap f g) _ = _
  unfold AffineVarietyDom.compMap
  simp only
  exact corollary_15_9_roundtrip_morphisms _ hθ U.isAlgebraic

/-- The contravariant function-field functor $\mathbf{AffVar} \to \mathbf{FFld}$ (here
realised as a covariant functor $\mathbf{AffVar}^{\mathrm{op}} \to \mathbf{FFld}$ via
the convention used in this file): sends an affine variety $V$ to its function field
$\bar k(V)$ and a dominant rational map $f$ to its pullback $f^*$. -/
noncomputable def functionFieldFunctorBar :
    (AffineVarietyDom k) ⥤ FunctionFieldObj k where
  obj V := V.toFunctionFieldObj k
  map {V W} f := dominantMapToPullbackHom k V W f
  map_id V := by
    apply FunctionFieldObj.Hom.ext
    show (dominantMapToPullbackHom k V V _).toAlgHom = _
    ext x
    show dominantRationalMapPullback (AffineVarietyDom.idMap V)
      (AffineVarietyDom.idMap_dominant V) x = x
    have h := pullback_id V
    exact congr_fun (congr_arg DFunLike.coe h) x
  map_comp {X Y Z} f g := by
    apply FunctionFieldObj.Hom.ext
    show (dominantMapToPullbackHom k X Z _).toAlgHom =
      ((dominantMapToPullbackHom k X Y f).toAlgHom).comp
        (dominantMapToPullbackHom k Y Z g).toAlgHom
    ext x
    show dominantRationalMapPullback (AffineVarietyDom.compMap f g)
      (AffineVarietyDom.compMap_dominant f g) x =
      dominantRationalMapPullback f.map f.dominant
        (dominantRationalMapPullback g.map g.dominant x)
    have h := pullback_comp f g
    exact congr_fun (congr_arg DFunLike.coe h) x

/-- Public wrapper for the fact that the function-field pullback is a $\bar k$-algebra
homomorphism (i.e. fixes the image of every constant). -/
theorem dominantRationalMapPullback_isKbarHom
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y)
    (hdom : IsDominantRationalMap Y φ) :
    IsKbarFunctionFieldHom (dominantRationalMapPullback φ hdom) :=
  dominantRationalMapPullback_isKbarHom' φ hdom

/-- Injectivity of the function-field pullback on rational maps: two dominant rational
maps between affine varieties that induce the same pullback on function fields must
themselves be equal. -/
theorem pullback_injective_on_maps
    {k : Type*} [Field k]
    (V W : AffineVarietyDom k)
    (f g : AffineVarietyDom.Hom k V W)
    (h : @dominantRationalMapPullback k _ V.dim W.dim
      V.carrier W.carrier V.isDomain W.isDomain f.map f.dominant =
      @dominantRationalMapPullback k _ V.dim W.dim
      V.carrier W.carrier V.isDomain W.isDomain g.map g.dominant) :
    f = g := by
  ext


  have hf_kbar := dominantRationalMapPullback_isKbarHom' f.map f.dominant
  have hg_kbar := dominantRationalMapPullback_isKbarHom' g.map g.dominant
  have hf_rt := corollary_15_9_roundtrip_maps_eq f.map f.dominant hf_kbar W.isAlgebraic
  have hg_rt := corollary_15_9_roundtrip_maps_eq g.map g.dominant hg_kbar W.isAlgebraic
  rw [← hf_rt, ← hg_rt]


  congr 1

/-- Every $\bar k$-algebra homomorphism $\theta : \bar k(W) \to \bar k(V)$ is in
particular a $\bar k$-function-field homomorphism in the sense of `IsKbarFunctionFieldHom`:
the algebra-map condition implies fixing the image of every constant. -/
theorem algHom_isKbarFunctionFieldHom
    {k : Type*} [Field k]
    {V W : AffineVarietyDom k}
    (θ : FractionRing (AffineCoordinateRingBar W.carrier) →ₐ[AlgebraicClosure k]
      FractionRing (AffineCoordinateRingBar V.carrier)) :
    IsKbarFunctionFieldHom θ.toRingHom := by
  intro r


  have h := θ.commutes r


  change θ (algebraMap (AffineCoordinateRingBar W.carrier)
    (FractionRing (AffineCoordinateRingBar W.carrier))
    (Ideal.Quotient.mk (idealOfAlgebraicSet W.carrier) (MvPolynomial.C r))) =
    algebraMap (AffineCoordinateRingBar V.carrier)
    (FractionRing (AffineCoordinateRingBar V.carrier))
    (Ideal.Quotient.mk (idealOfAlgebraicSet V.carrier) (MvPolynomial.C r))
  rw [show (Ideal.Quotient.mk (idealOfAlgebraicSet W.carrier) (MvPolynomial.C r) : AffineCoordinateRingBar W.carrier) = algebraMap (AlgebraicClosure k) (AffineCoordinateRingBar W.carrier) r from rfl]
  rw [show (Ideal.Quotient.mk (idealOfAlgebraicSet V.carrier) (MvPolynomial.C r) : AffineCoordinateRingBar V.carrier) = algebraMap (AlgebraicClosure k) (AffineCoordinateRingBar V.carrier) r from rfl]
  rw [← IsScalarTower.algebraMap_apply (AlgebraicClosure k) (AffineCoordinateRingBar W.carrier) (FractionRing (AffineCoordinateRingBar W.carrier))]
  rw [← IsScalarTower.algebraMap_apply (AlgebraicClosure k) (AffineCoordinateRingBar V.carrier) (FractionRing (AffineCoordinateRingBar V.carrier))]
  exact h

/-- Categorical version of the morphisms roundtrip: starting from a $\bar k$-algebra
homomorphism $\theta : \bar k(W) \to \bar k(V)$, taking the induced rational map and
then its function-field pullback recovers $\theta$. -/
theorem roundtrip_morphisms_categorical
    {k : Type*} [Field k]
    (V W : AffineVarietyDom k)
    (θ : FractionRing (AffineCoordinateRingBar W.carrier) →ₐ[AlgebraicClosure k]
      FractionRing (AffineCoordinateRingBar V.carrier)) :
    @dominantRationalMapPullback k _ V.dim W.dim
      V.carrier W.carrier V.isDomain W.isDomain
      (functionFieldMorphismInducedMap θ.toRingHom
        (algHom_isKbarFunctionFieldHom θ) W.isAlgebraic)
      (functionFieldMorphismInducedMap_isDominant θ.toRingHom
        (algHom_isKbarFunctionFieldHom θ) W.isAlgebraic) =
    θ.toRingHom := by
  exact corollary_15_9_roundtrip_morphisms θ.toRingHom
    (algHom_isKbarFunctionFieldHom θ) W.isAlgebraic

/-- The function-field functor is faithful: it is injective on morphisms between any
two objects, by `pullback_injective_on_maps`. -/
theorem functionFieldFunctorBar_faithful
    {k : Type*} [Field k] :
    (functionFieldFunctorBar k).Faithful where
  map_injective {V W} {f g} h := by
    apply pullback_injective_on_maps V W f g
    have h_alg := congr_arg FunctionFieldObj.Hom.toAlgHom h
    exact congr_arg AlgHom.toRingHom h_alg

/-- The function-field functor is full: every $\bar k$-algebra homomorphism on
function fields comes from a (unique) dominant rational map between the underlying
varieties. -/
theorem functionFieldFunctorBar_full
    {k : Type*} [Field k] :
    (functionFieldFunctorBar k).Full where
  map_surjective {V W} θ := by

    let θ_ring := θ.toAlgHom.toRingHom
    let hθ := algHom_isKbarFunctionFieldHom θ.toAlgHom
    let φ := functionFieldMorphismInducedMap θ_ring hθ W.isAlgebraic
    let hφ := functionFieldMorphismInducedMap_isDominant θ_ring hθ W.isAlgebraic
    refine ⟨⟨φ, hφ⟩, ?_⟩

    apply FunctionFieldObj.Hom.ext
    ext x

    show dominantRationalMapPullback φ hφ x = θ.toAlgHom x
    have h_roundtrip := roundtrip_morphisms_categorical V W θ.toAlgHom
    exact congr_fun (congr_arg DFunLike.coe h_roundtrip) x

/-- Essential surjectivity of the function-field functor on objects: every finitely
generated function field over $\bar k$ is isomorphic to $\bar k(V)$ for some affine
variety $V$ (this expresses the "geometric" side of Corollary 15.9). -/
theorem functionFieldFunctorBar_essSurj_mem_essImage
    {k : Type*} [Field k]
    (F : FunctionFieldObj k) :
    (functionFieldFunctorBar k).essImage F := by sorry

/-- Packaged essential surjectivity of the function-field functor. -/
theorem functionFieldFunctorBar_essSurj
    {k : Type*} [Field k] :
    (functionFieldFunctorBar k).EssSurj where
  mem_essImage := functionFieldFunctorBar_essSurj_mem_essImage

/-- Corollary 15.9 (functor is an equivalence). The function-field functor is full,
faithful and essentially surjective, hence an equivalence of categories between
$\mathbf{AffVar}$ (affine varieties with dominant rational maps) and $\mathbf{FFld}$
(finitely generated function fields over $\bar k$). -/
theorem corollary_15_9_categorical_equivalence :
    (functionFieldFunctorBar k).IsEquivalence where
  faithful := functionFieldFunctorBar_faithful
  full := functionFieldFunctorBar_full
  essSurj := functionFieldFunctorBar_essSurj

/-- The categorical equivalence packaged as a `CategoryTheory.Equivalence` between
$\mathbf{AffineVarietyDom}\;k$ and $\mathbf{FunctionFieldObj}\;k$. -/
noncomputable def affineVariety_functionField_contravariantEquivalence :
    AffineVarietyDom k ≌ FunctionFieldObj k := by
  letI := corollary_15_9_categorical_equivalence k
  exact (functionFieldFunctorBar k).asEquivalence

/-- Corollary 15.9 (final form). The category of affine varieties (with dominant
rational maps) is equivalent to the category of finitely generated function fields
over $\bar k$. -/
noncomputable def corollary_15_9 :
    AffineVarietyDom k ≌ FunctionFieldObj k :=
  affineVariety_functionField_contravariantEquivalence k

end Corollary159

section Corollary1511

variable (k : Type*) [Field k]

open MvPolynomial CategoryTheory

/-- If $\varphi : X \dashrightarrow Y$ and $\psi : Y \dashrightarrow X$ are dominant
rational maps whose composition $\psi \circ \varphi$ is the identity on its domain in
$X$, then the composition of their function-field pullbacks is the identity on $\bar k(X)$. -/
theorem pullback_comp_eq_id_of_birational
    {k : Type*} [Field k]
    {m n_cod : ℕ}
    {X : Set (Fin m → AlgebraicClosure k)}
    {Y : Set (Fin n_cod → AlgebraicClosure k)}
    [IsDomain (AffineCoordinateRingBar X)]
    [IsDomain (AffineCoordinateRingBar Y)]
    (φ : AffineRationalMap X Y)
    (ψ : AffineRationalMap Y X)
    (hdom_φ : IsDominantRationalMap Y φ)
    (hdom_ψ : IsDominantRationalMap X ψ)
    (hcomp : ∀ (P : Fin m → AlgebraicClosure k)
       (hc : P ∈ compositionDomain φ ψ),
       evalCompositionAt φ ψ P hc = P) :
    (dominantRationalMapPullback φ hdom_φ).comp
      (dominantRationalMapPullback ψ hdom_ψ) =
    RingHom.id (FractionRing (AffineCoordinateRingBar X)) := by sorry

/-- Categorical inverses give pointwise inverses on the domain of composition: if
$f : V \to W$ and $g : W \to V$ in `AffineVarietyDom` satisfy $g \circ f = \mathrm{id}_V$,
then $g(f(P)) = P$ for every $P$ where the composition is defined. -/
theorem evalCompositionAt_eq_id_of_catIso
    {k : Type*} [Field k]
    (V W : AffineVarietyDom k)
    (f : V ⟶ W) (g : W ⟶ V)
    (h : f ≫ g = 𝟙 V) :
    ∀ (P : Fin V.dim → AlgebraicClosure k)
      (hcomp : P ∈ compositionDomain f.map g.map),
      evalCompositionAt f.map g.map P hcomp = P := by sorry

/-- Two affine varieties (with domain coordinate rings) are birationally equivalent
in the sense of Definition 15.10 iff they are isomorphic in the category
`AffineVarietyDom k`. -/
theorem birationalEquiv_iff_catIso
    {k : Type*} [Field k]
    (V W : AffineVarietyDom k) :
    AreBirationallyEquivalent V.carrier W.carrier ↔
    Nonempty (V ≅ W) := by
  constructor
  ·
    intro ⟨φ, ψ, hdom_φ, hdom_ψ, hcomp1, hcomp2⟩

    let f : V ⟶ W := ⟨φ, hdom_φ⟩
    let g : W ⟶ V := ⟨ψ, hdom_ψ⟩
    have comp_eq₁ : f ≫ g = 𝟙 V := by
      apply AffineVarietyDom.Hom.ext
      show AffineVarietyDom.compMap f g = AffineVarietyDom.idMap V
      unfold AffineVarietyDom.compMap AffineVarietyDom.idMap
      simp only
      congr 1
      exact pullback_comp_eq_id_of_birational φ ψ hdom_φ hdom_ψ hcomp1
    have comp_eq₂ : g ≫ f = 𝟙 W := by
      apply AffineVarietyDom.Hom.ext
      show AffineVarietyDom.compMap g f = AffineVarietyDom.idMap W
      unfold AffineVarietyDom.compMap AffineVarietyDom.idMap
      simp only
      congr 1
      exact pullback_comp_eq_id_of_birational ψ φ hdom_ψ hdom_φ hcomp2
    exact ⟨⟨f, g, comp_eq₁, comp_eq₂⟩⟩
  ·
    intro ⟨i⟩
    refine ⟨i.hom.map, i.inv.map, i.hom.dominant, i.inv.dominant, ?_, ?_⟩
    · exact evalCompositionAt_eq_id_of_catIso V W i.hom i.inv i.hom_inv_id
    · exact evalCompositionAt_eq_id_of_catIso W V i.inv i.hom i.inv_hom_id

/-- Convert a categorical isomorphism in `FunctionFieldObj` to a $\bar k$-algebra
isomorphism of the underlying function fields. -/
noncomputable def functionFieldIsoToAlgEquiv
    (F G : FunctionFieldObj k)
    (i : F ≅ G) :
    G.carrier ≃ₐ[AlgebraicClosure k] F.carrier :=
  AlgEquiv.ofAlgHom
    i.hom.toAlgHom
    i.inv.toAlgHom
    (by
      have h := i.hom_inv_id
      exact congr_arg FunctionFieldObj.Hom.toAlgHom h)
    (by
      have h := i.inv_hom_id
      exact congr_arg FunctionFieldObj.Hom.toAlgHom h)

/-- Inverse of `functionFieldIsoToAlgEquiv`: convert a $\bar k$-algebra isomorphism
of function fields to an isomorphism in `FunctionFieldObj`. -/
noncomputable def algEquivToFunctionFieldIso
    (F G : FunctionFieldObj k)
    (e : G.carrier ≃ₐ[AlgebraicClosure k] F.carrier) :
    F ≅ G where
  hom := ⟨e.toAlgHom⟩
  inv := ⟨e.symm.toAlgHom⟩
  hom_inv_id := by
    apply FunctionFieldObj.Hom.ext
    ext x
    show e (e.symm x) = x
    simp
  inv_hom_id := by
    apply FunctionFieldObj.Hom.ext
    ext x
    show e.symm (e x) = x
    simp

/-- Corollary 15.11 (forward direction). If $V$ and $W$ are birationally equivalent
affine varieties, then their function fields $\bar k(V)$ and $\bar k(W)$ are
isomorphic as $\bar k$-algebras. -/
noncomputable def corollary_15_11_forward
    (V W : AffineVarietyDom k)
    (hbir : AreBirationallyEquivalent V.carrier W.carrier) :
    (V.toFunctionFieldObj k).carrier ≃ₐ[AlgebraicClosure k]
      (W.toFunctionFieldObj k).carrier := by

  have hiso := (birationalEquiv_iff_catIso V W).mp hbir
  let i := hiso.some


  let fi := (functionFieldFunctorBar k).mapIso i


  exact (functionFieldIsoToAlgEquiv k _ _ fi).symm

/-- Corollary 15.11 (reverse direction). If the function fields $\bar k(V)$ and
$\bar k(W)$ are $\bar k$-algebra isomorphic, then $V$ and $W$ are birationally
equivalent. -/
noncomputable def corollary_15_11_reverse
    (V W : AffineVarietyDom k)
    (e : (V.toFunctionFieldObj k).carrier ≃ₐ[AlgebraicClosure k]
         (W.toFunctionFieldObj k).carrier) :
    AreBirationallyEquivalent V.carrier W.carrier := by


  let fi : V.toFunctionFieldObj k ≅ W.toFunctionFieldObj k :=
    algEquivToFunctionFieldIso k _ _ e.symm

  haveI : (functionFieldFunctorBar k).Full := functionFieldFunctorBar_full
  haveI : (functionFieldFunctorBar k).Faithful := functionFieldFunctorBar_faithful
  let vi : V ≅ W := (functionFieldFunctorBar k).preimageIso fi

  exact (birationalEquiv_iff_catIso V W).mpr ⟨vi⟩


end Corollary1511
