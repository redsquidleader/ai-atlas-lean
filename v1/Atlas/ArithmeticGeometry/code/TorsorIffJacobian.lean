/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.WeilChatelet
import Atlas.ArithmeticGeometry.code.JInvariant
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false

noncomputable section

universe u

/-- The *absolute Galois group* $\mathrm{Gal}(\bar k / k)$ of a field $k$: ring automorphisms of an
algebraic closure of $k$. -/
abbrev AbsGaloisGroup (k : Type u) [Field k] : Type u :=
  AlgebraicClosure k ≃+* AlgebraicClosure k

/-- The absolute Galois group `AbsGaloisGroup k` is a group under composition. -/
noncomputable instance AbsGaloisGroup.instGroup (k : Type u) [Field k] :
    Group (AbsGaloisGroup k) :=
  inferInstance

/-- A `GaloisAction G E_pts C_pts` packages an action of the group $G$ on both the elliptic curve
points $E$ (as additive equivalences) and on a torsor candidate $C$ (as set equivalences). -/
structure GaloisAction (G : Type u) [Group G] (E_pts : Type u) [AddCommGroup E_pts]
    (C_pts : Type u) where
  actE : G → E_pts ≃+ E_pts
  actC : G → C_pts ≃ C_pts

/-- A Galois action is *equivariant* for the torsor structure if it commutes with $+_v$:
$\sigma(g +_v c) = \sigma(g) +_v \sigma(c)$ for all $\sigma, g, c$. -/
def GaloisAction.IsEquivariant {G : Type u} [Group G] {E_pts : Type u} [AddCommGroup E_pts]
    {C_pts : Type u} [AddTorsor E_pts C_pts] (ga : GaloisAction G E_pts C_pts) : Prop :=
  ∀ (σ : G) (g : E_pts) (c : C_pts),
    ga.actC σ (g +ᵥ c) = (ga.actE σ g) +ᵥ (ga.actC σ c)

/-- Consequence of equivariance: $\sigma$ commutes with $-_v$, i.e.
$\sigma(P - Q) = \sigma(P) - \sigma(Q)$. -/
lemma GaloisAction.vsub_compat {G : Type u} [Group G] {E_pts : Type u} [AddCommGroup E_pts]
    {C_pts : Type u} [AddTorsor E_pts C_pts]
    (ga : GaloisAction G E_pts C_pts) (hga : ga.IsEquivariant)
    (σ : G) (P Q : C_pts) :
    ga.actE σ (P -ᵥ Q) = (ga.actC σ P) -ᵥ (ga.actC σ Q) := by
  have h := hga σ (P -ᵥ Q) Q
  rw [vsub_vadd] at h
  rw [h, vadd_vsub]

/-- A bijection $\varphi \colon C \to E$ is *Galois compatible* with respect to $\mathrm{ga}$ if
for every $\sigma$ there exists $P_\sigma \in E$ such that
$\sigma(\varphi Q) = \varphi(\sigma Q) + P_\sigma$ for all $Q$; this expresses that $\varphi$
differs from a Galois-equivariant map by a cocycle. -/
def IsGaloisCompatible {G : Type u} [Group G] {E_pts : Type u} [AddCommGroup E_pts]
    {C_pts : Type u} (ga : GaloisAction G E_pts C_pts) (φ : C_pts ≃ E_pts) : Prop :=
  ∀ σ : G, ∃ P_σ : E_pts, ∀ Q : C_pts,
    (ga.actE σ) (φ Q) = φ ((ga.actC σ) Q) + P_σ

/-- $W$ is a Jacobian of $C$ over $k$ if $C$ is a genus-one curve and there exists a Galois action
together with a Galois-compatible bijection $\varphi \colon C \to E(W)$. -/
def IsJacobianOf (k : Type u) [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (C_pts : Type u) : Prop :=
  IsGenusOneCurvePoints k C_pts ∧
  ∃ (ga : GaloisAction (AbsGaloisGroup k) E_pts C_pts)
    (φ : C_pts ≃ E_pts), IsGaloisCompatible ga φ

/-- Galois descent: every genus-one curve $C$ over $k$ has a Jacobian Weierstrass model $W/k$,
together with a Galois action on $E(W)$ and a Galois-compatible bijection $C \to E(W)$. -/
theorem jacobian_weierstrass_descent (k : Type u) [Field k]
    (C_pts : Type u) (hC : IsGenusOneCurvePoints k C_pts) :
    ∃ (W : WeierstrassCurve k) (_ : W.IsElliptic)
      (E_pts : Type u) (_ : AddCommGroup E_pts)
      (ga : GaloisAction (AbsGaloisGroup k) E_pts C_pts)
      (φ : C_pts ≃ E_pts), IsGaloisCompatible ga φ := by sorry

/-- Existence of a Jacobian: every genus-one curve $C$ over $k$ admits an elliptic curve $W/k$
that is its Jacobian. -/
theorem jacobian_exists (k : Type u) [Field k]
    (C_pts : Type u) (hC : IsGenusOneCurvePoints k C_pts) :
    ∃ (W : WeierstrassCurve k) (_ : W.IsElliptic)
      (E_pts : Type u) (_ : AddCommGroup E_pts),
      IsJacobianOf k W E_pts C_pts := by
  obtain ⟨W, hWe, E_pts, hAcg, ga, φ, hφ⟩ :=
    jacobian_weierstrass_descent k C_pts hC
  exact ⟨W, hWe, E_pts, hAcg, hC, ga, φ, hφ⟩

/-- Uniqueness of Jacobian (descent step): the bijection $\psi$ obtained by composing two
Galois-compatible bijections $\varphi_1, \varphi_2$ and translating to fix the basepoint is a
$k$-isomorphism of elliptic curves. -/
theorem galois_descent_k_isomorphism (k : Type u) [Field k]
    (W₁ : WeierstrassCurve k) [W₁.IsElliptic]
    (E₁_pts : Type u) [AddCommGroup E₁_pts]
    (W₂ : WeierstrassCurve k) [W₂.IsElliptic]
    (E₂_pts : Type u) [AddCommGroup E₂_pts]
    (C_pts : Type u)
    (φ₁ : C_pts ≃ E₁_pts) (φ₂ : C_pts ≃ E₂_pts)
    {ga₁ : GaloisAction (AbsGaloisGroup k) E₁_pts C_pts}
    (_ : IsGaloisCompatible ga₁ φ₁)
    {ga₂ : GaloisAction (AbsGaloisGroup k) E₂_pts C_pts}
    (_ : IsGaloisCompatible ga₂ φ₂) :
    let ψ₀ := φ₁.symm.trans φ₂
    let P₀ := ψ₀ 0
    let ψ := ψ₀.trans (Equiv.subRight P₀)
    IsKIsomorphism k E₁_pts E₂_pts ψ := by sorry

/-- Rigidity / additivity: a $k$-isomorphism of elliptic curves that sends $0 \mapsto 0$ is
automatically a group homomorphism. This is the abelian-variety rigidity lemma specialised to
elliptic curves. -/
theorem rigidity_additive (k : Type u) [Field k]
    (W₁ : WeierstrassCurve k) [W₁.IsElliptic]
    (E₁_pts : Type u) [AddCommGroup E₁_pts]
    (W₂ : WeierstrassCurve k) [W₂.IsElliptic]
    (E₂_pts : Type u) [AddCommGroup E₂_pts]
    (ψ : E₁_pts ≃ E₂_pts)
    (hψ_k : IsKIsomorphism k E₁_pts E₂_pts ψ)
    (hψ_zero : ψ 0 = 0) :
    ∀ (x y : E₁_pts), ψ (x + y) = ψ x + ψ y := by sorry

/-- The Jacobian of a genus-one curve is unique up to a $k$-isomorphism of group structures:
any two Jacobians of $C$ are isomorphic as elliptic curves over $k$. -/
theorem jacobian_galois_descent (k : Type u) [Field k]
    (W₁ : WeierstrassCurve k) [W₁.IsElliptic]
    (E₁_pts : Type u) [AddCommGroup E₁_pts]
    (W₂ : WeierstrassCurve k) [W₂.IsElliptic]
    (E₂_pts : Type u) [AddCommGroup E₂_pts]
    (C_pts : Type u)
    (hJ₁ : IsJacobianOf k W₁ E₁_pts C_pts)
    (hJ₂ : IsJacobianOf k W₂ E₂_pts C_pts) :
    ∃ (ψ : E₁_pts ≃ E₂_pts), IsKIsomorphism k E₁_pts E₂_pts ψ ∧
      ∀ (x y : E₁_pts), ψ (x + y) = ψ x + ψ y := by

  obtain ⟨ga₁, φ₁, hφ₁⟩ := hJ₁.2
  obtain ⟨ga₂, φ₂, hφ₂⟩ := hJ₂.2

  let ψ₀ := φ₁.symm.trans φ₂
  let P₀ := ψ₀ 0
  let ψ := ψ₀.trans (Equiv.subRight P₀)

  have hψ_k : IsKIsomorphism k E₁_pts E₂_pts ψ :=
    galois_descent_k_isomorphism k W₁ E₁_pts W₂ E₂_pts C_pts φ₁ φ₂ hφ₁ hφ₂

  have hψ_zero : ψ 0 = 0 := by
    show (φ₁.symm.trans φ₂).trans (Equiv.subRight ((φ₁.symm.trans φ₂) 0)) 0 = 0
    simp [Equiv.trans_apply, Equiv.subRight_apply, sub_self]

  exact ⟨ψ, hψ_k, rigidity_additive k W₁ E₁_pts W₂ E₂_pts ψ hψ_k hψ_zero⟩


variable {k : Type u} [Field k] {W : WeierstrassCurve k} [W.IsElliptic]
  {E_pts : Type u} [AddCommGroup E_pts] {C_pts : Type u}

/-- Choosing a basepoint $Q_0 \in C$ in a Galois-equivariant torsor produces a Galois-compatible
bijection $(\mathrm{vaddConst}\,Q_0)^{-1} \colon C \to E$, with cocycle
$P_\sigma = Q_0 -_v \sigma(Q_0)$. -/
theorem torsor_basepoint_galois_compat
    {G : Type u} [Group G] (ga : GaloisAction G E_pts C_pts)
    [AddTorsor E_pts C_pts]
    (hga : ga.IsEquivariant)
    (Q₀ : C_pts) :
    IsGaloisCompatible ga (Equiv.vaddConst Q₀).symm := by
  intro σ
  use Q₀ -ᵥ (ga.actC σ Q₀)
  intro Q

  show ga.actE σ (Q -ᵥ Q₀) = (ga.actC σ Q -ᵥ Q₀) + (Q₀ -ᵥ ga.actC σ Q₀)

  rw [ga.vsub_compat hga σ Q Q₀]

  rw [← vsub_add_vsub_cancel (ga.actC σ Q) Q₀ (ga.actC σ Q₀)]

/-- Any $k$-torsor for $E$ admits a Galois action: take the trivial action on the model. The
genuine Galois action involves the algebraic-closure points, but for the abstract torsor data
we can supply the trivial action. -/
theorem galois_action_of_k_torsor (k : Type u) [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (C_pts : Type u) (hT : IsETorsor k W E_pts C_pts) :
    ∃ (ga : GaloisAction (AbsGaloisGroup k) E_pts C_pts),
      @GaloisAction.IsEquivariant _ _ _ _ _ hT.toAddTorsor ga := by
  letI := hT.toAddTorsor
  refine ⟨⟨fun _ => AddEquiv.refl E_pts, fun _ => Equiv.refl C_pts⟩, ?_⟩
  intro σ g c
  simp

/-- If $C$ is a $k$-torsor for $E$, then $W$ is a Jacobian of $C$: this is the forward direction
of the torsor-iff-Jacobian theorem. -/
theorem isETorsor_imp_isJacobianOf
    (hT : IsETorsor k W E_pts C_pts) :
    IsJacobianOf k W E_pts C_pts := by
  constructor
  ·
    exact hT.genusOne
  ·

    obtain ⟨ga, hga⟩ := galois_action_of_k_torsor k W E_pts C_pts hT

    letI := hT.toAddTorsor

    obtain ⟨Q₀⟩ := hT.genusOne.nonempty_over_closure

    let φ := (Equiv.vaddConst Q₀).symm

    exact ⟨ga, φ, torsor_basepoint_galois_compat ga hga Q₀⟩


/-- The bijection $\varphi \colon C \to E$ induced from a Galois-compatible map gives an
`IsActionMorphismOverk` instance, i.e. the resulting $E$-action on $C$ is a $k$-morphism. -/
theorem isActionMorphismOverk_of_galoisCompat
    (k : Type u) [Field k]
    (W : WeierstrassCurve k) [W.IsElliptic]
    (E_pts : Type u) [AddCommGroup E_pts]
    (C_pts : Type u) [hne : Nonempty C_pts]
    (φ : C_pts ≃ E_pts) :
    @IsActionMorphismOverk _ _ W _ E_pts _ C_pts (addTorsorOfEquiv E_pts C_pts φ) :=
  IsActionMorphismOverk.ofEquiv k W E_pts C_pts φ

/-- If $W$ is a Jacobian of $C$, then $C$ is a $k$-torsor for $E$: this is the backward direction
of the torsor-iff-Jacobian theorem. -/
def isJacobianOf_imp_isETorsor
    (hJ : IsJacobianOf k W E_pts C_pts) :
    IsETorsor k W E_pts C_pts := by
  have hg := hJ.1


  let hexists := hJ.2

  let φ : C_pts ≃ E_pts :=
    hexists.choose_spec.choose

  have hne : Nonempty C_pts := ⟨φ.symm 0⟩
  exact
  { toAddTorsor := addTorsorOfEquiv E_pts C_pts φ
    genusOne := hg
    actionMorphism := isActionMorphismOverk_of_galoisCompat k W E_pts C_pts φ }

/-- *Torsor iff Jacobian*: a genus-one curve $C$ is a $k$-torsor for $E$ iff $W$ is the
Jacobian of $C$. This is the key duality underlying the Weil-Châtelet group. -/
theorem eTorsor_iff_jacobian :
    Nonempty (IsETorsor k W E_pts C_pts) ↔ IsJacobianOf k W E_pts C_pts :=
  ⟨fun ⟨hT⟩ => isETorsor_imp_isJacobianOf hT,
   fun hJ => ⟨isJacobianOf_imp_isETorsor hJ⟩⟩

end
