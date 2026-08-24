/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Monotone.Basic

noncomputable section

open scoped Padic


attribute [local instance] Classical.dec

namespace PadicElliptic

variable {p : ℕ} [hp : Fact (Nat.Prime p)]

/-- The group of $\mathbb{Q}_p$-points of a Weierstrass curve $W$ defined over $\mathbb{Q}$,
obtained by base-changing to $\mathbb{Q}_p$ and taking the affine point set. -/
abbrev PadicPointGroup (W : WeierstrassCurve ℚ) : Type :=
  (W.baseChange ℚ_[p]).toAffine.Point

/-- Membership predicate for the $n$-th piece $E_n(\mathbb{Q}_p)$ of the $p$-adic filtration:
a point is either the identity, or has $y \ne 0$ and $v_p(x) - v_p(y) \ge n$. -/
def InPadicFiltration (W : WeierstrassCurve ℚ) (n : ℕ)
    (P : PadicPointGroup W (p := p)) : Prop :=
  match P with
  | .zero => True
  | .some x y _ => y ≠ 0 ∧ (n : ℤ) ≤ Padic.valuation x - Padic.valuation y

/-- The $p$-adic filtration is monotone in the level: $E_{n+1}(\mathbb{Q}_p) \subseteq
E_n(\mathbb{Q}_p)$. -/
theorem inPadicFiltration_mono {W : WeierstrassCurve ℚ} {n : ℕ}
    {P : PadicPointGroup W (p := p)}
    (h : InPadicFiltration W (n + 1) P) : InPadicFiltration W n P := by
  match P with
  | .zero => exact trivial
  | .some x y h' =>
    simp only [InPadicFiltration] at h ⊢
    exact ⟨h.1, le_trans (by omega) h.2⟩

/-- The $p$-adic valuation on $\mathbb{Q}_p$ is invariant under negation: $v_p(-y) = v_p(y)$. -/
lemma padic_valuation_neg (y : ℚ_[p]) : (-y).valuation = y.valuation := by
  by_cases hy : y = 0
  · simp [hy]
  · have hny : -y ≠ 0 := neg_ne_zero.mpr hy
    have hnorm : ‖(-y)‖ = ‖y‖ := norm_neg y
    rw [Padic.norm_eq_zpow_neg_valuation hny, Padic.norm_eq_zpow_neg_valuation hy] at hnorm
    have hp1 : (1 : ℝ) < p := by exact_mod_cast Nat.Prime.one_lt hp.out
    have hp_pos : (0 : ℝ) < p := lt_trans zero_lt_one hp1
    have hp_ne_one : (p : ℝ) ≠ 1 := ne_of_gt hp1
    have := zpow_right_injective₀ hp_pos hp_ne_one hnorm
    linarith

/-- For a Weierstrass curve in short form ($a_1 = a_3 = 0$), the negation of a point $(x, y)$ on
$W_{\mathbb{Q}_p}$ has $y$-coordinate $-y$. -/
lemma negY_short_weierstrass (W : WeierstrassCurve ℚ)
    (ha1 : W.a₁ = 0) (ha3 : W.a₃ = 0) (x y : ℚ_[p]) :
    (W.baseChange ℚ_[p]).toAffine.negY x y = -y := by
  unfold WeierstrassCurve.baseChange WeierstrassCurve.toAffine WeierstrassCurve.Affine.negY
  simp [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃, ha1, ha3]

/-- Negation preserves the $p$-adic filtration: if $P \in E_n(\mathbb{Q}_p)$ then so is $-P$.
This uses that negation only flips the sign of $y$ in short form, and $v_p$ is sign-invariant. -/
theorem negation_preserves_filtration (W : WeierstrassCurve ℚ)
    (ha1 : W.a₁ = 0) (ha3 : W.a₃ = 0) (n : ℕ)
    (P : PadicPointGroup W (p := p)) :
    InPadicFiltration W n P → InPadicFiltration W n (-P) := by
  match P with
  | .zero =>
    intro _
    show InPadicFiltration W n (-(0 : PadicPointGroup W))
    rw [neg_zero]
    trivial
  | .some x y h =>
    intro ⟨hy, hval⟩
    rw [WeierstrassCurve.Affine.Point.neg_some]
    have hNegY : (W.baseChange ℚ_[p]).toAffine.negY x y = -y :=
      negY_short_weierstrass W ha1 ha3 x y
    show (W.baseChange ℚ_[p]).toAffine.negY x y ≠ 0 ∧
         (n : ℤ) ≤ Padic.valuation x -
           Padic.valuation ((W.baseChange ℚ_[p]).toAffine.negY x y)
    rw [hNegY]
    exact ⟨neg_ne_zero.mpr hy, by rw [padic_valuation_neg]; exact hval⟩


/-- Secant case: when $x_1 \ne x_2$, adding two points $P, Q \in E_n(\mathbb{Q}_p)$ stays in
$E_n(\mathbb{Q}_p)$. Axiomatized for now. -/
theorem addition_secant_case {p : ℕ} [hp : Fact (Nat.Prime p)]
    (W : WeierstrassCurve ℚ)
    (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0) (n : ℕ)
    {x₁ x₂ y₁ y₂ : ℚ_[p]}
    (h₁ : (W.baseChange ℚ_[p]).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.baseChange ℚ_[p]).toAffine.Nonsingular x₂ y₂)
    (hx : x₁ ≠ x₂)
    (hP : y₁ ≠ 0 ∧ (n : ℤ) ≤ Padic.valuation x₁ - Padic.valuation y₁)
    (hQ : y₂ ≠ 0 ∧ (n : ℤ) ≤ Padic.valuation x₂ - Padic.valuation y₂) :
    (W.baseChange ℚ_[p]).toAffine.addY x₁ x₂ y₁
      ((W.baseChange ℚ_[p]).toAffine.slope x₁ x₂ y₁ y₂) ≠ 0 ∧
    (n : ℤ) ≤
      Padic.valuation ((W.baseChange ℚ_[p]).toAffine.addX x₁ x₂
        ((W.baseChange ℚ_[p]).toAffine.slope x₁ x₂ y₁ y₂)) -
      Padic.valuation ((W.baseChange ℚ_[p]).toAffine.addY x₁ x₂ y₁
        ((W.baseChange ℚ_[p]).toAffine.slope x₁ x₂ y₁ y₂)) := by sorry


/-- Tangent case: when $x_1 = x_2$ but $y_1 \ne -y_2$, doubling-type addition still preserves
$E_n(\mathbb{Q}_p)$. Axiomatized for now. -/
theorem addition_tangent_case {p : ℕ} [hp : Fact (Nat.Prime p)]
    (W : WeierstrassCurve ℚ)
    (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0) (n : ℕ)
    {x₁ x₂ y₁ y₂ : ℚ_[p]}
    (h₁ : (W.baseChange ℚ_[p]).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.baseChange ℚ_[p]).toAffine.Nonsingular x₂ y₂)
    (hx : x₁ = x₂)
    (hy : y₁ ≠ (W.baseChange ℚ_[p]).toAffine.negY x₂ y₂)
    (hP : y₁ ≠ 0 ∧ (n : ℤ) ≤ Padic.valuation x₁ - Padic.valuation y₁)
    (hQ : y₂ ≠ 0 ∧ (n : ℤ) ≤ Padic.valuation x₂ - Padic.valuation y₂) :
    (W.baseChange ℚ_[p]).toAffine.addY x₁ x₂ y₁
      ((W.baseChange ℚ_[p]).toAffine.slope x₁ x₂ y₁ y₂) ≠ 0 ∧
    (n : ℤ) ≤
      Padic.valuation ((W.baseChange ℚ_[p]).toAffine.addX x₁ x₂
        ((W.baseChange ℚ_[p]).toAffine.slope x₁ x₂ y₁ y₂)) -
      Padic.valuation ((W.baseChange ℚ_[p]).toAffine.addY x₁ x₂ y₁
        ((W.baseChange ℚ_[p]).toAffine.slope x₁ x₂ y₁ y₂)) := by sorry

/-- Combined statement (secant + tangent): the explicit addition formula on the Weierstrass curve
preserves the $p$-adic filtration; established by case analysis on whether $x_1 = x_2$. -/
theorem addition_formula_preserves_valuation_ax {p : ℕ} [hp : Fact (Nat.Prime p)]
    (W : WeierstrassCurve ℚ)
    (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0) (n : ℕ)
    {x₁ x₂ y₁ y₂ : ℚ_[p]}
    (h₁ : (W.baseChange ℚ_[p]).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.baseChange ℚ_[p]).toAffine.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (W.baseChange ℚ_[p]).toAffine.negY x₂ y₂))
    (hP : y₁ ≠ 0 ∧ (n : ℤ) ≤ Padic.valuation x₁ - Padic.valuation y₁)
    (hQ : y₂ ≠ 0 ∧ (n : ℤ) ≤ Padic.valuation x₂ - Padic.valuation y₂) :
    (W.baseChange ℚ_[p]).toAffine.addY x₁ x₂ y₁
      ((W.baseChange ℚ_[p]).toAffine.slope x₁ x₂ y₁ y₂) ≠ 0 ∧
    (n : ℤ) ≤
      Padic.valuation ((W.baseChange ℚ_[p]).toAffine.addX x₁ x₂
        ((W.baseChange ℚ_[p]).toAffine.slope x₁ x₂ y₁ y₂)) -
      Padic.valuation ((W.baseChange ℚ_[p]).toAffine.addY x₁ x₂ y₁
        ((W.baseChange ℚ_[p]).toAffine.slope x₁ x₂ y₁ y₂)) := by
  by_cases hx : x₁ = x₂
  ·
    have hy : y₁ ≠ (W.baseChange ℚ_[p]).toAffine.negY x₂ y₂ :=
      fun h => hxy ⟨hx, h⟩
    exact addition_tangent_case W ha1 ha2 ha3 n h₁ h₂ hx hy hP hQ
  ·
    exact addition_secant_case W ha1 ha2 ha3 n h₁ h₂ hx hP hQ

/-- Re-statement using `let` for readability: the addition formula preserves the $p$-adic
filtration. -/
theorem addition_formula_preserves_valuation (W : WeierstrassCurve ℚ)
    (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0) (n : ℕ)
    {x₁ x₂ y₁ y₂ : ℚ_[p]}
    (h₁ : (W.baseChange ℚ_[p]).toAffine.Nonsingular x₁ y₁)
    (h₂ : (W.baseChange ℚ_[p]).toAffine.Nonsingular x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (W.baseChange ℚ_[p]).toAffine.negY x₂ y₂))
    (hP : y₁ ≠ 0 ∧ (n : ℤ) ≤ Padic.valuation x₁ - Padic.valuation y₁)
    (hQ : y₂ ≠ 0 ∧ (n : ℤ) ≤ Padic.valuation x₂ - Padic.valuation y₂) :
    let W' := (W.baseChange ℚ_[p]).toAffine
    let ℓ := W'.slope x₁ x₂ y₁ y₂
    W'.addY x₁ x₂ y₁ ℓ ≠ 0 ∧
      (n : ℤ) ≤ Padic.valuation (W'.addX x₁ x₂ ℓ) -
        Padic.valuation (W'.addY x₁ x₂ y₁ ℓ) :=
  addition_formula_preserves_valuation_ax W ha1 ha2 ha3 n h₁ h₂ hxy hP hQ

/-- Closure under addition: if $P, Q \in E_n(\mathbb{Q}_p)$ then $P + Q \in E_n(\mathbb{Q}_p)$.
This combines the trivial cases (one summand is $0$ or $P + Q = 0$) with the addition formula. -/
theorem addition_preserves_filtration (W : WeierstrassCurve ℚ)
    (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0) (n : ℕ)
    (P Q : PadicPointGroup W (p := p)) :
    InPadicFiltration W n P → InPadicFiltration W n Q →
    InPadicFiltration W n (P + Q) := by
  intro hP hQ
  match P, Q with
  | .zero, Q =>

    exact hQ
  | .some x₁ y₁ h₁, .zero =>

    exact hP
  | .some x₁ y₁ h₁, .some x₂ y₂ h₂ =>
    simp only [InPadicFiltration] at hP hQ
    obtain ⟨hy₁, hv₁⟩ := hP
    obtain ⟨hy₂, hv₂⟩ := hQ
    show InPadicFiltration W n
      (WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ +
       WeierstrassCurve.Affine.Point.some x₂ y₂ h₂)
    by_cases hxy : x₁ = x₂ ∧ y₁ = (W.baseChange ℚ_[p]).toAffine.negY x₂ y₂
    ·
      rw [WeierstrassCurve.Affine.Point.add_of_Y_eq hxy.1 hxy.2]
      exact trivial
    ·
      rw [WeierstrassCurve.Affine.Point.add_some hxy]
      exact addition_formula_preserves_valuation W ha1 ha2 ha3 n h₁ h₂ hxy
        ⟨hy₁, hv₁⟩ ⟨hy₂, hv₂⟩

/-- The $n$-th piece $E_n(\mathbb{Q}_p)$ of the $p$-adic filtration on $E(\mathbb{Q}_p)$ realized
as an additive subgroup, with closure properties supplied by `negation_preserves_filtration` and
`addition_preserves_filtration`. -/
def padicFiltration (W : WeierstrassCurve ℚ)
    (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0) (n : ℕ) :
    AddSubgroup (PadicPointGroup W (p := p)) where
  carrier := {P | InPadicFiltration W n P}
  zero_mem' := trivial
  add_mem' {a b} ha hb := addition_preserves_filtration W ha1 ha2 ha3 n a b ha hb
  neg_mem' {a} ha := negation_preserves_filtration W ha1 ha3 n a ha

/-- Successor inclusion: $E_{n+1}(\mathbb{Q}_p) \le E_n(\mathbb{Q}_p)$ as subgroups. -/
theorem padicFiltration_le_succ (W : WeierstrassCurve ℚ)
    (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0) (n : ℕ) :
    padicFiltration W ha1 ha2 ha3 (n + 1) (p := p) ≤
      padicFiltration W ha1 ha2 ha3 n :=
  fun _ hP => inPadicFiltration_mono hP

/-- The $p$-adic filtration, viewed as a function $\mathbb{N} \to \mathrm{AddSubgroup}\,E$, is
antitone. -/
theorem padicFiltration_antitone (W : WeierstrassCurve ℚ)
    (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0) :
    Antitone (padicFiltration (p := p) W ha1 ha2 ha3) :=
  antitone_nat_of_succ_le (padicFiltration_le_succ W ha1 ha2 ha3)

/-- If $H$ is the kernel of a surjective additive group homomorphism $G \to \mathbb{Z}/p\mathbb{Z}$,
then $[G : H] = p$. -/
theorem index_eq_p_of_surjective_hom_to_zmod {G : Type*} [AddGroup G]
    (H : AddSubgroup G)
    (f : G →+ ZMod p) (hf : Function.Surjective f) (hker : f.ker = H) :
    H.index = p := by
  rw [← hker, AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hf,
      AddSubgroup.card_top, Nat.card_eq_fintype_card, ZMod.card]


/-- Axiomatized reduction homomorphism $E_n(\mathbb{Q}_p) \to \mathbb{Z}/p\mathbb{Z}$ used to
detect the next layer of the filtration. -/
noncomputable def reduction_hom_ax {p : ℕ} [hp : Fact (Nat.Prime p)]
    (W : WeierstrassCurve ℚ)
    (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0)
    [hW : (W.baseChange ℚ_[p]).IsElliptic]
    (n : ℕ) (hn : 0 < n) :
    ↥(padicFiltration W ha1 ha2 ha3 n (p := p)) →+ ZMod p := by sorry

/-- Axiomatized: the reduction homomorphism `reduction_hom_ax` is surjective. -/
theorem reduction_hom_surjective_ax {p : ℕ} [hp : Fact (Nat.Prime p)]
    (W : WeierstrassCurve ℚ)
    (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0)
    [hW : (W.baseChange ℚ_[p]).IsElliptic]
    (n : ℕ) (hn : 0 < n) :
    Function.Surjective (reduction_hom_ax (p := p) W ha1 ha2 ha3 n hn) := by sorry

/-- Axiomatized: the kernel of `reduction_hom_ax` is exactly $E_{n+1}(\mathbb{Q}_p)$ viewed as a
subgroup of $E_n(\mathbb{Q}_p)$. -/
theorem reduction_hom_kernel_ax {p : ℕ} [hp : Fact (Nat.Prime p)]
    (W : WeierstrassCurve ℚ)
    (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0)
    [hW : (W.baseChange ℚ_[p]).IsElliptic]
    (n : ℕ) (hn : 0 < n) :
    (reduction_hom_ax (p := p) W ha1 ha2 ha3 n hn).ker =
      (padicFiltration W ha1 ha2 ha3 (n + 1) (p := p)).addSubgroupOf
        (padicFiltration W ha1 ha2 ha3 n) := by sorry

/-- Bundled form: there exists a surjective additive homomorphism $E_n(\mathbb{Q}_p) \to
\mathbb{Z}/p\mathbb{Z}$ whose kernel is $E_{n+1}(\mathbb{Q}_p)$. -/
theorem exists_surjective_reduction_hom (W : WeierstrassCurve ℚ)
    (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0)
    [hW : (W.baseChange ℚ_[p]).IsElliptic]
    (n : ℕ) (hn : 0 < n) :
    ∃ (f : ↥(padicFiltration W ha1 ha2 ha3 n (p := p)) →+ ZMod p),
      Function.Surjective f ∧
      f.ker = (padicFiltration W ha1 ha2 ha3 (n + 1) (p := p)).addSubgroupOf
                (padicFiltration W ha1 ha2 ha3 n) :=
  ⟨reduction_hom_ax (p := p) W ha1 ha2 ha3 n hn,
   reduction_hom_surjective_ax W ha1 ha2 ha3 n hn,
   reduction_hom_kernel_ax W ha1 ha2 ha3 n hn⟩

/-- Lemma 24.12: for $n \ge 1$, the relative index $[E_n(\mathbb{Q}_p) : E_{n+1}(\mathbb{Q}_p)]$
equals $p$. Each successive layer of the $p$-adic filtration is a quotient of order $p$. -/
theorem lemma_24_12 (W : WeierstrassCurve ℚ)
    (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0)
    [hW : (W.baseChange ℚ_[p]).IsElliptic]
    (n : ℕ) (hn : 0 < n) :
    (padicFiltration W ha1 ha2 ha3 (n + 1) (p := p)).relIndex
      (padicFiltration W ha1 ha2 ha3 n) = p := by
  unfold AddSubgroup.relIndex
  obtain ⟨f, hf_surj, hf_ker⟩ :=
    exists_surjective_reduction_hom (p := p) W ha1 ha2 ha3 n hn
  exact index_eq_p_of_surjective_hom_to_zmod _ f hf_surj hf_ker

/-- The descending chain $E_0(\mathbb{Q}_p) \supseteq E_1(\mathbb{Q}_p) \supseteq \cdots$ as a
function $\mathbb{N} \to \mathrm{AddSubgroup}$. -/
def PadicFiltrationChain (W : WeierstrassCurve ℚ)
    (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0) :
    ℕ → AddSubgroup (PadicPointGroup W (p := p)) :=
  padicFiltration W ha1 ha2 ha3


/-- The kernel of reduction modulo $p$ on $E(\mathbb{Q}_p)$, equal to $E_1(\mathbb{Q}_p)$, the
first non-trivial layer of the $p$-adic filtration. -/
def reductionKernel (W : WeierstrassCurve ℚ)
    (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0) :
    AddSubgroup (PadicPointGroup W (p := p)) :=
  padicFiltration W ha1 ha2 ha3 1

/-- A point that lies in every filtration piece $E_n(\mathbb{Q}_p)$ is the identity: the only
element with infinite valuation difference is $0$. -/
lemma inPadicFiltration_all_eq_zero {W : WeierstrassCurve ℚ}
    {P : PadicPointGroup W (p := p)}
    (h : ∀ n : ℕ, InPadicFiltration W n P) : P = 0 := by
  match P with
  | .zero => rfl
  | .some x y hns =>
    exfalso
    have : ∀ n : ℕ, (n : ℤ) ≤ Padic.valuation x - Padic.valuation y := fun n => (h n).2
    have := this (Int.toNat (Padic.valuation x - Padic.valuation y) + 1)
    omega

/-- Axiomatized: if $P \in E_n(\mathbb{Q}_p)$ and $pP = 0$, then $P$ already lies in
$E_{n+1}(\mathbb{Q}_p)$. -/
theorem p_nsmul_in_filtration_succ_ax {p : ℕ} [hp : Fact (Nat.Prime p)]
    {W : WeierstrassCurve ℚ}
    (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0)
    (n : ℕ) (hn : 0 < n)
    (P : PadicPointGroup W (p := p))
    (hPn : InPadicFiltration W n P) (hpP : p • P = 0) :
    InPadicFiltration W (n + 1) P := by sorry

/-- Any torsion point of $E(\mathbb{Q}_p)$ lying in $E_1(\mathbb{Q}_p)$ must be zero. The proof
proceeds by strong induction on the torsion order, distinguishing the cases of coprime-to-$p$
torsion (annihilated by the surjective reduction) and $p$-power torsion (pushed deeper into the
filtration via `p_nsmul_in_filtration_succ_ax`). -/
theorem torsion_in_E1_eq_zero {p : ℕ} [hp : Fact (Nat.Prime p)]
    {W : WeierstrassCurve ℚ}
    (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0)
    [hW : (W.baseChange ℚ_[p]).IsElliptic]
    (P : PadicPointGroup W (p := p))
    (hP1 : P ∈ padicFiltration W ha1 ha2 ha3 1)
    (m : ℕ) (hm : m ≠ 0) (htors : m • P = 0) : P = 0 := by

  induction m using Nat.strongRecOn with
  | _ m ih =>
  by_cases hcop : Nat.Coprime m p
  ·
    apply inPadicFiltration_all_eq_zero
    intro k
    induction k with
    | zero => exact padicFiltration_antitone W ha1 ha2 ha3 (Nat.zero_le 1) hP1
    | succ n =>
      rename_i hk_ih

      by_cases hn : 0 < n
      ·
        obtain ⟨f, _, hf_ker⟩ :=
          exists_surjective_reduction_hom (p := p) W ha1 ha2 ha3 n hn

        have hP_ker : (⟨P, hk_ih⟩ : ↥(padicFiltration W ha1 ha2 ha3 n)) ∈ f.ker := by
          rw [AddMonoidHom.mem_ker]
          have h0 : m • (⟨P, hk_ih⟩ : ↥(padicFiltration W ha1 ha2 ha3 n)) = 0 := by
            ext
            simp only [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero]
            exact htors
          have hfm : f (m • ⟨P, hk_ih⟩) = 0 := by rw [h0]; simp
          rw [map_nsmul, nsmul_eq_mul] at hfm
          exact (IsUnit.mul_right_eq_zero (ZMod.unitOfCoprime m hcop).isUnit).mp hfm
        rw [hf_ker] at hP_ker
        exact hP_ker
      ·
        simp only [Nat.not_lt, Nat.le_zero] at hn
        subst hn; exact hP1
  ·
    have hdvd : p ∣ m := by
      rw [Nat.coprime_comm] at hcop
      rw [hp.out.coprime_iff_not_dvd] at hcop
      exact Classical.not_not.mp hcop
    have hm'_lt : m / p < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm) hp.out.one_lt
    have hm'_ne : m / p ≠ 0 := by
      intro h; have h2 := Nat.div_mul_cancel hdvd; simp [h] at h2; exact hm h2.symm

    have hpQ : p • ((m / p) • P) = 0 := by
      rw [← mul_nsmul', Nat.mul_div_cancel' hdvd]; exact htors

    have hQ_mem : (m / p) • P ∈ padicFiltration W ha1 ha2 ha3 1 := nsmul_mem hP1 (m / p)

    have hQ_all : ∀ k : ℕ, InPadicFiltration W k ((m / p) • P) := by
      intro k
      induction k with
      | zero => exact padicFiltration_antitone W ha1 ha2 ha3 (Nat.zero_le 1) hQ_mem
      | succ n =>
        rename_i hk_ih
        by_cases hn : 0 < n
        · exact p_nsmul_in_filtration_succ_ax ha1 ha2 ha3 n hn _ hk_ih hpQ
        · simp only [Nat.not_lt, Nat.le_zero] at hn; subst hn; exact hQ_mem

    have hQ_zero : (m / p) • P = 0 := inPadicFiltration_all_eq_zero hQ_all

    exact ih (m / p) hm'_lt hm'_ne hQ_zero

/-- Corollary 24.18 (kernel-of-reduction form): the additive subgroup $E_1(\mathbb{Q}_p)$ has no
nontrivial torsion. Proved from `torsion_in_E1_eq_zero` by reducing equalities of subgroup
elements to differences. -/
theorem cor_24_18_torsion_free_ax {p : ℕ} [hp : Fact (Nat.Prime p)]
    (W : WeierstrassCurve ℚ)
    (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0)
    [hW : (W.baseChange ℚ_[p]).IsElliptic] :
    IsAddTorsionFree (reductionKernel W ha1 ha2 ha3 (p := p)) := by
  rw [isAddTorsionFree_iff]
  intro n hn a b hab
  suffices h : a - b = 0 from sub_eq_zero.mp h
  have hsub : n • (a - b) = 0 := by rw [nsmul_sub, sub_eq_zero]; exact hab
  set c := a - b
  set Q : PadicPointGroup W (p := p) := (c : PadicPointGroup W (p := p)) with hQ_def
  have hQ_tors : n • Q = 0 := by
    have h := congr_arg Subtype.val hsub
    simp only [AddSubgroup.coe_nsmul, AddSubgroup.coe_zero] at h
    exact h
  have hQ_mem : Q ∈ padicFiltration W ha1 ha2 ha3 1 := c.prop
  have hzero : Q = 0 := torsion_in_E1_eq_zero ha1 ha2 ha3 Q hQ_mem n hn hQ_tors
  exact Subtype.ext hzero

/-- Corollary 24.18: the kernel of reduction $E_1(\mathbb{Q}_p)$ is torsion-free, the user-facing
restatement of `cor_24_18_torsion_free_ax`. -/
theorem cor_24_18_torsion_free (W : WeierstrassCurve ℚ)
    (ha1 : W.a₁ = 0) (ha2 : W.a₂ = 0) (ha3 : W.a₃ = 0)
    [hW : (W.baseChange ℚ_[p]).IsElliptic] :
    IsAddTorsionFree (reductionKernel W ha1 ha2 ha3 (p := p)) :=
  cor_24_18_torsion_free_ax W ha1 ha2 ha3


end PadicElliptic

end
