/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.EllipticFunction
import Atlas.EllipticCurves.code.Theorem161
import Atlas.EllipticCurves.code.Uniformization
import Mathlib.Algebra.Ring.Subring.Defs
import Mathlib.RingTheory.Polynomial.Basic

namespace ComplexLattice

noncomputable section

open Pointwise

/-- The *endomorphism ring* $\mathrm{End}(L)$ of a complex lattice $L$ is the subring
of $\mathbb{C}$ consisting of all $\alpha \in \mathbb{C}$ such that $\alpha L \subseteq L$.
Equivalently, an element $\alpha$ lies in $\mathrm{End}(L)$ iff multiplication by $\alpha$
preserves the additive subgroup underlying $L$. -/
def endomorphismRing (L : ComplexLattice) : Subring ℂ where
  carrier := { α : ℂ | ∀ z ∈ L.toAddSubgroup, α * z ∈ L.toAddSubgroup }
  mul_mem' {a b} ha hb z hz := by rw [mul_assoc]; exact ha _ (hb z hz)
  one_mem' z hz := by rwa [one_mul]
  add_mem' {a b} ha hb z hz := by
    rw [add_mul]; exact L.toAddSubgroup.add_mem (ha z hz) (hb z hz)
  zero_mem' _ _ := by rw [zero_mul]; exact L.toAddSubgroup.zero_mem
  neg_mem' {a} ha z hz := by rw [neg_mul]; exact L.toAddSubgroup.neg_mem (ha z hz)

/-- Characterization of membership in the endomorphism ring: $\alpha \in \mathrm{End}(L)$
iff $\alpha \cdot z \in L$ for every $z \in L$. -/
@[simp]
theorem mem_endomorphismRing {L : ComplexLattice} {α : ℂ} :
    α ∈ L.endomorphismRing ↔ ∀ z ∈ L.toAddSubgroup, α * z ∈ L.toAddSubgroup :=
  Iff.rfl

/-- A complex lattice $L$ is a *proper $\mathcal{O}$-ideal* if its endomorphism ring
equals $\mathcal{O}$ exactly (not just contains $\mathcal{O}$).  This is the standard
notion of proper ideal in the theory of orders in imaginary quadratic fields. -/
def IsProperIdeal (𝒪 : Subring ℂ) (L : ComplexLattice) : Prop :=
  L.endomorphismRing = 𝒪

/-- Two proper $\mathcal{O}$-ideals $L_1$ and $L_2$ are *equivalent* if there exist
nonzero $\alpha, \beta \in \mathcal{O}$ with $\alpha L_1 = \beta L_2$ as subsets of
$\mathbb{C}$.  This is the equivalence relation whose classes form the ideal class
group of $\mathcal{O}$. -/
def IsEquivalent (𝒪 : Subring ℂ) (L₁ L₂ : ComplexLattice) : Prop :=
  ∃ (α β : 𝒪), (α : ℂ) ≠ 0 ∧ (β : ℂ) ≠ 0 ∧
    (α : ℂ) • (L₁.lattice : Set ℂ) = (β : ℂ) • (L₂.lattice : Set ℂ)

/-- Reflexivity of ideal equivalence: every lattice is equivalent to itself (witnessed
by $\alpha = \beta = 1$). -/
theorem IsEquivalent.refl (𝒪 : Subring ℂ) (L : ComplexLattice) : IsEquivalent 𝒪 L L :=
  ⟨1, 1, one_ne_zero, one_ne_zero, rfl⟩

/-- Symmetry of ideal equivalence: if $\alpha L_1 = \beta L_2$, then $\beta L_2 =
\alpha L_1$ (with the roles of $\alpha$ and $\beta$ swapped). -/
theorem IsEquivalent.symm {𝒪 : Subring ℂ} {L₁ L₂ : ComplexLattice}
    (h : IsEquivalent 𝒪 L₁ L₂) : IsEquivalent 𝒪 L₂ L₁ := by
  obtain ⟨α, β, hα, hβ, h⟩ := h
  exact ⟨β, α, hβ, hα, h.symm⟩

/-- Transitivity of ideal equivalence: if $\alpha_1 L_1 = \beta_1 L_2$ and
$\alpha_2 L_2 = \beta_2 L_3$, then $(\alpha_2\alpha_1) L_1 = (\beta_1\beta_2) L_3$. -/
theorem IsEquivalent.trans {𝒪 : Subring ℂ} {L₁ L₂ L₃ : ComplexLattice}
    (h₁₂ : IsEquivalent 𝒪 L₁ L₂) (h₂₃ : IsEquivalent 𝒪 L₂ L₃) :
    IsEquivalent 𝒪 L₁ L₃ := by
  obtain ⟨α₁, β₁, hα₁, hβ₁, h₁⟩ := h₁₂
  obtain ⟨α₂, β₂, hα₂, hβ₂, h₂⟩ := h₂₃
  refine ⟨α₂ * α₁, β₁ * β₂, ?_, ?_, ?_⟩
  · simp only [Subring.coe_mul]; exact mul_ne_zero hα₂ hα₁
  · simp only [Subring.coe_mul]; exact mul_ne_zero hβ₁ hβ₂
  · simp only [Subring.coe_mul, ← smul_smul]
    calc (↑α₂ : ℂ) • (↑α₁ : ℂ) • (L₁.lattice : Set ℂ)
        = (↑α₂ : ℂ) • (↑β₁ : ℂ) • (L₂.lattice : Set ℂ) := by rw [h₁]
      _ = (↑β₁ : ℂ) • (↑α₂ : ℂ) • (L₂.lattice : Set ℂ) := by
          rw [show (↑α₂ : ℂ) • (↑β₁ : ℂ) • (L₂.lattice : Set ℂ) =
                  (↑β₁ : ℂ) • (↑α₂ : ℂ) • (L₂.lattice : Set ℂ) from by
            rw [smul_smul, smul_smul, mul_comm]]
      _ = (↑β₁ : ℂ) • (↑β₂ : ℂ) • (L₃.lattice : Set ℂ) := by rw [h₂]

/-- The relation `IsEquivalent 𝒪` is an equivalence relation on complex lattices. -/
theorem isEquivalent_equivalence (𝒪 : Subring ℂ) :
    Equivalence (IsEquivalent 𝒪) :=
  ⟨IsEquivalent.refl 𝒪, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Ideal equivalence implies homothety: if $\alpha L_1 = \beta L_2$, then
$L_2 = (\beta^{-1}\alpha) L_1$, so the lattices are homothetic with factor
$\beta^{-1}\alpha$. -/
theorem IsEquivalent.isHomothetic {𝒪 : Subring ℂ} {L₁ L₂ : ComplexLattice}
    (h : IsEquivalent 𝒪 L₁ L₂) : IsHomothetic L₁ L₂ := by
  obtain ⟨α, β, hα, hβ, h⟩ := h
  refine ⟨(β : ℂ)⁻¹ * (α : ℂ), mul_ne_zero (inv_ne_zero hβ) hα, ?_⟩

  have := congr_arg ((β : ℂ)⁻¹ • ·) h
  simp only [smul_smul, inv_mul_cancel₀ hβ, one_smul] at this
  exact this.symm

/-- The type of *proper $\mathcal{O}$-ideals*: pairs $(L, \mathrm{proof})$ where $L$ is
a complex lattice, $L$ is a proper $\mathcal{O}$-ideal (its endomorphism ring equals
$\mathcal{O}$), and $L$ is contained in $\mathcal{O}$ as a subset of $\mathbb{C}$. -/
def ProperIdeal (𝒪 : Subring ℂ) : Type :=
  { L : ComplexLattice // IsProperIdeal 𝒪 L ∧ ∀ z ∈ L.toAddSubgroup, z ∈ 𝒪 }

/-- The setoid structure on proper $\mathcal{O}$-ideals induced by ideal equivalence;
the quotient is the ideal class group of $\mathcal{O}$. -/
def properIdealSetoid (𝒪 : Subring ℂ) : Setoid (ProperIdeal 𝒪) where
  r L₁ L₂ := IsEquivalent 𝒪 L₁.val L₂.val
  iseqv := {
    refl := fun L => (isEquivalent_equivalence 𝒪).refl L.val
    symm := fun h => (isEquivalent_equivalence 𝒪).symm h
    trans := fun h₁ h₂ => (isEquivalent_equivalence 𝒪).trans h₁ h₂
  }

/-- The *ideal class group* $\mathrm{Cl}(\mathcal{O})$ of an order $\mathcal{O}$: the
quotient of proper $\mathcal{O}$-ideals by the equivalence relation of being equal up
to scaling by nonzero elements of $\mathcal{O}$.  It is a finite abelian group whose
order is the class number $h(\mathcal{O})$. -/
def IdealClassGroup (𝒪 : Subring ℂ) : Type :=
  Quotient (properIdealSetoid 𝒪)

/-- The class of a proper $\mathcal{O}$-ideal in the ideal class group. -/
def IdealClassGroup.mk (𝒪 : Subring ℂ) (L : ProperIdeal 𝒪) : IdealClassGroup 𝒪 :=
  Quotient.mk (properIdealSetoid 𝒪) L

/-- Two proper ideals define the same class in $\mathrm{Cl}(\mathcal{O})$ iff they are
equivalent as ideals. -/
theorem IdealClassGroup.mk_eq_mk_iff (𝒪 : Subring ℂ) (L₁ L₂ : ProperIdeal 𝒪) :
    IdealClassGroup.mk 𝒪 L₁ = IdealClassGroup.mk 𝒪 L₂ ↔
      IsEquivalent 𝒪 L₁.val L₂.val :=
  Quotient.eq (r := properIdealSetoid 𝒪)

/-- The *product* of two proper $\mathcal{O}$-ideals: given $\mathfrak{a}$ with period
pair $(\omega_1, \omega_2)$ and $\mathfrak{b}$ with period pair $(\omega_1', \omega_2')$,
the product is the lattice with period pair $(\omega_1\omega_1', \omega_1\omega_2')$.
The result is again a proper $\mathcal{O}$-ideal. -/
def ProperIdeal.mul (𝒪 : Subring ℂ) (𝔞 𝔟 : ProperIdeal 𝒪) : ProperIdeal 𝒪 :=
  let L₁ := 𝔞.val
  let L₂ := 𝔟.val


  have hω₁_ne : L₁.ω₁ ≠ 0 := by
    have := L₁.indep.ne_zero (⟨0, by omega⟩ : Fin 2)
    simpa using this
  have hindep : LinearIndependent ℝ ![L₁.ω₁ * L₂.ω₁, L₁.ω₁ * L₂.ω₂] := by
    let f : ℂ →ₗ[ℝ] ℂ := (Algebra.lmul ℝ ℂ) L₁.ω₁
    have hf_apply : ∀ x, f x = L₁.ω₁ * x := fun x => LinearMap.mul_apply' L₁.ω₁ x
    have hf_inj : Function.Injective f := by
      intro a b hab
      rw [hf_apply, hf_apply] at hab
      exact mul_left_cancel₀ hω₁_ne hab
    have hcomp : ![L₁.ω₁ * L₂.ω₁, L₁.ω₁ * L₂.ω₂] = f ∘ ![L₂.ω₁, L₂.ω₂] := by
      ext i; fin_cases i <;> simp [hf_apply]
    rw [hcomp]
    exact L₂.indep.map' f (LinearMap.ker_eq_bot_of_injective hf_inj)
  let Lprod : PeriodPair := ⟨L₁.ω₁ * L₂.ω₁, L₁.ω₁ * L₂.ω₂, hindep⟩
  ⟨Lprod,
    ⟨by


      show endomorphismRing Lprod = 𝒪
      rw [← 𝔟.prop.1]
      ext α
      simp only [mem_endomorphismRing]
      constructor
      ·
        intro hα z hz
        have hωz : L₁.ω₁ * z ∈ Lprod.lattice := by
          rw [PeriodPair.mem_lattice]
          obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hz
          exact ⟨m, n, by ring⟩
        have hαωz' := hα _ hωz
        have hαωz : L₁.ω₁ * (α * z) ∈ Lprod.lattice := by
          rwa [show α * (L₁.ω₁ * z) = L₁.ω₁ * (α * z) by ring] at hαωz'
        rw [PeriodPair.mem_lattice] at hαωz
        obtain ⟨m, n, hmn⟩ := hαωz
        show α * z ∈ L₂.lattice
        rw [PeriodPair.mem_lattice]
        refine ⟨m, n, mul_left_cancel₀ hω₁_ne ?_⟩
        have : ↑m * (L₁.ω₁ * L₂.ω₁) + ↑n * (L₁.ω₁ * L₂.ω₂) = L₁.ω₁ * (α * z) := hmn
        linear_combination this

      ·
        intro hα z hz
        obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.mp hz
        show α * (↑m * (L₁.ω₁ * L₂.ω₁) + ↑n * (L₁.ω₁ * L₂.ω₂)) ∈ Lprod.lattice
        have helem : (↑m * L₂.ω₁ + ↑n * L₂.ω₂) ∈ L₂.toAddSubgroup := by
          show _ ∈ L₂.lattice
          exact PeriodPair.mem_lattice.mpr ⟨m, n, rfl⟩
        have hα_elem := hα _ helem
        obtain ⟨m', n', hm'n'⟩ := PeriodPair.mem_lattice.mp hα_elem
        rw [PeriodPair.mem_lattice]
        exact ⟨m', n', by linear_combination L₁.ω₁ * hm'n'⟩,

     by

      intro z hz
      have hω₁_mem : L₁.ω₁ ∈ 𝒪 :=
        𝔞.prop.2 L₁.ω₁ (show L₁.ω₁ ∈ L₁.toAddSubgroup from L₁.ω₁_mem_lattice)
      have hω₁'_mem : L₂.ω₁ ∈ 𝒪 :=
        𝔟.prop.2 L₂.ω₁ (show L₂.ω₁ ∈ L₂.toAddSubgroup from L₂.ω₁_mem_lattice)
      have hω₂'_mem : L₂.ω₂ ∈ 𝒪 :=
        𝔟.prop.2 L₂.ω₂ (show L₂.ω₂ ∈ L₂.toAddSubgroup from L₂.ω₂_mem_lattice)
      have hmem : z ∈ Lprod.lattice := hz
      rw [PeriodPair.mem_lattice] at hmem
      obtain ⟨m, n, rfl⟩ := hmem
      exact 𝒪.add_mem (𝒪.mul_mem (intCast_mem 𝒪 m) (𝒪.mul_mem hω₁_mem hω₁'_mem))
        (𝒪.mul_mem (intCast_mem 𝒪 n) (𝒪.mul_mem hω₁_mem hω₂'_mem))⟩⟩

/-- The subring $\mathcal{O} \subseteq \mathbb{C}$ viewed as a complex lattice, when
$\mathcal{O}$ is an order in an imaginary quadratic field.  This is the lattice
underlying the unit ideal $\mathcal{O}$ itself. -/
noncomputable def subringAsComplexLattice (𝒪 : Subring ℂ) : ComplexLattice := by sorry

/-- The underlying set of `subringAsComplexLattice 𝒪` coincides with the set of
elements of $\mathcal{O}$. -/
theorem subringAsComplexLattice_mem (𝒪 : Subring ℂ) (z : ℂ) :
    z ∈ (subringAsComplexLattice 𝒪).toAddSubgroup ↔ z ∈ 𝒪 := by sorry

/-- The endomorphism ring of $\mathcal{O}$ (viewed as a lattice) equals $\mathcal{O}$
itself, so $\mathcal{O}$ is a proper ideal of itself. -/
theorem endomorphismRing_subring_eq (𝒪 : Subring ℂ) :
    (subringAsComplexLattice 𝒪).endomorphismRing = 𝒪 := by
  ext α
  simp only [mem_endomorphismRing]
  constructor
  · intro h
    have h1 : (1 : ℂ) ∈ (subringAsComplexLattice 𝒪).toAddSubgroup :=
      (subringAsComplexLattice_mem 𝒪 1).mpr (one_mem 𝒪)
    have := h 1 h1
    rw [mul_one] at this
    exact (subringAsComplexLattice_mem 𝒪 α).mp this
  · intro hα z hz
    rw [subringAsComplexLattice_mem] at hz ⊢
    exact mul_mem hα hz

/-- The *unit element* of the ideal class group: the proper $\mathcal{O}$-ideal
$\mathcal{O}$ itself. -/
def ProperIdeal.one (𝒪 : Subring ℂ) : ProperIdeal 𝒪 :=
  ⟨subringAsComplexLattice 𝒪,
    endomorphismRing_subring_eq 𝒪,
    fun z hz => (subringAsComplexLattice_mem 𝒪 z).mp hz⟩

/-- If $L_{\mathrm{inv}}$ has period pair $(\bar\omega_1/N(\omega_1), \bar\omega_2/N(\omega_1))$
for a proper $\mathcal{O}$-ideal $\mathfrak{a}$, then $L_{\mathrm{inv}}$ is again a proper
$\mathcal{O}$-ideal.  This is the construction of the inverse ideal in the ideal class
group. -/
theorem conjugateScaledLattice_isProperIdeal (𝒪 : Subring ℂ)
    (𝔞 : ProperIdeal 𝒪) (Linv : ComplexLattice)
    (hω₁ : Linv.ω₁ = starRingEnd ℂ 𝔞.val.ω₁ / ↑(Complex.normSq 𝔞.val.ω₁))
    (hω₂ : Linv.ω₂ = starRingEnd ℂ 𝔞.val.ω₂ / ↑(Complex.normSq 𝔞.val.ω₁)) :
    IsProperIdeal 𝒪 Linv := by sorry

/-- The conjugate-scaled lattice $L_{\mathrm{inv}}$ is contained in $\mathcal{O}$;
together with `conjugateScaledLattice_isProperIdeal` this shows that it qualifies as
a proper $\mathcal{O}$-ideal. -/
theorem conjugateScaledLattice_subset_order (𝒪 : Subring ℂ)
    (𝔞 : ProperIdeal 𝒪) (Linv : ComplexLattice)
    (hω₁ : Linv.ω₁ = starRingEnd ℂ 𝔞.val.ω₁ / ↑(Complex.normSq 𝔞.val.ω₁))
    (hω₂ : Linv.ω₂ = starRingEnd ℂ 𝔞.val.ω₂ / ↑(Complex.normSq 𝔞.val.ω₁)) :
    ∀ z ∈ Linv.toAddSubgroup, z ∈ 𝒪 := by sorry

/-- The *inverse* of a proper $\mathcal{O}$-ideal $\mathfrak{a}$ with period pair
$(\omega_1, \omega_2)$: the proper $\mathcal{O}$-ideal with period pair
$(\bar\omega_1/N(\omega_1), \bar\omega_2/N(\omega_1))$, which represents the inverse
class in $\mathrm{Cl}(\mathcal{O})$. -/
def ProperIdeal.inv (𝒪 : Subring ℂ) (𝔞 : ProperIdeal 𝒪) : ProperIdeal 𝒪 :=
  let L := 𝔞.val

  let N : ℂ := ↑(Complex.normSq L.ω₁)

  let g₁ := starRingEnd ℂ L.ω₁ / N
  let g₂ := starRingEnd ℂ L.ω₂ / N
  have hω₁_ne : L.ω₁ ≠ 0 := by
    have := L.indep.ne_zero (⟨0, by omega⟩ : Fin 2)
    simpa using this
  have hN_ne : N ≠ 0 := by
    simp only [N, ne_eq, Complex.ofReal_eq_zero, map_eq_zero]
    exact hω₁_ne
  have hindep : LinearIndependent ℝ ![g₁, g₂] := by

    have hconj : LinearIndependent ℝ ![starRingEnd ℂ L.ω₁, starRingEnd ℂ L.ω₂] := by
      have hcomp : ![starRingEnd ℂ L.ω₁, starRingEnd ℂ L.ω₂] =
          Complex.conjCLE.toLinearMap ∘ ![L.ω₁, L.ω₂] := by
        ext i; fin_cases i <;> simp [Complex.conjCLE]
      rw [hcomp]
      exact L.indep.map' _ (LinearMap.ker_eq_bot_of_injective Complex.conjCLE.injective)

    let c := N⁻¹
    have hc_ne : c ≠ 0 := inv_ne_zero hN_ne
    have heq : ![g₁, g₂] =
      (fun x => c * x) ∘ ![starRingEnd ℂ L.ω₁, starRingEnd ℂ L.ω₂] := by
      ext i; fin_cases i <;> simp [g₁, g₂, c, div_eq_mul_inv, mul_comm]
    rw [heq]
    let f : ℂ →ₗ[ℝ] ℂ := (Algebra.lmul ℝ ℂ) c
    have hf_apply : ∀ x, f x = c * x := fun x => LinearMap.mul_apply' c x
    have hf_inj : Function.Injective f := by
      intro a b hab; rw [hf_apply, hf_apply] at hab
      exact mul_left_cancel₀ hc_ne hab
    have hcomp2 : (fun x => c * x) ∘ ![starRingEnd ℂ L.ω₁, starRingEnd ℂ L.ω₂] =
      f ∘ ![starRingEnd ℂ L.ω₁, starRingEnd ℂ L.ω₂] := by
      ext i; fin_cases i <;> simp [hf_apply]
    rw [hcomp2]
    exact hconj.map' f (LinearMap.ker_eq_bot_of_injective hf_inj)
  let Linv : PeriodPair := ⟨g₁, g₂, hindep⟩
  ⟨Linv,
    conjugateScaledLattice_isProperIdeal 𝒪 𝔞 Linv rfl rfl,
    conjugateScaledLattice_subset_order 𝒪 𝔞 Linv rfl rfl⟩

/-- For any proper $\mathcal{O}$-ideals $\mathfrak{a}, \mathfrak{b}$, the product
$\mathfrak{a}\mathfrak{b}$ is equivalent to $\mathfrak{b}$ in the ideal class group;
this is the homothety $\mathfrak{a}\mathfrak{b} = \omega_1(\mathfrak{a}) \cdot \mathfrak{b}$
underlying the definition. -/
theorem ProperIdeal.mul_equiv_snd (𝒪 : Subring ℂ) (a b : ProperIdeal 𝒪) :
    IsEquivalent 𝒪 (ProperIdeal.mul 𝒪 a b).val b.val := by
  have hω₁_mem : a.val.ω₁ ∈ 𝒪 := a.prop.2 a.val.ω₁ a.val.ω₁_mem_lattice
  have hω₁_ne : a.val.ω₁ ≠ 0 := by
    have h0 := a.val.indep.ne_zero (0 : Fin 2)
    simp only [Matrix.cons_val_zero] at h0
    exact h0
  refine ⟨1, ⟨a.val.ω₁, hω₁_mem⟩, one_ne_zero, hω₁_ne, ?_⟩


  simp only [OneMemClass.coe_one, one_smul, Subtype.coe_mk]


  have hω₁ : (ProperIdeal.mul 𝒪 a b).val.ω₁ = a.val.ω₁ * b.val.ω₁ := rfl
  have hω₂ : (ProperIdeal.mul 𝒪 a b).val.ω₂ = a.val.ω₁ * b.val.ω₂ := rfl
  ext x
  simp only [SetLike.mem_coe, Set.mem_smul_set, smul_eq_mul]
  constructor
  ·
    intro hx
    rw [PeriodPair.mem_lattice] at hx
    obtain ⟨m, n, hmn⟩ := hx
    rw [hω₁, hω₂] at hmn
    refine ⟨↑m * b.val.ω₁ + ↑n * b.val.ω₂, ?_, ?_⟩
    · exact PeriodPair.mem_lattice.mpr ⟨m, n, rfl⟩
    · linear_combination hmn
  ·
    intro ⟨y, hy, hxy⟩
    rw [PeriodPair.mem_lattice] at hy
    obtain ⟨m, n, hmn⟩ := hy
    rw [PeriodPair.mem_lattice]
    refine ⟨m, n, ?_⟩
    rw [hω₁, hω₂]
    linear_combination hxy + a.val.ω₁ * hmn

/-- Ideal multiplication respects the equivalence relation: if $\mathfrak{a}_1 \sim
\mathfrak{a}_2$ and $\mathfrak{b}_1 \sim \mathfrak{b}_2$, then $\mathfrak{a}_1\mathfrak{b}_1
\sim \mathfrak{a}_2\mathfrak{b}_2$.  This makes ideal multiplication well-defined on
class group elements. -/
theorem ProperIdeal.mul_resp (𝒪 : Subring ℂ) (a₁ a₂ b₁ b₂ : ProperIdeal 𝒪) :
    (properIdealSetoid 𝒪).r a₁ a₂ → (properIdealSetoid 𝒪).r b₁ b₂ →
    (properIdealSetoid 𝒪).r (ProperIdeal.mul 𝒪 a₁ b₁) (ProperIdeal.mul 𝒪 a₂ b₂) := by
  intro _ h₂
  exact ((ProperIdeal.mul_equiv_snd 𝒪 a₁ b₁).trans h₂).trans
    (ProperIdeal.mul_equiv_snd 𝒪 a₂ b₂).symm

/-- Associativity of ideal multiplication up to equivalence: $(\mathfrak{a}\mathfrak{b})
\mathfrak{c} \sim \mathfrak{a}(\mathfrak{b}\mathfrak{c})$. -/
theorem ProperIdeal.mul_assoc_equiv (𝒪 : Subring ℂ) (a b c : ProperIdeal 𝒪) :
    (properIdealSetoid 𝒪).r
      (ProperIdeal.mul 𝒪 (ProperIdeal.mul 𝒪 a b) c)
      (ProperIdeal.mul 𝒪 a (ProperIdeal.mul 𝒪 b c)) := by


  have heq : ProperIdeal.mul 𝒪 (ProperIdeal.mul 𝒪 a b) c =
      ProperIdeal.mul 𝒪 a (ProperIdeal.mul 𝒪 b c) := by
    apply Subtype.ext
    simp only [ProperIdeal.mul]
    congr 1 <;> exact mul_assoc _ _ _
  rw [heq]

/-- Commutativity of ideal multiplication up to equivalence: $\mathfrak{a}\mathfrak{b}
\sim \mathfrak{b}\mathfrak{a}$. -/
theorem ProperIdeal.mul_comm_equiv (𝒪 : Subring ℂ) (a b : ProperIdeal 𝒪) :
    (properIdealSetoid 𝒪).r (ProperIdeal.mul 𝒪 a b) (ProperIdeal.mul 𝒪 b a) := by sorry

/-- Left identity for ideal multiplication up to equivalence: $\mathcal{O} \cdot
\mathfrak{a} \sim \mathfrak{a}$. -/
theorem ProperIdeal.one_mul_equiv (𝒪 : Subring ℂ) (a : ProperIdeal 𝒪) :
    (properIdealSetoid 𝒪).r (ProperIdeal.mul 𝒪 (ProperIdeal.one 𝒪) a) a := by
  show IsEquivalent 𝒪 (ProperIdeal.mul 𝒪 (ProperIdeal.one 𝒪) a).val a.val

  have hω₁_mem : (subringAsComplexLattice 𝒪).ω₁ ∈ 𝒪 :=
    (subringAsComplexLattice_mem 𝒪 _).mp (subringAsComplexLattice 𝒪).ω₁_mem_lattice

  have hω₁_ne : (subringAsComplexLattice 𝒪).ω₁ ≠ 0 := by
    have := (subringAsComplexLattice 𝒪).indep.ne_zero (⟨0, by omega⟩ : Fin 2)
    simpa using this

  set L𝒪 := subringAsComplexLattice 𝒪 with hL𝒪_def
  set La := a.val with hLa_def
  set Lprod := (ProperIdeal.mul 𝒪 (ProperIdeal.one 𝒪) a).val with hLprod_def

  have hprod_ω₁ : Lprod.ω₁ = L𝒪.ω₁ * La.ω₁ := rfl
  have hprod_ω₂ : Lprod.ω₂ = L𝒪.ω₁ * La.ω₂ := rfl

  refine ⟨1, ⟨L𝒪.ω₁, hω₁_mem⟩, one_ne_zero, hω₁_ne, ?_⟩

  simp only [OneMemClass.coe_one, one_smul]

  ext x
  constructor
  ·
    intro hx
    obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.mp hx
    rw [Set.mem_smul_set]
    refine ⟨↑m * La.ω₁ + ↑n * La.ω₂, PeriodPair.mem_lattice.mpr ⟨m, n, rfl⟩, ?_⟩
    rw [smul_eq_mul, ← hmn, hprod_ω₁, hprod_ω₂]
    ring
  ·
    intro hx
    rw [Set.mem_smul_set] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨m, n, hmn⟩ := PeriodPair.mem_lattice.mp hy
    rw [smul_eq_mul, ← hmn]
    exact PeriodPair.mem_lattice.mpr ⟨m, n, by rw [hprod_ω₁, hprod_ω₂]; ring⟩

/-- Inverse property for ideal multiplication up to equivalence: $\mathfrak{a}^{-1}
\cdot \mathfrak{a} \sim \mathcal{O}$. -/
theorem ProperIdeal.inv_mul_equiv (𝒪 : Subring ℂ) (a : ProperIdeal 𝒪) :
    (properIdealSetoid 𝒪).r
      (ProperIdeal.mul 𝒪 (ProperIdeal.inv 𝒪 a) a) (ProperIdeal.one 𝒪) := by
  show IsEquivalent 𝒪 (ProperIdeal.mul 𝒪 (ProperIdeal.inv 𝒪 a) a).val (ProperIdeal.one 𝒪).val
  set prod := ProperIdeal.mul 𝒪 (ProperIdeal.inv 𝒪 a) a
  set L := a.val

  have hω₁_ne : L.ω₁ ≠ 0 := by
    have := L.indep.ne_zero (⟨0, by omega⟩ : Fin 2); simpa using this
  have hN_ne : (Complex.normSq L.ω₁ : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, map_eq_zero]; exact hω₁_ne

  have hprod_ω₁ : prod.val.ω₁ = 1 := by
    show (starRingEnd ℂ L.ω₁ / ↑(Complex.normSq L.ω₁)) * L.ω₁ = 1
    rw [div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self]
    exact div_self hN_ne


  have hprod_sub_𝒪 : ∀ z ∈ prod.val.toAddSubgroup, z ∈ 𝒪 := prod.prop.2

  have h1_mem_prod : (1 : ℂ) ∈ prod.val.toAddSubgroup := by
    rw [show (1 : ℂ) = prod.val.ω₁ from hprod_ω₁.symm]
    exact prod.val.ω₁_mem_lattice
  have hendo : prod.val.endomorphismRing = 𝒪 := prod.prop.1
  have h𝒪_sub_prod : ∀ z ∈ (𝒪 : Set ℂ), z ∈ prod.val.toAddSubgroup := by
    intro z hz
    have hα_mem : z ∈ prod.val.endomorphismRing := by rw [hendo]; exact hz
    rw [mem_endomorphismRing] at hα_mem
    have := hα_mem 1 h1_mem_prod
    rwa [mul_one] at this

  have hone_iff : ∀ z, z ∈ (ProperIdeal.one 𝒪).val.toAddSubgroup ↔ z ∈ 𝒪 := fun z =>
    subringAsComplexLattice_mem 𝒪 z

  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  simp only [OneMemClass.coe_one, one_smul]

  ext x
  constructor
  · intro hx
    rw [show (x ∈ (prod.val.lattice : Set ℂ)) = (x ∈ prod.val.toAddSubgroup) from rfl] at hx
    exact (hone_iff x).mpr (hprod_sub_𝒪 x hx)
  · intro hx
    show x ∈ prod.val.toAddSubgroup
    exact h𝒪_sub_prod x ((hone_iff x).mp hx)

/-- Ideal inversion respects the equivalence relation: equivalent ideals have
equivalent inverses.  This makes inversion well-defined on class group elements. -/
theorem ProperIdeal.inv_resp (𝒪 : Subring ℂ) (a₁ a₂ : ProperIdeal 𝒪) :
    (properIdealSetoid 𝒪).r a₁ a₂ →
    (properIdealSetoid 𝒪).r (ProperIdeal.inv 𝒪 a₁) (ProperIdeal.inv 𝒪 a₂) := by
  intro h
  let S := properIdealSetoid 𝒪
  have equiv := S.iseqv

  have mul_one_inv_a₁ : S.r (ProperIdeal.inv 𝒪 a₁)
      (ProperIdeal.mul 𝒪 (ProperIdeal.inv 𝒪 a₁) (ProperIdeal.one 𝒪)) :=
    equiv.symm (equiv.trans (ProperIdeal.mul_comm_equiv 𝒪 _ _)
      (ProperIdeal.one_mul_equiv 𝒪 _))

  have a₂_mul_inv_a₂ : S.r (ProperIdeal.mul 𝒪 a₂ (ProperIdeal.inv 𝒪 a₂))
      (ProperIdeal.one 𝒪) :=
    equiv.trans (ProperIdeal.mul_comm_equiv 𝒪 _ _)
      (ProperIdeal.inv_mul_equiv 𝒪 _)

  have step3 : S.r (ProperIdeal.mul 𝒪 (ProperIdeal.inv 𝒪 a₁) (ProperIdeal.one 𝒪))
      (ProperIdeal.mul 𝒪 (ProperIdeal.inv 𝒪 a₁)
        (ProperIdeal.mul 𝒪 a₂ (ProperIdeal.inv 𝒪 a₂))) :=
    ProperIdeal.mul_resp 𝒪 _ _ _ _ (equiv.refl _) (equiv.symm a₂_mul_inv_a₂)

  have step5 : S.r (ProperIdeal.mul 𝒪 (ProperIdeal.inv 𝒪 a₁)
        (ProperIdeal.mul 𝒪 a₂ (ProperIdeal.inv 𝒪 a₂)))
      (ProperIdeal.mul 𝒪 (ProperIdeal.inv 𝒪 a₁)
        (ProperIdeal.mul 𝒪 a₁ (ProperIdeal.inv 𝒪 a₂))) :=
    ProperIdeal.mul_resp 𝒪 _ _ _ _ (equiv.refl _)
      (ProperIdeal.mul_resp 𝒪 _ _ _ _ (equiv.symm h) (equiv.refl _))

  have step6 : S.r (ProperIdeal.mul 𝒪 (ProperIdeal.inv 𝒪 a₁)
        (ProperIdeal.mul 𝒪 a₁ (ProperIdeal.inv 𝒪 a₂)))
      (ProperIdeal.mul 𝒪 (ProperIdeal.mul 𝒪 (ProperIdeal.inv 𝒪 a₁) a₁)
        (ProperIdeal.inv 𝒪 a₂)) :=
    equiv.symm (ProperIdeal.mul_assoc_equiv 𝒪 _ _ _)

  have step7 : S.r (ProperIdeal.mul 𝒪 (ProperIdeal.mul 𝒪 (ProperIdeal.inv 𝒪 a₁) a₁)
        (ProperIdeal.inv 𝒪 a₂))
      (ProperIdeal.mul 𝒪 (ProperIdeal.one 𝒪) (ProperIdeal.inv 𝒪 a₂)) :=
    ProperIdeal.mul_resp 𝒪 _ _ _ _ (ProperIdeal.inv_mul_equiv 𝒪 _) (equiv.refl _)

  exact equiv.trans mul_one_inv_a₁ (equiv.trans step3 (equiv.trans step5
    (equiv.trans step6 (equiv.trans step7 (ProperIdeal.one_mul_equiv 𝒪 _)))))

/-- The *commutative group structure* on the ideal class group $\mathrm{Cl}(\mathcal{O})$.
Multiplication, identity, and inversion are induced from the corresponding operations
on proper $\mathcal{O}$-ideals via the quotient by ideal equivalence. -/
@[reducible]
noncomputable def IdealClassGroup.commGroup (𝒪 : Subring ℂ) :
    CommGroup (IdealClassGroup 𝒪) where
  mul := Quotient.lift₂
    (fun a b => @Quotient.mk _ (properIdealSetoid 𝒪) (ProperIdeal.mul 𝒪 a b))
    (fun _ _ _ _ h₁ h₂ => Quotient.sound (ProperIdeal.mul_resp 𝒪 _ _ _ _ h₁ h₂))
  mul_assoc := by
    intro a b c
    induction a using Quotient.ind
    induction b using Quotient.ind
    induction c using Quotient.ind
    exact Quotient.sound (ProperIdeal.mul_assoc_equiv 𝒪 _ _ _)
  one := @Quotient.mk _ (properIdealSetoid 𝒪) (ProperIdeal.one 𝒪)
  one_mul := by
    intro a
    induction a using Quotient.ind
    exact Quotient.sound (ProperIdeal.one_mul_equiv 𝒪 _)
  mul_one := by
    intro a
    induction a using Quotient.ind
    exact Quotient.sound ((properIdealSetoid 𝒪).iseqv.trans
      (ProperIdeal.mul_comm_equiv 𝒪 _ _) (ProperIdeal.one_mul_equiv 𝒪 _))
  inv := Quotient.lift
    (fun a => @Quotient.mk _ (properIdealSetoid 𝒪) (ProperIdeal.inv 𝒪 a))
    (fun _ _ h => Quotient.sound (ProperIdeal.inv_resp 𝒪 _ _ h))
  inv_mul_cancel := by
    intro a
    induction a using Quotient.ind
    exact Quotient.sound (ProperIdeal.inv_mul_equiv 𝒪 _)
  mul_comm := by
    intro a b
    induction a using Quotient.ind
    induction b using Quotient.ind
    exact Quotient.sound (ProperIdeal.mul_comm_equiv 𝒪 _ _)

/-- *Finiteness of the ideal class group*: there exist finitely many proper ideal
representatives that surject onto $\mathrm{Cl}(\mathcal{O})$.  This is the classical
finiteness theorem for orders in imaginary quadratic fields. -/
theorem ProperIdeal.finite_representatives (𝒪 : Subring ℂ) :
    ∃ (n : ℕ) (f : Fin n → ProperIdeal 𝒪),
      ∀ x : IdealClassGroup 𝒪, ∃ i, IdealClassGroup.mk 𝒪 (f i) = x := by sorry

/-- The ideal class group $\mathrm{Cl}(\mathcal{O})$ is a finite type. -/
theorem IdealClassGroup.finite (𝒪 : Subring ℂ) :
    Finite (IdealClassGroup 𝒪) := by
  obtain ⟨n, f, hf⟩ := ProperIdeal.finite_representatives 𝒪
  exact Finite.of_surjective (fun i => IdealClassGroup.mk 𝒪 (f i))
    (fun x => let ⟨i, hi⟩ := hf x; ⟨i, hi⟩)

/-- The *class number* $h(\mathcal{O}) = |\mathrm{Cl}(\mathcal{O})|$ of an order
$\mathcal{O}$. -/
noncomputable def classNumber (𝒪 : Subring ℂ) : ℕ :=
  Nat.card (IdealClassGroup 𝒪)

end

end ComplexLattice

namespace ComplexLattice

noncomputable section

open Pointwise

/-- A subring $\mathcal{O} \subseteq \mathbb{C}$ is an *order in an imaginary quadratic
field* if it contains some non-integer element $\tau$ that satisfies a monic integer
quadratic polynomial $\tau^2 + b\tau + c = 0$ with negative discriminant $b^2 - 4c < 0$. -/
def IsImagQuadOrder (𝒪 : Subring ℂ) : Prop :=
  ∃ τ : ℂ, τ ∈ 𝒪 ∧ (∀ n : ℤ, τ ≠ (n : ℂ)) ∧
    ∃ b c : ℤ, τ * τ + (b : ℂ) * τ + (c : ℂ) = 0 ∧
      (b : ℤ) * b - 4 * c < 0

/-- The setoid structure on proper $\mathcal{O}$-ideals induced by *homothety*: two
proper ideals are identified if one is a complex scalar multiple of the other. -/
def homothetySetoidCM (𝒪 : Subring ℂ) : Setoid (ProperIdeal 𝒪) where
  r L₁ L₂ := IsHomothetic L₁.val L₂.val
  iseqv := {
    refl := fun L => isHomothetic_equivalence.refl L.val
    symm := fun h => isHomothetic_equivalence.symm h
    trans := fun h₁ h₂ => isHomothetic_equivalence.trans h₁ h₂
  }

/-- The set of *homothety classes* of proper $\mathcal{O}$-ideals.  When $\mathcal{O}$
is an order in an imaginary quadratic field, this set is in canonical bijection with
the ideal class group $\mathrm{Cl}(\mathcal{O})$. -/
def HomothetyClassCM (𝒪 : Subring ℂ) : Type :=
  Quotient (homothetySetoidCM 𝒪)

/-- A proper $\mathcal{O}$-ideal is contained in $\mathcal{O}$: every element of the
lattice underlying a proper ideal lies in $\mathcal{O}$. -/
theorem lattice_subset_of_isImagQuadOrder (𝒪 : Subring ℂ)
    (h𝒪 : IsImagQuadOrder 𝒪) (L : ProperIdeal 𝒪)
    (z : ℂ) (hz : z ∈ L.val.toAddSubgroup) : z ∈ 𝒪 :=
  L.property.2 z hz

/-- The first basis vector $\omega_1$ of a proper $\mathcal{O}$-ideal lies in
$\mathcal{O}$. -/
theorem omega1_mem_of_isImagQuadOrder (𝒪 : Subring ℂ) (h𝒪 : IsImagQuadOrder 𝒪)
    (L : ProperIdeal 𝒪) : L.val.ω₁ ∈ 𝒪 :=
  lattice_subset_of_isImagQuadOrder 𝒪 h𝒪 L L.val.ω₁ (ComplexLattice.ω₁_mem L.val)

/-- If $L_2 = c \cdot L_1$ (homothety) with $c \neq 0$ and both are proper
$\mathcal{O}$-ideals, then $c \omega_1(L_1) \in \mathcal{O}$. -/
theorem lambda_omega1_mem_of_isImagQuadOrder (𝒪 : Subring ℂ)
    (h𝒪 : IsImagQuadOrder 𝒪)
    (L₁ L₂ : ProperIdeal 𝒪) (c : ℂ) (hc : c ≠ 0)
    (hL : (L₂.val.lattice : Set ℂ) = c • (L₁.val.lattice : Set ℂ)) :
    c * L₁.val.ω₁ ∈ 𝒪 := by
  have hω₁_in_L₁ : L₁.val.ω₁ ∈ (L₁.val.lattice : Set ℂ) := ComplexLattice.ω₁_mem L₁.val
  have hcω₁_in_L₂ : c * L₁.val.ω₁ ∈ (L₂.val.lattice : Set ℂ) := by
    rw [hL]; exact ⟨L₁.val.ω₁, hω₁_in_L₁, rfl⟩
  exact lattice_subset_of_isImagQuadOrder 𝒪 h𝒪 L₂ (c * L₁.val.ω₁) hcω₁_in_L₂

/-- For proper ideals of an imaginary-quadratic order, homothety implies ideal
equivalence.  Combined with the converse `IsEquivalent.isHomothetic`, this means
the two notions of equivalence coincide for proper ideals. -/
theorem isEquivalent_of_isHomothetic_properIdeal (𝒪 : Subring ℂ)
    (h𝒪 : IsImagQuadOrder 𝒪) (L₁ L₂ : ProperIdeal 𝒪)
    (h : IsHomothetic L₁.val L₂.val) : IsEquivalent 𝒪 L₁.val L₂.val := by
  obtain ⟨c, hc_ne, hL2_eq⟩ := h
  have hω₁_mem : L₁.val.ω₁ ∈ 𝒪 := omega1_mem_of_isImagQuadOrder 𝒪 h𝒪 L₁
  have hcω₁_mem : c * L₁.val.ω₁ ∈ 𝒪 :=
    lambda_omega1_mem_of_isImagQuadOrder 𝒪 h𝒪 L₁ L₂ c hc_ne hL2_eq
  have hω₁_ne : L₁.val.ω₁ ≠ 0 := by
    have h0 := L₁.val.indep.ne_zero (0 : Fin 2)
    simp only [Matrix.cons_val_zero] at h0
    exact h0
  refine ⟨⟨c * L₁.val.ω₁, hcω₁_mem⟩, ⟨L₁.val.ω₁, hω₁_mem⟩, ?_, ?_, ?_⟩
  · exact mul_ne_zero hc_ne hω₁_ne
  · exact hω₁_ne
  · show (c * L₁.val.ω₁) • (L₁.val.lattice : Set ℂ) =
         L₁.val.ω₁ • (L₂.val.lattice : Set ℂ)
    rw [hL2_eq, smul_smul]
    congr 1
    ring

/-- For proper ideals of an order in an imaginary quadratic field, ideal equivalence
and homothety are equivalent notions. -/
theorem isEquivalent_iff_isHomothetic_properIdeal (𝒪 : Subring ℂ)
    (h𝒪 : IsImagQuadOrder 𝒪) (L₁ L₂ : ProperIdeal 𝒪) :
    IsEquivalent 𝒪 L₁.val L₂.val ↔ IsHomothetic L₁.val L₂.val :=
  ⟨IsEquivalent.isHomothetic, isEquivalent_of_isHomothetic_properIdeal 𝒪 h𝒪 L₁ L₂⟩

/-- For an order $\mathcal{O}$ in an imaginary quadratic field, the ideal class group
is in canonical bijection with the set of homothety classes of proper $\mathcal{O}$-ideals. -/
def idealClassGroup_equiv_homothetyClass (𝒪 : Subring ℂ) (h𝒪 : IsImagQuadOrder 𝒪) :
    IdealClassGroup 𝒪 ≃ HomothetyClassCM 𝒪 :=
  Quotient.congr (Equiv.refl _)
    (fun L₁ L₂ => isEquivalent_iff_isHomothetic_properIdeal 𝒪 h𝒪 L₁ L₂)

end

end ComplexLattice

namespace ComplexLattice

noncomputable section

/-- The endomorphism ring $\mathrm{End}(L)$ of any complex lattice $L$ is commutative,
since it is a subring of $\mathbb{C}$. -/
theorem endomorphismRing_commutative (L : ComplexLattice) :
    ∀ α β : ℂ, α ∈ L.endomorphismRing → β ∈ L.endomorphismRing →
      α * β = β * α :=
  fun _ _ _ _ => mul_comm _ _

/-- *Classification of endomorphism rings* (Theorem 12.17): the endomorphism ring
of any complex lattice $L$ is either isomorphic to $\mathbb{Z}$ (constructor `isZ`),
or is an order in an imaginary quadratic field (constructor `isOrderInImagQuadField`),
in which case $L$ embeds into that order via $\alpha \mapsto \alpha\omega_1$. -/
inductive EndomorphismRingClassification (L : ComplexLattice) : Prop where
  | isZ (h : ∀ α : ℂ, α ∈ L.endomorphismRing → ∃ n : ℤ, α = (n : ℂ)) :
      EndomorphismRingClassification L
  | isOrderInImagQuadField
      (hIsOrder : IsImagQuadOrder L.endomorphismRing)
      (hLatticeEmbed : ∀ α : ℂ, α ∈ L.endomorphismRing →
        ∃ a' b' : ℤ, ↑a' * L.ω₁ + ↑b' * L.ω₂ = α * L.ω₁) :
      EndomorphismRingClassification L

/-- A complex lattice $L$ *has complex multiplication* iff its endomorphism ring
contains some non-integer element (i.e. is strictly larger than $\mathbb{Z}$). -/
def HasComplexMultiplication (L : ComplexLattice) : Prop :=
  ∃ τ : ℂ, τ ∈ L.endomorphismRing ∧ ∀ n : ℤ, τ ≠ (n : ℂ)

/-- Every integer $n \in \mathbb{Z}$ acts on $L$ by multiplication, so $\mathbb{Z}
\subseteq \mathrm{End}(L)$ for any complex lattice $L$. -/
theorem intCast_mem_endomorphismRing (L : ComplexLattice) (n : ℤ) :
    (n : ℂ) ∈ L.endomorphismRing := by
  simp only [mem_endomorphismRing]
  intro z hz
  rw [show (n : ℂ) * z = ↑n * z from rfl]
  exact AddSubgroup.int_mul_mem n hz

/-- Every $\tau \in \mathrm{End}(L)$ satisfies the *characteristic polynomial*
$\tau^2 - (a+d)\tau + (ad - bc) = 0$ where $\begin{pmatrix}a & b\\c & d\end{pmatrix}$
is the matrix representation of $\tau$ acting on the lattice basis $(\omega_1, \omega_2)$. -/
theorem endomorphismRing_charPoly (L : ComplexLattice) (τ : ℂ)
    (hτ_mem : τ ∈ L.endomorphismRing) (hτ_not_int : ∀ n : ℤ, τ ≠ (n : ℂ))
    (a b c d : ℤ)
    (hab : ↑a * L.ω₁ + ↑b * L.ω₂ = τ * L.ω₁)
    (hcd : ↑c * L.ω₁ + ↑d * L.ω₂ = τ * L.ω₂) :
    τ * τ + (↑(-(a + d)) : ℂ) * τ + (↑(a * d - b * c) : ℂ) = 0 := by
  have hω₁ : L.ω₁ ≠ 0 := by
    have h0 := L.indep.ne_zero (0 : Fin 2); simp only [Matrix.cons_val_zero] at h0; exact h0
  have hab' : τ * L.ω₁ = ↑a * L.ω₁ + ↑b * L.ω₂ := hab.symm
  have hcd' : τ * L.ω₂ = ↑c * L.ω₁ + ↑d * L.ω₂ := hcd.symm
  have h_eq : (τ * τ + (↑(-(a + d)) : ℂ) * τ + (↑(a * d - b * c) : ℂ)) * L.ω₁ = 0 := by
    have hττω : τ * τ * L.ω₁ = (↑a * ↑a + ↑b * ↑c) * L.ω₁ + (↑a * ↑b + ↑b * ↑d) * L.ω₂ := by
      calc τ * τ * L.ω₁ = τ * (τ * L.ω₁) := by ring
        _ = τ * (↑a * L.ω₁ + ↑b * L.ω₂) := by rw [hab']
        _ = ↑a * (τ * L.ω₁) + ↑b * (τ * L.ω₂) := by ring
        _ = ↑a * (↑a * L.ω₁ + ↑b * L.ω₂) + ↑b * (↑c * L.ω₁ + ↑d * L.ω₂) := by rw [hab', hcd']
        _ = (↑a * ↑a + ↑b * ↑c) * L.ω₁ + (↑a * ↑b + ↑b * ↑d) * L.ω₂ := by ring
    have expand : (τ * τ + (↑(-(a + d)) : ℂ) * τ + (↑(a * d - b * c) : ℂ)) * L.ω₁ =
        τ * τ * L.ω₁ + (↑(-(a + d)) : ℂ) * (τ * L.ω₁) + (↑(a * d - b * c) : ℂ) * L.ω₁ := by ring
    rw [expand, hττω, hab']; push_cast; ring
  rcases mul_eq_zero.mp h_eq with h' | h'
  · exact h'
  · exact absurd h' hω₁

/-- The discriminant $(a + d)^2 - 4(ad - bc) = (\mathrm{tr}\,\tau)^2 - 4\det\tau$
of the characteristic polynomial of $\tau \in \mathrm{End}(L) \setminus \mathbb{Z}$
is negative.  Hence $\tau$ generates an imaginary quadratic extension of $\mathbb{Q}$. -/
theorem endomorphismRing_negDisc (L : ComplexLattice) (τ : ℂ)
    (hτ_mem : τ ∈ L.endomorphismRing) (hτ_not_int : ∀ n : ℤ, τ ≠ (n : ℂ))
    (a b c d : ℤ)
    (hab : ↑a * L.ω₁ + ↑b * L.ω₂ = τ * L.ω₁)
    (hcd : ↑c * L.ω₁ + ↑d * L.ω₂ = τ * L.ω₂) :
    -(a + d) * -(a + d) - 4 * (a * d - b * c) < 0 := by
  have hω₁ : L.ω₁ ≠ 0 := by
    have h0 := L.indep.ne_zero (0 : Fin 2); simp only [Matrix.cons_val_zero] at h0; exact h0
  have hb_ne : (b : ℂ) ≠ 0 := by
    intro hb0
    have : (↑a : ℂ) * L.ω₁ = τ * L.ω₁ := by
      have := hab; rw [hb0, zero_mul, add_zero] at this; exact this
    exact hτ_not_int a (mul_right_cancel₀ hω₁ this.symm)
  have hτ_im : τ.im ≠ 0 := by
    intro him
    have hτ_eq : τ = (↑τ.re : ℂ) := Complex.ext (by simp) (by simp [him])
    have hab' : (↑τ.re : ℂ) * L.ω₁ = (↑a : ℂ) * L.ω₁ + (↑b : ℂ) * L.ω₂ := by
      rw [← hτ_eq]; exact hab.symm
    have hlin : (τ.re - (↑a : ℝ)) • L.ω₁ + (-(↑b : ℝ)) • L.ω₂ = 0 := by
      have : (↑(τ.re - (↑a : ℝ)) : ℂ) * L.ω₁ + (↑(-(↑b : ℝ)) : ℂ) * L.ω₂ = 0 := by
        push_cast; linear_combination hab' - (↑a : ℂ) * L.ω₁ - (↑b : ℂ) * L.ω₂
      rwa [← Complex.real_smul, ← Complex.real_smul] at this
    have hpair := LinearIndependent.pair_iff.mp L.indep _ _ hlin
    exact hb_ne (by exact_mod_cast (neg_eq_zero.mp hpair.2 : (b : ℝ) = 0))
  have hchar := endomorphismRing_charPoly L τ hτ_mem hτ_not_int a b c d hab hcd
  have him := congr_arg Complex.im hchar
  simp only [Complex.add_im, Complex.mul_im, Complex.mul_re, Complex.zero_im,
    Complex.intCast_im, Complex.intCast_re, Complex.ofReal_im, Complex.ofReal_re] at him
  have hre' := congr_arg Complex.re hchar
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.zero_re,
    Complex.intCast_re, Complex.intCast_im, Complex.ofReal_re] at hre'
  have hre_val : 2 * τ.re = (↑a : ℝ) + ↑d := by
    have : τ.im * (2 * τ.re - ((↑a : ℝ) + ↑d)) = 0 := by push_cast at him ⊢; nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hτ_im
    · linarith
  have disc_eq : ((↑a : ℝ) + ↑d) * (↑a + ↑d) - 4 * (↑a * ↑d - ↑b * ↑c) =
      -4 * (τ.im * τ.im) := by push_cast at hre' ⊢; nlinarith [hre_val]
  have him2_pos : 0 < τ.im * τ.im := mul_self_pos.mpr hτ_im
  suffices h : ((-(a + d) * -(a + d) - 4 * (a * d - b * c) : ℤ) : ℝ) < 0 by exact_mod_cast h
  push_cast; linarith

/-- *Order witness*: if $\tau \in \mathrm{End}(L)$ is not an integer, then there
exists an element of $\mathrm{End}(L)$ (namely $\tau$ itself) satisfying a monic
integer quadratic polynomial with negative discriminant.  This shows that
$\mathrm{End}(L)$ is an order in an imaginary quadratic field. -/
theorem endomorphismRing_order_witness (L : ComplexLattice) (τ : ℂ)
    (hτ_mem : τ ∈ L.endomorphismRing) (hτ_not_int : ∀ n : ℤ, τ ≠ (n : ℂ)) :
    ∃ τ' : ℂ, τ' ∈ L.endomorphismRing ∧ (∀ n : ℤ, τ' ≠ (n : ℂ)) ∧
      ∃ b c : ℤ, τ' * τ' + (b : ℂ) * τ' + (c : ℂ) = 0 ∧
        (b : ℤ) * b - 4 * c < 0 := by

  have hτω₁ : τ * L.ω₁ ∈ L.lattice :=
    hτ_mem L.ω₁ (ComplexLattice.ω₁_mem L)
  have hτω₂ : τ * L.ω₂ ∈ L.lattice :=
    hτ_mem L.ω₂ (ComplexLattice.ω₂_mem L)
  rw [ComplexLattice.mem_lattice_iff] at hτω₁ hτω₂
  obtain ⟨a, b, hab⟩ := hτω₁
  obtain ⟨c, d, hcd⟩ := hτω₂
  exact ⟨τ, hτ_mem, hτ_not_int, -(a + d), a * d - b * c,
    endomorphismRing_charPoly L τ hτ_mem hτ_not_int a b c d hab hcd,
    endomorphismRing_negDisc L τ hτ_mem hτ_not_int a b c d hab hcd⟩

/-- *Theorem 12.17 (classification of endomorphism rings)*: for every complex lattice
$L$, either $\mathrm{End}(L) \cong \mathbb{Z}$ or $\mathrm{End}(L)$ is an order in
an imaginary quadratic field. -/
theorem endomorphismRing_classification (L : ComplexLattice) : EndomorphismRingClassification L := by
  by_cases h : ∀ α : ℂ, α ∈ L.endomorphismRing → ∃ n : ℤ, α = (n : ℂ)
  · exact EndomorphismRingClassification.isZ h
  · push_neg at h
    obtain ⟨τ, hτ_mem, hτ_not_int⟩ := h
    have hw := endomorphismRing_order_witness L τ hτ_mem hτ_not_int

    have hIsOrder : IsImagQuadOrder L.endomorphismRing := by
      obtain ⟨τ', hτ'_mem, hτ'_not_int, b, c, hpoly, hdisc⟩ := hw
      exact ⟨τ', hτ'_mem, hτ'_not_int, b, c, hpoly, hdisc⟩

    have hEmbed : ∀ α : ℂ, α ∈ L.endomorphismRing →
        ∃ a' b' : ℤ, ↑a' * L.ω₁ + ↑b' * L.ω₂ = α * L.ω₁ := by
      intro α hα
      have hαω : α * L.ω₁ ∈ L.lattice := hα L.ω₁ (ComplexLattice.ω₁_mem L)
      rw [ComplexLattice.mem_lattice_iff] at hαω
      exact hαω
    exact .isOrderInImagQuadField hIsOrder hEmbed

/-- Combined statement of Theorem 12.17: $\mathrm{End}(L)$ is commutative and is
either $\mathbb{Z}$ or an order in an imaginary quadratic field. -/
theorem endomorphismRing_comm_and_classification (L : ComplexLattice) :
    (∀ α β : ℂ, α ∈ L.endomorphismRing → β ∈ L.endomorphismRing →
      α * β = β * α) ∧
    EndomorphismRingClassification L :=
  ⟨endomorphismRing_commutative L, endomorphismRing_classification L⟩

end

end ComplexLattice

namespace ComplexLattice

noncomputable section

open Pointwise Function

/-- Zero belongs to the *lattice multiplier set* $\{\alpha \in \mathbb{C} : \alpha L_1
\subseteq L_2\}$. -/
theorem latticeMulSet_zero_mem (L₁ L₂ : ComplexLattice) :
    (0 : ℂ) ∈ latticeMulSet L₁ L₂ :=
  zero_mem_latticeMulSet L₁ L₂

/-- The lattice multiplier set is closed under addition: if $\alpha L_1, \beta L_1
\subseteq L_2$, then $(\alpha + \beta) L_1 \subseteq L_2$. -/
theorem latticeMulSet_add_mem (L₁ L₂ : ComplexLattice) {α β : ℂ}
    (hα : α ∈ latticeMulSet L₁ L₂) (hβ : β ∈ latticeMulSet L₁ L₂) :
    α + β ∈ latticeMulSet L₁ L₂ := by
  intro z hz
  rw [add_mul]
  exact L₂.lattice.add_mem (hα z hz) (hβ z hz)

/-- The lattice multiplier set is closed under negation: if $\alpha L_1 \subseteq L_2$,
then $-\alpha \cdot L_1 \subseteq L_2$. -/
theorem latticeMulSet_neg_mem (L₁ L₂ : ComplexLattice) {α : ℂ}
    (hα : α ∈ latticeMulSet L₁ L₂) :
    -α ∈ latticeMulSet L₁ L₂ := by
  intro z hz
  rw [neg_mul]
  exact L₂.lattice.neg_mem (hα z hz)

/-- The lattice multiplier set $\{\alpha : \alpha L_1 \subseteq L_2\}$ packaged as an
additive subgroup of $\mathbb{C}$. -/
def latticeMulAddSubgroup (L₁ L₂ : ComplexLattice) : AddSubgroup ℂ where
  carrier := latticeMulSet L₁ L₂
  zero_mem' := latticeMulSet_zero_mem L₁ L₂
  add_mem' := latticeMulSet_add_mem L₁ L₂
  neg_mem' := latticeMulSet_neg_mem L₁ L₂

/-- The induced map between complex tori is *additive* in the multiplier: the map
induced by $\alpha + \beta$ equals the sum of the maps induced by $\alpha$ and $\beta$
separately. -/
theorem inducedMap_add (L₁ L₂ : ComplexLattice) (α β : ℂ)
    (hα : α ∈ latticeMulSet L₁ L₂) (hβ : β ∈ latticeMulSet L₁ L₂) :
    ∀ x : torusQuot L₁,
      inducedMap L₁ L₂ (α + β) (latticeMulSet_add_mem L₁ L₂ hα hβ) x =
        inducedMap L₁ L₂ α hα x + inducedMap L₁ L₂ β hβ x := by
  intro x
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective L₁.lattice.toAddSubgroup x
  change inducedMap L₁ L₂ (α + β) _ (proj L₁ z) =
    inducedMap L₁ L₂ α hα (proj L₁ z) + inducedMap L₁ L₂ β hβ (proj L₁ z)
  simp only [inducedMap_proj, add_mul, map_add]

/-- *Corollary 16.2, surjectivity part*: every holomorphic map of complex tori
sending $0$ to $0$ is induced by some multiplier $\alpha \in \mathbb{C}$ with
$\alpha L_1 \subseteq L_2$. -/
theorem corollary_16_2_surj (L₁ L₂ : ComplexLattice)
    (φ : ComplexTorusHolMap L₁ L₂) (hφ0 : φ.toFun 0 = 0) :
    ∃ α : ℂ, ∃ hα : α ∈ latticeMulSet L₁ L₂,
      ∀ z : ℂ, φ.toFun (proj L₁ z) = inducedMap L₁ L₂ α hα (proj L₁ z) :=
  theorem_16_1_existence L₁ L₂ φ hφ0

/-- *Corollary 16.2, injectivity part*: the multiplier $\alpha$ inducing a given
holomorphic map of complex tori is uniquely determined. -/
theorem corollary_16_2_inj (L₁ L₂ : ComplexLattice) (α γ : ℂ)
    (hα : α ∈ latticeMulSet L₁ L₂) (hγ : γ ∈ latticeMulSet L₁ L₂)
    (heq : ∀ z : ℂ, inducedMap L₁ L₂ α hα (proj L₁ z) =
                      inducedMap L₁ L₂ γ hγ (proj L₁ z)) :
    α = γ :=
  inducedMap_unique L₁ L₂ α γ hα hγ heq

/-- *Corollary 16.2 (combined)*: the set of holomorphic torus maps $L_1 \to L_2$
sending $0$ to $0$ is in additive bijection with the multiplier set $\{\alpha :
\alpha L_1 \subseteq L_2\}$. -/
theorem corollary_16_2 (L₁ L₂ : ComplexLattice) :

    (∀ (φ : ComplexTorusHolMap L₁ L₂), φ.toFun 0 = 0 →
      ∃ α : ℂ, ∃ hα : α ∈ latticeMulSet L₁ L₂,
        ∀ z : ℂ, φ.toFun (proj L₁ z) = inducedMap L₁ L₂ α hα (proj L₁ z)) ∧

    (∀ (α γ : ℂ) (hα : α ∈ latticeMulSet L₁ L₂) (hγ : γ ∈ latticeMulSet L₁ L₂),
      (∀ z : ℂ, inducedMap L₁ L₂ α hα (proj L₁ z) =
                  inducedMap L₁ L₂ γ hγ (proj L₁ z)) → α = γ) ∧

    (∀ (α β : ℂ) (hα : α ∈ latticeMulSet L₁ L₂) (hβ : β ∈ latticeMulSet L₁ L₂),
      ∀ x : torusQuot L₁,
        inducedMap L₁ L₂ (α + β) (latticeMulSet_add_mem L₁ L₂ hα hβ) x =
          inducedMap L₁ L₂ α hα x + inducedMap L₁ L₂ β hβ x) :=
  ⟨fun φ hφ0 => corollary_16_2_surj L₁ L₂ φ hφ0,
   fun α γ hα hγ h => corollary_16_2_inj L₁ L₂ α γ hα hγ h,
   fun α β hα hβ => inducedMap_add L₁ L₂ α β hα hβ⟩

end

end ComplexLattice

namespace ComplexLattice

noncomputable section

open Polynomial

/-- A function $f : \mathbb{C} \to \mathbb{C}$ is *even* iff $f(-z) = f(z)$ for all
$z$. -/
def IsEvenFunction (f : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, f (-z) = f z

variable (L : ComplexLattice)

/-- The composition $z \mapsto f(-z)$ of a meromorphic function with negation is
again meromorphic. -/
lemma meromorphic_comp_neg {f : ℂ → ℂ} (hf : Meromorphic f) :
    Meromorphic (fun z => f (-z)) := by
  intro x; exact (hf (-x)).comp_analyticAt analyticAt_id.neg

/-- If $f$ is $L$-periodic, then so is $z \mapsto f(-z)$. -/
lemma latticePeriodic_neg_of_latticePeriodic {f : ℂ → ℂ}
    (hper : L.IsLatticePeriodic f) :
    ∀ ω ∈ L.lattice, ∀ z : ℂ, f (-(z + ω)) = f (-z) := by
  intro ω hω z
  rw [show -(z + ω) = -z + (-ω) from by ring]
  exact hper (-ω) (L.lattice.neg_mem hω) (-z)

/-- The *even part* $f_+(z) = \tfrac{1}{2}(f(z) + f(-z))$ of an elliptic function $f$
is again an elliptic function. -/
lemma even_part_isEllipticFunction {f : ℂ → ℂ} (hf : L.IsEllipticFunction f) :
    L.IsEllipticFunction (fun z => (f z + f (-z)) / 2) where
  meromorphic := (hf.meromorphic.add (meromorphic_comp_neg hf.meromorphic)).div
    (fun _ => analyticAt_const.meromorphicAt)
  periodic ω hω z := by
    simp only
    rw [hf.periodic ω hω z,
        latticePeriodic_neg_of_latticePeriodic L hf.periodic ω hω z]

/-- The even part $f_+ = \tfrac{1}{2}(f + f \circ (-\mathrm{id}))$ is indeed an even
function. -/
lemma even_part_isEvenFunction (f : ℂ → ℂ) :
    IsEvenFunction (fun z => (f z + f (-z)) / 2) :=
  fun z => by simp only [neg_neg]; ring

/-- The odd-part quotient $\tfrac{f(z) - f(-z)}{2 \wp'(z)}$ is an elliptic function:
since both the odd part of $f$ and $\wp'$ are odd elliptic functions, their ratio
is an even elliptic function. -/
lemma odd_quot_derivWP_isEllipticFunction {f : ℂ → ℂ} (hf : L.IsEllipticFunction f) :
    L.IsEllipticFunction (fun z => (f z - f (-z)) / 2 / L.derivWeierstrassP z) where
  meromorphic := ((hf.meromorphic.sub (meromorphic_comp_neg hf.meromorphic)).div
    (fun _ => analyticAt_const.meromorphicAt)).div L.meromorphic_derivWeierstrassP
  periodic ω hω z := by
    simp only
    rw [hf.periodic ω hω z,
        latticePeriodic_neg_of_latticePeriodic L hf.periodic ω hω z,
        L.derivWeierstrassP_add_coe z ⟨ω, hω⟩]

/-- The odd-part quotient $\tfrac{f(z) - f(-z)}{2\wp'(z)}$ is an even function. -/
lemma odd_quot_derivWP_isEvenFunction (f : ℂ → ℂ) :
    IsEvenFunction (fun z => (f z - f (-z)) / 2 / L.derivWeierstrassP z) := by
  intro z; simp only [neg_neg]
  rw [L.derivWeierstrassP_neg z]; field_simp; ring

/-- *Even holomorphic elliptic functions are polynomials in $\wp$*: if $f$ is an
even, $L$-periodic, meromorphic function with no poles outside $L$, then $f(z) =
P(\wp(z))$ for some polynomial $P \in \mathbb{C}[X]$. -/
theorem even_holomorphic_elliptic_is_polynomial_in_wp
    (f : ℂ → ℂ)
    (hf_ell : L.IsEllipticFunction f)
    (hf_even : IsEvenFunction f)
    (hf_holo : ∀ z : ℂ, z ∉ (L.lattice : Set ℂ) → DifferentiableAt ℂ f z) :
    ∃ P : ℂ[X], ∀ z : ℂ, f z = P.eval (L.weierstrassP z) := by sorry

/-- *Even elliptic functions are rational functions in $\wp$*: if $f$ is an even
elliptic function, then there exist polynomials $P, Q \in \mathbb{C}[X]$ with
$Q \neq 0$ such that $Q(\wp(z)) f(z) = P(\wp(z))$, i.e.\ $f = P(\wp)/Q(\wp)$. -/
theorem even_ellipticFunctionField_eq_rational_wp
    (f : ℂ → ℂ)
    (hf_ell : L.IsEllipticFunction f)
    (hf_even : IsEvenFunction f) :
    ∃ (P Q : ℂ[X]), Q ≠ 0 ∧
      ∀ z : ℂ, Q.eval (L.weierstrassP z) * f z = P.eval (L.weierstrassP z) := by sorry

/-- At a zero of $\wp'$, the odd part of an elliptic function $f$ vanishes:
if $\wp'(z) = 0$ then $f(z) = f(-z)$.  This is needed for the rational expression
of arbitrary elliptic functions in $\wp$ and $\wp'$. -/
lemma odd_part_vanishes_at_derivWP_zero (f : ℂ → ℂ)
    (hf : L.IsEllipticFunction f) (z : ℂ)
    (h : L.derivWeierstrassP z = 0) :
    f z = f (-z) := by
  have h2z : (2 : ℂ) * z ∈ (L.lattice : Set ℂ) := by
    by_cases hz : z ∈ (L.lattice : Set ℂ)
    · have : (2 : ℂ) * z = z + z := by ring
      rw [this]; exact L.lattice.add_mem hz hz
    · exact (L.derivWeierstrassPFun_eq_zero_iff z hz).mp h
  have hkey : -z + (2 : ℂ) * z = z := by ring
  have hperiod := hf.periodic ((2 : ℂ) * z) h2z (-z)
  rw [hkey] at hperiod
  exact hperiod

/-- *Assembly lemma for Lemma 16.3(i)*: given rational expressions for the even part
of $f$ (via $P_e, Q_e$) and for the odd-part quotient $\tfrac{f - f(-\cdot)}{2\wp'}$
(via $P_o, Q_o$), one assembles a rational expression $f = (Q_o P_e + Q_e P_o
\wp') / (Q_e Q_o)$ in $\wp$ and $\wp'$. -/
theorem lem_16_3_i_assembly (f : ℂ → ℂ)
    (hf : L.IsEllipticFunction f) (Pe Qe Po Qo : ℂ[X])
    (hQe : ∀ z, Qe.eval (L.weierstrassP z) * ((f z + f (-z)) / 2) =
      Pe.eval (L.weierstrassP z))
    (hQo : ∀ z, Qo.eval (L.weierstrassP z) *
      ((f z - f (-z)) / 2 / L.derivWeierstrassP z) =
      Po.eval (L.weierstrassP z)) :
    ∀ z, (Qe * Qo).eval (L.weierstrassP z) * f z =
      (Qo * Pe).eval (L.weierstrassP z) +
      (Qe * Po).eval (L.weierstrassP z) * L.derivWeierstrassP z := by
  intro z
  simp only [Polynomial.eval_mul]
  have heven := hQe z

  have hodd : Qo.eval (L.weierstrassP z) * ((f z - f (-z)) / 2) =
      Po.eval (L.weierstrassP z) * L.derivWeierstrassP z := by
    by_cases hwp : L.derivWeierstrassP z = 0
    ·
      have hfz_eq := odd_part_vanishes_at_derivWP_zero L f hf z hwp
      have hO : f z - f (-z) = 0 := sub_eq_zero.mpr hfz_eq
      have hpo : Po.eval (L.weierstrassP z) = 0 := by
        have h1 := hQo z; simp only [hwp, div_zero, mul_zero] at h1; exact h1.symm
      simp only [hO, zero_div, mul_zero, hpo, zero_mul]
    ·
      have h1 := hQo z


      have key : Qo.eval (L.weierstrassP z) *
          ((f z - f (-z)) / 2 / L.derivWeierstrassP z) *
          L.derivWeierstrassP z =
          Po.eval (L.weierstrassP z) * L.derivWeierstrassP z := by
        rw [h1]
      rw [mul_assoc, div_mul_cancel₀ _ hwp] at key
      exact key

  have hfz : f z = (f z + f (-z)) / 2 + (f z - f (-z)) / 2 := by ring
  have : Qe.eval (L.weierstrassP z) * Qo.eval (L.weierstrassP z) * f z =
      Qo.eval (L.weierstrassP z) * (Qe.eval (L.weierstrassP z) * ((f z + f (-z)) / 2)) +
      Qe.eval (L.weierstrassP z) * (Qo.eval (L.weierstrassP z) * ((f z - f (-z)) / 2)) := by
    rw [hfz]; ring
  rw [this, heven, hodd]; ring

/-- *Theorem*: the field of elliptic functions for $L$ equals $\mathbb{C}(\wp, \wp')$.
Every elliptic function $f$ can be expressed as
$f(z) = (P_1(\wp(z)) + P_2(\wp(z)) \wp'(z)) / Q(\wp(z))$ for polynomials
$P_1, P_2, Q \in \mathbb{C}[X]$ with $Q \neq 0$. -/
theorem ellipticFunctionField_eq_wp_wp'
    (f : ℂ → ℂ) (hf : L.IsEllipticFunction f) :
    ∃ (P₁ P₂ Q : ℂ[X]), Q ≠ 0 ∧
      ∀ z : ℂ, Q.eval (L.weierstrassP z) * f z =
        P₁.eval (L.weierstrassP z) +
        P₂.eval (L.weierstrassP z) * L.derivWeierstrassP z := by

  obtain ⟨Pe, Qe, hQe_ne, hQe_eq⟩ :=
    even_ellipticFunctionField_eq_rational_wp L _
      (even_part_isEllipticFunction L hf) (even_part_isEvenFunction f)

  obtain ⟨Po, Qo, hQo_ne, hQo_eq⟩ :=
    even_ellipticFunctionField_eq_rational_wp L _
      (odd_quot_derivWP_isEllipticFunction L hf) (odd_quot_derivWP_isEvenFunction L f)

  exact ⟨Qo * Pe, Qe * Po, Qe * Qo, mul_ne_zero hQe_ne hQo_ne,
    lem_16_3_i_assembly L f hf Pe Qe Po Qo hQe_eq hQo_eq⟩

end

end ComplexLattice

namespace ComplexLattice

noncomputable section

open Polynomial Pointwise

/-- $\wp_{L_2}(\alpha z)$ is a *rational function in $\wp_{L_1}(z)$*: there exist
polynomials $u, v$ with $v \neq 0$ such that $v(\wp_{L_1}(z)) \wp_{L_2}(\alpha z) =
u(\wp_{L_1}(z))$.  Condition (2) of Theorem 16.4. -/
def IsRationalFunctionInWP (L₁ L₂ : ComplexLattice) (α : ℂ) : Prop :=
  ∃ (u v : ℂ[X]), v ≠ 0 ∧
    ∀ z : ℂ, v.eval (L₁.weierstrassP z) * L₂.weierstrassP (α * z) =
      u.eval (L₁.weierstrassP z)

/-- The "isogeny" associated to $\alpha$ exists at the level of $\wp$-functions
and their derivatives: both $\wp_{L_2}(\alpha z)$ and $\wp'_{L_2}(\alpha z)$ can
be expressed rationally in $\wp_{L_1}$ and $\wp'_{L_1}$.  Condition (3) of
Theorem 16.4. -/
def ExistsUniqueIsogenyFromAlpha (L₁ L₂ : ComplexLattice) (α : ℂ) : Prop :=
  ∃ (u v s t : ℂ[X]), v ≠ 0 ∧ t ≠ 0 ∧
    (∀ z : ℂ, v.eval (L₁.weierstrassP z) * L₂.weierstrassP (α * z) =
      u.eval (L₁.weierstrassP z)) ∧
    (∀ z : ℂ, t.eval (L₁.weierstrassP z) * L₂.derivWeierstrassP (α * z) =
      s.eval (L₁.weierstrassP z) * L₁.derivWeierstrassP z)

/-- Theorem 16.4: (1) $\Rightarrow$ (2).  If $\alpha L_1 \subseteq L_2$, then
$\wp_{L_2}(\alpha z)$ is a rational function in $\wp_{L_1}(z)$. -/
theorem theorem_16_4_one_imp_two (L₁ L₂ : ComplexLattice) (α : ℂ)
    (hα : α ∈ latticeMulSet L₁ L₂) :
    IsRationalFunctionInWP L₁ L₂ α := by sorry

/-- Theorem 16.4: (2) $\Rightarrow$ (3).  If $\wp_{L_2}(\alpha z)$ is rational
in $\wp_{L_1}$, then both $\wp_{L_2}(\alpha z)$ and $\wp'_{L_2}(\alpha z)$ have
the required rational expressions, giving an isogeny. -/
theorem theorem_16_4_two_imp_three (L₁ L₂ : ComplexLattice) (α : ℂ)
    (h : IsRationalFunctionInWP L₁ L₂ α) :
    ExistsUniqueIsogenyFromAlpha L₁ L₂ α := by sorry

/-- Theorem 16.4: (3) $\Rightarrow$ (1).  Existence of the rational isogeny
formulae for $\alpha$ forces $\alpha L_1 \subseteq L_2$. -/
theorem theorem_16_4_three_imp_one (L₁ L₂ : ComplexLattice) (α : ℂ)
    (h : ExistsUniqueIsogenyFromAlpha L₁ L₂ α) :
    α ∈ latticeMulSet L₁ L₂ := by sorry

/-- **Theorem 16.4.**  The following are equivalent: (1) $\alpha L_1 \subseteq L_2$;
(2) $\wp_{L_2}(\alpha z)$ is a rational function in $\wp_{L_1}(z)$; (3) the
unique isogeny induced by $\alpha$ exists (i.e.\ both $\wp_{L_2}(\alpha z)$ and
$\wp'_{L_2}(\alpha z)$ admit rational expressions in $\wp_{L_1}$ and $\wp'_{L_1}$). -/
theorem theorem_16_4 (L₁ L₂ : ComplexLattice) (α : ℂ) :
    ((α ∈ latticeMulSet L₁ L₂) ↔ IsRationalFunctionInWP L₁ L₂ α) ∧
    (IsRationalFunctionInWP L₁ L₂ α ↔ ExistsUniqueIsogenyFromAlpha L₁ L₂ α) ∧
    (ExistsUniqueIsogenyFromAlpha L₁ L₂ α ↔ α ∈ latticeMulSet L₁ L₂) := by
  refine ⟨⟨fun h => theorem_16_4_one_imp_two L₁ L₂ α h,
           fun h2 => theorem_16_4_three_imp_one L₁ L₂ α
             (theorem_16_4_two_imp_three L₁ L₂ α h2)⟩,
          ⟨fun h => theorem_16_4_two_imp_three L₁ L₂ α h,
           fun h3 => theorem_16_4_one_imp_two L₁ L₂ α
             (theorem_16_4_three_imp_one L₁ L₂ α h3)⟩,
          ⟨fun h3 => theorem_16_4_three_imp_one L₁ L₂ α h3,
           fun h1 => theorem_16_4_two_imp_three L₁ L₂ α
             (theorem_16_4_one_imp_two L₁ L₂ α h1)⟩⟩

/-- Degree relation: if $v(\wp_{L_1}(z)) \wp_{L_2}(\alpha z) = u(\wp_{L_1}(z))$
expresses the isogeny induced by $\alpha$, then $\deg u = \deg v + 1$. -/
theorem poleOrder_deg_relation (L₁ L₂ : ComplexLattice) (α : ℂ)
    (hα : α ∈ latticeMulSet L₁ L₂) (hα0 : α ≠ 0)
    (u v : ℂ[X]) (hv : v ≠ 0)
    (h : ∀ z : ℂ, v.eval (L₁.weierstrassP z) * L₂.weierstrassP (α * z) =
      u.eval (L₁.weierstrassP z)) :
    u.natDegree = v.natDegree + 1 := by sorry

/-- For an endomorphism $\alpha$ of a single lattice $L$, the *norm*
$\alpha \overline{\alpha}$ equals the degree $\deg u$ of the rational
$\wp$-expression of the induced isogeny. -/
theorem normSq_eq_natDegree (L : ComplexLattice) (α : ℂ)
    (hα : α ∈ latticeMulSet L L) (hα0 : α ≠ 0)
    (u v : ℂ[X]) (hv : v ≠ 0)
    (h : ∀ z : ℂ, v.eval (L.weierstrassP z) * L.weierstrassP (α * z) =
      u.eval (L.weierstrassP z)) :
    α * starRingEnd ℂ α = ↑(u.natDegree : ℕ) := by sorry

/-- The endomorphism multiplier set $\{\alpha : \alpha L \subseteq L\}$ is
closed under multiplication, mirroring composition of endomorphisms. -/
theorem latticeMulSet_mul_mem (L : ComplexLattice) {α β : ℂ}
    (hα : α ∈ latticeMulSet L L) (hβ : β ∈ latticeMulSet L L) :
    α * β ∈ latticeMulSet L L := by
  intro z hz
  rw [mul_assoc]
  exact hα _ (hβ z hz)

/-- Multiplicativity of the induced map: the endomorphism of $\mathbb{C}/L$
attached to $\alpha \beta$ equals the composition of the endomorphisms attached
to $\alpha$ and $\beta$. -/
theorem inducedMap_mul (L : ComplexLattice) (α β : ℂ)
    (hα : α ∈ latticeMulSet L L) (hβ : β ∈ latticeMulSet L L) :
    ∀ x : torusQuot L,
      inducedMap L L (α * β) (latticeMulSet_mul_mem L hα hβ) x =
        inducedMap L L α hα (inducedMap L L β hβ x) := by
  intro x
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective L.lattice.toAddSubgroup x
  change inducedMap L L (α * β) _ (proj L z) =
    inducedMap L L α hα (inducedMap L L β hβ (proj L z))
  simp only [inducedMap_proj, mul_assoc]

/-- **Corollary 16.5 (ring isomorphism).**  The set
$\{\alpha : \alpha L \subseteq L\}$ with addition and multiplication of complex
numbers is naturally isomorphic to the ring of holomorphic endomorphisms of
$\mathbb{C}/L$: existence and uniqueness from Corollary 16.2 together with
additivity and multiplicativity of the induced maps. -/
theorem corollary_16_5_ring_iso (L : ComplexLattice) :

    (∀ (φ : ComplexTorusHolMap L L), φ.toFun 0 = 0 →
      ∃ α : ℂ, ∃ hα : α ∈ latticeMulSet L L,
        ∀ z : ℂ, φ.toFun (proj L z) = inducedMap L L α hα (proj L z)) ∧

    (∀ (α γ : ℂ) (hα : α ∈ latticeMulSet L L) (hγ : γ ∈ latticeMulSet L L),
      (∀ z : ℂ, inducedMap L L α hα (proj L z) =
                  inducedMap L L γ hγ (proj L z)) → α = γ) ∧

    (∀ (α β : ℂ) (hα : α ∈ latticeMulSet L L) (hβ : β ∈ latticeMulSet L L),
      ∀ x : torusQuot L,
        inducedMap L L (α + β) (latticeMulSet_add_mem L L hα hβ) x =
          inducedMap L L α hα x + inducedMap L L β hβ x) ∧

    (∀ (α β : ℂ) (hα : α ∈ latticeMulSet L L) (hβ : β ∈ latticeMulSet L L),
      ∀ x : torusQuot L,
        inducedMap L L (α * β) (latticeMulSet_mul_mem L hα hβ) x =
          inducedMap L L α hα (inducedMap L L β hβ x)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (corollary_16_2 L L).1
  · exact (corollary_16_2 L L).2.1
  · exact (corollary_16_2 L L).2.2
  · exact fun α β hα hβ => inducedMap_mul L α β hα hβ

/-- The *Rosati involution* on $\mathrm{End}(\mathbb{C}/L)$: for any
endomorphism multiplier $\alpha$, the complex conjugate
$\overline{\alpha}$ is also an endomorphism multiplier. -/
theorem rosatiInvolution_exists (L : ComplexLattice) (α : ℂ)
    (hα : α ∈ latticeMulSet L L) :
    ∃ β : ℂ, β ∈ latticeMulSet L L ∧ β = starRingEnd ℂ α := by sorry

/-- The *dual endomorphism* (Rosati involution) of $\alpha$: an element of the
endomorphism multiplier set realising the complex conjugate $\overline{\alpha}$. -/
noncomputable def dualEndomorphism (L : ComplexLattice) (α : ℂ)
    (hα : α ∈ latticeMulSet L L) : ℂ :=
  Classical.choose (rosatiInvolution_exists L α hα)

/-- The dual endomorphism is the complex conjugate of the original endomorphism. -/
theorem dualEndomorphism_eq_conj (L : ComplexLattice) (α : ℂ)
    (hα : α ∈ latticeMulSet L L) :
    dualEndomorphism L α hα = starRingEnd ℂ α :=
  (Classical.choose_spec (rosatiInvolution_exists L α hα)).2

/-- The *trace* of an endomorphism: $\alpha + \overline{\alpha}$, an integer
(more precisely, a real-integer) by Theorem 12.21. -/
noncomputable def traceEndomorphism (L : ComplexLattice) (α : ℂ)
    (hα : α ∈ latticeMulSet L L) : ℂ :=
  α + dualEndomorphism L α hα

/-- **Corollary 16.5 (involution = conjugation).**  The Rosati involution on the
endomorphism ring of $\mathbb{C}/L$ is exactly complex conjugation. -/
@[simp]
theorem corollary_16_5_involution_conjugation (L : ComplexLattice) (α : ℂ)
    (hα : α ∈ latticeMulSet L L) :
    dualEndomorphism L α hα = starRingEnd ℂ α :=
  dualEndomorphism_eq_conj L α hα

end

end ComplexLattice
