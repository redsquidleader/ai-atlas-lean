/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ArithmeticGeometry.code.AdelePlusFDim

open scoped RestrictedProduct
open FunctionFieldAdeleRing DiscreteValuationFamily

/-- Axiomatized package of genus data for a function field $F/k$ with the chosen structure: a
natural number $g \in \mathbb{N}$ together with the two defining properties of the genus, namely
that the Riemann defect of every divisor is bounded above by $g - 1$ and that this bound is
attained by at least one divisor $D_0$. -/
noncomputable def genus_data_ax
    {F : Type*} [Field F] {P : Type*} [DecidableEq P]
    {O : P → ValuationSubring F}
    (k : Type*) [Field k] [Algebra k F]
    [ConstantField k (F := F) (P := P) (O := O)]
    [FunctionFieldProperty F P O]
    [DiscreteValuationFamily P F k]
    [HasResidueFieldSurjection P F k O] :
    { g : ℕ //
      (∀ (D : P →₀ ℤ), riemannDefect (F := F) (O := O) k D ≤ (g : ℤ) - 1) ∧
      (∃ (D₀ : P →₀ ℤ), riemannDefect (F := F) (O := O) k D₀ = (g : ℤ) - 1) } := by sorry

/-- The genus value extracted from `genus_data_ax`: the unique $g$ such that
$\max_D \mathrm{riemannDefect}(D) = g - 1$. -/
noncomputable def genusVal_ax
    {F : Type*} [Field F] {P : Type*} [DecidableEq P]
    {O : P → ValuationSubring F}
    (k : Type*) [Field k] [Algebra k F]
    [ConstantField k (F := F) (P := P) (O := O)]
    [FunctionFieldProperty F P O]
    [DiscreteValuationFamily P F k]
    [HasResidueFieldSurjection P F k O] : ℕ :=
  (genus_data_ax (F := F) (O := O) k).val

/-- For every divisor $D$, the Riemann defect $r(D)$ is bounded above by $g - 1$, where $g$ is the
genus extracted from `genus_data_ax`. -/
theorem riemannDefect_le_ax
    {F : Type*} [Field F] {P : Type*} [DecidableEq P]
    {O : P → ValuationSubring F}
    (k : Type*) [Field k] [Algebra k F]
    [ConstantField k (F := F) (P := P) (O := O)]
    [FunctionFieldProperty F P O]
    [DiscreteValuationFamily P F k]
    [HasResidueFieldSurjection P F k O]
    (D : P →₀ ℤ) :
    riemannDefect (F := F) (O := O) k D ≤
      (genusVal_ax (F := F) (O := O) k : ℤ) - 1 :=
  (genus_data_ax (F := F) (O := O) k).property.1 D

/-- The genus bound is attained: there exists a divisor $D_0$ with $r(D_0) = g - 1$. -/
theorem genus_attained_ax
    {F : Type*} [Field F] {P : Type*} [DecidableEq P]
    {O : P → ValuationSubring F}
    (k : Type*) [Field k] [Algebra k F]
    [ConstantField k (F := F) (P := P) (O := O)]
    [FunctionFieldProperty F P O]
    [DiscreteValuationFamily P F k]
    [HasResidueFieldSurjection P F k O] :
    ∃ (D₀ : P →₀ ℤ),
      riemannDefect (F := F) (O := O) k D₀ =
        (genusVal_ax (F := F) (O := O) k : ℤ) - 1 :=
  (genus_data_ax (F := F) (O := O) k).property.2

/-- Axiomatized: an element of the valuation subring at $p$ has nonnegative order at $p$. -/
theorem dvf_ord_nonneg_of_mem_valuationSubring
    {F : Type*} [Field F] {P : Type*}
    {O : P → ValuationSubring F}
    (k : Type*) [Field k] [Algebra k F]
    [DiscreteValuationFamily P F k]
    (p : P) (x : F) (hx : x ∈ O p) :
    DiscreteValuationFamily.ord (k := k) p x ≥ (0 : ℤ) := by sorry

/-- A nonzero element of $F$ has finite order at every place $p$. -/
lemma dvf_ord_ne_top_of_ne_zero
    {F : Type*} [Field F] {P : Type*}
    (k : Type*) [Field k] [Algebra k F]
    [DiscreteValuationFamily P F k]
    (p : P) (x : F) (hx : x ≠ 0) :
    DiscreteValuationFamily.ord (k := k) p x ≠ ⊤ := by
  intro h
  have hmul := DiscreteValuationFamily.ord_mul (k := k) p x x⁻¹
  rw [mul_inv_cancel₀ hx] at hmul
  have hone : DiscreteValuationFamily.ord (k := k) p (1 : F) = (0 : ℤ) := by
    have := DiscreteValuationFamily.ord_algebraMap (k := k) (F := F) p (1 : k) one_ne_zero
    rwa [map_one] at this
  rw [hone, h] at hmul
  simp at hmul

/-- For a nonzero $x \in F$, the order $\mathrm{ord}_p(x)$ is given by a (finite) integer. -/
lemma dvf_ord_eq_coe_of_ne_zero
    {F : Type*} [Field F] {P : Type*}
    (k : Type*) [Field k] [Algebra k F]
    [DiscreteValuationFamily P F k]
    (p : P) (x : F) (hx : x ≠ 0) :
    ∃ n : ℤ, DiscreteValuationFamily.ord (k := k) p x = ↑n := by
  cases hv : DiscreteValuationFamily.ord (k := k) p x with
  | top => exact absurd hv (dvf_ord_ne_top_of_ne_zero k p x hx)
  | coe n => exact ⟨n, rfl⟩

/-- Adele covering: any adele $\alpha \in \mathbb{A}_F$ and divisor $D$ admit a divisor $D' \ge D$
such that $\alpha$ lies in the adele subspace $A(D')$. The covering divisor is built from the
component-wise orders of $\alpha$ together with the cofinite vanishing of its negative parts. -/
theorem adele_covering_ax

    {F : Type*} [Field F] {P : Type*} [DecidableEq P]
    {O : P → ValuationSubring F}
    (k : Type*) [Field k] [Algebra k F]
    [ConstantField k (F := F) (P := P) (O := O)]
    [FunctionFieldProperty F P O]
    [DiscreteValuationFamily P F k]
    [HasResidueFieldSurjection P F k O]
    (α : FunctionFieldAdeleRing F P O) (D : P →₀ ℤ) :
    ∃ (D' : P →₀ ℤ), (∀ p, D p ≤ D' p) ∧
      (α : FunctionFieldAdeleRing F P O) ∈
        AF_subspace (F := F) (O := O) k (D' : P → ℤ) := by
  classical

  have h_cofin := FunctionFieldAdeleRing.mem_valuationSubring_cofinitely α


  let ordBound : P → ℤ := fun p =>
    if h : α p = 0 then 0
    else (dvf_ord_eq_coe_of_ne_zero k p (α p) h).choose
  have hordBound : ∀ p, DiscreteValuationFamily.ord (k := k) p (α p) ≥ ↑(ordBound p) := by
    intro p
    simp only [ordBound]
    split_ifs with h
    · rw [h, DiscreteValuationFamily.ord_zero]; exact le_top
    · exact le_of_eq (dvf_ord_eq_coe_of_ne_zero k p (α p) h).choose_spec.symm

  have hordBound_nonneg : ∀ᶠ p in Filter.cofinite, ordBound p ≥ 0 := by
    apply Filter.Eventually.mono h_cofin
    intro p hp
    have h_ord_nonneg := dvf_ord_nonneg_of_mem_valuationSubring k p (α p) hp
    have h_ord_ge := hordBound p
    simp only [ordBound] at h_ord_ge ⊢
    split_ifs with hzero
    · exact le_refl 0
    · have hspec := (dvf_ord_eq_coe_of_ne_zero k p (α p) hzero).choose_spec
      rw [hspec] at h_ord_nonneg
      exact_mod_cast h_ord_nonneg

  let D'fun : P → ℤ := fun p => max (D p) (-ordBound p)
  have hD'_fin_supp : (Function.support D'fun).Finite := by
    have hS1 : (D.support : Set P).Finite := D.support.finite_toSet
    have hS2 : {p : P | ¬(ordBound p ≥ 0)}.Finite := by
      rw [Filter.Eventually, Filter.mem_cofinite] at hordBound_nonneg
      exact hordBound_nonneg
    apply (hS1.union hS2).subset
    intro p hp
    simp only [Function.mem_support, D'fun, ne_eq] at hp
    simp only [Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_setOf_eq]
    by_contra h_neg
    push Not at h_neg
    obtain ⟨hD_zero, hord_nonneg⟩ := h_neg
    have : D'fun p = 0 := by
      simp only [D'fun]
      rw [hD_zero]
      omega
    exact hp this
  let D' : P →₀ ℤ := Finsupp.ofSupportFinite D'fun hD'_fin_supp
  refine ⟨D', ?_, ?_⟩
  ·
    intro p
    simp only [D', Finsupp.ofSupportFinite_coe, D'fun]
    exact le_max_left _ _
  ·

    apply Submodule.mem_sup_left

    intro p
    simp only [D', Finsupp.ofSupportFinite_coe, D'fun]


    have h1 : (↑(-(max (D p) (-ordBound p))) : WithTop ℤ) ≤ ↑(ordBound p) := by
      norm_cast; omega
    exact le_trans h1 (hordBound p)

section Lemma22_10

variable {F : Type*} [Field F] {P : Type*} [DecidableEq P]
  {O : P → ValuationSubring F}
  (k : Type*) [Field k] [Algebra k F]
  [ConstantField k (F := F) (P := P) (O := O)]
  [FunctionFieldProperty F P O]
  [DiscreteValuationFamily P F k]
  [HasResidueFieldSurjection P F k O]

/-- Monotonicity of the Riemann defect: if $D \le D'$ pointwise, then $r(D) \le r(D')$. -/
theorem riemannDefect_mono
    (D D' : P →₀ ℤ) (h : ∀ p, D p ≤ D' p) :
    riemannDefect (F := F) (O := O) k D ≤ riemannDefect (F := F) (O := O) k D' := by
  have h_dim := AF_subspace_dim (F := F) (O := O) k D D' h
  obtain ⟨_, h_dim_eq⟩ := h_dim


  have h_nn : (0 : ℤ) ≤ ↑(Module.finrank k
      (↥(AF_subspace (F := F) (O := O) k ⇑D') ⧸
        Submodule.comap (AF_subspace (F := F) (O := O) k ⇑D').subtype
          (AF_subspace (F := F) (O := O) k ⇑D))) := Int.natCast_nonneg _
  linarith

/-- Restatement of the genus bound `riemannDefect_le_ax` inside the `Lemma22_10` section. -/
theorem riemannDefect_le_of_genus
    (D : P →₀ ℤ) :
    riemannDefect (F := F) (O := O) k D ≤
      (genusVal_ax (F := F) (O := O) k : ℤ) - 1 :=
  riemannDefect_le_ax k D

/-- Convenience restatement of `adele_covering_ax`: every adele is captured by some adele subspace
$A(D')$ with $D' \ge D$. -/
theorem adele_in_AF_of_restricted_product
    (α : FunctionFieldAdeleRing F P O) (D : P →₀ ℤ) :
    ∃ (D' : P →₀ ℤ), (∀ p, D p ≤ D' p) ∧
      (α : FunctionFieldAdeleRing F P O) ∈
        AF_subspace (F := F) (O := O) k (D' : P → ℤ) :=
  adele_covering_ax k α D

/-- Linear-algebra lemma: if $S \le T$ are submodules of $M$ over a division ring with finite
$T/S$ of dimension $0$, then $S = T$. -/
lemma submodule_eq_of_finrank_quotient_zero {R : Type*} [DivisionRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    (S T : Submodule R M) (hST : S ≤ T)
    [hFD : FiniteDimensional R (↥T ⧸ Submodule.comap T.subtype S)]
    (h0 : Module.finrank R (↥T ⧸ Submodule.comap T.subtype S) = 0) :
    S = T := by
  have hforall := finrank_zero_iff_forall_zero.mp h0
  ext x
  constructor
  · exact fun hx => hST hx
  · intro hx
    have := hforall (Submodule.Quotient.mk (⟨x, hx⟩ : T))
    rw [Submodule.Quotient.mk_eq_zero] at this
    rw [Submodule.mem_comap, Submodule.subtype_apply] at this
    exact this

/-- Lemma 22.10: if the Riemann defect of $D$ equals $g - 1$ (i.e. attains the maximum), then the
adele subspace $A(D)$ exhausts the entire adele ring: $A(D) = \mathbb{A}_F$. Equivalently,
$A = A(D) + F$ in the original formulation. The proof combines the covering lemma with the
finite-quotient identification $S = T$ when their quotient has dimension $0$. -/
theorem AF_subspace_eq_top (D : P →₀ ℤ)
    (hrD : riemannDefect (F := F) (O := O) k D =
      (genusVal_ax (F := F) (O := O) k : ℤ) - 1) :
    AF_subspace (F := F) (O := O) k (D : P → ℤ) = ⊤ := by
  ext α
  simp only [Submodule.mem_top, iff_true]

  obtain ⟨D', hD'_ge, hα_mem⟩ :=
    adele_in_AF_of_restricted_product (F := F) (O := O) k α D

  have hrD' : riemannDefect (F := F) (O := O) k D' =
      (genusVal_ax (F := F) (O := O) k : ℤ) - 1 := by
    have h_le := riemannDefect_le_of_genus (F := F) (O := O) k D'
    have h_mono : riemannDefect (F := F) (O := O) k D ≤
        riemannDefect (F := F) (O := O) k D' :=
      riemannDefect_mono k D D' hD'_ge
    linarith

  have h_dim := AF_subspace_dim (F := F) (O := O) k D D' hD'_ge
  obtain ⟨hFD, h_dim_eq⟩ := h_dim
  haveI := hFD

  have h_dim_zero : (Module.finrank k
      (↥(AF_subspace (F := F) (O := O) k (D' : P → ℤ)) ⧸
        Submodule.comap
          (AF_subspace (F := F) (O := O) k (D' : P → ℤ)).subtype
          (AF_subspace (F := F) (O := O) k (D : P → ℤ))) : ℤ) = 0 := by
    linarith
  have h_dim_zero_nat : Module.finrank k
      (↥(AF_subspace (F := F) (O := O) k (D' : P → ℤ)) ⧸
        Submodule.comap
          (AF_subspace (F := F) (O := O) k (D' : P → ℤ)).subtype
          (AF_subspace (F := F) (O := O) k (D : P → ℤ))) = 0 := by
    exact_mod_cast h_dim_zero

  have h_eq : AF_subspace (F := F) (O := O) k (D : P → ℤ) =
      AF_subspace (F := F) (O := O) k (D' : P → ℤ) :=
    submodule_eq_of_finrank_quotient_zero _ _
      (AF_subspace_mono k hD'_ge) h_dim_zero_nat

  rw [h_eq]
  exact hα_mem

end Lemma22_10
