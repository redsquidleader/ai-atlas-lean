/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.ChevalleyRestriction
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.RingTheory.Adjoin.Tower
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Polynomial.Subring
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.GoingUp

set_option linter.unusedSectionVars false

noncomputable section

open MvPolynomial Finset

section ReynoldsOperator

variable {k : Type*} [Field k] [CharZero k]
  {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))

def reynoldsOperator :
    MvPolynomial ι k →ₗ[k] MvPolynomial ι k where
  toFun h := (Fintype.card G : k)⁻¹ • Finset.univ.sum fun g => (algAct g) h
  map_add' x y := by
    simp only [map_add, Finset.sum_add_distrib, smul_add]
  map_smul' r x := by
    simp only [map_smul, Finset.smul_sum, smul_comm r, RingHom.id_apply]

theorem reynolds_maps_to_invariants
    (h : MvPolynomial ι k) :
    reynoldsOperator algAct h ∈ polynomialInvariantSubalgebra k G ι algAct := by

  intro g₀
  simp only [reynoldsOperator, LinearMap.coe_mk, AddHom.coe_mk]
  rw [map_smul (algAct g₀ : MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k)]
  congr 1
  rw [map_sum]

  apply Finset.sum_equiv (Equiv.mulLeft g₀)
  · intro g; simp
  · intro g _
    show (algAct g₀) ((algAct g) h) = (algAct (g₀ * g)) h
    rw [map_mul]
    rfl

theorem reynolds_identity_on_invariants
    (h : MvPolynomial ι k)
    (hh : h ∈ polynomialInvariantSubalgebra k G ι algAct) :
    reynoldsOperator algAct h = h := by

  simp only [reynoldsOperator, LinearMap.coe_mk, AddHom.coe_mk]

  have : Finset.univ.sum (fun g => (algAct g) h) = (Fintype.card G : k) • h := by
    rw [Finset.sum_congr rfl (fun g _ => hh g)]
    rw [Finset.sum_const, Finset.card_univ]
    simp [Algebra.smul_def]
  rw [this]
  rw [smul_smul]
  rw [inv_mul_cancel₀]
  · simp
  · exact Nat.cast_ne_zero.mpr (Fintype.card_pos.ne')

end ReynoldsOperator

section Lemma11_1

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))

def positiveInvariantIdeal :
    Ideal (MvPolynomial ι k) :=
  Ideal.span {f | f ∈ polynomialInvariantSubalgebra k G ι algAct ∧
    f ≠ 0 ∧ MvPolynomial.totalDegree f > 0}

lemma reynolds_mul_invariant
    {k : Type*} [Field k] [CharZero k]
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (h f : MvPolynomial ι k)
    (hf : f ∈ polynomialInvariantSubalgebra k G ι algAct) :
    reynoldsOperator algAct (h * f) = reynoldsOperator algAct h * f := by
  simp only [reynoldsOperator, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.smul_sum, Finset.smul_sum, Finset.sum_mul]
  congr 1
  funext g
  simp only [Algebra.smul_mul_assoc]
  congr 1
  rw [map_mul, hf g]

theorem invariant_subalgebra_generated_by_ideal_generators
    (r : ℕ) (f : Fin r → MvPolynomial ι k)
    (hf_inv : ∀ i, f i ∈ polynomialInvariantSubalgebra k G ι algAct)
    (hf_gen : positiveInvariantIdeal algAct = Ideal.span (Set.range f))


    (hf_pos : ∀ i, 0 < (f i).totalDegree)
    (h_deg_pres : ∀ (g : G) (p : MvPolynomial ι k),
        ((algAct g) p).totalDegree ≤ p.totalDegree)
    (h_coeff_deg : ∀ (q : MvPolynomial ι k), q ∈ Ideal.span (Set.range f) → q ≠ 0 →
        ∃ (s : Fin r → MvPolynomial ι k),
          q = ∑ i, s i * f i ∧
          ∀ i, s i ≠ 0 → (s i).totalDegree + (f i).totalDegree ≤ q.totalDegree) :
    polynomialInvariantSubalgebra k G ι algAct =
      Algebra.adjoin k (Set.range f) := by
  apply le_antisymm
  ·

    intro p hp

    suffices key : ∀ n, ∀ q : MvPolynomial ι k,
        q ∈ polynomialInvariantSubalgebra k G ι algAct →
        q.totalDegree = n →
        q ∈ Algebra.adjoin k (Set.range f) by
      exact key p.totalDegree p hp rfl
    intro n
    induction n using Nat.strongRecOn with
    | _ n ih =>
    intro q hq hq_deg
    by_cases h0 : n = 0
    ·
      subst h0
      have : q = MvPolynomial.C (MvPolynomial.coeff 0 q) := by
        ext a
        simp only [MvPolynomial.coeff_C]
        split_ifs with ha
        · subst ha; rfl
        · have hsup := (MvPolynomial.totalDegree_eq_zero_iff ι q).mp hq_deg
          rw [MvPolynomial.notMem_support_iff.mp]
          intro hmem
          exact ha (Finsupp.ext (fun x => by
            simp [Finsupp.zero_apply]
            have := hsup a hmem x
            omega))
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
    ·
      have hq_pos : q.totalDegree > 0 := by omega

      have hq_ne : q ≠ 0 := by
        intro heq; subst heq; simp at hq_pos
      have hq_in_I : q ∈ positiveInvariantIdeal algAct := by
        rw [positiveInvariantIdeal]
        exact Ideal.subset_span ⟨hq, hq_ne, hq_pos⟩

      have hq_in_span : q ∈ Ideal.span (Set.range f) := hf_gen ▸ hq_in_I

      obtain ⟨s, hs, hs_deg⟩ := h_coeff_deg q hq_in_span hq_ne


      let a : Fin r → MvPolynomial ι k := fun i => reynoldsOperator algAct (s i)
      have ha_inv : ∀ i, a i ∈ polynomialInvariantSubalgebra k G ι algAct :=
        fun i => reynolds_maps_to_invariants algAct (s i)
      have ha_eq : q = ∑ i : Fin r, a i * f i := by
        have h1 : reynoldsOperator algAct q = q :=
          reynolds_identity_on_invariants algAct q hq
        rw [← h1, hs]
        simp only [map_sum, a]
        congr 1
        funext i
        exact reynolds_mul_invariant algAct (s i) (f i) (hf_inv i)


      have reynolds_deg_le : ∀ (p : MvPolynomial ι k),
          (reynoldsOperator algAct p).totalDegree ≤ p.totalDegree := by
        intro p₀
        show ((Fintype.card G : k)⁻¹ • Finset.univ.sum fun g => (algAct g) p₀).totalDegree
            ≤ p₀.totalDegree
        calc ((Fintype.card G : k)⁻¹ • Finset.univ.sum fun g => (algAct g) p₀).totalDegree
            ≤ (Finset.univ.sum fun g => (algAct g) p₀).totalDegree := by
              exact MvPolynomial.totalDegree_smul_le _ _
          _ ≤ p₀.totalDegree := by
              apply MvPolynomial.totalDegree_finsetSum_le
              intro g _
              exact h_deg_pres g p₀
      have ha_deg : ∀ i, (a i).totalDegree < q.totalDegree := by
        intro i
        by_cases hsi : s i = 0
        ·
          show (reynoldsOperator algAct (s i)).totalDegree < q.totalDegree
          rw [hsi, map_zero]
          exact hq_pos
        ·
          have h_bound := hs_deg i hsi
          have h_si_lt : (s i).totalDegree < q.totalDegree := by
            have := hf_pos i
            omega
          exact lt_of_le_of_lt (reynolds_deg_le (s i)) h_si_lt

      rw [ha_eq]
      apply Subalgebra.sum_mem
      intro i _
      apply Subalgebra.mul_mem
      ·
        exact ih (a i).totalDegree (hq_deg ▸ ha_deg i) (a i) (ha_inv i) rfl
      ·
        exact Algebra.subset_adjoin ⟨i, rfl⟩
  ·
    rw [Algebra.adjoin_le_iff]
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    exact hf_inv i

def normPoly (x : MvPolynomial ι k) : Polynomial (MvPolynomial ι k) :=
  Finset.univ.prod (fun g : G => Polynomial.X - Polynomial.C ((algAct g) x))

lemma normPoly_eval_self (x : MvPolynomial ι k) :
    Polynomial.eval x (normPoly algAct x) = 0 := by
  simp only [normPoly, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C]
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : G))
  simp [map_one]

lemma normPoly_monic (x : MvPolynomial ι k) :
    (normPoly algAct x).Monic := by
  simp only [normPoly]
  exact Polynomial.monic_prod_of_monic _ _ (fun g _ => Polynomial.monic_X_sub_C _)

lemma normPoly_coeff_invariant (x : MvPolynomial ι k) (n : ℕ) (h : G) :
    (algAct h) ((normPoly algAct x).coeff n) = (normPoly algAct x).coeff n := by
  suffices key : Polynomial.map (algAct h : MvPolynomial ι k →+* MvPolynomial ι k)
      (normPoly algAct x) = normPoly algAct x by
    have := congr_arg (fun p => Polynomial.coeff p n) key
    simp [Polynomial.coeff_map] at this
    exact this
  simp only [normPoly]
  rw [Polynomial.map_prod]
  apply Finset.prod_equiv (Equiv.mulLeft h)
  · intro g; simp
  · intro g _
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    congr 1
    congr 1
    show (algAct h) ((algAct g) x) = (algAct (h * g)) x
    rw [map_mul]; rfl

lemma normPoly_coeffs_subset (x : MvPolynomial ι k) :
    (↑(normPoly algAct x).coeffs : Set (MvPolynomial ι k)) ⊆
      (polynomialInvariantSubalgebra k G ι algAct).toSubring := by
  intro c hc
  rw [Polynomial.coeffs] at hc
  simp only [Finset.coe_image, Set.mem_image] at hc
  obtain ⟨n, _, rfl⟩ := hc
  intro g
  exact normPoly_coeff_invariant algAct x n g

lemma isIntegral_over_invariants (x : MvPolynomial ι k) :
    IsIntegral (polynomialInvariantSubalgebra k G ι algAct) x := by
  let SR := (polynomialInvariantSubalgebra k G ι algAct).toSubring
  let p_sub := (normPoly algAct x).toSubring SR (normPoly_coeffs_subset algAct x)
  refine ⟨p_sub, ?_, ?_⟩
  · rw [Polynomial.monic_toSubring]
    exact normPoly_monic algAct x
  · rw [Polynomial.eval₂_eq_eval_map]
    have h_eq_map : Polynomial.map (algebraMap ↥(polynomialInvariantSubalgebra k G ι algAct)
        (MvPolynomial ι k)) p_sub = normPoly algAct x := by
      have h1 := Polynomial.map_toSubring (normPoly algAct x) SR (normPoly_coeffs_subset algAct x)
      convert h1 using 1
    rw [h_eq_map]
    exact normPoly_eval_self algAct x

theorem invariant_subalgebra_fg :
    (polynomialInvariantSubalgebra k G ι algAct).FG := by

  have h_int : Algebra.IsIntegral (polynomialInvariantSubalgebra k G ι algAct) (MvPolynomial ι k) :=
    ⟨fun x => isIntegral_over_invariants algAct x⟩


  have h_ft : Algebra.FiniteType (↥(polynomialInvariantSubalgebra k G ι algAct)) (MvPolynomial ι k) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _

  have h_mf : Module.Finite (↥(polynomialInvariantSubalgebra k G ι algAct)) (MvPolynomial ι k) :=
    @Algebra.IsIntegral.finite _ _ _ _ _ h_int h_ft

  rw [← Subalgebra.fg_top]
  exact fg_of_fg_of_fg (A := k) (B := ↥(polynomialInvariantSubalgebra k G ι algAct))
    (C := MvPolynomial ι k)
    (Algebra.FiniteType.out (R := k) (A := MvPolynomial ι k))
    (Module.finite_def.mp h_mf)
    Subtype.val_injective

end Lemma11_1

section Remark11_2

theorem hilbert_noether_lemma
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {A : Type*} [CommRing A] [Algebra k A]
    {G : Type*} [Group G] [Fintype G]
    (algAct : G →* (A ≃ₐ[k] A))
    (hA_fg : Subalgebra.FG (⊤ : Subalgebra k A)) :
    (Subalgebra.invariants G algAct).FG := by


  let S := Subalgebra.invariants G algAct


  have h_int : Algebra.IsIntegral S A := by
    constructor
    intro x

    let p := Finset.univ.prod (fun g : G => Polynomial.X - Polynomial.C ((algAct g) x))

    have hp_monic : p.Monic :=
      Polynomial.monic_prod_of_monic _ _ (fun g _ => Polynomial.monic_X_sub_C _)

    have hp_eval : Polynomial.eval x p = 0 := by
      simp only [p, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      apply Finset.prod_eq_zero (Finset.mem_univ (1 : G))
      simp [map_one]

    have hp_coeff_inv : ∀ n h_g, (algAct h_g) (p.coeff n) = p.coeff n := by
      intro n h_g
      suffices key : Polynomial.map (algAct h_g : A →+* A) p = p by
        have := congr_arg (fun q => Polynomial.coeff q n) key
        simp [Polynomial.coeff_map] at this
        exact this
      simp only [p]
      rw [Polynomial.map_prod]
      apply Finset.prod_equiv (Equiv.mulLeft h_g)
      · intro g; simp
      · intro g _
        simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
        congr 1; congr 1
        show (algAct h_g) ((algAct g) x) = (algAct (h_g * g)) x
        rw [map_mul]; rfl

    have hp_coeffs_sub : (↑p.coeffs : Set A) ⊆ S.toSubring := by
      intro c hc
      rw [Polynomial.coeffs] at hc
      simp only [Finset.coe_image, Set.mem_image] at hc
      obtain ⟨n, _, rfl⟩ := hc
      intro g
      exact hp_coeff_inv n g
    let p_sub := p.toSubring S.toSubring hp_coeffs_sub
    exact ⟨p_sub, by rw [Polynomial.monic_toSubring]; exact hp_monic,
      by rw [Polynomial.eval₂_eq_eval_map]
         have h_eq : Polynomial.map (algebraMap ↥S A) p_sub = p := by
           have h1 := Polynomial.map_toSubring p S.toSubring hp_coeffs_sub
           convert h1 using 1
         rw [h_eq]; exact hp_eval⟩

  haveI : Algebra.FiniteType k A := ⟨hA_fg⟩
  have h_ft : Algebra.FiniteType S A :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _

  have h_mf : Module.Finite S A := Algebra.IsIntegral.finite

  rw [← Subalgebra.fg_top]
  exact fg_of_fg_of_fg (A := k) (B := ↥S) (C := A)
    hA_fg
    (Module.finite_def.mp h_mf)
    Subtype.val_injective

end Remark11_2

section Lemma11_3

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (ρ : G →* V ≃ₗ[k] V)
  (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))

lemma reynolds_diff_of_groupDiff_mem
    {k : Type*} [Field k] [CharZero k]
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (p : MvPolynomial ι k)
    (I : Ideal (MvPolynomial ι k))
    (h_all : ∀ w : G, (algAct w) p - p ∈ I) :
    reynoldsOperator algAct p - p ∈ I := by

  simp only [reynoldsOperator, LinearMap.coe_mk, AddHom.coe_mk]

  have hG_ne : (Fintype.card G : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_pos.ne')


  suffices h : (Fintype.card G : k)⁻¹ •
      (Finset.univ.sum fun w => ((algAct w) p - p)) ∈ I by
    convert h using 1
    have hsum : Finset.univ.sum (fun g => (algAct g) p) =
        Finset.univ.sum (fun g => ((algAct g) p - p)) +
        Finset.univ.sum (fun _ : G => p) := by
      rw [← Finset.sum_add_distrib]
      congr 1; ext g; ring
    rw [hsum, smul_add]
    have hconst : (Fintype.card G : k)⁻¹ • Finset.univ.sum (fun _ : G => p) = p := by
      rw [Finset.sum_const, Finset.card_univ]
      rw [← Nat.cast_smul_eq_nsmul k (Fintype.card G) p]
      rw [smul_smul, inv_mul_cancel₀ hG_ne, one_smul]
    rw [hconst]
    ring
  rw [Algebra.smul_def, MvPolynomial.algebraMap_eq]
  exact Ideal.mul_mem_left I _ (I.sum_mem (fun w _ => h_all w))

lemma positiveInvariantIdeal_stable
    {k : Type*} [Field k]
    {G : Type*} [Group G]
    {ι : Type*}
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (w : G) (f : MvPolynomial ι k)
    (hf : f ∈ positiveInvariantIdeal algAct) :
    (algAct w) f ∈ positiveInvariantIdeal algAct := by
  have hmem : Ideal.map (algAct w).toAlgHom.toRingHom (positiveInvariantIdeal algAct) ≤
      positiveInvariantIdeal algAct := by
    rw [positiveInvariantIdeal, Ideal.map_span, Ideal.span_le]
    intro x ⟨y, hy, hyx⟩
    have hinv : y ∈ polynomialInvariantSubalgebra k G ι algAct := hy.1
    have heq : (algAct w) y = y := hinv w
    subst hyx
    rw [show (↑(algAct w).toAlgHom.toRingHom : MvPolynomial ι k → MvPolynomial ι k) y =
        (algAct w) y from rfl, heq]
    exact Ideal.subset_span hy
  exact hmem (Ideal.mem_map_of_mem _ hf)

lemma list_prod_diff_mem_ideal
    {k : Type*} [Field k]
    {G : Type*} [Group G]
    {ι : Type*}
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (I : Ideal (MvPolynomial ι k))
    (hstable : ∀ (w : G) (f : MvPolynomial ι k), f ∈ I → (algAct w) f ∈ I)
    (p : MvPolynomial ι k)
    (L : List G)
    (hL : ∀ g ∈ L, (algAct g) p - p ∈ I) :
    (algAct L.prod) p - p ∈ I := by
  induction L with
  | nil => simp [map_one]
  | cons σ rest ih =>
    have hσ : (algAct σ) p - p ∈ I := hL σ List.mem_cons_self
    have hrest : (algAct rest.prod) p - p ∈ I :=
      ih (fun g hg => hL g (List.mem_cons_of_mem _ hg))
    simp only [List.prod_cons]
    have key : (algAct (σ * rest.prod)) p - p =
        (algAct σ) ((algAct rest.prod) p - p) + ((algAct σ) p - p) := by
      simp only [map_mul, AlgEquiv.mul_apply, map_sub]
      ring
    rw [key]
    exact I.add_mem (hstable σ _ hrest) hσ

lemma algHom_sub_dvd_of_X_dvd
    {ι : Type*} [Fintype ι] [DecidableEq ι] {k : Type*} [CommRing k]
    (φ : MvPolynomial ι k →ₐ[k] MvPolynomial ι k)
    (α : MvPolynomial ι k)
    (hX : ∀ i : ι, α ∣ (φ (MvPolynomial.X i) - MvPolynomial.X i))
    (p : MvPolynomial ι k) :
    α ∣ (φ p - p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q ihp ihq =>
    have : φ p + φ q - (p + q) = (φ p - p) + (φ q - q) := by ring
    rw [map_add, this]; exact dvd_add ihp ihq
  | mul_X p i ih =>
    have key : φ (p * MvPolynomial.X i) - p * MvPolynomial.X i =
        φ p * (φ (MvPolynomial.X i) - MvPolynomial.X i) +
        (φ p - p) * MvPolynomial.X i := by
      simp only [map_mul]; ring
    rw [key]; exact dvd_add ((hX i).mul_left _) (ih.mul_right _)

theorem reflection_hyperplane_linear_form
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : G →* V ≃ₗ[k] V)
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (σ : G) (hσ : IsComplexReflection (ρ σ)) :
    ∃ (α : MvPolynomial ι k),
      α ≠ 0 ∧ α.IsHomogeneous 1 ∧ α.totalDegree = 1 ∧
      (∀ i : ι, α ∣ ((algAct σ) (MvPolynomial.X i) - MvPolynomial.X i)) ∧
      (∀ i : ι, ∀ d, (MvPolynomial.X i : MvPolynomial ι k).IsHomogeneous d →
        ∀ q, (algAct σ) (MvPolynomial.X i) - MvPolynomial.X i = q * α →
        q.IsHomogeneous (d - 1)) ∧
      (∀ (p : MvPolynomial ι k) (d : ℕ), p.IsHomogeneous d →
        ∀ q, (algAct σ) p - p = q * α → q.IsHomogeneous (d - 1)) := by sorry

theorem reflection_hyperplane_divisibility
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : G →* V ≃ₗ[k] V)
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (σ : G) (hσ : IsComplexReflection (ρ σ)) :
    ∃ (α : MvPolynomial ι k),
      α ≠ 0 ∧ α.IsHomogeneous 1 ∧ α.totalDegree = 1 ∧
      ∀ (p : MvPolynomial ι k), ∃ (q : MvPolynomial ι k),
        (algAct σ) p - p = q * α ∧
        (∀ d, p.IsHomogeneous d → q.IsHomogeneous (d - 1)) := by
  obtain ⟨α, hα_ne, hα_homog, hα_deg, hα_divX, _, hα_homog_q⟩ :=
    reflection_hyperplane_linear_form ρ algAct σ hσ
  refine ⟨α, hα_ne, hα_homog, hα_deg, fun p => ?_⟩

  have hdvd := algHom_sub_dvd_of_X_dvd (algAct σ).toAlgHom α hα_divX p
  obtain ⟨q, hq⟩ := hdvd
  have heq : (algAct σ) p - p = q * α := by
    show (algAct σ).toAlgHom p - p = q * α
    rw [hq, mul_comm]
  refine ⟨q, heq, fun d hd => ?_⟩
  exact hα_homog_q p d hd q heq

theorem reflection_divisibility_quotients
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : G →* V ≃ₗ[k] V)
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (m : ℕ) (hm_pos : 0 < m)
    (F : Fin m → MvPolynomial ι k) (g : Fin m → MvPolynomial ι k)
    (hF_inv : ∀ i, F i ∈ polynomialInvariantSubalgebra k G ι algAct)
    (_hF_homog : ∀ i, ∃ d, (F i).IsHomogeneous d)
    (hg_homog : ∀ i, ∃ d, (g i).IsHomogeneous d)
    (h_relation : Finset.univ.sum (fun i => g i * F i) = 0)
    (σ : G) (hσ : IsComplexReflection (ρ σ)) :
    ∃ (h : Fin m → MvPolynomial ι k),

      Finset.univ.sum (fun i => h i * F i) = 0 ∧

      (∀ i, ∃ d, (h i).IsHomogeneous d) ∧


      (∀ i, g i ≠ 0 → (g i).totalDegree ≥ 1 → (h i).totalDegree + 1 ≤ (g i).totalDegree) ∧

      (h ⟨0, hm_pos⟩ ∈ positiveInvariantIdeal algAct →
        (algAct σ) (g ⟨0, hm_pos⟩) - g ⟨0, hm_pos⟩ ∈ positiveInvariantIdeal algAct) ∧

      (g ⟨0, hm_pos⟩ = 0 →
        (algAct σ) (g ⟨0, hm_pos⟩) - g ⟨0, hm_pos⟩ ∈ positiveInvariantIdeal algAct) := by

  obtain ⟨α, hα_ne, hα_homog, hα_deg, hα_div⟩ :=
    reflection_hyperplane_divisibility ρ algAct σ hσ

  choose q hq_eq hq_homog using fun i => hα_div (g i)

  refine ⟨q, ?_, ?_, ?_, ?_, ?_⟩
  ·

    have h_sigma_rel : Finset.univ.sum (fun i => ((algAct σ) (g i) - g i) * F i) = 0 := by
      have h_sigma_sum : Finset.univ.sum (fun i => (algAct σ) (g i) * F i) = 0 := by
        have := congr_arg (algAct σ) h_relation
        simp only [map_sum, map_mul, map_zero] at this
        convert this using 1
        congr 1; funext i
        rw [show (algAct σ) (F i) = F i from hF_inv i σ]
      have : Finset.univ.sum (fun i => ((algAct σ) (g i) - g i) * F i) =
          Finset.univ.sum (fun i => (algAct σ) (g i) * F i) -
          Finset.univ.sum (fun i => g i * F i) := by
        simp only [sub_mul]
        rw [Finset.sum_sub_distrib]
      rw [this, h_sigma_sum, h_relation, sub_self]

    have h_rewrite : Finset.univ.sum (fun i => ((algAct σ) (g i) - g i) * F i) =
        α * Finset.univ.sum (fun i => q i * F i) := by
      rw [Finset.mul_sum]
      congr 1; funext i
      rw [hq_eq i]; ring
    rw [h_rewrite] at h_sigma_rel
    exact (mul_eq_zero.mp h_sigma_rel).resolve_left hα_ne
  ·
    intro i
    obtain ⟨d, hd⟩ := hg_homog i
    exact ⟨d - 1, hq_homog i d hd⟩
  ·
    intro i hgi_ne hgi_deg
    obtain ⟨d, hd⟩ := hg_homog i
    have hd_pos : d ≥ 1 := by
      rwa [hd.totalDegree hgi_ne] at hgi_deg
    have hqi_homog := hq_homog i d hd
    by_cases hqi_ne : q i = 0
    · rw [hqi_ne, MvPolynomial.totalDegree_zero]
      rw [hd.totalDegree hgi_ne]
      omega
    · rw [hqi_homog.totalDegree hqi_ne, hd.totalDegree hgi_ne]
      omega
  ·
    intro h_mem

    rw [hq_eq ⟨0, hm_pos⟩]
    exact Ideal.mul_mem_right α _ h_mem
  ·
    intro h0
    rw [h0, map_zero, sub_self]
    exact Ideal.zero_mem _

lemma reynolds_invariant_pos_deg_mem_positiveInvariantIdeal
    (_hG : IsComplexReflectionGroup G ρ)
    (m : ℕ) (hm_pos : 0 < m)
    (F : Fin m → MvPolynomial ι k) (g : Fin m → MvPolynomial ι k)
    (hF_inv : ∀ i, F i ∈ polynomialInvariantSubalgebra k G ι algAct)
    (_hF_homog : ∀ i, ∃ d, (F i).IsHomogeneous d)
    (_hg_homog : ∀ i, ∃ d, (g i).IsHomogeneous d)
    (hF1_not_in_invG :
      ¬ ∃ (c : {j : Fin m // j ≠ ⟨0, hm_pos⟩} → MvPolynomial ι k),
        (∀ i, c i ∈ polynomialInvariantSubalgebra k G ι algAct) ∧
        F ⟨0, hm_pos⟩ = ∑ i : {j : Fin m // j ≠ ⟨0, hm_pos⟩}, c i * F i.val)
    (h_relation : Finset.univ.sum (fun i => g i * F i) = 0) :
    reynoldsOperator algAct (g ⟨0, hm_pos⟩) ∈ positiveInvariantIdeal algAct := by
  set R := reynoldsOperator algAct (g ⟨0, hm_pos⟩) with hR_def

  have hR_inv : R ∈ polynomialInvariantSubalgebra k G ι algAct :=
    reynolds_maps_to_invariants algAct (g ⟨0, hm_pos⟩)

  by_cases h0 : R = 0
  · rw [h0]; exact Ideal.zero_mem _

  · by_cases hdeg : R.totalDegree > 0
    ·
      exact Ideal.subset_span ⟨hR_inv, h0, hdeg⟩
    ·


      exfalso
      push Not at hdeg
      have hdeg0 : R.totalDegree = 0 := Nat.le_zero.mp hdeg

      have hR_const : ∃ r : k, r ≠ 0 ∧ R = MvPolynomial.C r := by
        rw [MvPolynomial.totalDegree_eq_zero_iff] at hdeg0
        refine ⟨MvPolynomial.coeff 0 R, ?_, ?_⟩
        · intro hr0
          apply h0
          ext a
          by_cases ha : a = 0
          · subst ha; simp [hr0]
          · simp only [MvPolynomial.coeff_zero]
            exact MvPolynomial.notMem_support_iff.mp (fun hmem =>
              ha (Finsupp.ext (fun x => by
                simp [Finsupp.zero_apply]
                have := hdeg0 a hmem x
                omega)))
        · ext a
          simp only [MvPolynomial.coeff_C]
          split_ifs with ha
          · subst ha; rfl
          · exact MvPolynomial.notMem_support_iff.mp (fun hmem =>
              ha (Finsupp.ext (fun x => by
                simp [Finsupp.zero_apply]
                have := hdeg0 a hmem x
                omega)))
      obtain ⟨r, hr_ne, hR_eq⟩ := hR_const

      have h_avg_rel : ∑ i : Fin m, reynoldsOperator algAct (g i) * F i = 0 := by
        have h1 : reynoldsOperator algAct (∑ i : Fin m, g i * F i) = 0 := by
          rw [h_relation]; simp [map_zero]
        rw [map_sum] at h1
        convert h1 using 1
        congr 1; funext i
        exact (reynolds_mul_invariant algAct (g i) (F i) (hF_inv i)).symm

      have h_split : R * F ⟨0, hm_pos⟩ +
          ∑ j : {j : Fin m // j ≠ ⟨0, hm_pos⟩},
            reynoldsOperator algAct (g j.val) * F j.val = 0 := by
        have := h_avg_rel
        rw [Fintype.sum_eq_add_sum_subtype_ne _ ⟨0, hm_pos⟩] at this
        exact this

      have h_F1 : MvPolynomial.C r * F ⟨0, hm_pos⟩ =
          -(∑ j : {j : Fin m // j ≠ ⟨0, hm_pos⟩},
            reynoldsOperator algAct (g j.val) * F j.val) := by
        have h_split' := h_split
        rw [hR_eq] at h_split'
        rw [add_eq_zero_iff_eq_neg] at h_split'
        exact h_split'

      apply hF1_not_in_invG
      refine ⟨fun j => -(MvPolynomial.C r⁻¹) * reynoldsOperator algAct (g j.val), ?_, ?_⟩
      ·
        intro j
        apply (polynomialInvariantSubalgebra k G ι algAct).mul_mem
        · apply (polynomialInvariantSubalgebra k G ι algAct).neg_mem

          show ∀ g₀ : G, (algAct g₀) (MvPolynomial.C r⁻¹) = MvPolynomial.C r⁻¹
          intro g₀; exact AlgEquiv.commutes (algAct g₀) r⁻¹
        · exact reynolds_maps_to_invariants algAct (g j.val)
      ·
        have hC_ne : (MvPolynomial.C r : MvPolynomial ι k) ≠ 0 := by
          intro h
          apply hr_ne
          rw [← map_zero (MvPolynomial.C (R := k) (σ := ι))] at h
          exact MvPolynomial.C_injective ι k h
        have key : F ⟨0, hm_pos⟩ = MvPolynomial.C r⁻¹ *
            (-(∑ j : {j : Fin m // j ≠ ⟨0, hm_pos⟩},
            reynoldsOperator algAct (g j.val) * F j.val)) := by
          have h2 : MvPolynomial.C r * F ⟨0, hm_pos⟩ = MvPolynomial.C r *
              (MvPolynomial.C r⁻¹ * (-(∑ j : {j : Fin m // j ≠ ⟨0, hm_pos⟩},
              reynoldsOperator algAct (g j.val) * F j.val))) := by
            rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hr_ne, map_one, one_mul]
            exact h_F1
          exact mul_left_cancel₀ hC_ne h2
        rw [key]
        simp only [mul_neg, Finset.mul_sum, neg_mul, mul_assoc]
        simp only [Finset.sum_neg_distrib]

lemma reflection_single_diff_mem
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : G →* V ≃ₗ[k] V)
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (_hG : IsComplexReflectionGroup G ρ)

    (m : ℕ) (hm_pos : 0 < m)
    (F : Fin m → MvPolynomial ι k) (g : Fin m → MvPolynomial ι k)
    (hF_inv : ∀ i, F i ∈ polynomialInvariantSubalgebra k G ι algAct)
    (hF_homog : ∀ i, ∃ d, (F i).IsHomogeneous d)
    (hg_homog : ∀ i, ∃ d, (g i).IsHomogeneous d)
    (_hF1_not_in_invG :

      ¬ ∃ (c : {j : Fin m // j ≠ ⟨0, hm_pos⟩} → MvPolynomial ι k),
        (∀ i, c i ∈ polynomialInvariantSubalgebra k G ι algAct) ∧
        F ⟨0, hm_pos⟩ = ∑ i : {j : Fin m // j ≠ ⟨0, hm_pos⟩}, c i * F i.val)
    (h_relation : Finset.univ.sum (fun i => g i * F i) = 0)
    (σ : G) (hσ : IsComplexReflection (ρ σ))

    (IH : ∀ (g' : Fin m → MvPolynomial ι k),
      (∀ i, ∃ d, (g' i).IsHomogeneous d) →
      Finset.univ.sum (fun i => g' i * F i) = 0 →
      (g' ⟨0, hm_pos⟩).totalDegree < (g ⟨0, hm_pos⟩).totalDegree →
      g' ⟨0, hm_pos⟩ ∈ positiveInvariantIdeal algAct) :
    (algAct σ) (g ⟨0, hm_pos⟩) - g ⟨0, hm_pos⟩ ∈ positiveInvariantIdeal algAct := by

  obtain ⟨h_quot, hh_rel, hh_homog, hh_deg, hh_impl, hh_zero⟩ :=
    reflection_divisibility_quotients ρ algAct m hm_pos F g
      hF_inv hF_homog hg_homog h_relation σ hσ

  by_cases hg0 : g ⟨0, hm_pos⟩ = 0
  · exact hh_zero hg0
  ·
    by_cases hdeg_pos : (g ⟨0, hm_pos⟩).totalDegree ≥ 1
    ·
      have hlt : (h_quot ⟨0, hm_pos⟩).totalDegree < (g ⟨0, hm_pos⟩).totalDegree := by
        have := hh_deg ⟨0, hm_pos⟩ hg0 hdeg_pos
        omega

      have h1_in_I : h_quot ⟨0, hm_pos⟩ ∈ positiveInvariantIdeal algAct :=
        IH h_quot hh_homog hh_rel hlt

      exact hh_impl h1_in_I
    ·
      push Not at hdeg_pos
      have hdeg0 : (g ⟨0, hm_pos⟩).totalDegree = 0 := by omega
      have hconst : ∃ c : k, g ⟨0, hm_pos⟩ = MvPolynomial.C c := by
        rw [MvPolynomial.totalDegree_eq_zero_iff] at hdeg0
        exact ⟨MvPolynomial.coeff 0 (g ⟨0, hm_pos⟩), by
          ext a; simp only [MvPolynomial.coeff_C]
          split_ifs with ha
          · subst ha; rfl
          · exact MvPolynomial.notMem_support_iff.mp (fun hmem =>
              ha (Finsupp.ext (fun x => by
                simp [Finsupp.zero_apply]; have := hdeg0 a hmem x; omega)))⟩
      obtain ⟨c, hc⟩ := hconst
      rw [hc, show (algAct σ) (MvPolynomial.C c) = MvPolynomial.C c from by
        have : MvPolynomial.C c = algebraMap k (MvPolynomial ι k) c := rfl
        rw [this, AlgEquiv.commutes], sub_self]
      exact Ideal.zero_mem _

lemma reflection_group_diff_mem_positiveInvariantIdeal
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : G →* V ≃ₗ[k] V)
    (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))
    (hG : IsComplexReflectionGroup G ρ)
    (m : ℕ) (hm_pos : 0 < m)
    (F : Fin m → MvPolynomial ι k) (g : Fin m → MvPolynomial ι k)
    (hF_inv : ∀ i, F i ∈ polynomialInvariantSubalgebra k G ι algAct)
    (hF_homog : ∀ i, ∃ d, (F i).IsHomogeneous d)
    (hg_homog : ∀ i, ∃ d, (g i).IsHomogeneous d)
    (hF1_not_in_invG :
      ¬ ∃ (c : {j : Fin m // j ≠ ⟨0, hm_pos⟩} → MvPolynomial ι k),
        (∀ i, c i ∈ polynomialInvariantSubalgebra k G ι algAct) ∧
        F ⟨0, hm_pos⟩ = ∑ i : {j : Fin m // j ≠ ⟨0, hm_pos⟩}, c i * F i.val)
    (h_relation : Finset.univ.sum (fun i => g i * F i) = 0)
    (w : G) :
    (algAct w) (g ⟨0, hm_pos⟩) - g ⟨0, hm_pos⟩ ∈ positiveInvariantIdeal algAct := by


  suffices IH_full : ∀ (D : ℕ) (g' : Fin m → MvPolynomial ι k),
    (∀ i, ∃ d, (g' i).IsHomogeneous d) →
    Finset.univ.sum (fun i => g' i * F i) = 0 →
    (g' ⟨0, hm_pos⟩).totalDegree ≤ D →
    (g' ⟨0, hm_pos⟩ ∈ positiveInvariantIdeal algAct ∧
     ∀ w : G, (algAct w) (g' ⟨0, hm_pos⟩) - g' ⟨0, hm_pos⟩ ∈ positiveInvariantIdeal algAct) by
    exact (IH_full _ g hg_homog h_relation le_rfl).2 w

  intro D
  induction D with
  | zero =>

    intro g' hg'_homog h_rel' hdeg
    have hdeg0 : (g' ⟨0, hm_pos⟩).totalDegree = 0 := Nat.le_zero.mp hdeg
    constructor
    ·

      have hconst' : ∃ c : k, g' ⟨0, hm_pos⟩ = MvPolynomial.C c := by
        rw [MvPolynomial.totalDegree_eq_zero_iff] at hdeg0
        exact ⟨MvPolynomial.coeff 0 (g' ⟨0, hm_pos⟩), by
          ext a; simp only [MvPolynomial.coeff_C]
          split_ifs with ha
          · subst ha; rfl
          · exact MvPolynomial.notMem_support_iff.mp (fun hmem =>
              ha (Finsupp.ext (fun x => by
                simp [Finsupp.zero_apply]; have := hdeg0 a hmem x; omega)))⟩
      obtain ⟨c', hc'⟩ := hconst'

      have h_reynolds_eq : reynoldsOperator algAct (g' ⟨0, hm_pos⟩) = g' ⟨0, hm_pos⟩ := by
        rw [hc']
        exact reynolds_identity_on_invariants algAct (MvPolynomial.C c')
          (fun w => by
            show (algAct w) (MvPolynomial.C c') = MvPolynomial.C c'
            have : MvPolynomial.C c' = algebraMap k (MvPolynomial ι k) c' := rfl
            rw [this, AlgEquiv.commutes])
      rw [← h_reynolds_eq]
      exact reynolds_invariant_pos_deg_mem_positiveInvariantIdeal ρ algAct hG m hm_pos F g'
        hF_inv hF_homog hg'_homog hF1_not_in_invG h_rel'

    ·
      intro w'
      have hconst : ∃ c : k, g' ⟨0, hm_pos⟩ = MvPolynomial.C c := by
        rw [MvPolynomial.totalDegree_eq_zero_iff] at hdeg0
        exact ⟨MvPolynomial.coeff 0 (g' ⟨0, hm_pos⟩), by
          ext a; simp only [MvPolynomial.coeff_C]
          split_ifs with ha
          · subst ha; rfl
          · exact MvPolynomial.notMem_support_iff.mp (fun hmem =>
              ha (Finsupp.ext (fun x => by
                simp [Finsupp.zero_apply]; have := hdeg0 a hmem x; omega)))⟩
      obtain ⟨c, hc⟩ := hconst
      rw [hc, show (algAct w') (MvPolynomial.C c) = MvPolynomial.C c from by
        have : MvPolynomial.C c = algebraMap k (MvPolynomial ι k) c := rfl
        rw [this, AlgEquiv.commutes], sub_self]
      exact Ideal.zero_mem _
  | succ D' ih =>

    intro g' hg'_homog h_rel' hdeg

    by_cases hle : (g' ⟨0, hm_pos⟩).totalDegree ≤ D'
    · exact ih g' hg'_homog h_rel' hle
    ·
      push Not at hle

      have hIH_lower : ∀ (g'' : Fin m → MvPolynomial ι k),
        (∀ i, ∃ d, (g'' i).IsHomogeneous d) →
        Finset.univ.sum (fun i => g'' i * F i) = 0 →
        (g'' ⟨0, hm_pos⟩).totalDegree < (g' ⟨0, hm_pos⟩).totalDegree →
        g'' ⟨0, hm_pos⟩ ∈ positiveInvariantIdeal algAct := by
        intro g'' hg''_homog h_rel'' hlt
        have hle' : (g'' ⟨0, hm_pos⟩).totalDegree ≤ D' := by omega
        exact (ih g'' hg''_homog h_rel'' hle').1

      have h_diff : ∀ w' : G,
        (algAct w') (g' ⟨0, hm_pos⟩) - g' ⟨0, hm_pos⟩ ∈ positiveInvariantIdeal algAct := by
        intro w'
        obtain ⟨n, σs, hσ_refl, hw_eq⟩ := hG.generated_by_reflections w'
        rw [hw_eq]
        exact list_prod_diff_mem_ideal algAct (positiveInvariantIdeal algAct)
          (fun w f hf => positiveInvariantIdeal_stable algAct w f hf)
          (g' ⟨0, hm_pos⟩)
          (List.ofFn σs)
          (fun σ hσ_mem => by
            rw [List.mem_ofFn] at hσ_mem
            obtain ⟨j, rfl⟩ := hσ_mem
            exact reflection_single_diff_mem ρ algAct hG m hm_pos F g'
              hF_inv hF_homog hg'_homog hF1_not_in_invG h_rel' (σs j) (hσ_refl j)
              hIH_lower)
      constructor
      ·

        have h_reynolds_diff := reynolds_diff_of_groupDiff_mem algAct
          (g' ⟨0, hm_pos⟩) (positiveInvariantIdeal algAct) h_diff

        have h_reynolds_in :=
          reynolds_invariant_pos_deg_mem_positiveInvariantIdeal ρ algAct hG m hm_pos F g'
            hF_inv hF_homog hg'_homog hF1_not_in_invG h_rel'

        have h_eq : g' ⟨0, hm_pos⟩ = reynoldsOperator algAct (g' ⟨0, hm_pos⟩) -
            (reynoldsOperator algAct (g' ⟨0, hm_pos⟩) - g' ⟨0, hm_pos⟩) := by ring
        rw [h_eq]
        exact Ideal.sub_mem _ h_reynolds_in h_reynolds_diff
      · exact h_diff

lemma reynolds_diff_mem_positiveInvariantIdeal
    (hG : IsComplexReflectionGroup G ρ)
    (m : ℕ) (hm_pos : 0 < m)
    (F : Fin m → MvPolynomial ι k) (g : Fin m → MvPolynomial ι k)
    (hF_inv : ∀ i, F i ∈ polynomialInvariantSubalgebra k G ι algAct)
    (hF_homog : ∀ i, ∃ d, (F i).IsHomogeneous d)
    (hg_homog : ∀ i, ∃ d, (g i).IsHomogeneous d)
    (hF1_not_in_invG :
      ¬ ∃ (c : {j : Fin m // j ≠ ⟨0, hm_pos⟩} → MvPolynomial ι k),
        (∀ i, c i ∈ polynomialInvariantSubalgebra k G ι algAct) ∧
        F ⟨0, hm_pos⟩ = ∑ i : {j : Fin m // j ≠ ⟨0, hm_pos⟩}, c i * F i.val)
    (h_relation : Finset.univ.sum (fun i => g i * F i) = 0) :
    reynoldsOperator algAct (g ⟨0, hm_pos⟩) - g ⟨0, hm_pos⟩ ∈ positiveInvariantIdeal algAct :=
  reynolds_diff_of_groupDiff_mem algAct (g ⟨0, hm_pos⟩) (positiveInvariantIdeal algAct)
    (fun w => reflection_group_diff_mem_positiveInvariantIdeal ρ algAct hG m hm_pos F g
      hF_inv hF_homog hg_homog hF1_not_in_invG h_relation w)

theorem complex_reflection_syzygy_lemma
    (hG : IsComplexReflectionGroup G ρ)
    (m : ℕ) (hm_pos : 0 < m)
    (F : Fin m → MvPolynomial ι k) (g : Fin m → MvPolynomial ι k)

    (hF_inv : ∀ i, F i ∈ polynomialInvariantSubalgebra k G ι algAct)
    (hF_homog : ∀ i, ∃ d, (F i).IsHomogeneous d)

    (hg_homog : ∀ i, ∃ d, (g i).IsHomogeneous d)


    (hF1_not_in_invG :
      ¬ ∃ (c : {j : Fin m // j ≠ ⟨0, hm_pos⟩} → MvPolynomial ι k),
        (∀ i, c i ∈ polynomialInvariantSubalgebra k G ι algAct) ∧
        F ⟨0, hm_pos⟩ = ∑ i : {j : Fin m // j ≠ ⟨0, hm_pos⟩}, c i * F i.val)

    (h_relation : Finset.univ.sum (fun i => g i * F i) = 0) :

    g ⟨0, hm_pos⟩ ∈ positiveInvariantIdeal algAct := by

  have h_reynolds_minus :=
    reynolds_diff_mem_positiveInvariantIdeal ρ algAct hG m hm_pos F g
      hF_inv hF_homog hg_homog hF1_not_in_invG h_relation

  have h_reynolds_in :=
    reynolds_invariant_pos_deg_mem_positiveInvariantIdeal ρ algAct hG m hm_pos F g
      hF_inv hF_homog hg_homog hF1_not_in_invG h_relation

  have h_eq : g ⟨0, hm_pos⟩ = reynoldsOperator algAct (g ⟨0, hm_pos⟩) -
      (reynoldsOperator algAct (g ⟨0, hm_pos⟩) - g ⟨0, hm_pos⟩) := by ring
  rw [h_eq]
  exact Ideal.sub_mem _ h_reynolds_in h_reynolds_minus

end Lemma11_3

section Lemma11_4

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (ρ : G →* V ≃ₗ[k] V)
  (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))

def IsMinimalGeneratingSet (r : ℕ) (f : Fin r → MvPolynomial ι k)
    (I : Ideal (MvPolynomial ι k)) : Prop :=
  I = Ideal.span (Set.range f) ∧
    ∀ j : Fin r, f j ∉ Ideal.span (Set.range (fun i : {i : Fin r // i ≠ j} => f i.val))

lemma pderiv_aeval_chain_rule {k' : Type*} [CommRing k'] {σ' τ' : Type*} [DecidableEq σ']
    [Fintype σ'] (h : MvPolynomial σ' k') (g : σ' → MvPolynomial τ' k') (κ : τ') :
    MvPolynomial.pderiv κ (MvPolynomial.aeval g h) =
      ∑ j : σ', MvPolynomial.aeval g (MvPolynomial.pderiv j h) *
        MvPolynomial.pderiv κ (g j) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add]
    rw [hp, hq, ← Finset.sum_add_distrib]
    congr 1; ext j; rw [add_mul]

  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    rw [MvPolynomial.pderiv_mul, hp]
    simp only [Derivation.leibniz, MvPolynomial.pderiv_X, Pi.single_apply, smul_eq_mul, mul_ite,
      mul_one, mul_zero, map_add, map_mul, MvPolynomial.aeval_X]
    have h1 : ∀ x : σ', (MvPolynomial.aeval g) (if i = x then p else 0) =
        if i = x then (MvPolynomial.aeval g) p else 0 := by
      intro x; split_ifs <;> simp
    simp_rw [h1, add_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · symm
      have h2 : ∀ x : σ', (if i = x then (MvPolynomial.aeval g) p else 0) *
          (MvPolynomial.pderiv κ) (g x) =
          if x = i then (MvPolynomial.aeval g) p * (MvPolynomial.pderiv κ) (g x) else 0 := by
        intro x
        by_cases hxi : i = x
        · simp [hxi]
        · simp [hxi, Ne.symm hxi]
      simp_rw [h2]
      rw [Finset.sum_ite_eq' _ i]; exact if_pos (Finset.mem_univ _)
    · rw [Finset.sum_mul]; congr 1; ext j; ring

theorem sum_X_mul_pderiv_eq (r : ℕ)
    (f : Fin r → MvPolynomial ι k) (d : Fin r → ℕ)
    (a : Fin r → MvPolynomial ι k)
    (b : Fin r → ι → MvPolynomial ι k)
    (hf_homog : ∀ j, (f j).IsHomogeneous (d j))
    (heq : ∀ κ : ι, ∑ j, a j * pderiv κ (f j) = ∑ j, b j κ * f j) :
    ∑ j, (d j) • (a j * f j) = ∑ j, (∑ κ, X κ * b j κ) * f j := by
  have h1 : ∑ κ, X κ * ∑ j, a j * pderiv κ (f j) =
      ∑ κ, X κ * ∑ j, b j κ * f j := by
    congr 1; ext κ; rw [heq]
  simp_rw [Finset.mul_sum] at h1
  rw [Finset.sum_comm] at h1
  conv at h1 => rhs; rw [Finset.sum_comm]
  have h2 : ∀ j : Fin r,
      ∑ κ : ι, X κ * (a j * pderiv κ (f j)) = (d j) • (a j * f j) := by
    intro j
    simp_rw [← mul_assoc, mul_comm (X _) (a j), mul_assoc]
    rw [← Finset.mul_sum, (hf_homog j).sum_X_mul_pderiv, mul_smul_comm]
  simp_rw [h2] at h1
  have h3 : ∀ j : Fin r,
      ∑ κ : ι, X κ * (b j κ * f j) = (∑ κ, X κ * b j κ) * f j := by
    intro j
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
  simp_rw [h3] at h1
  exact h1

theorem quasi_homogeneous_wlog_homogeneity
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ℕ} (f : Fin r → MvPolynomial ι k)
    (d : Fin r → ℕ)
    (hf_homog : ∀ j, (f j).IsHomogeneous (d j))
    (p : MvPolynomial (Fin r) k)
    (hp : MvPolynomial.aeval f p = 0)
    (hp_ne : p ≠ 0) :
    ∀ i : Fin r, ∃ dg,
      ((d i : MvPolynomial ι k) * MvPolynomial.aeval f (MvPolynomial.pderiv i p)).IsHomogeneous dg := by sorry

theorem euler_degree_argument_gives_membership
    {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {r : ℕ} (hr_pos : 0 < r)
    (f : Fin r → MvPolynomial ι k)
    (d : Fin r → ℕ)
    (hd_pos : ∀ j, 0 < d j)
    (hf_homog : ∀ j, (f j).IsHomogeneous (d j))
    (hf_min : IsMinimalGeneratingSet r f
      (Ideal.span (Set.range f)))
    (a : Fin r → MvPolynomial ι k)
    (h_euler : Finset.univ.sum (fun j : Fin r =>
        ((d j : MvPolynomial ι k) * a j) * f j) = 0)
    (h_g0_in : ((d ⟨0, hr_pos⟩ : MvPolynomial ι k) * a ⟨0, hr_pos⟩) ∈
        Ideal.span (Set.range f)) :
    ∃ j : Fin r,
      f j ∈ Ideal.span (Set.range (fun i : {i : Fin r // i ≠ j} => f i.val)) := by


  sorry

theorem minimal_generators_algebraically_independent
    (hG : IsComplexReflectionGroup G ρ)
    (r : ℕ) (f : Fin r → MvPolynomial ι k)
    (d : Fin r → ℕ)
    (hd_pos : ∀ j, 0 < d j)
    (hf_homog : ∀ j, (f j).IsHomogeneous (d j))
    (hf_inv : ∀ i, f i ∈ polynomialInvariantSubalgebra k G ι algAct)
    (hf_min : IsMinimalGeneratingSet r f (positiveInvariantIdeal algAct)) :
    AlgebraicIndependent k f := by
  rw [algebraicIndependent_iff]
  intro p hp
  by_contra hp_ne

  have hr_pos : 0 < r := by
    by_contra hr0
    push Not at hr0
    interval_cases r
    haveI : IsEmpty (Fin 0) := Fin.isEmpty
    haveI : Nontrivial (MvPolynomial ι k) := inferInstance
    exact hp_ne (algebraicIndependent_empty_type.eq_zero_of_aeval_eq_zero p hp)


  have h_chain : ∀ κ : ι, ∑ j : Fin r,
      MvPolynomial.aeval f (MvPolynomial.pderiv j p) *
      MvPolynomial.pderiv κ (f j) = 0 := by
    intro κ
    have h := pderiv_aeval_chain_rule p f κ
    rw [hp, map_zero] at h
    exact h.symm


  let a : Fin r → MvPolynomial ι k := fun j =>
    MvPolynomial.aeval f (MvPolynomial.pderiv j p)
  have ha_inv : ∀ j, a j ∈ polynomialInvariantSubalgebra k G ι algAct := by
    intro j g
    show (algAct g) (MvPolynomial.aeval f (MvPolynomial.pderiv j p)) =
      MvPolynomial.aeval f (MvPolynomial.pderiv j p)


    have : (algAct g).toAlgHom.comp (MvPolynomial.aeval f) = MvPolynomial.aeval f := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
      exact hf_inv i g
    exact AlgHom.congr_fun this (MvPolynomial.pderiv j p)


  have h_euler_relation : ∑ j : Fin r, (d j) • (a j * f j) = 0 := by
    have ha_chain : ∀ κ : ι, ∑ j : Fin r, a j * pderiv κ (f j) = 0 := h_chain
    have heq : ∀ κ : ι, ∑ j, a j * pderiv κ (f j) =
        ∑ j, (fun (_ : Fin r) (_ : ι) => (0 : MvPolynomial ι k)) j κ * f j := by
      intro κ
      trans (0 : MvPolynomial ι k)
      · exact ha_chain κ
      · symm
        apply sum_eq_zero
        intro j _
        exact zero_mul _
    have h_sxm := sum_X_mul_pderiv_eq r f d a
      (fun (_ : Fin r) (_ : ι) => (0 : MvPolynomial ι k)) hf_homog heq
    have h_rhs_zero : ∑ j : Fin r, (∑ κ : ι, X κ *
        (fun (_ : Fin r) (_ : ι) => (0 : MvPolynomial ι k)) j κ) * f j = 0 := by
      apply sum_eq_zero; intro j _
      have : (∑ κ : ι, X κ * (fun (_ : Fin r) (_ : ι) => (0 : MvPolynomial ι k)) j κ) = 0 := by
        apply sum_eq_zero; intro κ _; exact mul_zero _
      rw [this, zero_mul]
    rw [h_rhs_zero] at h_sxm
    exact h_sxm


  have h_contradiction : ∃ j : Fin r,
      f j ∈ Ideal.span (Set.range (fun i : {i : Fin r // i ≠ j} => f i.val)) := by

    have h_syzygy_relation : Finset.univ.sum (fun j : Fin r =>
        ((d j : MvPolynomial ι k) * a j) * f j) = 0 := by
      have : ∀ j : Fin r,
          (d j : MvPolynomial ι k) * a j * f j = (d j) • (a j * f j) := by
        intro j
        rw [nsmul_eq_mul]
        ring
      simp_rw [this]
      exact h_euler_relation

    have hf_homog' : ∀ i : Fin r, ∃ dg, (f i).IsHomogeneous dg :=
      fun i => ⟨d i, hf_homog i⟩


    have hf0_not_in_invG :
        ¬ ∃ (c : {j : Fin r // j ≠ ⟨0, hr_pos⟩} → MvPolynomial ι k),
          (∀ i, c i ∈ polynomialInvariantSubalgebra k G ι algAct) ∧
          f ⟨0, hr_pos⟩ = ∑ i : {j : Fin r // j ≠ ⟨0, hr_pos⟩}, c i * f i.val := by
      intro ⟨c, _, hc_eq⟩
      apply hf_min.2 ⟨0, hr_pos⟩
      rw [Ideal.mem_span_range_iff_exists_fun]
      exact ⟨fun i => c i, hc_eq.symm⟩


    have hg_homog : ∀ i : Fin r, ∃ dg, ((d i : MvPolynomial ι k) * a i).IsHomogeneous dg := by


      exact quasi_homogeneous_wlog_homogeneity f d hf_homog p hp hp_ne
    have h_g0_in_I : ((d ⟨0, hr_pos⟩ : MvPolynomial ι k) * a ⟨0, hr_pos⟩) ∈
        positiveInvariantIdeal algAct :=
      complex_reflection_syzygy_lemma ρ algAct hG r hr_pos f
        (fun j => (d j : MvPolynomial ι k) * a j)
        hf_inv hf_homog' hg_homog hf0_not_in_invG h_syzygy_relation


    have h_g0_in_span : ((d ⟨0, hr_pos⟩ : MvPolynomial ι k) * a ⟨0, hr_pos⟩) ∈
        Ideal.span (Set.range f) := by
      rw [← hf_min.1]
      exact h_g0_in_I
    have hf_min_span : IsMinimalGeneratingSet r f (Ideal.span (Set.range f)) :=
      ⟨rfl, hf_min.2⟩
    exact euler_degree_argument_gives_membership hr_pos f d hd_pos hf_homog
      hf_min_span a h_syzygy_relation h_g0_in_span

  obtain ⟨j, hj_mem⟩ := h_contradiction
  exact hf_min.2 j hj_mem

end Lemma11_4

section Remark11_5

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))

end Remark11_5

section Lemma11_6

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))

def jacobianMatrixAt (y : ι → MvPolynomial ι k) (u : ι → k) : Matrix ι ι k :=
  fun i j => MvPolynomial.eval u ((MvPolynomial.pderiv j) (y i))

lemma eval_algAct_eq_eval_actPoint
    (g : G) (w : ι → k) (f : MvPolynomial ι k) :
    MvPolynomial.eval w ((algAct g) f) =
    MvPolynomial.eval (fun i => MvPolynomial.eval w ((algAct g) (MvPolynomial.X i))) f := by
  have key : (MvPolynomial.eval w : MvPolynomial ι k →+* k).comp
      (↑(algAct g) : MvPolynomial ι k →+* MvPolynomial ι k) =
      MvPolynomial.eval (fun i => MvPolynomial.eval w ((algAct g) (MvPolynomial.X i))) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply]
      change MvPolynomial.eval w ((algAct g) ((algebraMap k _) r)) = _
      rw [(algAct g).commutes]; simp [MvPolynomial.eval_C]
    · intro i; simp only [RingHom.comp_apply, MvPolynomial.eval_X]; rfl
  exact RingHom.congr_fun key f

lemma mv_polynomial_disjoint_separation
    (S T : Finset (ι → k)) (hST : Disjoint S T) :
    ∃ p : MvPolynomial ι k,
      (∀ w ∈ S, MvPolynomial.eval w p = 0) ∧
      (∀ w ∈ T, MvPolynomial.eval w p = 1) := by
  haveI : DecidableEq (ι → k) := Classical.decEq _
  have h_ne : ∀ s ∈ S, ∀ t ∈ T, s ≠ t := by
    intro s hs t ht hst; exact Finset.disjoint_left.mp hST hs (hst ▸ ht)
  have h_sep : ∀ s ∈ S, ∀ t ∈ T, ∃ i : ι, s i ≠ t i := by
    intro s hs t ht; by_contra h; push Not at h; exact h_ne s hs t ht (funext h)
  let i_st : (s : { x // x ∈ S }) → (t : { x // x ∈ T }) → ι := fun s t =>
    Classical.choose (h_sep s.val s.prop t.val t.prop)
  have hi_st : ∀ (s : { x // x ∈ S }) (t : { x // x ∈ T }),
      s.val (i_st s t) ≠ t.val (i_st s t) := fun s t =>
    Classical.choose_spec (h_sep s.val s.prop t.val t.prop)
  let φ : { x // x ∈ S } → MvPolynomial ι k := fun s =>
    T.attach.prod (fun t => MvPolynomial.X (i_st s t) - MvPolynomial.C (t.val (i_st s t)))
  have hφ_s_ne : ∀ (s : { x // x ∈ S }), MvPolynomial.eval s.val (φ s) ≠ 0 := by
    intro s
    simp only [φ, map_prod, MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_C]
    rw [Finset.prod_ne_zero_iff]; intro t _; exact sub_ne_zero.mpr (hi_st s t)
  have hφ_zero : ∀ (s : { x // x ∈ S }) (t₀ : ι → k) (ht₀ : t₀ ∈ T),
      MvPolynomial.eval t₀ (φ s) = 0 := by
    intro s t₀ ht₀
    simp only [φ, map_prod, MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_C]
    exact Finset.prod_eq_zero (Finset.mem_attach T ⟨t₀, ht₀⟩) (by simp [sub_self])
  let ψ : { x // x ∈ S } → MvPolynomial ι k := fun s =>
    MvPolynomial.C (MvPolynomial.eval s.val (φ s))⁻¹ * φ s
  have hψ_one : ∀ (s : { x // x ∈ S }), MvPolynomial.eval s.val (ψ s) = 1 := by
    intro s; simp only [ψ, map_mul, MvPolynomial.eval_C]; exact inv_mul_cancel₀ (hφ_s_ne s)
  have hψ_zero : ∀ (s : { x // x ∈ S }) (t : ι → k) (ht : t ∈ T),
      MvPolynomial.eval t (ψ s) = 0 := by
    intro s t ht; simp only [ψ, map_mul, MvPolynomial.eval_C, hφ_zero s t ht, mul_zero]
  let p : MvPolynomial ι k := S.attach.prod (fun s => 1 - ψ s)
  exact ⟨p, fun w hw => by
    simp only [p, map_prod, map_sub, map_one]
    exact Finset.prod_eq_zero (Finset.mem_attach S ⟨w, hw⟩) (by simp [hψ_one ⟨w, hw⟩]),
   fun w hw => by
    simp only [p, map_prod, map_sub, map_one]
    exact Finset.prod_eq_one (fun s _ => by simp [hψ_zero s w hw])⟩

theorem maximal_ideals_invariants_bij_orbits
    (u v : ι → k) :
    (∀ f ∈ polynomialInvariantSubalgebra k G ι algAct,
      MvPolynomial.eval u f = MvPolynomial.eval v f) ↔
    (∃ g : G, ∀ i, MvPolynomial.eval v ((algAct g) (MvPolynomial.X i)) = u i) := by
  constructor
  ·

    intro hall
    by_contra h_not_orbit
    push Not at h_not_orbit

    haveI : DecidableEq (ι → k) := Classical.decEq _

    let orbitV : Finset (ι → k) :=
      Finset.univ.image (fun g : G => fun i =>
        MvPolynomial.eval v ((algAct g) (MvPolynomial.X i)))

    let orbitU : Finset (ι → k) :=
      Finset.univ.image (fun g : G => fun i =>
        MvPolynomial.eval u ((algAct g) (MvPolynomial.X i)))

    have hu_not_in_orbitV : u ∉ orbitV := by
      simp only [orbitV, Finset.mem_image, Finset.mem_univ, true_and]
      push Not
      intro g
      obtain ⟨i, hi⟩ := h_not_orbit g
      exact fun h => absurd (congrFun h i ▸ rfl) hi

    have h_disj : Disjoint orbitV orbitU := by
      rw [Finset.disjoint_left]
      intro w hw_in_V hw_in_U
      simp only [orbitU, Finset.mem_image, Finset.mem_univ, true_and] at hw_in_U
      simp only [orbitV, Finset.mem_image, Finset.mem_univ, true_and] at hw_in_V
      obtain ⟨g₁, hg₁⟩ := hw_in_U
      obtain ⟨g₂, hg₂⟩ := hw_in_V
      have : ∀ i, MvPolynomial.eval v
          ((algAct (g₂ * g₁⁻¹)) (MvPolynomial.X i)) = u i := by
        intro i
        have h1 : ∀ f, MvPolynomial.eval u ((algAct g₁) f) =
            MvPolynomial.eval w f := by
          intro f
          rw [eval_algAct_eq_eval_actPoint algAct g₁ u f, hg₁]
        have h2 : ∀ f, MvPolynomial.eval v ((algAct g₂) f) =
            MvPolynomial.eval w f := by
          intro f
          rw [eval_algAct_eq_eval_actPoint algAct g₂ v f, hg₂]
        have step1 : (algAct (g₂ * g₁⁻¹)) (MvPolynomial.X i) =
            (algAct g₂) ((algAct g₁⁻¹) (MvPolynomial.X i)) := by
          rw [map_mul algAct]; rfl
        rw [step1, h2, ← h1]
        have step2 : (algAct g₁) ((algAct g₁⁻¹) (MvPolynomial.X i)) =
            (algAct (g₁ * g₁⁻¹)) (MvPolynomial.X i) := by
          rw [map_mul algAct]; rfl
        rw [step2, mul_inv_cancel, map_one algAct]
        simp
      obtain ⟨i, hi⟩ := h_not_orbit (g₂ * g₁⁻¹)
      exact hi (this i)

    obtain ⟨h, h_vanish, h_one⟩ :=
      mv_polynomial_disjoint_separation orbitV orbitU h_disj

    let Rh := reynoldsOperator algAct h
    have hRh_inv : Rh ∈ polynomialInvariantSubalgebra k G ι algAct :=
      reynolds_maps_to_invariants algAct h

    have hRh_v : MvPolynomial.eval v Rh = 0 := by
      simp only [Rh, reynoldsOperator, LinearMap.coe_mk, AddHom.coe_mk]
      have heval_smul : MvPolynomial.eval v ((Fintype.card G : k)⁻¹ •
        Finset.univ.sum fun g => (algAct g) h) =
        (Fintype.card G : k)⁻¹ *
        MvPolynomial.eval v (Finset.univ.sum fun g => (algAct g) h) := by
        rw [Algebra.smul_def, map_mul]; simp
      rw [heval_smul, map_sum]
      have hsum : ∑ g : G, MvPolynomial.eval v ((algAct g) h) = 0 := by
        apply Finset.sum_eq_zero
        intro g _
        rw [eval_algAct_eq_eval_actPoint algAct g v h]
        apply h_vanish
        simp only [orbitV, Finset.mem_image, Finset.mem_univ, true_and]
        exact ⟨g, rfl⟩
      rw [hsum, mul_zero]

    have hRh_u : MvPolynomial.eval u Rh = 1 := by
      simp only [Rh, reynoldsOperator, LinearMap.coe_mk, AddHom.coe_mk]
      have heval_smul : MvPolynomial.eval u ((Fintype.card G : k)⁻¹ •
        Finset.univ.sum fun g => (algAct g) h) =
        (Fintype.card G : k)⁻¹ *
        MvPolynomial.eval u (Finset.univ.sum fun g => (algAct g) h) := by
        rw [Algebra.smul_def, map_mul]; simp
      rw [heval_smul, map_sum]
      have hsum : ∑ g : G, MvPolynomial.eval u ((algAct g) h) =
          (Fintype.card G : k) := by
        have h1 : ∑ g : G, MvPolynomial.eval u ((algAct g) h) =
            ∑ _g : G, (1 : k) := by
          apply Finset.sum_congr rfl
          intro g _
          rw [eval_algAct_eq_eval_actPoint algAct g u h]
          apply h_one
          simp only [orbitU, Finset.mem_image, Finset.mem_univ, true_and]
          exact ⟨g, rfl⟩
        rw [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      rw [hsum]
      exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_pos.ne')

    have key := hall Rh hRh_inv
    rw [hRh_u, hRh_v] at key
    exact one_ne_zero key

  ·
    intro ⟨g, hg⟩ f hf
    have h1 : MvPolynomial.eval v ((algAct g) f) = MvPolynomial.eval u f := by
      rw [eval_algAct_eq_eval_actPoint algAct g v f]
      have : (fun i => MvPolynomial.eval v ((algAct g) (MvPolynomial.X i))) = u :=
        funext hg
      rw [this]
    rw [← h1, hf g]

end Lemma11_6

section Section11_3

variable {k : Type*} [Field k] [CharZero k] [IsAlgClosed k]
  {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {G : Type*} [Group G] [Fintype G] [DecidableEq G]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  (ρ : G →* V ≃ₗ[k] V)
  (algAct : G →* (MvPolynomial ι k ≃ₐ[k] MvPolynomial ι k))

def IsProductOfReflections (g : G) : Prop :=
  ∃ (n : ℕ) (reflections : Fin n → G),
    (∀ i, IsComplexReflection (ρ (reflections i))) ∧
    g = (List.ofFn reflections).prod

end Section11_3

end
