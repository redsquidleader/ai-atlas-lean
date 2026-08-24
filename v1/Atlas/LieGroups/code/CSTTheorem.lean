/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.ChevalleyRestriction
import Atlas.LieGroups.code.SyzygiesKoszul
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.RepresentationTheory.Equiv
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Character
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.AlgebraicIndependent.Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Invariant.Basic

noncomputable section

universe u

def qIntegerCST (d : ℕ) : PowerSeries ℤ :=
  ∑ i ∈ Finset.range d, PowerSeries.X ^ i

def quotientGradedComponent (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (N : ℕ) :
    Submodule ℂ (MvPolynomial (Fin n) ℂ ⧸ I) :=
  Submodule.map (I.mkQ.restrictScalars ℂ)
    (MvPolynomial.homogeneousSubmodule (Fin n) ℂ N)

def polyRepresentation {n : ℕ} {G : Type*} [Group G]
    (algAct : G →* (MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ)) :
    Representation ℂ G (MvPolynomial (Fin n) ℂ) where
  toFun g := (algAct g).toLinearMap
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [map_mul]

structure CSTPartIIData where
  n : ℕ
  G : Type*
  [instGroup : Group G]
  [instFintype : Fintype G]
  [instDecEq : DecidableEq G]
  linearAction : G →* ((Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ))
  is_reflection_group : IsComplexReflectionGroup G linearAction
  algAct : G →* (MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial (Fin n) ℂ)
  invariantSubalgebra : Subalgebra ℂ (MvPolynomial (Fin n) ℂ)
  mem_invariant_iff : ∀ p : MvPolynomial (Fin n) ℂ,
    p ∈ invariantSubalgebra ↔ ∀ g : G, algAct g p = p
  basicInvariants : Fin n → ↥invariantSubalgebra
  alg_independent : AlgebraicIndependent ℂ basicInvariants
  generators_generate : Algebra.adjoin ℂ (Set.range basicInvariants) = ⊤
  degrees : Fin n → ℕ
  basicInvariants_homogeneous : ∀ i,
    (↑(basicInvariants i) : MvPolynomial (Fin n) ℂ).IsHomogeneous (degrees i)
  basicInvariants_vanish : ∀ (v : Fin n → ℂ),
    (∀ i, MvPolynomial.eval v (↑(basicInvariants i) : MvPolynomial (Fin n) ℂ) = 0) → v = 0
  R₀ : Type*
  [instR₀AddCommGroup : AddCommGroup R₀]
  [instR₀Module : Module ℂ R₀]
  [instR₀FiniteDimensional : FiniteDimensional ℂ R₀]
  R₀Action : Representation ℂ G R₀
  R₀_quotient_iso : R₀ ≃ₗ[ℂ]
    (MvPolynomial (Fin n) ℂ ⧸
      Ideal.span (Set.range (fun i => (basicInvariants i : MvPolynomial (Fin n) ℂ))))
  hilbertR₀ : PowerSeries ℤ
  hilbertR₀_coeff_eq : ∀ N : ℕ,
    (PowerSeries.coeff N) hilbertR₀ =
      ↑(Module.finrank ℂ
        (quotientGradedComponent n
          (Ideal.span (Set.range (fun i => (↑(basicInvariants i) : MvPolynomial (Fin n) ℂ))))
          N))

attribute [instance] CSTPartIIData.instGroup CSTPartIIData.instFintype
attribute [instance] CSTPartIIData.instDecEq
attribute [instance] CSTPartIIData.instR₀AddCommGroup CSTPartIIData.instR₀Module
attribute [instance] CSTPartIIData.instR₀FiniteDimensional

def CSTPartIIData.polyRep (cst : CSTPartIIData) :
    Representation ℂ cst.G (MvPolynomial (Fin cst.n) ℂ) :=
  polyRepresentation cst.algAct

variable (cst : CSTPartIIData)

theorem cst_pos_degrees (cst : CSTPartIIData) : ∀ i, 0 < cst.degrees i := by
  intro i
  by_contra h
  simp only [not_lt, Nat.le_zero] at h


  have h0 := cst.basicInvariants_homogeneous i
  rw [h] at h0
  rw [← MvPolynomial.totalDegree_zero_iff_isHomogeneous] at h0
  rw [MvPolynomial.totalDegree_eq_zero_iff_eq_C] at h0
  set c := MvPolynomial.coeff 0 (↑(cst.basicInvariants i) : MvPolynomial (Fin cst.n) ℂ)

  have hxi : cst.basicInvariants i = algebraMap ℂ _ c := by
    ext; simp [h0, MvPolynomial.algebraMap_eq]

  have hp : MvPolynomial.aeval cst.basicInvariants
      (MvPolynomial.X i - MvPolynomial.C c) = (0 : ↥cst.invariantSubalgebra) := by
    simp [hxi]
  have hne : MvPolynomial.X i - MvPolynomial.C c ≠
      (0 : MvPolynomial (Fin cst.n) ℂ) := by
    intro h
    have h1 := sub_eq_zero.mp h
    have h2 := MvPolynomial.totalDegree_X (R := ℂ) i
    have h3 := MvPolynomial.totalDegree_C (σ := Fin cst.n) c
    linarith [congr_arg MvPolynomial.totalDegree h1]
  exact hne (cst.alg_independent hp)

theorem cst_finite_over_invariants (cst : CSTPartIIData) :
    Module.Finite (Algebra.adjoin ℂ (Set.range (fun i =>
      (↑(cst.basicInvariants i) : MvPolynomial (Fin cst.n) ℂ))))
      (MvPolynomial (Fin cst.n) ℂ) := by

  set S := Algebra.adjoin ℂ (Set.range (fun i =>
    (↑(cst.basicInvariants i) : MvPolynomial (Fin cst.n) ℂ)))

  haveI : Algebra.FiniteType (↥S) (MvPolynomial (Fin cst.n) ℂ) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ _ _


  suffices Algebra.IsIntegral (↥S) (MvPolynomial (Fin cst.n) ℂ) from
    Algebra.IsIntegral.finite

  have hS_eq : S = cst.invariantSubalgebra := by
    apply le_antisymm
    ·
      apply Algebra.adjoin_le
      rintro _ ⟨i, rfl⟩
      exact (cst.basicInvariants i).2
    ·
      intro p hp
      have hmem : (⟨p, hp⟩ : ↥cst.invariantSubalgebra) ∈
          Algebra.adjoin ℂ (Set.range cst.basicInvariants) :=
        cst.generators_generate ▸ Algebra.mem_top

      have key : ∀ (x : ↥cst.invariantSubalgebra),
          x ∈ Algebra.adjoin ℂ (Set.range cst.basicInvariants) →
          (x : MvPolynomial (Fin cst.n) ℂ) ∈ S := by
        intro x hx
        induction hx using Algebra.adjoin_induction with
        | mem y hy =>
          obtain ⟨i, rfl⟩ := hy
          exact Algebra.subset_adjoin ⟨i, rfl⟩
        | algebraMap r => exact S.algebraMap_mem r
        | add _ _ _ _ ha hb => exact S.add_mem ha hb
        | mul _ _ _ _ ha hb => exact S.mul_mem ha hb
      exact key ⟨p, hp⟩ hmem

  letI : MulSemiringAction cst.G (MvPolynomial (Fin cst.n) ℂ) :=
    MulSemiringAction.compHom _
      { toFun := fun g => (cst.algAct g).toRingEquiv
        map_one' := by ext; simp
        map_mul' := by intro a b; ext; simp [map_mul] }
  have hsmul : ∀ (g : cst.G) (f : MvPolynomial (Fin cst.n) ℂ),
      g • f = cst.algAct g f := fun _ _ => rfl

  letI : SMulCommClass cst.G ℂ (MvPolynomial (Fin cst.n) ℂ) :=
    ⟨fun g c f => by
      show cst.algAct g (c • f) = c • (cst.algAct g f)
      rw [Algebra.smul_def, map_mul, (cst.algAct g).commutes, ← Algebra.smul_def]⟩

  haveI : Algebra.IsInvariant (↥S) (MvPolynomial (Fin cst.n) ℂ) cst.G := by
    constructor
    intro b hb
    have hb_inv : b ∈ cst.invariantSubalgebra := by
      rw [cst.mem_invariant_iff]; intro g; exact hsmul g b ▸ hb g
    have hb_S : b ∈ S := hS_eq ▸ hb_inv
    exact ⟨⟨b, hb_S⟩, rfl⟩

  exact Algebra.IsInvariant.isIntegral (↥S) (MvPolynomial (Fin cst.n) ℂ) cst.G

lemma qIntegerCST_eq_qAnalog (d : ℕ) : qIntegerCST d = qAnalog d := by
  simp only [qIntegerCST, qAnalog]
  ext n
  simp [PowerSeries.coeff_mk, map_sum, PowerSeries.coeff_X_pow]

lemma quotientGradedComponent_eq_quotientHomogeneousSubmodule
    (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (N : ℕ) :
    quotientGradedComponent n I N = quotientHomogeneousSubmodule ℂ n I N := rfl

lemma isHomogeneous_to_coeff_form {n : ℕ} {p : MvPolynomial (Fin n) ℂ} {d : ℕ}
    (hp : p.IsHomogeneous d) :
    ∀ (m : Fin n →₀ ℕ), MvPolynomial.coeff m p ≠ 0 → (m.sum fun _ e => e) = d := by
  intro m hm
  have := hp hm
  simp [Finsupp.weight_apply] at this
  exact this

theorem cst_hilbert_series_helper (cst : CSTPartIIData) :
    ∀ N : ℕ,
      ↑(Module.finrank ℂ
        (quotientGradedComponent cst.n
          (Ideal.span (Set.range (fun i => (↑(cst.basicInvariants i) : MvPolynomial (Fin cst.n) ℂ))))
          N)) =
      (PowerSeries.coeff N) (∏ i : Fin cst.n, qIntegerCST (cst.degrees i)) := by


  set f := (fun i => (↑(cst.basicInvariants i) : MvPolynomial (Fin cst.n) ℂ)) with hf_def
  set I := Ideal.span (Set.range f) with hI_def
  have hhom : ∀ i, ∀ (m : Fin cst.n →₀ ℕ),
      MvPolynomial.coeff m (f i) ≠ 0 → (m.sum fun _ e => e) = cst.degrees i :=
    fun i => isHomogeneous_to_coeff_form (cst.basicInvariants_homogeneous i)

  have hvanish : ∀ (v : Fin cst.n → ℂ),
      (∀ i, MvPolynomial.eval v (f i) = 0) → v = 0 :=
    cst.basicInvariants_vanish

  have hHS := prop_12_10_hilbert_series ℂ cst.n inferInstance f cst.degrees
    (cst_pos_degrees cst) hhom hvanish (cst_finite_over_invariants cst)

  intro N
  have hcoeff : ∀ M : ℕ,
    (PowerSeries.coeff M) (hilbertSeries (quotientHomogeneousSubmodule ℂ cst.n I)) =
    (PowerSeries.coeff M) (∏ i : Fin cst.n, qAnalog (cst.degrees i)) :=
    fun M => by rw [hHS]
  specialize hcoeff N

  simp only [hilbertSeries, PowerSeries.coeff_mk] at hcoeff

  rw [quotientGradedComponent_eq_quotientHomogeneousSubmodule]
  rw [show ∏ i : Fin cst.n, qIntegerCST (cst.degrees i) =
    ∏ i : Fin cst.n, qAnalog (cst.degrees i) from
    Finset.prod_congr rfl (fun i _ => qIntegerCST_eq_qAnalog (cst.degrees i))]
  exact hcoeff

def qIntPoly (d : ℕ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range d, Polynomial.X ^ i

lemma qIntPoly_coe_eq_qIntegerCST (d : ℕ) :
    (qIntPoly d : PowerSeries ℤ) = qIntegerCST d := by
  ext n; simp only [qIntPoly, qIntegerCST]
  simp [Polynomial.coeff_coe, Polynomial.coeff_X_pow, PowerSeries.coeff_X_pow, map_sum]

lemma qIntPoly_eval_one (d : ℕ) : Polynomial.eval 1 (qIntPoly d) = ↑d := by
  simp only [qIntPoly]; simp [Polynomial.eval_finset_sum, Polynomial.eval_pow]

lemma prod_qIntPoly_coe_eq_prod_qIntegerCST {n : ℕ} (degrees : Fin n → ℕ) :
    ((∏ i : Fin n, qIntPoly (degrees i) : Polynomial ℤ) : PowerSeries ℤ) =
    ∏ i : Fin n, qIntegerCST (degrees i) := by
  rw [show (↑(∏ i : Fin n, qIntPoly (degrees i)) : PowerSeries ℤ) =
    Polynomial.coeToPowerSeries.ringHom (∏ i, qIntPoly (degrees i)) from rfl]
  rw [map_prod]; congr 1; funext i
  show (qIntPoly (degrees i) : PowerSeries ℤ) = _
  exact qIntPoly_coe_eq_qIntegerCST (degrees i)

lemma prod_qIntCST_coeff_eq_poly_coeff {n : ℕ} (degrees : Fin n → ℕ) (N : ℕ) :
    (PowerSeries.coeff N) (∏ i : Fin n, qIntegerCST (degrees i)) =
    (∏ i : Fin n, qIntPoly (degrees i)).coeff N := by
  rw [← prod_qIntPoly_coe_eq_prod_qIntegerCST]; simp [Polynomial.coeff_coe]

lemma sum_poly_coeff_eq_eval_one {p : Polynomial ℤ} {B : ℕ} (hB : p.natDegree < B) :
    ∑ i ∈ Finset.range B, p.coeff i = Polynomial.eval 1 p := by
  rw [Polynomial.eval_eq_sum_range]; simp only [one_pow, mul_one]; symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro x hx1 hx2
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [Finset.mem_range] at hx1 hx2; omega)

lemma sum_prod_qIntCST_coeff_eq_prod_degrees {n : ℕ} (degrees : Fin n → ℕ) {B : ℕ}
    (hB : (∏ i : Fin n, qIntPoly (degrees i)).natDegree < B) :
    ∑ N ∈ Finset.range B,
      (PowerSeries.coeff N) (∏ i : Fin n, qIntegerCST (degrees i)) =
    ↑(∏ i : Fin n, degrees i) := by
  simp_rw [prod_qIntCST_coeff_eq_poly_coeff]
  rw [sum_poly_coeff_eq_eval_one hB]
  simp [Polynomial.eval_prod, qIntPoly_eval_one]

theorem quotient_finrank_eq_sum_graded
    (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ))
    [FiniteDimensional ℂ (MvPolynomial (Fin n) ℂ ⧸ I)]
    (D : ℕ) :
    ∃ B : ℕ, D < B ∧
      Module.finrank ℂ (MvPolynomial (Fin n) ℂ ⧸ I) =
        ∑ N ∈ Finset.range B,
          Module.finrank ℂ (quotientGradedComponent n I N) := by
  sorry

theorem graded_decomp_finrank (cst : CSTPartIIData) :
    ∃ B, (∏ i : Fin cst.n, qIntPoly (cst.degrees i)).natDegree < B ∧
      Module.finrank ℂ cst.R₀ =
        ∑ N ∈ Finset.range B,
          Module.finrank ℂ
            (quotientGradedComponent cst.n
              (Ideal.span (Set.range
                (fun i => (↑(cst.basicInvariants i) : MvPolynomial (Fin cst.n) ℂ))))
              N) := by
  set I := Ideal.span (Set.range (fun i => (↑(cst.basicInvariants i) : MvPolynomial (Fin cst.n) ℂ)))

  haveI : FiniteDimensional ℂ (MvPolynomial (Fin cst.n) ℂ ⧸ I) :=
    Module.Finite.equiv cst.R₀_quotient_iso

  obtain ⟨B, hBdeg, hBsum⟩ :=
    quotient_finrank_eq_sum_graded cst.n I
      (∏ i : Fin cst.n, qIntPoly (cst.degrees i)).natDegree
  refine ⟨B, hBdeg, ?_⟩

  rw [cst.R₀_quotient_iso.finrank_eq]
  exact hBsum

theorem cst_dim_R0_eq_prod_helper (cst : CSTPartIIData) :
    Module.finrank ℂ cst.R₀ = ∏ i : Fin cst.n, cst.degrees i := by

  obtain ⟨B, hB_deg, hB_eq⟩ := graded_decomp_finrank cst

  suffices h : (↑(Module.finrank ℂ cst.R₀) : ℤ) = ↑(∏ i : Fin cst.n, cst.degrees i) by
    exact_mod_cast h

  rw [hB_eq, Nat.cast_sum]

  simp_rw [cst_hilbert_series_helper cst]

  exact sum_prod_qIntCST_coeff_eq_prod_degrees cst.degrees hB_deg

theorem galois_theory_R0_iso (cst : CSTPartIIData) :
    Nonempty (cst.R₀Action.Equiv (Representation.leftRegular ℂ cst.G)) := by
  sorry

theorem cst_R0_regular_rep_helper (cst : CSTPartIIData) :
    Nonempty (cst.R₀Action.Equiv (Representation.leftRegular ℂ cst.G)) :=
  galois_theory_R0_iso cst

section CSTHomGradedProjective
set_option synthInstance.maxHeartbeats 200000

theorem cst_hom_graded_projective_data (cst : CSTPartIIData)
    (W : Type*) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ cst.G W) [ρ.IsIrreducible]
    [Module cst.invariantSubalgebra
      (Representation.invariants (Representation.linHom ρ cst.polyRep))] :
    ∃ (𝒮 : ℕ → Submodule ℂ ↥cst.invariantSubalgebra)
      (hGA : GradedAlgebra 𝒮)
      (_ : @IsConnectedGrading ℂ ↥cst.invariantSubalgebra _ _ _ 𝒮 hGA)
      (ℳ : ℕ → Submodule ℂ ↥(ρ.linHom cst.polyRep).invariants)
      (_ : @IsScalarTower ℂ ↥cst.invariantSubalgebra
        ↥(ρ.linHom cst.polyRep).invariants _ _ _)
      (_ : @Module.Projective ↥cst.invariantSubalgebra _
        ↥(ρ.linHom cst.polyRep).invariants _ _),
      @IsGradedSModule ℂ ↥cst.invariantSubalgebra
        ↥(ρ.linHom cst.polyRep).invariants
        _ _ _ _ _ _ _ 𝒮 hGA ℳ := by
  sorry

theorem cst_hom_is_free_helper (cst : CSTPartIIData)
    (W : Type*) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ cst.G W) [ρ.IsIrreducible]
    [Module cst.invariantSubalgebra
      (Representation.invariants (Representation.linHom ρ cst.polyRep))] :
    Module.Free cst.invariantSubalgebra
      (Representation.invariants (Representation.linHom ρ cst.polyRep)) := by
  obtain ⟨𝒮, hGA, hconn, ℳ, hscalar, hproj, hgr⟩ :=
    cst_hom_graded_projective_data cst W ρ
  exact @graded_projective_is_free ℂ ↥cst.invariantSubalgebra _ _ _
    𝒮 hGA hconn ↥(ρ.linHom cst.polyRep).invariants _ _ _ hscalar hproj ℳ hgr

end CSTHomGradedProjective

theorem galois_theory_hom_rank (cst : CSTPartIIData)
    (W : Type*) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ cst.G W) [ρ.IsIrreducible]
    [Module cst.invariantSubalgebra
      (Representation.invariants (Representation.linHom ρ cst.polyRep))]
    (hfree : Module.Free cst.invariantSubalgebra
      (Representation.invariants (Representation.linHom ρ cst.polyRep))) :
    Module.finrank cst.invariantSubalgebra
      (Representation.invariants (Representation.linHom ρ cst.polyRep)) =
    Module.finrank ℂ W := by
  sorry

theorem cst_hom_rank_eq_dim_helper (cst : CSTPartIIData)
    (W : Type*) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ cst.G W) [ρ.IsIrreducible]
    [Module cst.invariantSubalgebra
      (Representation.invariants (Representation.linHom ρ cst.polyRep))]
    (hfree : Module.Free cst.invariantSubalgebra
      (Representation.invariants (Representation.linHom ρ cst.polyRep))) :
    Module.finrank cst.invariantSubalgebra
      (Representation.invariants (Representation.linHom ρ cst.polyRep)) =
    Module.finrank ℂ W :=
  galois_theory_hom_rank cst W ρ hfree

theorem cst_hom_free_rank_helper (cst : CSTPartIIData)
    (W : Type*) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ cst.G W) [ρ.IsIrreducible]
    [Module cst.invariantSubalgebra
      (Representation.invariants (Representation.linHom ρ cst.polyRep))] :
    Module.Free cst.invariantSubalgebra
      (Representation.invariants (Representation.linHom ρ cst.polyRep)) ∧
    (∀ (_ : Module.Free cst.invariantSubalgebra
      (Representation.invariants (Representation.linHom ρ cst.polyRep))),
     Module.finrank cst.invariantSubalgebra
       (Representation.invariants (Representation.linHom ρ cst.polyRep)) =
     Module.finrank ℂ W) := by
  exact ⟨cst_hom_is_free_helper cst W ρ,
         fun hfree => cst_hom_rank_eq_dim_helper cst W ρ hfree⟩

theorem cst_theorem_12_2_proof (cst : CSTPartIIData) :

    (∀ N : ℕ,
      ↑(Module.finrank ℂ
        (quotientGradedComponent cst.n
          (Ideal.span (Set.range (fun i => (↑(cst.basicInvariants i) : MvPolynomial (Fin cst.n) ℂ))))
          N)) =
      (PowerSeries.coeff N) (∏ i : Fin cst.n, qIntegerCST (cst.degrees i))) ∧

    (Module.finrank ℂ cst.R₀ = ∏ i : Fin cst.n, cst.degrees i) ∧

    Nonempty (cst.R₀Action.Equiv (Representation.leftRegular ℂ cst.G)) ∧

    (∀ (W : Type*) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
       (ρ : Representation ℂ cst.G W) [ρ.IsIrreducible]
       [Module cst.invariantSubalgebra
         (Representation.invariants (Representation.linHom ρ cst.polyRep))],
     Module.Free cst.invariantSubalgebra
       (Representation.invariants (Representation.linHom ρ cst.polyRep)) ∧
     (∀ (_ : Module.Free cst.invariantSubalgebra
       (Representation.invariants (Representation.linHom ρ cst.polyRep))),
      Module.finrank cst.invariantSubalgebra
        (Representation.invariants (Representation.linHom ρ cst.polyRep)) =
      Module.finrank ℂ W)) := by
  exact ⟨cst_hilbert_series_helper cst,
         cst_dim_R0_eq_prod_helper cst,
         cst_R0_regular_rep_helper cst,
         fun W _ _ _ ρ _ _ => cst_hom_free_rank_helper cst W ρ⟩

theorem cst_regular_sequence_graded_dim (cst : CSTPartIIData) :
    ∀ N : ℕ,
      ↑(Module.finrank ℂ
        (quotientGradedComponent cst.n
          (Ideal.span (Set.range (fun i => (↑(cst.basicInvariants i) : MvPolynomial (Fin cst.n) ℂ))))
          N)) =
      (PowerSeries.coeff N) (∏ i : Fin cst.n, qIntegerCST (cst.degrees i)) :=
  (cst_theorem_12_2_proof.{0} cst).1

theorem cst_finrank_R0_eq_prod_degrees (cst : CSTPartIIData) :
    Module.finrank ℂ cst.R₀ = ∏ i : Fin cst.n, cst.degrees i :=
  (cst_theorem_12_2_proof.{0} cst).2.1

theorem cst_R0_is_regular_rep (cst : CSTPartIIData) :
    Nonempty (cst.R₀Action.Equiv (Representation.leftRegular ℂ cst.G)) :=
  (cst_theorem_12_2_proof.{0} cst).2.2.1

theorem cst_finrank_R0_eq_card (cst : CSTPartIIData) :
    Module.finrank ℂ cst.R₀ = Fintype.card cst.G := by
  obtain ⟨e⟩ := cst_R0_is_regular_rep cst
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_finsupp_self]

theorem cst_partII_hom_free_and_rank
    (W : Type*) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ cst.G W) [ρ.IsIrreducible]
    [Module cst.invariantSubalgebra
      (Representation.invariants (Representation.linHom ρ cst.polyRep))] :
    Module.Free cst.invariantSubalgebra
      (Representation.invariants (Representation.linHom ρ cst.polyRep)) ∧
    (∀ (_ : Module.Free cst.invariantSubalgebra
      (Representation.invariants (Representation.linHom ρ cst.polyRep))),
    Module.finrank cst.invariantSubalgebra
      (Representation.invariants (Representation.linHom ρ cst.polyRep)) =
    Module.finrank ℂ W) := by
  have h := cst_theorem_12_2_proof cst
  exact h.2.2.2 W ρ

theorem cst_partII_R0_regular_rep :
    Nonempty (cst.R₀Action.Equiv (Representation.leftRegular ℂ cst.G)) :=
  cst_R0_is_regular_rep cst

theorem cst_partII_prod_degrees_eq_card :
    ∏ i : Fin cst.n, cst.degrees i = Fintype.card cst.G := by

  have hProd := cst_finrank_R0_eq_prod_degrees cst


  have hCard := cst_finrank_R0_eq_card cst

  omega

theorem cst_partII_hilbert_polynomial :
    cst.hilbertR₀ = ∏ i : Fin cst.n, qIntegerCST (cst.degrees i) := by


  ext N
  rw [cst.hilbertR₀_coeff_eq]
  exact cst_regular_sequence_graded_dim cst N

theorem cst_partII :

    (∀ (W : Type*) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
       (ρ : Representation ℂ cst.G W) [ρ.IsIrreducible]
       [Module cst.invariantSubalgebra
         (Representation.invariants (Representation.linHom ρ cst.polyRep))],
     Module.Free cst.invariantSubalgebra
       (Representation.invariants (Representation.linHom ρ cst.polyRep)) ∧
     (∀ (_ : Module.Free cst.invariantSubalgebra
       (Representation.invariants (Representation.linHom ρ cst.polyRep))),
      Module.finrank cst.invariantSubalgebra
        (Representation.invariants (Representation.linHom ρ cst.polyRep)) =
      Module.finrank ℂ W)) ∧

    Nonempty (cst.R₀Action.Equiv (Representation.leftRegular ℂ cst.G)) ∧

    ∏ i : Fin cst.n, cst.degrees i = Fintype.card cst.G ∧

    cst.hilbertR₀ = ∏ i : Fin cst.n, qIntegerCST (cst.degrees i) := by
  exact ⟨fun W _ _ _ ρ _ _ => cst_partII_hom_free_and_rank cst W ρ,
    cst_partII_R0_regular_rep cst, cst_partII_prod_degrees_eq_card cst,
    cst_partII_hilbert_polynomial cst⟩

end
