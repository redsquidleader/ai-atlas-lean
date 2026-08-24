/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal

import Mathlib.Algebra.Module.GradedModule
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv

noncomputable section

set_option synthInstance.maxHeartbeats 80000

open MvPolynomial

def IsRegularSequence {A : Type*} [CommRing A] {m : ℕ} (f : Fin m → A) : Prop :=
  (∀ (j : Fin m),
    ∀ (r : A ⧸ Ideal.span (Set.image f {i | (i : ℕ) < j})),
      r ≠ 0 →
        (Ideal.Quotient.mk (Ideal.span (Set.image f {i | (i : ℕ) < j})) (f j)) • r ≠ 0) ∧
  Nontrivial (A ⧸ Ideal.span (Set.range f))

structure IsGradedSModule {k S M : Type*} [CommRing k] [Ring S] [Algebra k S]
    [AddCommGroup M] [Module S M] [Module k M] [IsScalarTower k S M]
    (𝒮 : ℕ → Submodule k S) [GradedAlgebra 𝒮]
    (ℳ : ℕ → Submodule k M) : Prop where
  internal : DirectSum.IsInternal ℳ
  smul_mem : ∀ (i j : ℕ) (s : S) (m : M), s ∈ 𝒮 j → m ∈ ℳ i → s • m ∈ ℳ (i + j)

def IsConnectedGrading (k : Type*) (S : Type*) [CommRing k] [Ring S]
    [Algebra k S] (𝒮 : ℕ → Submodule k S) [GradedAlgebra 𝒮] : Prop :=
  𝒮 0 = (Algebra.linearMap k S).range

def augmentationIdealGraded {k S : Type*} [CommRing k] [CommRing S]
    [Algebra k S] (𝒮 : ℕ → Submodule k S) [GradedAlgebra 𝒮] : Ideal S :=
  Ideal.span (⋃ (i : ℕ) (_ : 0 < i), ↑(𝒮 i))

lemma isHomogeneous_augmentationIdealGraded {k S : Type*} [CommRing k] [CommRing S]
    [Algebra k S] (𝒮 : ℕ → Submodule k S) [GradedAlgebra 𝒮] :
    Ideal.IsHomogeneous 𝒮 (augmentationIdealGraded 𝒮) := by
  unfold augmentationIdealGraded
  apply Ideal.homogeneous_span
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨i, _, hxi⟩ := hx
  exact ⟨i, hxi⟩

lemma augmentationIdealGraded_component_mem {k S : Type*} [CommRing k] [CommRing S]
    [Algebra k S] (𝒮 : ℕ → Submodule k S) [GradedAlgebra 𝒮]
    (r : S) (hr : r ∈ augmentationIdealGraded 𝒮) (j : ℕ) :
    ((DirectSum.decompose 𝒮 r) j : S) ∈ augmentationIdealGraded 𝒮 :=
  ((isHomogeneous_augmentationIdealGraded 𝒮).mem_iff.mp hr) j

def hilbertSeries {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    (ℳ : ℕ → Submodule k M) : PowerSeries ℤ :=
  PowerSeries.mk (fun i => (Module.finrank k (ℳ i) : ℤ))

variable (k : Type*) [Field k] (n : ℕ)

local notation "R" => MvPolynomial (Fin n) k

def augmentation_ideal_poly : Ideal (MvPolynomial (Fin n) k) :=
  Ideal.span (Set.range (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k)))

lemma homog_in_aug_smul
    {k' S : Type*} [Field k'] [CommRing S] [Algebra k' S]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮]
    {M : Type*} [AddCommGroup M] [Module S M] [Module k' M] [IsScalarTower k' S M]
    (ℳ : ℕ → Submodule k' M) (hgr : IsGradedSModule 𝒮 ℳ)
    (d : ℕ) (x : M) (hxd : x ∈ ℳ d)
    (hxP : x ∈ (augmentationIdealGraded 𝒮) • (⊤ : Submodule S M)) :
    x ∈ Submodule.span k'
      (⋃ (j : ℕ) (_ : 0 < j) (i : ℕ) (_ : i + j = d),
        Set.image2 HSMul.hSMul (↑(𝒮 j) : Set S) (↑(ℳ i) : Set M)) := by
  classical
  haveI : DirectSum.Decomposition ℳ := hgr.internal.chooseDecomposition
  set target := Submodule.span k'
    (⋃ (j : ℕ) (_ : 0 < j) (i : ℕ) (_ : i + j = d),
      Set.image2 HSMul.hSMul (↑(𝒮 j) : Set S) (↑(ℳ i) : Set M)) with htarget_def

  have hx_eq : (↑((DirectSum.decompose ℳ x) d) : M) = x :=
    DirectSum.decompose_of_mem_same ℳ hxd
  rw [← hx_eq]

  clear hxd hx_eq

  refine Submodule.smul_induction_on hxP ?_ ?_
  ·
    intro r hr n _

    suffices key : ∀ (r : S), r ∈ augmentationIdealGraded 𝒮 → ∀ (n : M),
        (↑((DirectSum.decompose ℳ (r • n)) d) : M) ∈ target from key r hr n
    intro r hr
    induction hr using Submodule.span_induction with
    | mem s hs =>

      intro n
      simp only [Set.mem_iUnion] at hs
      obtain ⟨j, hj, hs_j⟩ := hs

      rw [(DirectSum.sum_support_decompose ℳ n).symm, Finset.smul_sum,
        DirectSum.decompose_sum, DirectSum.sum_apply, AddSubmonoidClass.coe_finset_sum]
      apply Submodule.sum_mem; intro i _

      have hni_mem := SetLike.coe_mem ((DirectSum.decompose ℳ n) i)
      have hsmul : s • (↑((DirectSum.decompose ℳ n) i) : M) ∈ ℳ (i + j) :=
        hgr.smul_mem i j s _ hs_j hni_mem

      by_cases he : d = i + j
      ·
        subst he; rw [DirectSum.decompose_of_mem_same ℳ hsmul]
        apply Submodule.subset_span

        simp only [Set.mem_iUnion]
        exact ⟨j, hj, i, rfl, Set.mem_image2_of_mem hs_j (SetLike.coe_mem _)⟩
      ·
        rw [DirectSum.decompose_of_mem_ne ℳ hsmul (Ne.symm he)]; exact target.zero_mem
    | zero =>
      intro n
      simp only [zero_smul, DirectSum.decompose_zero, DirectSum.zero_apply,
        ZeroMemClass.coe_zero]
      exact target.zero_mem
    | add _ _ _ _ ih₁ ih₂ =>
      intro n
      rw [add_smul, DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add]
      exact target.add_mem (ih₁ n) (ih₂ n)
    | smul a _ _ ih =>
      intro n
      change (↑((DirectSum.decompose ℳ ((a * _) • n)) d) : M) ∈ target
      rw [mul_comm, mul_smul]; exact ih (a • n)

  ·
    intro x y hx hy
    rw [DirectSum.decompose_add]
    simp only [DirectSum.add_apply, AddMemClass.coe_add]
    exact target.add_mem hx hy

lemma exists_homogeneous_span_quotient
    {k' S : Type*} [Field k'] [CommRing S] [Algebra k' S]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮]
    {M : Type*} [AddCommGroup M] [Module S M] [Module k' M] [IsScalarTower k' S M]
    (ℳ : ℕ → Submodule k' M) (hgr : IsGradedSModule 𝒮 ℳ)
    (hfin : FiniteDimensional k' (M ⧸ (augmentationIdealGraded 𝒮) • (⊤ : Submodule S M))) :
    ∃ (T : Finset M),
      (∀ t ∈ T, ∃ d, t ∈ ℳ d) ∧
      Submodule.span k' (((augmentationIdealGraded 𝒮) • (⊤ : Submodule S M)).mkQ '' ↑T) = ⊤ := by
  classical
  set P := (augmentationIdealGraded 𝒮) • (⊤ : Submodule S M)
  set H : Set M := ⋃ d, ↑(ℳ d)
  have hH_span : Submodule.span k' H = ⊤ := by
    rw [show H = ⋃ d, ↑(ℳ d) from rfl, ← Submodule.iSup_eq_span]
    exact hgr.internal.submodule_iSup_eq_top
  set f := P.mkQ.restrictScalars k'
  have hf_surj : Function.Surjective f := Submodule.mkQ_surjective P
  obtain ⟨S₀, hS₀⟩ := (Module.finite_def.mp (inferInstance) : (⊤ : Submodule k' (M ⧸ P)).FG)
  have hS₀_lift : ∀ q ∈ S₀, ∃ (Tq : Finset M), ↑Tq ⊆ H ∧ q ∈ Submodule.span k' (f '' ↑Tq) := by
    intro q _
    obtain ⟨m, hm⟩ := hf_surj q
    have hm_in : m ∈ Submodule.span k' H := hH_span ▸ Submodule.mem_top
    obtain ⟨Tm, hTm_sub, hm_mem⟩ := Submodule.mem_span_finite_of_mem_span hm_in
    exact ⟨Tm, hTm_sub, by rw [← hm, Submodule.span_image]; exact Submodule.mem_map_of_mem hm_mem⟩
  choose Tq hTq_sub hTq_mem using hS₀_lift
  set T := S₀.attach.biUnion (fun ⟨q, hq⟩ => Tq q hq)
  refine ⟨T, ?_, ?_⟩
  ·
    intro t ht
    rw [Finset.mem_biUnion] at ht
    obtain ⟨⟨q, hq⟩, _, ht'⟩ := ht
    have : (t : M) ∈ H := hTq_sub q hq (Finset.mem_coe.mpr ht')
    rw [Set.mem_iUnion] at this
    exact this
  ·
    rw [eq_top_iff, ← hS₀]
    apply Submodule.span_le.mpr
    intro q hq
    have hq' : q ∈ S₀ := hq
    have hTq_sub_T : (Tq q hq' : Set M) ⊆ (T : Set M) := by
      intro m hm
      show m ∈ T
      rw [Finset.mem_biUnion]
      exact ⟨⟨q, hq'⟩, Finset.mem_attach _ _, hm⟩
    have himg_sub : f '' ↑(Tq q hq') ⊆ (P.mkQ : M →ₗ[S] M ⧸ P) '' ↑T := by
      intro x ⟨m, hm, hmx⟩
      exact ⟨m, hTq_sub_T hm, hmx⟩
    exact Submodule.span_mono himg_sub (hTq_mem q hq')


lemma homog_smul_component_mem_aug
    {k' S : Type*} [Field k'] [CommRing S] [Algebra k' S]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮]
    {M : Type*} [AddCommGroup M] [Module S M] [Module k' M] [IsScalarTower k' S M]
    (ℳ : ℕ → Submodule k' M) (hgr : IsGradedSModule 𝒮 ℳ)
    [DirectSum.Decomposition ℳ]
    (d j : ℕ) (rj : S) (hrj_homog : rj ∈ 𝒮 j)
    (hrj_aug : rj ∈ augmentationIdealGraded 𝒮) (n : M) :
    ((DirectSum.decompose ℳ (rj • n)) d : M) ∈
      (augmentationIdealGraded 𝒮 : Ideal S) • (⊤ : Submodule S M) := by
  classical
  have h_eq : ((DirectSum.decompose ℳ (rj • n)) d : M) =
      ∑ i ∈ (DirectSum.decompose ℳ n).support,
        ((DirectSum.decompose ℳ (rj • ((DirectSum.decompose ℳ n) i : M))) d : M) := by
    conv_lhs => rw [show rj • n = ∑ i ∈ (DirectSum.decompose ℳ n).support,
        rj • ((DirectSum.decompose ℳ n) i : M) from by
      conv_lhs => rw [← DirectSum.sum_support_decompose ℳ n]; rw [Finset.smul_sum]]
    rw [DirectSum.decompose_sum]; simp
  rw [h_eq]
  apply Submodule.sum_mem
  intro i _
  have h_mem_grade := hgr.smul_mem i j rj _ hrj_homog ((DirectSum.decompose ℳ n) i).2
  by_cases h : i + j = d
  · rw [← h, DirectSum.decompose_of_mem_same ℳ h_mem_grade]
    exact Submodule.smul_mem_smul hrj_aug Submodule.mem_top
  · rw [DirectSum.decompose_of_mem_ne ℳ h_mem_grade h]; exact Submodule.zero_mem _

lemma aug_smul_graded_component
    {k' S : Type*} [Field k'] [CommRing S] [Algebra k' S]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮]
    {M : Type*} [AddCommGroup M] [Module S M] [Module k' M] [IsScalarTower k' S M]
    (ℳ : ℕ → Submodule k' M) (hgr : IsGradedSModule 𝒮 ℳ)
    [DirectSum.Decomposition ℳ]
    (d : ℕ) (z : M) (hz : z ∈ (augmentationIdealGraded 𝒮) • (⊤ : Submodule S M)) :
    (↑((DirectSum.decompose ℳ z) d) : M) ∈ (augmentationIdealGraded 𝒮) • (⊤ : Submodule S M) := by
  classical
  refine Submodule.smul_induction_on hz ?_ ?_
  · intro r hr n _hn
    have h_eq_r : ((DirectSum.decompose ℳ (r • n)) d : M) =
        ∑ j ∈ (DirectSum.decompose 𝒮 r).support,
          ((DirectSum.decompose ℳ (((DirectSum.decompose 𝒮 r) j : S) • n)) d : M) := by
      conv_lhs => rw [show r • n = ∑ j ∈ (DirectSum.decompose 𝒮 r).support,
          ((DirectSum.decompose 𝒮 r) j : S) • n from by
        conv_lhs => rw [← DirectSum.sum_support_decompose 𝒮 r]; rw [Finset.sum_smul]]
      rw [DirectSum.decompose_sum]; simp
    rw [h_eq_r]
    apply Submodule.sum_mem
    intro j _
    have hrj_aug : ((DirectSum.decompose 𝒮 r) j : S) ∈ augmentationIdealGraded 𝒮 :=
      augmentationIdealGraded_component_mem 𝒮 r hr j

    exact homog_smul_component_mem_aug 𝒮 ℳ hgr d j _
      ((DirectSum.decompose 𝒮 r) j).2 hrj_aug n

  · intro x y hx hy
    have h_add : (↑((DirectSum.decompose ℳ (x + y)) d) : M) =
        (↑((DirectSum.decompose ℳ x) d) : M) + (↑((DirectSum.decompose ℳ y) d) : M) := by
      simp [DirectSum.decompose_add]
    rw [h_add]
    exact Submodule.add_mem _ hx hy

lemma decompose_mod_P
    {k' S : Type*} [Field k'] [CommRing S] [Algebra k' S]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮]
    {M : Type*} [AddCommGroup M] [Module S M] [Module k' M] [IsScalarTower k' S M]
    (ℳ : ℕ → Submodule k' M) (hgr : IsGradedSModule 𝒮 ℳ)
    (T : Finset M) (hThom : ∀ t ∈ T, ∃ d, t ∈ ℳ d)
    (hTspan : Submodule.span k' (((augmentationIdealGraded 𝒮) • (⊤ : Submodule S M)).mkQ '' ↑T) = ⊤)
    (d : ℕ) (m : M) (hm : m ∈ ℳ d) :
    ∃ (v : M), v ∈ Submodule.span k' (↑T ∩ (ℳ d : Set M)) ∧
      (m - v) ∈ ℳ d ∧
      (m - v) ∈ (augmentationIdealGraded 𝒮) • (⊤ : Submodule S M) := by
  classical
  set P := (augmentationIdealGraded 𝒮) • (⊤ : Submodule S M) with hP_def
  haveI : DirectSum.Decomposition ℳ := hgr.internal.chooseDecomposition

  have hm_quot : P.mkQ m ∈ Submodule.span k' ((P.mkQ.restrictScalars k') '' ↑T) := by
    change P.mkQ m ∈ Submodule.span k' (P.mkQ '' ↑T)
    rw [hTspan]; exact Submodule.mem_top
  rw [Submodule.span_image, Submodule.mem_map] at hm_quot
  obtain ⟨y, hy, hym⟩ := hm_quot
  rw [Submodule.mem_span_finset] at hy
  obtain ⟨c, _, hc⟩ := hy

  have hsum_in_P : m - ∑ t ∈ T, c t • t ∈ P := by
    have key : P.mkQ (m - ∑ t ∈ T, c t • t) = 0 := by
      simp only [map_sub, map_sum]
      rw [show P.mkQ m = (P.mkQ.restrictScalars k') y from hym.symm, ← hc, map_sum, sub_eq_zero]
      apply Finset.sum_congr rfl
      intro t _; exact ((P.mkQ.restrictScalars k').map_smul (c t) t).symm
    rwa [P.mkQ_apply, Submodule.Quotient.mk_eq_zero] at key

  set v := ∑ t ∈ T.filter (fun t => t ∈ ℳ d), c t • t with hv_def
  refine ⟨v, ?_, ?_, ?_⟩
  ·
    apply Submodule.sum_mem; intro t ht; rw [Finset.mem_filter] at ht
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Finset.mem_coe.mpr ht.1, ht.2⟩)
  ·
    apply (ℳ d).sub_mem hm
    apply Submodule.sum_mem; intro t ht; rw [Finset.mem_filter] at ht
    exact (ℳ d).smul_mem _ ht.2
  ·


    set z := m - ∑ t ∈ T, c t • t with hz_def
    have hmv_d : m - v ∈ ℳ d := (ℳ d).sub_mem hm (by
      apply Submodule.sum_mem; intro t ht; rw [Finset.mem_filter] at ht
      exact (ℳ d).smul_mem _ ht.2)

    suffices h_decomp : (↑((DirectSum.decompose ℳ z) d) : M) = m - v by
      rw [← h_decomp]
      exact aug_smul_graded_component 𝒮 ℳ hgr d z hsum_in_P

    set w := ∑ t ∈ T.filter (fun t => t ∉ ℳ d), c t • t with hw_def
    have hz_split : z = (m - v) - w := by
      simp only [z, v, w, sub_sub]

      congr 1
      rw [← Finset.sum_union (s₁ := T.filter (· ∈ ℳ d)) (s₂ := T.filter (· ∉ ℳ d))]
      · congr 1; ext x; simp [Finset.mem_filter, Finset.mem_union]; tauto
      · exact Finset.disjoint_filter.mpr (fun x _ h1 h2 => h2 h1)

    conv_lhs => rw [hz_split]
    rw [show DirectSum.decompose ℳ ((m - v) - w) =
        DirectSum.decompose ℳ (m - v) - DirectSum.decompose ℳ w from
      map_sub (DirectSum.decomposeAddEquiv ℳ) _ _]
    simp only [DirectSum.sub_apply, AddSubgroupClass.coe_sub,
      DirectSum.decompose_of_mem_same ℳ hmv_d]

    suffices hw0 : (↑((DirectSum.decompose ℳ w) d) : M) = 0 by rw [hw0, sub_zero]

    change (↑((DirectSum.decomposeAddEquiv ℳ w) d) : M) = 0
    rw [hw_def, map_sum (DirectSum.decomposeAddEquiv ℳ)]
    have key2 : (↑((∑ x ∈ T.filter (fun t => t ∉ ℳ d),
        (DirectSum.decomposeAddEquiv ℳ) (c x • x)) d) : M) =
        ↑(∑ x ∈ T.filter (fun t => t ∉ ℳ d),
          ((DirectSum.decomposeAddEquiv ℳ) (c x • x)) d : ↥(ℳ d)) := by
      congr 1; exact DFinsupp.finset_sum_apply _ _ _
    rw [key2, AddSubmonoidClass.coe_finset_sum]

    apply Finset.sum_eq_zero
    intro t ht; rw [Finset.mem_filter] at ht
    obtain ⟨hT, hnd⟩ := ht
    obtain ⟨e, he⟩ := hThom t hT
    have hne : e ≠ d := fun heq => hnd (heq ▸ he)
    show (↑((DirectSum.decomposeAddEquiv ℳ (c t • t)) d) : M) = 0
    change (↑((DirectSum.decompose ℳ (c t • t)) d) : M) = 0
    exact DirectSum.decompose_of_mem_ne ℳ ((ℳ e).smul_mem _ he) hne

theorem lemma_12_3_i_generators

    {k' S : Type*} [Field k'] [CommRing S] [Algebra k' S]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮] (hconn : IsConnectedGrading k' S 𝒮)
    {M : Type*} [AddCommGroup M] [Module S M] [Module k' M] [IsScalarTower k' S M]
    (ℳ : ℕ → Submodule k' M) (hgr : IsGradedSModule 𝒮 ℳ)
    (hfin : FiniteDimensional k' (M ⧸ (augmentationIdealGraded 𝒮) • (⊤ : Submodule S M))) :
    Module.Finite S M := by
  set P := ((augmentationIdealGraded 𝒮) • (⊤ : Submodule S M)) with hP_def

  obtain ⟨T, hThom, hTspan⟩ := exists_homogeneous_span_quotient 𝒮 ℳ hgr hfin

  let N := Submodule.span S (T : Set M)

  suffices hN : N = ⊤ by
    rw [Module.finite_def]; exact ⟨T, hN⟩
  rw [eq_top_iff]


  suffices hall : ∀ d, ℳ d ≤ N.restrictScalars k' by
    intro m _
    have hint := hgr.internal
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hint
    have hle : (⨆ d, ℳ d) ≤ N.restrictScalars k' := iSup_le hall
    rw [hint.2] at hle
    exact hle Submodule.mem_top

  intro d
  induction d using Nat.strongRecOn with
  | ind d ih =>
    intro m hm
    show m ∈ N

    obtain ⟨v, hv_span, hm_v_d, hm_v_P⟩ := decompose_mod_P 𝒮 ℳ hgr T hThom hTspan d m hm

    have hv_N : v ∈ N := by
      have h1 : Submodule.span k' (↑T ∩ (ℳ d : Set M)) ≤ Submodule.span k' (↑T : Set M) :=
        Submodule.span_mono Set.inter_subset_left
      have h2 : Submodule.span k' (↑T : Set M) ≤ N.restrictScalars k' :=
        Submodule.span_le_restrictScalars k' S (↑T : Set M)
      exact h2 (h1 hv_span)


    have hm_v_N : m - v ∈ N := by
      have hmem := homog_in_aug_smul 𝒮 ℳ hgr d (m - v) hm_v_d hm_v_P
      suffices m - v ∈ N.restrictScalars k' from this
      apply Submodule.span_le.mpr _ hmem
      intro y hy
      simp only [Set.mem_iUnion, Set.mem_image2, SetLike.mem_coe] at hy
      obtain ⟨j, hj, i, hij, s, hs, m', hm', rfl⟩ := hy
      change s • m' ∈ N
      exact N.smul_mem s (ih i (by omega) hm')

    have : m = v + (m - v) := by abel
    rw [this]
    exact N.add_mem hv_N hm_v_N

theorem graded_nakayama
    {k' S : Type*} [Field k'] [CommRing S] [Algebra k' S]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮] (_hconn : IsConnectedGrading k' S 𝒮)
    {N : Type*} [AddCommGroup N] [Module S N] [Module k' N] [IsScalarTower k' S N]
    (𝒩 : ℕ → Submodule k' N) (hgr : IsGradedSModule 𝒮 𝒩)
    (hdeg0 : 𝒩 0 = ⊥)
    (hSN : ∀ (d : ℕ) (n : N), n ∈ 𝒩 d →
      n ∈ Submodule.span k'
        (⋃ (j : ℕ) (_ : 0 < j) (i : ℕ) (_ : i + j = d),
          Set.image2 HSMul.hSMul (↑(𝒮 j) : Set S) (↑(𝒩 i) : Set N))) :
    ∀ n : N, n = 0 := by

  have hall : ∀ d, 𝒩 d = ⊥ := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      cases d with
      | zero => exact hdeg0
      | succ d =>
        rw [Submodule.eq_bot_iff]
        intro n hn
        have hmem := hSN (d + 1) n hn

        have hset_zero : (⋃ (j : ℕ) (_ : 0 < j) (i : ℕ) (_ : i + j = d + 1),
            Set.image2 HSMul.hSMul (↑(𝒮 j) : Set S) (↑(𝒩 i) : Set N)) ⊆ {(0 : N)} := by
          intro x hx
          simp only [Set.mem_iUnion, Set.mem_image2] at hx
          obtain ⟨j, hj, i, hij, s, hs, m, hm, rfl⟩ := hx
          have hi : i < d + 1 := by omega
          rw [ih i hi] at hm
          simp at hm
          simp [hm]

        have hspan_bot : Submodule.span k'
            (⋃ (j : ℕ) (_ : 0 < j) (i : ℕ) (_ : i + j = d + 1),
              Set.image2 HSMul.hSMul (↑(𝒮 j) : Set S) (↑(𝒩 i) : Set N)) = ⊥ := by
          have : Submodule.span k' ({(0 : N)} : Set N) = ⊥ :=
            Submodule.span_singleton_eq_bot.mpr rfl
          exact le_antisymm (this ▸ Submodule.span_mono hset_zero) bot_le
        rw [hspan_bot] at hmem
        exact (Submodule.mem_bot k').mp hmem

  intro n
  have hint := hgr.internal
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hint
  have htop := hint.2
  have hbot : ⨆ i, 𝒩 i = ⊥ := by simp [hall]
  rw [hbot] at htop
  exact (Submodule.mem_bot k').mp (htop ▸ Submodule.mem_top)

theorem kernel_has_graded_nakayama_data
    {k' S : Type*} [Field k'] [CommRing S] [Algebra k' S]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮] (hconn : IsConnectedGrading k' S 𝒮)
    {M : Type*} [AddCommGroup M] [Module S M] [Module k' M] [IsScalarTower k' S M]
    (ℳ : ℕ → Submodule k' M) (hgr : IsGradedSModule 𝒮 ℳ)
    {F : Type*} [AddCommGroup F] [Module S F] [Module k' F] [IsScalarTower k' S F]
    [Module.Free S F]
    (iMF : M →ₗ[S] F) (sFM : F →ₗ[S] M)
    (h_split : sFM.comp iMF = LinearMap.id) :
    ∃ (𝒦 : ℕ → Submodule k' ↥(sFM.ker)),
      (IsGradedSModule 𝒮 𝒦) ∧
      (𝒦 0 = ⊥) ∧
      (∀ (d : ℕ) (n : ↥(sFM.ker)), n ∈ 𝒦 d →
        n ∈ Submodule.span k'
          (⋃ (j : ℕ) (_ : 0 < j) (i : ℕ) (_ : i + j = d),
            Set.image2 HSMul.hSMul (↑(𝒮 j) : Set S) (↑(𝒦 i) : Set ↥(sFM.ker)))) := by


  exact sorry

theorem kernel_vanishes_of_graded_split
    {k' S : Type*} [Field k'] [CommRing S] [Algebra k' S]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮] (hconn : IsConnectedGrading k' S 𝒮)
    {M : Type*} [AddCommGroup M] [Module S M] [Module k' M] [IsScalarTower k' S M]
    (ℳ : ℕ → Submodule k' M) (hgr : IsGradedSModule 𝒮 ℳ)
    {F : Type*} [AddCommMonoid F] [Module S F] [Module.Free S F]
    (iMF : M →ₗ[S] F) (sFM : F →ₗ[S] M)
    (h_split : sFM.comp iMF = LinearMap.id) :
    Function.Injective sFM := by


  letI : AddCommGroup F := Module.addCommMonoidToAddCommGroup S

  letI : Module k' F := Module.restrictScalars k' S F
  letI : IsScalarTower k' S F := IsScalarTower.restrictScalars k' S F

  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx


  obtain ⟨𝒦, hgr_K, hdeg0_K, hSN_K⟩ :=
    kernel_has_graded_nakayama_data 𝒮 hconn ℳ hgr iMF sFM h_split

  have hzero := graded_nakayama 𝒮 hconn 𝒦 hgr_K hdeg0_K hSN_K
  exact congr_arg Subtype.val (hzero ⟨x, hx⟩)

theorem graded_projective_is_free
    {k' S : Type*} [Field k'] [CommRing S] [Algebra k' S]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮] (hconn : IsConnectedGrading k' S 𝒮)
    {M : Type*} [AddCommGroup M] [Module S M] [Module k' M] [IsScalarTower k' S M]
    [Module.Projective S M]
    (ℳ : ℕ → Submodule k' M) (hgr : IsGradedSModule 𝒮 ℳ) :
    Module.Free S M := by


  obtain ⟨F, _, _, hFfree, iMF, sFM, h_split⟩ :=
    Module.Projective.iff_split.mp ‹Module.Projective S M›

  have hsFM_surj : Function.Surjective sFM := by
    intro m; exact ⟨iMF m, congr_fun (congr_arg DFunLike.coe h_split) m⟩


  haveI : Module.Free S F := hFfree
  have hsFM_inj : Function.Injective sFM :=
    kernel_vanishes_of_graded_split 𝒮 hconn ℳ hgr iMF sFM h_split

  have hsFM_bij : Function.Bijective sFM := ⟨hsFM_inj, hsFM_surj⟩
  let e : F ≃ₗ[S] M := LinearEquiv.ofBijective sFM hsFM_bij
  obtain ⟨⟨ι, b⟩⟩ := hFfree.exists_basis
  exact Module.Free.of_basis (b.map e)

def quotientGrading {k' S : Type*} [CommRing k'] [CommRing S] [Algebra k' S]
    {M : Type*} [AddCommGroup M] [Module S M] [Module k' M] [IsScalarTower k' S M]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮]
    (ℳ : ℕ → Submodule k' M) (i : ℕ) :
    Submodule k' (M ⧸ (augmentationIdealGraded 𝒮 • (⊤ : Submodule S M))) :=
  (ℳ i).map ((augmentationIdealGraded 𝒮 • (⊤ : Submodule S M)).mkQ.restrictScalars k')

theorem graded_free_module_dim_conv
    {k' S : Type*} [Field k'] [CommRing S] [Algebra k' S]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮] (hconn : IsConnectedGrading k' S 𝒮)
    {M : Type*} [AddCommGroup M] [Module S M] [Module k' M] [IsScalarTower k' S M]
    [Module.Projective S M]
    (ℳ : ℕ → Submodule k' M) (hgr : IsGradedSModule 𝒮 ℳ)
    (hfindim : ∀ i, FiniteDimensional k' (ℳ i)) :
    ∀ n, (Module.finrank k' (ℳ n) : ℤ) =
      ∑ p ∈ Finset.antidiagonal n,
        (Module.finrank k' (𝒮 p.1) : ℤ) * (Module.finrank k' (quotientGrading 𝒮 ℳ p.2) : ℤ) := by


  exact sorry


theorem lemma_12_3_ii_hilbert_series
    {k' S : Type*} [Field k'] [CommRing S] [Algebra k' S]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮] (hconn : IsConnectedGrading k' S 𝒮)
    {M : Type*} [AddCommGroup M] [Module S M] [Module k' M] [IsScalarTower k' S M]
    [Module.Projective S M]
    (ℳ : ℕ → Submodule k' M) (hgr : IsGradedSModule 𝒮 ℳ)
    (hfindim : ∀ i, FiniteDimensional k' (ℳ i)) :
    hilbertSeries ℳ = hilbertSeries 𝒮 * hilbertSeries (quotientGrading 𝒮 ℳ) := by


  have hdim : ∀ m, (Module.finrank k' (ℳ m) : ℤ) =
      ∑ p ∈ Finset.antidiagonal m,
        (Module.finrank k' (𝒮 p.1) : ℤ) * (Module.finrank k' (quotientGrading 𝒮 ℳ p.2) : ℤ) :=
    graded_free_module_dim_conv 𝒮 hconn ℳ hgr hfindim

  apply PowerSeries.ext
  intro m
  rw [PowerSeries.coeff_mul]
  simp only [hilbertSeries, PowerSeries.coeff_mk]
  exact hdim m

theorem lemma_12_3_ii_graded_projective_free
    {k' S : Type*} [Field k'] [CommRing S] [Algebra k' S]
    (𝒮 : ℕ → Submodule k' S) [GradedAlgebra 𝒮] (hconn : IsConnectedGrading k' S 𝒮)
    {M : Type*} [AddCommGroup M] [Module S M] [Module k' M] [IsScalarTower k' S M]
    [Module.Projective S M]
    (ℳ : ℕ → Submodule k' M) (hgr : IsGradedSModule 𝒮 ℳ)
    (hfindim : ∀ i, FiniteDimensional k' (ℳ i)) :
    Module.Free S M ∧
    hilbertSeries ℳ = hilbertSeries (quotientGrading 𝒮 ℳ) * hilbertSeries 𝒮 := by
  constructor
  · exact graded_projective_is_free 𝒮 hconn ℳ hgr
  · rw [mul_comm]
    exact lemma_12_3_ii_hilbert_series 𝒮 hconn ℳ hgr hfindim

attribute [local instance] MvPolynomial.gradedAlgebra

theorem mvpoly_connected_grading :
    @IsConnectedGrading k R _ _ _
      (homogeneousSubmodule (Fin n) k) MvPolynomial.gradedAlgebra := by
  show homogeneousSubmodule (Fin n) k 0 = (Algebra.linearMap k R).range
  ext p
  simp only [mem_homogeneousSubmodule, LinearMap.mem_range]
  constructor
  · intro hp
    refine ⟨coeff 0 p, ?_⟩
    simp only [Algebra.linearMap_apply, algebraMap_eq]
    ext d
    simp only [coeff_C]
    split_ifs with hd
    · exact hd ▸ rfl
    · symm
      exact hp.coeff_eq_zero (by
        intro h
        apply hd
        ext i
        have : Finsupp.degree d = 0 := h
        simp only [Finsupp.degree, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at this
        have hsum := Finset.sum_eq_zero_iff.mp this
        simp only [Finsupp.coe_zero, Pi.zero_apply]
        by_cases hi : i ∈ d.support
        · exact (hsum i hi).symm
        · rw [Finsupp.mem_support_iff, not_not] at hi; exact hi.symm)
  · rintro ⟨c, rfl⟩
    simp only [Algebra.linearMap_apply, algebraMap_eq]
    exact isHomogeneous_C (Fin n) c

structure KoszulComplex (k : Type*) [Field k] (n : ℕ) where
  rank : (p : ℕ) → (hp : p ≤ n) → ℕ
  rank_eq : ∀ (p : ℕ) (hp : p ≤ n), rank p hp = Nat.choose n p
  differential : ∀ (p : ℕ) (hp : 0 < p) (hp' : p ≤ n),
    ((Fin (rank p hp') → MvPolynomial (Fin n) k) →ₗ[MvPolynomial (Fin n) k]
     (Fin (rank (p - 1) (by omega)) → MvPolynomial (Fin n) k))
  d_squared_zero : ∀ (p : ℕ) (hp : 1 < p) (hp' : p ≤ n),
    (differential (p - 1) (by omega) (by omega)).comp
      (differential p (by omega) hp') = 0

theorem split_exact_tensor_preserves_resolution
    (k : Type*) [Field k] (n : ℕ)
    (M : Type*) [AddCommGroup M] [Module (MvPolynomial (Fin n) k) M] :
    ∃ (B_M : Type*)
      (d : ∀ (i : ℕ) (_ : i < n),
        ((Fin (Nat.choose n (i + 1)) × B_M →₀ MvPolynomial (Fin n) k)
          →ₗ[MvPolynomial (Fin n) k]
         (Fin (Nat.choose n i) × B_M →₀ MvPolynomial (Fin n) k)))
      (ε : (Fin (Nat.choose n 0) × B_M →₀ MvPolynomial (Fin n) k)
          →ₗ[MvPolynomial (Fin n) k] M),
      Function.Surjective ε ∧
      (∀ (hn : 0 < n), LinearMap.ker ε = LinearMap.range (d 0 hn)) ∧
      (n = 0 → LinearMap.ker ε = ⊥) ∧
      (∀ (i : ℕ) (hi : i < n) (hi' : i + 1 < n),
        LinearMap.ker (d i hi) = LinearMap.range (d (i + 1) hi')) ∧
      (∀ (hn : 0 < n), Function.Injective (d (n - 1) (by omega))) := by
  exact sorry

theorem prop_12_4_ext_vanishing
    (M : Type*) [AddCommGroup M] [Module R M] :
    ∃ (ι : Fin (n + 1) → Type*)
      (d : ∀ (i : ℕ) (_ : i < n),
        ((ι ⟨i + 1, by omega⟩ →₀ R) →ₗ[R]
         (ι ⟨i, by omega⟩ →₀ R)))
      (ε : (ι ⟨0, by omega⟩ →₀ R) →ₗ[R] M),


      Function.Surjective ε ∧

      (∀ (hn : 0 < n), LinearMap.ker ε = LinearMap.range (d 0 hn)) ∧

      (n = 0 → LinearMap.ker ε = ⊥) ∧

      (∀ (i : ℕ) (hi : i < n) (hi' : i + 1 < n),
        LinearMap.ker (d i hi) = LinearMap.range (d (i + 1) hi')) ∧

      (∀ (hn : 0 < n), Function.Injective (d (n - 1) (by omega))) := by

  obtain ⟨B_M, d, ε, hε_surj, hε_exact, hε_iso, hd_exact, hd_inj⟩ :=
    split_exact_tensor_preserves_resolution k n M

  exact ⟨fun i => Fin (Nat.choose n i.val) × B_M,
    fun i hi => d i hi, ε,
    hε_surj, hε_exact, hε_iso, hd_exact, hd_inj⟩

theorem syzygy_ext_vanishing
    (k : Type*) [Field k] (n : ℕ)
    (M : Type*) [AddCommGroup M] [Module (MvPolynomial (Fin n) k) M]
    [Module.Finite (MvPolynomial (Fin n) k) M] :
    ∃ (r : Fin (n + 1) → ℕ)
      (d : ∀ (i : ℕ) (_ : i < n),
        ((Fin (r ⟨i + 1, by omega⟩) → MvPolynomial (Fin n) k) →ₗ[MvPolynomial (Fin n) k]
         (Fin (r ⟨i, by omega⟩) → MvPolynomial (Fin n) k)))
      (ε : (Fin (r ⟨0, by omega⟩) → MvPolynomial (Fin n) k) →ₗ[MvPolynomial (Fin n) k] M),
      Function.Surjective ε ∧
      (∀ (hn : 0 < n), LinearMap.ker ε = LinearMap.range (d 0 hn)) ∧
      (∀ (i : ℕ) (hi : i < n) (hi' : i + 1 < n),
        LinearMap.ker (d i hi) = LinearMap.range (d (i + 1) hi')) ∧
      (∀ (hn : 0 < n), Function.Injective (d (n - 1) (by omega))) := by
  exact sorry

theorem nth_syzygy_is_free
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (r : Fin (n + 1) → ℕ)
      (d : ∀ (i : ℕ) (_ : i < n),
        ((Fin (r ⟨i + 1, by omega⟩) → R) →ₗ[R]
         (Fin (r ⟨i, by omega⟩) → R)))
      (ε : (Fin (r ⟨0, by omega⟩) → R) →ₗ[R] M),

      Function.Surjective ε ∧

      (∀ (hn : 0 < n), LinearMap.ker ε = LinearMap.range (d 0 hn)) ∧

      (∀ (i : ℕ) (hi : i < n) (hi' : i + 1 < n),
        LinearMap.ker (d i hi) = LinearMap.range (d (i + 1) hi')) ∧

      (∀ (hn : 0 < n), Function.Injective (d (n - 1) (by omega))) :=
  syzygy_ext_vanishing k n M

attribute [local instance] MvPolynomial.gradedAlgebra

def freeModuleGrading (d : ℕ) :
    Submodule k (Fin m → MvPolynomial (Fin n) k) where
  carrier := {f | ∀ i, f i ∈ homogeneousSubmodule (Fin n) k d}
  zero_mem' i := (homogeneousSubmodule (Fin n) k d).zero_mem
  add_mem' ha hb i := (homogeneousSubmodule (Fin n) k d).add_mem (ha i) (hb i)
  smul_mem' c _ ha i := (homogeneousSubmodule (Fin n) k d).smul_mem c (ha i)

def twistedFreeModuleGrading {m : ℕ} (degrees : Fin m → ℕ) (p : ℕ) :
    Submodule k (Fin m → MvPolynomial (Fin n) k) where
  carrier := {f | ∀ j, f j ∈ homogeneousSubmodule (Fin n) k (p - degrees j)}
  zero_mem' j := (homogeneousSubmodule (Fin n) k (p - degrees j)).zero_mem
  add_mem' ha hb j := (homogeneousSubmodule (Fin n) k (p - degrees j)).add_mem (ha j) (hb j)
  smul_mem' c _ ha j := (homogeneousSubmodule (Fin n) k (p - degrees j)).smul_mem c (ha j)


lemma mem_finsuppAntidiag_iff_degree (d : ℕ) (f : Fin n →₀ ℕ) :
    f ∈ (Finset.univ : Finset (Fin n)).finsuppAntidiag d ↔ Finsupp.degree f = d := by
  rw [Finset.mem_finsuppAntidiag]
  simp only [Finset.subset_univ, and_true]
  have key : (Finset.univ : Finset (Fin n)).sum f = Finsupp.degree f := by
    simp [Finsupp.degree]
    exact (Finsupp.sum_fintype f (fun _ => id) (fun _ => rfl)).symm
  rw [key]


noncomputable instance fintypeFinsuppDegreeEq (d : ℕ) :
    Fintype {s : Fin n →₀ ℕ | Finsupp.degree s = d} :=
  Fintype.ofFinset ((Finset.univ : Finset (Fin n)).finsuppAntidiag d)
    (fun f => mem_finsuppAntidiag_iff_degree n d f)


instance instModuleFiniteHomogSub (d : ℕ) :
    Module.Finite k (homogeneousSubmodule (Fin n) k d) := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  exact Module.Finite.equiv (Finsupp.supportedEquivFinsupp _).symm


noncomputable def freeModuleGradingEquiv (m d : ℕ) :
    freeModuleGrading k n (m := m) d ≃ₗ[k]
    (Fin m → ↥(homogeneousSubmodule (Fin n) k d)) where
  toFun f i := ⟨f.val i, f.property i⟩
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  invFun g := ⟨fun i => (g i).val, fun i => (g i).property⟩
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl


lemma finrank_homogeneousSubmodule_eq (d : ℕ) :
    Module.finrank k (homogeneousSubmodule (Fin n) k d) = n.multichoose d := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  have e : ↥(Finsupp.supported k k {s : Fin n →₀ ℕ | Finsupp.degree s = d}) ≃ₗ[k]
      ↥{s : Fin n →₀ ℕ | Finsupp.degree s = d} →₀ k :=
    Finsupp.supportedEquivFinsupp _
  calc Module.finrank k ↥(Finsupp.supported k k {d_1 | Finsupp.degree d_1 = d})
      = Module.finrank k (↥{d_1 : Fin n →₀ ℕ | Finsupp.degree d_1 = d} →₀ k) := e.finrank_eq
    _ = Fintype.card ↥{d_1 : Fin n →₀ ℕ | Finsupp.degree d_1 = d} :=
        Module.finrank_finsupp_self k
    _ = ((Finset.univ : Finset (Fin n)).finsuppAntidiag d).card := Fintype.card_ofFinset ..
    _ = n.multichoose d := by
        rw [Finset.card_finsuppAntidiag_nat_eq_multichoose]; simp [Fintype.card_fin]


lemma hilbertSeries_homogeneousSubmodule :
    hilbertSeries (homogeneousSubmodule (Fin n) k) = (PowerSeries.mk (1 : ℕ → ℤ)) ^ n := by
  cases n with
  | zero =>
    ext d; simp only [hilbertSeries, PowerSeries.coeff_mk, pow_zero, PowerSeries.coeff_one]
    rw [finrank_homogeneousSubmodule_eq]
    cases d <;> simp
  | succ n =>
    ext d
    rw [show PowerSeries.mk (1 : ℕ → ℤ) = PowerSeries.mk 1 from rfl]
    rw [PowerSeries.mk_one_pow_eq_mk_choose_add]
    simp only [hilbertSeries, PowerSeries.coeff_mk]

    rw [finrank_homogeneousSubmodule_eq]
    congr 1
    rw [Nat.multichoose_eq]
    rw [show n + 1 + d - 1 = n + d from by omega]
    exact Nat.choose_symm_of_eq_add (by omega)

theorem hilbert_series_twisted_free_module_poly {m : ℕ} (degrees : Fin m → ℕ) :
    ∃ (p : Polynomial ℤ),
      (1 - PowerSeries.X : PowerSeries ℤ) ^ n *
        hilbertSeries (twistedFreeModuleGrading k n degrees) =
        Polynomial.toPowerSeries p := by
  exact sorry

theorem hilbert_syzygy_graded_free_resolution
    {M : Type*} [AddCommGroup M] [Module (MvPolynomial (Fin n) k) M]
    [Module k M] [IsScalarTower k (MvPolynomial (Fin n) k) M]
    [Module.Finite (MvPolynomial (Fin n) k) M]
    (ℳ : ℕ → Submodule k M)
    (hgr : IsGradedSModule (homogeneousSubmodule (Fin n) k) ℳ) :
    ∃ (r : Fin (n + 1) → ℕ)
      (shifts : (i : Fin (n + 1)) → Fin (r i) → ℕ)
      (d : ∀ (i : ℕ) (hi : i < n),
        ((Fin (r ⟨i + 1, by omega⟩) → MvPolynomial (Fin n) k) →ₗ[MvPolynomial (Fin n) k]
         (Fin (r ⟨i, by omega⟩) → MvPolynomial (Fin n) k)))
      (ε : (Fin (r ⟨0, by omega⟩) → MvPolynomial (Fin n) k) →ₗ[MvPolynomial (Fin n) k] M),

      Function.Surjective ε ∧

      (∀ (hn : 0 < n), LinearMap.ker ε = LinearMap.range (d 0 hn)) ∧

      (n = 0 → LinearMap.ker ε = ⊥) ∧

      (∀ (i : ℕ) (hi : i < n) (hi' : i + 1 < n),
        LinearMap.ker (d i hi) = LinearMap.range (d (i + 1) hi')) ∧

      (∀ (hn : 0 < n), Function.Injective (d (n - 1) (by omega))) ∧

      (∀ (i : ℕ) (hi : i < n) (p : ℕ)
        (v : Fin (r ⟨i + 1, by omega⟩) → MvPolynomial (Fin n) k),
        v ∈ (twistedFreeModuleGrading k n (shifts ⟨i + 1, Nat.succ_lt_succ hi⟩) p : Set _) →
        d i hi v ∈ (twistedFreeModuleGrading k n (shifts ⟨i, Nat.lt_succ_of_lt hi⟩) p : Set _)) ∧

      (∀ (p : ℕ)
        (v : Fin (r ⟨0, by omega⟩) → MvPolynomial (Fin n) k),
        v ∈ (twistedFreeModuleGrading k n (shifts ⟨0, Nat.zero_lt_succ n⟩) p : Set _) → ε v ∈ ℳ p) := by
  exact sorry

theorem graded_euler_characteristic_telescope
    {M : Type*} [AddCommGroup M] [Module (MvPolynomial (Fin n) k) M]
    [Module k M] [IsScalarTower k (MvPolynomial (Fin n) k) M]
    (ℳ : ℕ → Submodule k M)
    (hgr : IsGradedSModule (homogeneousSubmodule (Fin n) k) ℳ)
    (hfindim : ∀ i, FiniteDimensional k (ℳ i))
    (r : Fin (n + 1) → ℕ)
    (shifts : (i : Fin (n + 1)) → Fin (r i) → ℕ)
    (d : ∀ (i : ℕ) (hi : i < n),
      ((Fin (r ⟨i + 1, by omega⟩) → MvPolynomial (Fin n) k) →ₗ[MvPolynomial (Fin n) k]
       (Fin (r ⟨i, by omega⟩) → MvPolynomial (Fin n) k)))
    (ε : (Fin (r ⟨0, by omega⟩) → MvPolynomial (Fin n) k) →ₗ[MvPolynomial (Fin n) k] M)
    (hε_surj : Function.Surjective ε)
    (hε_exact : ∀ (hn : 0 < n), LinearMap.ker ε = LinearMap.range (d 0 hn))
    (hε_zero : n = 0 → LinearMap.ker ε = ⊥)
    (hd_exact : ∀ (i : ℕ) (hi : i < n) (hi' : i + 1 < n),
      LinearMap.ker (d i hi) = LinearMap.range (d (i + 1) hi'))
    (hd_inj : ∀ (hn : 0 < n), Function.Injective (d (n - 1) (by omega)))
    (hd_graded : ∀ (i : ℕ) (hi : i < n) (p : ℕ)
      (v : Fin (r ⟨i + 1, by omega⟩) → MvPolynomial (Fin n) k),
      v ∈ (twistedFreeModuleGrading k n (shifts ⟨i + 1, Nat.succ_lt_succ hi⟩) p : Set _) →
      d i hi v ∈ (twistedFreeModuleGrading k n (shifts ⟨i, Nat.lt_succ_of_lt hi⟩) p : Set _))
    (hε_graded : ∀ (p : ℕ)
      (v : Fin (r ⟨0, by omega⟩) → MvPolynomial (Fin n) k),
      v ∈ (twistedFreeModuleGrading k n (shifts ⟨0, Nat.zero_lt_succ n⟩) p : Set _) → ε v ∈ ℳ p)

    (p : ℕ) :
    ∃ (b : ℕ → ℤ),
      b 0 = (Module.finrank k ↥(ℳ p) : ℤ) ∧
      b (n + 1) = 0 ∧
      ∀ j : Fin (n + 1),
        (Module.finrank k ↥(twistedFreeModuleGrading k n (shifts j) p) : ℤ) = b j.val + b (j.val + 1) := by
  exact sorry

lemma alternating_sum_general' (nn : ℕ) (b : ℕ → ℤ) :
    ∑ j : Fin (nn + 1), (-1 : ℤ) ^ j.val * (b j.val + b (j.val + 1)) =
    b 0 + (-1 : ℤ) ^ nn * b (nn + 1) := by
  induction nn with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]; ring

lemma alternating_sum_eq' (nn : ℕ) (a : Fin (nn + 1) → ℤ) (target : ℤ)
    (b : ℕ → ℤ) (hb0 : b 0 = target) (hbn : b (nn + 1) = 0)
    (hab : ∀ j : Fin (nn + 1), a j = b j.val + b (j.val + 1)) :
    ∑ j : Fin (nn + 1), (-1 : ℤ) ^ j.val * a j = target := by
  have : ∑ j : Fin (nn + 1), (-1 : ℤ) ^ j.val * a j =
    ∑ j : Fin (nn + 1), (-1 : ℤ) ^ j.val * (b j.val + b (j.val + 1)) := by
    congr 1; ext j; rw [hab j]
  rw [this, alternating_sum_general', hbn, mul_zero, add_zero, hb0]


set_option maxHeartbeats 8000000 in
theorem resolution_hilbert_alternating_sum
    {M : Type*} [AddCommGroup M] [Module (MvPolynomial (Fin n) k) M]
    [Module k M] [IsScalarTower k (MvPolynomial (Fin n) k) M]
    (ℳ : ℕ → Submodule k M)
    (hgr : IsGradedSModule (homogeneousSubmodule (Fin n) k) ℳ)
    (hfindim : ∀ i, FiniteDimensional k (ℳ i))
    (r : Fin (n + 1) → ℕ)
    (shifts : (i : Fin (n + 1)) → Fin (r i) → ℕ)
    (d : ∀ (i : ℕ) (hi : i < n),
      ((Fin (r ⟨i + 1, by omega⟩) → MvPolynomial (Fin n) k) →ₗ[MvPolynomial (Fin n) k]
       (Fin (r ⟨i, by omega⟩) → MvPolynomial (Fin n) k)))
    (ε : (Fin (r ⟨0, by omega⟩) → MvPolynomial (Fin n) k) →ₗ[MvPolynomial (Fin n) k] M)
    (hε_surj : Function.Surjective ε)
    (hε_exact : ∀ (hn : 0 < n), LinearMap.ker ε = LinearMap.range (d 0 hn))
    (hε_zero : n = 0 → LinearMap.ker ε = ⊥)
    (hd_exact : ∀ (i : ℕ) (hi : i < n) (hi' : i + 1 < n),
      LinearMap.ker (d i hi) = LinearMap.range (d (i + 1) hi'))
    (hd_inj : ∀ (hn : 0 < n), Function.Injective (d (n - 1) (by omega)))

    (hd_graded : ∀ (i : ℕ) (hi : i < n) (p : ℕ)
      (v : Fin (r ⟨i + 1, by omega⟩) → MvPolynomial (Fin n) k),
      v ∈ (twistedFreeModuleGrading k n (shifts ⟨i + 1, Nat.succ_lt_succ hi⟩) p : Set _) →
      d i hi v ∈ (twistedFreeModuleGrading k n (shifts ⟨i, Nat.lt_succ_of_lt hi⟩) p : Set _))
    (hε_graded : ∀ (p : ℕ)
      (v : Fin (r ⟨0, by omega⟩) → MvPolynomial (Fin n) k),
      v ∈ (twistedFreeModuleGrading k n (shifts ⟨0, Nat.zero_lt_succ n⟩) p : Set _) → ε v ∈ ℳ p) :

    hilbertSeries ℳ =
      ∑ j : Fin (n + 1),
        ((-1 : ℤ) ^ j.val) • hilbertSeries (twistedFreeModuleGrading k n (shifts j)) := by

  apply PowerSeries.ext; intro p

  simp only [hilbertSeries, map_sum, map_zsmul, PowerSeries.coeff_mk, smul_eq_mul]

  obtain ⟨b, hb0, hbn, hab⟩ := graded_euler_characteristic_telescope k n ℳ hgr hfindim
    r shifts d ε hε_surj hε_exact hε_zero hd_exact hd_inj hd_graded hε_graded p

  symm
  exact alternating_sum_eq' n
    (fun j => (Module.finrank k ↥(twistedFreeModuleGrading k n (shifts j) p) : ℤ))
    (Module.finrank k ↥(ℳ p) : ℤ)
    b hb0 hbn hab

theorem free_resolution_euler_char
    {M : Type*} [AddCommGroup M] [Module (MvPolynomial (Fin n) k) M]
    [Module k M] [IsScalarTower k (MvPolynomial (Fin n) k) M]
    [Module.Finite (MvPolynomial (Fin n) k) M]
    (ℳ : ℕ → Submodule k M)
    (hgr : IsGradedSModule (homogeneousSubmodule (Fin n) k) ℳ)
    (hfindim : ∀ i, FiniteDimensional k (ℳ i))
    (r : Fin (n + 1) → ℕ)
    (shifts : (i : Fin (n + 1)) → Fin (r i) → ℕ)
    (d : ∀ (i : ℕ) (hi : i < n),
      ((Fin (r ⟨i + 1, by omega⟩) → MvPolynomial (Fin n) k) →ₗ[MvPolynomial (Fin n) k]
       (Fin (r ⟨i, by omega⟩) → MvPolynomial (Fin n) k)))
    (ε : (Fin (r ⟨0, by omega⟩) → MvPolynomial (Fin n) k) →ₗ[MvPolynomial (Fin n) k] M)
    (hε_surj : Function.Surjective ε)
    (hε_exact : ∀ (hn : 0 < n), LinearMap.ker ε = LinearMap.range (d 0 hn))
    (hε_zero : n = 0 → LinearMap.ker ε = ⊥)
    (hd_exact : ∀ (i : ℕ) (hi : i < n) (hi' : i + 1 < n),
      LinearMap.ker (d i hi) = LinearMap.range (d (i + 1) hi'))
    (hd_inj : ∀ (hn : 0 < n), Function.Injective (d (n - 1) (by omega)))
    (hd_graded : ∀ (i : ℕ) (hi : i < n) (p : ℕ)
      (v : Fin (r ⟨i + 1, by omega⟩) → MvPolynomial (Fin n) k),
      v ∈ (twistedFreeModuleGrading k n (shifts ⟨i + 1, Nat.succ_lt_succ hi⟩) p : Set _) →
      d i hi v ∈ (twistedFreeModuleGrading k n (shifts ⟨i, Nat.lt_succ_of_lt hi⟩) p : Set _))
    (hε_graded : ∀ (p : ℕ)
      (v : Fin (r ⟨0, by omega⟩) → MvPolynomial (Fin n) k),
      v ∈ (twistedFreeModuleGrading k n (shifts ⟨0, Nat.zero_lt_succ n⟩) p : Set _) → ε v ∈ ℳ p) :

    ∃ (p : Polynomial ℤ),
      (1 - PowerSeries.X : PowerSeries ℤ) ^ n * hilbertSeries ℳ =
        Polynomial.toPowerSeries p := by

  have halt := resolution_hilbert_alternating_sum k n ℳ hgr hfindim r shifts d ε
    hε_surj hε_exact hε_zero hd_exact hd_inj hd_graded hε_graded

  choose pj hpj using fun j : Fin (n + 1) =>
    hilbert_series_twisted_free_module_poly k n (shifts j)

  rw [halt, Finset.mul_sum]
  simp_rw [mul_comm ((1 - PowerSeries.X : PowerSeries ℤ) ^ n), smul_mul_assoc,
    mul_comm _ ((1 - PowerSeries.X : PowerSeries ℤ) ^ n), hpj]

  refine ⟨∑ x : Fin (n + 1), (-1 : ℤ) ^ x.val • pj x, ?_⟩
  show ∑ x : Fin (n + 1), (-1 : ℤ) ^ x.val • (Polynomial.coeToPowerSeries.algHom ℤ) (pj x) =
    (Polynomial.coeToPowerSeries.algHom ℤ) (∑ x, (-1 : ℤ) ^ x.val • pj x)
  simp_rw [map_sum, map_smul]

theorem hilbert_syzygy_theorem
    {M : Type*} [AddCommGroup M] [Module R M] [Module k M]
    [IsScalarTower k R M]
    [Module.Finite R M]
    (ℳ : ℕ → Submodule k M)
    (hgr : IsGradedSModule (homogeneousSubmodule (Fin n) k) ℳ)
    (hfindim : ∀ i, FiniteDimensional k (ℳ i)) :
    ∃ (p : Polynomial ℤ),
      (1 - PowerSeries.X : PowerSeries ℤ) ^ n * hilbertSeries ℳ =
        Polynomial.toPowerSeries p := by

  obtain ⟨r, shifts, d, ε, hε_surj, hε_exact, hε_zero, hd_exact, hd_inj, hd_graded, hε_graded⟩ :=
    hilbert_syzygy_graded_free_resolution k n ℳ hgr

  exact free_resolution_euler_char k n ℳ hgr hfindim r shifts d ε hε_surj hε_exact hε_zero hd_exact hd_inj hd_graded hε_graded

theorem lemma_12_6_krull_dim_quotient
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A) :
    ringKrullDim A ≤ ringKrullDim (A ⧸ Ideal.span {f}) + 1 := by
  have h : ({f} : Set A) ⊆ ↑(Ring.jacobson A) := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact Set.singleton_subset_iff.mpr hf
  have := ringKrullDim_le_ringKrullDim_quotient_add_encard {f} h
  simp [Set.encard_singleton] at this
  exact this

theorem polynomial_height_add_coheight_ge
    (S : Type*) [CommRing S] [IsNoetherianRing S] [FiniteRingKrullDim S]
    (Q : PrimeSpectrum (Polynomial S)) :
    (1 : ℕ∞) + ringKrullDim S ≤ ↑(Order.height Q + Order.coheight Q) := by


  sorry

lemma mvPolynomial_height_add_coheight_ge
    (k : Type*) [Field k] (n : ℕ)
    (pp : PrimeSpectrum (MvPolynomial (Fin n) k)) :
    (n : ℕ∞) ≤ Order.height pp + Order.coheight pp := by
  induction n with
  | zero => exact bot_le
  | succ n ih =>
    let S := MvPolynomial (Fin n) k

    let e : PrimeSpectrum (Polynomial S) ≃o PrimeSpectrum (MvPolynomial (Fin (n + 1)) k) :=
      (PrimeSpectrum.comapEquiv (MvPolynomial.finSuccEquiv k n).toRingEquiv).symm
    let Q := e.symm pp
    have hh : Order.height pp = Order.height Q := by
      conv_lhs => rw [show pp = e Q from (e.apply_symm_apply pp).symm]
      exact Order.height_orderIso e Q
    have hc : Order.coheight pp = Order.coheight Q := by
      conv_lhs => rw [show pp = e Q from (e.apply_symm_apply pp).symm]
      exact Order.coheight_orderIso e Q
    rw [hh, hc]

    haveI : FiniteRingKrullDim S := by
      rw [finiteRingKrullDim_iff_ne_bot_and_top]
      rw [show ringKrullDim S = ringKrullDim (MvPolynomial (Fin n) k) from rfl,
          MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
      simp only [zero_add, ne_eq]
      exact ⟨WithBot.coe_ne_bot,
             fun h => absurd (WithBot.coe_injective h) (WithTop.natCast_ne_top _)⟩
    have hQ := polynomial_height_add_coheight_ge S Q
    have hdim : ringKrullDim S = (n : WithBot ℕ∞) := by
      show ringKrullDim (MvPolynomial (Fin n) k) = _
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]
      simp [ringKrullDim_eq_zero_of_field]
    rw [hdim] at hQ
    rw [show n + 1 = 1 + n from by omega]
    norm_cast at hQ ⊢

theorem catenary_inequality_polynomial_ring
    (k : Type*) [Field k] (n : ℕ)
    (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] :
    ringKrullDim (MvPolynomial (Fin n) k) ≤
      ringKrullDim (MvPolynomial (Fin n) k ⧸ p) + p.height := by
  set Rp := MvPolynomial (Fin n) k with hRp_def
  let pp : PrimeSpectrum Rp := ⟨p, inferInstance⟩

  have h_quot_eq : ringKrullDim (Rp ⧸ p) = ↑(Order.coheight pp) := by
    rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]; congr 1

  have h_ht_eq : p.height = Order.height pp := by
    rw [Ideal.height_eq_primeHeight, Ideal.primeHeight]

  have h_dim : ringKrullDim Rp = (n : WithBot ℕ∞) := by
    show ringKrullDim (MvPolynomial (Fin n) k) = (n : WithBot ℕ∞)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
        ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin]

  have h_cat := mvPolynomial_height_add_coheight_ge k n pp

  rw [h_dim, h_quot_eq, h_ht_eq, ← WithBot.coe_add, add_comm]
  exact WithBot.coe_le_coe.mpr h_cat

theorem polynomial_ring_dimension_formula
    (k : Type*) [Field k] (n : ℕ)
    (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] :
    (n : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) k ⧸ p) + p.height := by
  have h1 : ringKrullDim (MvPolynomial (Fin n) k) = (n : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
        zero_add, Nat.card_fin]
  have h2 : ringKrullDim (MvPolynomial (Fin n) k) ≤
      ringKrullDim (MvPolynomial (Fin n) k ⧸ p) + p.height :=
    catenary_inequality_polynomial_ring k n p
  rw [← h1]
  exact h2

theorem cor_12_7_dim_irred_component
    (_hk : IsAlgClosed k) (m : ℕ)
    (f : Fin m → R)
    (_hhom : ∀ i, ∃ (d : ℕ), 0 < d ∧
      ∀ (s : Fin n →₀ ℕ), MvPolynomial.coeff s (f i) ≠ 0 →
        (s.sum fun _ e => e) = d)
    (p : Ideal R)
    (hp : p ∈ (Ideal.span (Set.range f)).minimalPrimes) :
    (n : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) + (m : ℕ∞) := by
  haveI : p.IsPrime := Ideal.minimalPrimes_isPrime hp

  have hdim := polynomial_ring_dimension_formula k n p

  have hht : p.height ≤ m := by
    have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span (Set.finite_range f) hp
    have h2 := Set.ncard_image_le (s := Set.univ) (f := f) (Set.finite_univ)
    rw [Set.image_univ] at h2
    simp only [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h2

    exact h1.trans (by exact_mod_cast h2)

  calc (n : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ p) + p.height := hdim
    _ ≤ ringKrullDim (R ⧸ p) + (m : ℕ∞) := by gcongr; exact_mod_cast hht

lemma image_castSucc_eq_image {A : Type*} {k : ℕ} (f : Fin (k + 1) → A) (j : Fin k) :
    Set.image (f ∘ Fin.castSucc) {i : Fin k | (i : ℕ) < (j : ℕ)} =
    Set.image f {i : Fin (k + 1) | (i : ℕ) < (Fin.castSucc j : ℕ)} := by
  ext x
  simp only [Set.mem_image, Set.mem_setOf_eq, Function.comp]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨Fin.castSucc i, by simp [Fin.castSucc, hi], rfl⟩
  · rintro ⟨i, hi, rfl⟩
    have hik : (i : ℕ) < k := by
      have := j.isLt; simp [Fin.castSucc] at hi; omega
    exact ⟨⟨i, hik⟩, by simp [Fin.castSucc] at hi ⊢; exact hi, by simp [Fin.castSucc]⟩

lemma isRegularSequence_init {A : Type*} [CommRing A] {k : ℕ}
    {f : Fin (k + 1) → A} (hreg : IsRegularSequence f) :
    IsRegularSequence (f ∘ Fin.castSucc) := by
  obtain ⟨hnzd, hnt⟩ := hreg
  constructor
  · intro j r hr
    suffices h : ∀ (I : Ideal A)
      (hI : I = Ideal.span (Set.image (f ∘ Fin.castSucc) {i : Fin k | (i : ℕ) < (j : ℕ)})),
      ∀ (r : A ⧸ I), r ≠ 0 → (Ideal.Quotient.mk I ((f ∘ Fin.castSucc) j)) • r ≠ 0 by
      exact h _ rfl r hr
    intro I hI r' hr'
    subst hI
    have hImgEq := image_castSucc_eq_image f j
    suffices h2 : ∀ (I : Ideal A)
      (hI : I = Ideal.span (Set.image f {i : Fin (k + 1) | (i : ℕ) < (Fin.castSucc j : ℕ)})),
      ∀ (r : A ⧸ I), r ≠ 0 → (Ideal.Quotient.mk I ((f ∘ Fin.castSucc) j)) • r ≠ 0 by
      exact h2 _ (by rw [← hImgEq]) r' hr'
    intro I' hI' r'' hr''
    subst hI'
    exact hnzd (Fin.castSucc j) r'' hr''
  · have hsub : Ideal.span (Set.range (f ∘ Fin.castSucc)) ≤ Ideal.span (Set.range f) := by
      apply Ideal.span_mono; intro x ⟨i, hi⟩; exact ⟨Fin.castSucc i, hi⟩
    rw [Ideal.Quotient.nontrivial_iff] at hnt ⊢
    exact ne_top_of_le_ne_top hnt hsub

section KoszulHelpers

variable {A : Type*} [CommRing A]

def koszulProjL (b c : ℕ) : (Fin (b + c) → A) →ₗ[A] (Fin b → A) where
  toFun v i := v (Fin.castAdd c i); map_add' _ _ := rfl; map_smul' _ _ := rfl

def koszulProjR (b c : ℕ) : (Fin (b + c) → A) →ₗ[A] (Fin c → A) where
  toFun v i := v (Fin.natAdd b i); map_add' _ _ := rfl; map_smul' _ _ := rfl

def koszulReindex {a b : ℕ} (h : a = b) : (Fin a → A) →ₗ[A] (Fin b → A) where
  toFun v i := v (Fin.cast h.symm i); map_add' _ _ := rfl; map_smul' _ _ := rfl

def koszulSmulLM (a_val : A) (k : ℕ) : (Fin k → A) →ₗ[A] (Fin k → A) where
  toFun v i := a_val * v i
  map_add' v w := by ext; simp [mul_add]
  map_smul' r v := by ext; simp [smul_eq_mul, mul_left_comm]

def koszulInjectL (b c : ℕ) : (Fin b → A) →ₗ[A] (Fin (b + c) → A) where
  toFun u := Fin.addCases u (fun _ => 0)
  map_add' u₁ u₂ := by ext ⟨i, hi⟩; by_cases h : i < b <;> simp [Fin.addCases, h]
  map_smul' r u := by ext ⟨i, hi⟩; by_cases h : i < b <;> simp [Fin.addCases, h, smul_eq_mul]

def koszulInjectR (b c : ℕ) : (Fin c → A) →ₗ[A] (Fin (b + c) → A) where
  toFun w := Fin.addCases (fun _ => 0) w
  map_add' w₁ w₂ := by ext ⟨i, hi⟩; by_cases h : i < b <;> simp [Fin.addCases, h]
  map_smul' r w := by ext ⟨i, hi⟩; by_cases h : i < b <;> simp [Fin.addCases, h, smul_eq_mul]

noncomputable def koszulDSafe (n : ℕ)
    (d' : ∀ i, i < n → (Fin (n.choose (i+1)) → A) →ₗ[A] (Fin (n.choose i) → A))
    (p : ℕ) : (Fin (n.choose (p+1)) → A) →ₗ[A] (Fin (n.choose p) → A) :=
  if h : p < n then d' p h else 0

end KoszulHelpers

section KoszulConeDiff

variable {A : Type*} [CommRing A]

noncomputable def koszulConeDiff0 (n : ℕ) (hn : 0 < n)
    (d' : ∀ i, i < n → (Fin (n.choose (i+1)) → A) →ₗ[A] (Fin (n.choose i) → A))
    (a : A) : (Fin ((n+1).choose 1) → A) →ₗ[A] (Fin ((n+1).choose 0) → A) :=
  let h_s := Nat.choose_succ_succ n 0
  have h_t : n.choose 0 = (n+1).choose 0 := by simp [Nat.choose_zero_right]
  (koszulReindex h_t).comp (
    (-(koszulSmulLM a (n.choose 0))).comp ((koszulProjL (n.choose 0) (n.choose 1)).comp (koszulReindex h_s)) +
    (d' 0 hn).comp ((koszulProjR (n.choose 0) (n.choose 1)).comp (koszulReindex h_s)))

noncomputable def koszulConeDiffSucc (n p' : ℕ) (hp' : p' < n)
    (d' : ∀ i, i < n → (Fin (n.choose (i+1)) → A) →ₗ[A] (Fin (n.choose i) → A))
    (a : A) : (Fin ((n+1).choose (p'+2)) → A) →ₗ[A] (Fin ((n+1).choose (p'+1)) → A) :=
  (koszulReindex (Nat.choose_succ_succ n p').symm).comp (
    (koszulInjectL (n.choose p') (n.choose (p'+1))).comp
      ((d' p' hp').comp ((koszulProjL (n.choose (p'+1)) (n.choose (p'+2))).comp
        (koszulReindex (Nat.choose_succ_succ n (p'+1))))) +
    (koszulInjectR (n.choose p') (n.choose (p'+1))).comp (
      (koszulSmulLM ((-1 : A) ^ (p' + 2) * a) (n.choose (p'+1))).comp
        ((koszulProjL (n.choose (p'+1)) (n.choose (p'+2))).comp
          (koszulReindex (Nat.choose_succ_succ n (p'+1)))) +
      (koszulDSafe n d' (p'+1)).comp
        ((koszulProjR (n.choose (p'+1)) (n.choose (p'+2))).comp
          (koszulReindex (Nat.choose_succ_succ n (p'+1))))))

noncomputable def koszulConeDiff (n : ℕ) (hn : 0 < n)
    (d' : ∀ i, i < n → (Fin (n.choose (i+1)) → A) →ₗ[A] (Fin (n.choose i) → A))
    (a : A) : (p : ℕ) → (hp : p < n + 1) →
    (Fin ((n+1).choose (p+1)) → A) →ₗ[A] (Fin ((n+1).choose p) → A)
  | 0, _ => koszulConeDiff0 n hn d' a
  | p + 1, hp => koszulConeDiffSucc n p (Nat.lt_of_succ_lt_succ hp) d' a

end KoszulConeDiff

section KoszulBlockLemmas

variable {A : Type*} [CommRing A]

end KoszulBlockLemmas

section KoszulConeExactness
omit k n

theorem koszulCone_exactness
    {A : Type*} [CommRing A] {n : ℕ} (hn : 0 < n)
    (f : Fin (n + 1) → A)
    (hreg : IsRegularSequence f)
    (d' : ∀ i, i < n → (Fin (n.choose (i+1)) → A) →ₗ[A] (Fin (n.choose i) → A))
    (ε' : (Fin (n.choose 0) → A) →ₗ[A] A ⧸ Ideal.span (Set.range (f ∘ Fin.castSucc)))
    (hε'_surj : Function.Surjective ε')
    (hε'_exact : ∀ (hm : 0 < n), LinearMap.ker ε' = LinearMap.range (d' 0 hm))
    (hε'_exact_top : n = 0 → LinearMap.ker ε' = ⊥)
    (hd'_exact : ∀ (i : ℕ) (hi : i < n) (hi' : i + 1 < n),
      LinearMap.ker (d' i hi) = LinearMap.range (d' (i + 1) hi'))
    (hd'_inj : ∀ (hm : 0 < n), Function.Injective (d' (n - 1) (by omega)))
    (a : A) (ha : a = f (Fin.last n)) :
    let d := fun i (hi : i < n + 1) => koszulConeDiff n hn d' a i (by omega : i < n + 1)
    let h_choose0 : 0 < (n + 1).choose 0 := by simp [Nat.choose_zero_right]
    let ε : (Fin ((n + 1).choose 0) → A) →ₗ[A] A ⧸ Ideal.span (Set.range f) :=
      { toFun := fun v => Ideal.Quotient.mk _ (v ⟨0, h_choose0⟩)
        map_add' := fun v w => by simp [map_add]
        map_smul' := fun r v => rfl }

    (∀ (hm : 0 < n + 1), LinearMap.ker ε = LinearMap.range (d 0 hm)) ∧

    (∀ (i : ℕ) (hi : i < n + 1) (hi' : i + 1 < n + 1),
      LinearMap.ker (d i hi) = LinearMap.range (d (i + 1) hi')) ∧

    (∀ (hm : 0 < n + 1), Function.Injective (d ((n + 1) - 1) (by omega))) := by


  refine ⟨?_, ?_, ?_⟩
  ·


    exact sorry
  ·


    exact sorry
  ·

    exact sorry

end KoszulConeExactness

theorem lemma_12_8_koszul_exact
    {A : Type*} [CommRing A] {m : ℕ}
    (f : Fin m → A) (hreg : IsRegularSequence f) :
    ∃ (d : ∀ (i : ℕ) (_ : i < m),
        ((Fin (Nat.choose m (i + 1)) → A) →ₗ[A]
         (Fin (Nat.choose m i) → A)))
      (ε : (Fin (Nat.choose m 0) → A) →ₗ[A]
        (A ⧸ Ideal.span (Set.range f))),

      Function.Surjective ε ∧

      (∀ (hm : 0 < m), LinearMap.ker ε = LinearMap.range (d 0 hm)) ∧

      (m = 0 → LinearMap.ker ε = ⊥) ∧

      (∀ (i : ℕ) (hi : i < m) (hi' : i + 1 < m),
        LinearMap.ker (d i hi) = LinearMap.range (d (i + 1) hi')) ∧

      (∀ (hm : 0 < m), Function.Injective (d (m - 1) (by omega))) := by
  induction m with
  | zero =>


    have hrange : Set.range f = ∅ := Set.range_eq_empty f
    have hspan : Ideal.span (Set.range f) = ⊥ := by rw [hrange, Ideal.span_empty]

    have h01 : (0 : ℕ) < Nat.choose 0 0 := by decide

    let ε : (Fin (Nat.choose 0 0) → A) →ₗ[A] (A ⧸ Ideal.span (Set.range f)) :=
      { toFun := fun v => Ideal.Quotient.mk _ (v ⟨0, h01⟩)
        map_add' := fun v w => by simp [map_add]
        map_smul' := fun r v => rfl }

    refine ⟨fun i hi => absurd hi (by omega), ε, ?_, ?_, ?_, ?_, ?_⟩
    ·
      intro x
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨fun _ => a, rfl⟩
    ·
      intro hm; exact absurd hm (by omega)
    ·
      intro _
      ext v
      simp only [LinearMap.mem_ker, Submodule.mem_bot]
      constructor
      · intro h
        change (Ideal.Quotient.mk _) (v ⟨0, h01⟩) = 0 at h
        rw [Ideal.Quotient.eq_zero_iff_mem, hspan] at h
        simp only [Ideal.mem_bot] at h
        ext ⟨i, hi⟩
        have : i = 0 := by
          have := Nat.choose_zero_right 0
          omega
        subst this
        exact h
      · intro h
        show (Ideal.Quotient.mk _) (v ⟨0, h01⟩) = 0
        have : v = 0 := h
        rw [this]; simp
    ·
      intro i hi; exact absurd hi (by omega)
    ·
      intro hm; exact absurd hm (by omega)
  | succ k ih =>

    obtain ⟨d', ε', hε'_surj, hε'_exact, hε'_exact_top, hd'_exact, hd'_inj⟩ :=
      ih (f ∘ Fin.castSucc) (isRegularSequence_init hreg)
    rcases k with _ | k'
    ·


      have h01 : (0 : ℕ) < Nat.choose 1 0 := by decide
      have h11 : (0 : ℕ) < Nat.choose 1 1 := by decide

      let d : ∀ (i : ℕ) (_ : i < 1),
          ((Fin (Nat.choose 1 (i + 1)) → A) →ₗ[A] (Fin (Nat.choose 1 i) → A)) :=
        fun i hi => by
          have hi0 : i = 0 := by omega
          subst hi0
          exact {
            toFun := fun v => fun j => f ⟨0, by decide⟩ * v ⟨0, h11⟩
            map_add' := fun v w => by ext; simp [mul_add]
            map_smul' := fun r v => by ext; simp [smul_eq_mul, mul_left_comm]
          }

      let ε : (Fin (Nat.choose 1 0) → A) →ₗ[A] (A ⧸ Ideal.span (Set.range f)) :=
        { toFun := fun v => Ideal.Quotient.mk _ (v ⟨0, h01⟩)
          map_add' := fun v w => by simp [map_add]
          map_smul' := fun r v => rfl }
      refine ⟨d, ε, ?_, ?_, ?_, ?_, ?_⟩
      ·
        intro x; obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact ⟨fun _ => a, rfl⟩
      ·
        intro hm
        ext v
        simp only [LinearMap.mem_ker, LinearMap.mem_range]
        constructor
        ·
          intro hv
          change (Ideal.Quotient.mk _) (v ⟨0, h01⟩) = 0 at hv
          rw [Ideal.Quotient.eq_zero_iff_mem] at hv

          have hrange1 : Set.range f = {f ⟨0, by decide⟩} := by
            ext x; simp only [Set.mem_range, Set.mem_singleton_iff]
            constructor
            · rintro ⟨i, rfl⟩; congr 1; exact Fin.ext (Fin.val_eq_zero i)
            · intro h; exact ⟨⟨0, by decide⟩, h.symm⟩
          rw [hrange1, Ideal.mem_span_singleton] at hv
          obtain ⟨c, hc⟩ := hv
          refine ⟨fun _ => c, ?_⟩
          ext ⟨j, hj⟩
          have hj0 : j = 0 := by simp [Nat.choose] at hj; omega
          subst hj0
          show f ⟨0, _⟩ * c = v ⟨0, h01⟩
          rw [hc, mul_comm]
        ·
          rintro ⟨w, rfl⟩
          show (Ideal.Quotient.mk _) (d 0 hm w ⟨0, h01⟩) = 0
          change (Ideal.Quotient.mk _) (f ⟨0, _⟩ * w ⟨0, h11⟩) = 0
          rw [Ideal.Quotient.eq_zero_iff_mem]
          have hrange1 : Set.range f = {f ⟨0, by decide⟩} := by
            ext x; simp only [Set.mem_range, Set.mem_singleton_iff]
            constructor
            · rintro ⟨i, rfl⟩; congr 1; exact Fin.ext (Fin.val_eq_zero i)
            · intro h; exact ⟨⟨0, by decide⟩, h.symm⟩
          rw [hrange1, Ideal.mem_span_singleton]
          exact ⟨w ⟨0, h11⟩, rfl⟩
      ·
        intro h; exact absurd h (by omega)
      ·
        intro i hi hi'; exact absurd hi' (by omega)
      ·
        intro hm v w hvw

        have hsub : f ⟨0, by decide⟩ * (v ⟨0, h11⟩ - w ⟨0, h11⟩) = 0 := by
          have : f ⟨0, by decide⟩ * v ⟨0, h11⟩ = f ⟨0, by decide⟩ * w ⟨0, h11⟩ :=
            congr_fun hvw ⟨0, h01⟩
          rw [mul_sub, this, sub_self]

        obtain ⟨hnzd, _⟩ := hreg
        specialize hnzd ⟨0, by decide⟩
        have hI : Ideal.span (Set.image f {i : Fin 1 | (i : ℕ) < (⟨0, by decide⟩ : Fin 1).val}) = ⊥ := by
          have : Set.image f {i : Fin 1 | (i : ℕ) < (⟨0, by decide⟩ : Fin 1).val} = ∅ := by simp
          rw [this, Ideal.span_empty]

        suffices h0 : v ⟨0, h11⟩ = w ⟨0, h11⟩ by
          ext ⟨i, hi⟩
          have : i = 0 := by simp [Nat.choose] at hi; omega
          subst this; exact h0

        by_contra hne
        have hmk_ne : (Ideal.Quotient.mk (Ideal.span (Set.image f {i : Fin 1 | (i : ℕ) < (⟨0, by decide⟩ : Fin 1).val}))) (v ⟨0, h11⟩ - w ⟨0, h11⟩) ≠ 0 := by
          rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_bot, sub_eq_zero]
          exact hne
        exact hnzd _ hmk_ne (by
          show (Ideal.Quotient.mk _ (f ⟨0, _⟩)) • (Ideal.Quotient.mk _ (v ⟨0, _⟩ - w ⟨0, _⟩)) = 0
          rw [smul_eq_mul, ← map_mul, hsub, map_zero])
    ·


      let n := k' + 1
      have hn : 0 < n := by omega
      let a := f (Fin.last (k' + 1))

      let d : ∀ (i : ℕ) (_ : i < k' + 1 + 1),
          ((Fin (Nat.choose (k' + 1 + 1) (i + 1)) → A) →ₗ[A]
           (Fin (Nat.choose (k' + 1 + 1) i) → A)) :=
        fun i hi => koszulConeDiff n hn d' a i (by omega)

      have h_choose0 : (0 : ℕ) < Nat.choose (k' + 1 + 1) 0 := by
        simp [Nat.choose_zero_right]
      let ε : (Fin (Nat.choose (k' + 1 + 1) 0) → A) →ₗ[A] (A ⧸ Ideal.span (Set.range f)) :=
        { toFun := fun v => Ideal.Quotient.mk _ (v ⟨0, h_choose0⟩)
          map_add' := fun v w => by simp [map_add]
          map_smul' := fun r v => rfl }

      have hcone := koszulCone_exactness hn f hreg d' ε'
        hε'_surj hε'_exact hε'_exact_top hd'_exact hd'_inj a rfl
      obtain ⟨hcone_exact0, hcone_exact_mid, hcone_inj⟩ := hcone
      refine ⟨d, ε, ?_, ?_, ?_, ?_, ?_⟩
      ·
        intro x; obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
        exact ⟨fun _ => b, rfl⟩
      ·


        exact hcone_exact0
      ·
        intro h; exact absurd h (by omega)
      ·

        exact hcone_exact_mid
      ·

        exact hcone_inj

lemma X_nonzerodiv_mod_lower (k : Type*) [Field k] (n : ℕ) (j : Fin n)
    (p : MvPolynomial (Fin n) k)
    (hp : MvPolynomial.X j * p ∈ Ideal.span (MvPolynomial.X '' {i : Fin n | (i : ℕ) < (j : ℕ)})) :
    p ∈ Ideal.span (MvPolynomial.X '' {i : Fin n | (i : ℕ) < (j : ℕ)}) := by
  rw [MvPolynomial.mem_ideal_span_X_image] at hp ⊢
  intro m hm
  have hcoeff : MvPolynomial.coeff m p ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  have hcoeff2 : MvPolynomial.coeff (Finsupp.single j 1 + m) (MvPolynomial.X j * p) ≠ 0 := by
    rw [MvPolynomial.coeff_X_mul]; exact hcoeff
  obtain ⟨i, hi_lt, hi_ne⟩ := hp _ (MvPolynomial.mem_support_iff.mpr hcoeff2)
  refine ⟨i, hi_lt, ?_⟩
  have hij : j ≠ i := by intro h; subst h; exact Nat.lt_irrefl _ hi_lt
  rwa [Finsupp.add_apply, Finsupp.single_apply, if_neg hij, zero_add] at hi_ne

set_option maxHeartbeats 400000 in

theorem variables_form_regular_sequence
    (k : Type*) [Field k] (n : ℕ) :
    IsRegularSequence (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k)) := by
  refine ⟨fun j r hr h => ?_, ?_⟩
  ·
    apply hr
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r

    have hmul : (X j : MvPolynomial (Fin n) k) * p ∈
        Ideal.span ((fun i : Fin n => (X i : MvPolynomial (Fin n) k)) '' {i | (i : ℕ) < ↑j}) := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul]
      rwa [smul_eq_mul] at h
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact X_nonzerodiv_mod_lower k n j p hmul
  ·
    rw [Ideal.Quotient.nontrivial_iff]
    intro htop
    have h1 : (1 : MvPolynomial (Fin n) k) ∈
        Ideal.span (Set.range (fun i : Fin n => (X i : MvPolynomial (Fin n) k))) := by
      rw [htop]; trivial
    have hrange : Set.range (fun i : Fin n => (X i : MvPolynomial (Fin n) k)) =
      (X : Fin n → MvPolynomial (Fin n) k) '' Set.univ := by ext x; simp [Set.mem_range]
    rw [hrange, mem_ideal_span_X_image] at h1
    have hmem : (0 : Fin n →₀ ℕ) ∈ (1 : MvPolynomial (Fin n) k).support := by
      rw [mem_support_iff, coeff_one, if_pos rfl]; exact one_ne_zero
    obtain ⟨i, _, hi⟩ := h1 0 hmem
    simp at hi

theorem koszul_complex_is_acyclic
    (k : Type*) [Field k] (n : ℕ) :
    ∃ (r : Fin (n + 1) → ℕ)
      (d : ∀ (i : ℕ) (_ : i < n),
        ((Fin (r ⟨i + 1, by omega⟩) → MvPolynomial (Fin n) k) →ₗ[MvPolynomial (Fin n) k]
         (Fin (r ⟨i, by omega⟩) → MvPolynomial (Fin n) k))),

      (∀ (i : ℕ) (hi : i < n) (hi' : i + 1 < n),
        (d i hi).comp (d (i + 1) hi') = 0) ∧

      (∀ (i : ℕ) (hi : i < n) (hi' : i + 1 < n),
        LinearMap.ker (d i hi) = LinearMap.range (d (i + 1) hi')) ∧

      (∀ (hn : 0 < n), Function.Injective (d (n - 1) (by omega))) ∧

      (∀ (p : ℕ) (hp : p ≤ n), r ⟨p, by omega⟩ = Nat.choose n p) := by

  have hreg := variables_form_regular_sequence k n

  obtain ⟨d, ε, _hε_surj, _hε_exact, _hε_iso, hd_exact, hd_inj⟩ :=
    lemma_12_8_koszul_exact (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k)) hreg

  let r : Fin (n + 1) → ℕ := fun p => Nat.choose n p
  refine ⟨r, d, ?_, ?_, ?_, ?_⟩
  ·
    intro i hi hi'
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, LinearMap.zero_apply]
    have hexact := hd_exact i hi hi'
    have hv : d (i + 1) hi' v ∈ LinearMap.range (d (i + 1) hi') := LinearMap.mem_range_self _ _
    rw [← hexact] at hv
    exact (LinearMap.mem_ker.mp hv)
  ·
    exact hd_exact
  ·
    exact hd_inj
  ·
    intro p hp
    rfl

lemma eval_zero_of_homogeneous_pos_deg
    (f : MvPolynomial (Fin n) k) (d : ℕ) (hd : 0 < d)
    (hhom : ∀ (m : Fin n →₀ ℕ), MvPolynomial.coeff m f ≠ 0 →
      (m.sum fun _ e => e) = d) :
    MvPolynomial.eval (0 : Fin n → k) f = 0 := by
  simp only [MvPolynomial.eval_zero]
  rw [MvPolynomial.constantCoeff_eq]

  by_contra h
  have := hhom 0 h
  simp [Finsupp.sum] at this
  omega

theorem assocPrimes_quotient_subset_minimalPrimes_polynomial
    (k : Type*) [inst : Field k] (n : ℕ)
    (I : Ideal (MvPolynomial (Fin n) k))
    (p : Ideal (MvPolynomial (Fin n) k))
    (hp : p ∈ associatedPrimes (MvPolynomial (Fin n) k)
      (MvPolynomial (Fin n) k ⧸ I)) :
    p ∈ I.minimalPrimes := by


  sorry

theorem height_le_of_assocPrime_quotient_span_range
    (k : Type*) [Field k] (n m : ℕ)
    (f : Fin m → MvPolynomial (Fin n) k)
    (p : Ideal (MvPolynomial (Fin n) k))
    (hp : p ∈ associatedPrimes (MvPolynomial (Fin n) k)
      (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f))) :
    p.height ≤ m := by

  have hmem : p ∈ (Ideal.span (Set.range f)).minimalPrimes :=
    assocPrimes_quotient_subset_minimalPrimes_polynomial k n
      (Ideal.span (Set.range f)) p hp

  have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span (Set.finite_range f) hmem

  have h2 : (Set.range f).ncard ≤ m := by
    rw [← Set.image_univ]
    exact (Set.ncard_image_le Set.finite_univ).trans
      (by simp [Set.ncard_univ])
  exact h1.trans (by exact_mod_cast h2)

theorem assoc_prime_dim_lower_bound
    (k : Type*) [Field k] (n : ℕ)
    (_hk : IsAlgClosed k)
    (f : Fin n → MvPolynomial (Fin n) k)
    (_hhom : ∀ i, ∃ (d : ℕ), 0 < d ∧
      ∀ (m : Fin n →₀ ℕ), MvPolynomial.coeff m (f i) ≠ 0 →
        (m.sum fun _ e => e) = d)
    (j : Fin n)
    (p : Ideal (MvPolynomial (Fin n) k))
    (hp : p ∈ associatedPrimes (MvPolynomial (Fin n) k)
      (MvPolynomial (Fin n) k ⧸ Ideal.span (f '' {i | (i : ℕ) < j}))) :
    ((n : ℕ) - (j : ℕ) : ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) k ⧸ p) := by

  haveI : p.IsPrime := (instIsPrimeValIdealMemSetAssociatedPrimes ⟨p, hp⟩)

  have hdim := polynomial_ring_dimension_formula k n p

  let g : Fin (j : ℕ) → MvPolynomial (Fin n) k :=
    fun i => f ⟨i, lt_trans i.isLt j.isLt⟩
  have hrange : f '' {i : Fin n | (i : ℕ) < (j : ℕ)} = Set.range g := by
    ext x
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_range, g]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩
    · rintro ⟨i, rfl⟩; exact ⟨⟨i, lt_trans i.isLt j.isLt⟩, i.isLt, rfl⟩

  have hht : p.height ≤ (j : ℕ) :=
    height_le_of_assocPrime_quotient_span_range k n (j : ℕ) g p (hrange ▸ hp)

  have h1 : (n : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin n) k ⧸ p) + ((j : ℕ∞) : WithBot ℕ∞) :=
    calc (n : WithBot ℕ∞)
          ≤ ringKrullDim (MvPolynomial (Fin n) k ⧸ p) + p.height := hdim
        _ ≤ ringKrullDim (MvPolynomial (Fin n) k ⧸ p) + ((j : ℕ∞) : WithBot ℕ∞) := by
            gcongr; exact_mod_cast hht
  by_cases hD : ringKrullDim (MvPolynomial (Fin n) k ⧸ p) = ⊥
  · rw [hD, WithBot.bot_add] at h1
    exact absurd h1 (not_le.mpr (WithBot.bot_lt_coe _))
  · obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hD
    rw [← hd] at h1 ⊢
    have h' : (n : ℕ∞) ≤ d + (j : ℕ∞) := by exact_mod_cast h1
    have : ((n - (j : ℕ) : ℕ) : ℕ∞) ≤ d := by
      calc ((n - (j : ℕ) : ℕ) : ℕ∞)
            ≤ (n : ℕ∞) - ((j : ℕ) : ℕ∞) := by
              exact_mod_cast Nat.sub_le_sub_right (le_refl n) j
          _ ≤ d := tsub_le_iff_right.mpr h'
    exact_mod_cast this

theorem reverse_catenary_polynomial_ring
    (k : Type*) [Field k] (n : ℕ)
    (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] :
    ringKrullDim (MvPolynomial (Fin n) k ⧸ p) + p.height ≤
      (n : WithBot ℕ∞) := by
  set Rp := MvPolynomial (Fin n) k with hRp_def
  let pp : PrimeSpectrum Rp := ⟨p, inferInstance⟩

  have h_quot_eq : ringKrullDim (Rp ⧸ p) = ↑(Order.coheight pp) := by
    rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]; congr 1

  have h_ht_eq : p.height = Order.height pp := by
    rw [Ideal.height_eq_primeHeight, Ideal.primeHeight]

  have hbdd : BddAbove (Set.range fun (a : PrimeSpectrum Rp) =>
      Order.height a + Order.coheight a) :=
    OrderTop.bddAbove _
  have h3 : Order.height pp + Order.coheight pp ≤
      ⨆ (a : PrimeSpectrum Rp), Order.height a + Order.coheight a :=
    le_ciSup hbdd pp
  have h4 : Order.krullDim (PrimeSpectrum Rp) =
      ↑(⨆ (a : PrimeSpectrum Rp), Order.height a + Order.coheight a) :=
    Order.krullDim_eq_iSup_height_add_coheight_of_nonempty
  have h5 : ↑(Order.height pp + Order.coheight pp) ≤
      Order.krullDim (PrimeSpectrum Rp) := by
    rw [h4, WithBot.coe_le_coe]; exact h3

  have h6 : ringKrullDim Rp = (n : WithBot ℕ∞) := by
    show ringKrullDim (MvPolynomial (Fin n) k) = (n : WithBot ℕ∞)
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
        ringKrullDim_eq_zero_of_field, zero_add, Nat.card_fin]

  rw [h_quot_eq, h_ht_eq, ← WithBot.coe_add, add_comm]
  exact le_trans h5 (by rw [ringKrullDim] at h6; exact h6.le)

theorem quotient_dim_bound_from_vanishing
    (k : Type*) [Field k] (n : ℕ)
    (hk : IsAlgClosed k)
    (f : Fin n → MvPolynomial (Fin n) k)
    (hhom : ∀ i, ∃ (d : ℕ), 0 < d ∧
      ∀ (m : Fin n →₀ ℕ), MvPolynomial.coeff m (f i) ≠ 0 →
        (m.sum fun _ e => e) = d)
    (hvanish : ∀ (v : Fin n → k),
      (∀ i, MvPolynomial.eval v (f i) = 0) → v = 0)
    (j : Fin n)
    (p : Ideal (MvPolynomial (Fin n) k))
    [p.IsPrime]
    (hp_contains : ∀ i : Fin n, (i : ℕ) ≤ j → f i ∈ p) :
    ringKrullDim (MvPolynomial (Fin n) k ⧸ p) +
      (((j : ℕ) + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) := by


  sorry

lemma height_bound_from_dim_bounds
    (dim : WithBot ℕ∞) (ht : ℕ∞) (n j1 : ℕ)
    (h_le : dim + ht ≤ (n : WithBot ℕ∞))
    (h_ge : (n : WithBot ℕ∞) ≤ dim + ht)
    (h_dim : dim + ((j1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞)) :
    (j1 : ℕ∞) ≤ ht := by
  have h_eq : dim + (ht : WithBot ℕ∞) = (n : WithBot ℕ∞) := le_antisymm h_le h_ge
  by_cases hdim : dim = ⊥
  · rw [hdim, WithBot.bot_add] at h_eq; exact absurd h_eq.symm WithBot.coe_ne_bot
  obtain ⟨dim_val, hdim_eq⟩ := WithBot.ne_bot_iff_exists.mp hdim
  subst hdim_eq
  by_cases hht : ht = ⊤
  · subst hht; exact le_top
  by_cases hdv : dim_val = ⊤
  · exfalso; rw [hdv, ← WithBot.coe_add, top_add] at h_eq
    exact absurd (WithBot.coe_injective h_eq) (ENat.top_ne_coe n)
  obtain ⟨h_nat, hht_eq⟩ := WithTop.ne_top_iff_exists.mp hht
  obtain ⟨d_nat, hdim_eq⟩ := WithTop.ne_top_iff_exists.mp hdv
  subst hht_eq; subst hdim_eq
  change (j1 : ℕ∞) ≤ h_nat
  have h1 : (d_nat : ℕ∞) + (h_nat : ℕ∞) = (n : ℕ∞) := by
    rw [← WithBot.coe_add] at h_eq; exact WithBot.coe_injective h_eq
  rw [show ((j1 : ℕ) : WithBot ℕ∞) = ((j1 : ℕ∞) : WithBot ℕ∞) from by norm_cast] at h_dim
  have h2 : (d_nat : ℕ∞) + (j1 : ℕ∞) ≤ (n : ℕ∞) := by
    rw [← WithBot.coe_add] at h_dim; exact WithBot.coe_le_coe.mp h_dim
  have : d_nat + h_nat = n := by exact_mod_cast h1
  have : d_nat + j1 ≤ n := by exact_mod_cast h2
  exact_mod_cast (show j1 ≤ h_nat by omega)

theorem height_ge_succ_of_vanishing_contains
    (k : Type*) [Field k] (n : ℕ)
    (hk : IsAlgClosed k)
    (f : Fin n → MvPolynomial (Fin n) k)
    (hhom : ∀ i, ∃ (d : ℕ), 0 < d ∧
      ∀ (m : Fin n →₀ ℕ), MvPolynomial.coeff m (f i) ≠ 0 →
        (m.sum fun _ e => e) = d)
    (hvanish : ∀ (v : Fin n → k),
      (∀ i, MvPolynomial.eval v (f i) = 0) → v = 0)
    (j : Fin n)
    (p : Ideal (MvPolynomial (Fin n) k))
    [p.IsPrime]
    (hp_contains : ∀ i : Fin n, (i : ℕ) ≤ j → f i ∈ p) :
    ((j : ℕ) + 1 : ℕ∞) ≤ p.height := by

  have h_le : ringKrullDim (MvPolynomial (Fin n) k ⧸ p) + p.height ≤
      (n : WithBot ℕ∞) :=
    reverse_catenary_polynomial_ring k n p

  have h_ge : (n : WithBot ℕ∞) ≤
      ringKrullDim (MvPolynomial (Fin n) k ⧸ p) + p.height :=
    polynomial_ring_dimension_formula k n p

  have h_dim : ringKrullDim (MvPolynomial (Fin n) k ⧸ p) +
      (((j : ℕ) + 1 : ℕ) : WithBot ℕ∞) ≤ (n : WithBot ℕ∞) :=
    quotient_dim_bound_from_vanishing k n hk f hhom hvanish j p hp_contains

  exact height_bound_from_dim_bounds
    (ringKrullDim (MvPolynomial (Fin n) k ⧸ p)) p.height n ((j : ℕ) + 1)
    h_le h_ge h_dim

theorem prime_dim_upper_bound_from_vanishing
    (k : Type*) [Field k] (n : ℕ)
    (hk : IsAlgClosed k)
    (f : Fin n → MvPolynomial (Fin n) k)
    (hhom : ∀ i, ∃ (d : ℕ), 0 < d ∧
      ∀ (m : Fin n →₀ ℕ), MvPolynomial.coeff m (f i) ≠ 0 →
        (m.sum fun _ e => e) = d)
    (hvanish : ∀ (v : Fin n → k),
      (∀ i, MvPolynomial.eval v (f i) = 0) → v = 0)
    (j : Fin n)
    (p : Ideal (MvPolynomial (Fin n) k))
    [p.IsPrime]
    (hp_contains : ∀ i : Fin n, (i : ℕ) ≤ j → f i ∈ p) :
    ringKrullDim (MvPolynomial (Fin n) k ⧸ p) + ((j : ℕ) + 1 : ℕ∞) ≤
      (n : WithBot ℕ∞) := by

  have hht : ((j : ℕ) + 1 : ℕ∞) ≤ p.height :=
    height_ge_succ_of_vanishing_contains k n hk f hhom hvanish j p hp_contains

  have hcat : ringKrullDim (MvPolynomial (Fin n) k ⧸ p) + p.height ≤
      (n : WithBot ℕ∞) :=
    reverse_catenary_polynomial_ring k n p


  have hht_wb : (((j : ℕ) + 1 : ℕ∞) : WithBot ℕ∞) ≤ (p.height : WithBot ℕ∞) :=
    WithBot.coe_le_coe.mpr hht
  exact le_trans (by gcongr) hcat

theorem fj_not_in_associated_prime
    (k : Type*) [Field k] (n : ℕ)
    (hk : IsAlgClosed k)
    (f : Fin n → MvPolynomial (Fin n) k)
    (hhom : ∀ i, ∃ (d : ℕ), 0 < d ∧
      ∀ (m : Fin n →₀ ℕ), MvPolynomial.coeff m (f i) ≠ 0 →
        (m.sum fun _ e => e) = d)
    (hvanish : ∀ (v : Fin n → k),
      (∀ i, MvPolynomial.eval v (f i) = 0) → v = 0)
    (j : Fin n)
    (p : Ideal (MvPolynomial (Fin n) k))
    (hp : p ∈ associatedPrimes (MvPolynomial (Fin n) k)
      (MvPolynomial (Fin n) k ⧸ Ideal.span (f '' {i | (i : ℕ) < j}))) :
    f j ∉ p := by

  haveI hp_prime : p.IsPrime := (hp : IsAssociatedPrime p _).isPrime

  have hI_le_p : Ideal.span (f '' {i | (i : ℕ) < j}) ≤ p := by
    have hap : IsAssociatedPrime p _ := hp
    have h1 := hap.annihilator_le
    rw [Submodule.annihilator_top, Ideal.annihilator_quotient] at h1
    exact h1

  intro hfj

  have hp_contains : ∀ i : Fin n, (i : ℕ) ≤ j → f i ∈ p := by
    intro i hi
    rcases Nat.lt_or_eq_of_le hi with h | h
    · exact hI_le_p (Ideal.subset_span ⟨i, ⟨h, rfl⟩⟩)
    · exact Fin.ext h ▸ hfj

  have h_lower := assoc_prime_dim_lower_bound k n hk f hhom j p hp

  have h_upper := prime_dim_upper_bound_from_vanishing k n hk f hhom hvanish j p hp_contains

  have hd_ne_bot : ringKrullDim (MvPolynomial (Fin n) k ⧸ p) ≠ ⊥ := by
    intro hd; rw [hd] at h_lower; exact absurd h_lower (not_le.mpr (WithBot.bot_lt_coe _))
  obtain ⟨d', hd'⟩ := WithBot.ne_bot_iff_exists.mp hd_ne_bot
  rw [← hd'] at h_lower h_upper
  have h1 : ((n - (j : ℕ) : ℕ) : ℕ∞) ≤ d' := by exact_mod_cast h_lower
  have h2 : d' + (((j : ℕ) + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast h_upper
  have h3 : ((n - (j : ℕ) + ((j : ℕ) + 1) : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by
    calc ((n - (j : ℕ) + ((j : ℕ) + 1) : ℕ) : ℕ∞)
          = ((n - (j : ℕ) : ℕ) : ℕ∞) + (((j : ℕ) + 1 : ℕ) : ℕ∞) := by push_cast; ring
        _ ≤ d' + (((j : ℕ) + 1 : ℕ) : ℕ∞) := by gcongr
        _ ≤ (n : ℕ∞) := h2
  rw [ENat.coe_le_coe] at h3
  exact absurd h3 (by omega)

theorem prop_12_9_non_zero_divisor_step
    (hk : IsAlgClosed k)
    (f : Fin n → R)
    (hhom : ∀ i, ∃ (d : ℕ), 0 < d ∧
      ∀ (m : Fin n →₀ ℕ), MvPolynomial.coeff m (f i) ≠ 0 →
        (m.sum fun _ e => e) = d)
    (hvanish : ∀ (v : Fin n → k),
      (∀ i, MvPolynomial.eval v (f i) = 0) → v = 0)
    (j : Fin n)
    (r : MvPolynomial (Fin n) k ⧸ Ideal.span (f '' {i | (i : ℕ) < j}))
    (hr : r ≠ 0) :
    (Ideal.Quotient.mk (Ideal.span (f '' {i | (i : ℕ) < j}))) (f j) • r ≠ 0 := by
  let I := Ideal.span (f '' {i | (i : ℕ) < j})

  intro h_zd


  have h_mem_zd : f j ∈ { a : R | ∃ x : R ⧸ I, x ≠ 0 ∧ a • x = 0 } := ⟨r, hr, h_zd⟩


  rw [← biUnion_associatedPrimes_eq_zero_divisors R (R ⧸ I)] at h_mem_zd

  simp only [Set.mem_iUnion] at h_mem_zd
  obtain ⟨p, hp, hfp⟩ := h_mem_zd

  exact fj_not_in_associated_prime k n hk f hhom hvanish j p hp hfp

theorem prop_12_9_regular_sequence
    (hk : IsAlgClosed k)
    (f : Fin n → R)
    (hhom : ∀ i, ∃ (d : ℕ), 0 < d ∧
      ∀ (m : Fin n →₀ ℕ), MvPolynomial.coeff m (f i) ≠ 0 →
        (m.sum fun _ e => e) = d)
    (hvanish : ∀ (v : Fin n → k),
      (∀ i, MvPolynomial.eval v (f i) = 0) → v = 0) :
    IsRegularSequence f := by
  constructor
  ·

    intro j r hr
    exact prop_12_9_non_zero_divisor_step k n hk f hhom hvanish j r hr
  ·


    rw [Ideal.Quotient.nontrivial_iff]
    intro h
    have h1 : (1 : MvPolynomial (Fin n) k) ∈ Ideal.span (Set.range f) := by
      rw [h]; trivial
    have hker : Ideal.span (Set.range f) ≤
        RingHom.ker (MvPolynomial.eval (0 : Fin n → k)) := by
      apply Ideal.span_le.mpr
      intro x hx
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨d, hd, hhomi⟩ := hhom i
      show f i ∈ RingHom.ker (MvPolynomial.eval (0 : Fin n → k))
      rw [RingHom.mem_ker]
      exact eval_zero_of_homogeneous_pos_deg k n (f i) d hd hhomi
    have h2 : MvPolynomial.eval (0 : Fin n → k) (1 : MvPolynomial (Fin n) k) = 0 := by
      have := hker h1
      rwa [RingHom.mem_ker] at this
    simp at h2

def quotientHomogeneousSubmodule
    (I : Ideal (MvPolynomial (Fin n) k)) (i : ℕ) :
    Submodule k (MvPolynomial (Fin n) k ⧸ I) :=
  (homogeneousSubmodule (Fin n) k i).map (I.mkQ.restrictScalars k)

def qAnalog (d : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun i => if i < d then 1 else 0)

def invOneSubX : PowerSeries ℤ :=
  PowerSeries.mk (fun _ => 1)

section HilbertHelpers
variable {n}

lemma mem_finsuppAntidiag_univ_iff_degree' {d : ℕ} (f : Fin n →₀ ℕ) :
    f ∈ (Finset.univ : Finset (Fin n)).finsuppAntidiag d ↔ Finsupp.degree f = d := by
  rw [Finset.mem_finsuppAntidiag]
  simp only [Finset.subset_univ, and_true]
  have key : (Finset.univ : Finset (Fin n)).sum f = Finsupp.degree f := by
    simp [Finsupp.degree]
    exact (Finsupp.sum_fintype f (fun _ => id) (fun _ => rfl)).symm
  rw [key]

noncomputable instance fintypeFinsuppDegreeEq' (d : ℕ) :
    Fintype {s : Fin n →₀ ℕ | Finsupp.degree s = d} :=
  Fintype.ofFinset ((Finset.univ : Finset (Fin n)).finsuppAntidiag d)
    (fun f => mem_finsuppAntidiag_univ_iff_degree' f)

lemma finrank_homogeneousSubmodule_eq' (d : ℕ) :
    Module.finrank k (homogeneousSubmodule (Fin n) k d) = n.multichoose d := by
  rw [homogeneousSubmodule_eq_finsupp_supported]
  have e : ↥(Finsupp.supported k k {s : Fin n →₀ ℕ | Finsupp.degree s = d}) ≃ₗ[k]
      ↥{s : Fin n →₀ ℕ | Finsupp.degree s = d} →₀ k :=
    Finsupp.supportedEquivFinsupp _
  calc Module.finrank k ↥(Finsupp.supported k k {d_1 | Finsupp.degree d_1 = d})
      = Module.finrank k (↥{d_1 : Fin n →₀ ℕ | Finsupp.degree d_1 = d} →₀ k) := e.finrank_eq
    _ = Fintype.card ↥{d_1 : Fin n →₀ ℕ | Finsupp.degree d_1 = d} :=
        Module.finrank_finsupp_self k
    _ = ((Finset.univ : Finset (Fin n)).finsuppAntidiag d).card := Fintype.card_ofFinset ..
    _ = n.multichoose d := by
        rw [Finset.card_finsuppAntidiag_nat_eq_multichoose]; simp [Fintype.card_fin]

end HilbertHelpers

theorem hilbert_series_polynomial_ring :
    hilbertSeries (homogeneousSubmodule (Fin n) k) = invOneSubX ^ n := by
  ext d
  simp only [hilbertSeries, invOneSubX, PowerSeries.coeff_mk, PowerSeries.coeff_pow,
    Finset.prod_const_one]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, finrank_homogeneousSubmodule_eq']
  norm_cast
  rw [Finset.card_finsuppAntidiag_nat_eq_multichoose, Finset.card_range]

theorem hilbert_series_quotient_regular_seq
    (m : ℕ) (s : Fin m → MvPolynomial (Fin n) k) (degs : Fin m → ℕ)
    (hhom : ∀ i, ∀ (c : Fin n →₀ ℕ), MvPolynomial.coeff c (s i) ≠ 0 →
      (c.sum fun _ e => e) = degs i)
    (hreg : IsRegularSequence s) :
    hilbertSeries (quotientHomogeneousSubmodule k n (Ideal.span (Set.range s))) =
      (∏ i : Fin m, (1 - (PowerSeries.X : PowerSeries ℤ) ^ degs i)) *
        hilbertSeries (homogeneousSubmodule (Fin n) k) := by
  sorry

lemma one_sub_X_pow_mul_invOneSubX (d : ℕ) :
    (1 - (PowerSeries.X : PowerSeries ℤ) ^ d) * invOneSubX = qAnalog d := by
  ext m
  simp only [qAnalog, PowerSeries.coeff_mk, sub_mul, one_mul, map_sub, invOneSubX]
  by_cases hm : m < d
  · simp only [hm, ite_true]
    suffices h : (PowerSeries.coeff m) ((PowerSeries.X : PowerSeries ℤ) ^ d *
        PowerSeries.mk (fun _ => (1 : ℤ))) = 0 by linarith
    rw [PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro ⟨a, b⟩ hab
    simp only [Finset.mem_antidiagonal] at hab
    simp [PowerSeries.coeff_X_pow, show a ≠ d from by omega]
  · simp only [show ¬(m < d) from by omega, ite_false]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (by omega : d ≤ m)
    rw [show d + j = j + d from by ring, PowerSeries.coeff_X_pow_mul, PowerSeries.coeff_mk]
    ring

lemma prod_one_sub_mul_invOneSubX_eq_prod_qAnalog {m : ℕ} (d : Fin m → ℕ) :
    (∏ i : Fin m, (1 - (PowerSeries.X : PowerSeries ℤ) ^ d i)) * invOneSubX ^ m =
    ∏ i : Fin m, qAnalog (d i) := by
  have h1 : invOneSubX ^ m = ∏ _i : Fin m, (invOneSubX : PowerSeries ℤ) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h1, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact one_sub_X_pow_mul_invOneSubX (d i)

theorem free_over_adjoin_of_homogeneous
    (k : Type*) [Field k] (n : ℕ)
    (f : Fin n → MvPolynomial (Fin n) k)
    (d : Fin n → ℕ)
    (hd : ∀ i, 0 < d i)
    (hhom : ∀ i, ∀ (m : Fin n →₀ ℕ),
      MvPolynomial.coeff m (f i) ≠ 0 → (m.sum fun _ e => e) = d i)
    (hfin : Module.Finite (Algebra.adjoin k (Set.range f)) (MvPolynomial (Fin n) k)) :
    Module.Free (Algebra.adjoin k (Set.range f)) (MvPolynomial (Fin n) k) := by
  sorry

theorem rank_eq_prod_of_homogeneous
    (k : Type*) [Field k] (n : ℕ)
    (f : Fin n → MvPolynomial (Fin n) k)
    (d : Fin n → ℕ)
    (hd : ∀ i, 0 < d i)
    (hhom : ∀ i, ∀ (m : Fin n →₀ ℕ),
      MvPolynomial.coeff m (f i) ≠ 0 → (m.sum fun _ e => e) = d i)
    (hfin : Module.Finite (Algebra.adjoin k (Set.range f)) (MvPolynomial (Fin n) k)) :
    Module.rank (Algebra.adjoin k (Set.range f)) (MvPolynomial (Fin n) k) =
      ↑(Finset.univ.prod d) := by
  sorry

theorem filtered_deformation_iso
    (k : Type*) [Field k] (n : ℕ)
    (f : Fin n → MvPolynomial (Fin n) k)
    (d : Fin n → ℕ)
    (hd : ∀ i, 0 < d i)
    (hhom : ∀ i, ∀ (m : Fin n →₀ ℕ),
      MvPolynomial.coeff m (f i) ≠ 0 → (m.sum fun _ e => e) = d i)
    (hfin : Module.Finite (Algebra.adjoin k (Set.range f)) (MvPolynomial (Fin n) k)) :
    Nonempty ((MvPolynomial (Fin n) k) ≃ₗ[Algebra.adjoin k (Set.range f)]
      (Fin (Finset.univ.prod d) → Algebra.adjoin k (Set.range f))) := by
  haveI := free_over_adjoin_of_homogeneous k n f d hd hhom hfin
  have hrank := rank_eq_prod_of_homogeneous k n f d hd hhom hfin
  exact ⟨finDimVectorspaceEquiv _ hrank⟩

theorem prop_12_10_free_module
    (f : Fin n → R)
    (d : Fin n → ℕ)
    (hd : ∀ i, 0 < d i)
    (hhom : ∀ i, ∀ (m : Fin n →₀ ℕ),
      MvPolynomial.coeff m (f i) ≠ 0 → (m.sum fun _ e => e) = d i)
    (hfin : Module.Finite (Algebra.adjoin k (Set.range f)) R) :
    Module.Free (Algebra.adjoin k (Set.range f)) R ∧
      Module.finrank (Algebra.adjoin k (Set.range f)) R = Finset.univ.prod d := by


  set S := Algebra.adjoin k (Set.range f)
  have _hSrc : StrongRankCondition S := commRing_strongRankCondition S
  obtain ⟨e⟩ := filtered_deformation_iso k n f d hd hhom hfin
  exact ⟨Module.Free.of_equiv e.symm,
    by rw [e.finrank_eq, Module.finrank_pi_fintype]; simp [Module.finrank_self]⟩

theorem prop_12_10_hilbert_series
    (hk : IsAlgClosed k)
    (f : Fin n → R)
    (d : Fin n → ℕ)
    (hd : ∀ i, 0 < d i)
    (hhom : ∀ i, ∀ (m : Fin n →₀ ℕ),
      MvPolynomial.coeff m (f i) ≠ 0 → (m.sum fun _ e => e) = d i)
    (hvanish : ∀ (v : Fin n → k),
      (∀ i, MvPolynomial.eval v (f i) = 0) → v = 0)
    (_hfin : Module.Finite (Algebra.adjoin k (Set.range f)) R) :
    hilbertSeries (quotientHomogeneousSubmodule k n (Ideal.span (Set.range f))) =
      ∏ i : Fin n, qAnalog (d i) := by

  have hreg : IsRegularSequence f :=
    prop_12_9_regular_sequence k n hk f
      (fun i => ⟨d i, hd i, hhom i⟩) hvanish


  rw [hilbert_series_quotient_regular_seq k n n f d hhom hreg,
      hilbert_series_polynomial_ring k n,
      prod_one_sub_mul_invOneSubX_eq_prod_qAnalog]

end
