/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.UniformSpace.Cauchy
import Atlas.LieGroups.code.CompactMeasures
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.Algebra.UniformConvergence
import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
import Mathlib.Analysis.LocallyConvex.Barrelled
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus

noncomputable section

open Filter Topology

namespace Meas

def embedMap (X : Type*) [TopologicalSpace X]
    (MX : Type*) [AddCommGroup MX] [Module ℂ MX] [TopologicalSpace MX]
    [CompactlySupportedMeasureSpace X MX] : (X →₀ ℂ) →ₗ[ℂ] MX :=
  Finsupp.linearCombination ℂ (CompactlySupportedMeasureSpace.dirac (X := X) (MX := MX))

def atomicIn {X : Type*} [TopologicalSpace X]
    {MX : Type*} [AddCommGroup MX] [Module ℂ MX] [TopologicalSpace MX]
    [CompactlySupportedMeasureSpace X MX] (K : Set X) : Set MX :=
  (embedMap X MX) '' { f : X →₀ ℂ | ↑f.support ⊆ K }

def IsSupportedIn {X : Type*} [TopologicalSpace X]
    {MX : Type*} [AddCommGroup MX] [Module ℂ MX] [TopologicalSpace MX]
    [CompactlySupportedMeasureSpace X MX] (μ : MX) (K : Set X) : Prop :=
  μ ∈ closure (atomicIn K)

end Meas


namespace Meas

def functionalSupp (X : Type*) [TopologicalSpace X]
    {MX : Type*} [AddCommGroup MX] [Module ℂ MX] [TopologicalSpace MX]
    [CompactlySupportedMeasureSpace X MX] (μ : MX) : Set X :=
  ⋂₀ { K : Set X | IsClosed K ∧ IsSupportedIn (X := X) μ K }

end Meas

noncomputable instance ContinuousMap.instIsUniformAddGroupComplex
    {X : Type*} [TopologicalSpace X] :
    IsUniformAddGroup C(X, ℂ) :=
  IsUniformInducing.isUniformAddGroup
    ({ toFun := ContinuousMap.toUniformOnFunIsCompact
       map_zero' := rfl
       map_add' := fun _ _ => rfl } : C(X, ℂ) →+ UniformOnFun X ℂ {K | IsCompact K})
    ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isUniformInducing

namespace ConcreteMeasSupp

open Filter Topology

variable {X : Type*} [TopologicalSpace X]

def IsSupportedIn (μ : C(X, ℂ) →L[ℂ] ℂ) (K : Set X) : Prop :=
  ∀ f : C(X, ℂ), (∀ x ∈ K, f x = 0) → μ f = 0

def IsWeakStarCauchy (μ : ℕ → (C(X, ℂ) →L[ℂ] ℂ)) : Prop :=
  ∀ f : C(X, ℂ), CauchySeq (fun n => μ n f)

def TendstoWeakStar (μ : ℕ → (C(X, ℂ) →L[ℂ] ℂ)) (μ₀ : C(X, ℂ) →L[ℂ] ℂ) : Prop :=
  ∀ f : C(X, ℂ), Tendsto (fun n => μ n f) atTop (nhds (μ₀ f))

theorem cauchySeq_supportedIn_compact
    {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    (μ : ℕ → (C(X, ℂ) →L[ℂ] ℂ)) (hcauchy : IsWeakStarCauchy μ) :
    ∃ K : Set X, IsCompact K ∧ ∀ n, IsSupportedIn (μ n) K := by

  rcases isEmpty_or_nonempty X with hempty | hne
  · exact ⟨∅, isCompact_empty, fun n f hf => by
      have : f = 0 := by ext x; exact IsEmpty.elim hempty x
      simp [this, map_zero]⟩

  haveI : BaireSpace C(X, ℂ) := inferInstance

  let A : ℕ → Set C(X, ℂ) := fun k => {f | ∀ n, ‖μ n f‖ ≤ ↑k}

  have A_closed : ∀ k, IsClosed (A k) := by
    intro k
    show IsClosed {f : C(X, ℂ) | ∀ n, ‖μ n f‖ ≤ ↑k}
    suffices h : {f : C(X, ℂ) | ∀ n, ‖μ n f‖ ≤ ↑k} =
        ⋂ n, (fun f => ‖μ n f‖) ⁻¹' Set.Iic ↑k by
      rw [h]
      exact isClosed_iInter fun n => IsClosed.preimage ((μ n).continuous.norm) isClosed_Iic
    ext f; simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]

  have A_cover : ∀ f : C(X, ℂ), ∃ k, f ∈ A k := by
    intro f
    obtain ⟨R, _, hR⟩ := cauchySeq_bdd (hcauchy f)
    refine ⟨⌈‖μ 0 f‖ + R⌉₊, fun n => ?_⟩
    calc ‖μ n f‖ = ‖μ 0 f + (μ n f - μ 0 f)‖ := by ring_nf
      _ ≤ ‖μ 0 f‖ + ‖μ n f - μ 0 f‖ := norm_add_le _ _
      _ ≤ ‖μ 0 f‖ + dist (μ n f) (μ 0 f) := by rw [dist_eq_norm]
      _ ≤ ‖μ 0 f‖ + R := by linarith [hR n 0]
      _ ≤ ↑⌈‖μ 0 f‖ + R⌉₊ := Nat.le_ceil _
  have A_union : ⋃ k, A k = Set.univ := by
    ext f; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]; exact A_cover f

  obtain ⟨k, hk_int⟩ : ∃ k, (interior (A k)).Nonempty :=
    nonempty_interior_of_iUnion_of_closed A_closed A_union
  obtain ⟨g, hg⟩ := hk_int
  have hg_nhds : A k ∈ nhds g :=
    mem_nhds_iff.mpr ⟨interior (A k), interior_subset, isOpen_interior, hg⟩

  rw [UniformSpace.mem_nhds_iff] at hg_nhds
  obtain ⟨E, hE_mem, hE_sub⟩ := hg_nhds
  rw [ContinuousMap.mem_compactConvergence_entourage_iff] at hE_mem
  obtain ⟨K, V, hK, hV, hKV⟩ := hE_mem

  refine ⟨K, hK, fun n f hfK => ?_⟩
  by_contra hne


  have hmem : ∀ c : ℂ, ∀ m, ‖μ m (g + c • f)‖ ≤ ↑k := by
    intro c
    suffices g + c • f ∈ A k from this
    apply hE_sub
    apply hKV
    intro x hx
    simp only [ContinuousMap.coe_add, ContinuousMap.coe_smul, Pi.add_apply, Pi.smul_apply]
    rw [hfK x hx, smul_zero, add_zero]
    exact refl_mem_uniformity hV

  have hbound : ∀ (c : ℂ), ‖(μ n) g + c * (μ n) f‖ ≤ ↑k := by
    intro c
    have h := hmem c n
    rw [map_add, map_smul, smul_eq_mul] at h
    exact h

  set a := (μ n) g
  set b := (μ n) f
  have hb_ne : b ≠ 0 := hne
  have hscale : ∀ (t : ℕ), ‖a + ↑t‖ ≤ ↑k := by
    intro t
    have h := hbound (↑t / b)
    rwa [div_mul_cancel₀ _ hb_ne] at h

  set t := k + ⌈‖a‖⌉₊ + 1
  have h1 := hscale t

  have h2 : (↑t : ℝ) - ‖a‖ ≤ ‖a + (↑t : ℂ)‖ := by
    have h : ‖(↑t : ℂ)‖ ≤ ‖a‖ + ‖a + (↑t : ℂ)‖ := by
      calc ‖(↑t : ℂ)‖ = ‖-a + (a + ↑t)‖ := by ring_nf
        _ ≤ ‖-a‖ + ‖a + ↑t‖ := norm_add_le _ _
        _ = ‖a‖ + ‖a + ↑t‖ := by rw [norm_neg]
    rw [Complex.norm_natCast] at h
    linarith

  have h3 : (k : ℝ) < ↑t - ‖a‖ := by
    have h_ceil : ‖a‖ ≤ ↑⌈‖a‖⌉₊ := Nat.le_ceil ‖a‖
    show (k : ℝ) < ↑(k + ⌈‖a‖⌉₊ + 1) - ‖a‖
    push_cast
    linarith
  linarith

end ConcreteMeasSupp

namespace Meas

end Meas

namespace ConcreteMeasSupp

variable {X : Type*} [TopologicalSpace X]

theorem pointwiseLimitOfCLM_continuous
    {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    (μ : ℕ → (C(X, ℂ) →L[ℂ] ℂ))
    (g : C(X, ℂ) →ₗ[ℂ] ℂ)
    (hlim : ∀ f : C(X, ℂ), Tendsto (fun n => μ n f) atTop (nhds (g f))) :
    Continuous g := by

  have htendsto : Tendsto (fun n (f : C(X, ℂ)) => μ n f) atTop (nhds (fun f => g f)) := by
    rw [tendsto_pi_nhds]
    exact hlim


  exact (continuousLinearMapOfTendsto μ htendsto).cont

theorem weakStarCauchyLimit_exists
    {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    (μ : ℕ → (C(X, ℂ) →L[ℂ] ℂ))
    (_hcauchy : IsWeakStarCauchy μ)
    (_hlim : ∀ f : C(X, ℂ), ∃ c : ℂ, Tendsto (fun n => μ n f) atTop (nhds c)) :
    ∃ (μ₀ : C(X, ℂ) →L[ℂ] ℂ), TendstoWeakStar μ μ₀ := by

  let limfun : C(X, ℂ) → ℂ := fun f => (_hlim f).choose
  have hlim_spec : ∀ f, Tendsto (fun n => μ n f) atTop (nhds (limfun f)) :=
    fun f => (_hlim f).choose_spec

  have htendsto_pi : Tendsto (fun n => (fun f => μ n f)) atTop (𝓝 limfun) := by
    rw [tendsto_pi_nhds]
    exact hlim_spec

  let g : C(X, ℂ) →ₗ[ℂ] ℂ :=
    linearMapOfTendsto limfun (fun n => (μ n).toLinearMap) htendsto_pi

  have hg_eq : ∀ f, g f = limfun f := fun f => by
    simp [g, linearMapOfTendsto]

  have hg_lim : ∀ f, Tendsto (fun n => μ n f) atTop (nhds (g f)) := by
    intro f; rw [hg_eq]; exact hlim_spec f
  have hcont : Continuous g := pointwiseLimitOfCLM_continuous μ g hg_lim

  let μ₀ : C(X, ℂ) →L[ℂ] ℂ := ⟨g, hcont⟩

  exact ⟨μ₀, fun f => by exact hg_lim f⟩

theorem seqComplete
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    (μ : ℕ → (C(X, ℂ) →L[ℂ] ℂ)) (hcauchy : IsWeakStarCauchy μ) :
    ∃ (K : Set X) (μ₀ : C(X, ℂ) →L[ℂ] ℂ), IsCompact K ∧
      IsSupportedIn μ₀ K ∧ TendstoWeakStar μ μ₀ := by

  obtain ⟨K, hK, hsupp⟩ := cauchySeq_supportedIn_compact μ hcauchy

  have hlim : ∀ f : C(X, ℂ), ∃ c : ℂ, Tendsto (fun n => μ n f) atTop (nhds c) := by
    intro f
    exact ⟨_, (hcauchy f).tendsto_limUnder⟩

  obtain ⟨μ₀, hμ₀_eq⟩ := weakStarCauchyLimit_exists μ hcauchy hlim

  refine ⟨K, μ₀, hK, ?_, ?_⟩

  · intro f hf
    have : ∀ n, μ n f = 0 := fun n => hsupp n f hf
    have htend : Tendsto (fun n => μ n f) atTop (nhds (μ₀ f)) := hμ₀_eq f
    have htend0 : Tendsto (fun n => μ n f) atTop (nhds 0) := by
      simp [this]
    exact tendsto_nhds_unique htend htend0

  · exact hμ₀_eq

def functionalSupport (μ : C(X, ℂ) →L[ℂ] ℂ) : Set X :=
  {x : X | ∀ U ∈ nhds x, ∃ g : C(X, ℂ), (∀ y, y ∉ U → g y = 0) ∧ μ g ≠ 0}

lemma isClosed_functionalSupport (μ : C(X, ℂ) →L[ℂ] ℂ) :
    IsClosed (functionalSupport μ) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  simp only [Set.mem_compl_iff, functionalSupport, Set.mem_setOf_eq, not_forall] at hx
  obtain ⟨U, hU_nhds, hU_prop⟩ := hx
  push Not at hU_prop


  obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hU_nhds
  apply mem_nhds_iff.mpr
  refine ⟨V, ?_, hVopen, hxV⟩
  intro y hyV
  simp only [Set.mem_compl_iff, functionalSupport, Set.mem_setOf_eq, not_forall]
  exact ⟨U, mem_nhds_iff.mpr ⟨V, hVU, hVopen, hyV⟩,
    by push Not; exact hU_prop⟩

theorem not_in_support_local_vanishing
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    (μ : C(X, ℂ) →L[ℂ] ℂ) (x : X) (hx : x ∉ functionalSupport μ) :
    ∃ U ∈ nhds x, ∀ g : C(X, ℂ), (∀ y, y ∉ U → g y = 0) → μ g = 0 := by
  simp only [functionalSupport, Set.mem_setOf_eq, not_forall] at hx
  obtain ⟨U, hU, hprop⟩ := hx
  push Not at hprop
  exact ⟨U, hU, hprop⟩

theorem exists_pou_subordinate_open
    {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    (S : Set X) (hS : IsOpen S)
    (U : X → Set X) (hUo : ∀ x, IsOpen (U x)) (hUmem : ∀ x ∈ S, x ∈ U x) :
    ∃ (ρ : ℕ → C(X, ℝ)) (idx : ℕ → X),
      (∀ n, ρ n ≠ 0 → idx n ∈ S) ∧
      (∀ n, ∀ x, 0 ≤ ρ n x) ∧
      (∀ n, tsupport (ρ n) ⊆ U (idx n)) ∧
      (LocallyFinite (fun n => Function.support (ρ n))) ∧
      (∀ x ∈ S, ∑ᶠ n, ρ n x = 1) := by
  sorry

noncomputable def toComplexCM : C(ℝ, ℂ) := ⟨Complex.ofReal, Complex.continuous_ofReal⟩

set_option maxHeartbeats 400000 in
theorem pou_decomposition
    {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    (S : Set X) (hS : IsOpen S)
    (f : C(X, ℂ)) (hfS : ∀ x ∉ S, f x = 0)
    (U : X → Set X) (hUo : ∀ x, IsOpen (U x)) (hUmem : ∀ x ∈ S, x ∈ U x) :
    ∃ (g : ℕ → C(X, ℂ)) (idx : ℕ → X),
      (∀ n, g n ≠ 0 → idx n ∈ S) ∧
      (∀ n, ∀ y, y ∉ U (idx n) → g n y = 0) ∧
      LocallyFinite (fun n => Function.support (⇑(g n))) ∧
      (∀ x, HasSum (fun n => g n x) (f x)) := by
  obtain ⟨ρ, idx, hidx, _, hsubord, hlf, hsum1⟩ := exists_pou_subordinate_open S hS U hUo hUmem
  refine ⟨fun n => toComplexCM.comp (ρ n) * f, idx, ?_, ?_, ?_, ?_⟩
  ·
    intro n hgn; apply hidx n; intro hρn; apply hgn; ext x
    simp only [ContinuousMap.mul_apply, ContinuousMap.comp_apply, ContinuousMap.zero_apply, hρn]
    simp only [toComplexCM, ContinuousMap.coe_mk, Complex.ofReal_zero, zero_mul]
  ·
    intro n y hy
    show toComplexCM ((ρ n) y) * f y = 0
    have : y ∉ Function.support (ρ n) := fun hmem => hy (hsubord n (subset_tsupport _ hmem))
    rw [show (ρ n) y = 0 from Function.notMem_support.mp this]
    simp [toComplexCM, ContinuousMap.coe_mk, Complex.ofReal_zero]
  ·
    apply hlf.subset
    intro n x hx
    simp only [ContinuousMap.mul_apply, ContinuousMap.comp_apply, Function.mem_support] at hx ⊢
    intro hρn
    apply hx
    simp [hρn, toComplexCM, ContinuousMap.coe_mk, Complex.ofReal_zero]
  ·
    intro x
    by_cases hxS : x ∈ S
    ·
      set s := (hlf.point_finite x).toFinset
      have hs_mem : ∀ n, n ∈ s ↔ (ρ n) x ≠ 0 := fun n => by
        simp [s, Set.Finite.mem_toFinset, Function.mem_support]
      have hvanish : ∀ n ∉ s, (toComplexCM.comp (ρ n) * f) x = 0 := fun n hn => by
        show toComplexCM ((ρ n) x) * f x = 0
        rw [show (ρ n) x = 0 from not_not.mp ((hs_mem n).not.mp hn)]
        simp [toComplexCM, ContinuousMap.coe_mk, Complex.ofReal_zero]
      suffices h : ∑ n ∈ s, (toComplexCM.comp (ρ n) * f) x = f x by
        rw [← h]; exact hasSum_sum_of_ne_finset_zero hvanish
      show ∑ n ∈ s, toComplexCM ((ρ n) x) * f x = f x
      rw [← Finset.sum_mul]
      have hfs : ∑ n ∈ s, (ρ n) x = 1 := by
        rw [← finsum_eq_sum_of_support_subset _
            (fun n hn => (hs_mem n).mpr (Function.mem_support.mp hn))]
        exact hsum1 x hxS
      show (∑ n ∈ s, toComplexCM ((ρ n) x)) * f x = f x
      simp only [toComplexCM, ContinuousMap.coe_mk]
      have : (∑ n ∈ s, ((ρ n) x : ℂ)) = 1 := by exact_mod_cast hfs
      rw [this, one_mul]
    ·
      have hfx : f x = 0 := hfS x hxS
      show HasSum (fun n => toComplexCM ((ρ n) x) * f x) (f x)
      simp [hfx]

theorem pou_kills_functional
    {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    (μ : C(X, ℂ) →L[ℂ] ℂ) (f : C(X, ℂ))
    (g : ℕ → C(X, ℂ))
    (hlf : LocallyFinite (fun n => Function.support (⇑(g n))))
    (hpw : ∀ x, HasSum (fun n => g n x) (f x))
    (hzero : ∀ n, μ (g n) = 0) :
    μ f = 0 := by

  have hsum : HasSum g f := by
    rw [HasSum]
    rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly]
    intro u hu x
    obtain ⟨t, ht_nhd, ht_fin⟩ := hlf x
    refine ⟨t, ht_nhd, ?_⟩
    simp only [SummationFilter.unconditional, Filter.eventually_atTop]
    use ht_fin.toFinset
    intro s hs y hy
    have hvan : ∀ n ∉ ht_fin.toFinset, (g n) y = 0 := by
      intro n hn
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hn
      have : y ∉ Function.support (⇑(g n)) := by
        intro hy_supp
        exact hn ⟨y, Set.mem_inter hy_supp hy⟩
      exact Function.notMem_support.mp this
    suffices h : (∑ n ∈ s, g n) y = f y by
      rw [h]; exact refl_mem_uniformity hu
    simp only [ContinuousMap.sum_apply]
    have h1 : ∑ n ∈ s, (g n) y = ∑ n ∈ ht_fin.toFinset, (g n) y :=
      (Finset.sum_subset hs (fun n _ hn' => hvan n hn')).symm
    rw [h1]
    exact (hasSum_sum_of_ne_finset_zero (fun n hn => hvan n hn)).unique (hpw y)

  have hμsum : HasSum (fun n => μ (g n)) (μ f) := μ.hasSum hsum

  have hμzero : HasSum (fun _ : ℕ => (0 : ℂ)) (μ f) := by
    convert hμsum using 1; ext n; exact (hzero n).symm

  exact hμzero.unique hasSum_zero

theorem partitionOfUnity_kills_on_openSet
    {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    (μ : C(X, ℂ) →L[ℂ] ℂ) (f : C(X, ℂ))
    (S : Set X) (hS : IsOpen S)
    (hfS : ∀ x ∉ S, f x = 0)
    (U : X → Set X)
    (hUo : ∀ x, IsOpen (U x))
    (hUmem : ∀ x ∈ S, x ∈ U x)
    (hUkill : ∀ x ∈ S, ∀ g : C(X, ℂ), (∀ y, y ∉ U x → g y = 0) → μ g = 0) :
    μ f = 0 := by

  obtain ⟨g, idx, hidx, hsupp, hlf, hpw⟩ := pou_decomposition S hS f hfS U hUo hUmem

  have hzero : ∀ n, μ (g n) = 0 := fun n => by
    by_cases hgn : g n = 0
    · rw [hgn]; exact map_zero μ
    · exact hUkill (idx n) (hidx n hgn) (g n) (hsupp n)


  exact pou_kills_functional μ f g hlf hpw hzero

theorem functional_kills_vanishing_on_closed_support
    {X : Type*} [TopologicalSpace X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    (μ : C(X, ℂ) →L[ℂ] ℂ) (f : C(X, ℂ))
    (hf : ∀ x ∈ functionalSupport μ, f x = 0)
    (hloc : ∀ x ∉ functionalSupport μ, ∃ U ∈ nhds x,
      ∀ g : C(X, ℂ), (∀ y, y ∉ U → g y = 0) → μ g = 0) :
    μ f = 0 := by

  set S := (functionalSupport μ)ᶜ with hS_def
  have hS : IsOpen S := (isClosed_functionalSupport μ).isOpen_compl

  have hfS : ∀ x ∉ S, f x = 0 := by
    intro x hx
    exact hf x (Set.notMem_compl_iff.mp hx)


  have hloc' : ∀ x ∈ S, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      ∀ g : C(X, ℂ), (∀ y, y ∉ V → g y = 0) → μ g = 0 := by
    intro x hxS
    have hx : x ∉ functionalSupport μ := hxS
    obtain ⟨U, hU_nhds, hU_kill⟩ := hloc x hx
    obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hU_nhds
    exact ⟨V, hVopen, hxV, fun g hg => hU_kill g (fun y hy => hg y (fun h => hy (hVU h)))⟩

  choose V hV_open hV_mem hV_kill using hloc'

  have : ∀ x : X, ∃ W : Set X, IsOpen W ∧
      (x ∈ S → x ∈ W) ∧
      (x ∈ S → ∀ g : C(X, ℂ), (∀ y, y ∉ W → g y = 0) → μ g = 0) := by
    intro x
    by_cases hx : x ∈ S
    · exact ⟨V x hx, hV_open x hx, fun _ => hV_mem x hx, fun _ => hV_kill x hx⟩
    · exact ⟨Set.univ, isOpen_univ, fun h => absurd h hx, fun h => absurd h hx⟩
  choose W hW_open hW_mem hW_kill using this

  exact partitionOfUnity_kills_on_openSet μ f S hS hfS W
    (fun x => hW_open x)
    (fun x hxS => hW_mem x hxS)
    (fun x hxS g hg => hW_kill x hxS g hg)

theorem prop_3_3_vanishing_on_support
    [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    (μ : C(X, ℂ) →L[ℂ] ℂ)
    (f : C(X, ℂ))
    (hf : ∀ x ∈ functionalSupport μ, f x = 0) :
    μ f = 0 := by
  exact functional_kills_vanishing_on_closed_support μ f hf
    (fun x hx => not_in_support_local_vanishing μ x hx)

end ConcreteMeasSupp

end
