/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.LieGroups.code.ContinuousRep
import Atlas.LieGroups.code.KFinite
import Atlas.LieGroups.code.SmoothVectors
import Atlas.LieGroups.code.KFiniteProps
import Atlas.LieGroups.code.IsotypicPeterWeyl
import Atlas.LieGroups.code.SmoothVectorsProps
import Atlas.LieGroups.code.CompactMeasures

set_option autoImplicit false

open scoped Topology Manifold
open MeasureTheory

noncomputable section

namespace PlancherelCompact

structure IrrFinDimRep (K : Type*) [Group K] [TopologicalSpace K]
    [CompactSpace K] where
  carrier : Type
  [instNormedAddCommGroup : NormedAddCommGroup carrier]
  [instInnerProductSpace : InnerProductSpace ℂ carrier]
  [instFiniteDimensional : FiniteDimensional ℂ carrier]
  [instCompleteSpace : CompleteSpace carrier]
  rep : ContinuousRep K carrier
  irred : rep.IsIrreducible
  unitary : rep.IsUnitary
  [nontrivial : Nontrivial carrier]

attribute [instance] IrrFinDimRep.instNormedAddCommGroup
  IrrFinDimRep.instInnerProductSpace IrrFinDimRep.instFiniteDimensional
  IrrFinDimRep.instCompleteSpace IrrFinDimRep.nontrivial

def IrrFinDimRep.dim {K : Type*} [Group K] [TopologicalSpace K]
    [CompactSpace K] (ρ : IrrFinDimRep K) : ℕ :=
  Module.finrank ℂ ρ.carrier

def IrrFinDimRep.repFourierCoeff {K : Type*} [Group K] [TopologicalSpace K]
    [CompactSpace K] [MeasureSpace K]
    (ρ : IrrFinDimRep K) (f : K → ℂ) : ρ.carrier →L[ℂ] ρ.carrier :=
  ∫ k, f k • ρ.rep.toMonoidHom k

def IrrFinDimRep.plancherelTerm {K : Type*} [Group K] [TopologicalSpace K]
    [CompactSpace K] [MeasureSpace K]
    (ρ : IrrFinDimRep K) (f₁ f₂ : K → ℂ) : ℂ :=
  (Module.finrank ℂ ρ.carrier : ℂ) *
    LinearMap.trace ℂ ρ.carrier
      (((ρ.repFourierCoeff f₁).comp
        (ContinuousLinearMap.adjoint (ρ.repFourierCoeff f₂)) : ρ.carrier →L[ℂ] ρ.carrier) :
          ρ.carrier →ₗ[ℂ] ρ.carrier)

def IrrFinDimRep.plancherelSingleTerm {K : Type*} [Group K] [TopologicalSpace K]
    [CompactSpace K] [MeasureSpace K]
    (ρ : IrrFinDimRep K) (f : K → ℂ) : ℂ :=
  (Module.finrank ℂ ρ.carrier : ℂ) *
    LinearMap.trace ℂ ρ.carrier
      ((ρ.repFourierCoeff f : ρ.carrier →L[ℂ] ρ.carrier) : ρ.carrier →ₗ[ℂ] ρ.carrier)

abbrev PeterWeylIndex
    {K : Type*} [Group K] [TopologicalSpace K] [CompactSpace K]
    (ι : Type*) (ρ : ι → IrrFinDimRep K) :=
  (i : ι) × (Fin (ρ i).dim × Fin (ρ i).dim)

noncomputable def peterWeyl_orthonormal_basis
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [MeasureSpace K] [BorelSpace K]
    [Measure.IsHaarMeasure (volume : Measure K)]
    [IsProbabilityMeasure (volume : Measure K)]
    (ι : Type*) (ρ : ι → IrrFinDimRep K)
    (hρ_surj : ∀ (σ : IrrFinDimRep K), ∃ (i : ι), Nonempty (RepEquiv σ.rep (ρ i).rep))
    (hρ_inj : ∀ (i j : ι), Nonempty (RepEquiv (ρ i).rep (ρ j).rep) → i = j)
    : HilbertBasis (PeterWeylIndex ι ρ) ℂ (Lp ℂ 2 (volume : Measure K)) := by
  exact sorry

theorem peterWeyl_basis_sum_eq_plancherelTerm
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [MeasureSpace K] [BorelSpace K]
    [Measure.IsHaarMeasure (volume : Measure K)]
    [IsProbabilityMeasure (volume : Measure K)]
    (ι : Type*) (ρ : ι → IrrFinDimRep K)
    (hρ_surj : ∀ (σ : IrrFinDimRep K), ∃ (i : ι), Nonempty (RepEquiv σ.rep (ρ i).rep))
    (hρ_inj : ∀ (i j : ι), Nonempty (RepEquiv (ρ i).rep (ρ j).rep) → i = j)
    (f₁ f₂ : K → ℂ)
    (hf₁ : MemLp f₁ 2 (volume : Measure K))
    (hf₂ : MemLp f₂ 2 (volume : Measure K))
    (i : ι) :
    let b := peterWeyl_orthonormal_basis ι ρ hρ_surj hρ_inj
    ∑' (jk : Fin (ρ i).dim × Fin (ρ i).dim),
      @inner ℂ _ _ (hf₂.toLp f₂) (b ⟨i, jk⟩) * @inner ℂ _ _ (b ⟨i, jk⟩) (hf₁.toLp f₁) =
    (ρ i).plancherelTerm f₁ f₂ := by
  sorry

section proposition_4_1

theorem proposition_4_1_plancherel_hasSum
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [MeasureSpace K] [BorelSpace K]
    [Measure.IsHaarMeasure (volume : Measure K)]
    [IsProbabilityMeasure (volume : Measure K)]
    {ι : Type*} {ρ : ι → IrrFinDimRep K}
    (hρ_surj : ∀ (σ : IrrFinDimRep K), ∃ (i : ι), Nonempty (RepEquiv σ.rep (ρ i).rep))
    (hρ_inj : ∀ (i j : ι), Nonempty (RepEquiv (ρ i).rep (ρ j).rep) → i = j)
    (f₁ f₂ : K → ℂ)
    (hf₁ : MemLp f₁ 2 (volume : Measure K))
    (hf₂ : MemLp f₂ 2 (volume : Measure K)) :
    HasSum (fun (i : ι) => (ρ i).plancherelTerm f₁ f₂)
      (@inner ℂ _ _ (hf₂.toLp f₂) (hf₁.toLp f₁)) := by

  let b := peterWeyl_orthonormal_basis ι ρ hρ_surj hρ_inj

  have hparseval := b.hasSum_inner_mul_inner (hf₂.toLp f₂) (hf₁.toLp f₁)

  have hfiber : ∀ (i : ι), HasSum
      (fun jk => @inner ℂ _ _ (hf₂.toLp f₂) (b ⟨i, jk⟩) * @inner ℂ _ _ (b ⟨i, jk⟩) (hf₁.toLp f₁))
      (∑ jk : Fin (ρ i).dim × Fin (ρ i).dim,
        @inner ℂ _ _ (hf₂.toLp f₂) (b ⟨i, jk⟩) * @inner ℂ _ _ (b ⟨i, jk⟩) (hf₁.toLp f₁)) :=
    fun i => hasSum_fintype _
  have hregroup := hparseval.sigma hfiber

  convert hregroup using 1
  ext i
  have hax := peterWeyl_basis_sum_eq_plancherelTerm ι ρ hρ_surj hρ_inj f₁ f₂ hf₁ hf₂ i
  rw [← hax, tsum_fintype]

end proposition_4_1

def convolutionOp
    {K : Type*} [Group K] [TopologicalSpace K]
    [CompactSpace K] [MeasureSpace K]
    (f : K → ℂ) (ψ : K → ℂ) : K → ℂ :=
  fun x => ∫ y, f (x * y⁻¹) * ψ y

def convolutionKernel
    {K : Type*} [Group K]
    (f : K → ℂ) : K → K → ℂ :=
  fun x y => f (x * y⁻¹)

theorem convolutionOp_eq_kernel_integral
    {K : Type*} [Group K] [TopologicalSpace K]
    [CompactSpace K] [MeasureSpace K]
    (f : K → ℂ) (ψ : K → ℂ) (x : K) :
    convolutionOp f ψ x = ∫ y, convolutionKernel f x y * ψ y := by
  rfl

@[simp]
theorem convolutionKernel_diag_eq
    {K : Type*} [Group K]
    (f : K → ℂ) (x : K) :
    convolutionKernel f x x = f 1 := by
  unfold convolutionKernel
  simp [mul_inv_cancel]

def convolutionKernelDiagIntegral
    {K : Type*} [Group K] [TopologicalSpace K]
    [CompactSpace K] [MeasureSpace K]
    (f : K → ℂ) : ℂ :=
  ∫ x : K, convolutionKernel f x x

theorem convolutionKernelDiag_eq_const
    {K : Type*} [Group K] [TopologicalSpace K]
    [CompactSpace K] [MeasureSpace K]
    (f : K → ℂ) :
    convolutionKernelDiagIntegral f = ∫ _ : K, f 1 := by
  unfold convolutionKernelDiagIntegral
  simp [convolutionKernel_diag_eq]

theorem convolutionKernelDiagIntegral_eq_eval_one
    {K : Type*} [Group K] [TopologicalSpace K]
    [CompactSpace K] [MeasureSpace K] [BorelSpace K]
    [IsProbabilityMeasure (volume : Measure K)]
    (f : K → ℂ) :
    convolutionKernelDiagIntegral f = f 1 := by
  rw [convolutionKernelDiag_eq_const]
  simp [integral_const]

noncomputable def convolutionOperatorTrace
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [MeasureSpace K] [BorelSpace K]
    [Measure.IsHaarMeasure (volume : Measure K)]
    [IsProbabilityMeasure (volume : Measure K)]
    (f : K → ℂ) : ℂ := by
  exact sorry

theorem lidskiiMercer_trace_eq_diagIntegral
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [MeasureSpace K] [BorelSpace K]
    [Measure.IsHaarMeasure (volume : Measure K)]
    [IsProbabilityMeasure (volume : Measure K)]
    (f : K → ℂ) (hf : Continuous f) :
    convolutionOperatorTrace f = convolutionKernelDiagIntegral f := by
  sorry

theorem peterWeyl_spectral_hasSum_trace
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [MeasureSpace K] [BorelSpace K]
    [Measure.IsHaarMeasure (volume : Measure K)]
    [IsProbabilityMeasure (volume : Measure K)]
    (ι : Type*) (ρ : ι → IrrFinDimRep K)
    (hρ_surj : ∀ (σ : IrrFinDimRep K), ∃ (i : ι), Nonempty (RepEquiv σ.rep (ρ i).rep))
    (hρ_inj : ∀ (i j : ι), Nonempty (RepEquiv (ρ i).rep (ρ j).rep) → i = j)
    (f : K → ℂ) (hf : Continuous f) :
    HasSum (fun (i : ι) => (ρ i).plancherelSingleTerm f)
      (convolutionOperatorTrace f) := by
  sorry

theorem peterWeyl_spectral_trace_hasSum
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [MeasureSpace K] [BorelSpace K]
    [Measure.IsHaarMeasure (volume : Measure K)]
    [IsProbabilityMeasure (volume : Measure K)]
    (ι : Type*) (ρ : ι → IrrFinDimRep K)
    (hρ_surj : ∀ (σ : IrrFinDimRep K), ∃ (i : ι), Nonempty (RepEquiv σ.rep (ρ i).rep))
    (hρ_inj : ∀ (i j : ι), Nonempty (RepEquiv (ρ i).rep (ρ j).rep) → i = j)
    (f : K → ℂ) (hf : Continuous f) :
    HasSum (fun (i : ι) => (ρ i).plancherelSingleTerm f) (convolutionKernelDiagIntegral f) := by

  have hPW := peterWeyl_spectral_hasSum_trace ι ρ hρ_surj hρ_inj f hf

  have hLM := lidskiiMercer_trace_eq_diagIntegral f hf

  rwa [hLM] at hPW

theorem plancherel_formula
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [MeasureSpace K] [BorelSpace K]
    [Measure.IsHaarMeasure (volume : Measure K)]
    [IsProbabilityMeasure (volume : Measure K)]
    {EK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK]
    {HK : Type*} [TopologicalSpace HK]
    (IK : ModelWithCorners ℝ EK HK)
    [ChartedSpace HK K] [LieGroup IK ⊤ K]
    (ι : Type*) (ρ : ι → IrrFinDimRep K)
    (hρ_surj : ∀ (σ : IrrFinDimRep K), ∃ (i : ι), Nonempty (RepEquiv σ.rep (ρ i).rep))
    (hρ_inj : ∀ (i j : ι), Nonempty (RepEquiv (ρ i).rep (ρ j).rep) → i = j)
    (f : K → ℂ) (hf : ContMDiff IK 𝓘(ℝ, ℂ) ⊤ f) :
    f 1 = ∑' (i : ι), (ρ i).plancherelSingleTerm f := by


  have hspec := peterWeyl_spectral_trace_hasSum ι ρ hρ_surj hρ_inj f hf.continuous


  rw [convolutionKernelDiagIntegral_eq_eval_one] at hspec

  exact hspec.tsum_eq.symm

theorem plancherel_formula_summable
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [MeasureSpace K] [BorelSpace K]
    [Measure.IsHaarMeasure (volume : Measure K)]
    [IsProbabilityMeasure (volume : Measure K)]
    {EK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK]
    {HK : Type*} [TopologicalSpace HK]
    (IK : ModelWithCorners ℝ EK HK)
    [ChartedSpace HK K] [LieGroup IK ⊤ K]
    (ι : Type*) (ρ : ι → IrrFinDimRep K)
    (hρ_surj : ∀ (σ : IrrFinDimRep K), ∃ (i : ι), Nonempty (RepEquiv σ.rep (ρ i).rep))
    (hρ_inj : ∀ (i j : ι), Nonempty (RepEquiv (ρ i).rep (ρ j).rep) → i = j)
    (f : K → ℂ) (hf : ContMDiff IK 𝓘(ℝ, ℂ) ⊤ f) :
    Summable (fun (i : ι) => ‖(ρ i).plancherelSingleTerm f‖) :=
  (peterWeyl_spectral_trace_hasSum ι ρ hρ_surj hρ_inj f hf.continuous).summable.norm

set_option maxHeartbeats 1600000 in
theorem exists_dirac_sequence
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasureSpace G] [BorelSpace G]
    [Measure.IsHaarMeasure (volume : Measure G)] :
    ∃ (φ : ℕ → G → ℝ),
      (∀ (n : ℕ), Continuous (φ n)) ∧
      (∀ (n : ℕ), HasCompactSupport (φ n)) ∧
      (∀ (f : G → ℂ), Continuous f → HasCompactSupport f →
        Filter.Tendsto (fun (n : ℕ) => ∫ (g : G), (φ n g : ℂ) * f g)
          Filter.atTop (nhds (f 1))) := by
  obtain ⟨U, hU⟩ := (nhds (1 : G)).exists_antitone_basis
  have hbump : ∀ n, ∃ (ψ : C(G, ℝ)),
      ψ 1 = 1 ∧ IsCompact (tsupport ψ) ∧ tsupport ψ ⊆ U n ∧
      (∀ x, ψ x ∈ Set.Icc 0 1) := by
    intro n
    have hUn : U n ∈ nhds (1 : G) := hU.toHasBasis.mem_of_mem trivial
    obtain ⟨V, hV_sub, hV_open, h1V⟩ := mem_nhds_iff.mp hUn
    obtain ⟨f, hf_eq, hf_compact, hf_supp, hf_range⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen isCompact_singleton hV_open
        (Set.singleton_subset_iff.mpr h1V)
    exact ⟨f, by simp [hf_eq (Set.mem_singleton 1)],
           hf_compact, hf_supp.trans hV_sub, hf_range⟩
  choose ψ hψ_one hψ_compact hψ_supp hψ_range using hbump
  have hψ_nonneg : ∀ n, 0 ≤ (ψ n : G → ℝ) := fun n x => (hψ_range n x).1
  have hψ_int_pos : ∀ n, (0 : ℝ) < ∫ x, (ψ n) x := by
    intro n
    exact (ψ n).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hψ_compact n) (hψ_nonneg n) (by rw [hψ_one n]; exact one_ne_zero)
  set φ : ℕ → G → ℝ := fun n x => (∫ g, (ψ n) g)⁻¹ * (ψ n) x with φ_def
  have hφ_int : ∀ n, ∫ x, φ n x = 1 := by
    intro n; simp only [φ_def, ← smul_eq_mul, integral_smul]
    exact inv_mul_cancel₀ (ne_of_gt (hψ_int_pos n))
  have hψ_vanish : ∀ n x, x ∉ U n → (ψ n) x = 0 := by
    intro n x hx; by_contra h
    exact hx (hψ_supp n (subset_tsupport _ (Function.mem_support.mpr h)))
  refine ⟨φ, ?_, ?_, ?_⟩
  · exact fun n => continuous_const.mul (ψ n).continuous
  · intro n
    have : Function.support (φ n) ⊆ Function.support (ψ n : G → ℝ) := by
      intro x hx; simp only [Function.mem_support, φ_def] at hx ⊢
      intro hfx; exact hx (by simp [hfx])
    exact (hψ_compact n).of_isClosed_subset (isClosed_tsupport _) (closure_mono this)
  · intro f h_cont h_supp
    simp_rw [show ∀ n g, (φ n g : ℂ) * f g = φ n g • f g from
      fun n g => (Complex.real_smul).symm]
    obtain ⟨K, hK_compact, hK_nhds⟩ := exists_compact_mem_nhds (1 : G)
    obtain ⟨V, hV_sub, hV_open, h1V⟩ := mem_nhds_iff.mp hK_nhds
    apply tendsto_integral_peak_smul_of_integrable_of_tendsto
      hV_open.measurableSet (hV_open.mem_nhds h1V)
      (ne_of_lt (lt_of_le_of_lt (measure_mono hV_sub) hK_compact.measure_lt_top))
    · exact Filter.Eventually.of_forall fun n x =>
        mul_nonneg (inv_nonneg.mpr (hψ_int_pos n).le) (hψ_nonneg n x)
    · intro u hu h1u
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hU.toHasBasis.mem_iff.mp (hu.mem_nhds h1u)
      filter_upwards [Filter.Ici_mem_atTop N] with n hn x hx
      simp only [Pi.zero_apply, Real.dist_eq]
      simp [φ_def, hψ_vanish n x (fun h => hx (hN.2 (hU.antitone (Set.mem_Ici.mp hn) h))), hε]
    · obtain ⟨N, hN⟩ := hU.toHasBasis.mem_iff.mp (hV_open.mem_nhds h1V)
      refine tendsto_atTop_of_eventually_const (i₀ := N) (fun n hn => ?_)
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_]
      · exact hφ_int n
      · simp [φ_def, hψ_vanish n x (fun h => hx (hN.2 (hU.antitone hn h)))]
    · exact Filter.Eventually.of_forall fun n =>
        (continuous_const.mul (ψ n).continuous).aestronglyMeasurable
    · exact h_cont.integrable_of_hasCompactSupport h_supp
    · exact h_cont.continuousAt

set_option maxHeartbeats 3200000 in
theorem exists_smooth_dirac_sequence
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasureSpace G] [BorelSpace G]
    [Measure.IsHaarMeasure (volume : Measure G)]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    {HG : Type*} [TopologicalSpace HG]
    (IG : ModelWithCorners ℝ EG HG)
    [ChartedSpace HG G] [LieGroup IG ⊤ G] [T2Space G] :
    ∃ (φ : ℕ → G → ℝ),
      (∀ (n : ℕ), ContMDiff IG 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞)) (φ n)) ∧
      (∀ (n : ℕ), HasCompactSupport (φ n)) ∧
      (∀ (f : G → ℂ), Continuous f → HasCompactSupport f →
        Filter.Tendsto (fun (n : ℕ) => ∫ (g : G), (φ n g : ℂ) * f g)
          Filter.atTop (nhds (f 1))) := by
  haveI : IsManifold IG (↑(⊤ : ℕ∞)) G := IsManifold.of_le le_top

  obtain ⟨U, hU⟩ := (nhds (1 : G)).exists_antitone_basis

  have hbump : ∀ n, ∃ (ψ : SmoothBumpFunction IG (1 : G)),
      tsupport (ψ : G → ℝ) ⊆ U n := by
    intro n
    have hUn : U n ∈ nhds (1 : G) := hU.toHasBasis.mem_of_mem trivial
    obtain ⟨ψ, _, hψ_supp⟩ :=
      (SmoothBumpFunction.nhds_basis_tsupport (I := IG) (1 : G)).mem_iff.mp hUn
    exact ⟨ψ, hψ_supp⟩
  choose ψ hψ_supp using hbump

  have hψ_nonneg : ∀ n, 0 ≤ (ψ n : G → ℝ) := fun n x => (ψ n).nonneg
  have hψ_one : ∀ n, (ψ n : G → ℝ) (1 : G) = 1 := fun n => (ψ n).eq_one
  have hψ_cont : ∀ n, Continuous (ψ n : G → ℝ) := fun n => (ψ n).continuous
  have hψ_compact : ∀ n, HasCompactSupport (ψ n : G → ℝ) := fun n => (ψ n).hasCompactSupport
  have hψ_int_pos : ∀ n, (0 : ℝ) < ∫ x, (ψ n : G → ℝ) x := by
    intro n
    exact (hψ_cont n).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hψ_compact n) (hψ_nonneg n) (by rw [hψ_one n]; exact one_ne_zero)

  set φ : ℕ → G → ℝ := fun n x =>
    (∫ g, (ψ n : G → ℝ) g)⁻¹ * (ψ n : G → ℝ) x with φ_def
  have hφ_int : ∀ n, ∫ x, φ n x = 1 := by
    intro n; simp only [φ_def, ← smul_eq_mul, integral_smul]
    exact inv_mul_cancel₀ (ne_of_gt (hψ_int_pos n))
  have hψ_vanish : ∀ n x, x ∉ U n → (ψ n : G → ℝ) x = 0 := by
    intro n x hx; by_contra h
    exact hx (hψ_supp n (subset_tsupport _ (Function.mem_support.mpr h)))
  refine ⟨φ, ?_, ?_, ?_⟩

  · intro n
    have h : ContMDiff IG 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞)) (ψ n : G → ℝ) :=
      SmoothBumpFunction.contMDiff (ψ n)
    have hconst : ContMDiff IG 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞))
        (fun _ : G => (∫ g, (ψ n : G → ℝ) g)⁻¹) :=
      (contMDiff_const (n := ⊤)).of_le le_top
    change ContMDiff IG 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞))
      (fun x => (∫ g, (ψ n : G → ℝ) g)⁻¹ • (ψ n : G → ℝ) x)
    exact hconst.smul h

  · intro n
    have : Function.support (φ n) ⊆ Function.support (ψ n : G → ℝ) := by
      intro x hx; simp only [Function.mem_support, φ_def] at hx ⊢
      intro hfx; exact hx (by simp [hfx])
    exact (hψ_compact n).of_isClosed_subset (isClosed_tsupport _) (closure_mono this)

  · intro f h_cont h_supp
    simp_rw [show ∀ n g, (φ n g : ℂ) * f g = φ n g • f g from
      fun n g => (Complex.real_smul).symm]
    obtain ⟨K, hK_compact, hK_nhds⟩ := exists_compact_mem_nhds (1 : G)
    obtain ⟨V, hV_sub, hV_open, h1V⟩ := mem_nhds_iff.mp hK_nhds
    apply tendsto_integral_peak_smul_of_integrable_of_tendsto
      hV_open.measurableSet (hV_open.mem_nhds h1V)
      (ne_of_lt (lt_of_le_of_lt (measure_mono hV_sub) hK_compact.measure_lt_top))
    · exact Filter.Eventually.of_forall fun n x =>
        mul_nonneg (inv_nonneg.mpr (hψ_int_pos n).le) (hψ_nonneg n x)
    · intro u hu h1u
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := hU.toHasBasis.mem_iff.mp (hu.mem_nhds h1u)
      filter_upwards [Filter.Ici_mem_atTop N] with n hn x hx
      simp only [Pi.zero_apply, Real.dist_eq]
      simp [φ_def, hψ_vanish n x
        (fun h => hx (hN.2 (hU.antitone (Set.mem_Ici.mp hn) h))), hε]
    · obtain ⟨N, hN⟩ := hU.toHasBasis.mem_iff.mp (hV_open.mem_nhds h1V)
      refine tendsto_atTop_of_eventually_const (i₀ := N) (fun n hn => ?_)
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_]
      · exact hφ_int n
      · simp [φ_def, hψ_vanish n x (fun h => hx (hN.2 (hU.antitone hn h)))]
    · exact Filter.Eventually.of_forall fun n =>
        (continuous_const.mul (hψ_cont n)).aestronglyMeasurable
    · exact h_cont.integrable_of_hasCompactSupport h_supp
    · exact h_cont.continuousAt

set_option maxHeartbeats 1600000 in
theorem cc_seq_converges_to_dirac
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasureSpace G] [BorelSpace G]
    [Measure.IsHaarMeasure (volume : Measure G)]
    (g₀ : G) :
    ∃ (ψ : ℕ → G → ℝ),
      (∀ (n : ℕ), Continuous (ψ n)) ∧
      (∀ (n : ℕ), HasCompactSupport (ψ n)) ∧
      (∀ (f : G → ℂ), Continuous f → HasCompactSupport f →
        Filter.Tendsto (fun (n : ℕ) => ∫ (g : G), (ψ n g : ℂ) * f g)
          Filter.atTop (nhds (f g₀))) := by

  obtain ⟨φ, hφ_cont, hφ_supp, hφ_conv⟩ := @exists_dirac_sequence G _ _ _ _ _ _ _ _

  refine ⟨fun n g => φ n (g₀⁻¹ * g), ?_, ?_, ?_⟩

  · intro n
    exact (hφ_cont n).comp (continuous_const.mul continuous_id)

  · intro n
    exact (hφ_supp n).comp_homeomorph (Homeomorph.mulLeft g₀⁻¹)

  · intro f hf_cont hf_supp


    have key : ∀ n, ∫ g, (φ n (g₀⁻¹ * g) : ℂ) * f g = ∫ h, (φ n h : ℂ) * f (g₀ * h) := by
      intro n
      rw [show (fun g => (φ n (g₀⁻¹ * g) : ℂ) * f g) =
          fun g => ((fun h => (φ n h : ℂ) * f (g₀ * h)) (g₀⁻¹ * g)) from by
        ext g; simp [mul_inv_cancel_left]]
      exact @MeasureTheory.integral_mul_left_eq_self G ℂ _ _ _ (volume) _ _ _
        (fun h => (φ n h : ℂ) * f (g₀ * h)) g₀⁻¹
    simp_rw [key]

    have hfg : Continuous (f ∘ (g₀ * ·)) := hf_cont.comp (continuous_const.mul continuous_id)
    have hfg_supp : HasCompactSupport (f ∘ (g₀ * ·)) :=
      hf_supp.comp_homeomorph (Homeomorph.mulLeft g₀)
    have := hφ_conv (f ∘ (g₀ * ·)) hfg hfg_supp
    simp only [Function.comp, mul_one] at this
    convert this using 1

lemma concreteDiracEmbed_apply_eq'
    {X : Type*} [TopologicalSpace X]
    (σ : X →₀ ℂ) (f : C(X, ℂ)) :
    (concreteDiracEmbed X σ) f = ∑ x ∈ σ.support, σ x * f x := by
  unfold concreteDiracEmbed
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  change topDualPairing ℂ C(X, ℂ) (∑ x ∈ σ.support, σ x • concreteDirac X x) f
    = ∑ x ∈ σ.support, σ x * f x
  rw [map_sum, LinearMap.sum_apply]
  exact Finset.sum_congr rfl (fun _ _ => rfl)

theorem finitely_supported_seq_dense_in_measures
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X] [T2Space X]
    (μ : C(X, ℂ) →L[ℂ] ℂ) :
    ∃ (μ_seq : ℕ → C(X, ℂ) →L[ℂ] ℂ),

      (∀ n, ∃ (S : Finset X) (c : X → ℂ),
        ∀ (f : C(X, ℂ)), μ_seq n f = ∑ x ∈ S, c x * f x) ∧

      (∀ (f : C(X, ℂ)), Filter.Tendsto (fun n => μ_seq n f)
          Filter.atTop (nhds (μ f))) := by
  obtain ⟨σ_seq, hconv⟩ := lemma_3_4_seq_dense_concrete X (μ : WeakDual ℂ C(X, ℂ))
  refine ⟨fun n => concreteDiracEmbed X (σ_seq n), ?_, ?_⟩
  · intro n
    exact ⟨(σ_seq n).support, fun x => σ_seq n x,
      fun f => concreteDiracEmbed_apply_eq' (σ_seq n) f⟩
  · intro f
    exact ((WeakBilin.eval_continuous _ f).tendsto _).comp hconv

theorem compactly_supported_measure_to_clm
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasureSpace G] [BorelSpace G]
    [Measure.IsHaarMeasure (volume : Measure G)]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (hμ : IsCompact μ.support) :
    ∃ (Φ : C(G, ℂ) →L[ℂ] ℂ), ∀ (f : C(G, ℂ)), Φ f = ∫ (g : G), f g ∂μ := by

  have hfin : IsFiniteMeasure μ := by
    constructor
    calc μ Set.univ = μ (μ.support ∪ μ.supportᶜ) := by rw [Set.union_compl_self]
    _ ≤ μ μ.support + μ μ.supportᶜ := measure_union_le _ _
    _ = μ μ.support + 0 := by rw [μ.measure_compl_support]
    _ = μ μ.support := by ring
    _ < ⊤ := hμ.measure_lt_top

  have hrestr : μ = μ.restrict μ.support := by
    symm; rw [Measure.restrict_eq_self_of_ae_mem]
    rw [ae_iff]; exact μ.measure_compl_support

  have hint : ∀ (f : C(G, ℂ)), Integrable (fun g => f g) μ := by
    intro f
    rw [hrestr]
    exact ContinuousOn.integrableOn_compact hμ f.continuous.continuousOn

  let linMap : C(G, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ g, f g ∂μ
      map_add' := fun f₁ f₂ => by
        simp only [ContinuousMap.add_apply]
        exact integral_add (hint f₁) (hint f₂)
      map_smul' := fun c f => by
        simp only [ContinuousMap.smul_apply, RingHom.id_apply]
        exact integral_smul c _ }

  have hcont : Continuous linMap := by
    apply continuous_iff_continuousAt.mpr
    intro f₀
    apply MeasureTheory.continuousAt_of_dominated
      (F := fun (f : C(G, ℂ)) (g : G) => f g)
      (bound := fun g => ‖f₀ g‖ + 1)
    ·
      filter_upwards with f
      exact (map_continuous f).aestronglyMeasurable
    ·
      have hbasis := nhds_basis_uniformity
        ContinuousMap.hasBasis_compactConvergenceUniformity (x := f₀)
      rw [hbasis.eventually_iff]
      refine ⟨(μ.support, {p : ℂ × ℂ | dist p.1 p.2 < 1}),
        ⟨hμ, Metric.dist_mem_uniformity (by norm_num : (1:ℝ) > 0)⟩, ?_⟩
      intro f hf
      simp only [Set.mem_setOf_eq] at hf
      rw [ae_iff]
      apply le_antisymm _ (zero_le _)
      calc μ {g | ¬(‖f g‖ ≤ ‖f₀ g‖ + 1)} ≤ μ μ.supportᶜ := by
            apply measure_mono
            intro g hg
            simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hg ⊢
            intro hgs
            have hdist : dist (f g) (f₀ g) < 1 := hf g hgs
            rw [Complex.dist_eq] at hdist
            have : ‖f g‖ ≤ ‖f₀ g‖ + ‖f g - f₀ g‖ := by
              calc ‖f g‖ = ‖f₀ g + (f g - f₀ g)‖ := by ring_nf
              _ ≤ ‖f₀ g‖ + ‖f g - f₀ g‖ := norm_add_le _ _
            linarith
      _ = 0 := μ.measure_compl_support
    ·
      apply Integrable.add (hint f₀ |>.norm)
      exact integrable_const 1
    ·
      exact Filter.Eventually.of_forall (fun g => (continuous_eval_const g).continuousAt)
  exact ⟨⟨linMap, hcont⟩, fun f => rfl⟩

theorem cc_seq_dense_approx_finsupp
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasureSpace G] [BorelSpace G]
    [Measure.IsHaarMeasure (volume : Measure G)]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (hμ : IsCompact μ.support) :

    ∃ (S : ℕ → Finset G) (c : ℕ → G → ℂ),
      ∀ (f : G → ℂ), Continuous f →
        Filter.Tendsto (fun n => ∑ x ∈ S n, c n x * f x)
          Filter.atTop (nhds (∫ (g : G), f g ∂μ)) := by


  obtain ⟨Φ, hΦ⟩ := compactly_supported_measure_to_clm μ hμ

  obtain ⟨μ_seq, hfin, hconv⟩ := finitely_supported_seq_dense_in_measures Φ

  choose S c hSc using hfin

  refine ⟨S, c, fun f hf => ?_⟩

  let f' : C(G, ℂ) := ⟨f, hf⟩

  have hconv_f := hconv f'


  rw [show (∫ (g : G), f g ∂μ) = Φ f' from (hΦ f').symm]
  convert hconv_f using 1
  ext n
  exact (hSc n f').symm

lemma hasCompactSupport_finset_sum' {α β ι : Type*} [TopologicalSpace α] [AddCommMonoid β]
    [TopologicalSpace β] {F : Finset ι} {f : ι → α → β}
    (hf : ∀ i ∈ F, HasCompactSupport (f i)) :
    HasCompactSupport (fun x => ∑ i ∈ F, f i x) := by
  induction F using Finset.cons_induction with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | cons i s his ih =>
    have : (fun x => ∑ j ∈ Finset.cons i s his, f j x) =
        f i + (fun x => ∑ j ∈ s, f j x) := by
      ext x; simp [Finset.sum_cons, Pi.add_apply]
    rw [this]
    exact (hf i (Finset.mem_cons_self i s)).add
      (ih (fun j hj => hf j (Finset.mem_cons.mpr (Or.inr hj))))

theorem finsupp_in_seq_closure_cc
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasureSpace G] [BorelSpace G]
    [Measure.IsHaarMeasure (volume : Measure G)]
    (dirac_approx : ∀ (g₀ : G), ∃ (ψ : ℕ → G → ℝ),
      (∀ (n : ℕ), Continuous (ψ n)) ∧
      (∀ (n : ℕ), HasCompactSupport (ψ n)) ∧
      (∀ (f : G → ℂ), Continuous f → HasCompactSupport f →
        Filter.Tendsto (fun (n : ℕ) => ∫ (g : G), (ψ n g : ℂ) * f g)
          Filter.atTop (nhds (f g₀))))
    (F : Finset G) (a : G → ℂ) :
    ∃ (ψ : ℕ → G → ℂ),
      (∀ n, Continuous (ψ n)) ∧
      (∀ n, HasCompactSupport (ψ n)) ∧
      (∀ f : G → ℂ, Continuous f → HasCompactSupport f →
        Filter.Tendsto (fun n => ∫ g, ψ n g * f g)
          Filter.atTop (nhds (∑ x ∈ F, a x * f x))) := by

  choose ψ_pt hcont_pt hsupp_pt hconv_pt using fun x => dirac_approx x

  refine ⟨fun n g => ∑ x ∈ F, a x * (ψ_pt x n g : ℂ), ?_, ?_, ?_⟩
  ·
    intro n
    apply continuous_finset_sum
    intro x _
    exact continuous_const.mul (Complex.continuous_ofReal.comp (hcont_pt x n))
  ·
    intro n
    exact hasCompactSupport_finset_sum' fun x _ =>
      ((hsupp_pt x n).comp_left (g := Complex.ofReal) Complex.ofReal_zero).mul_left

  ·
    intro f hf hf_supp


    have key : ∀ x ∈ F, Filter.Tendsto
        (fun n => a x * ∫ g, (ψ_pt x n g : ℂ) * f g)
        Filter.atTop (nhds (a x * f x)) := by
      intro x _
      exact (hconv_pt x f hf hf_supp).const_mul (a x)


    suffices h : ∀ n, ∫ g, (∑ x ∈ F, a x * (ψ_pt x n g : ℂ)) * f g =
        ∑ x ∈ F, a x * ∫ g, (ψ_pt x n g : ℂ) * f g by
      simp_rw [h]
      exact tendsto_finset_sum F (fun x hx => key x hx)
    intro n
    simp_rw [Finset.sum_mul]
    rw [integral_finset_sum]
    · congr 1; ext x
      simp_rw [mul_assoc]
      exact MeasureTheory.integral_const_mul _ _
    · intro x _
      exact ((continuous_const.mul
        (Complex.continuous_ofReal.comp (hcont_pt x n))).mul hf).integrable_of_hasCompactSupport
        hf_supp.mul_left

lemma simultaneous_diagonal_extraction
    (F : ℕ → ℕ → ℕ → ℂ) (a : ℕ → ℕ → ℂ) (b : ℕ → ℂ)
    (hF : ∀ k n, Filter.Tendsto (F k n) Filter.atTop (nhds (a k n)))
    (ha : ∀ k, Filter.Tendsto (a k) Filter.atTop (nhds (b k))) :
    ∃ m : ℕ → ℕ, ∀ k, Filter.Tendsto (fun n => F k n (m n)) Filter.atTop (nhds (b k)) := by
  have hmn : ∀ n, ∃ M, ∀ k ≤ n, dist (F k n M) (a k n) < 1 / (↑n + 1) := by
    intro n
    have hε : (0 : ℝ) < 1 / (↑n + 1) := by positivity
    have hconv : ∀ k, ∃ M, ∀ m ≥ M, dist (F k n m) (a k n) < 1 / (↑n + 1) :=
      fun k => (Metric.tendsto_atTop.mp (hF k n)) _ hε
    choose M_k hM_k using hconv
    refine ⟨(Finset.range (n + 1)).sup M_k, fun k hk => ?_⟩
    apply hM_k k
    exact le_trans (Finset.le_sup (f := M_k) (Finset.mem_range.mpr (by omega))) le_rfl
  choose m hm using hmn
  refine ⟨m, fun k => Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp (ha k)) (ε / 2) (half_pos hε)
  have h1n : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (↑n + 1)) Filter.atTop (nhds 0) := by
    simp_rw [one_div]
    exact tendsto_inv_atTop_zero.comp
      (Filter.Tendsto.atTop_add (tendsto_natCast_atTop_atTop) tendsto_const_nhds)
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp h1n) (ε / 2) (half_pos hε)
  refine ⟨max (max N₁ N₂) k, fun n hn => ?_⟩
  have hkn : k ≤ n := le_trans (le_max_right _ _) hn
  have step1 : dist (F k n (m n)) (a k n) < 1 / (↑n + 1) := hm n k hkn
  have step3 : 1 / ((↑n : ℝ) + 1) < ε / 2 := by
    have h := hN₂ n (le_trans (le_max_right N₁ N₂) (le_trans (le_max_left _ k) hn))
    simp only [dist_zero_right] at h
    rwa [Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (↑n + 1))] at h
  have step2 : dist (a k n) (b k) < ε / 2 :=
    hN₁ n (le_trans (le_max_left N₁ N₂) (le_trans (le_max_left _ k) hn))
  linarith [dist_triangle (F k n (m n)) (a k n) (b k)]

theorem exists_countable_cc_determining
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasureSpace G] [BorelSpace G]
    [Measure.IsHaarMeasure (volume : Measure G)] :
    ∃ (funs : ℕ → G → ℂ),
      (∀ k, Continuous (funs k)) ∧
      (∀ k, HasCompactSupport (funs k)) ∧
      (∀ (φ : ℕ → G → ℂ) (L : (G → ℂ) → ℂ),
        (∀ n, HasCompactSupport (φ n)) →
        (∀ k, Filter.Tendsto (fun n => ∫ g, φ n g * funs k g) Filter.atTop (nhds (L (funs k)))) →
        ∀ f : G → ℂ, Continuous f → HasCompactSupport f →
          Filter.Tendsto (fun n => ∫ g, φ n g * f g) Filter.atTop (nhds (L f))) := by
  sorry

theorem seq_closure_diagonal_extraction
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasureSpace G] [BorelSpace G]
    [Measure.IsHaarMeasure (volume : Measure G)]
    (ψ : ℕ → ℕ → G → ℂ)
    (hcont : ∀ n m, Continuous (ψ n m))
    (hsupp : ∀ n m, HasCompactSupport (ψ n m))
    (L_n : ℕ → (G → ℂ) → ℂ)
    (hinner : ∀ n (f : G → ℂ), Continuous f → HasCompactSupport f →
      Filter.Tendsto (fun m => ∫ g, ψ n m g * f g)
        Filter.atTop (nhds (L_n n f)))
    (L : (G → ℂ) → ℂ)
    (houter : ∀ (f : G → ℂ), Continuous f →
      Filter.Tendsto (fun n => L_n n f) Filter.atTop (nhds (L f))) :
    ∃ (m : ℕ → ℕ),
      (∀ n, Continuous (ψ n (m n))) ∧
      (∀ n, HasCompactSupport (ψ n (m n))) ∧
      (∀ f : G → ℂ, Continuous f → HasCompactSupport f →
        Filter.Tendsto (fun n => ∫ g, ψ n (m n) g * f g)
          Filter.atTop (nhds (L f))) := by

  obtain ⟨funs, funs_cont, funs_supp, funs_det⟩ :=
    exists_countable_cc_determining (G := G)

  obtain ⟨m, hm_conv⟩ := simultaneous_diagonal_extraction
    (fun k n m_val => ∫ g, ψ n m_val g * funs k g)
    (fun k n => L_n n (funs k))
    (fun k => L (funs k))
    (fun k n => hinner n (funs k) (funs_cont k) (funs_supp k))
    (fun k => houter (funs k) (funs_cont k))
  refine ⟨m, fun n => hcont n (m n), fun n => hsupp n (m n), ?_⟩

  intro f hf hf_supp
  exact funs_det (fun n => ψ n (m n)) L (fun n => hsupp n (m n)) hm_conv f hf hf_supp

theorem cc_seq_dense_diag
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasureSpace G] [BorelSpace G]
    [Measure.IsHaarMeasure (volume : Measure G)]

    (dirac_approx : ∀ (g₀ : G), ∃ (ψ : ℕ → G → ℝ),
      (∀ (n : ℕ), Continuous (ψ n)) ∧
      (∀ (n : ℕ), HasCompactSupport (ψ n)) ∧
      (∀ (f : G → ℂ), Continuous f → HasCompactSupport f →
        Filter.Tendsto (fun (n : ℕ) => ∫ (g : G), (ψ n g : ℂ) * f g)
          Filter.atTop (nhds (f g₀))))

    (μ : Measure G)
    (S : ℕ → Finset G) (c : ℕ → G → ℂ)
    (hconv : ∀ (f : G → ℂ), Continuous f →
      Filter.Tendsto (fun n => ∑ x ∈ S n, c n x * f x)
        Filter.atTop (nhds (∫ (g : G), f g ∂μ))) :
    ∃ (ψ : ℕ → G → ℂ),
      (∀ (n : ℕ), Continuous (ψ n)) ∧
      (∀ (n : ℕ), HasCompactSupport (ψ n)) ∧
      (∀ (f : G → ℂ), Continuous f → HasCompactSupport f →
        Filter.Tendsto (fun (n : ℕ) => ∫ (g : G), ψ n g * f g)
          Filter.atTop (nhds (∫ (g : G), f g ∂μ))) := by


  have step1 : ∀ n, ∃ (φ : ℕ → G → ℂ),
      (∀ m, Continuous (φ m)) ∧
      (∀ m, HasCompactSupport (φ m)) ∧
      (∀ f : G → ℂ, Continuous f → HasCompactSupport f →
        Filter.Tendsto (fun m => ∫ g, φ m g * f g)
          Filter.atTop (nhds (∑ x ∈ S n, c n x * f x))) := by
    intro n
    exact finsupp_in_seq_closure_cc dirac_approx (S n) (c n)

  choose φ hφ using step1

  obtain ⟨m, hm_cont, hm_supp, hm_conv⟩ := seq_closure_diagonal_extraction
    φ
    (fun n k => (hφ n).1 k)
    (fun n k => (hφ n).2.1 k)
    (fun n f => ∑ x ∈ S n, c n x * f x)
    (fun n f hf hf_supp => (hφ n).2.2 f hf hf_supp)
    (fun f => ∫ g, f g ∂μ)
    (fun f hf => hconv f hf)

  exact ⟨fun n => φ n (m n), hm_cont, hm_supp, hm_conv⟩

theorem cc_seq_dense_in_measures
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasureSpace G] [BorelSpace G]
    [Measure.IsHaarMeasure (volume : Measure G)]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (hμ : IsCompact μ.support) :

    ∃ (ψ : ℕ → G → ℂ),
      (∀ (n : ℕ), Continuous (ψ n)) ∧
      (∀ (n : ℕ), HasCompactSupport (ψ n)) ∧
      (∀ (f : G → ℂ), Continuous f → HasCompactSupport f →
        Filter.Tendsto (fun (n : ℕ) => ∫ (g : G), ψ n g * f g)
          Filter.atTop (nhds (∫ (g : G), f g ∂μ))) := by

  have step_a := fun g₀ => cc_seq_converges_to_dirac (G := G) g₀

  obtain ⟨S, c, hconv⟩ := cc_seq_dense_approx_finsupp μ hμ

  exact cc_seq_dense_diag step_a μ S c hconv

theorem cc_seq_dense_in_measures_weakstar
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasureSpace G] [BorelSpace G]
    [Measure.IsHaarMeasure (volume : Measure G)]
    (μ : WeakDual ℂ C(G, ℂ)) :
    ∃ (ψ : ℕ → C(G, ℂ)),
      ∀ (f : C(G, ℂ)),
        Filter.Tendsto (fun n => ∫ x, (ψ n x) * (f x) ∂(volume : Measure G))
          Filter.atTop (nhds (μ f)) := by
  sorry

theorem cc_seq_dense_in_measures_of_measure
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasureSpace G] [BorelSpace G]
    [Measure.IsHaarMeasure (volume : Measure G)]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (hμ : IsCompact μ.support) :
    ∃ (ψ : ℕ → C(G, ℂ)),
      ∀ (f : C(G, ℂ)),
        Filter.Tendsto (fun n => ∫ x, (ψ n x) * (f x) ∂(volume : Measure G))
          Filter.atTop (nhds (∫ x, f x ∂μ)) := by

  obtain ⟨ψ_raw, hψ_cont, hψ_supp, hψ_conv⟩ := cc_seq_dense_in_measures μ hμ

  refine ⟨fun n => ⟨ψ_raw n, hψ_cont n⟩, fun f => ?_⟩

  have hf_supp : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport f) (Set.subset_univ _)
  exact hψ_conv f f.continuous hf_supp

set_option maxHeartbeats 3200000 in
theorem smooth_cc_seq_converges_to_dirac
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasureSpace G] [BorelSpace G]
    [Measure.IsHaarMeasure (volume : Measure G)]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    {HG : Type*} [TopologicalSpace HG]
    (IG : ModelWithCorners ℝ EG HG)
    [ChartedSpace HG G] [LieGroup IG ⊤ G] [T2Space G]
    (g₀ : G) :
    ∃ (ψ : ℕ → G → ℝ),
      (∀ (n : ℕ), ContMDiff IG 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞)) (ψ n)) ∧
      (∀ (n : ℕ), HasCompactSupport (ψ n)) ∧
      (∀ (f : G → ℂ), Continuous f → HasCompactSupport f →
        Filter.Tendsto (fun (n : ℕ) => ∫ (g : G), (ψ n g : ℂ) * f g)
          Filter.atTop (nhds (f g₀))) := by

  obtain ⟨φ, hφ_smooth, hφ_supp, hφ_conv⟩ := @exists_smooth_dirac_sequence G _ _ _ _ _ _ _ _ EG _ _ _ HG _ IG _ _ _

  refine ⟨fun n g => φ n (g₀⁻¹ * g), ?_, ?_, ?_⟩

  · intro n
    have hlmul : ContMDiff IG IG (↑(⊤ : ℕ∞)) (fun g : G => g₀⁻¹ * g) := by
      exact contMDiff_const.mul contMDiff_id
    exact (hφ_smooth n).comp hlmul

  · intro n
    exact (hφ_supp n).comp_homeomorph (Homeomorph.mulLeft g₀⁻¹)

  · intro f hf_cont hf_supp


    have key : ∀ n, ∫ g, (φ n (g₀⁻¹ * g) : ℂ) * f g = ∫ h, (φ n h : ℂ) * f (g₀ * h) := by
      intro n
      rw [show (fun g => (φ n (g₀⁻¹ * g) : ℂ) * f g) =
          fun g => ((fun h => (φ n h : ℂ) * f (g₀ * h)) (g₀⁻¹ * g)) from by
        ext g; simp [mul_inv_cancel_left]]
      exact @MeasureTheory.integral_mul_left_eq_self G ℂ _ _ _ (volume) _ _ _
        (fun h => (φ n h : ℂ) * f (g₀ * h)) g₀⁻¹
    simp_rw [key]

    have hfg : Continuous (f ∘ (g₀ * ·)) := hf_cont.comp (continuous_const.mul continuous_id)
    have hfg_supp : HasCompactSupport (f ∘ (g₀ * ·)) :=
      hf_supp.comp_homeomorph (Homeomorph.mulLeft g₀)
    have := hφ_conv (f ∘ (g₀ * ·)) hfg hfg_supp
    simp only [Function.comp, mul_one] at this
    convert this using 1

set_option maxHeartbeats 6400000 in
theorem smooth_cc_seq_dense_in_measures
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasureSpace G] [BorelSpace G]
    [Measure.IsHaarMeasure (volume : Measure G)]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    {HG : Type*} [TopologicalSpace HG]
    (IG : ModelWithCorners ℝ EG HG)
    [ChartedSpace HG G] [LieGroup IG ⊤ G] [T2Space G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] (hμ : IsCompact μ.support) :

    ∃ (ψ : ℕ → G → ℂ),
      (∀ (n : ℕ), ContMDiff IG 𝓘(ℝ, ℂ) (↑(⊤ : ℕ∞)) (ψ n)) ∧
      (∀ (n : ℕ), HasCompactSupport (ψ n)) ∧
      (∀ (f : G → ℂ), Continuous f → HasCompactSupport f →
        Filter.Tendsto (fun (n : ℕ) => ∫ (g : G), ψ n g * f g)
          Filter.atTop (nhds (∫ (g : G), f g ∂μ))) := by


  have step_a : ∀ (g₀ : G), ∃ (ψ_r : ℕ → G → ℝ),
      (∀ (n : ℕ), ContMDiff IG 𝓘(ℝ, ℝ) (↑(⊤ : ℕ∞)) (ψ_r n)) ∧
      (∀ (n : ℕ), Continuous (ψ_r n)) ∧
      (∀ (n : ℕ), HasCompactSupport (ψ_r n)) ∧
      (∀ (f : G → ℂ), Continuous f → HasCompactSupport f →
        Filter.Tendsto (fun (n : ℕ) => ∫ (g : G), (ψ_r n g : ℂ) * f g)
          Filter.atTop (nhds (f g₀))) := by
    intro g₀
    obtain ⟨ψ_r, hsmooth, hsupp, hconv⟩ := smooth_cc_seq_converges_to_dirac IG g₀
    exact ⟨ψ_r, hsmooth, fun n => (hsmooth n).continuous, hsupp, hconv⟩

  obtain ⟨S, c, hconv_b⟩ := cc_seq_dense_approx_finsupp μ hμ

  choose ψ_pt hψ_smooth hψ_cont hψ_supp hψ_conv using step_a


  let φ : ℕ → ℕ → G → ℂ := fun n m g => ∑ x ∈ S n, c n x * (ψ_pt x m g : ℂ)

  have hφ_smooth : ∀ n m, ContMDiff IG 𝓘(ℝ, ℂ) (↑(⊤ : ℕ∞)) (φ n m) := by
    intro n m
    apply contMDiff_finset_sum
    intro x _

    let L : ℂ →L[ℝ] ℂ := (c n x) • ContinuousLinearMap.id ℝ ℂ
    have hL : ∀ z, L z = c n x * z := fun z => by
      simp [L, ContinuousLinearMap.smul_apply, mul_comm]
    have : (fun g => c n x * (ψ_pt x m g : ℂ)) = (fun g => L (Complex.ofRealCLM (ψ_pt x m g))) := by
      ext g; simp [hL, Complex.ofReal]
    rw [this]
    exact (L.contMDiff.of_le le_top).comp
      ((Complex.ofRealCLM.contMDiff.of_le le_top).comp (hψ_smooth x m))

  have hφ_cont : ∀ n m, Continuous (φ n m) := by
    intro n m; exact (hφ_smooth n m).continuous

  have hφ_supp : ∀ n m, HasCompactSupport (φ n m) := by
    intro n m
    exact hasCompactSupport_finset_sum' fun x _ =>
      ((hψ_supp x m).comp_left (g := Complex.ofReal) Complex.ofReal_zero).mul_left

  have hφ_conv : ∀ n (f : G → ℂ), Continuous f → HasCompactSupport f →
      Filter.Tendsto (fun m => ∫ g, φ n m g * f g)
        Filter.atTop (nhds (∑ x ∈ S n, c n x * f x)) := by
    intro n f hf hf_supp

    have key : ∀ x ∈ S n, Filter.Tendsto
        (fun m => c n x * ∫ g, (ψ_pt x m g : ℂ) * f g)
        Filter.atTop (nhds (c n x * f x)) := by
      intro x _
      exact (hψ_conv x f hf hf_supp).const_mul (c n x)

    suffices h : ∀ m, ∫ g, φ n m g * f g =
        ∑ x ∈ S n, c n x * ∫ g, (ψ_pt x m g : ℂ) * f g by
      simp_rw [h]
      exact tendsto_finset_sum (S n) (fun x hx => key x hx)
    intro m
    show ∫ g, (∑ x ∈ S n, c n x * (ψ_pt x m g : ℂ)) * f g =
        ∑ x ∈ S n, c n x * ∫ g, (ψ_pt x m g : ℂ) * f g
    simp_rw [Finset.sum_mul]
    rw [integral_finset_sum]
    · congr 1; ext x
      simp_rw [mul_assoc]
      exact MeasureTheory.integral_const_mul _ _
    · intro x _
      exact ((continuous_const.mul
        (Complex.continuous_ofReal.comp (hψ_cont x m))).mul hf).integrable_of_hasCompactSupport
        hf_supp.mul_left

  obtain ⟨m, _, _, hm_conv⟩ := seq_closure_diagonal_extraction
    φ
    (fun n k => hφ_cont n k)
    (fun n k => hφ_supp n k)
    (fun n f => ∑ x ∈ S n, c n x * f x)
    (fun n f hf hf_supp => hφ_conv n f hf hf_supp)
    (fun f => ∫ g, f g ∂μ)
    (fun f hf => hconv_b f hf)

  exact ⟨fun n => φ n (m n), fun n => hφ_smooth n (m n), fun n => hφ_supp n (m n), hm_conv⟩

theorem kfinite_dense_in_rep
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K]
    {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (π : ContinuousRep K V) :
    Dense (ContinuousRep.kFiniteSubspace π ⊤ : Set V) := by
  haveI : CompactSpace (⊤ : Subgroup K) := by
    have : IsCompact ((⊤ : Subgroup K) : Set K) := by
      rw [Subgroup.coe_top]
      exact isCompact_univ
    exact isCompact_iff_compactSpace.mp this
  exact ContinuousRep.kFiniteSubspace_dense π ⊤

def IsKFiniteFunction
    (K : Type*) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] (f : K → ℂ) : Prop :=
  ∃ (n : ℕ)
    (mc : Fin n → (K → ℂ))
    (c : Fin n → ℂ),

    (∀ i, ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W)
          (_ : TopologicalSpace W) (_ : FiniteDimensional ℂ W)
          (ρ : ContinuousRep K W) (φ : W →L[ℂ] ℂ) (v : W),
          mc i = ContinuousRep.matrixCoefficient K ρ φ v) ∧
    (∀ g, f g = ∑ i, c i * mc i g)

lemma matrixCoefficient_continuous
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    (ρ : ContinuousRep K W) (φ : W →L[ℂ] ℂ) (v : W) :
    Continuous (ContinuousRep.matrixCoefficient K ρ φ v) := by
  unfold ContinuousRep.matrixCoefficient
  exact φ.continuous.comp (ρ.continuous_action.comp (Continuous.prodMk continuous_id continuous_const))

lemma isKFiniteFunction_continuous
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K]
    (p : K → ℂ) (hp : IsKFiniteFunction K p) : Continuous p := by
  obtain ⟨n, mc, c, hmc, hpg⟩ := hp

  have hmc_cont : ∀ i, Continuous (mc i) := by
    intro i
    obtain ⟨W, hACG, hMod, hTop, hFD, ρ, φ, v, hmci⟩ := hmc i
    rw [hmci]
    exact @matrixCoefficient_continuous K _ _ _ _ W hACG hMod hTop ρ φ v

  have : p = fun g => ∑ i : Fin n, c i * mc i g := funext hpg
  rw [this]
  exact continuous_finset_sum _ (fun i _ => continuous_const.mul (hmc_cont i))

noncomputable def leftRegularRep_CK
    (K : Type*) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] :
    ContinuousRep K C(K, ℂ) where
  toMonoidHom :=
    { toFun := fun g =>
        { toFun := fun f => f.comp ⟨fun x => g⁻¹ * x, continuous_const.mul continuous_id⟩
          map_add' := fun f₁ f₂ => by ext x; simp [ContinuousMap.comp]
          map_smul' := fun c f => by ext x; simp [ContinuousMap.comp]
          cont := (⟨fun x => g⁻¹ * x, continuous_const.mul continuous_id⟩ : C(K, K)).continuous_precomp }
      map_one' := by
        ext f x
        simp [ContinuousMap.comp]
      map_mul' := fun g h => by
        ext f x
        simp [ContinuousMap.comp, mul_inv_rev, mul_assoc] }
  continuous_action := by

    show Continuous (fun p : K × C(K, ℂ) =>
      p.2.comp ⟨fun x => p.1⁻¹ * x, continuous_const.mul continuous_id⟩)

    have h_left : Continuous (fun g : K => (⟨fun x => g⁻¹ * x, continuous_const.mul continuous_id⟩ : C(K, K))) :=
      ContinuousMap.continuous_of_continuous_uncurry _ (continuous_fst.inv.mul continuous_snd)

    have h_comp : Continuous (fun q : C(K, K) × C(K, ℂ) => q.2.comp q.1) :=
      ContinuousMap.continuous_comp'

    exact h_comp.comp (Continuous.prodMk (h_left.comp continuous_fst) continuous_snd)

@[simp]
lemma leftRegularRep_CK_apply_val
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K]
    (g : K) (f : C(K, ℂ)) (x : K) :
    ((leftRegularRep_CK K).toMonoidHom g f) x = f (g⁻¹ * x) := by
  rfl

lemma leftRegularRep_eval_identity
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K]
    (f : C(K, ℂ)) (g : K) :
    f g = ((leftRegularRep_CK K).toMonoidHom g⁻¹ f) (1 : K) := by
  simp [leftRegularRep_CK_apply_val, mul_one]

noncomputable def contragredientFinRep
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (K : Type*) [Group K] [TopologicalSpace K] [CompactSpace K]
    (ρ : Representation ℂ K V) [FiniteDimensional ℂ V] :
    Representation ℂ K (V →ₗ[ℂ] ℂ) where
  toFun k :=
    { toFun := fun φ => φ.comp (ρ k⁻¹)
      map_add' := fun φ₁ φ₂ => by simp only [LinearMap.add_comp]
      map_smul' := fun c φ => by simp only [LinearMap.smul_comp, RingHom.id_apply] }
  map_one' := by
    ext φ v
    simp
  map_mul' := fun g h => by
    ext φ v
    simp [mul_inv_rev]

@[simp]
theorem contragredientFinRep_apply
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (K : Type*) [Group K] [TopologicalSpace K] [CompactSpace K]
    (ρ : Representation ℂ K V) [FiniteDimensional ℂ V]
    (k : K) (φ : V →ₗ[ℂ] ℂ) (v : V) :
    (contragredientFinRep K ρ k φ) v = φ (ρ k⁻¹ v) :=
  rfl

lemma orbit_span_invariant_of_monoidHom
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    (π : G →* (V →L[ℂ] V))
    (K : Subgroup G)
    (v : V)
    (g : G) (hg : g ∈ K)
    (w : V)
    (hw : w ∈ Submodule.span ℂ (Set.range (fun k : K => (π k) v))) :
    (π g) w ∈ Submodule.span ℂ (Set.range (fun k : K => (π k) v)) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨k, hk⟩, rfl⟩ := hx
    have heq : (π g) ((π k) v) = (π (g * k)) v := by
      rw [π.map_mul g k]; rfl
    rw [heq]
    exact Submodule.subset_span ⟨⟨g * k, K.mul_mem hg hk⟩, rfl⟩
  | zero => simp [map_zero]
  | add x y _ _ ihx ihy =>
    rw [map_add]
    exact Submodule.add_mem _ ihx ihy
  | smul c x _ ih =>
    rw [map_smul]
    exact Submodule.smul_mem _ c ih

theorem isKFinite_leftReg_implies_isKFiniteFunction
    (K : Type*) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K]
    (p : C(K, ℂ))
    (hp : ContinuousRep.IsKFinite (leftRegularRep_CK K) ⊤ p) :
    IsKFiniteFunction K (⇑p) := by


  refine ⟨1, fun _ => ⇑p, fun _ => (1 : ℂ), ?_, ?_⟩
  ·


    intro i
    sorry
  ·
    intro g
    simp [Fin.sum_univ_one]

theorem kfinite_functions_uniformly_dense
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K]
    (f : C(K, ℂ)) (ε : ℝ) (hε : ε > 0) :
    ∃ (p : K → ℂ),
      IsKFiniteFunction K p ∧
      (∀ (g : K), ‖f g - p g‖ < ε) := by

  let π := leftRegularRep_CK K

  have hdense : Dense (ContinuousRep.kFiniteSubspace π ⊤ : Set C(K, ℂ)) :=
    kfinite_dense_in_rep π

  have hf_closure := hdense f
  rw [Metric.mem_closure_iff] at hf_closure
  obtain ⟨q, hq_kfin, hq_dist⟩ := hf_closure ε hε

  rw [SetLike.mem_coe, ContinuousRep.mem_kFiniteSubspace] at hq_kfin
  have hq_concrete := isKFinite_leftReg_implies_isKFiniteFunction K q hq_kfin

  refine ⟨⇑q, hq_concrete, fun g => ?_⟩
  calc ‖f g - q g‖ ≤ ‖f - q‖ := ContinuousMap.norm_coe_le_norm (f - q) g
    _ = dist f q := by rw [dist_eq_norm]
    _ < ε := hq_dist

theorem kfinite_dense_in_continuous
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K]
    (f : C(K, ℂ)) (ε : ℝ) (hε : ε > 0) :
    ∃ (p : K → ℂ),
      IsKFiniteFunction K p ∧
      Continuous p ∧
      (∀ (g : K), ‖f g - p g‖ < ε) := by

  obtain ⟨p, hp_kfin, hp_approx⟩ := kfinite_functions_uniformly_dense f ε hε

  exact ⟨p, hp_kfin, isKFiniteFunction_continuous p hp_kfin, hp_approx⟩

theorem kfinite_dense_in_continuous_dense
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] :
    Dense {f : C(K, ℂ) | IsKFiniteFunction K (⇑f)} := by
  intro f
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨p, hp_kfin, hp_cont, hp_approx⟩ := kfinite_dense_in_continuous f ε hε
  refine ⟨⟨p, hp_cont⟩, ?_, ?_⟩
  · exact hp_kfin
  · rw [dist_eq_norm, ContinuousMap.norm_lt_iff _ hε]
    intro g
    simp only [ContinuousMap.coe_mk, ContinuousMap.coe_sub]
    exact hp_approx g

theorem kfinite_subspace_dense_in_CK
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] :
    Dense (ContinuousRep.kFiniteSubspace (leftRegularRep_CK K) ⊤ : Set C(K, ℂ)) :=
  kfinite_dense_in_rep (leftRegularRep_CK K)

theorem auto_smooth_finiteDim_rep_orbit
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K]
    {EK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK]
    {HK : Type*} [TopologicalSpace HK]
    (IK : ModelWithCorners ℝ EK HK)
    [ChartedSpace HK K] [LieGroup IK ⊤ K]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    [FiniteDimensional ℂ W]
    (ρ_hom : K →* (W →L[ℂ] W))
    (h_cont : Continuous (fun p : K × W => (ρ_hom p.1) p.2))
    (φ : W →L[ℂ] ℂ) (v : W) :
    ContMDiff IK 𝓘(ℝ, ℂ) ⊤ (fun g => φ ((ρ_hom g) v)) := by
  sorry

theorem matrixCoefficient_contMDiff
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K]
    {EK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK]
    {HK : Type*} [TopologicalSpace HK]
    (IK : ModelWithCorners ℝ EK HK)
    [ChartedSpace HK K] [LieGroup IK ⊤ K]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    [FiniteDimensional ℂ W]
    (ρ : ContinuousRep K W) (φ : W →L[ℂ] ℂ) (v : W) :
    ContMDiff IK 𝓘(ℝ, ℂ) ⊤ (ContinuousRep.matrixCoefficient K ρ φ v) := by


  unfold ContinuousRep.matrixCoefficient
  exact auto_smooth_finiteDim_rep_orbit IK ρ.toMonoidHom ρ.continuous_action φ v

universe uK uEK uHK in
theorem isKFiniteFunction_contMDiff
    {K : Type uK} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K]
    {EK : Type uEK} [NormedAddCommGroup EK] [NormedSpace ℝ EK]
    {HK : Type uHK} [TopologicalSpace HK]
    (IK : ModelWithCorners ℝ EK HK)
    [ChartedSpace HK K] [LieGroup IK ⊤ K]
    (p : K → ℂ) (hp : IsKFiniteFunction K p) :
    ContMDiff IK 𝓘(ℝ, ℂ) ⊤ p := by

  obtain ⟨n, mc, c, hmc, hpg⟩ := hp

  have hmc_smooth : ∀ i, ContMDiff IK 𝓘(ℝ, ℂ) ⊤ (mc i) := by
    intro i
    obtain ⟨W, hACG, hMod, hTop, hFD, ρ, φ, v, hmci⟩ := hmc i
    rw [hmci]
    exact @matrixCoefficient_contMDiff K _ _ _ _ EK _ _ HK _ IK _ _ W hACG hMod hTop hFD ρ φ v

  have hterm_smooth : ∀ i, ContMDiff IK 𝓘(ℝ, ℂ) ⊤ (fun g => c i * mc i g) := by
    intro i

    let L : ℂ →L[ℝ] ℂ := (c i) • ContinuousLinearMap.id ℝ ℂ
    have hL : ∀ z, L z = c i * z := fun z => by
      simp [L, ContinuousLinearMap.smul_apply, mul_comm]
    show ContMDiff IK 𝓘(ℝ, ℂ) ⊤ (fun g => L (mc i g))
    exact L.contMDiff.comp (hmc_smooth i)

  have hp_eq : p = fun g => ∑ i : Fin n, c i * mc i g := funext hpg
  rw [hp_eq]
  exact contMDiff_finset_sum (fun i _ => hterm_smooth i)

theorem leftRegularRep_ck_isContinuousRep
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K]
    {EK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK]
    {HK : Type*} [TopologicalSpace HK]
    (IK : ModelWithCorners ℝ EK HK)
    [ChartedSpace HK K] [LieGroup IK ⊤ K]
    (m : ℕ) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : TopologicalSpace V)
      (π : ContinuousRep K V)
      (emb : V → (K → ℂ))
      (emb_inj : Function.Injective emb),

    (∀ (k : K) (v : V), emb (π.toMonoidHom k v) = fun x => emb v (k⁻¹ * x)) ∧

    (∀ (f : K → ℂ), ContMDiff IK 𝓘(ℝ, ℂ) ⊤ f → ∃ v : V, emb v = f) ∧

    (∀ (f : K → ℂ) (hf : ContMDiff IK 𝓘(ℝ, ℂ) ⊤ f) (ε : ℝ) (hε : ε > 0),
      ∀ (v : V), emb v = f →
        ∃ (U : Set V), v ∈ U ∧ IsOpen U ∧
          ∀ w ∈ U, ∀ (g : K) (j : ℕ), j ≤ m →
            ‖iteratedFDeriv ℝ j
              (writtenInExtChartAt IK 𝓘(ℝ, ℂ) g f -
               writtenInExtChartAt IK 𝓘(ℝ, ℂ) g (emb w))
              (extChartAt IK g g)‖ < ε) ∧

    (∀ (v : V), v ∈ (ContinuousRep.kFiniteSubspace π ⊤ : Set V) →
      IsKFiniteFunction K (emb v)) := by
  sorry

theorem kfinite_uniform_to_ck_dense
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K]
    {EK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK]
    {HK : Type*} [TopologicalSpace HK]
    (IK : ModelWithCorners ℝ EK HK)
    [ChartedSpace HK K] [LieGroup IK ⊤ K]
    (f : K → ℂ) (hf : ContMDiff IK 𝓘(ℝ, ℂ) ⊤ f)
    (h_uniform_dense : ∀ (δ : ℝ), δ > 0 →
      ∃ (q : K → ℂ), IsKFiniteFunction K q ∧ (∀ (g : K), ‖f g - q g‖ < δ))
    (h_smooth : ∀ (q : K → ℂ), IsKFiniteFunction K q → ContMDiff IK 𝓘(ℝ, ℂ) ⊤ q)
    (m : ℕ) (ε : ℝ) (hε : ε > 0) :
    ∃ (p : K → ℂ),
      IsKFiniteFunction K p ∧
      (∀ (g : K) (j : ℕ), j ≤ m →
        ‖iteratedFDeriv ℝ j
          (writtenInExtChartAt IK 𝓘(ℝ, ℂ) g f -
           writtenInExtChartAt IK 𝓘(ℝ, ℂ) g p)
          (extChartAt IK g g)‖ < ε) := by

  have h_infra := leftRegularRep_ck_isContinuousRep (K := K) IK m
  obtain ⟨V, instAG, instMod, instTop, π, emb, emb_inj, h_action, h_surj, h_balls, h_kfin_id⟩ :=
    h_infra

  obtain ⟨vf, hvf⟩ := h_surj f hf

  obtain ⟨U, hvfU, hUopen, hUapprox⟩ := h_balls f hf ε hε vf hvf

  haveI : CompactSpace (⊤ : Subgroup K) := by
    have : IsCompact ((⊤ : Subgroup K) : Set K) := by
      rw [Subgroup.coe_top]; exact isCompact_univ
    exact isCompact_iff_compactSpace.mp this
  have h_dense : Dense (ContinuousRep.kFiniteSubspace π ⊤ : Set V) :=
    @ContinuousRep.kFiniteSubspace_dense K _ _ V instAG instMod instTop π ⊤ ‹_›


  have h_meet : ∃ w, w ∈ U ∧ w ∈ (ContinuousRep.kFiniteSubspace π ⊤ : Set V) := by
    have h_nhd : U ∈ nhds vf := hUopen.mem_nhds hvfU
    have h_cl := h_dense vf
    rw [mem_closure_iff_nhds] at h_cl
    obtain ⟨w, hwU, hw_kfin⟩ := h_cl U h_nhd
    exact ⟨w, hwU, hw_kfin⟩

  obtain ⟨w, hwU, hw_kfin⟩ := h_meet
  exact ⟨emb w, h_kfin_id w hw_kfin, hUapprox w hwU⟩

theorem kfinite_ck_dense
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K]
    {EK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK]
    {HK : Type*} [TopologicalSpace HK]
    (IK : ModelWithCorners ℝ EK HK)
    [ChartedSpace HK K] [LieGroup IK ⊤ K]
    (f : K → ℂ) (hf : ContMDiff IK 𝓘(ℝ, ℂ) ⊤ f)
    (m : ℕ) (ε : ℝ) (hε : ε > 0) :
    ∃ (p : K → ℂ),
      IsKFiniteFunction K p ∧
      (∀ (g : K) (j : ℕ), j ≤ m →
        ‖iteratedFDeriv ℝ j
          (writtenInExtChartAt IK 𝓘(ℝ, ℂ) g f -
           writtenInExtChartAt IK 𝓘(ℝ, ℂ) g p)
          (extChartAt IK g g)‖ < ε) := by


  have h_unif : ∀ (δ : ℝ), δ > 0 →
      ∃ (q : K → ℂ), IsKFiniteFunction K q ∧ (∀ (g : K), ‖f g - q g‖ < δ) := by
    intro δ hδ
    have hf_cont : Continuous f := hf.continuous
    exact kfinite_functions_uniformly_dense ⟨f, hf_cont⟩ δ hδ

  have h_smooth : ∀ (q : K → ℂ), IsKFiniteFunction K q → ContMDiff IK 𝓘(ℝ, ℂ) ⊤ q :=
    fun q hq => isKFiniteFunction_contMDiff IK q hq

  exact kfinite_uniform_to_ck_dense IK f hf h_unif h_smooth m ε hε

theorem kfinite_functions_smooth_dense
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K]
    {EK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK]
    {HK : Type*} [TopologicalSpace HK]
    (IK : ModelWithCorners ℝ EK HK)
    [ChartedSpace HK K] [LieGroup IK ⊤ K]
    (f : K → ℂ) (hf : ContMDiff IK 𝓘(ℝ, ℂ) ⊤ f)
    (m : ℕ) (ε : ℝ) (hε : ε > 0) :
    ∃ (p : K → ℂ),
      IsKFiniteFunction K p ∧
      ContMDiff IK 𝓘(ℝ, ℂ) ⊤ p ∧
      (∀ (g : K) (j : ℕ), j ≤ m →
        ‖iteratedFDeriv ℝ j
          (writtenInExtChartAt IK 𝓘(ℝ, ℂ) g f -
           writtenInExtChartAt IK 𝓘(ℝ, ℂ) g p)
          (extChartAt IK g g)‖ < ε) := by

  obtain ⟨p, hp_kfin, hp_approx⟩ := kfinite_ck_dense IK f hf m ε hε

  exact ⟨p, hp_kfin, isKFiniteFunction_contMDiff IK p hp_kfin, hp_approx⟩

theorem kfinite_dense_in_smooth
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K]
    {EK : Type*} [NormedAddCommGroup EK] [NormedSpace ℝ EK]
    {HK : Type*} [TopologicalSpace HK]
    (IK : ModelWithCorners ℝ EK HK)
    [ChartedSpace HK K] [LieGroup IK ⊤ K]
    (f : K → ℂ) (hf : ContMDiff IK 𝓘(ℝ, ℂ) ⊤ f)
    (m : ℕ) (ε : ℝ) (hε : ε > 0) :
    ∃ (p : K → ℂ),
      IsKFiniteFunction K p ∧
      ContMDiff IK 𝓘(ℝ, ℂ) ⊤ p ∧


      (∀ (g : K) (j : ℕ), j ≤ m →
        ‖iteratedFDeriv ℝ j
          (writtenInExtChartAt IK 𝓘(ℝ, ℂ) g f -
           writtenInExtChartAt IK 𝓘(ℝ, ℂ) g p)
          (extChartAt IK g g)‖ < ε) := by
  exact kfinite_functions_smooth_dense IK f hf m ε hε

theorem irreducible_rep_finiteDimensional
    {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K]
    {W : Type*} [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    [IsTopologicalAddGroup W] [ContinuousSMul ℂ W] [T2Space W]
    (π : ContinuousRep K W) (hirr : π.IsIrreducible) :
    FiniteDimensional ℂ W := by

  have hdense := kfinite_dense_in_rep π

  by_cases hW : ∀ v : W, v ∈ ContinuousRep.kFiniteSubspace π ⊤ → v = 0
  ·

    have hsub : (ContinuousRep.kFiniteSubspace π ⊤ : Set W) ⊆ {0} := by
      intro v hv; exact hW v hv
    have hdense0 : Dense ({0} : Set W) := Dense.mono hsub hdense
    have hcl : closure ({0} : Set W) = {0} := isClosed_singleton.closure_eq
    have huniv : (Set.univ : Set W) = {0} := by
      rw [← hdense0.closure_eq, hcl]
    have htriv : ∀ w : W, w = 0 := by
      intro w; have hw := Set.mem_univ w; rw [huniv] at hw
      exact Set.mem_singleton_iff.mp hw

    haveI : Subsingleton W := ⟨fun a b => by rw [htriv a, htriv b]⟩
    exact Module.Finite.of_surjective (0 : (Fin 0 → ℂ) →ₗ[ℂ] W)
      (fun w => ⟨0, by simp [htriv w]⟩)
  ·
    push Not at hW
    obtain ⟨v, hv_kfin, hv_ne⟩ := hW

    set S := Submodule.span ℂ (Set.range (fun k : (⊤ : Subgroup K) => (π.toMonoidHom k) v))
      with hS_def

    have hfin : FiniteDimensional ℂ S := by
      have := (ContinuousRep.mem_kFiniteSubspace π ⊤ v).mp hv_kfin
      exact this

    have hinv : ∀ (g : K) (w : W), w ∈ S → (π.toMonoidHom g) w ∈ S := by
      intro g w hw
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
      ·
        intro x hx
        obtain ⟨⟨k, _⟩, rfl⟩ := hx

        have : (π.toMonoidHom g) ((π.toMonoidHom k) v) = (π.toMonoidHom (g * k)) v := by
          simp [map_mul]
        rw [this]
        exact Submodule.subset_span ⟨⟨g * k, Subgroup.mem_top _⟩, rfl⟩
      ·
        simp
      ·
        intro x y _ _ hx' hy'
        rw [map_add]
        exact Submodule.add_mem _ hx' hy'
      ·
        intro c x _ hx'
        rw [map_smul]
        exact Submodule.smul_mem _ c hx'

    have hclosed : IsClosed (S : Set W) := by
      exact Submodule.closed_of_finiteDimensional S

    have hinv_sub : π.IsInvariantSubspace S :=
      ⟨hclosed, hinv⟩

    have h_or := hirr S hinv_sub

    have hv_in_S : v ∈ S := by
      have : v = (π.toMonoidHom 1) v := by simp
      rw [this]
      exact Submodule.subset_span ⟨⟨1, Subgroup.mem_top _⟩, by simp⟩
    have hS_ne_bot : S ≠ ⊥ := by
      intro h
      rw [h] at hv_in_S
      simp at hv_in_S
      exact hv_ne hv_in_S

    have hS_top : S = ⊤ := by
      cases h_or with
      | inl h => exact absurd h hS_ne_bot
      | inr h => exact h

    have : FiniteDimensional ℂ (⊤ : Submodule ℂ W) := hS_top ▸ hfin
    exact Module.Finite.of_surjective (Submodule.subtype (⊤ : Submodule ℂ W))
      (fun w => ⟨⟨w, Submodule.mem_top⟩, rfl⟩)

abbrev IsSmoothVector
    {G : Type*} [Group G] [TopologicalSpace G]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
    {HG : Type*} [TopologicalSpace HG]
    (IG : ModelWithCorners ℝ EG HG) [ChartedSpace HG G] [LieGroup IG ⊤ G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (v : F) : Prop :=
  π.IsSmoothVector IG v

abbrev smoothVectors
    {G : Type*} [Group G] [TopologicalSpace G]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
    {HG : Type*} [TopologicalSpace HG]
    (IG : ModelWithCorners ℝ EG HG) [ChartedSpace HG G] [LieGroup IG ⊤ G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) : Submodule ℂ F :=
  π.smoothSubspace IG

theorem derivedRep_preserves_smooth
    {G : Type*} [Group G] [TopologicalSpace G]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
    {HG : Type*} [TopologicalSpace HG]
    (IG : ModelWithCorners ℝ EG HG) [ChartedSpace HG G] [LieGroup IG ⊤ G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (π : ContinuousRep G F)
    (lieExp : EG → G) (hExp : ContMDiff 𝓘(ℝ, EG) IG ⊤ lieExp) (hExp1 : lieExp 0 = 1)
    (b : EG) (v : F) (hv : π.IsSmoothVector IG v) :
    π.IsSmoothVector IG (π.derivedRep lieExp b v) :=
  ContinuousRep.derivedRep_maps_smooth IG π lieExp hExp hExp1 b v hv

theorem derivedRep_lie_algebra_hom
    {G : Type*} [Group G] [TopologicalSpace G]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [LieRing EG] [LieAlgebra ℝ EG]
    {HG : Type*} [TopologicalSpace HG]
    (IG : ModelWithCorners ℝ EG HG) [ChartedSpace HG G] [LieGroup IG ⊤ G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (π : ContinuousRep G F)
    (lieExp : EG → G) (hExp : ContMDiff 𝓘(ℝ, EG) IG ⊤ lieExp) (hExp1 : lieExp 0 = 1)
    (hExpAdd : ∀ (X : EG) (t s : ℝ), lieExp ((t + s) • X) = lieExp (t • X) * lieExp (s • X))
    (X Y : EG) (v : F)
    (hv : π.IsSmoothVector IG v) :
    π.derivedRep lieExp ⁅X, Y⁆ v =
      π.derivedRep lieExp X (π.derivedRep lieExp Y v) -
      π.derivedRep lieExp Y (π.derivedRep lieExp X v) := by


  sorry

theorem smooth_vectors_dense
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasureSpace G] [BorelSpace G]
    [Measure.IsHaarMeasure (volume : Measure G)]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [FiniteDimensional ℝ EG]
    {HG : Type*} [TopologicalSpace HG]
    (IG : ModelWithCorners ℝ EG HG) [ChartedSpace HG G] [LieGroup IG ⊤ G] [T2Space G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (π : ContinuousRep G F) :
    Dense (π.smoothSubspace IG : Set F) := by

  have hGardDense := ContinuousRep.gardingSubspace_dense IG π


  have hGardLeSmooth : (π.gardingSubspace IG : Set F) ⊆ (π.smoothSubspace IG : Set F) := by
    intro w hw
    have hsub : π.gardingSubspace IG ≤ π.smoothSubspace IG := by
      apply Submodule.span_le.mpr
      intro x ⟨f, v, hf, hx⟩
      rw [hx]
      exact ContinuousRep.gardingVector_isSmooth IG π f hf v
    exact hsub hw

  exact Dense.mono hGardLeSmooth hGardDense

theorem kfinite_subset_smooth
    {G : Type*} [Group G] [TopologicalSpace G]
    {EG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
    {HG : Type*} [TopologicalSpace HG]
    (IG : ModelWithCorners ℝ EG HG) [ChartedSpace HG G] [LieGroup IG ⊤ G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (π : ContinuousRep G F)
    (v : F) (hv : ContinuousRep.IsKFinite π ⊤ v) :
    π.IsSmoothVector IG v := by
  exact ContinuousRep.kfinite_le_smooth IG π hv

end PlancherelCompact

end
