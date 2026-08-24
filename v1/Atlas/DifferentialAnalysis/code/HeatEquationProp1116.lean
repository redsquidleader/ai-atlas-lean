/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Analysis.Distribution.Support
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi
import Atlas.DifferentialAnalysis.code.DifferentialOperators
import Atlas.DifferentialAnalysis.code.SchwartzPartition
import Atlas.DifferentialAnalysis.code.SchwartzCutoffConvergence
import Atlas.DifferentialAnalysis.code.DistributionSupport
import Atlas.DifferentialAnalysis.code.SmoothingOperators

noncomputable section

open scoped SchwartzMap
open TemperedDistribution LineDeriv Distribution

namespace HeatEquation

variable (n : ℕ)

/-- Space-time `ℝ^(n+1)` for the heat equation, with the time coordinate at index `0` and
spatial coordinates at indices `1, …, n`. -/
abbrev SpaceTime := EuclideanSpace ℝ (Fin (n + 1))

/-- The unit vector in the time direction (index `0`) in space-time. -/
def timeDirection : SpaceTime n :=
  EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)

/-- The `i`-th spatial unit vector in space-time (at index `i.succ`, since `0` is time). -/
def spatialDirection (i : Fin n) : SpaceTime n :=
  EuclideanSpace.single i.succ (1 : ℝ)

/-- The (positive) spatial Laplacian `Δ_x = Σ ∂²/∂xᵢ²` acting on tempered distributions on
space-time. -/
def positiveSpatialLaplacian (u : 𝓢'(SpaceTime n, ℂ)) : 𝓢'(SpaceTime n, ℂ) :=
  ∑ i : Fin n, ∂_{spatialDirection n i} (∂_{spatialDirection n i} u)

/-- The heat operator `∂_t - Δ_x` acting on tempered distributions on space-time. -/
def heatOperator (u : 𝓢'(SpaceTime n, ℂ)) : 𝓢'(SpaceTime n, ℂ) :=
  ∂_{timeDirection n} u - positiveSpatialLaplacian n u

/-- A tempered distribution has compact distributional support if its `dsupport` is compact. -/
def HasCompactDSupport (u : 𝓢'(SpaceTime n, ℂ)) : Prop :=
  IsCompact (dsupport u)

/-- The time coordinate of a space-time point `x`, i.e. `x 0`. -/
def timeCoord (x : SpaceTime n) : ℝ := x 0

/-- A tempered distribution `u` is supported in `{t ≥ c}` if its distributional support is
contained in the half-space `{x | timeCoord x ≥ c}`. -/
def SupportedInTimeGeq (u : 𝓢'(SpaceTime n, ℂ)) (c : ℝ) : Prop :=
  dsupport u ⊆ {x : SpaceTime n | timeCoord n x ≥ c}

/-- `IsVanishingOn` is preserved by subtraction: if `u` and `v` both vanish on `s`, so does
`u - v`. -/
lemma isVanishingOn_sub {u v : 𝓢'(SpaceTime n, ℂ)} {s : Set (SpaceTime n)}
    (hu : IsVanishingOn u s) (hv : IsVanishingOn v s) :
    IsVanishingOn (u - v) s := by
  intro φ hφ
  rw [show (u - v) φ = u φ - v φ from rfl, hu φ hφ, hv φ hφ, sub_self]

/-- The distributional support of `u - v` is contained in the union of the supports of `u`
and `v`. -/
lemma dsupport_sub_subset (u v : 𝓢'(SpaceTime n, ℂ)) :
    dsupport (u - v) ⊆ dsupport u ∪ dsupport v := by
  intro x hx
  by_contra h
  simp only [Set.mem_union, not_or] at h
  obtain ⟨hnu, hnv⟩ := h
  simp only [Distribution.notMem_dsupport_iff] at hnu hnv
  obtain ⟨s₁, hvan₁, hopen₁, hx₁⟩ := hnu
  obtain ⟨s₂, hvan₂, hopen₂, hx₂⟩ := hnv
  have hvan : IsVanishingOn (u - v) (s₁ ∩ s₂) :=
    isVanishingOn_sub n (hvan₁.mono Set.inter_subset_left)
      (hvan₂.mono Set.inter_subset_right)
  have : x ∉ dsupport (u - v) := by
    simp only [Distribution.notMem_dsupport_iff]
    exact ⟨s₁ ∩ s₂, hvan, hopen₁.inter hopen₂, ⟨hx₁, hx₂⟩⟩
  exact this hx

/-- If `u` is supported in `{t ≥ a}` and `v` is supported in `{t ≥ b}`, then `u - v` is supported
in `{t ≥ min a b}`. -/
lemma supportedInTimeGeq_sub (u v : 𝓢'(SpaceTime n, ℂ))
    (a b : ℝ) (ha : SupportedInTimeGeq n u a) (hb : SupportedInTimeGeq n v b) :
    SupportedInTimeGeq n (u - v) (min a b) := by
  intro x hx
  have hsub := dsupport_sub_subset n u v hx
  simp only [Set.mem_union] at hsub
  simp only [Set.mem_setOf_eq]
  rcases hsub with hu | hv
  · exact le_trans (min_le_left a b) (ha hu)
  · exact le_trans (min_le_right a b) (hb hv)

/-- `SupportedInTimeGeq` is invariant under negation of the distribution. -/
lemma supportedInTimeGeq_neg (u : 𝓢'(SpaceTime n, ℂ)) (c : ℝ) :
    SupportedInTimeGeq n (-u) c ↔ SupportedInTimeGeq n u c := by
  unfold SupportedInTimeGeq
  constructor
  · intro h x hx
    apply h
    rw [Distribution.mem_dsupport_iff] at hx ⊢
    intro C hvan hclosed
    apply hx C _ hclosed
    intro φ hφ
    have := hvan φ hφ
    show u φ = 0
    rwa [show (-u) φ = -(u φ) from rfl, neg_eq_zero] at this
  · intro h x hx
    apply h
    rw [Distribution.mem_dsupport_iff] at hx ⊢
    intro C hvan hclosed
    apply hx C _ hclosed
    intro φ hφ
    have := hvan φ hφ
    show -(u φ) = 0
    rw [this, neg_zero]

/-- A distribution with compact distributional support is automatically supported in some
half-space `{t ≥ b}`: the time coordinate attains its minimum on a compact set. -/
lemma compact_dsupport_time_bounded_below
    (f : 𝓢'(SpaceTime n, ℂ)) (hf : HasCompactDSupport n f) :
    ∃ b : ℝ, SupportedInTimeGeq n f b := by
  by_cases hempty : dsupport f = ∅
  · exact ⟨0, fun x hx => (hempty ▸ hx : x ∈ (∅ : Set _)).elim⟩
  · have hne : Set.Nonempty (dsupport f) := Set.nonempty_iff_ne_empty.mpr hempty
    have hcont : Continuous (timeCoord n) :=
      PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0
    obtain ⟨x₀, _, hx₀_min⟩ := hf.exists_isMinOn hne hcont.continuousOn
    exact ⟨timeCoord n x₀, fun x hx => hx₀_min hx⟩

/-- The classical heat-kernel density `(4πt)^(-n/2) · exp(-|x|²/(4t))` for `t > 0`, extended by
`0` for `t ≤ 0`. -/
noncomputable def heatKernelFun (v : SpaceTime n) : ℝ :=
  let t := v (0 : Fin (n + 1))
  if t > 0 then
    (4 * Real.pi * t) ^ (-(n : ℝ) / 2) *
      Real.exp (- ‖fun i : Fin n => v i.succ‖ ^ 2 / (4 * t))
  else 0

/-- The heat-kernel density is everywhere nonnegative. -/
lemma heatKernelFun_nonneg (v : SpaceTime n) : 0 ≤ heatKernelFun n v := by
  simp only [heatKernelFun]
  split_ifs with ht
  · apply mul_nonneg
    · exact Real.rpow_nonneg (mul_nonneg (mul_nonneg (by positivity) Real.pi_pos.le) ht.le) _
    · exact (Real.exp_pos _).le
  · exact le_rfl

/-- The heat-kernel density vanishes whenever the time coordinate is nonpositive. -/
lemma heatKernelFun_eq_zero_of_time_nonpos (v : SpaceTime n)
    (hv : v (0 : Fin (n + 1)) ≤ 0) : heatKernelFun n v = 0 := by
  simp only [heatKernelFun]
  split_ifs with ht
  · linarith
  · rfl

/-- The heat-kernel measure on space-time: the Lebesgue measure weighted by the heat-kernel
density. -/
def heatKernelMeasure : MeasureTheory.Measure (SpaceTime n) :=
  MeasureTheory.Measure.withDensity MeasureTheory.volume
    (fun v => ENNReal.ofReal (heatKernelFun n v))

open MeasureTheory in
/-- The heat-kernel measure assigns measure zero to the half-space `{t ≤ 0}`. -/
lemma heatKernelMeasure_nonpos_eq_zero :
    (heatKernelMeasure n) {v : SpaceTime n | v 0 ≤ 0} = 0 := by
  have hms : MeasurableSet {v : SpaceTime n | v 0 ≤ 0} :=
    measurableSet_le (by fun_prop) (by fun_prop)
  rw [heatKernelMeasure, withDensity_apply _ hms]
  exact setLIntegral_eq_zero hms (fun v (hv : v 0 ≤ 0) => by
    simp only [Pi.zero_apply]
    rw [heatKernelFun_eq_zero_of_time_nonpos n v hv, ENNReal.ofReal_zero])

/-- For `t ≥ 1`, the heat-kernel density is bounded above by `1`. -/
lemma heatKernelFun_le_one_of_time_ge_one (v : SpaceTime n)
    (ht : v (0 : Fin (n+1)) ≥ 1) : heatKernelFun n v ≤ 1 := by
  simp only [heatKernelFun]
  split_ifs with h
  · exact le_trans (mul_le_one₀
      (Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [Real.pi_gt_three])
        (by have := Nat.cast_nonneg (α := ℝ) n; linarith))
      (Real.exp_pos _).le
      (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (sq_nonneg _)) (by positivity)))) le_rfl
  · linarith

open MeasureTheory in
set_option maxHeartbeats 800000 in
/-- On the half-space `{t ≥ 1}`, the heat-kernel measure is dominated by Lebesgue measure
(since the density there is at most `1`). -/
lemma heatKernelMeasure_le_volume_on_time_ge_one :
    (heatKernelMeasure n).restrict {v : SpaceTime n | v (0 : Fin (n+1)) ≥ 1} ≤
    MeasureTheory.volume.restrict {v : SpaceTime n | v (0 : Fin (n+1)) ≥ 1} := by
  rw [MeasureTheory.Measure.le_iff]
  intro A hA
  rw [MeasureTheory.Measure.restrict_apply hA, MeasureTheory.Measure.restrict_apply hA]
  have hms : MeasurableSet (A ∩ {v : SpaceTime n | v (0 : Fin (n+1)) ≥ 1}) :=
    hA.inter (measurableSet_le (by fun_prop) (by fun_prop))
  rw [heatKernelMeasure, MeasureTheory.withDensity_apply _ hms]
  calc ∫⁻ v in A ∩ {v | v (0 : Fin (n+1)) ≥ 1},
        ENNReal.ofReal (heatKernelFun n v) ∂MeasureTheory.volume
      ≤ ∫⁻ _ in A ∩ {v | v (0 : Fin (n+1)) ≥ 1}, 1 ∂MeasureTheory.volume := by
        apply MeasureTheory.setLIntegral_mono (by fun_prop)
        intro v hv
        have hvS : v (0 : Fin (n+1)) ≥ 1 := hv.2
        exact ENNReal.ofReal_le_one.mpr
          (heatKernelFun_le_one_of_time_ge_one n v hvS)
    _ = MeasureTheory.volume (A ∩ {v | v (0 : Fin (n+1)) ≥ 1}) := by simp

end HeatEquation


/-- The Gaussian `exp(-b·|v|²)` on Euclidean space `ℝ^m` is Lebesgue integrable for any `b > 0`. -/
lemma HeatEquation.integrable_rexp_neg_mul_sq_norm_euclidean (m : ℕ) {b : ℝ} (hb : 0 < b) :
    MeasureTheory.Integrable
      (fun v : EuclideanSpace ℝ (Fin m) => Real.exp (-b * ‖v‖ ^ 2))
      MeasureTheory.volume := by
  have hcint := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (show (0 : ℝ) < (↑b : ℂ).re by simp [hb]) (0 : ℂ) (0 : EuclideanSpace ℝ (Fin m))
  simp only [zero_mul, add_zero] at hcint
  refine hcint.re.congr (MeasureTheory.ae_of_all _ fun v => ?_)
  simp only
  have h1 : (-↑b * ↑‖v‖ ^ 2 : ℂ) = ↑(-b * ‖v‖ ^ 2) := by push_cast; ring
  rw [h1]; exact Complex.ofReal_re _


open HeatEquation MeasureTheory in
/-- The Lebesgue integral of the heat-kernel density over the time slab `{0 < t < 1}` is finite. -/
theorem HeatEquation.heatKernelFun_lintegral_time_lt_one (n : ℕ) :
    ∫⁻ v in {v : SpaceTime n | 0 < v (0 : Fin (n+1)) ∧ v (0 : Fin (n+1)) < 1},
      ENNReal.ofReal (heatKernelFun n v) ∂volume < ⊤ := by sorry

open HeatEquation MeasureTheory in
/-- The heat-kernel measure of the half-space `{t < 1}` is finite. -/
theorem HeatEquation.heatKernelMeasure_time_lt_one_finite (n : ℕ) :
    (heatKernelMeasure n) {v : SpaceTime n | v (0 : Fin (n+1)) < 1} < ⊤ := by

  have hsub : {v : SpaceTime n | v (0 : Fin (n+1)) < 1} ⊆
    {v : SpaceTime n | v (0 : Fin (n+1)) ≤ 0} ∪
    {v : SpaceTime n | 0 < v (0 : Fin (n+1)) ∧ v (0 : Fin (n+1)) < 1} := by
    intro v hv; simp only [Set.mem_setOf_eq, Set.mem_union] at *
    by_cases h : v (0 : Fin (n+1)) ≤ 0
    · exact Or.inl h
    · exact Or.inr ⟨not_le.mp h, hv⟩
  have hms2 : MeasurableSet {v : SpaceTime n | 0 < v (0 : Fin (n+1)) ∧ v (0 : Fin (n+1)) < 1} := by
    have hm : Measurable (fun v : SpaceTime n => v (0 : Fin (n+1))) := by fun_prop
    exact (measurableSet_lt measurable_const hm).inter (measurableSet_lt hm measurable_const)
  calc (heatKernelMeasure n) {v | v (0 : Fin (n+1)) < 1}
    ≤ (heatKernelMeasure n) ({v | v (0 : Fin (n+1)) ≤ 0} ∪
        {v | 0 < v (0 : Fin (n+1)) ∧ v (0 : Fin (n+1)) < 1}) :=
      measure_mono hsub
    _ ≤ (heatKernelMeasure n) {v | v (0 : Fin (n+1)) ≤ 0} +
        (heatKernelMeasure n) {v | 0 < v (0 : Fin (n+1)) ∧ v (0 : Fin (n+1)) < 1} :=
      measure_union_le _ _
    _ = 0 + (heatKernelMeasure n) {v | 0 < v (0 : Fin (n+1)) ∧ v (0 : Fin (n+1)) < 1} := by
      rw [heatKernelMeasure_nonpos_eq_zero]
    _ = (heatKernelMeasure n) {v | 0 < v (0 : Fin (n+1)) ∧ v (0 : Fin (n+1)) < 1} := by
      rw [zero_add]
    _ < ⊤ := by
      rw [heatKernelMeasure, withDensity_apply _ hms2]
      exact heatKernelFun_lintegral_time_lt_one n

open HeatEquation MeasureTheory Measure in
/-- The function `(1 + ‖x‖)^(-(n+2))` is integrable with respect to the heat-kernel measure. This
provides the temperate growth witness needed to view the heat kernel as a tempered distribution. -/
theorem HeatEquation.heatKernelMeasure_integrable_one_add_norm (n : ℕ) :
    MeasureTheory.Integrable
      (fun x => (1 + ‖x‖) ^ (-(↑(n + 2) : ℝ))) (heatKernelMeasure n) := by
  rw [← integrableOn_univ]
  have huniv : (Set.univ : Set (SpaceTime n)) =
    {v | v (0 : Fin (n+1)) < 1} ∪ {v | v (0 : Fin (n+1)) ≥ 1} := by
    ext v; simp [lt_or_ge]
  rw [huniv]
  apply IntegrableOn.union
  ·
    rw [IntegrableOn]
    have hfin : IsFiniteMeasure ((heatKernelMeasure n).restrict
        {v | v (0 : Fin (n+1)) < 1}) := by
      constructor; rw [restrict_apply_univ]; exact heatKernelMeasure_time_lt_one_finite n
    apply Integrable.mono' (g := fun _ => (1 : ℝ))
    · exact integrable_const 1
    · exact (Measurable.aestronglyMeasurable (by fun_prop)).restrict
    · exact Filter.Eventually.of_forall (fun v => by
        rw [Real.norm_rpow_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + ‖v‖)]
        exact Real.rpow_le_one_of_one_le_of_nonpos
          (by rw [Real.norm_of_nonneg (by positivity)]; linarith [norm_nonneg v])
          (by have : (0 : ℝ) ≤ (n + 2 : ℕ) := Nat.cast_nonneg _; linarith))
  ·
    rw [IntegrableOn]
    exact Integrable.mono_measure
      ((integrable_one_add_norm (by simp [Fintype.card_fin])).integrableOn)
      (heatKernelMeasure_le_volume_on_time_ge_one n)

open HeatEquation in
/-- The heat-kernel measure has temperate growth, witnessed by the integrability of
`(1 + ‖x‖)^(-(n+2))` against it. -/
instance HeatEquation.heatKernelMeasure_hasTemperateGrowth (n : ℕ) :
    (heatKernelMeasure n).HasTemperateGrowth where
  exists_integrable := ⟨n + 2, heatKernelMeasure_integrable_one_add_norm n⟩

open HeatEquation in
/-- The forward fundamental solution of the heat operator: the tempered distribution associated
to the heat-kernel measure via the temperate-growth representation. -/
noncomputable def HeatEquation.forwardFundSol (n : ℕ) : 𝓢'(SpaceTime n, ℂ) :=
  (heatKernelMeasure n).toTemperedDistribution


open HeatEquation in
/-- The heat-kernel density is measurable. -/
lemma HeatEquation.heatKernelFun_measurable (n : ℕ) : Measurable (heatKernelFun n) := by
  unfold heatKernelFun
  apply Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
  · exact (by fun_prop : Measurable _).mul (by fun_prop)
  · exact measurable_const


open HeatEquation MeasureTheory in
/-- The weighted-integral form of the fundamental-solution identity: integrating the formal
adjoint `-∂_t - Δ_x` applied to a Schwartz function against the heat-kernel density yields
`φ(0)`. -/
theorem HeatEquation.heatKernelFun_weighted_adjoint_integral_eq
    (n : ℕ) (φ : 𝓢(SpaceTime n, ℂ)) :
    ∫ (v : SpaceTime n),
      (heatKernelFun n v) • ((-∂_{timeDirection n} φ - ∑ i : Fin n,
        ∂_{spatialDirection n i} (∂_{spatialDirection n i} φ)) v : ℂ) =
    φ 0 := by sorry


open HeatEquation MeasureTheory in
set_option maxHeartbeats 800000 in
/-- The measure-theoretic form of the fundamental-solution identity: integrating the formal
adjoint of the heat operator against `φ` with respect to the heat-kernel measure equals `φ(0)`. -/
theorem HeatEquation.heatKernelMeasure_adjoint_integral_eq (n : ℕ) (φ : 𝓢(SpaceTime n, ℂ)) :
    ∫ (x : SpaceTime n),
      (-∂_{timeDirection n} φ - ∑ i : Fin n,
        ∂_{spatialDirection n i} (∂_{spatialDirection n i} φ)) x ∂heatKernelMeasure n =
    φ 0 := by
  rw [show heatKernelMeasure n = Measure.withDensity volume
    (fun v => ENNReal.ofReal (heatKernelFun n v)) from rfl]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    ((heatKernelFun_measurable n).ennreal_ofReal.aemeasurable)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp_rw [ENNReal.toReal_ofReal (heatKernelFun_nonneg n _)]
  exact heatKernelFun_weighted_adjoint_integral_eq n φ


open HeatEquation in
/-- The forward fundamental solution applied to the formal adjoint of the heat operator
evaluated at `φ` yields `φ(0)`. -/
theorem HeatEquation.heatKernel_adjoint_integral (n : ℕ) (φ : 𝓢(SpaceTime n, ℂ)) :
    (forwardFundSol n)
      (-∂_{timeDirection n} φ - ∑ i : Fin n,
        ∂_{spatialDirection n i} (∂_{spatialDirection n i} φ)) = φ 0 := by
  simp only [forwardFundSol, MeasureTheory.Measure.toTemperedDistribution_apply]
  exact heatKernelMeasure_adjoint_integral_eq n φ


open HeatEquation in
/-- The forward fundamental solution satisfies the heat-equation distributional identity
`(∂_t - Δ_x) E = δ₀`, identifying `E` as a fundamental solution of the heat operator. -/
theorem HeatEquation.forwardFundSol_eq (n : ℕ) :
    heatOperator n (forwardFundSol n) = delta 0 := by
  ext φ
  simp only [delta_apply]
  show (∂_{timeDirection n} (forwardFundSol n) -
    positiveSpatialLaplacian n (forwardFundSol n)) φ = φ 0
  unfold positiveSpatialLaplacian
  change (∂_{timeDirection n} (forwardFundSol n)) φ -
    (∑ i : Fin n, ∂_{spatialDirection n i}
      (∂_{spatialDirection n i} (forwardFundSol n))) φ = φ 0
  rw [UniformConvergenceCLM.sum_apply]
  simp only [lineDerivOp_apply_apply, map_neg, neg_neg]
  rw [← map_sum, ← map_neg, ← map_sub]
  exact heatKernel_adjoint_integral n φ

open HeatEquation MeasureTheory in
/-- The forward fundamental solution is supported in the forward time half-space `{t ≥ 0}`,
since the heat-kernel density vanishes for `t ≤ 0`. -/
theorem HeatEquation.forwardFundSol_support (n : ℕ) :
    SupportedInTimeGeq n (forwardFundSol n) 0 := by
  intro x hx
  simp only [Set.mem_setOf_eq]
  by_contra hlt
  push Not at hlt
  rw [mem_dsupport_iff_not_isVanishingOn] at hx
  have hopen : IsOpen {v : SpaceTime n | timeCoord n v < 0} :=
    isOpen_lt (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0) continuous_const
  have := hx _ hlt hopen
  apply this
  intro φ hφ
  simp only [forwardFundSol, MeasureTheory.Measure.toTemperedDistribution_apply]
  apply integral_eq_zero_of_ae
  rw [Filter.EventuallyEq, ae_iff]
  apply measure_mono_null _ (heatKernelMeasure_nonpos_eq_zero n)
  intro v hv
  simp only [Set.mem_setOf_eq, Pi.zero_apply] at hv ⊢
  have hmem : v ∈ Function.support (⇑φ) := hv
  have htsup : v ∈ tsupport (⇑φ) := subset_tsupport _ hmem
  have hlt2 := hφ htsup
  simp only [Set.mem_setOf_eq, timeCoord] at hlt2
  exact le_of_lt hlt2


open HeatEquation DifferentialOperators in
/-- The continuous linear map sending a Schwartz function `φ` to the convolution
`v * φ` (smoothed via the compact-distributional-support convolution construction), packaged
as a `𝓢(ℝ^(n+1), ℂ) →L[ℂ] 𝓢(ℝ^(n+1), ℂ)` map. -/
def HeatEquation.reflConvSchwartzMap (n : ℕ)
    (v : 𝓢'(SpaceTime n, ℂ)) (hv : HasCompactDSupport n v) :
    𝓢(SpaceTime n, ℂ) →L[ℂ] 𝓢(SpaceTime n, ℂ) :=
  ⟨{ toFun := compactDsupportConvolutionSchwartzMap v hv
     map_add' := compactDsupportConvolution_map_add v hv
     map_smul' := compactDsupportConvolution_map_smul v hv },
   continuous_compactDsupportConvolution v hv⟩


open HeatEquation DifferentialOperators in
/-- Evaluating the reflected convolution `reflConvSchwartzMap n f hf φ` at the origin recovers
`f φ`. -/
theorem HeatEquation.reflConvSchwartzMap_apply_zero (n : ℕ)
    (f : 𝓢'(SpaceTime n, ℂ)) (hf : HasCompactDSupport n f)
    (φ : 𝓢(SpaceTime n, ℂ)) :
    (reflConvSchwartzMap n f hf φ) 0 = f φ := by
  simp only [reflConvSchwartzMap, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
    compactDsupportConvolutionSchwartzMap_apply, SchwartzMap.compSubConstCLM_zero,
    ContinuousLinearMap.id_apply]


open HeatEquation in
/-- The distributional convolution `dconv n u v hv = u * v` when `v` has compact distributional
support, defined as the composition of `u` with the reflected-convolution Schwartz map. -/
def HeatEquation.dconv (n : ℕ)
    (u v : 𝓢'(SpaceTime n, ℂ)) (hv : HasCompactDSupport n v) :
    𝓢'(SpaceTime n, ℂ) :=
  u.comp (reflConvSchwartzMap n v hv)


open HeatEquation DifferentialOperators in
/-- The Fréchet derivative of the convolution `f * φ` is computed via the test-function
translation identity. -/
theorem HeatEquation.compactDsupport_conv_fderiv_eq (n : ℕ)
    (f : 𝓢'(SpaceTime n, ℂ)) (hf : HasCompactDSupport n f)
    (m : SpaceTime n) (φ : 𝓢(SpaceTime n, ℂ)) (x : SpaceTime n) :
    (fderiv ℝ (⇑(compactDsupportConvolutionSchwartzMap f hf φ)) x) m =
      f ((SchwartzMap.compSubConstCLM ℂ x) (∂_{-m} φ)) := by
  have hfun_eq : (⇑(compactDsupportConvolutionSchwartzMap f hf φ) : SpaceTime n → ℂ) =
      (fun z => f (SchwartzMap.compSubConstCLM ℂ z φ)) := by ext z; rfl
  rw [hfun_eq]
  exact SmoothingOperators.schwartz_translation_fderiv_apply f φ x m


open HeatEquation DifferentialOperators in
/-- Commutation of `reflConvSchwartzMap` with directional derivatives: applying the line
derivative `∂_{-m}` to `φ` before convolving equals applying `∂_m` after convolving. -/
theorem HeatEquation.reflConvSchwartzMap_comm_lineDerivOp (n : ℕ)
    (f : 𝓢'(SpaceTime n, ℂ)) (hf : HasCompactDSupport n f)
    (m : SpaceTime n) (φ : 𝓢(SpaceTime n, ℂ)) :
    reflConvSchwartzMap n f hf (∂_{-m} φ) = ∂_{m} (reflConvSchwartzMap n f hf φ) := by
  ext x
  simp only [reflConvSchwartzMap, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
    compactDsupportConvolutionSchwartzMap_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  exact (compactDsupport_conv_fderiv_eq n f hf m φ x).symm


open HeatEquation in
/-- The line derivative `∂_{-m}` of a distributional convolution `dconv n u f hf` equals the
convolution of `∂_m u` with `f`. -/
lemma HeatEquation.lineDerivOp_dconv (n : ℕ)
    (u f : 𝓢'(SpaceTime n, ℂ)) (hf : HasCompactDSupport n f)
    (m : SpaceTime n) :
    ∂_{-m} (dconv n u f hf) = dconv n (∂_{m} u) f hf := by
  ext φ
  change u (reflConvSchwartzMap n f hf (-∂_{-m} φ)) = (∂_{m} u) (reflConvSchwartzMap n f hf φ)
  rw [show -∂_{-m} φ = ∂_{m} φ from by ext y; simp [SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.neg_apply, map_neg]]
  have hcomm := reflConvSchwartzMap_comm_lineDerivOp n f hf m φ


  have hcomm' : reflConvSchwartzMap n f hf (∂_{m} φ) = ∂_{-m} (reflConvSchwartzMap n f hf φ) := by
    have := reflConvSchwartzMap_comm_lineDerivOp n f hf (-m) φ
    simp only [neg_neg] at this
    exact this
  rw [hcomm']


  rw [lineDerivOp_apply_apply]
  congr 1
  ext y
  simp [SchwartzMap.lineDerivOp_apply_eq_fderiv, SchwartzMap.neg_apply, map_neg]


open HeatEquation in

open HeatEquation in
/-- The heat operator commutes with the distributional convolution:
`heatOperator (u * f) = (heatOperator u) * f` when `f` has compact distributional support. -/
theorem HeatEquation.heatOp_dconv (n : ℕ)
    (u f : 𝓢'(SpaceTime n, ℂ)) (hf : HasCompactDSupport n f) :
    heatOperator n (dconv n u f hf) = dconv n (heatOperator n u) f hf := by sorry

open HeatEquation in
/-- The Dirac delta at the origin is the identity for distributional convolution:
`δ₀ * f = f` for any `f` with compact distributional support. -/
theorem HeatEquation.delta_dconv (n : ℕ)
    (f : 𝓢'(SpaceTime n, ℂ)) (hf : HasCompactDSupport n f) :
    dconv n (delta 0) f hf = f := by
  ext φ
  simp only [dconv]
  show (delta (0 : SpaceTime n)) (reflConvSchwartzMap n f hf φ) = f φ
  rw [TemperedDistribution.delta_apply]
  exact reflConvSchwartzMap_apply_zero n f hf φ


open HeatEquation in
set_option maxHeartbeats 800000 in
/-- If the distributional support of `u` is contained in a closed set `S`, then `u` vanishes
on the open complement `Sᶜ` (in the sense that `u φ = 0` whenever `tsupport φ ⊆ Sᶜ`). -/
theorem HeatEquation.isVanishingOn_compl_of_dsupport_subset (n : ℕ)
    (u : 𝓢'(SpaceTime n, ℂ)) (S : Set (SpaceTime n))
    (hS : IsClosed S) (h : dsupport u ⊆ S) :
    IsVanishingOn u Sᶜ := by
  intro φ hφ


  suffices h_compact : ∀ (ψ : 𝓢(SpaceTime n, ℂ)),
      HasCompactSupport ψ → tsupport (⇑ψ) ⊆ Sᶜ → u ψ = 0 by


    have htend : Filter.Tendsto (fun m => SchwartzMap.bumpCutoffMul m φ)
        Filter.atTop (nhds φ) := by
      rw [(schwartz_withSeminorms ℂ (SpaceTime n) ℂ).tendsto_nhds _ φ]
      intro ⟨k, j⟩ ε hε
      have h1 := SchwartzMap.seminorm_cutoff_sub_tendsto ℂ φ k j
      rw [Metric.tendsto_atTop] at h1
      obtain ⟨N, hN⟩ := h1 ε hε
      filter_upwards [Filter.Ici_mem_atTop N] with m hm
      simp only [SchwartzMap.schwartzSeminormFamily_apply]
      have h2 := hN m hm
      rw [Real.dist_0_eq_abs, abs_of_nonneg (apply_nonneg _ _)] at h2
      calc (SchwartzMap.seminorm ℂ k j) (SchwartzMap.bumpCutoffMul m φ - φ)
          = (SchwartzMap.seminorm ℂ k j) (φ - SchwartzMap.bumpCutoffMul m φ) := by
            rw [← map_neg_eq_map]; congr 1; abel
        _ < ε := h2
    have hvanish : ∀ m : ℕ, u (SchwartzMap.bumpCutoffMul m φ) = 0 := by
      intro m
      apply h_compact
      · exact SchwartzMap.bumpCutoffMul_hasCompactSupport m φ
      · calc tsupport ⇑(SchwartzMap.bumpCutoffMul m φ)
            ⊆ tsupport (⇑φ) := by
              apply closure_mono; intro x hx
              rw [Function.mem_support] at hx ⊢
              intro hf; apply hx; simp [hf]
          _ ⊆ Sᶜ := hφ

    have hclosed : IsClosed {ψ : 𝓢(SpaceTime n, ℂ) | u ψ = 0} :=
      isClosed_eq u.cont continuous_const
    have hmem : φ ∈ closure {ψ : 𝓢(SpaceTime n, ℂ) | u ψ = 0} := by
      apply mem_closure_of_tendsto htend
      exact Filter.Eventually.of_forall hvanish
    have hmem2 : φ ∈ {ψ : 𝓢(SpaceTime n, ℂ) | u ψ = 0} :=
      closure_minimal (fun ψ hψ => hψ) hclosed hmem
    exact hmem2

  intro ψ hcs hψ
  classical
  have h_Sc_vanish : ∀ x ∈ Sᶜ, ∃ V : Set (SpaceTime n),
      IsOpen V ∧ x ∈ V ∧ IsVanishingOn u V := by
    intro x hx
    have : x ∉ dsupport u := fun hd => hx (h hd)
    rw [notMem_dsupport_iff] at this
    obtain ⟨V, hV_van, hV_open, hx_mem⟩ := this
    exact ⟨V, hV_open, hx_mem, hV_van⟩
  let V : SpaceTime n → Set (SpaceTime n) := fun x =>
    if hx : x ∈ Sᶜ then (h_Sc_vanish x hx).choose else (tsupport (⇑ψ))ᶜ
  have hV_open : ∀ x, IsOpen (V x) := by
    intro x; simp only [V]
    split_ifs with hx
    · exact (h_Sc_vanish x hx).choose_spec.1
    · exact (isClosed_tsupport _).isOpen_compl
  have hV_mem : ∀ x, x ∈ V x := by
    intro x; simp only [V]
    split_ifs with hx
    · exact (h_Sc_vanish x hx).choose_spec.2.1
    · exact fun hmem => hx (hψ hmem)
  have hV_cover : Set.univ ⊆ ⋃ x, V x :=
    fun x _ => Set.mem_iUnion.mpr ⟨x, hV_mem x⟩
  obtain ⟨ρ, hρ_sub⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (modelWithCornersSelf ℝ (SpaceTime n)) isClosed_univ V hV_open hV_cover
  have hlf := ρ.locallyFinite
  have hfin : {i | (Function.support (⇑(ρ i)) ∩ tsupport (⇑ψ)).Nonempty}.Finite :=
    hlf.finite_nonempty_inter_compact hcs
  set s := hfin.toFinset with hs_def
  have hρ_smooth : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (ρ i : SpaceTime n → ℝ) := by
    intro i; rw [← contMDiff_iff_contDiff]; exact (ρ i).contMDiff
  have hprod_cs : ∀ i, HasCompactSupport (fun x => (↑(ρ i x) : ℂ) * ψ x) :=
    fun i => hcs.mul_left
  have hprod_smooth : ∀ i,
      ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (↑(ρ i x) : ℂ) * ψ x) :=
    fun i => (Complex.ofRealCLM.contDiff.comp (hρ_smooth i)).mul (ψ.smooth ⊤)
  let g : SpaceTime n → 𝓢(SpaceTime n, ℂ) :=
    fun i => (hprod_cs i).toSchwartzMap (hprod_smooth i)
  have hg_vanish : ∀ i, u (g i) = 0 := by
    intro i
    by_cases hi : i ∈ Sᶜ
    · have hV_van : IsVanishingOn u (V i) := by
        simp only [V, dif_pos hi]
        exact (h_Sc_vanish i hi).choose_spec.2.2
      have hg_tsup : tsupport (⇑(g i)) ⊆ V i := by
        calc tsupport ⇑(g i) ⊆ tsupport (ρ i : SpaceTime n → ℝ) := by
              apply closure_mono; intro x hx
              rw [Function.mem_support] at hx ⊢
              intro hρx; apply hx
              show (↑(ρ i x) : ℂ) * ψ x = 0; simp [hρx]
           _ ⊆ V i := hρ_sub i
      exact hV_van _ hg_tsup
    · have hV_eq : V i = (tsupport (⇑ψ))ᶜ := by simp only [V]; rw [dif_neg hi]
      have hgi_zero : g i = 0 := by
        ext x; show (↑(ρ i x) : ℂ) * ψ x = 0
        by_cases hρ : (ρ i) x = 0
        · simp [hρ]
        · have hx_in_V : x ∈ V i :=
            (hρ_sub i) (subset_tsupport _ (Function.mem_support.mpr hρ))
          rw [hV_eq] at hx_in_V
          simp [image_eq_zero_of_notMem_tsupport hx_in_V]
      rw [hgi_zero, map_zero]
  have hψ_eq : ψ = ∑ i ∈ s, g i := by
    ext x
    have hsum_app : (∑ i ∈ s, g i) x = ∑ i ∈ s, (g i) x := by simp
    rw [hsum_app]
    have heq : ∀ i, (g i) x = (↑(ρ i x) : ℂ) * ψ x :=
      fun i => (hprod_cs i).toSchwartzMap_toFun (hprod_smooth i) x
    simp_rw [heq, ← Finset.sum_mul]
    by_cases hψx : (ψ : SpaceTime n → ℂ) x = 0
    · simp [hψx]
    · have hx_supp : x ∈ tsupport (⇑ψ) :=
        subset_tsupport _ (Function.mem_support.mpr hψx)
      have hρ_zero : ∀ i, i ∉ s → (ρ i) x = 0 := by
        intro i hi; by_contra h'
        exact hi (hs_def ▸ hfin.mem_toFinset.mpr
          ⟨x, Function.mem_support.mpr h', hx_supp⟩)
      have hsum_one : ∑ᶠ i, (ρ i) x = 1 := ρ.sum_eq_one (Set.mem_univ x)
      have hsupp : Function.support (fun i => (ρ i) x) ⊆ ↑s := by
        intro i hi; rw [Finset.mem_coe]
        by_contra hi'; exact (Function.mem_support.mp hi) (hρ_zero i hi')
      rw [finsum_eq_sum_of_support_subset _ hsupp] at hsum_one
      have hcsum : (∑ i ∈ s, (↑(ρ i x) : ℂ)) = 1 := by
        rw [← Complex.ofReal_one, ← hsum_one]; push_cast; rfl
      rw [hcsum, one_mul]
  rw [hψ_eq, map_sum]
  exact Finset.sum_eq_zero (fun i _ => hg_vanish i)


open HeatEquation in
/-- Support property of the reflected-convolution Schwartz map: if `f` is supported in
`{t ≥ b}` and `φ` has time support in `{t < a + b}`, then the convolution
`reflConvSchwartzMap n f hf φ` has time support in `{t < a}`. -/
theorem HeatEquation.reflConvSchwartzMap_tsupport_subset (n : ℕ)
    (f : 𝓢'(SpaceTime n, ℂ)) (hf : HasCompactDSupport n f)
    (a b : ℝ) (hb : SupportedInTimeGeq n f b)
    (φ : 𝓢(SpaceTime n, ℂ))
    (hφ : tsupport (↑φ : SpaceTime n → ℂ) ⊆ {x : SpaceTime n | timeCoord n x < a + b}) :
    tsupport (↑(reflConvSchwartzMap n f hf φ) : SpaceTime n → ℂ) ⊆
      {x : SpaceTime n | timeCoord n x < a} := by sorry

open HeatEquation in
/-- If `u` is supported in `{t ≥ a}` and `f` is supported in `{t ≥ b}`, then `u` vanishes on
the convolution `reflConvSchwartzMap n f hf φ` whenever `φ` has time support in `{t < a + b}`. -/
theorem HeatEquation.reflConvSchwartzMap_isVanishingOn (n : ℕ)
    (u f : 𝓢'(SpaceTime n, ℂ)) (hf : HasCompactDSupport n f)
    (a b : ℝ) (ha : SupportedInTimeGeq n u a) (hb : SupportedInTimeGeq n f b) :
    ∀ (φ : 𝓢(SpaceTime n, ℂ)),
      tsupport (↑φ : SpaceTime n → ℂ) ⊆ {x : SpaceTime n | timeCoord n x < a + b} →
      u (reflConvSchwartzMap n f hf φ) = 0 := by
  intro φ hφ

  have hsupp : tsupport (↑(reflConvSchwartzMap n f hf φ) : SpaceTime n → ℂ) ⊆
      {x : SpaceTime n | timeCoord n x < a} :=
    reflConvSchwartzMap_tsupport_subset n f hf a b hb φ hφ

  have hvan : IsVanishingOn u {x : SpaceTime n | timeCoord n x < a} := by
    have hclosed : IsClosed {x : SpaceTime n | timeCoord n x ≥ a} :=
      isClosed_le continuous_const
        (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0)
    have hcompl : {x : SpaceTime n | timeCoord n x < a} =
        {x : SpaceTime n | timeCoord n x ≥ a}ᶜ := by
      ext x; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
    rw [hcompl]
    exact isVanishingOn_compl_of_dsupport_subset n u _ hclosed ha

  exact hvan (reflConvSchwartzMap n f hf φ) hsupp


open HeatEquation in
/-- Support additivity for the distributional convolution: if `u` is supported in `{t ≥ a}`
and `f` in `{t ≥ b}`, then `dconv n u f hf` is supported in `{t ≥ a + b}`. -/
theorem HeatEquation.dconv_support_timeGeq (n : ℕ)
    (u f : 𝓢'(SpaceTime n, ℂ)) (hf : HasCompactDSupport n f)
    (a b : ℝ) (ha : SupportedInTimeGeq n u a) (hb : SupportedInTimeGeq n f b) :
    SupportedInTimeGeq n (dconv n u f hf) (a + b) := by
  intro x hx
  rw [Distribution.mem_dsupport_iff] at hx
  apply hx {x | timeCoord n x ≥ a + b}
  ·
    intro φ hφ
    have hφ' : tsupport (↑φ : SpaceTime n → ℂ) ⊆ {x | timeCoord n x < a + b} := by
      convert hφ using 1
      ext x
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]

    show u (reflConvSchwartzMap n f hf φ) = 0
    exact reflConvSchwartzMap_isVanishingOn n u f hf a b ha hb φ hφ'
  · exact isClosed_le continuous_const
      (PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) 0)


open HeatEquation in
/-- Cutoff heat-kernel identity: there exists a cutoff `E_s` of the forward fundamental solution
with compact distributional support and an "error" distribution `ψ` (supported in `{t ≥ s}`) such
that the heat operator applied to the convolution `v * E_s` equals `v + v * ψ` for all `v`. This
is a key technical tool for the uniqueness argument in Prop 11.16. -/
theorem HeatEquation.cutoffHeatKernel_identity (n : ℕ) (s : ℝ) :
    ∃ (E_s : 𝓢'(SpaceTime n, ℂ)) (hE_s : HasCompactDSupport n E_s)
      (ψ : 𝓢'(SpaceTime n, ℂ)) (hψ : HasCompactDSupport n ψ),
      SupportedInTimeGeq n ψ s ∧
      ∀ (v : 𝓢'(SpaceTime n, ℂ)),
        heatOperator n (dconv n v E_s hE_s) = v + dconv n v ψ hψ := by sorry

open HeatEquation in
/-- Cutoff perturbation identity for homogeneous heat solutions: for every `s`, there is a
distribution `ψ` (with compact distributional support, supported in `{t ≥ s}`) such that any
solution `v` of the homogeneous heat equation satisfies `v + v * ψ = 0`. -/
theorem HeatEquation.cutoffPerturbation_exists (n : ℕ) (s : ℝ) :
    ∃ (ψ : 𝓢'(SpaceTime n, ℂ)) (hψ : HasCompactDSupport n ψ),
      SupportedInTimeGeq n ψ s ∧
      ∀ (v : 𝓢'(SpaceTime n, ℂ)),
        heatOperator n v = 0 →
        v + dconv n v ψ hψ = 0 := by

  obtain ⟨E_s, hE_s, ψ, hψ, hψ_supp, hident⟩ := cutoffHeatKernel_identity n s
  exact ⟨ψ, hψ, hψ_supp, fun v hv => by

    have h1 := hident v

    have h2 := heatOp_dconv n v E_s hE_s

    rw [hv] at h2

    have h3 : dconv n 0 E_s hE_s = 0 := ContinuousLinearMap.zero_comp _
    rw [h3] at h2

    rw [h2] at h1
    exact h1.symm⟩


open HeatEquation in
/-- Support-shift lemma for homogeneous heat solutions: a homogeneous solution `v` whose support
lies in `{t ≥ T'}` is in fact supported in `{t ≥ T' + s}` for every `s`. Iterating this drives
the support to `∅`, yielding uniqueness. -/
theorem HeatEquation.heat_homogeneous_support_shift (n : ℕ)
    (v : 𝓢'(SpaceTime n, ℂ))
    (hv_eq : heatOperator n v = 0)
    (T' s : ℝ)
    (hsupp : SupportedInTimeGeq n v T') :
    SupportedInTimeGeq n v (T' + s) := by

  obtain ⟨ψ, hψ_compact, hψ_supp, hψ_eq⟩ := cutoffPerturbation_exists n s

  have hv_identity := hψ_eq v hv_eq

  have hv_neg : v = -(dconv n v ψ hψ_compact) := eq_neg_of_add_eq_zero_left hv_identity

  have hconv_supp := dconv_support_timeGeq n v ψ hψ_compact T' s hsupp hψ_supp

  rw [hv_neg]
  exact (supportedInTimeGeq_neg n _ _).mpr hconv_supp


open HeatEquation in
/-- A tempered distribution with empty distributional support is the zero distribution. -/
theorem HeatEquation.dsupport_eq_empty_imp_eq_zero (n : ℕ)
    (v : 𝓢'(SpaceTime n, ℂ))
    (h : Distribution.dsupport v = ∅) :
    v = 0 := by sorry


open HeatEquation in
/-- Uniqueness statement for the homogeneous heat equation: any solution `v` of
`(∂_t - Δ_x) v = 0` whose distributional support is bounded below in time must vanish. -/
theorem HeatEquation.heat_homogeneous_uniqueness (n : ℕ)
    (v : 𝓢'(SpaceTime n, ℂ))
    (hv_eq : heatOperator n v = 0)
    (hv_supp : ∃ T' : ℝ, SupportedInTimeGeq n v T') :
    v = 0 := by
  obtain ⟨T', hT'⟩ := hv_supp
  apply dsupport_eq_empty_imp_eq_zero
  by_contra h
  rw [← Ne, ← Set.nonempty_iff_ne_empty] at h
  obtain ⟨x, hx⟩ := h

  have shift : ∀ M : ℝ, SupportedInTimeGeq n v M := by
    intro M
    have key := heat_homogeneous_support_shift n v hv_eq T' (M - T') hT'
    rwa [add_sub_cancel] at key

  have hM : timeCoord n x ≥ timeCoord n x + 1 := (shift (timeCoord n x + 1)) hx
  linarith

namespace HeatEquation

variable (n : ℕ)

/-- The heat operator is linear, in particular `heatOperator (u - v) = heatOperator u
- heatOperator v`. -/
lemma heatOperator_sub (u v : 𝓢'(SpaceTime n, ℂ)) :
    heatOperator n (u - v) = heatOperator n u - heatOperator n v := by
  simp only [heatOperator, positiveSpatialLaplacian, sub_eq_add_neg,
    lineDerivOp_add, lineDerivOp_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  abel

/-- Proposition 11.16 (existence and uniqueness for the heat equation): for every tempered
distribution `f` with compact distributional support, there is a unique tempered distribution `u`,
bounded below in time, satisfying `(∂_t - Δ_x) u = f`. -/
theorem heat_equation_existence_uniqueness
    (f : 𝓢'(SpaceTime n, ℂ)) (hf : HasCompactDSupport n f) :
    ∃! u : 𝓢'(SpaceTime n, ℂ),
      (∃ T : ℝ, SupportedInTimeGeq n u (-T)) ∧ heatOperator n u = f := by
  set u₀ := dconv n (forwardFundSol n) f hf
  have h_u₀_eq : heatOperator n u₀ = f :=
    calc heatOperator n u₀
        = dconv n (heatOperator n (forwardFundSol n)) f hf :=
          heatOp_dconv n (forwardFundSol n) f hf
      _ = dconv n (delta 0) f hf := by rw [forwardFundSol_eq]
      _ = f := delta_dconv n f hf
  have h_u₀_supp : ∀ b, SupportedInTimeGeq n f b → SupportedInTimeGeq n u₀ b := by
    intro b hb x hx
    have := dconv_support_timeGeq n (forwardFundSol n) f hf 0 b
      (forwardFundSol_support n) hb hx
    simp only [Set.mem_setOf_eq, zero_add] at this
    exact this
  refine ⟨u₀, ?_, ?_⟩
  · refine ⟨?_, h_u₀_eq⟩
    obtain ⟨b, hb⟩ := compact_dsupport_time_bounded_below n f hf
    exact ⟨-b, by simpa only [neg_neg] using h_u₀_supp b hb⟩
  · intro u₁ ⟨⟨T₁, hT₁⟩, hu₁_eq⟩
    have hv_eq : heatOperator n (u₁ - u₀) = 0 := by
      rw [heatOperator_sub, hu₁_eq, h_u₀_eq, sub_self]
    have hv_supp : ∃ T' : ℝ, SupportedInTimeGeq n (u₁ - u₀) T' := by
      obtain ⟨b, hb⟩ := compact_dsupport_time_bounded_below n f hf
      exact ⟨min (-T₁) b, supportedInTimeGeq_sub n u₁ u₀ (-T₁) b hT₁ (h_u₀_supp b hb)⟩
    exact sub_eq_zero.mp (heat_homogeneous_uniqueness n (u₁ - u₀) hv_eq hv_supp)

end HeatEquation

end
