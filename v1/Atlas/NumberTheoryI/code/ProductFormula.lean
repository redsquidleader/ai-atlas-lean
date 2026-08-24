/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Complex
import Mathlib.Analysis.Normed.Field.ProperSpace

noncomputable section

open MeasureTheory Measure TopologicalSpace Pointwise Filter Topology

structure IsRadonMeasure {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [T2Space X] [LocallyCompactSpace X]
    (μ : MeasureTheory.Measure X) : Prop where
  isFiniteMeasureOnCompacts : MeasureTheory.IsFiniteMeasureOnCompacts μ
  regular : MeasureTheory.Measure.Regular μ
  innerRegular : MeasureTheory.Measure.InnerRegular μ

theorem compact_group_finite_measure (G : Type*) [AddCommGroup G] [TopologicalSpace G]
    [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure] : IsFiniteMeasure μ :=
  CompactSpace.isFiniteMeasure

theorem weil_uniqueness (G : Type*) [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    (μ ν : Measure G) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure] :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧ ν = c • μ := by
  obtain ⟨K0⟩ := PositiveCompacts.nonempty' (α := G)
  set c := ν ↑K0 / μ ↑K0 with hc_def
  have hμ_pos : μ ↑K0 ≠ 0 :=
    (measure_pos_of_nonempty_interior μ K0.interior_nonempty).ne'
  have hμ_fin : μ ↑K0 ≠ ⊤ := (IsCompact.measure_lt_top K0.isCompact).ne
  have hν_pos : ν ↑K0 ≠ 0 :=
    (measure_pos_of_nonempty_interior ν K0.interior_nonempty).ne'
  have hν_fin : ν ↑K0 ≠ ⊤ := (IsCompact.measure_lt_top K0.isCompact).ne
  refine ⟨c, ENNReal.div_ne_zero.mpr ⟨hν_pos, hμ_fin⟩,
         ENNReal.div_ne_top hν_fin hμ_pos, ?_⟩


  have hμ_eq := addHaarMeasure_unique μ K0
  have hν_eq := addHaarMeasure_unique ν K0
  rw [hμ_eq, hν_eq, smul_smul, hc_def, ENNReal.div_mul_cancel hμ_pos hμ_fin]

def mulLeftContinuousAddEquiv {K : Type*} [NormedField K]
    {a : K} (ha : a ≠ 0) : K ≃ₜ+ K :=
  ContinuousAddEquiv.mk
    { toFun := (a * ·)
      invFun := (a⁻¹ * ·)
      left_inv := fun x => by
        show a⁻¹ * (a * x) = x; rw [← mul_assoc, inv_mul_cancel₀ ha, one_mul]
      right_inv := fun x => by
        show a * (a⁻¹ * x) = x; rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]
      map_add' := fun x y => by show a * (x + y) = a * x + a * y; ring }

@[simp] lemma mulLeftContinuousAddEquiv_apply {K : Type*} [NormedField K]
    {a : K} (ha : a ≠ 0) (x : K) :
    mulLeftContinuousAddEquiv ha x = a * x := rfl

lemma mulLeftContinuousAddEquiv_preimage_smul {K : Type*} [NormedField K]
    {a : K} (ha : a ≠ 0) (S : Set K) :
    (mulLeftContinuousAddEquiv ha) ⁻¹' (a • S) = S := by
  ext x
  simp only [Set.mem_preimage, mulLeftContinuousAddEquiv_apply,
    Set.mem_smul_set_iff_inv_smul_mem₀ ha, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ ha, one_mul]

lemma mulLeftContinuousAddEquiv_symm {K : Type*} [NormedField K]
    {a : K} (ha : a ≠ 0) :
    (mulLeftContinuousAddEquiv ha).symm = mulLeftContinuousAddEquiv (inv_ne_zero ha) := by
  ext x; show a⁻¹ * x = a⁻¹ * x; rfl

theorem proposition_13_16_haar_scaling
    (K : Type*) [NormedField K] [LocallyCompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]
    (a : K) (ha : a ≠ 0) (S : Set K) :
    μ (a • S) = ↑(addEquivAddHaarChar (mulLeftContinuousAddEquiv ha)) * μ S := by
  have hscale := addEquivAddHaarChar_smul_preimage μ (mulLeftContinuousAddEquiv ha) (X := a • S)
  rw [mulLeftContinuousAddEquiv_preimage_smul ha S] at hscale
  rw [← hscale]; simp

lemma distribHaarChar_eq_addEquivAddHaarChar_mulLeft
    {K : Type*} [NormedField K] [LocallyCompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    {a : K} (ha : a ≠ 0) :
    distribHaarChar K (Units.mk0 a ha) =
    addEquivAddHaarChar (mulLeftContinuousAddEquiv ha) := by
  obtain ⟨s, hs_compact, hs_nhd⟩ := exists_compact_mem_nhds (0 : K)
  have hs_ne_zero : (addHaar : Measure K) s ≠ 0 := by
    obtain ⟨U, hU_sub, hU_open, h0U⟩ := mem_nhds_iff.mp hs_nhd
    exact ne_of_gt (lt_of_lt_of_le (hU_open.measure_pos addHaar ⟨0, h0U⟩) (measure_mono hU_sub))
  have hs_ne_top : (addHaar : Measure K) s ≠ ⊤ := hs_compact.measure_lt_top.ne
  apply distribHaarChar_eq_of_measure_smul_eq_mul (s := s) (μ := addHaar) hs_ne_zero hs_ne_top
  have h := addEquivAddHaarChar_smul_preimage addHaar (mulLeftContinuousAddEquiv ha)
    (X := (Units.mk0 a ha) • s)
  have preimage_eq : (mulLeftContinuousAddEquiv ha) ⁻¹' ((Units.mk0 a ha) • s) = s := by
    ext x
    simp only [Set.mem_preimage, Set.mem_smul_set]
    constructor
    · rintro ⟨y, hy, hxy⟩
      have : a * y = a * x := by
        simp only [Units.smul_def, smul_eq_mul, Units.val_mk0] at hxy; exact hxy
      exact mul_left_cancel₀ ha this ▸ hy
    · intro hx
      exact ⟨x, hx, by simp [Units.smul_def, smul_eq_mul, mulLeftContinuousAddEquiv]⟩
  rw [preimage_eq] at h
  rw [← h]; simp [ENNReal.smul_def, smul_eq_mul]

lemma units_smul_closedBall_zero_one {K : Type*} [NormedField K] (g : Kˣ) :
    (g : K) • Metric.closedBall (0 : K) 1 = Metric.closedBall (0 : K) ‖(g : K)‖ := by
  ext x
  simp only [Set.mem_smul_set, Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [smul_eq_mul]
    calc ‖(g : K) * y‖ = ‖(g : K)‖ * ‖y‖ := norm_mul _ _
    _ ≤ ‖(g : K)‖ * 1 := by gcongr
    _ = ‖(g : K)‖ := mul_one _
  · intro hx
    refine ⟨(g : K)⁻¹ * x, ?_, ?_⟩
    · show ‖(↑g)⁻¹ * x‖ ≤ 1
      calc ‖(g : K)⁻¹ * x‖ = ‖(g : K)‖⁻¹ * ‖x‖ := by rw [norm_mul, norm_inv]
      _ ≤ ‖(g : K)‖⁻¹ * ‖(g : K)‖ := by gcongr
      _ = 1 := inv_mul_cancel₀ (norm_ne_zero_iff.mpr g.ne_zero)
    · simp [smul_eq_mul]

lemma units_smul_ball_zero_one {K : Type*} [NormedField K] (g : Kˣ) :
    (g : K) • Metric.ball (0 : K) 1 = Metric.ball (0 : K) ‖(g : K)‖ := by
  ext x
  simp only [Set.mem_smul_set, Metric.mem_ball, dist_zero_right]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [smul_eq_mul, norm_mul]
    exact mul_lt_of_lt_one_right (norm_pos_iff.mpr g.ne_zero) hy
  · intro hx
    refine ⟨(g : K)⁻¹ * x, ?_, ?_⟩
    · simp only [norm_mul, norm_inv]
      rw [inv_mul_lt_iff₀ (norm_pos_iff.mpr g.ne_zero)]
      linarith
    · simp [smul_eq_mul]

end

open MeasureTheory MeasureTheory.Measure Metric Pointwise in
theorem dvr_index_eq_nnnorm_inv
  (K : Type*) [NontriviallyNormedField K] [LocallyCompactSpace K] [IsUltrametricDist K]
  (g : Kˣ) (hg : ‖(g : K)‖ < 1)
  (reps : Finset K)
  (hcover : closedBall (0 : K) 1 = ⋃ a ∈ reps, closedBall a ‖(g : K)‖)
  (hdisjoint : ∀ a ∈ reps, ∀ b ∈ reps, a ≠ b →
      Disjoint (closedBall a ‖(g : K)‖) (closedBall b ‖(g : K)‖)) :
  (reps.card : NNReal) * ‖(g : K)‖₊ = 1 := by sorry

open MeasureTheory MeasureTheory.Measure Metric Pointwise in
theorem haar_closedBall_eq_nnnorm_mul_of_norm_lt_one
  (K : Type*) [NontriviallyNormedField K] [LocallyCompactSpace K] [IsUltrametricDist K]
  [MeasurableSpace K] [BorelSpace K]
  (μ : MeasureTheory.Measure K) [μ.IsAddHaarMeasure]
  (g : Kˣ) (hg : ‖(g : K)‖ < 1) :
  μ (Metric.closedBall (0 : K) ‖(g : K)‖) = ↑‖(g : K)‖₊ * μ (Metric.closedBall (0 : K) 1) := by
  haveI : ProperSpace K :=
    ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  set r := ‖(g : K)‖ with hr_def
  have hr_pos : 0 < r := norm_pos_iff.mpr (Units.ne_zero g)
  have hr_ne : r ≠ 0 := hr_pos.ne'
  have hball_sub : ∀ a ∈ closedBall (0 : K) 1,
      closedBall a r ⊆ closedBall (0 : K) 1 := by
    intro a ha x hx
    simp only [mem_closedBall] at *
    calc dist x 0 ≤ max (dist x a) (dist a 0) := IsUltrametricDist.dist_triangle_max x a 0
      _ ≤ max r 1 := max_le_max hx ha
      _ = 1 := max_eq_right hg.le
  obtain ⟨T, hT⟩ := (isCompact_closedBall (0 : K) 1).elim_finite_subcover
    (fun x : K => closedBall x r)
    (fun x => IsUltrametricDist.isOpen_closedBall x (r := r) hr_ne)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, mem_closedBall_self hr_pos.le⟩)
  classical
  let useful := T.filter (fun a => (closedBall a r ∩ closedBall (0 : K) 1).Nonempty)
  let canon : K → K := fun a =>
    Classical.epsilon (fun x => x ∈ closedBall a r ∩ closedBall (0 : K) 1)
  have hcanon_consistent : ∀ a b : K,
      closedBall a r = closedBall b r → canon a = canon b := by
    intro a b hab
    show Classical.epsilon _ = Classical.epsilon _
    congr 1; ext x; rw [hab]
  have hcanon_spec : ∀ a : K,
      (closedBall a r ∩ closedBall (0 : K) 1).Nonempty →
      canon a ∈ closedBall a r ∩ closedBall (0 : K) 1 :=
    fun a hne => Classical.epsilon_spec hne
  have hcanon_mem : ∀ a ∈ useful, canon a ∈ closedBall (0 : K) 1 :=
    fun a ha => (hcanon_spec a (Finset.mem_filter.mp ha).2).2
  have hcanon_ball : ∀ a ∈ useful, closedBall (canon a) r = closedBall a r :=
    fun a ha => (IsUltrametricDist.closedBall_eq_of_mem
      (hcanon_spec a (Finset.mem_filter.mp ha).2).1).symm
  have hcanon_idemp : ∀ a ∈ useful, canon (canon a) = canon a := by
    intro a ha; exact hcanon_consistent _ _ (hcanon_ball a ha)
  let reps := useful.image canon
  have hcover : closedBall (0 : K) 1 = ⋃ a ∈ reps, closedBall a r := by
    ext x; constructor
    · intro hx
      obtain ⟨a, haT, hxa⟩ := Set.mem_iUnion₂.mp (hT hx)
      exact Set.mem_biUnion (Finset.mem_image.mpr
        ⟨a, Finset.mem_filter.mpr ⟨haT, ⟨x, hxa, hx⟩⟩, rfl⟩)
        (hcanon_ball a (Finset.mem_filter.mpr ⟨haT, ⟨x, hxa, hx⟩⟩) ▸ hxa)
    · intro hx
      obtain ⟨a, ha_reps, hxa⟩ := Set.mem_iUnion₂.mp hx
      obtain ⟨b, hb_useful, rfl⟩ := Finset.mem_image.mp ha_reps
      exact hball_sub _ (hcanon_mem b hb_useful) (hcanon_ball b hb_useful ▸ hxa)
  have hdisjoint : ∀ a ∈ reps, ∀ b ∈ reps, a ≠ b →
      Disjoint (closedBall a r) (closedBall b r) := by
    intro a ha b hb hab
    rw [Set.disjoint_left]
    intro x hxa hxb
    apply hab
    obtain ⟨a', ha', rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    calc canon a' = canon (canon a') := (hcanon_idemp a' ha').symm
      _ = canon (canon b') := hcanon_consistent _ _
          (IsUltrametricDist.closedBall_eq_of_mem hxa ▸
           (IsUltrametricDist.closedBall_eq_of_mem hxb).symm)
      _ = canon b' := hcanon_idemp b' hb'
  have hmeas : μ (closedBall (0 : K) 1) = reps.card * μ (closedBall (0 : K) r) := by
    conv_lhs => rw [hcover]
    rw [measure_biUnion_finset (fun a ha b hb hab => hdisjoint a ha b hb hab) (fun a _ => by
      rw [show closedBall a r = a +ᵥ closedBall (0 : K) r from
        (vadd_closedBall_zero r a).symm]
      exact (IsUltrametricDist.isClopen_closedBall (0 : K) hr_ne).1.measurableSet.const_vadd _)]
    simp_rw [addHaar_closedBall_center]
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcard_nnnorm : (reps.card : NNReal) * ‖(g : K)‖₊ = 1 :=
    dvr_index_eq_nnnorm_inv K g hg reps hcover hdisjoint
  rw [hmeas, ← mul_assoc, ← ENNReal.coe_natCast, ← ENNReal.coe_mul,
    mul_comm ‖(g : K)‖₊ _, hcard_nnnorm, ENNReal.coe_one, one_mul]

noncomputable section
open MeasureTheory Measure TopologicalSpace Pointwise Filter Topology Metric

theorem distribHaarChar_eq_nnnorm_of_norm_lt_one
    (K : Type*) [NontriviallyNormedField K] [LocallyCompactSpace K] [IsUltrametricDist K]
    (g : Kˣ) (hg : ‖(g : K)‖ < 1) : distribHaarChar K g = ‖(g : K)‖₊ := by
  haveI : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  let μ : Measure K := addHaar
  have hS_pos : μ (closedBall (0 : K) 1) ≠ 0 :=
    ((IsUltrametricDist.isClopen_closedBall (0 : K) one_ne_zero).2.measure_pos μ
      ⟨0, mem_closedBall_self zero_le_one⟩).ne'
  have hS_fin : μ (closedBall (0 : K) 1) ≠ ⊤ :=
    (isCompact_closedBall 0 1).measure_lt_top.ne
  apply distribHaarChar_eq_of_measure_smul_eq_mul hS_pos hS_fin

  have hsmul : g • closedBall (0 : K) 1 = closedBall (0 : K) ‖(g : K)‖ := by
    have : g • closedBall (0 : K) 1 = (g : K) • closedBall (0 : K) 1 := by
      ext; simp [Units.smul_def]
    rw [this, units_smul_closedBall_zero_one g]
  rw [hsmul]

  exact haar_closedBall_eq_nnnorm_mul_of_norm_lt_one K μ g hg

theorem distribHaarChar_eq_nnnorm_dvr_helper
    (K : Type*) [NontriviallyNormedField K] [LocallyCompactSpace K] [IsUltrametricDist K]
    (g : Kˣ) (hg : ‖(g : K)‖ < 1) : distribHaarChar K g = ‖(g : K)‖₊ :=
  distribHaarChar_eq_nnnorm_of_norm_lt_one K g hg

theorem distribHaarChar_eq_nnnorm_ultrametric_axiom
    (K : Type*) [NontriviallyNormedField K] [LocallyCompactSpace K] [IsUltrametricDist K]
    (g : Kˣ) (hg : ‖(g : K)‖ ≤ 1) : distribHaarChar K g = ‖(g : K)‖₊ := by
  rcases hg.eq_or_lt with hg1 | hg_lt
  ·
    letI : MeasurableSpace K := borel K
    haveI : BorelSpace K := ⟨rfl⟩
    haveI : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
    let μ : Measure K := Measure.addHaar
    have hball_pos : μ (Metric.ball (0 : K) 1) ≠ 0 :=
      Metric.isOpen_ball.measure_ne_zero μ ⟨0, Metric.mem_ball_self one_pos⟩
    have hball_fin : μ (Metric.ball (0 : K) 1) ≠ ⊤ :=
      ne_top_of_le_ne_top (IsCompact.measure_lt_top (isCompact_closedBall 0 1)).ne
        (measure_mono Metric.ball_subset_closedBall)
    apply distribHaarChar_eq_of_measure_smul_eq_mul (μ := μ) (s := Metric.ball 0 1)
      hball_pos hball_fin
    have hsmul_eq : g • Metric.ball (0 : K) 1 = (g : K) • Metric.ball (0 : K) 1 := by
      ext; simp [Units.smul_def]
    rw [hsmul_eq, units_smul_ball_zero_one g]
    have hn : ‖(g : K)‖₊ = 1 := by ext; simp [hg1]
    rw [hg1, hn, ENNReal.coe_one, one_mul]
  ·
    exact distribHaarChar_eq_nnnorm_dvr_helper K g hg_lt

theorem distribHaarChar_eq_nnnorm_ultrametric
    (K : Type*) [NontriviallyNormedField K] [LocallyCompactSpace K] [IsUltrametricDist K]
    (g : Kˣ) : distribHaarChar K g = ‖(g : K)‖₊ := by
  by_cases hle : ‖(g : K)‖ ≤ 1
  · exact distribHaarChar_eq_nnnorm_ultrametric_axiom K g hle
  ·
    push Not at hle
    have hginv_le : ‖((g⁻¹ : Kˣ) : K)‖ ≤ 1 := by
      simp only [Units.val_inv_eq_inv_val, norm_inv]
      exact inv_le_one_of_one_le₀ hle.le
    have h_inv := distribHaarChar_eq_nnnorm_ultrametric_axiom K g⁻¹ hginv_le

    have h1 : distribHaarChar K g * distribHaarChar K g⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    rw [h_inv] at h1
    have hne : ‖((g⁻¹ : Kˣ) : K)‖₊ ≠ 0 := nnnorm_ne_zero_iff.mpr (Units.ne_zero g⁻¹)

    suffices distribHaarChar K g = (‖((g⁻¹ : Kˣ) : K)‖₊)⁻¹ by
      rw [this, Units.val_inv_eq_inv_val, nnnorm_inv, inv_inv]

    have : distribHaarChar K g * ‖((g⁻¹ : Kˣ) : K)‖₊ * (‖((g⁻¹ : Kˣ) : K)‖₊)⁻¹ =
           1 * (‖((g⁻¹ : Kˣ) : K)‖₊)⁻¹ := by rw [h1]
    rwa [mul_assoc, mul_inv_cancel₀ hne, mul_one, one_mul] at this

theorem distribHaarChar_eq_nnnorm_of_ultrametric
    (K : Type*) [NontriviallyNormedField K] [LocallyCompactSpace K] [IsUltrametricDist K]
    (g : Kˣ) (_hg : ‖(g : K)‖ ≤ 1) :
    distribHaarChar K g = ‖(g : K)‖₊ :=
  distribHaarChar_eq_nnnorm_ultrametric K g

lemma distribHaarChar_eq_nnnorm_of_norm_le_one_aux
    (K : Type*) [NontriviallyNormedField K] [LocallyCompactSpace K]
    [MeasurableSpace K] [BorelSpace K] [IsUltrametricDist K]
    (g : Kˣ) (hg : ‖(g : K)‖ ≤ 1) :
    distribHaarChar K g = ‖(g : K)‖₊ :=
  distribHaarChar_eq_nnnorm_of_ultrametric K g hg

theorem dvr_haar_char_eq_nnnorm_of_norm_le_one
    (K : Type*) [NontriviallyNormedField K] [LocallyCompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [IsUltrametricDist K]
    (a : K) (ha : a ≠ 0) (ha_le : ‖a‖ ≤ 1) :
    addEquivAddHaarChar (mulLeftContinuousAddEquiv (K := K) ha) = ‖a‖₊ := by
  rw [← distribHaarChar_eq_addEquivAddHaarChar_mulLeft ha]
  exact distribHaarChar_eq_nnnorm_of_norm_le_one_aux K (Units.mk0 a ha) ha_le

theorem addEquivAddHaarChar_mulLeft_eq_nnnorm
    (K : Type*) [NontriviallyNormedField K] [LocallyCompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [IsUltrametricDist K]
    (a : K) (ha : a ≠ 0) :
    addEquivAddHaarChar (mulLeftContinuousAddEquiv (K := K) ha) = ‖a‖₊ := by
  by_cases h : ‖a‖ ≤ 1
  ·
    exact dvr_haar_char_eq_nnnorm_of_norm_le_one K a ha h
  ·
    push Not at h
    have ha_inv : a⁻¹ ≠ 0 := inv_ne_zero ha
    have h_inv_le : ‖a⁻¹‖ ≤ 1 := by
      rw [norm_inv]; exact inv_le_one_of_one_le₀ h.le

    have h_inv := dvr_haar_char_eq_nnnorm_of_norm_le_one K a⁻¹ ha_inv h_inv_le

    have key : (mulLeftContinuousAddEquiv ha_inv).symm =
        mulLeftContinuousAddEquiv ha := by
      rw [mulLeftContinuousAddEquiv_symm]
      ext x; show (a⁻¹)⁻¹ * x = a * x; rw [inv_inv]

    rw [← key, addEquivAddHaarChar_symm, h_inv, nnnorm_inv, inv_inv]

theorem proposition_13_16_nonarchimedean
    (K : Type*) [NontriviallyNormedField K] [LocallyCompactSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [IsUltrametricDist K]
    (μ : Measure K) [μ.IsAddHaarMeasure] [μ.Regular]
    (a : K) (ha : a ≠ 0)
    (S : Set K) :
    μ (a • S) = (↑‖a‖₊ : ENNReal) * μ S := by
  rw [← addEquivAddHaarChar_mulLeft_eq_nnnorm K a ha]
  exact proposition_13_16_haar_scaling K μ a ha S

def IsNormalizedAbsVal
    {K : Type*} [Field K] [TopologicalSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [LocallyCompactSpace K] [T2Space K]
    (f : K → ℝ) : Prop :=
  (∀ a, 0 ≤ f a) ∧
  ∀ (μ : Measure K) [μ.IsAddHaarMeasure] (a : K) (S : Set K),
    μ ((a * ·) '' S) = ENNReal.ofReal (f a) * μ S

lemma isNormalizedAbsVal_unique
    {K : Type*} [Field K] [TopologicalSpace K]
    [MeasurableSpace K] [BorelSpace K]
    [LocallyCompactSpace K] [T2Space K]
    [IsTopologicalAddGroup K]
    (f g : K → ℝ) (hf : IsNormalizedAbsVal f) (hg : IsNormalizedAbsVal g) :
    f = g := by
  ext a
  obtain ⟨U, hU_compact, hU_nhd⟩ := exists_compact_mem_nhds (0 : K)
  set μ : Measure K := addHaar with hμ_def
  have hμ : μ.IsAddHaarMeasure := inferInstance
  have hU_pos : μ U ≠ 0 := ne_of_gt (measure_pos_of_mem_nhds μ hU_nhd)
  have hU_fin : μ U ≠ ⊤ := ne_of_lt hU_compact.measure_lt_top
  have h1 := @hf.2 μ hμ a U
  have h2 := @hg.2 μ hμ a U
  rw [h1] at h2
  have h3 : ENNReal.ofReal (f a) = ENNReal.ofReal (g a) :=
    (ENNReal.mul_left_inj hU_pos hU_fin).mp h2
  exact (ENNReal.ofReal_eq_ofReal_iff (hf.1 a) (hg.1 a)).mp h3

theorem haar_scaling_det
    (K_v : Type*) [Field K_v] [TopologicalSpace K_v]
      [MeasurableSpace K_v] [BorelSpace K_v]
      [LocallyCompactSpace K_v] [T2Space K_v]
    (L_w : Type*) [Field L_w] [TopologicalSpace L_w]
      [MeasurableSpace L_w] [BorelSpace L_w]
      [LocallyCompactSpace L_w] [T2Space L_w]
      [IsTopologicalAddGroup L_w]
    [Algebra K_v L_w] [FiniteDimensional K_v L_w]
    (normAbsVal_v : K_v → ℝ) (hv : IsNormalizedAbsVal normAbsVal_v)
    (μ : Measure L_w) [μ.IsAddHaarMeasure]
    (f : L_w →ₗ[K_v] L_w) (S : Set L_w) :
    μ (f '' S) = ENNReal.ofReal (normAbsVal_v (LinearMap.det f)) * μ S := by sorry

theorem haar_scaling_algebra_norm
    (K_v : Type*) [Field K_v] [TopologicalSpace K_v]
      [MeasurableSpace K_v] [BorelSpace K_v]
      [LocallyCompactSpace K_v] [T2Space K_v]
    (L_w : Type*) [Field L_w] [TopologicalSpace L_w]
      [MeasurableSpace L_w] [BorelSpace L_w]
      [LocallyCompactSpace L_w] [T2Space L_w]
      [IsTopologicalAddGroup L_w]
    [Algebra K_v L_w] [FiniteDimensional K_v L_w]
    (normAbsVal_v : K_v → ℝ) (hv : IsNormalizedAbsVal normAbsVal_v)
    (μ : Measure L_w) [μ.IsAddHaarMeasure] (a : L_w) (S : Set L_w) :
    μ ((a * ·) '' S) = ENNReal.ofReal (normAbsVal_v ((Algebra.norm K_v) a)) * μ S := by

  have h_eq : (a * ·) = ⇑((Algebra.lmul K_v L_w) a) := by
    ext x; rfl

  rw [h_eq, haar_scaling_det K_v L_w normAbsVal_v hv μ ((Algebra.lmul K_v L_w) a) S]

  rw [Algebra.norm_apply]

theorem norm_composition_isNormalizedAbsVal
    (K_v : Type*) [Field K_v] [TopologicalSpace K_v]
      [MeasurableSpace K_v] [BorelSpace K_v]
      [LocallyCompactSpace K_v] [T2Space K_v]
    (L_w : Type*) [Field L_w] [TopologicalSpace L_w]
      [MeasurableSpace L_w] [BorelSpace L_w]
      [LocallyCompactSpace L_w] [T2Space L_w]
      [IsTopologicalAddGroup L_w]
    [Algebra K_v L_w] [FiniteDimensional K_v L_w]
    (normAbsVal_v : K_v → ℝ) (hv : IsNormalizedAbsVal normAbsVal_v) :
    IsNormalizedAbsVal (fun x : L_w => normAbsVal_v ((Algebra.norm K_v) x)) := by
  exact ⟨fun a => hv.1 _, fun μ _ a S =>
    haar_scaling_algebra_norm K_v L_w normAbsVal_v hv μ a S⟩

theorem lemma_13_19
    (K_v : Type*) [Field K_v] [TopologicalSpace K_v]
      [MeasurableSpace K_v] [BorelSpace K_v]
      [LocallyCompactSpace K_v] [T2Space K_v]
    (L_w : Type*) [Field L_w] [TopologicalSpace L_w]
      [MeasurableSpace L_w] [BorelSpace L_w]
      [LocallyCompactSpace L_w] [T2Space L_w]
      [IsTopologicalAddGroup L_w]
    [Algebra K_v L_w] [FiniteDimensional K_v L_w]
    (normAbsVal_v : K_v → ℝ) (hv : IsNormalizedAbsVal normAbsVal_v)
    (normAbsVal_w : L_w → ℝ) (hw : IsNormalizedAbsVal normAbsVal_w)
    (x : L_w) :
    normAbsVal_w x = normAbsVal_v ((Algebra.norm K_v) x) := by


  have h_norm_comp := norm_composition_isNormalizedAbsVal K_v L_w normAbsVal_v hv


  have h_eq := isNormalizedAbsVal_unique
    (fun x => normAbsVal_w x) (fun x => normAbsVal_v ((Algebra.norm K_v) x))
    hw h_norm_comp
  exact congr_fun h_eq x

class IsGlobalField (K : Type*) [Field K] where
  PlaceType : Type*
  place_nonempty : Nonempty PlaceType
  Completion : PlaceType → Type*
  completionField : ∀ v, Field (Completion v)
  completionTopologicalSpace : ∀ v, TopologicalSpace (Completion v)
  completionLocallyCompact : ∀ v,
    @LocallyCompactSpace (Completion v) (completionTopologicalSpace v)
  completionNontrivial : ∀ v, @Nontrivial (Completion v)
  absVal : PlaceType → AbsoluteValue K ℝ
  exponent : PlaceType → ℝ
  exponent_pos : ∀ v, 0 < exponent v
  normAbsVal : PlaceType → K → ℝ
  normAbsVal_nonneg : ∀ v x, 0 ≤ normAbsVal v x
  normAbsVal_eq : ∀ v x, normAbsVal v x = (absVal v x) ^ (exponent v)
  normAbsVal_eq_one_of_finite : ∀ x, x ≠ 0 →
    Set.Finite {v | normAbsVal v x ≠ 1}
  product_formula : ∀ x, x ≠ 0 → ∏ᶠ v, normAbsVal v x = 1

theorem theorem_13_21_product_formula_global (K : Type*) [Field K] [NumberField K]
    {x : K} (hx : x ≠ 0) :
    (∏ w : NumberField.InfinitePlace K, (w x) ^ w.mult) *
    ∏ᶠ w : NumberField.FinitePlace K, (w x) = 1 :=
  NumberField.prod_abs_eq_one hx

theorem artin_whaples_classification (K : Type*) [Field K] [IsGlobalField K] :
    (∃ (_ : Algebra ℚ K), FiniteDimensional ℚ K) ∨
    (∃ (Fq : Type*) (_ : Field Fq) (_ : Fintype Fq) (_ : Algebra (RatFunc Fq) K),
      FiniteDimensional (RatFunc Fq) K) := by sorry

end
