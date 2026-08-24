/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.DifferentialAnalysis.code.WavefrontSet
import Atlas.DifferentialAnalysis.code.ConeSupportCorollary

noncomputable section

open scoped SchwartzMap

namespace WavefrontSet

variable {n : ℕ}


/-- If the conic singular support set `Css u` of a tempered distribution `u` is empty, then its
sphere component `ConicSingularSupportSphere u` is also empty. -/
lemma ConicSingularSupportSphere_empty_of_Css_empty {n : ℕ}
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (h : Css u = ∅) :
    ConeSupport.ConicSingularSupportSphere u = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro w hw
  have hp_norm : ‖w.val‖ = 1 := by
    have := w.property
    rwa [Metric.mem_sphere, dist_zero_right] at this
  have hp_le : ‖w.val‖ ≤ 1 := le_of_eq hp_norm
  let p : ClosedBall n := ⟨w.val, hp_le⟩
  have hp_mem : p ∈ Css u := by
    show (if h : ‖p.val‖ = 1 then _ else _)
    rw [dif_pos hp_norm]
    convert hw using 1
  exact (h ▸ hp_mem : p ∈ (∅ : Set (ClosedBall n)))

/-- If the conic singular support set `Css u` of a tempered distribution `u` is empty, then its
ordinary singular support is also empty. -/
lemma singularSupport_empty_of_Css_empty {n : ℕ}
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (h : Css u = ∅) :
    ConeSupport.singularSupport u = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have h1x_pos : (0 : ℝ) < 1 + ‖x‖ := by positivity
  have h1x_ne : (1 + ‖x‖ : ℝ) ≠ 0 := ne_of_gt h1x_pos
  set c := (1 + ‖x‖)⁻¹ with hc_def
  have hc_pos : 0 < c := inv_pos.mpr h1x_pos
  have hc_norm : ‖c • x‖ = ‖x‖ / (1 + ‖x‖) := by
    rw [norm_smul, Real.norm_of_nonneg hc_pos.le, hc_def, inv_mul_eq_div]
  have hc_lt : ‖c • x‖ < 1 := by
    rw [hc_norm]
    rw [div_lt_one h1x_pos, lt_add_iff_pos_left]
    exact one_pos
  have hc_le : ‖c • x‖ ≤ 1 := le_of_lt hc_lt
  let p : ClosedBall n := ⟨c • x, hc_le⟩
  have hp_ne : ‖p.val‖ ≠ 1 := ne_of_lt hc_lt
  have hto : p.toEuclidean hc_lt = x := by
    simp only [ClosedBall.toEuclidean, p]
    rw [hc_norm]
    have h_factor : (1 : ℝ) - ‖x‖ / (1 + ‖x‖) = 1 / (1 + ‖x‖) := by
      field_simp
      ring
    rw [h_factor, one_div, inv_inv, smul_smul]
    rw [hc_def, mul_inv_cancel₀ h1x_ne, one_smul]
  have hp_mem : p ∈ Css u := by
    show (if hh : ‖p.val‖ = 1 then _ else _)
    rw [dif_neg hp_ne]
    convert hx using 1
  exact (h ▸ hp_mem : p ∈ (∅ : Set (ClosedBall n)))

/-- If the conic singular support set `Css u` of a tempered distribution `u` is empty, then its
cone singular support (the union of singular support and conic sphere part) is also empty. -/
lemma coneSingularSupport_empty_of_Css_empty {n : ℕ}
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (h : Css u = ∅) :
    ConeSupport.coneSingularSupport u = ∅ := by
  simp only [ConeSupport.coneSingularSupport, Set.union_empty_iff, Set.image_eq_empty]
  exact ⟨singularSupport_empty_of_Css_empty u h,
    ConicSingularSupportSphere_empty_of_Css_empty u h⟩

/-- When the conic singular support `Css u` of a tempered distribution is empty, produce a Schwartz
function whose Schwartz embedding equals `u`. -/
def toSchwartzOfEmptyCss {n : ℕ}
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (h : Css u = ∅) : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ :=
  ((ConeSupport.coneSingularSupport_eq_empty_iff u).mp
    (coneSingularSupport_empty_of_Css_empty u h)).choose

/-- Predicate that `ψ₁` acts as a conic cutoff separating conic singular supports `K₁` and `K₂`:
multiplying by `ψ₁` (resp. `1 - ψ₁`) kills the conic singular support of any distribution whose
`Css` lies in `K₂` (resp. `K₁`). -/
structure IsConicCutoffForDisjointCss (K₁ K₂ : Set (ClosedBall n))
    (ψ₁ : EuclideanSpace ℝ (Fin n) → ℂ) : Prop where
  schwartz_of_mul :
    ∀ u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ), Css u₂ ⊆ K₂ →
      Css (TemperedDistribution.smulLeftCLM ℂ ψ₁ u₂) = ∅
  schwartz_of_compl_mul :
    ∀ u₁ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ), Css u₁ ⊆ K₁ →
      Css (TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁) u₁) = ∅

/-- Pairing of distributions `u₁, u₂` with disjoint conic singular supports, defined via a
specified conic cutoff `ψ₁`: applies `u₁` to the Schwartz representative of `ψ₁ · u₂` and `u₂` to
the Schwartz representative of `(1 - ψ₁) · u₁`, then sums. -/
def cssPairingWith {K₁ K₂ : Set (ClosedBall n)}
    (ψ₁ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hψ : IsConicCutoffForDisjointCss K₁ K₂ ψ₁)
    (u₁ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (h₁ : Css u₁ ⊆ K₁)
    (u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (h₂ : Css u₂ ⊆ K₂) : ℂ :=
  u₁ (toSchwartzOfEmptyCss _ (hψ.schwartz_of_mul u₂ h₂)) +
  u₂ (toSchwartzOfEmptyCss _ (hψ.schwartz_of_compl_mul u₁ h₁))

/-- The Schwartz embedding of `toSchwartzOfEmptyCss u h` recovers the original tempered
distribution `u`. -/
lemma schwEmbed_toSchwartzOfEmptyCss {n : ℕ}
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (h : Css u = ∅) :
    ConeSupport.schwEmbed (toSchwartzOfEmptyCss u h) = u :=
  ((ConeSupport.coneSingularSupport_eq_empty_iff u).mp
    (coneSingularSupport_empty_of_Css_empty u h)).choose_spec


/-- Partition of unity identity: for any temperate-growth `φ` and tempered distribution `u`, we have
`φ · u + (1 - φ) · u = u`. -/
theorem smul_partition
    {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hφ : φ.HasTemperateGrowth)
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) :
    TemperedDistribution.smulLeftCLM ℂ φ u +
      TemperedDistribution.smulLeftCLM ℂ (1 - φ) u = u := by
  have h1 : (1 : EuclideanSpace ℝ (Fin n) → ℂ).HasTemperateGrowth :=
    Function.HasTemperateGrowth.const 1
  have h1φ : (1 - φ).HasTemperateGrowth := h1.sub hφ
  have hadd := TemperedDistribution.smulLeftCLM_add (F := ℂ) hφ h1φ
  have hone : φ + (1 - φ) = (1 : EuclideanSpace ℝ (Fin n) → ℂ) := by
    ext x; simp [Pi.add_apply, Pi.sub_apply]
  rw [hone] at hadd
  have key := congr_arg (· u) hadd.symm
  simp only [ContinuousLinearMap.add_apply] at key
  rw [key]
  have h_one_eq : (1 : EuclideanSpace ℝ (Fin n) → ℂ) = fun _ => (1 : ℂ) := rfl
  rw [h_one_eq, TemperedDistribution.smulLeftCLM_const, one_smul]


/-- The Schwartz embedding `schwEmbed : 𝓢(ℝⁿ, ℂ) → 𝓢'(ℝⁿ, ℂ)` is injective. -/
theorem schwEmbed_injective
    {n : ℕ}
    {f g : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ}
    (h : ConeSupport.schwEmbed f = ConeSupport.schwEmbed g) :
    f = g := by
  open MeasureTheory in
  rw [← sub_eq_zero]
  have hfg : ConeSupport.schwEmbed (f - g) = 0 := by
    simp only [map_sub, h, sub_self]
  apply SchwartzMap.injective_toLp (F := ℂ) (E := EuclideanSpace ℝ (Fin n)) 2 (μ := volume)
  have hLp_eq : Lp.toTemperedDistribution ((f - g).toLp 2 volume) =
    (0 : TemperedDistribution (EuclideanSpace ℝ (Fin n)) ℂ) := by
    rw [Lp.toTemperedDistribution_toLp_eq]
    exact hfg
  have hinj := Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := ℂ) (E := EuclideanSpace ℝ (Fin n)) (μ := volume) (p := 2)
  rw [LinearMap.ker_eq_bot'] at hinj
  exact hinj _ hLp_eq


/-- If a temperate-growth function `χ` agrees outside a ball with smooth homogeneous functions
vanishing at every direction of the conic singular support of `u`, then the conic singular support
of `χ · u` is empty. -/
theorem css_empty_of_conicSupport_disjoint
    {n : ℕ} (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (χ : EuclideanSpace ℝ (Fin n) → ℂ) (hχ : χ.HasTemperateGrowth)
    (K : Set (ClosedBall n)) (hK : Css u ⊆ K)
    (hdisjoint : ∀ ω : ConeSupport.Sphere n, ω ∈ ConeSupport.ConicSingularSupportSphere u →
      ∃ (ψ : EuclideanSpace ℝ (Fin n) → ℂ)
        (hψ_hom : ∀ (a : ℝ), 0 < a → ∀ (x : EuclideanSpace ℝ (Fin n)), x ≠ 0 → ψ (a • x) = ψ x)
        (R : ℝ) (_ : 0 < R),
        (∀ x, R < ‖x‖ → χ x = ψ x) ∧ ψ (↑ω) = 0) :
    Css (TemperedDistribution.smulLeftCLM ℂ χ u) = ∅ := by


  by_cases hne : Set.Nonempty (ConeSupport.ConicSingularSupportSphere u)
  ·
    obtain ⟨ω₀, hω₀⟩ := hne
    obtain ⟨ψ₀, hψ₀_hom, R₀, hR₀, hχ_eq₀, hψ₀_zero⟩ := hdisjoint ω₀ hω₀

    have hψ₀_disjoint : ∀ ω : ConeSupport.Sphere n,
        ω ∈ ConeSupport.ConicSingularSupportSphere u → ψ₀ (↑ω) = 0 := by
      intro ω₁ hω₁
      obtain ⟨ψ₁, hψ₁_hom, R₁, hR₁, hχ_eq₁, hψ₁_zero⟩ := hdisjoint ω₁ hω₁

      have hψ_agree : ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 → ψ₀ x = ψ₁ x := by
        intro x hx

        set a := (max R₀ R₁ + 1) / ‖x‖ with ha_def
        have hx_norm_pos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
        have ha_pos : (0 : ℝ) < a := by
          apply div_pos
          · linarith [le_max_left R₀ R₁]
          · exact hx_norm_pos
        have hax_norm : ‖a • x‖ = a * ‖x‖ := by
          rw [norm_smul, Real.norm_of_nonneg ha_pos.le]
        have hax_gt_R₀ : R₀ < ‖a • x‖ := by
          rw [hax_norm, ha_def, div_mul_cancel₀]
          · linarith [le_max_left R₀ R₁]
          · exact ne_of_gt hx_norm_pos
        have hax_gt_R₁ : R₁ < ‖a • x‖ := by
          rw [hax_norm, ha_def, div_mul_cancel₀]
          · linarith [le_max_right R₀ R₁]
          · exact ne_of_gt hx_norm_pos
        calc ψ₀ x = ψ₀ (a • x) := (hψ₀_hom a ha_pos x hx).symm
          _ = χ (a • x) := (hχ_eq₀ (a • x) hax_gt_R₀).symm
          _ = ψ₁ (a • x) := hχ_eq₁ (a • x) hax_gt_R₁
          _ = ψ₁ x := hψ₁_hom a ha_pos x hx

      have hω₁_ne : (↑ω₁ : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
        intro h_eq
        have := ω₁.property
        rw [Metric.mem_sphere, dist_zero_right] at this
        rw [h_eq, norm_zero] at this
        linarith
      rw [hψ_agree (↑ω₁) hω₁_ne]
      exact hψ₁_zero

    have hχ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := by
      exact_mod_cast hχ.1
    obtain ⟨f, hf⟩ := ConeSupport.css_disjoint_implies_schwartz_general u χ hχ_smooth
      R₀ hR₀ ψ₀ hψ₀_hom hχ_eq₀ hψ₀_disjoint

    rw [hf]
    have h_cone : ConeSupport.coneSingularSupport (ConeSupport.schwEmbed f) = ∅ :=
      (ConeSupport.coneSingularSupport_eq_empty_iff _).mpr ⟨f, rfl⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro p hp
    simp only [Css, Set.mem_setOf_eq] at hp
    simp only [ConeSupport.coneSingularSupport, Set.union_empty_iff,
      Set.image_eq_empty] at h_cone
    obtain ⟨h_ss, h_csss⟩ := h_cone
    split_ifs at hp with hh
    · rw [Set.eq_empty_iff_forall_notMem] at h_csss
      exact h_csss _ hp
    · rw [Set.eq_empty_iff_forall_notMem] at h_ss
      exact h_ss _ hp
  ·
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have hχ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ := by
      exact_mod_cast hχ.1

    have hcss_decomp := ConeSupport.hasEmptyConicSingularSupportSphere_of_eq_empty u hne
    obtain ⟨⟨f₀, g, hg_compact, hsum⟩⟩ := hcss_decomp.hasDecomp
    have hχ_u_eq : TemperedDistribution.smulLeftCLM ℂ χ u =
        TemperedDistribution.smulLeftCLM ℂ χ (ConeSupport.schwEmbed f₀) +
        TemperedDistribution.smulLeftCLM ℂ χ g := by
      rw [hsum, map_add]
    have hχf₀ : TemperedDistribution.smulLeftCLM ℂ χ (ConeSupport.schwEmbed f₀) =
        (ConeSupport.schwEmbed (SchwartzMap.smulLeftCLM ℂ χ f₀)) :=
      ConeSupport.smulLeftCLM_schwartz_embed hχ f₀


    obtain ⟨K_g, hK_g_compact, hK_g_supp⟩ := hg_compact

    obtain ⟨R_g, hR_g⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hK_g_compact.isBounded
    let R_g' := max R_g 0
    have hR_g'_pos : 0 < R_g' + 1 := by positivity
    let bump_g : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
      { rIn := R_g' + 1, rOut := R_g' + 2, rIn_pos := hR_g'_pos, rIn_lt_rOut := by linarith }
    let θ : EuclideanSpace ℝ (Fin n) → ℂ := Complex.ofRealCLM ∘ bump_g
    have hθ_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ :=
      Complex.ofRealCLM.contDiff.comp bump_g.contDiff
    have hθ_compact : HasCompactSupport θ :=
      bump_g.hasCompactSupport.comp_left (map_zero _)
    have hθ_tg : Function.HasTemperateGrowth θ := hθ_compact.hasTemperateGrowth hθ_smooth

    obtain ⟨f_g', hf_g'⟩ := ConeSupport.smulLeftCLM_schwartz_of_compactSmooth g θ
      hθ_smooth hθ_compact hθ_tg

    have hθg_eq_g : TemperedDistribution.smulLeftCLM ℂ θ g = g := by
      apply ConeSupport.smulLeftCLM_eq_self_of_one_on_support g K_g hK_g_compact hK_g_supp θ
        hθ_smooth hθ_compact
      · intro x hx
        simp only [θ, Function.comp, Complex.ofRealCLM_apply]
        have hx_in : x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) bump_g.rIn := by
          apply Metric.closedBall_subset_closedBall (show R_g ≤ R_g' + 1 by
            exact le_add_of_le_of_nonneg (le_max_left R_g 0) one_pos.le)
          exact hR_g hx
        rw [bump_g.one_of_mem_closedBall hx_in]
        simp [Complex.ofReal_one]
      · exact hθ_tg

    have hg_schwartz : g = ConeSupport.schwEmbed f_g' := by
      rw [← hθg_eq_g, hf_g']

    have hχg_eq : TemperedDistribution.smulLeftCLM ℂ χ g =
        ConeSupport.schwEmbed (SchwartzMap.smulLeftCLM ℂ χ f_g') := by
      rw [hg_schwartz]
      exact ConeSupport.smulLeftCLM_schwartz_embed hχ f_g'

    set f_g := SchwartzMap.smulLeftCLM ℂ χ f_g'
    have hf_g : TemperedDistribution.smulLeftCLM ℂ χ g = ConeSupport.schwEmbed f_g := hχg_eq

    have hχ_u_schwartz : TemperedDistribution.smulLeftCLM ℂ χ u =
        ConeSupport.schwEmbed (SchwartzMap.smulLeftCLM ℂ χ f₀ + f_g) := by
      rw [hχ_u_eq, hχf₀, hf_g, map_add]
    rw [hχ_u_schwartz]

    have h_cone : ConeSupport.coneSingularSupport
        (ConeSupport.schwEmbed (SchwartzMap.smulLeftCLM ℂ χ f₀ + f_g)) = ∅ :=
      (ConeSupport.coneSingularSupport_eq_empty_iff _).mpr
        ⟨SchwartzMap.smulLeftCLM ℂ χ f₀ + f_g, rfl⟩
    rw [Set.eq_empty_iff_forall_notMem]
    intro p hp
    simp only [Css, Set.mem_setOf_eq] at hp
    simp only [ConeSupport.coneSingularSupport, Set.union_empty_iff,
      Set.image_eq_empty] at h_cone
    obtain ⟨h_ss, h_csss⟩ := h_cone
    split_ifs at hp with hh
    · rw [Set.eq_empty_iff_forall_notMem] at h_csss
      exact h_csss _ hp
    · rw [Set.eq_empty_iff_forall_notMem] at h_ss
      exact h_ss _ hp


/-- Multiplication by `χ` fixes the Schwartz-valued differences `(ψ₁ - ψ₁') · u₂` and
`((1 - ψ₁') - (1 - ψ₁)) · u₁` arising from a pair of conic cutoffs for disjoint conic singular
supports. -/
theorem smulLeftCLM_fixes_schwartz_diff
    {n : ℕ} (χ : EuclideanSpace ℝ (Fin n) → ℂ) (hχ : χ.HasTemperateGrowth)
    {K₁ K₂ : Set (ClosedBall n)}
    {ψ₁ ψ₁' : EuclideanSpace ℝ (Fin n) → ℂ}
    (hψ : IsConicCutoffForDisjointCss K₁ K₂ ψ₁)
    (hψ' : IsConicCutoffForDisjointCss K₁ K₂ ψ₁')
    (u₁ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (h₁ : Css u₁ ⊆ K₁)
    (u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (h₂ : Css u₂ ⊆ K₂)
    (hχu₁ : Css (TemperedDistribution.smulLeftCLM ℂ χ u₁) = ∅)
    (hχu₂ : Css (TemperedDistribution.smulLeftCLM ℂ χ u₂) = ∅) :
    TemperedDistribution.smulLeftCLM ℂ χ
      (TemperedDistribution.smulLeftCLM ℂ ψ₁ u₂ -
       TemperedDistribution.smulLeftCLM ℂ ψ₁' u₂) =
      TemperedDistribution.smulLeftCLM ℂ ψ₁ u₂ -
       TemperedDistribution.smulLeftCLM ℂ ψ₁' u₂ ∧
    TemperedDistribution.smulLeftCLM ℂ χ
      (TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁') u₁ -
       TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁) u₁) =
      TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁') u₁ -
       TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁) u₁ := by sorry


/-- If two distributions `u₁, u₂` have conic singular supports contained in disjoint sets
`K₁, K₂`, then their conic singular support spheres are also disjoint. -/
theorem css_implies_sphere_disjoint
    {n : ℕ} {K₁ K₂ : Set (ClosedBall n)} (hK : Disjoint K₁ K₂)
    {u₁ u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    (h₁ : Css u₁ ⊆ K₁) (h₂ : Css u₂ ⊆ K₂) :
    Disjoint (ConeSupport.ConicSingularSupportSphere u₁)
             (ConeSupport.ConicSingularSupportSphere u₂) := by sorry


/-- Existence of a temperate-growth cutoff `χ` such that `χ · u₁` and `χ · u₂` both have empty
conic singular support and `χ` fixes the relevant Schwartz-valued differences. -/
theorem exists_chi_css_both_empty_with_fixing
    {n : ℕ} {K₁ K₂ : Set (ClosedBall n)}
    (hK : Disjoint K₁ K₂)
    {ψ₁ ψ₁' : EuclideanSpace ℝ (Fin n) → ℂ}
    (hψ : IsConicCutoffForDisjointCss K₁ K₂ ψ₁)
    (hψ' : IsConicCutoffForDisjointCss K₁ K₂ ψ₁')
    (u₁ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (h₁ : Css u₁ ⊆ K₁)
    (u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (h₂ : Css u₂ ⊆ K₂) :
    ∃ (χ : EuclideanSpace ℝ (Fin n) → ℂ),
      χ.HasTemperateGrowth ∧
      Css (TemperedDistribution.smulLeftCLM ℂ χ u₁) = ∅ ∧
      Css (TemperedDistribution.smulLeftCLM ℂ χ u₂) = ∅ ∧
      TemperedDistribution.smulLeftCLM ℂ χ
        (TemperedDistribution.smulLeftCLM ℂ ψ₁ u₂ -
         TemperedDistribution.smulLeftCLM ℂ ψ₁' u₂) =
        TemperedDistribution.smulLeftCLM ℂ ψ₁ u₂ -
         TemperedDistribution.smulLeftCLM ℂ ψ₁' u₂ ∧
      TemperedDistribution.smulLeftCLM ℂ χ
        (TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁') u₁ -
         TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁) u₁) =
        TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁') u₁ -
         TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁) u₁ := by


  have hdisj_sphere : Disjoint (ConeSupport.ConicSingularSupportSphere u₁)
      (ConeSupport.ConicSingularSupportSphere u₂) :=
    css_implies_sphere_disjoint hK h₁ h₂

  obtain ⟨_f₁, _f₂, g, hg_smooth, hg_u₂, h1g_u₁⟩ :=
    ConeSupport.exists_separating_schwartz_pair u₁ u₂ hdisj_sphere


  obtain ⟨ψ_sep, hψ_sep_hom, hψ_sep_one, _⟩ :=
    ConeSupport.exists_smooth_homogeneous_separator
      (ConeSupport.ConicSingularSupportSphere u₁ ∪ ConeSupport.ConicSingularSupportSphere u₂)
      ∅ (Set.disjoint_empty _)


  set χ_hom := (1 : EuclideanSpace ℝ (Fin n) → ℂ) - ψ_sep
  have hχ_hom_hom : ∀ (a : ℝ), 0 < a → ∀ (x : EuclideanSpace ℝ (Fin n)), x ≠ 0 →
      χ_hom (a • x) = χ_hom x := by
    intro a ha x hx
    simp only [χ_hom, Pi.sub_apply, Pi.one_apply, hψ_sep_hom a ha x hx]

  obtain ⟨χ, hχ_smooth, R, _R', hR, _hR', hχ_supp, hχ_eq⟩ :=
    ConeSupport.exists_conic_cutoff_from_homogeneous χ_hom hχ_hom_hom (by sorry)

  have hχ_tg : χ.HasTemperateGrowth := by sorry


  have hχu₁ : Css (TemperedDistribution.smulLeftCLM ℂ χ u₁) = ∅ := by
    apply css_empty_of_conicSupport_disjoint u₁ χ hχ_tg K₁ h₁
    intro ω hω
    exact ⟨χ_hom, hχ_hom_hom, _R', (by linarith [_hR'] : (0 : ℝ) < _R'), hχ_eq, by
      have := hψ_sep_one ω (Set.mem_union_left _ hω)
      simp [χ_hom, Pi.sub_apply, Pi.one_apply, this]⟩
  have hχu₂ : Css (TemperedDistribution.smulLeftCLM ℂ χ u₂) = ∅ := by
    apply css_empty_of_conicSupport_disjoint u₂ χ hχ_tg K₂ h₂
    intro ω hω
    exact ⟨χ_hom, hχ_hom_hom, _R', (by linarith [_hR'] : (0 : ℝ) < _R'), hχ_eq, by
      have := hψ_sep_one ω (Set.mem_union_right _ hω)
      simp [χ_hom, Pi.sub_apply, Pi.one_apply, this]⟩

  have hfix := smulLeftCLM_fixes_schwartz_diff χ hχ_tg hψ hψ' u₁ h₁ u₂ h₂ hχu₁ hχu₂
  exact ⟨χ, hχ_tg, hχu₁, hχu₂, hfix.1, hfix.2⟩

/-- Existence of a temperate-growth cutoff `χ` making the conic singular supports of `χ · u₁` and
`χ · u₂` empty while fixing the Schwartz differences associated to the cutoffs `ψ₁` and `ψ₁'`. -/
theorem exists_chi_css_empty
    {n : ℕ}
    {K₁ K₂ : Set (ClosedBall n)}
    (hK : Disjoint K₁ K₂)
    (hK₁_closed : IsClosed K₁) (hK₂_closed : IsClosed K₂)
    {ψ₁ ψ₁' : EuclideanSpace ℝ (Fin n) → ℂ}
    (hψ : IsConicCutoffForDisjointCss K₁ K₂ ψ₁)
    (hψ' : IsConicCutoffForDisjointCss K₁ K₂ ψ₁')
    (u₁ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (h₁ : Css u₁ ⊆ K₁)
    (u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (h₂ : Css u₂ ⊆ K₂) :
    ∃ (χ : EuclideanSpace ℝ (Fin n) → ℂ),
      χ.HasTemperateGrowth ∧
      Css (TemperedDistribution.smulLeftCLM ℂ χ u₁) = ∅ ∧
      Css (TemperedDistribution.smulLeftCLM ℂ χ u₂) = ∅ ∧

      TemperedDistribution.smulLeftCLM ℂ χ
        (TemperedDistribution.smulLeftCLM ℂ ψ₁ u₂ -
         TemperedDistribution.smulLeftCLM ℂ ψ₁' u₂) =
        TemperedDistribution.smulLeftCLM ℂ ψ₁ u₂ -
         TemperedDistribution.smulLeftCLM ℂ ψ₁' u₂ ∧

      TemperedDistribution.smulLeftCLM ℂ χ
        (TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁') u₁ -
         TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁) u₁) =
        TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁') u₁ -
         TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁) u₁ :=
  exists_chi_css_both_empty_with_fixing hK hψ hψ' u₁ h₁ u₂ h₂


/-- Given Schwartz representatives for `χ · u₁`, `χ · u₂` and Schwartz functions `f, g` with
prescribed embeddings (and fixed by `χ`-multiplication), the pairings `u₁ f` and `u₂ g` agree. -/
theorem schwEmbed_chi_cross_integral
    {n : ℕ} {χ ψ₁ ψ₁' : EuclideanSpace ℝ (Fin n) → ℂ}
    {u₁ u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    (c₁ c₂ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
    (hc₁ : ConeSupport.schwEmbed c₁ = TemperedDistribution.smulLeftCLM ℂ χ u₁)
    (hc₂ : ConeSupport.schwEmbed c₂ = TemperedDistribution.smulLeftCLM ℂ χ u₂)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
    (hf : ConeSupport.schwEmbed f =
            TemperedDistribution.smulLeftCLM ℂ ψ₁ u₂ -
              TemperedDistribution.smulLeftCLM ℂ ψ₁' u₂)
    (hchif : SchwartzMap.smulLeftCLM ℂ χ f = f)
    (g : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
    (hg : ConeSupport.schwEmbed g =
            TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁') u₁ -
              TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁) u₁)
    (hchig : SchwartzMap.smulLeftCLM ℂ χ g = g) :
    u₁ f = u₂ g := by sorry

/-- Cross-pairing identity: under the empty-`Css` and fixing hypotheses on `χ`, the pairings of
the Schwartz representatives `c₁, c₂` with the Schwartz functions `f, g` corresponding to the two
cutoffs coincide. -/
theorem chi_cross_pairing
    {n : ℕ}
    {χ ψ₁ ψ₁' : EuclideanSpace ℝ (Fin n) → ℂ}
    {u₁ u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
    (hχu₁ : Css (TemperedDistribution.smulLeftCLM ℂ χ u₁) = ∅)
    (hχu₂ : Css (TemperedDistribution.smulLeftCLM ℂ χ u₂) = ∅)
    (hχ_fix_f : TemperedDistribution.smulLeftCLM ℂ χ
        (TemperedDistribution.smulLeftCLM ℂ ψ₁ u₂ -
         TemperedDistribution.smulLeftCLM ℂ ψ₁' u₂) =
        TemperedDistribution.smulLeftCLM ℂ ψ₁ u₂ -
         TemperedDistribution.smulLeftCLM ℂ ψ₁' u₂)
    (hχ_fix_g : TemperedDistribution.smulLeftCLM ℂ χ
        (TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁') u₁ -
         TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁) u₁) =
        TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁') u₁ -
         TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁) u₁)
    (c₁ c₂ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
    (hc₁ : ConeSupport.schwEmbed c₁ = TemperedDistribution.smulLeftCLM ℂ χ u₁)
    (hc₂ : ConeSupport.schwEmbed c₂ = TemperedDistribution.smulLeftCLM ℂ χ u₂)
    (f g : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ)
    (hf : ConeSupport.schwEmbed f =
            TemperedDistribution.smulLeftCLM ℂ ψ₁ u₂ -
              TemperedDistribution.smulLeftCLM ℂ ψ₁' u₂)
    (hg : ConeSupport.schwEmbed g =
            TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁') u₁ -
              TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁) u₁) :
    (ConeSupport.schwEmbed c₁) f = (ConeSupport.schwEmbed c₂) g := by

  have hchif : SchwartzMap.smulLeftCLM ℂ χ f = f := by
    apply schwEmbed_injective
    rw [← ConeSupport.smulLeftCLM_schwEmbed_eq, hf, hχ_fix_f]
  have hchig : SchwartzMap.smulLeftCLM ℂ χ g = g := by
    apply schwEmbed_injective
    rw [← ConeSupport.smulLeftCLM_schwEmbed_eq, hg, hχ_fix_g]

  have lhs_eq : (ConeSupport.schwEmbed c₁) f = u₁ f := by
    calc (ConeSupport.schwEmbed c₁) f
        = (TemperedDistribution.smulLeftCLM ℂ χ u₁) f := by rw [← hc₁]
      _ = u₁ (SchwartzMap.smulLeftCLM ℂ χ f) := by
          rw [TemperedDistribution.smulLeftCLM_apply_apply]
      _ = u₁ f := by rw [hchif]
  have rhs_eq : (ConeSupport.schwEmbed c₂) g = u₂ g := by
    calc (ConeSupport.schwEmbed c₂) g
        = (TemperedDistribution.smulLeftCLM ℂ χ u₂) g := by rw [← hc₂]
      _ = u₂ (SchwartzMap.smulLeftCLM ℂ χ g) := by
          rw [TemperedDistribution.smulLeftCLM_apply_apply]
      _ = u₂ g := by rw [hchig]

  rw [lhs_eq, rhs_eq]
  exact schwEmbed_chi_cross_integral c₁ c₂ hc₁ hc₂ f hf hchif g hg hchig

/-- Bundled existence statement combining `exists_chi_css_empty` with the cross-pairing identity:
there is a temperate-growth `χ` whose multiplication empties the conic singular supports, fixes the
Schwartz differences, and makes the cross-pairings of the Schwartz representatives agree. -/
theorem exists_chi_with_properties
    {n : ℕ}
    {K₁ K₂ : Set (ClosedBall n)}
    (hK : Disjoint K₁ K₂)
    (hK₁_closed : IsClosed K₁) (hK₂_closed : IsClosed K₂)
    {ψ₁ ψ₁' : EuclideanSpace ℝ (Fin n) → ℂ}
    (hψ : IsConicCutoffForDisjointCss K₁ K₂ ψ₁)
    (hψ' : IsConicCutoffForDisjointCss K₁ K₂ ψ₁')
    (u₁ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (h₁ : Css u₁ ⊆ K₁)
    (u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (h₂ : Css u₂ ⊆ K₂) :
    ∃ (χ : EuclideanSpace ℝ (Fin n) → ℂ),
      χ.HasTemperateGrowth ∧
      Css (TemperedDistribution.smulLeftCLM ℂ χ u₁) = ∅ ∧
      Css (TemperedDistribution.smulLeftCLM ℂ χ u₂) = ∅ ∧
      TemperedDistribution.smulLeftCLM ℂ χ
        (TemperedDistribution.smulLeftCLM ℂ ψ₁ u₂ -
         TemperedDistribution.smulLeftCLM ℂ ψ₁' u₂) =
        TemperedDistribution.smulLeftCLM ℂ ψ₁ u₂ -
         TemperedDistribution.smulLeftCLM ℂ ψ₁' u₂ ∧
      TemperedDistribution.smulLeftCLM ℂ χ
        (TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁') u₁ -
         TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁) u₁) =
        TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁') u₁ -
         TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁) u₁ ∧
      ∀ (c₁ c₂ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ),
        ConeSupport.schwEmbed c₁ = TemperedDistribution.smulLeftCLM ℂ χ u₁ →
        ConeSupport.schwEmbed c₂ = TemperedDistribution.smulLeftCLM ℂ χ u₂ →
        ∀ (f g : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ),
          ConeSupport.schwEmbed f =
            TemperedDistribution.smulLeftCLM ℂ ψ₁ u₂ -
              TemperedDistribution.smulLeftCLM ℂ ψ₁' u₂ →
          ConeSupport.schwEmbed g =
            TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁') u₁ -
              TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁) u₁ →
          (ConeSupport.schwEmbed c₁) f = (ConeSupport.schwEmbed c₂) g := by

  obtain ⟨χ, hχ_temp, hχu₁, hχu₂, hχ_fix_f, hχ_fix_g⟩ :=
    exists_chi_css_empty hK hK₁_closed hK₂_closed hψ hψ' u₁ h₁ u₂ h₂

  exact ⟨χ, hχ_temp, hχu₁, hχu₂, hχ_fix_f, hχ_fix_g,
    fun c₁ c₂ hc₁ hc₂ f g hf hg =>
      chi_cross_pairing hχu₁ hχu₂ hχ_fix_f hχ_fix_g c₁ c₂ hc₁ hc₂ f g hf hg⟩


/-- If multiplication by a temperate-growth `χ` fixes a tempered distribution `v`, then
multiplication by `1 - χ` annihilates `v`. -/
lemma smulLeft_complement_eq_zero_of_fixed
    {n : ℕ} (χ : EuclideanSpace ℝ (Fin n) → ℂ)
    (hχ : χ.HasTemperateGrowth)
    (v : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (hfix : TemperedDistribution.smulLeftCLM ℂ χ v = v) :
    TemperedDistribution.smulLeftCLM ℂ (1 - χ) v = 0 := by
  have hpart := smul_partition χ hχ v
  have : TemperedDistribution.smulLeftCLM ℂ χ v +
      TemperedDistribution.smulLeftCLM ℂ (1 - χ) v = v := hpart
  rw [hfix] at this

  have := sub_eq_zero.mpr this
  simp only [add_sub_cancel_left] at this
  exact this

/-- Existence of auxiliary Schwartz representatives `c₁, c₂` such that pairings of `u₁` and `u₂`
with the Schwartz preimages of the cutoff differences factor through the embeddings of `c₁` and
`c₂`, and the cross-pairings agree. -/
theorem exists_auxiliary_cutoff
    {n : ℕ}
    {K₁ K₂ : Set (ClosedBall n)}
    (hK : Disjoint K₁ K₂)
    (hK₁_closed : IsClosed K₁) (hK₂_closed : IsClosed K₂)
    {ψ₁ ψ₁' : EuclideanSpace ℝ (Fin n) → ℂ}
    (hψ : IsConicCutoffForDisjointCss K₁ K₂ ψ₁)
    (hψ' : IsConicCutoffForDisjointCss K₁ K₂ ψ₁')
    (u₁ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (h₁ : Css u₁ ⊆ K₁)
    (u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (h₂ : Css u₂ ⊆ K₂) :
    ∃ (c₁ c₂ : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ),
      (∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
        ConeSupport.schwEmbed f =
          TemperedDistribution.smulLeftCLM ℂ ψ₁ u₂ -
            TemperedDistribution.smulLeftCLM ℂ ψ₁' u₂ →
        u₁ f = (ConeSupport.schwEmbed c₁) f) ∧
      (∀ g : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
        ConeSupport.schwEmbed g =
          TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁') u₁ -
            TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁) u₁ →
        u₂ g = (ConeSupport.schwEmbed c₂) g) ∧
      (∀ (f g : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ),
        ConeSupport.schwEmbed f =
          TemperedDistribution.smulLeftCLM ℂ ψ₁ u₂ -
            TemperedDistribution.smulLeftCLM ℂ ψ₁' u₂ →
        ConeSupport.schwEmbed g =
          TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁') u₁ -
            TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁) u₁ →
        (ConeSupport.schwEmbed c₁) f = (ConeSupport.schwEmbed c₂) g) := by
  obtain ⟨χ, hχ_temp, hχu₁, hχu₂, hχ_fix_f, hχ_fix_g, hχ_cross⟩ :=
    exists_chi_with_properties hK hK₁_closed hK₂_closed hψ hψ' u₁ h₁ u₂ h₂
  set c₁ := toSchwartzOfEmptyCss _ hχu₁
  set c₂ := toSchwartzOfEmptyCss _ hχu₂
  have hc₁ : ConeSupport.schwEmbed c₁ = TemperedDistribution.smulLeftCLM ℂ χ u₁ :=
    schwEmbed_toSchwartzOfEmptyCss _ _
  have hc₂ : ConeSupport.schwEmbed c₂ = TemperedDistribution.smulLeftCLM ℂ χ u₂ :=
    schwEmbed_toSchwartzOfEmptyCss _ _

  have h_1chi_f := smulLeft_complement_eq_zero_of_fixed χ hχ_temp _ hχ_fix_f
  have h_1chi_g := smulLeft_complement_eq_zero_of_fixed χ hχ_temp _ hχ_fix_g

  have h_1chi_schw_f : ∀ f : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
      ConeSupport.schwEmbed f = TemperedDistribution.smulLeftCLM ℂ ψ₁ u₂ -
        TemperedDistribution.smulLeftCLM ℂ ψ₁' u₂ →
      SchwartzMap.smulLeftCLM ℂ (1 - χ) f = 0 := by
    intro f hf
    apply schwEmbed_injective
    rw [← ConeSupport.smulLeftCLM_schwEmbed_eq, hf, h_1chi_f, map_zero]
  have h_1chi_schw_g : ∀ g : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ,
      ConeSupport.schwEmbed g = TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁') u₁ -
        TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁) u₁ →
      SchwartzMap.smulLeftCLM ℂ (1 - χ) g = 0 := by
    intro g hg
    apply schwEmbed_injective
    rw [← ConeSupport.smulLeftCLM_schwEmbed_eq, hg, h_1chi_g, map_zero]
  refine ⟨c₁, c₂, ?_, ?_, ?_⟩

  · intro f hf


    have key : (TemperedDistribution.smulLeftCLM ℂ (1 - χ) u₁) f = 0 := by
      rw [TemperedDistribution.smulLeftCLM_apply_apply]
      rw [h_1chi_schw_f f hf, map_zero]
    have hpart := smul_partition χ hχ_temp u₁

    calc u₁ f = (TemperedDistribution.smulLeftCLM ℂ χ u₁ +
        TemperedDistribution.smulLeftCLM ℂ (1 - χ) u₁) f := by rw [hpart]
      _ = (TemperedDistribution.smulLeftCLM ℂ χ u₁) f +
          (TemperedDistribution.smulLeftCLM ℂ (1 - χ) u₁) f := by
        rfl
      _ = (TemperedDistribution.smulLeftCLM ℂ χ u₁) f := by rw [key, add_zero]
      _ = (ConeSupport.schwEmbed c₁) f := by rw [hc₁]

  · intro g hg
    have key : (TemperedDistribution.smulLeftCLM ℂ (1 - χ) u₂) g = 0 := by
      rw [TemperedDistribution.smulLeftCLM_apply_apply]
      rw [h_1chi_schw_g g hg, map_zero]
    have hpart := smul_partition χ hχ_temp u₂
    calc u₂ g = (TemperedDistribution.smulLeftCLM ℂ χ u₂ +
        TemperedDistribution.smulLeftCLM ℂ (1 - χ) u₂) g := by rw [hpart]
      _ = (TemperedDistribution.smulLeftCLM ℂ χ u₂) g +
          (TemperedDistribution.smulLeftCLM ℂ (1 - χ) u₂) g := by
        rfl
      _ = (TemperedDistribution.smulLeftCLM ℂ χ u₂) g := by rw [key, add_zero]
      _ = (ConeSupport.schwEmbed c₂) g := by rw [hc₂]


  · exact fun f g hf hg => hχ_cross c₁ c₂ hc₁ hc₂ f g hf hg

/-- Independence-of-cutoff key identity: the pairing of `u₁` with the Schwartz preimage of
`(ψ₁ - ψ₁') · u₂` equals the pairing of `u₂` with the Schwartz preimage of
`((1 - ψ₁') - (1 - ψ₁)) · u₁`. -/
lemma css_pairing_derivative_zero
    {n : ℕ}
    {K₁ K₂ : Set (ClosedBall n)}
    (hK : Disjoint K₁ K₂)
    (hK₁_closed : IsClosed K₁) (hK₂_closed : IsClosed K₂)
    {ψ₁ ψ₁' : EuclideanSpace ℝ (Fin n) → ℂ}
    (hψ : IsConicCutoffForDisjointCss K₁ K₂ ψ₁)
    (hψ' : IsConicCutoffForDisjointCss K₁ K₂ ψ₁')
    (u₁ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (h₁ : Css u₁ ⊆ K₁)
    (u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (h₂ : Css u₂ ⊆ K₂) :
    u₁ (toSchwartzOfEmptyCss _ (hψ.schwartz_of_mul u₂ h₂)
       - toSchwartzOfEmptyCss _ (hψ'.schwartz_of_mul u₂ h₂)) =
    u₂ (toSchwartzOfEmptyCss _ (hψ'.schwartz_of_compl_mul u₁ h₁)
       - toSchwartzOfEmptyCss _ (hψ.schwartz_of_compl_mul u₁ h₁)) := by
  set f := toSchwartzOfEmptyCss _ (hψ.schwartz_of_mul u₂ h₂)
       - toSchwartzOfEmptyCss _ (hψ'.schwartz_of_mul u₂ h₂)
  set g := toSchwartzOfEmptyCss _ (hψ'.schwartz_of_compl_mul u₁ h₁)
       - toSchwartzOfEmptyCss _ (hψ.schwartz_of_compl_mul u₁ h₁)

  have hf : ConeSupport.schwEmbed f =
      TemperedDistribution.smulLeftCLM ℂ ψ₁ u₂ -
        TemperedDistribution.smulLeftCLM ℂ ψ₁' u₂ := by
    simp only [f, map_sub, schwEmbed_toSchwartzOfEmptyCss]
  have hg : ConeSupport.schwEmbed g =
      TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁') u₁ -
        TemperedDistribution.smulLeftCLM ℂ (1 - ψ₁) u₁ := by
    simp only [g, map_sub, schwEmbed_toSchwartzOfEmptyCss]

  obtain ⟨c₁, c₂, h_u₁_eq, h_u₂_eq, h_cross⟩ :=
    exists_auxiliary_cutoff hK hK₁_closed hK₂_closed hψ hψ' u₁ h₁ u₂ h₂

  calc u₁ f = (ConeSupport.schwEmbed c₁) f := h_u₁_eq f hf
    _ = (ConeSupport.schwEmbed c₂) g := h_cross f g hf hg
    _ = u₂ g := (h_u₂_eq g hg).symm

/-- The value of `cssPairingWith ψ₁ hψ u₁ h₁ u₂ h₂` is independent of the choice of conic cutoff
`ψ₁`: any two valid cutoffs give equal pairings. -/
theorem disjoint_css_pairing_independent
    {n : ℕ}
    {K₁ K₂ : Set (ClosedBall n)}
    (hK : Disjoint K₁ K₂)
    (hK₁_closed : IsClosed K₁) (hK₂_closed : IsClosed K₂)
    {ψ₁ ψ₁' : EuclideanSpace ℝ (Fin n) → ℂ}
    (hψ : IsConicCutoffForDisjointCss K₁ K₂ ψ₁)
    (hψ' : IsConicCutoffForDisjointCss K₁ K₂ ψ₁')
    (u₁ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (h₁ : Css u₁ ⊆ K₁)
    (u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (h₂ : Css u₂ ⊆ K₂) :
    cssPairingWith ψ₁ hψ u₁ h₁ u₂ h₂ = cssPairingWith ψ₁' hψ' u₁ h₁ u₂ h₂ := by
  simp only [cssPairingWith]
  have h_lin₁ := map_sub u₁
    (toSchwartzOfEmptyCss _ (hψ.schwartz_of_mul u₂ h₂))
    (toSchwartzOfEmptyCss _ (hψ'.schwartz_of_mul u₂ h₂))
  have h_lin₂ := map_sub u₂
    (toSchwartzOfEmptyCss _ (hψ'.schwartz_of_compl_mul u₁ h₁))
    (toSchwartzOfEmptyCss _ (hψ.schwartz_of_compl_mul u₁ h₁))
  have h_deriv := css_pairing_derivative_zero hK hK₁_closed hK₂_closed hψ hψ' u₁ h₁ u₂ h₂
  linear_combination h_deriv - h_lin₁ + h_lin₂

/-- Existence of a canonical pairing `P u₁ u₂` for distributions with disjoint conic singular
supports `K₁, K₂`, which agrees with `cssPairingWith` for every choice of conic cutoff. -/
theorem exists_disjoint_css_pairing
    {n : ℕ}
    {K₁ K₂ : Set (ClosedBall n)}
    (hK : Disjoint K₁ K₂)
    (hK₁_closed : IsClosed K₁) (hK₂_closed : IsClosed K₂) :
    ∃ P : (u₁ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) → Css u₁ ⊆ K₁ →
          (u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) → Css u₂ ⊆ K₂ → ℂ,
      ∀ (ψ₁ : EuclideanSpace ℝ (Fin n) → ℂ)
        (hψ : IsConicCutoffForDisjointCss K₁ K₂ ψ₁)
        (u₁ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (h₁ : Css u₁ ⊆ K₁)
        (u₂ : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) (h₂ : Css u₂ ⊆ K₂),
        P u₁ h₁ u₂ h₂ = cssPairingWith ψ₁ hψ u₁ h₁ u₂ h₂ := by
  by_cases h : ∃ (ψ₁₀ : EuclideanSpace ℝ (Fin n) → ℂ),
      IsConicCutoffForDisjointCss K₁ K₂ ψ₁₀
  · obtain ⟨ψ₁₀, hψ₀⟩ := h
    exact ⟨fun u₁ h₁ u₂ h₂ => cssPairingWith ψ₁₀ hψ₀ u₁ h₁ u₂ h₂,
      fun ψ₁ hψ u₁ h₁ u₂ h₂ =>
        disjoint_css_pairing_independent hK hK₁_closed hK₂_closed hψ₀ hψ u₁ h₁ u₂ h₂⟩
  · exact ⟨fun _ _ _ _ => 0,
      fun ψ₁ hψ _ _ _ _ => absurd ⟨ψ₁, hψ⟩ h⟩

end WavefrontSet
