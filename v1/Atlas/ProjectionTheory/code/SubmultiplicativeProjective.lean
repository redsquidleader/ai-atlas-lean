/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProjectionTheory.code.Submultiplicative

namespace ProjectionTheory

/-- The abstract data of a *projective* AD-regular configuration space at every scale
$\delta$. Each projective configuration embeds into the AD configuration space with matching
ratios, and admits a constant-loss decomposition: there exists $C > 0$ such that for every
factorization $\delta = \delta_1 \delta_2$ and every configuration $c$ at scale $\delta$,
there are configurations $c_1, c_2$ at scales $\delta_1, \delta_2$ with ratio bound
$\mathrm{ratio}(c) \le C \cdot \mathrm{ratio}(c_1) \cdot \mathrm{ratio}(c_2)$. -/
structure ProjectiveConfigSpace where
  Config : ℝ → Type
  ratio : (δ : ℝ) → Config δ → ℝ
  ratio_nonneg : ∀ (δ : ℝ) (c : Config δ), 0 ≤ ratio δ c
  ratio_bddAbove : ∀ (δ : ℝ), BddAbove (Set.range (ratio δ))
  config_nonempty : ∀ (δ : ℝ), Nonempty (Config δ)
  embed : (δ : ℝ) → Config δ → adConfigSpace.Config δ
  embed_ratio : ∀ (δ : ℝ) (c : Config δ), ratio δ c = adConfigSpace.ratio δ (embed δ c)
  decompose : ∃ C : ℝ, 0 < C ∧ ∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → δ₁ < 1 → 0 < δ₂ → δ₂ < 1 →
    ∀ c : Config (δ₁ * δ₂), ∃ c₁ : Config δ₁, ∃ c₂ : Config δ₂,
      ratio (δ₁ * δ₂) c ≤ C * (ratio δ₁ c₁ * ratio δ₂ c₂)

/-- The raw data underlying a projective AD configuration space: configurations with
explicit coarsen/restrict maps, and the pointwise incidence decomposition bound with
a universal constant $C$. -/
structure ProjectiveConfigData where
  Config : ℝ → Type
  ratio : (δ : ℝ) → Config δ → ℝ
  ratio_nonneg : ∀ (δ : ℝ) (c : Config δ), 0 ≤ ratio δ c
  ratio_bddAbove : ∀ (δ : ℝ), BddAbove (Set.range (ratio δ))
  config_nonempty : ∀ (δ : ℝ), Nonempty (Config δ)
  embed : (δ : ℝ) → Config δ → adConfigSpace.Config δ
  embed_ratio : ∀ (δ : ℝ) (c : Config δ), ratio δ c = adConfigSpace.ratio δ (embed δ c)
  coarsen : ∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → δ₁ < 1 → 0 < δ₂ → δ₂ < 1 →
    Config (δ₁ * δ₂) → Config δ₁
  restrict : ∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → δ₁ < 1 → 0 < δ₂ → δ₂ < 1 →
    Config (δ₁ * δ₂) → Config δ₂
  incidence_decomp : ∃ C : ℝ, 0 < C ∧ ∀ (δ₁ δ₂ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁' : δ₁ < 1)
    (hδ₂ : 0 < δ₂) (hδ₂' : δ₂ < 1),
    ∀ c : Config (δ₁ * δ₂),
      ratio (δ₁ * δ₂) c ≤ C *
        (ratio δ₁ (coarsen δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c) *
         ratio δ₂ (restrict δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c))

/-- The concrete projective AD configuration data used in the projection theory framework. -/
noncomputable def projConfigData : ProjectiveConfigData := by sorry

/-- The projective AD configuration space obtained from `projConfigData` by extracting the
pointwise incidence decomposition into a decomposition existence statement. -/
noncomputable def projConfigSpace : ProjectiveConfigSpace where
  Config := projConfigData.Config
  ratio := projConfigData.ratio
  ratio_nonneg := projConfigData.ratio_nonneg
  ratio_bddAbove := projConfigData.ratio_bddAbove
  config_nonempty := projConfigData.config_nonempty
  embed := projConfigData.embed
  embed_ratio := projConfigData.embed_ratio
  decompose := by

    obtain ⟨C, hC, hdecomp⟩ := projConfigData.incidence_decomp
    exact ⟨C, hC, fun δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c =>
      ⟨projConfigData.coarsen δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c,
       projConfigData.restrict δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c,
       hdecomp δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c⟩⟩

/-- The projective AD-regular incidence quantity $R_{AD,\mathrm{proj}}(\delta)$ at scale
$\delta$, defined as the supremum of the projective configuration ratios at scale $\delta$. -/
noncomputable def R_AD_proj (δ : ℝ) : ℝ :=
  sSup (Set.range (projConfigSpace.ratio δ))

/-- Each projective configuration ratio is bounded above by the supremum
$R_{AD,\mathrm{proj}}(\delta)$. -/
theorem proj_ratio_le_R_AD_proj (δ : ℝ) (c : projConfigSpace.Config δ) :
    projConfigSpace.ratio δ c ≤ R_AD_proj δ := by
  unfold R_AD_proj
  exact le_csSup (projConfigSpace.ratio_bddAbove δ) ⟨c, rfl⟩

/-- $R_{AD,\mathrm{proj}}(\delta) \ge 0$ for every scale $\delta$. -/
theorem R_AD_proj_nonneg (δ : ℝ) : 0 ≤ R_AD_proj δ := by
  unfold R_AD_proj
  apply le_csSup_of_le (projConfigSpace.ratio_bddAbove δ)
  · exact ⟨(projConfigSpace.config_nonempty δ).some, rfl⟩
  · exact projConfigSpace.ratio_nonneg δ _

/-- **Submultiplicative Lemma, projective version.** There exists a constant $C > 0$
such that whenever $\delta = \delta_1 \delta_2$ with $\delta_1, \delta_2 < 1$,
$R_{AD,\mathrm{proj}}(\delta_1 \delta_2) \le C \cdot
R_{AD,\mathrm{proj}}(\delta_1) \cdot R_{AD,\mathrm{proj}}(\delta_2)$. -/
theorem R_AD_proj_submultiplicative :
    ∃ C : ℝ, 0 < C ∧ ∀ (δ₁ δ₂ : ℝ), 0 < δ₁ → δ₁ < 1 → 0 < δ₂ → δ₂ < 1 →
      R_AD_proj (δ₁ * δ₂) ≤ C * R_AD_proj δ₁ * R_AD_proj δ₂ := by
  obtain ⟨C, hC, hdecomp⟩ := projConfigSpace.decompose
  refine ⟨C, hC, fun δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' => ?_⟩
  unfold R_AD_proj
  apply csSup_le
  · have := projConfigSpace.config_nonempty (δ₁ * δ₂)
    exact Set.range_nonempty (projConfigSpace.ratio (δ₁ * δ₂))
  · rintro _ ⟨c, rfl⟩
    obtain ⟨c₁, c₂, hc⟩ := hdecomp δ₁ δ₂ hδ₁ hδ₁' hδ₂ hδ₂' c
    calc projConfigSpace.ratio (δ₁ * δ₂) c
        ≤ C * (projConfigSpace.ratio δ₁ c₁ * projConfigSpace.ratio δ₂ c₂) := hc
      _ ≤ C * (sSup (Set.range (projConfigSpace.ratio δ₁)) *
              sSup (Set.range (projConfigSpace.ratio δ₂))) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul (proj_ratio_le_R_AD_proj δ₁ c₁) (proj_ratio_le_R_AD_proj δ₂ c₂)
              (projConfigSpace.ratio_nonneg δ₂ c₂) (R_AD_proj_nonneg δ₁)
          · exact le_of_lt hC
      _ = C * sSup (Set.range (projConfigSpace.ratio δ₁)) *
              sSup (Set.range (projConfigSpace.ratio δ₂)) := by ring

end ProjectionTheory
