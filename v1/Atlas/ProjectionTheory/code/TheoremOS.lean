/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProjectionTheory.code.Submultiplicative

namespace ProjectionTheory

/-- Abstract data bundling the parameter space used to define
`R_{AD}(s, t, δ)` in the AD-regular case. For each triple `(s, t, δ)` it
provides:

* a type `Config s t δ` of admissible AD-regular configurations,
* a non-negative, bounded ratio functional `ratio s t δ : Config s t δ → ℝ`,
* an embedding into the un-parameterised `adConfigSpace.Config δ`
  preserving the ratio.

`R_AD_st s t δ` is then defined as the supremum of `ratio s t δ` over all
configurations. -/
structure ADConfigDataST where
  Config : ℝ → ℝ → ℝ → Type
  ratio : (s t δ : ℝ) → Config s t δ → ℝ
  ratio_nonneg : ∀ (s t δ : ℝ) (c : Config s t δ), 0 ≤ ratio s t δ c
  ratio_bddAbove : ∀ (s t δ : ℝ), BddAbove (Set.range (ratio s t δ))
  config_nonempty : ∀ (s t δ : ℝ), Nonempty (Config s t δ)
  embed : (s t δ : ℝ) → Config s t δ → adConfigSpace.Config δ
  embed_ratio : ∀ (s t δ : ℝ) (c : Config s t δ),
    adConfigSpace.ratio δ (embed s t δ c) = ratio s t δ c

/-- A chosen instance of `ADConfigDataST`: the concrete `(s, t)`-parameterised
AD-regular configuration data used throughout this section. -/
noncomputable def adConfigDataST : ADConfigDataST := by sorry

/-- The Orponen-Shmerkin quantity $R_{AD}(s, t, \delta)$: the supremum of
the ratio functional over all admissible `(s, t)`-AD-regular configurations
at scale `δ`. -/
noncomputable def R_AD_st (s t δ : ℝ) : ℝ :=
  sSup (Set.range (adConfigDataST.ratio s t δ))

/-- **Theorem (Orponen-Shmerkin).** Sharp projection bound in the
AD-regular case: for `0 < s ≤ 1`, `0 < t < 2` and every `ε > 0`, there is
a constant `C > 0` such that for all `0 < δ < 1`,
$$R_{AD}(s, t, \delta) \;\le\; C\,\delta^{-\varepsilon}\,
   \max\!\Big( 1,\; \delta^{-t/2}\delta^{s/2},\; \delta^{\,1 - t} \Big).$$
This is the central estimate of the chapter on sharp projection theorems
for AD-regular sets. -/
theorem theorem_OS
    (s t : ℝ) (hs : 0 < s) (hs' : s ≤ 1) (ht : 0 < t) (ht' : t < 2)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 →
        R_AD_st s t δ ≤ C * δ ^ (-ε) *
          max (max 1 (δ ^ ((-t + s) / 2))) (δ ^ (1 - t)) := by sorry

end ProjectionTheory
