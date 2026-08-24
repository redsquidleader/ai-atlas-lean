/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProjectionTheory.code.SubmultiplicativeProjective
import Atlas.ProjectionTheory.code.BourgainPropositions

namespace ProjectionTheory

/-- Abstract data packaging the projective AD-regular projection configurations indexed
by parameters `s, t` and scale `δ`, together with a nonnegative, uniformly bounded
"ratio" functional whose supremum defines `R_{AD, proj}(s, t, δ)`. -/
structure ProjConfigDataST where
  Config : ℝ → ℝ → ℝ → Type
  ratio : (s t δ : ℝ) → Config s t δ → ℝ
  ratio_nonneg : ∀ (s t δ : ℝ) (c : Config s t δ), 0 ≤ ratio s t δ c
  ratio_bddAbove : ∀ (s t δ : ℝ), BddAbove (Set.range (ratio s t δ))
  config_nonempty : ∀ (s t δ : ℝ), Nonempty (Config s t δ)

/-- The canonical `ProjConfigDataST` instance used to build the projective AD-regular
projection quantity `R_{AD, proj}(s, t, δ)`. -/
noncomputable def projConfigDataST : ProjConfigDataST := by sorry

/-- The projective AD-regular projection quantity `R_{AD, proj}(s, t, δ)`, defined as
the supremum of the ratio over all admissible configurations at parameters `(s, t, δ)`. -/
noncomputable def R_AD_proj_st (s t δ : ℝ) : ℝ :=
  sSup (Set.range (projConfigDataST.ratio s t δ))

/-- **Lemma (`ε`-improvement to the projective submultiplicative lemma).** Fix `s, t`
with `0 < s` and `0 < t < 2`. For every `α > 0` there exist `ε > 0` and `C > 0` such
that for every scale `δ ∈ (0, 1)`, either
`R_{AD, proj}(δ^{1/2}) ≲ δ^{-α} · max(1, δ^{-t/2+s/2}, δ^{1-t})` (the desired bound
already holds at scale `δ^{1/2}`), or the submultiplicative inequality improves to
`R_{AD, proj}(δ) ≲ δ^{ε} · R_{AD, proj}(δ^{1/2})²`. -/
theorem R_AD_proj_epsilon_improvement_submult
  (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (ht' : t < 2) (α : ℝ) (hα : 0 < α) :
  ∃ ε : ℝ, 0 < ε ∧ ∃ C : ℝ, 0 < C ∧
    ∀ δ : ℝ, 0 < δ → δ < 1 →
      (R_AD_proj_st s t (δ ^ (1/2 : ℝ)) ≤ C * δ ^ (-α) *
        max 1 (max (δ ^ (-(t/2)) * δ ^ (s/2)) (δ ^ (1 - t)))) ∨
      (R_AD_proj_st s t δ ≤ C * δ ^ ε * (R_AD_proj_st s t (δ ^ (1/2 : ℝ)))^2) := by sorry

end ProjectionTheory
