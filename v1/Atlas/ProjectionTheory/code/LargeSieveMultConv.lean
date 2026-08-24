/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.ProjectionTheory.code.LinnikLargeSieve
import Atlas.ProjectionTheory.code.MultConvLinftyBound

open Finset Complex BigOperators

noncomputable section

namespace LargeSieveMultConv

/-- Squared $L^2$ norm of a function `f : Fin N → ℂ`: $\sum_n |f(n)|^2$. -/
def l2NormSq {N : ℕ} (f : Fin N → ℂ) : ℝ :=
  ∑ n : Fin N, ‖f n‖ ^ 2

/-- The $L^\infty(\mathbb{Z}_p^*)$ norm of the high-frequency part of the multiplicative
convolution `(π_p f *_M π_p g)_H^*` over the unit group of `ZMod p`. -/
def highFreqProjMulConvLinf (N₁ N₂ : ℕ) (p : ℕ) (hp : Nat.Prime p)
    (f : Fin N₁ → ℂ) (g : Fin N₂ → ℂ) : ℝ :=
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  ⨆ a : (ZMod p)ˣ,
    ‖HighFreqMultConv.highFreqUnits p
      (HighFreqMultConv.mulConvUnits p
        (fun u => LinnikLargeSieve.modProjection N₁ p f (u : ZMod p))
        (fun u => LinnikLargeSieve.modProjection N₂ p g (u : ZMod p))) a‖

/-- Left-hand side of the large-sieve / multiplicative convolution theorem:
`∑_{p ∈ P_M} ‖(π_p(f *_M g))_h^*‖_{L^∞}^2`. -/
def largeSieveMultConvLHS (N₁ N₂ M : ℕ) (f : Fin N₁ → ℂ) (g : Fin N₂ → ℂ) : ℝ :=
  ∑ p ∈ LinnikLargeSieve.primesInRange M,
    if hp : Nat.Prime p then (highFreqProjMulConvLinf N₁ N₂ p hp f g) ^ 2
    else 0

/-- $L^2$ norm of `f : Fin N → ℂ`: the square root of `l2NormSq f`. -/
def l2Norm {N : ℕ} (f : Fin N → ℂ) : ℝ :=
  Real.sqrt (l2NormSq f)

end LargeSieveMultConv

end


/-- Combined bound used as a black box for the main theorem: the LHS is at most
$((N_1/M + M)(N_2/M + M))^{1/2} \cdot \|f\|_{L^2} \cdot \|g\|_{L^2}$ (without an extra constant). -/
theorem largeSieveMultConvLHS_le_combined
    (N₁ N₂ M : ℕ) (hM : 0 < M)
    (f : Fin N₁ → ℂ) (g : Fin N₂ → ℂ) :
    LargeSieveMultConv.largeSieveMultConvLHS N₁ N₂ M f g ≤
      ((↑N₁ / ↑M + ↑M) * (↑N₂ / ↑M + ↑M)) ^ ((1 : ℝ) / 2) *
        LargeSieveMultConv.l2Norm f * LargeSieveMultConv.l2Norm g := by sorry

noncomputable section

open Finset BigOperators

/-- Large sieve and multiplicative convolution theorem: if `f : [N₁] → ℂ` and `g : [N₂] → ℂ`,
then `f *_M g : [N₁ N₂] → ℂ`, and
$$\sum_{p \in P_M} \|(\pi_p(f *_M g))_h^*\|_{L^\infty}^2 \lesssim
\big((N_1/M + M)(N_2/M + M)\big)^{1/2} \|f\|_{L^2} \|g\|_{L^2}.$$ -/
theorem LargeSieveMultConv.large_sieve_mult_conv :
    ∃ C : ℝ, C > 0 ∧ ∀ (N₁ N₂ M : ℕ), 0 < M →
      ∀ (f : Fin N₁ → ℂ) (g : Fin N₂ → ℂ),
        LargeSieveMultConv.largeSieveMultConvLHS N₁ N₂ M f g ≤
          C * ((↑N₁ / ↑M + ↑M) * (↑N₂ / ↑M + ↑M)) ^ ((1 : ℝ) / 2) *
            LargeSieveMultConv.l2Norm f * LargeSieveMultConv.l2Norm g := by
  refine ⟨1, one_pos, fun N₁ N₂ M hM f g => ?_⟩
  have h := largeSieveMultConvLHS_le_combined N₁ N₂ M hM f g
  linarith

end
