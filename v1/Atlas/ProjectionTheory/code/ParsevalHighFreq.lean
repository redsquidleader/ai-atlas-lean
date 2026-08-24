/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open Finset Complex ZMod

namespace ProjectionTheory

variable {p : ℕ} [NeZero p]

/-- The high-frequency part of `g : ZMod p → ℂ`: the function `g` with its mean
removed, $g_h(a) = g(a) - \tfrac{1}{p}\sum_b g(b)$. This is the orthogonal complement
of the constant (zero-frequency) component $g_0$ in the decomposition $g = g_0 + g_h$. -/
noncomputable def highFreqPart (g : ZMod p → ℂ) : ZMod p → ℂ :=
  fun a => g a - (↑p)⁻¹ * (∑ b : ZMod p, g b)

/-- The Fourier transform of the high-frequency part vanishes at $0$:
$\widehat{g_h}(0) = 0$. This is the defining property of removing the zero
Fourier mode. -/
lemma dft_highFreqPart_zero (g : ZMod p → ℂ) :
    𝓕 (highFreqPart g) 0 = 0 := by
  simp only [dft_apply_zero, highFreqPart, sum_sub_distrib, sum_const, card_univ, ZMod.card]
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  rw [nsmul_eq_mul]
  field_simp
  ring

/-- Off the zero frequency, the Fourier transform of the high-frequency part agrees
with that of `g`: $\widehat{g_h}(\alpha) = \hat g(\alpha)$ for $\alpha \neq 0$. -/
lemma dft_highFreqPart_ne_zero (g : ZMod p → ℂ) (α : ZMod p) (hα : α ≠ 0) :
    𝓕 (highFreqPart g) α = 𝓕 g α := by
  simp only [highFreqPart, dft_apply, smul_eq_mul]
  have hfunc : (fun j => (stdAddChar (-(j * α)) : ℂ) * (g j - (↑p)⁻¹ * ∑ b, g b)) =
      (fun j => (stdAddChar (-(j * α)) : ℂ) * g j -
                (stdAddChar (-(j * α)) : ℂ) * ((↑p)⁻¹ * ∑ b, g b)) := by
    ext; ring
  rw [hfunc, sum_sub_distrib]
  suffices h : ∑ j : ZMod p, (stdAddChar (-(j * α)) : ℂ) * ((↑p)⁻¹ * ∑ b, g b) = 0 by
    simp [h]
  have hcomm : (fun j => (stdAddChar (-(j * α)) : ℂ) * ((↑p)⁻¹ * ∑ b, g b)) =
      (fun j => ((↑p)⁻¹ * ∑ b, g b) * (stdAddChar (-(j * α)) : ℂ)) := by
    ext; ring
  rw [hcomm, ← mul_sum]
  suffices hchar : ∑ j : ZMod p, (stdAddChar (-(j * α)) : ℂ) = 0 by
    rw [hchar, mul_zero]
  have key := AddChar.sum_mulShift (-(α : ZMod p)) (isPrimitive_stdAddChar p)
  simp only [neg_eq_zero, hα, ↓reduceIte, Nat.cast_zero] at key
  convert key using 1
  congr 1; ext j
  ring_nf

end ProjectionTheory

section PlancherelAxiom

open Finset Complex ZMod


/-- **Plancherel's identity on $\mathbb{Z}/p\mathbb{Z}$.** For `g : ZMod p → ℂ`,
$$p \sum_{a \in \mathbb{Z}/p} |g(a)|^2 = \sum_{\alpha \in \mathbb{Z}/p} |\hat g(\alpha)|^2.$$ -/
theorem plancherel_zmod (p : ℕ) [NeZero p] (g : ZMod p → ℂ) :
    (↑p : ℝ) * ∑ a : ZMod p, ‖g a‖^2 = ∑ α : ZMod p, ‖𝓕 g α‖^2 := by sorry

end PlancherelAxiom

namespace ProjectionTheory

open Finset Complex ZMod

variable {p : ℕ} [NeZero p]

/-- **Parseval applied to the high-frequency part $f_h$.** The $L^2$ mass of the
high-frequency part is captured by the non-zero Fourier modes of `g`:
$$p \sum_{a} |g_h(a)|^2 = \sum_{\alpha \neq 0} |\hat g(\alpha)|^2.$$ -/
theorem parseval_high_freq (g : ZMod p → ℂ) :
    (↑p : ℝ) * ∑ a : ZMod p, ‖highFreqPart g a‖^2 =
    ∑ α ∈ (univ : Finset (ZMod p)).filter (· ≠ 0), ‖𝓕 g α‖^2 := by

  have hP := plancherel_zmod p (highFreqPart g)
  rw [hP]

  have hsplit : ∑ α : ZMod p, ‖𝓕 (highFreqPart g) α‖^2 =
      ‖𝓕 (highFreqPart g) 0‖^2 +
      ∑ α ∈ (univ : Finset (ZMod p)).filter (· ≠ 0), ‖𝓕 (highFreqPart g) α‖^2 := by
    rw [← Finset.add_sum_erase _ _ (mem_univ (0 : ZMod p))]
    congr 1
    apply sum_congr
    · ext x; simp [mem_erase, mem_filter]
    · intros; rfl
  rw [hsplit, dft_highFreqPart_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_add]

  apply sum_congr rfl
  intro α hα
  rw [mem_filter] at hα
  rw [dft_highFreqPart_ne_zero g α hα.2]

end ProjectionTheory
