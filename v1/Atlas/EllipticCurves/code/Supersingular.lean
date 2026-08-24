/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.EllipticCurves.code.OrdinarySupersingular

open OrdinarySupersingular Hasse

namespace Supersingular

/-- Auxiliary number-theoretic fact: if `t = k * p` satisfies `t^2 ≤ 4p` with `p ≥ 5`,
then `t = 0`. Used to deduce that, for `p ≥ 5`, the only multiple of `p` in the Hasse
interval `[-2√p, 2√p]` is zero. -/
lemma trace_eq_zero_of_dvd_of_sq_le
    {p : ℕ} (t : ℤ) (hp5 : (p : ℤ) ≥ 5) (hle : t ^ 2 ≤ 4 * (p : ℤ))
    (hdvd : (p : ℤ) ∣ t) :
    t = 0 := by
  obtain ⟨k, rfl⟩ := hdvd
  suffices k = 0 by simp [this]
  by_contra hk

  have hk_sq : 1 ≤ k ^ 2 := by
    have h0 := sq_pos_of_ne_zero hk
    omega

  have hle' : k ^ 2 * (p : ℤ) ^ 2 ≤ 4 * (p : ℤ) := by
    have : (k * (p : ℤ)) ^ 2 = k ^ 2 * (p : ℤ) ^ 2 := by ring
    linarith

  have hp_sq : (p : ℤ) ^ 2 ≤ 4 * (p : ℤ) := by nlinarith

  nlinarith

/-- Restatement of the Hasse bound `|t|^2 ≤ 4q` (Theorem 7.3) specialized to a prime
field `ZMod p`: the trace of Frobenius `t = tr π_E` of an affine Weierstrass curve over
`ℤ/pℤ` satisfies `t^2 ≤ 4p`. -/
lemma trace_sq_le_four_mul_prime
    (p : ℕ) [Fact (Nat.Prime p)]
    (E : WeierstrassCurve.Affine (ZMod p)) :
    (Hasse.traceFrobenius E) ^ 2 ≤ 4 * (p : ℤ) := by
  have hq : 0 < Fintype.card (ZMod p) := Fintype.card_pos
  have hsq := Hasse.trace_sq_le_four_mul_card E hq
  rw [ZMod.card] at hsq

  have h : ((Hasse.traceFrobenius E : ℤ) : ℝ) ^ 2 ≤ ((4 * (p : ℤ) : ℤ) : ℝ) := by
    push_cast; exact hsq
  exact_mod_cast h

/-- For `E/F_p` with `p > 3`, the prime `p` divides the trace of Frobenius `tr π_E`
if and only if `tr π_E = 0`. This is the bridge between the divisibility characterization
of supersingularity (Theorem 13.3) and the trace-zero characterization (Corollary 13.4). -/
theorem trace_dvd_iff_trace_eq_zero
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (hp3 : p > 3) (E : WeierstrassCurve.Affine (ZMod p)) :
    (p : ℤ) ∣ Hasse.traceFrobenius E ↔ Hasse.traceFrobenius E = 0 := by
  constructor
  · intro hdvd
    have hp5 : (p : ℤ) ≥ 5 := by
      have hprime := hp.out
      have : p ≠ 4 := by intro h; subst h; exact absurd hprime (by decide)
      omega
    exact trace_eq_zero_of_dvd_of_sq_le _ hp5
      (trace_sq_le_four_mul_prime p E) hdvd
  · intro h; rw [h]; exact dvd_zero _

/-- For `E/F_p` with `p` prime, `tr π_E = 0` iff `#E(F_p) = p + 1`, since
`tr π_E = (p + 1) - #E(F_p)` by definition. -/
theorem trace_zero_iff_card_eq
    (p : ℕ) [Fact (Nat.Prime p)]
    (E : WeierstrassCurve.Affine (ZMod p)) :
    Hasse.traceFrobenius E = 0 ↔
      (Hasse.numPoints E : ℤ) = (p : ℤ) + 1 := by
  unfold Hasse.traceFrobenius Hasse.numPoints
  rw [ZMod.card]
  omega

/-- Half of Corollary 13.4: for `E/F_p` with `p > 3` prime, `E` is supersingular iff
`tr π_E = 0`. -/
theorem supersingular_iff_trace_eq_zero
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    (hp3 : p > 3) (E : WeierstrassCurve.Affine (ZMod p)) :
    IsSupersingular E p ↔ Hasse.traceFrobenius E = 0 := by
  rw [isSupersingular_iff_trace_dvd p E]
  exact trace_dvd_iff_trace_eq_zero p hp3 E

/-- Corollary 13.4: for `E/F_p` with `p > 3` prime, `E` is supersingular iff
`#E(F_p) = p + 1`. -/
theorem supersingular_iff_card_eq
    (p : ℕ) [Fact (Nat.Prime p)]
    (hp3 : p > 3) (E : WeierstrassCurve.Affine (ZMod p)) :
    IsSupersingular E p ↔
      (Hasse.numPoints E : ℤ) = (p : ℤ) + 1 := by
  rw [supersingular_iff_trace_eq_zero p hp3, trace_zero_iff_card_eq]

end Supersingular
