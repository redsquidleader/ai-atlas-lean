/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace ProjectionTheory

/--
Data bundle for the Euclidean projection bound theorem: a scale parameter `R > 1`,
a point set `X` of cardinality `cardX`, a direction set `D` of cardinality `cardD`,
a uniform projection bound `S = max_{θ ∈ D} |π_θ(X)|`, and local covering numbers
`nX r`, `nD ρ` measuring the maximum number of points of `X` (resp. directions of `D`)
in any ball of radius `r` (resp. `ρ`), each bounded above by `cardX`, `cardD`.
-/
structure EuclideanProjectionData where
  R : ℝ
  hR : 1 < R
  cardX : ℕ
  hcardX : 0 < cardX
  cardD : ℕ
  hcardD : 0 < cardD
  S : ℕ
  hS : 0 < S
  nX : ℝ → ℕ
  nD : ℝ → ℕ
  hnX_le : ∀ r, (nX r : ℝ) ≤ cardX
  hnD_le : ∀ ρ, (nD ρ : ℝ) ≤ cardD

/-- Number of dyadic scales `1 ≤ r ≤ R` used in the wave packet decomposition;
explicitly `⌊log₂ ⌈R⌉⌋ + 1`. -/
noncomputable def numDyadicScales (d : EuclideanProjectionData) : ℕ :=
  Nat.log 2 (Nat.ceil d.R) + 1

/--
Existence of the wave packet decomposition `f = ∑ₖ fₖ` underlying the Euclidean
projection bound. Produces a total `L²`-energy together with per-scale energies and
pointwise values such that:
* `f(i) ≥ |D|` at every point of `X` (the projection lower bound),
* the total energy equals both `∑ᵢ f(i)²` and the sum of per-scale energies, and
* each per-scale energy is bounded by `S · |D| · R · max_{r ∈ [1,R]} (N_X(r) · N_D(r/R) / r²)`.
-/
theorem wave_packet_construction (d : EuclideanProjectionData) :
  ∃ (L2_energy : ℝ) (per_scale : Fin (numDyadicScales d) → ℝ)
    (f_values : Fin d.cardX → ℝ),
    (∀ i, f_values i ≥ (d.cardD : ℝ)) ∧
    L2_energy = ∑ i, (f_values i) ^ 2 ∧
    L2_energy = Finset.univ.sum per_scale ∧
    (∀ k, per_scale k ≤
      (d.S : ℝ) * (d.cardD : ℝ) * d.R *
        ⨆ r ∈ Set.Icc 1 d.R, ((d.nX r : ℝ) * (d.nD (r / d.R) : ℝ) / (r ^ 2))) := by sorry

/-- The total `L²`-energy of the wave packet decomposition extracted from
`wave_packet_construction`. -/
noncomputable def wave_packet_L2_energy (d : EuclideanProjectionData) : ℝ :=
  (wave_packet_construction d).choose

/-- The per-scale `L²`-energies `‖fₖ‖²` extracted from `wave_packet_construction`. -/
noncomputable def wave_packet_per_scale_energy (d : EuclideanProjectionData) :
    Fin (numDyadicScales d) → ℝ :=
  (wave_packet_construction d).choose_spec.choose

/-- The pointwise values `f(i)` of the wave packet at the points of `X`,
extracted from `wave_packet_construction`. -/
noncomputable def wave_packet_f_values (d : EuclideanProjectionData) :
    Fin d.cardX → ℝ :=
  (wave_packet_construction d).choose_spec.choose_spec.choose

/-- Bundles the defining properties of the wave packet construction: pointwise
lower bound `f(i) ≥ |D|`, the two energy identities, and the per-scale energy bound. -/
theorem wave_packet_construction_props (d : EuclideanProjectionData) :
    (∀ i, wave_packet_f_values d i ≥ (d.cardD : ℝ)) ∧
    wave_packet_L2_energy d = ∑ i, (wave_packet_f_values d i) ^ 2 ∧
    wave_packet_L2_energy d = Finset.univ.sum (wave_packet_per_scale_energy d) ∧
    (∀ k, wave_packet_per_scale_energy d k ≤
      (d.S : ℝ) * (d.cardD : ℝ) * d.R *
        ⨆ r ∈ Set.Icc 1 d.R, ((d.nX r : ℝ) * (d.nD (r / d.R) : ℝ) / (r ^ 2))) :=
  (wave_packet_construction d).choose_spec.choose_spec.choose_spec

/-- Pointwise lower bound for the wave packet: there exist values `f(i) ≥ |D|`
whose squared sum equals the total `L²`-energy. -/
theorem wave_packet_pointwise_bound (d : EuclideanProjectionData) :
    ∃ (f_values : Fin d.cardX → ℝ),
      (∀ i, f_values i ≥ (d.cardD : ℝ)) ∧
      wave_packet_L2_energy d = ∑ i, (f_values i) ^ 2 :=
  ⟨wave_packet_f_values d,
    (wave_packet_construction_props d).1,
    (wave_packet_construction_props d).2.1⟩

/-- Near-orthogonality of the dyadic pieces: the total `L²`-energy equals the
sum of the per-scale energies `∑ₖ ‖fₖ‖²`. -/
theorem wave_packet_lp_orthogonality (d : EuclideanProjectionData) :
    wave_packet_L2_energy d = Finset.univ.sum (wave_packet_per_scale_energy d) :=
  (wave_packet_construction_props d).2.2.1

/-- Lower bound on the wave packet `L²`-energy: since `f(i) ≥ |D|` at each of the
`|X|` points, we have `‖f‖² ≥ |D|² · |X|`. -/
theorem wave_packet_lower_bound (d : EuclideanProjectionData) :
    (d.cardD : ℝ) ^ 2 * (d.cardX : ℝ) ≤ wave_packet_L2_energy d := by
  obtain ⟨f_values, hge, henergy⟩ := wave_packet_pointwise_bound d
  rw [henergy]
  have h_sq : ∀ i, (d.cardD : ℝ) ^ 2 ≤ (f_values i) ^ 2 := by
    intro i
    exact sq_le_sq' (by linarith [hge i]) (hge i)
  calc (d.cardD : ℝ) ^ 2 * (d.cardX : ℝ)
      = ∑ _i : Fin d.cardX, (d.cardD : ℝ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ i : Fin d.cardX, (f_values i) ^ 2 :=
        Finset.sum_le_sum (fun i _ => h_sq i)

/-- Trivial inequality form of orthogonality: `‖f‖² ≤ ∑ₖ ‖fₖ‖²`. -/
theorem wave_packet_decomposition_bound (d : EuclideanProjectionData) :
    wave_packet_L2_energy d ≤
      Finset.univ.sum (wave_packet_per_scale_energy d) := by
  rw [wave_packet_lp_orthogonality d]

/-- Per-scale `L²`-bound for the wave packet decomposition:
`‖fₖ‖² ≤ S · |D| · R · max_{r ∈ [1,R]} (N_X(r) N_D(r/R) / r²)`. -/
theorem wave_packet_per_scale_estimate (d : EuclideanProjectionData)
    (k : Fin (numDyadicScales d)) :
    wave_packet_per_scale_energy d k ≤
      (d.S : ℝ) * (d.cardD : ℝ) * d.R *
        ⨆ r ∈ Set.Icc 1 d.R, ((d.nX r : ℝ) * (d.nD (r / d.R) : ℝ) / (r ^ 2)) :=
  (wave_packet_construction_props d).2.2.2 k

/-- The number of dyadic scales is at most `log₂ R + 2`, which produces the
logarithmic factor in the final Euclidean projection bound. -/
theorem dyadic_scale_count_le_log (d : EuclideanProjectionData) :
    (numDyadicScales d : ℝ) ≤ Real.logb 2 d.R + 2 := by
  unfold numDyadicScales
  push_cast
  have hR_pos : (0 : ℝ) < d.R := by linarith [d.hR]
  have hceil_pos : 0 < Nat.ceil d.R := Nat.ceil_pos.mpr hR_pos

  have h1 : (Nat.log 2 (Nat.ceil d.R) : ℝ) ≤ Real.logb 2 (Nat.ceil d.R : ℝ) := by
    have := Real.natLog_le_logb (Nat.ceil d.R) 2
    simp only [Nat.cast_ofNat] at this
    exact this

  have h2 : Real.logb 2 (Nat.ceil d.R : ℝ) ≤ Real.logb 2 d.R + 1 := by
    have hceil_bound : (Nat.ceil d.R : ℝ) ≤ 2 * d.R := by
      have h := Nat.ceil_lt_add_one (le_of_lt hR_pos)
      linarith [d.hR]
    calc Real.logb 2 (Nat.ceil d.R : ℝ)
        ≤ Real.logb 2 (2 * d.R) := by
          apply Real.logb_le_logb_of_le (by norm_num : (1:ℝ) < 2)
          · exact Nat.cast_pos.mpr hceil_pos
          · exact hceil_bound
      _ = Real.logb 2 2 + Real.logb 2 d.R := by
          rw [Real.logb_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hR_pos)]
      _ = 1 + Real.logb 2 d.R := by
          rw [Real.logb_self_eq_one (by norm_num : (1:ℝ) < 2)]
      _ = Real.logb 2 d.R + 1 := by ring
  linarith

/-- Upper bound on the wave packet `L²`-energy obtained by summing the per-scale
estimates over the `log₂ R + 2` dyadic scales:
`‖f‖² ≤ S · |D| · R · (log₂ R + 2) · max_{r ∈ [1,R]} (N_X(r) N_D(r/R) / r²)`. -/
theorem wave_packet_upper_bound (d : EuclideanProjectionData) :
    wave_packet_L2_energy d ≤
      (d.S : ℝ) * (d.cardD : ℝ) * d.R * (Real.logb 2 d.R + 2) *
        ⨆ r ∈ Set.Icc 1 d.R, ((d.nX r : ℝ) * (d.nD (r / d.R) : ℝ) / (r ^ 2)) := by
  set M := ⨆ r ∈ Set.Icc 1 d.R, ((d.nX r : ℝ) * (d.nD (r / d.R) : ℝ) / (r ^ 2))
  set n := numDyadicScales d
  set g := wave_packet_per_scale_energy d
  set B := (d.S : ℝ) * (d.cardD : ℝ) * d.R * M

  have hB_nonneg : 0 ≤ B := by
    apply mul_nonneg
    apply mul_nonneg
    apply mul_nonneg
    · exact Nat.cast_nonneg' _
    · exact Nat.cast_nonneg' _
    · linarith [d.hR]
    · exact Real.iSup_nonneg fun r => Real.iSup_nonneg fun _ => by positivity

  calc wave_packet_L2_energy d

      ≤ Finset.univ.sum g := wave_packet_decomposition_bound d

    _ ≤ ↑n * B := by
        have h_bound := Finset.sum_le_card_nsmul Finset.univ g B
          (fun k _ => wave_packet_per_scale_estimate d k)
        simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h_bound
        exact h_bound

    _ ≤ (Real.logb 2 d.R + 2) * B :=
        mul_le_mul_of_nonneg_right (dyadic_scale_count_le_log d) hB_nonneg

    _ = (d.S : ℝ) * (d.cardD : ℝ) * d.R * (Real.logb 2 d.R + 2) * M := by ring

/-- Combined energy estimate chaining the lower and upper bounds:
`|D|² · |X| ≤ S · |D| · R · (log₂ R + 2) · max_r (N_X(r) N_D(r/R) / r²)`. -/
theorem wave_packet_energy_bound (d : EuclideanProjectionData) :
    (d.cardD : ℝ) ^ 2 * (d.cardX : ℝ) ≤
      (d.S : ℝ) * (d.cardD : ℝ) * d.R * (Real.logb 2 d.R + 2) *
        ⨆ r ∈ Set.Icc 1 d.R, ((d.nX r : ℝ) * (d.nD (r / d.R) : ℝ) / (r ^ 2)) :=
  le_trans (wave_packet_lower_bound d) (wave_packet_upper_bound d)

/--
Euclidean projection bound (the main theorem of the section): there is a constant
`C > 0` such that
$$|D| \lessapprox \frac{S R}{|X|} \max_{1 \le r \le R} \frac{N_X(r)\, N_D(r/R)}{r^2}.$$
This is the Euclidean analogue of the Fourier projection bound (Theorem 2.3) and
follows from canceling a factor of `|D|` in the wave packet energy estimate.
-/
theorem euclidean_projection_bound (d : EuclideanProjectionData) :
    ∃ C : ℝ, C > 0 ∧
      (d.cardD : ℝ) ≤ C * (Real.logb 2 d.R + 2) *
        ((d.S : ℝ) * d.R / (d.cardX : ℝ)) *
        ⨆ r ∈ Set.Icc 1 d.R,
          ((d.nX r : ℝ) * (d.nD (r / d.R) : ℝ) / (r ^ 2)) := by

  refine ⟨1, one_pos, ?_⟩
  have hD_pos : (0 : ℝ) < (d.cardD : ℝ) := Nat.cast_pos.mpr d.hcardD
  have hX_pos : (0 : ℝ) < (d.cardX : ℝ) := Nat.cast_pos.mpr d.hcardX
  set M := ⨆ r ∈ Set.Icc 1 d.R, ((d.nX r : ℝ) * (d.nD (r / d.R) : ℝ) / (r ^ 2))


  have h_combined : (d.cardD : ℝ) ^ 2 * (d.cardX : ℝ) ≤
      (d.S : ℝ) * (d.cardD : ℝ) * d.R * (Real.logb 2 d.R + 2) * M :=
    wave_packet_energy_bound d

  have h_div_D : (d.cardD : ℝ) * (d.cardX : ℝ) ≤
      (d.S : ℝ) * d.R * (Real.logb 2 d.R + 2) * M := by
    nlinarith [sq_nonneg (d.cardD : ℝ)]

  rw [show (1 : ℝ) * (Real.logb 2 d.R + 2) * ((d.S : ℝ) * d.R / (d.cardX : ℝ)) * M =
      (d.S : ℝ) * d.R * (Real.logb 2 d.R + 2) * M / (d.cardX : ℝ) from by ring]
  rw [le_div_iff₀ hX_pos]
  linarith

end ProjectionTheory
