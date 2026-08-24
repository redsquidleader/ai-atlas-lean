/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Atlas.ProjectionTheory.code.OSRWSharp

open Classical

noncomputable section

namespace ProjectionTheory

/-- The *richness* of a `δ`-tube `T` with respect to a point set `E` is the number of
points of `E` contained in `T`. -/
noncomputable def DeltaTube.richness (T : DeltaTube) (E : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (E.filter (fun x => T.contains x)).card

/-- Two `δ`-tubes are *essentially distinct* at scale `δ` if either their midpoints are more
than `δ` apart, or their directions differ by more than `δ`. -/
def DeltaTube.EssentiallyDistinct (T₁ T₂ : DeltaTube) (δ : ℝ) : Prop :=
  dist T₁.midpoint T₂.midpoint > δ ∨ |T₁.direction - T₂.direction| > δ

/-- A finite point set `E ⊆ ℝ²` is *well-spaced* with constant `C₀` if every ball of radius
`|E|^(-1/2)` contains at most `C₀` points of `E`, i.e. $|E \cap B_{|E|^{-1/2}}| \lesssim 1$. -/
def IsWellSpaced (E : Finset (EuclideanSpace ℝ (Fin 2))) (C₀ : ℝ) : Prop :=
  ∀ c : EuclideanSpace ℝ (Fin 2),
    ((E.filter (fun x => dist x c ≤ (E.card : ℝ) ^ (-(1 : ℝ) / 2))).card : ℝ) ≤ C₀

/-- **GSW Fourier bound (first ingredient).** There is a universal constant `C₀ > 0` such
that for any `δ`-separated set `E` of points in the unit ball and any collection `𝒯` of
essentially distinct `δ`-tubes of width `δ`, each of which is `R`-rich for `E`, one has
$|\mathcal T| \le C_0 \, \delta^{-1} |E| / R^2$. -/
theorem gsw_basic_fourier_bound :
  ∃ (C₀ : ℝ), C₀ > 0 ∧
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
    ∀ (E : Finset (EuclideanSpace ℝ (Fin 2))),
      0 < E.card →
      (∀ x ∈ E, ‖x‖ ≤ 1) →
      (∀ x ∈ E, ∀ y ∈ E, x ≠ y → δ ≤ dist x y) →
    ∀ (R : ℝ), R > 0 → R ≤ (E.card : ℝ) →
    ∀ (𝒯 : Finset DeltaTube),
      (∀ T ∈ 𝒯, T.width = δ) →
      (∀ T ∈ 𝒯, (T.richness E : ℝ) ≥ R) →
      (∀ T₁ ∈ 𝒯, ∀ T₂ ∈ 𝒯, T₁ ≠ T₂ → DeltaTube.EssentiallyDistinct T₁ T₂ δ) →
      (𝒯.card : ℝ) ≤ C₀ * δ⁻¹ * (E.card : ℝ) / R ^ 2 := by sorry

/-- **GSW two-ends bound (second ingredient).** There exists `C₁ > 0` such that whenever a
collection `𝒯_sub` of `R`-rich `δ`-tubes admits, for some scale `Rtilde`, a subset
`E_sub ⊆ E` of size `≤ Rtilde` and pairwise-disjoint witness pairs (one large pair set of
size `≥ R²/4` per tube), the number of tubes satisfies
$|\mathcal T| \le C_1 \, \widetilde R^2 / R^2$.

This is a combinatorial double-counting on point pairs inside `E_sub × E_sub`. -/
theorem gsw_two_ends_bound :
  ∃ (C₁ : ℝ), C₁ > 0 ∧
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
    ∀ (E : Finset (EuclideanSpace ℝ (Fin 2))),
      0 < E.card →
      (∀ x ∈ E, ‖x‖ ≤ 1) →
      (∀ x ∈ E, ∀ y ∈ E, x ≠ y → δ ≤ dist x y) →
    ∀ (R : ℝ), R > 0 → R ≤ (E.card : ℝ) →
    ∀ (Rtilde : ℝ), δ ≤ Rtilde → Rtilde ≤ 1 →
    ∀ (𝒯_sub : Finset DeltaTube),
      (∀ T ∈ 𝒯_sub, T.width = δ) →
      (∀ T ∈ 𝒯_sub, (T.richness E : ℝ) ≥ R) →


      (∃ (E_sub : Finset (EuclideanSpace ℝ (Fin 2))),
        E_sub ⊆ E ∧
        (E_sub.card : ℝ) ≤ Rtilde ∧
        (∃ (witnesses : DeltaTube → Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2))),
          (∀ T ∈ 𝒯_sub, witnesses T ⊆ E_sub ×ˢ E_sub) ∧
          (∀ T ∈ 𝒯_sub, (witnesses T).card ≥ ⌈R ^ 2 / 4⌉₊) ∧
          (∀ T₁ ∈ 𝒯_sub, ∀ T₂ ∈ 𝒯_sub, T₁ ≠ T₂ →
            Disjoint (witnesses T₁) (witnesses T₂)))) →
      (𝒯_sub.card : ℝ) ≤ C₁ * Rtilde ^ 2 / R ^ 2 := by

  refine ⟨4, by norm_num, ?_⟩
  intro δ _hδ _hδ1 E _hE_pos _hE_ball _hE_sep R hR _hR_le_N Rtilde _hδ_Rtilde _hRtilde1
    𝒯_sub _h𝒯_width _h𝒯_rich hcomb
  obtain ⟨E_sub, _hE_sub_ss, hE_sub_card, witnesses, hwit_ss, hwit_card, hwit_disj⟩ := hcomb


  have h_union_le : (𝒯_sub.biUnion witnesses).card ≤ (E_sub ×ˢ E_sub).card := by
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨T, hT_mem, hp_wit⟩ := hp
    exact hwit_ss T hT_mem hp_wit

  have h_sum_eq : (𝒯_sub.biUnion witnesses).card = ∑ T ∈ 𝒯_sub, (witnesses T).card := by
    apply Finset.card_biUnion
    intro T₁ hT₁ T₂ hT₂ hne
    exact hwit_disj T₁ hT₁ T₂ hT₂ hne

  have h_sum_ge : 𝒯_sub.card * ⌈R ^ 2 / 4⌉₊ ≤ ∑ T ∈ 𝒯_sub, (witnesses T).card := by
    have := Finset.card_nsmul_le_sum 𝒯_sub (fun T => (witnesses T).card) ⌈R ^ 2 / 4⌉₊ hwit_card
    omega

  have h_prod_card : (E_sub ×ˢ E_sub).card = E_sub.card ^ 2 := by
    rw [Finset.card_product, sq]

  have h_key : 𝒯_sub.card * ⌈R ^ 2 / 4⌉₊ ≤ E_sub.card ^ 2 := by
    linarith [h_sum_ge, h_sum_eq ▸ h_union_le, h_prod_card ▸ (h_sum_eq ▸ h_union_le)]

  have hR2_pos : R ^ 2 > 0 := by positivity
  have h_ceil_ge : (⌈R ^ 2 / 4⌉₊ : ℝ) ≥ R ^ 2 / 4 := Nat.le_ceil _
  have h_key_real : (𝒯_sub.card : ℝ) * (R ^ 2 / 4) ≤ (E_sub.card : ℝ) ^ 2 := by
    calc (𝒯_sub.card : ℝ) * (R ^ 2 / 4)
        ≤ (𝒯_sub.card : ℝ) * (⌈R ^ 2 / 4⌉₊ : ℝ) := by
          apply mul_le_mul_of_nonneg_left h_ceil_ge (Nat.cast_nonneg _)
      _ = ((𝒯_sub.card * ⌈R ^ 2 / 4⌉₊ : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((E_sub.card ^ 2 : ℕ) : ℝ) := by exact_mod_cast h_key
      _ = (E_sub.card : ℝ) ^ 2 := by push_cast; ring

  have h_bound : (𝒯_sub.card : ℝ) ≤ 4 * (E_sub.card : ℝ) ^ 2 / R ^ 2 := by
    rw [le_div_iff₀ hR2_pos]
    linarith

  have h_Esub_sq : (E_sub.card : ℝ) ^ 2 ≤ Rtilde ^ 2 := by
    apply sq_le_sq'
    · linarith [Nat.cast_nonneg (α := ℝ) E_sub.card]
    · exact hE_sub_card
  calc (𝒯_sub.card : ℝ)
      ≤ 4 * (E_sub.card : ℝ) ^ 2 / R ^ 2 := h_bound
    _ ≤ 4 * Rtilde ^ 2 / R ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ R ^ 2)
        linarith

/-- **Dyadic geometric partition for GSW.** Given the Fourier and two-ends constants
`CF, CT > 0`, the set of `R`-rich essentially distinct `δ`-tubes can be partitioned into
`K ≲ 1 + log(1/δ)` dyadic scales `Rtilde k`, each carrying counts `n_rho k`, `per_rho k`
bounded respectively by the Fourier and two-ends estimates, with total
$|\mathcal T| \le \sum_k n_\rho(k)\, \text{per}_\rho(k)$. -/
theorem gsw_geometric_partition :
  ∀ (CF CT : ℝ), CF > 0 → CT > 0 →
  ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
  ∀ (E : Finset (EuclideanSpace ℝ (Fin 2))),
    0 < E.card →
    (∀ x ∈ E, ‖x‖ ≤ 1) →
    (∀ x ∈ E, ∀ y ∈ E, x ≠ y → δ ≤ dist x y) →
  ∀ (R : ℝ), R > 0 → R ≤ (E.card : ℝ) →
  ∀ (𝒯 : Finset DeltaTube),
    (∀ T ∈ 𝒯, T.width = δ) →
    (∀ T ∈ 𝒯, (T.richness E : ℝ) ≥ R) →
    (∀ T₁ ∈ 𝒯, ∀ T₂ ∈ 𝒯, T₁ ≠ T₂ → DeltaTube.EssentiallyDistinct T₁ T₂ δ) →

    ∃ (K : ℕ),
      (K : ℝ) ≤ 1 + Real.log (1 / δ) / Real.log 2 ∧
      ∃ (Rtilde : Fin K → ℝ) (n_rho per_rho : Fin K → ℝ),

        (∀ k, Rtilde k > 0) ∧

        (∀ k, 0 ≤ n_rho k) ∧
        (∀ k, 0 ≤ per_rho k) ∧

        (∀ k, n_rho k ≤ CF * (E.card : ℝ) ^ 2 / (R * (Rtilde k) ^ 2)) ∧

        (∀ k, per_rho k ≤ CT * (Rtilde k) ^ 2 / R ^ 2) ∧

        (𝒯.card : ℝ) ≤ ∑ k : Fin K, n_rho k * per_rho k := by sorry

/-- **Fat-tube decomposition.** Combining `gsw_basic_fourier_bound`, `gsw_two_ends_bound`,
and `gsw_geometric_partition`, the count of `R`-rich essentially distinct `δ`-tubes splits
into at most `K ≲ 1 + log(1/δ)` dyadic pieces, each bounded by the product
$\bigl(C_0 |E|^2 / (R\,\widetilde R^2)\bigr) \cdot \bigl(C_1 \widetilde R^2 / R^2\bigr)$. -/
theorem gsw_fat_tube_decomposition :
  ∃ (C₀ C₁ : ℝ), C₀ > 0 ∧ C₁ > 0 ∧
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
    ∀ (E : Finset (EuclideanSpace ℝ (Fin 2))),
      0 < E.card →
      (∀ x ∈ E, ‖x‖ ≤ 1) →
      (∀ x ∈ E, ∀ y ∈ E, x ≠ y → δ ≤ dist x y) →
    ∀ (R : ℝ), R > 0 → R ≤ (E.card : ℝ) →
    ∀ (𝒯 : Finset DeltaTube),
      (∀ T ∈ 𝒯, T.width = δ) →
      (∀ T ∈ 𝒯, (T.richness E : ℝ) ≥ R) →
      (∀ T₁ ∈ 𝒯, ∀ T₂ ∈ 𝒯, T₁ ≠ T₂ → DeltaTube.EssentiallyDistinct T₁ T₂ δ) →

      ∃ (K : ℕ),

        (K : ℝ) ≤ 1 + Real.log (1 / δ) / Real.log 2 ∧


        ∃ (Rtilde : Fin K → ℝ) (fourier twoends : Fin K → ℝ),
          (∀ k, Rtilde k > 0) ∧

          (∀ k, fourier k ≤ C₀ * (E.card : ℝ) ^ 2 / (R * (Rtilde k) ^ 2)) ∧

          (∀ k, twoends k ≤ C₁ * (Rtilde k) ^ 2 / R ^ 2) ∧

          (∀ k, 0 ≤ fourier k) ∧
          (∀ k, 0 ≤ twoends k) ∧

          (𝒯.card : ℝ) ≤ ∑ k : Fin K, fourier k * twoends k := by

  obtain ⟨CF, hCF_pos, _hCF_bound⟩ := gsw_basic_fourier_bound

  obtain ⟨CT, hCT_pos, _hCT_bound⟩ := gsw_two_ends_bound

  refine ⟨CF, CT, hCF_pos, hCT_pos, ?_⟩
  intro δ hδ hδ1 E hE_pos hE_ball hE_sep R hR hR_le_N 𝒯 h𝒯_width h𝒯_rich h𝒯_distinct

  obtain ⟨K, hK, Rtilde, n_rho, per_rho, hRt, hn_nn, hp_nn,
    hn_bound, hp_bound, hcard_sum⟩ :=
    gsw_geometric_partition CF CT hCF_pos hCT_pos δ hδ hδ1 E hE_pos hE_ball hE_sep
      R hR hR_le_N 𝒯 h𝒯_width h𝒯_rich h𝒯_distinct

  exact ⟨K, hK, Rtilde, n_rho, per_rho, hRt, hn_bound, hp_bound,
    hn_nn, hp_nn, hcard_sum⟩

/-- **Dyadic combination giving the GSW bound (up to a log).** Summing the dyadic pieces
of `gsw_fat_tube_decomposition` yields
$|\mathcal T| \le C_2 \bigl(1 + \log_2(1/\delta)\bigr) |E|^2 / R^3$. -/
theorem gsw_dyadic_combination :
  ∃ (C₂ : ℝ), C₂ > 0 ∧
    ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
    ∀ (E : Finset (EuclideanSpace ℝ (Fin 2))),
      0 < E.card →
      (∀ x ∈ E, ‖x‖ ≤ 1) →
      (∀ x ∈ E, ∀ y ∈ E, x ≠ y → δ ≤ dist x y) →
    ∀ (R : ℝ), R > 0 → R ≤ (E.card : ℝ) →
    ∀ (𝒯 : Finset DeltaTube),
      (∀ T ∈ 𝒯, T.width = δ) →
      (∀ T ∈ 𝒯, (T.richness E : ℝ) ≥ R) →
      (∀ T₁ ∈ 𝒯, ∀ T₂ ∈ 𝒯, T₁ ≠ T₂ → DeltaTube.EssentiallyDistinct T₁ T₂ δ) →
      (𝒯.card : ℝ) ≤ C₂ * (1 + Real.log (1 / δ) / Real.log 2) *
        (E.card : ℝ) ^ 2 / R ^ 3 := by

  obtain ⟨C₀, C₁, hC₀, hC₁, hdecomp⟩ := gsw_fat_tube_decomposition

  refine ⟨C₀ * C₁, by positivity, ?_⟩
  intro δ hδ hδ1 E hE_pos hE_ball hE_sep R hR hR_le_N 𝒯 h𝒯_width h𝒯_rich h𝒯_distinct

  obtain ⟨K, hK, Rtilde, fourier, twoends, hRt, hfourier, htwoends, hfourier_nn,
    htwoends_nn, hcard⟩ := hdecomp δ hδ hδ1 E hE_pos hE_ball hE_sep R hR hR_le_N
    𝒯 h𝒯_width h𝒯_rich h𝒯_distinct


  have h_prod_bound : ∀ k : Fin K,
      fourier k * twoends k ≤ C₀ * C₁ * (E.card : ℝ) ^ 2 / R ^ 3 := by
    intro k
    have hRtk : Rtilde k > 0 := hRt k
    calc fourier k * twoends k
        ≤ (C₀ * (E.card : ℝ) ^ 2 / (R * (Rtilde k) ^ 2)) *
          (C₁ * (Rtilde k) ^ 2 / R ^ 2) := by
          apply mul_le_mul (hfourier k) (htwoends k) (htwoends_nn k)
          positivity
      _ = C₀ * C₁ * (E.card : ℝ) ^ 2 / R ^ 3 := by

          field_simp


  calc (𝒯.card : ℝ)
      ≤ ∑ k : Fin K, fourier k * twoends k := hcard
    _ ≤ ∑ _k : Fin K, (C₀ * C₁ * (E.card : ℝ) ^ 2 / R ^ 3) :=
        Finset.sum_le_sum (fun k _ => h_prod_bound k)
    _ = (K : ℝ) * (C₀ * C₁ * (E.card : ℝ) ^ 2 / R ^ 3) := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (1 + Real.log (1 / δ) / Real.log 2) * (C₀ * C₁ * (E.card : ℝ) ^ 2 / R ^ 3) := by
        gcongr
    _ = C₀ * C₁ * (1 + Real.log (1 / δ) / Real.log 2) * (E.card : ℝ) ^ 2 / R ^ 3 := by
        ring

/-- For any `ε > 0`, the logarithmic factor `1 + log(1/δ)/log 2` is dominated by
`(1 + 1/(ε log 2)) · δ^(-ε)`. Used to convert the log factor in `gsw_dyadic_combination`
into the arbitrarily small loss `δ^(-ε)` appearing in `gsw_theorem`. -/
lemma log_dominated_by_rpow (ε : ℝ) (hε : 0 < ε) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 + Real.log (1 / δ) / Real.log 2 ≤ (1 + 1 / (ε * Real.log 2)) * δ ^ (-ε) := by
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hδε_ge_1 : (1 : ℝ) ≤ δ ^ (-ε) := by
    rw [Real.rpow_neg (le_of_lt hδ)]
    exact Bound.one_le_inv₀ (Real.rpow_pos_of_pos hδ ε)
      (Real.rpow_le_one (le_of_lt hδ) hδ1 (le_of_lt hε))
  have hδ_inv_nonneg : (0 : ℝ) ≤ 1 / δ := by positivity
  have hlog_bound : Real.log (1 / δ) ≤ (1 / δ) ^ ε / ε :=
    Real.log_le_rpow_div hδ_inv_nonneg hε
  have hpow_eq : (1 / δ) ^ ε = δ ^ (-ε) := by
    rw [one_div, Real.inv_rpow (le_of_lt hδ), Real.rpow_neg (le_of_lt hδ)]
  rw [hpow_eq] at hlog_bound

  have hmul : Real.log (1 / δ) * ε ≤ δ ^ (-ε) := by
    rwa [le_div_iff₀ hε] at hlog_bound
  have hlog_div : Real.log (1 / δ) / Real.log 2 ≤ δ ^ (-ε) / (ε * Real.log 2) := by
    rw [div_le_div_iff₀ hlog2_pos (by positivity : (0:ℝ) < ε * Real.log 2)]
    nlinarith
  have hexpand : (1 + 1 / (ε * Real.log 2)) * δ ^ (-ε) =
    δ ^ (-ε) + δ ^ (-ε) / (ε * Real.log 2) := by ring
  rw [hexpand]
  linarith

/-- **Theorem (GSW).** Let `E ⊂ ℝ²` be a set of `N` `δ`-balls in `B₁` which is well-spaced
(every ball of radius `N^(-1/2)` meets `E` in `≲ 1` points). Let `𝒯_R(E)` be a family of
essentially distinct `δ`-tubes with `|T ∩ E|_δ ≥ R`, and assume `R > δ^(-ε) · δ · |E|_δ`.
Then $|\mathcal T_R(E)| \lessapprox N^2 / R^3$, formalised here as
$|\mathcal T| \le C_\varepsilon \, \delta^{-\varepsilon} |E|^2 / R^3$. -/
theorem gsw_theorem (ε : ℝ) (hε : 0 < ε) :
  ∃ (C_ws : ℝ) (C_conc : ℝ), C_ws > 0 ∧ C_conc > 0 ∧
    ∀ (δ : ℝ) (_ : 0 < δ) (_ : δ ≤ 1)
      (E : Finset (EuclideanSpace ℝ (Fin 2)))
      (_ : 0 < E.card)
      (_ : ∀ x ∈ E, ‖x‖ ≤ 1)
      (_ : ∀ x ∈ E, ∀ y ∈ E, x ≠ y → δ ≤ dist x y)
      (_ : IsWellSpaced E C_ws)
      (R : ℝ) (_ : R > δ ^ (-ε) * δ * (E.card : ℝ))
      (𝒯 : Finset DeltaTube)
      (_ : ∀ T ∈ 𝒯, T.width = δ)
      (_ : ∀ T ∈ 𝒯, (T.richness E : ℝ) ≥ R)
      (_ : ∀ T₁ ∈ 𝒯, ∀ T₂ ∈ 𝒯, T₁ ≠ T₂ → DeltaTube.EssentiallyDistinct T₁ T₂ δ),
      (𝒯.card : ℝ) ≤ C_conc * δ ^ (-ε) * (E.card : ℝ) ^ 2 / R ^ 3 := by

  obtain ⟨C₂, hC₂_pos, hdyadic⟩ := gsw_dyadic_combination

  set Cε := C₂ * (1 + 1 / (ε * Real.log 2)) with hCε_def
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hCε_pos : Cε > 0 := by positivity
  refine ⟨C₂, Cε, hC₂_pos, hCε_pos, ?_⟩
  intro δ hδ hδ1 E hE_pos hE_ball hE_sep _hE_ws R hR 𝒯 h𝒯_width h𝒯_rich h𝒯_distinct
  have hR_pos : R > 0 := lt_trans (by positivity) hR
  have hN_pos : (0 : ℝ) < E.card := Nat.cast_pos.mpr hE_pos
  by_cases h𝒯_empty : 𝒯 = ∅
  · simp [h𝒯_empty]
    positivity
  ·
    obtain ⟨T₀, hT₀⟩ := Finset.nonempty_iff_ne_empty.mpr h𝒯_empty
    have hR_le_N : R ≤ (E.card : ℝ) :=
      le_trans (h𝒯_rich T₀ hT₀) (by exact_mod_cast Finset.card_filter_le E _)

    have hdc := hdyadic δ hδ hδ1 E hE_pos hE_ball hE_sep R hR_pos hR_le_N
      𝒯 h𝒯_width h𝒯_rich h𝒯_distinct


    have hlog_bound := log_dominated_by_rpow ε hε δ hδ hδ1


    calc (𝒯.card : ℝ)
        ≤ C₂ * (1 + Real.log (1 / δ) / Real.log 2) * (E.card : ℝ) ^ 2 / R ^ 3 := hdc
      _ ≤ C₂ * ((1 + 1 / (ε * Real.log 2)) * δ ^ (-ε)) * (E.card : ℝ) ^ 2 / R ^ 3 := by
          apply div_le_div_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ R ^ 3)
          apply mul_le_mul_of_nonneg_right _ (by positivity : (0 : ℝ) ≤ (E.card : ℝ) ^ 2)
          exact mul_le_mul_of_nonneg_left hlog_bound (le_of_lt hC₂_pos)
      _ = Cε * δ ^ (-ε) * (E.card : ℝ) ^ 2 / R ^ 3 := by
          rw [hCε_def]; ring

end ProjectionTheory

end
