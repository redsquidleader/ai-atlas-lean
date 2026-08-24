/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.HighDimensionalStatistics.code.Chapter3.Remark_3_1
import Atlas.HighDimensionalStatistics.code.Chapter3.Def_3_10
import Atlas.HighDimensionalStatistics.code.Chapter3.Lemma_3_14
import Atlas.HighDimensionalStatistics.code.Chapter3.Lemma_3_13
import Atlas.HighDimensionalStatistics.code.Chapter3.Thm_3_11

set_option maxHeartbeats 4800000
set_option maxRecDepth 4096

open Real MeasureTheory

namespace Chapter3

/-- The squared `L²` norm of a real-valued function `g` over `[0,1]`,
defined as `∫₀¹ g(x)² dx`. -/
noncomputable def L2normSq (g : ℝ → ℝ) : ℝ :=
  ∫ x in Set.Icc (0 : ℝ) 1, g x ^ 2

/-- The squared empirical norm of `g` evaluated on the uniform grid `{i/n : i = 0, …, n-1}`,
defined as `(1/n) ∑ g(i/n)²`. -/
noncomputable def empiricalNormSq (n : ℕ) (g : ℝ → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, g ((i : ℝ) / (n : ℝ)) ^ 2

/-- Sub-Gaussian noise vector: the coordinates `ε ω i` of `ε : Ω → Fin n → ℝ` are
componentwise sub-Gaussian with variance proxy `σsq`, integrable, with integrable exponentials,
and satisfying the analogous bound for arbitrary linear combinations. -/
structure IsSubGaussianNoiseVec {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (ε : Ω → Fin n → ℝ) (σsq : ℝ) (μ : Measure Ω) : Prop where
  bound : ∀ i : Fin n, ∀ s : ℝ,
    ∫ ω, Real.exp (s * ε ω i) ∂μ ≤ Real.exp (σsq * s ^ 2 / 2)
  integ : ∀ i : Fin n, MeasureTheory.Integrable (fun ω => ε ω i) μ
  exp_integ : ∀ i : Fin n, ∀ s : ℝ,
    MeasureTheory.Integrable (fun ω => Real.exp (s * ε ω i)) μ
  weighted_sum_bound : ∀ (w : Fin n → ℝ), ∀ s : ℝ,
    ∫ ω, Real.exp (s * ∑ i, w i * ε ω i) ∂μ ≤
      Real.exp (σsq * (∑ i, w i ^ 2) * s ^ 2 / 2)

/-- Coerce an `IsSubGaussianNoiseVec` witness to its componentwise MGF bound. -/
instance {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {ε : Ω → Fin n → ℝ} {σsq : ℝ} {μ : Measure Ω} :
    CoeFun (IsSubGaussianNoiseVec ε σsq μ)
      (fun _ => ∀ i : Fin n, ∀ s : ℝ,
        ∫ ω, Real.exp (s * ε ω i) ∂μ ≤ Real.exp (σsq * s ^ 2 / 2)) where
  coe := IsSubGaussianNoiseVec.bound

/-- The trigonometric linear combination `∑_{j=0}^{M-1} θ_j · φ_{j+1}(x)` where
`φ_k` denotes the `k`-th element of the trigonometric basis. -/
noncomputable def trigLinComb (M : ℕ) (θ : Fin M → ℝ) (x : ℝ) : ℝ :=
  ∑ j : Fin M, θ j * trigBasis (j.val + 1) x

/-- `θhat` is a least-squares estimator for the trigonometric regression: for every
`ω` it minimizes the empirical squared error `∑ (Y_i - φ_θ(i/n))²` over all `θ`. -/
def IsLSEstimator {Ω : Type*} {n M : ℕ}
    (Y : Ω → Fin n → ℝ) (θhat : Ω → Fin M → ℝ) : Prop :=
  ∀ ω θ,
    ∑ i : Fin n, (Y ω i - trigLinComb M (θhat ω) ((i : ℝ) / (n : ℝ))) ^ 2 ≤
    ∑ i : Fin n, (Y ω i - trigLinComb M θ ((i : ℝ) / (n : ℝ))) ^ 2

/-- The `(i,j)` entry of the trigonometric design matrix equals the basis function
`φ_{j+1}` evaluated at the grid point `i/n`. -/
lemma trigDesignMatrix_eq_trigBasis (n M : ℕ) (hn : 0 < n) (i : Fin n) (j : Fin M) :
    trigDesignMatrix n M i j = trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)) := by
  simp only [trigDesignMatrix, trigBasis]
  have hj1 : j.val + 1 ≠ 0 := Nat.succ_ne_zero _
  simp only [hj1, ↓reduceIte]
  by_cases hj1eq : j.val + 1 = 1
  ·
    have hj0 : j.val = 0 := by omega
    simp [hj0]
  ·
    have hjge1 : j.val ≥ 1 := by omega
    simp only [hj1eq, ↓reduceIte]
    by_cases hjmod : j.val = 0
    · omega
    · simp only [show j.val ≠ 0 from hjmod]

      by_cases heven : (j.val + 1) % 2 = 0
      ·
        simp only [heven, ↓reduceIte]


        have hj_odd : j.val % 2 = 1 := by omega
        simp only [hj_odd, ↓reduceIte]


        congr 1
        have : (j.val + 1) / 2 = (j.val + 1) / 2 := rfl
        ring
      ·
        have hodd : (j.val + 1) % 2 = 1 := by omega
        simp only [show ¬((j.val + 1) % 2 = 0) from by omega, ↓reduceIte]


        have hj_even : j.val % 2 = 0 := by omega
        have hj_ne0 : ¬(j.val = 0) := hjmod
        simp only [hj_even]

        push_cast
        ring

/-- Empirical Parseval identity: the squared empirical norm of a trigonometric linear
combination on the uniform grid coincides with the sum of squared coefficients
(using orthonormality from Lemma 3.13). -/
lemma empirical_norm_eq_sum_sq (n M : ℕ) (hn : 0 < n) (hM : M ≤ n - 1)
    (θ : Fin M → ℝ) :
    (1 / (n : ℝ)) * ∑ i : Fin n,
      (∑ j : Fin M, θ j * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ))) ^ 2 =
    ∑ j : Fin M, θ j ^ 2 := by

  have hΦ : ∀ i : Fin n,
      ∑ j : Fin M, θ j * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)) =
      ∑ j : Fin M, trigDesignMatrix n M i j * θ j := by
    intro i
    congr 1; ext j
    rw [trigDesignMatrix_eq_trigBasis n M hn i j]; ring
  simp_rw [hΦ]


  set Φ := trigDesignMatrix n M
  have hmv : ∀ i, ∑ j : Fin M, Φ i j * θ j = (Φ.mulVec θ) i := by
    intro i; simp [Matrix.mulVec, dotProduct]
  simp_rw [hmv]

  have hdot_sum : ∑ i : Fin n, (Φ.mulVec θ i) ^ 2 =
      dotProduct (Φ.mulVec θ) (Φ.mulVec θ) := by
    simp [dotProduct, sq]
  rw [hdot_sum]

  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec]

  rw [lemma_3_13 n M hn hM]

  rw [Matrix.vecMul_smul, Matrix.vecMul_one]

  rw [smul_dotProduct, smul_eq_mul]

  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  field_simp

  simp [dotProduct, sq]

/-- `L²([0,1])` orthonormality of the trigonometric basis `{φ_j}_{j≥1}`:
`∫₀¹ φ_j φ_{j'} dx = 1` if `j = j'` and `0` otherwise. -/
theorem trigBasis_L2_orthonormal (j j' : ℕ) (hj : 0 < j) (hj' : 0 < j') :
    ∫ x in Set.Icc (0 : ℝ) 1, trigBasis j x * trigBasis j' x =
    if j = j' then 1 else 0 :=
  trigBasis_orthonormal j j' hj hj'

/-- `L²([0,1])` Parseval identity for the trigonometric basis: the squared `L²`-norm of
a finite linear combination equals the sum of squared coefficients. -/
lemma L2_norm_eq_sum_sq (M : ℕ) (θ : Fin M → ℝ) :
    L2normSq (fun x => ∑ j : Fin M, θ j * trigBasis (j.val + 1) x) =
    ∑ j : Fin M, θ j ^ 2 := by
  unfold L2normSq


  have hcont : Continuous (fun x => ∑ j : Fin M, θ j * trigBasis (j.val + 1) x) :=
    continuous_finset_sum _ (fun j _ => continuous_const.mul
      (by unfold trigBasis; split_ifs <;> fun_prop))
  have hint : IntegrableOn (fun x =>
      (∑ j : Fin M, θ j * trigBasis (j.val + 1) x) ^ 2) (Set.Icc 0 1) :=
    (hcont.pow 2).continuousOn.integrableOn_compact isCompact_Icc

  simp_rw [sq, Finset.sum_mul_sum]

  have hint_prod : ∀ j j' : Fin M,
      IntegrableOn (fun x => θ j * trigBasis (j.val + 1) x * (θ j' * trigBasis (j'.val + 1) x))
        (Set.Icc 0 1) :=
    fun j j' => ((continuous_const.mul
      (by unfold trigBasis; split_ifs <;> fun_prop)).mul
      (continuous_const.mul
      (by unfold trigBasis; split_ifs <;> fun_prop))).continuousOn.integrableOn_compact isCompact_Icc

  rw [integral_finset_sum _ (fun j _ =>
    integrable_finset_sum _ (fun j' _ => hint_prod j j'))]

  congr 1; ext j
  rw [integral_finset_sum _ (fun j' _ => hint_prod j j')]

  simp_rw [show ∀ (j' : Fin M) (x : ℝ),
    θ j * trigBasis (j.val + 1) x * (θ j' * trigBasis (j'.val + 1) x) =
    θ j * θ j' * (trigBasis (j.val + 1) x * trigBasis (j'.val + 1) x)
    from by intros; ring]
  simp_rw [integral_const_mul]
  simp_rw [trigBasis_L2_orthonormal _ _ (Nat.succ_pos _) (Nat.succ_pos _)]

  simp_rw [Nat.succ_inj, Fin.val_injective.eq_iff]
  simp

/-- Bridge between empirical and `L²` norms (Property ORT): for `M ≤ n - 1`, the squared
`L²`-norm of a trigonometric linear combination equals its squared empirical norm on the
uniform grid `{i/n}`. -/
theorem ORT_L2_eq_empirical_normSq
    (n M : ℕ) (hn : 0 < n) (hM : M ≤ n - 1) (θ : Fin M → ℝ) :
    L2normSq (fun x => ∑ j : Fin M, θ j * trigBasis (j.val + 1) x) =
    (1 / (n : ℝ)) * ∑ i : Fin n,
      (∑ j : Fin M, θ j * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ))) ^ 2 := by

  rw [L2_norm_eq_sum_sq, empirical_norm_eq_sum_sq n M hn hM]

/-- The trigonometric linear combination evaluated on the uniform grid coincides with the
matrix-vector product of the design matrix and the coefficient vector. -/
lemma trigLinComb_eq_mulVec (n M : ℕ) (hn : 0 < n) (θ : Fin M → ℝ) (i : Fin n) :
    trigLinComb M θ ((i : ℝ) / (n : ℝ)) = (trigDesignMatrix n M).mulVec θ i := by
  simp only [trigLinComb, Matrix.mulVec, dotProduct]
  congr 1; ext j
  rw [trigDesignMatrix_eq_trigBasis n M hn i j]; ring

/-- Re-indexing a `Finset.range M` sum as a sum over `Fin M`. -/
lemma finset_range_eq_fin_sum (M : ℕ) (θstar : ℕ → ℝ) (x : ℝ) :
    ∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x =
    ∑ j : Fin M, θstar j.val * trigBasis (j.val + 1) x := by
  rw [← Finset.sum_range (fun j => θstar j * trigBasis (j + 1) x)]

/-- The squared empirical norm of a difference of two trigonometric linear combinations
equals the sum of squared coefficient differences. -/
lemma empirical_diff_eq_coeff_sq
    (n M : ℕ) (hn : 0 < n) (hM : M ≤ n - 1)
    (θ₁ θ₂ : Fin M → ℝ) :
    (1 / (n : ℝ)) * ∑ i : Fin n,
      (∑ j : Fin M, θ₁ j * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)) -
       ∑ j : Fin M, θ₂ j * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ))) ^ 2 =
    ∑ j : Fin M, (θ₁ j - θ₂ j) ^ 2 := by

  have hdiff : ∀ i : Fin n,
      ∑ j : Fin M, θ₁ j * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)) -
      ∑ j : Fin M, θ₂ j * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)) =
      ∑ j : Fin M, (θ₁ j - θ₂ j) * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)) := by
    intro i
    rw [← Finset.sum_sub_distrib]
    congr 1; ext j; ring
  simp_rw [hdiff]
  exact empirical_norm_eq_sum_sq n M hn hM (θ₁ - θ₂)

/-- Each column of the trigonometric design matrix has squared norm equal to `n` on the
uniform grid (follows from Lemma 3.13). -/
lemma trigBasis_col_sq_sum (n M : ℕ) (hn : 0 < n) (hM : M ≤ n - 1) (j : Fin M) :
    ∑ i : Fin n, (trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ))) ^ 2 = (n : ℝ) := by

  have h_eq : ∀ i : Fin n,
      trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)) = trigDesignMatrix n M i j :=
    fun i => (trigDesignMatrix_eq_trigBasis n M hn i j).symm
  simp_rw [h_eq]


  have h_ort := lemma_3_13 n M hn hM
  have h_entry := congr_fun (congr_fun h_ort j) j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul] at h_entry
  simp only [if_true] at h_entry
  simp_rw [sq]
  linarith

/-- Complement form of a sub-Gaussian `χ²` tail bound: for `M` coordinatewise sub-Gaussian
random variables `Z_j` with variance proxy `v`, the probability that
`∑ Z_j² > 4 M v (M + log(1/δ))` is at most `δ`. -/
theorem subG_chi2_complement_bound
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : ℕ) (hM_pos : 0 < M)
    (Z : Fin M → Ω → ℝ)
    (v : ℝ) (hv : 0 < v)
    (hZ_subG : ∀ j : Fin M, ∀ s : ℝ,
      ∫ ω, Real.exp (s * Z j ω) ∂μ ≤ Real.exp (v * s ^ 2 / 2))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    μ {ω | 4 * (↑M : ℝ) * v * ((↑M : ℝ) + Real.log (1 / δ)) <
        ∑ j : Fin M, (Z j ω) ^ 2} ≤ ENNReal.ofReal δ := by sorry

/-- Sub-Gaussian `χ²` concentration inequality: with high probability `1 - δ`,
`∑_{j} Z_j² ≤ C v (M + log(1/δ))` for some absolute constant `C`. -/
theorem subG_chi2_concentration_ch2
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (M : ℕ) (hM_pos : 0 < M)
    (Z : Fin M → Ω → ℝ)
    (v : ℝ) (hv : 0 < v)
    (hZ_subG : ∀ j : Fin M, ∀ s : ℝ,
      ∫ ω, Real.exp (s * Z j ω) ∂μ ≤ Real.exp (v * s ^ 2 / 2)) :
    ∃ (C_chi2 : ℝ), 0 < C_chi2 ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
      μ {ω | ∑ j : Fin M, (Z j ω) ^ 2 ≤
          C_chi2 * v * ((M : ℝ) + Real.log (1 / δ))} ≥
        ENNReal.ofReal (1 - δ) := by
  refine ⟨4 * ↑M, by positivity, fun δ hδ hδ1 => ?_⟩

  have hcompl := subG_chi2_complement_bound M hM_pos Z v hv hZ_subG δ hδ hδ1

  set S := {ω : Ω | ∑ j : Fin M, (Z j ω) ^ 2 ≤
      4 * (↑M : ℝ) * v * ((↑M : ℝ) + Real.log (1 / δ))}
  have hSc_le : μ Sᶜ ≤ ENNReal.ofReal δ := by
    show μ {ω | ω ∉ S} ≤ _
    convert hcompl using 2; ext ω; simp [S, not_le]

  rw [ge_iff_le]
  have h1 : (1 : ENNReal) ≤ μ S + μ Sᶜ := by
    calc (1 : ENNReal) = μ Set.univ := measure_univ.symm
      _ = μ (S ∪ Sᶜ) := by rw [Set.union_compl_self]
      _ ≤ μ S + μ Sᶜ := measure_union_le S Sᶜ
  calc ENNReal.ofReal (1 - δ)
      ≤ 1 - ENNReal.ofReal δ := by
        rw [show (1 : ENNReal) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
            ← ENNReal.ofReal_sub 1 hδ.le]
    _ ≤ 1 - μ Sᶜ := tsub_le_tsub_left hSc_le _
    _ ≤ μ S := by rw [tsub_le_iff_right]; exact h1

/-- The coordinates `θhat_j - θbar_j` of the least-squares estimator are sub-Gaussian with
variance proxy of order `σ²/n`. -/
theorem ls_coeff_subG_mgf_ch2
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    (M : ℕ) (hM_pos : 0 < M) (hM_le : M ≤ n - 1)
    (σ : ℝ) (hσ : 0 < σ)
    (ε : Ω → Fin n → ℝ)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
    (f : ℝ → ℝ)
    (Y : Ω → Fin n → ℝ)
    (hModel : ∀ ω i, Y ω i = f ((i : ℝ) / (n : ℝ)) + ε ω i)
    (θhat : Ω → Fin M → ℝ)
    (hLS : IsLSEstimator Y θhat)
    (θbar : Fin M → ℝ)
    (hθbar : ∀ j : Fin M, θbar j = (1 / (n : ℝ)) *
      ∑ i : Fin n, f ((i : ℝ) / (n : ℝ)) * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ))) :
    ∃ (C₀ : ℝ), 0 < C₀ ∧
      ∀ j : Fin M, ∀ s : ℝ,
        ∫ ω, Real.exp (s * (θhat ω j - θbar j)) ∂μ ≤
          Real.exp (C₀ * (σ ^ 2 / (n : ℝ)) * s ^ 2 / 2) := by sorry

/-- Concentration for the LS coefficients: with probability `≥ 1 - δ`,
`∑_j (θ̂_j - θ̄_j)² ≲ σ² (M + log(1/δ)) / n`. -/
theorem subG_trig_concentration
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    (M : ℕ) (hM_pos : 0 < M) (hM_le : M ≤ n - 1)
    (σ : ℝ) (hσ : 0 < σ) (hσ_le : σ ^ 2 ≤ 1)
    (ε : Ω → Fin n → ℝ)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
    (f : ℝ → ℝ)
    (Y : Ω → Fin n → ℝ)
    (hModel : ∀ ω i, Y ω i = f ((i : ℝ) / (n : ℝ)) + ε ω i)
    (θhat : Ω → Fin M → ℝ)
    (hLS : IsLSEstimator Y θhat)
    (θbar : Fin M → ℝ)
    (hθbar : ∀ j : Fin M, θbar j = (1 / (n : ℝ)) *
      ∑ i : Fin n, f ((i : ℝ) / (n : ℝ)) * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ))) :
    ∃ (C_conc : ℝ), 0 < C_conc ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
    μ {ω | ∑ j : Fin M, (θhat ω j - θbar j) ^ 2 ≤
        C_conc * σ ^ 2 * ((M : ℝ) + Real.log (1 / δ)) / (n : ℝ)}
      ≥ ENNReal.ofReal (1 - δ) := by

  obtain ⟨C₀, hC₀_pos, hMGF⟩ := ls_coeff_subG_mgf_ch2 hn M hM_pos hM_le σ hσ ε hsubG
    f Y hModel θhat hLS θbar hθbar

  have hv : 0 < C₀ * (σ ^ 2 / (n : ℝ)) := by
    apply mul_pos hC₀_pos
    apply div_pos (sq_pos_of_pos hσ)
    exact Nat.cast_pos.mpr hn
  obtain ⟨C_chi2, hC_chi2_pos, hConc⟩ :=
    subG_chi2_concentration_ch2 M hM_pos
      (fun j ω => θhat ω j - θbar j) (C₀ * (σ ^ 2 / (n : ℝ))) hv hMGF

  refine ⟨C_chi2 * C₀, mul_pos hC_chi2_pos hC₀_pos, fun δ hδ hδ1 => ?_⟩


  have hkey := hConc δ hδ hδ1
  apply le_trans hkey
  apply MeasureTheory.measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have : C_chi2 * (C₀ * (σ ^ 2 / (↑n : ℝ))) * ((↑M : ℝ) + Real.log (1 / δ)) =
    C_chi2 * C₀ * σ ^ 2 * ((↑M : ℝ) + Real.log (1 / δ)) / (↑n : ℝ) := by
    field_simp
  linarith

/-- Oracle inequality, empirical form: with probability `≥ 1 - δ`, the squared empirical
distance between the LS fit and the truncated Fourier series of `f` is bounded by
`C₁ (n^{1-2β} + σ²(M + log(1/δ))/n)`. -/
theorem oracle_ineq_empirical_form
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    (β : ℝ) (hβ_pos : 0 < β)
    (Q : ℝ) (hQ : 0 < Q)
    (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (hθstar : ∀ j, θstar j = fourierCoeff f j)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
    (σ : ℝ) (hσ : 0 < σ) (hσ_le : σ ^ 2 ≤ 1)
    (ε : Ω → Fin n → ℝ)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
    (Y : Ω → Fin n → ℝ)
    (hModel : ∀ ω i, Y ω i = f ((i : ℝ) / (n : ℝ)) + ε ω i)
    (M : ℕ) (hM_pos : 0 < M) (hM_le : M ≤ n - 1)
    (θhat : Ω → Fin M → ℝ)
    (hLS : IsLSEstimator Y θhat)
    (hθstar_emp : ∀ j : Fin M, θstar j.val = (1 / (n : ℝ)) *
      ∑ i : Fin n, f ((i : ℝ) / (n : ℝ)) * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ))) :
    ∃ (C₁ : ℝ), 0 < C₁ ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
    μ {ω | (1 / (n : ℝ)) * ∑ i : Fin n,
          (trigLinComb M (θhat ω) ((i : ℝ) / (n : ℝ)) -
           ∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) ((i : ℝ) / (n : ℝ))) ^ 2 ≤
          C₁ * ((n : ℝ) ^ (1 - 2 * β) +
                σ ^ 2 * ((M : ℝ) + Real.log (1 / δ)) / (n : ℝ))}
      ≥ ENNReal.ofReal (1 - δ) := by

  set θbar : Fin M → ℝ := fun j => θstar j.val

  obtain ⟨C_conc, hC_conc_pos, hConc⟩ := subG_trig_concentration hn M hM_pos hM_le
    σ hσ hσ_le ε hsubG f Y hModel θhat hLS θbar hθstar_emp


  have hNorm_eq : ∀ ω, (1 / (n : ℝ)) * ∑ i : Fin n,
      (trigLinComb M (θhat ω) ((i : ℝ) / (n : ℝ)) -
       ∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) ((i : ℝ) / (n : ℝ))) ^ 2 =
      ∑ j : Fin M, (θhat ω j - θbar j) ^ 2 := by
    intro ω

    simp_rw [trigLinComb, finset_range_eq_fin_sum]

    exact empirical_diff_eq_coeff_sq n M hn hM_le (θhat ω) θbar


  refine ⟨C_conc, hC_conc_pos, ?_⟩
  intro δ hδ_pos hδ_le
  apply le_trans (hConc δ hδ_pos hδ_le)
  apply MeasureTheory.measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [hNorm_eq]
  calc ∑ j : Fin M, (θhat ω j - θbar j) ^ 2
      ≤ C_conc * σ ^ 2 * ((M : ℝ) + Real.log (1 / δ)) / (n : ℝ) := hω
    _ ≤ C_conc * ((n : ℝ) ^ (1 - 2 * β) +
          σ ^ 2 * ((M : ℝ) + Real.log (1 / δ)) / (n : ℝ)) := by
        have hbias_nonneg : 0 ≤ (n : ℝ) ^ (1 - 2 * β) := rpow_nonneg (Nat.cast_nonneg _) _
        have hC_nonneg : 0 ≤ C_conc := le_of_lt hC_conc_pos
        have h_expand : C_conc * ((n : ℝ) ^ (1 - 2 * β) + σ ^ 2 * ((M : ℝ) + Real.log (1 / δ)) / (n : ℝ)) =
          C_conc * (n : ℝ) ^ (1 - 2 * β) + C_conc * σ ^ 2 * ((M : ℝ) + Real.log (1 / δ)) / (n : ℝ) := by ring
        linarith [mul_nonneg hC_nonneg hbias_nonneg]

/-- Oracle inequality, `L²` form: using property ORT, the empirical oracle bound transfers
to the `L²` norm — with probability `≥ 1 - δ`,
`‖φ_{θ̂} - φ_{θ*}‖²_{L²} ≤ C₁ (n^{1-2β} + σ²(M + log(1/δ))/n)`. -/
theorem oracle_inequality_L2_form
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    (β : ℝ) (hβ_pos : 0 < β)
    (Q : ℝ) (hQ : 0 < Q)
    (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (hθstar : ∀ j, θstar j = fourierCoeff f j)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
    (σ : ℝ) (hσ : 0 < σ) (hσ_le : σ ^ 2 ≤ 1)
    (ε : Ω → Fin n → ℝ)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
    (Y : Ω → Fin n → ℝ)
    (hModel : ∀ ω i, Y ω i = f ((i : ℝ) / (n : ℝ)) + ε ω i)
    (M : ℕ) (hM_pos : 0 < M) (hM_le : M ≤ n - 1)
    (θhat : Ω → Fin M → ℝ)
    (hLS : IsLSEstimator Y θhat)
    (hθstar_emp : ∀ j : Fin M, θstar j.val = (1 / (n : ℝ)) *
      ∑ i : Fin n, f ((i : ℝ) / (n : ℝ)) * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ))) :
    ∃ (C₁ : ℝ), 0 < C₁ ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
    μ {ω | L2normSq (fun x => trigLinComb M (θhat ω) x -
              ∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) ≤
            C₁ * ((n : ℝ) ^ (1 - 2 * β) +
                  σ ^ 2 * ((M : ℝ) + Real.log (1 / δ)) / (n : ℝ))}
      ≥ ENNReal.ofReal (1 - δ) := by


  obtain ⟨C₁, hC₁_pos, hEmpirical⟩ := oracle_ineq_empirical_form hn β hβ_pos Q hQ f
    θstar hθstar hSobolev σ hσ hσ_le ε hsubG Y hModel M hM_pos hM_le θhat hLS hθstar_emp


  refine ⟨C₁, hC₁_pos, ?_⟩
  intro δ hδ_pos hδ_le

  apply le_trans (hEmpirical δ hδ_pos hδ_le)
  apply MeasureTheory.measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢


  have hDiff : ∀ x, trigLinComb M (θhat ω) x -
      ∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x =
      ∑ j : Fin M, (θhat ω j - θstar j.val) * trigBasis (j.val + 1) x := by
    intro x
    simp only [trigLinComb, Finset.sum_range (fun j => θstar j * trigBasis (j + 1) x)]
    rw [← Finset.sum_sub_distrib]
    congr 1; ext j; ring

  have hL2_eq : L2normSq (fun x => trigLinComb M (θhat ω) x -
      ∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) =
      L2normSq (fun x => ∑ j : Fin M, (θhat ω j - θstar j.val) *
        trigBasis (j.val + 1) x) := by
    unfold L2normSq
    congr 1; ext x; congr 1; exact hDiff x

  rw [hL2_eq, ORT_L2_eq_empirical_normSq n M hn hM_le]


  simp_rw [← hDiff] at *
  exact hω

/-- Auxiliary `L²`-completeness statement: under Sobolev regularity, `f` equals its
Fourier expansion `∑ θ*_j φ_{j+1}(x)` almost everywhere on `[0,1]`. -/
theorem fourier_L2_completeness_aux
    (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (hθstar : ∀ j, θstar j = fourierCoeff f j)
    (β Q : ℝ) (hβ : 0 < β) (hQ : 0 < Q)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
    (hSqSum : Summable (fun j : ℕ => (θstar j) ^ 2)) :
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc (0:ℝ) 1)),
      f x = ∑' j, θstar j * trigBasis (j + 1) x := by sorry

/-- `L²` completeness of the trigonometric basis on `[0,1]` for Sobolev-class functions:
`f(x) = ∑ θ*_j · φ_{j+1}(x)` almost everywhere on `[0,1]`. -/
theorem fourier_L2_completeness
    (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (hθstar : ∀ j, θstar j = fourierCoeff f j)
    (β Q : ℝ) (hβ : 0 < β) (hQ : 0 < Q)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q) :
    ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc (0:ℝ) 1)),
      f x = ∑' j, θstar j * trigBasis (j + 1) x := by

  have hRange : ∀ K, ∑ i ∈ Finset.range K,
      (sobolevCoeff β (↑i + 1)) ^ 2 * (θstar ↑i) ^ 2 ≤ Q := by
    intro K; rw [← Fin.sum_univ_eq_sum_range]; exact hSobolev K
  have hnn : ∀ i, 0 ≤ (sobolevCoeff β (↑i + 1)) ^ 2 * (θstar ↑i) ^ 2 :=
    fun i => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hSummable : Summable (fun j => (sobolevCoeff β (↑j + 1)) ^ 2 * (θstar ↑j) ^ 2) :=
    summable_of_sum_range_le hnn hRange
  have h_tail : Summable (fun j : ℕ => (θstar (j + 1)) ^ 2) := by
    have hsumshift : Summable (fun j =>
        (sobolevCoeff β (↑(j + 1) + 1)) ^ 2 * (θstar ↑(j + 1)) ^ 2) :=
      hSummable.comp_injective (fun a b h => by omega)
    exact Summable.of_nonneg_of_le (fun j => sq_nonneg _)
      (fun j => by
        nlinarith [sq_nonneg (θstar (j + 1)),
                   sobolev_weight_ge_one β hβ (j + 1) (by omega)])
      hsumshift
  have hSqSum : Summable (fun j : ℕ => (θstar j) ^ 2) :=
    (summable_nat_add_iff 1).mp h_tail


  exact fourier_L2_completeness_aux f θstar hθstar β Q hβ hQ hSobolev hSqSum

/-- Truncation tail bound: for a Sobolev-class function with `β > 1/2`, the squared
`L²`-error from truncating the Fourier series at `M` terms is at most `Q · M^{-2β}`. -/
theorem fourier_tail_L2_bound
    (M : ℕ) (hM : 0 < M)
    (β Q : ℝ) (hβ : 1/2 < β) (hQ : 0 < Q)
    (θstar : ℕ → ℝ)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q) :
    L2normSq (fun x => (∑' j, θstar j * trigBasis (j + 1) x) -
      ∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) ≤
      Q * (M : ℝ) ^ (-(2 * β)) := by
  have hβ_pos : 0 < β := by linarith

  have hRange : ∀ K, ∑ i ∈ Finset.range K,
      (sobolevCoeff β (↑i + 1)) ^ 2 * (θstar ↑i) ^ 2 ≤ Q := by
    intro K
    rw [← Fin.sum_univ_eq_sum_range]
    exact hSobolev K

  have hnn : ∀ i, 0 ≤ (sobolevCoeff β (↑i + 1)) ^ 2 * (θstar ↑i) ^ 2 :=
    fun i => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hSummable : Summable (fun j => (sobolevCoeff β (↑j + 1)) ^ 2 * (θstar ↑j) ^ 2) :=
    summable_of_sum_range_le hnn hRange
  have hBound : ∑' j, (sobolevCoeff β (↑j + 1)) ^ 2 * (θstar ↑j) ^ 2 ≤ Q :=
    tsum_le_of_sum_range_le hnn hRange


  have h_tail : Summable (fun j : ℕ => (θstar (j + 1)) ^ 2) := by
    have hsumshift : Summable (fun j =>
        (sobolevCoeff β (j + 1 + 1)) ^ 2 * (θstar (j + 1)) ^ 2) :=
      hSummable.comp_injective (fun a b h => by omega)
    exact Summable.of_nonneg_of_le (fun j => sq_nonneg _)
      (fun j => by
        nlinarith [sq_nonneg (θstar (j + 1)),
                   sobolev_weight_ge_one β hβ_pos (j + 1) (by omega)])
      hsumshift
  have hSqSum : Summable (fun j : ℕ => (θstar j) ^ 2) :=
    (summable_nat_add_iff 1).mp h_tail

  show L2normSq _ ≤ _
  simp only [L2normSq]
  have hAbsSum : Summable θstar := by
    exact summable_of_sobolev hβ θstar ⟨hSummable, hBound⟩
  rw [parseval_truncation_L2_error θstar M hSqSum hAbsSum]


  have hM_pos : (0 : ℝ) < (M : ℝ) := Nat.cast_pos.mpr hM
  have hMinv_pos : (0 : ℝ) < (M : ℝ) ^ (-(2 * β)) := rpow_pos_of_pos hM_pos _

  have h_term : ∀ (j : ↑(Set.Ici M)),
      (θstar ↑j) ^ 2 ≤ (M : ℝ) ^ (-(2 * β)) *
        ((sobolevCoeff β (↑(↑j : ℕ) + 1)) ^ 2 * (θstar ↑j) ^ 2) := by
    intro ⟨j, hj⟩
    simp only [Set.mem_Ici] at hj
    suffices h1 : 1 ≤ (M : ℝ) ^ (-(2 * β)) *
        (sobolevCoeff β (j + 1)) ^ 2 by
      nlinarith [sq_nonneg (θstar j)]
    rw [rpow_neg hM_pos.le, inv_mul_eq_div,
        le_div_iff₀ (rpow_pos_of_pos hM_pos _)]
    simp only [one_mul]
    exact sobolev_weight_ge_rpow β hβ_pos M j hj
  calc ∑' (j : ↑(Set.Ici M)), (θstar ↑j) ^ 2
      _ ≤ ∑' (j : ↑(Set.Ici M)), (M : ℝ) ^ (-(2 * β)) *
          ((sobolevCoeff β (↑(↑j : ℕ) + 1)) ^ 2 * (θstar ↑j) ^ 2) :=
        Summable.tsum_le_tsum h_term (hSqSum.subtype _)
          ((Summable.mul_left _ hSummable).subtype _)
      _ = (M : ℝ) ^ (-(2 * β)) *
          ∑' (j : ↑(Set.Ici M)),
            ((sobolevCoeff β (↑(↑j : ℕ) + 1)) ^ 2 * (θstar ↑j) ^ 2) :=
        tsum_mul_left
      _ ≤ (M : ℝ) ^ (-(2 * β)) *
          ∑' j : ℕ, (sobolevCoeff β (j + 1)) ^ 2 * (θstar j) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hMinv_pos.le
        exact Summable.tsum_subtype_le _ _
          (fun j => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hSummable
      _ ≤ (M : ℝ) ^ (-(2 * β)) * Q :=
        mul_le_mul_of_nonneg_left hBound hMinv_pos.le
      _ = Q * (M : ℝ) ^ (-(2 * β)) := mul_comm ..

/-- Approximation error in `L²`-form: the squared `L²` distance between the truncated
Fourier expansion at `M` terms and the true function `f` is at most `Q · M^{-2β}`. -/
theorem approx_error_L2_form
    (M : ℕ) (hM : 0 < M)
    (β Q : ℝ) (hβ : 1/2 < β) (hQ : 0 < Q)
    (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (hθstar : ∀ j, θstar j = fourierCoeff f j)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q) :
    L2normSq (fun x => (∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) - f x) ≤
      Q * (M : ℝ) ^ (-(2 * β)) := by


  have hβ_pos : 0 < β := by linarith
  have hComplete := fourier_L2_completeness f θstar hθstar β Q hβ_pos hQ hSobolev
  have hTail := fourier_tail_L2_bound M hM β Q hβ hQ θstar hSobolev


  set S := fun x => ∑' j, θstar j * trigBasis (j + 1) x
  set P := fun x => ∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x


  have hL2_rewrite : L2normSq (fun x => P x - f x) ≤
      L2normSq (fun x => S x - P x) := by


    unfold L2normSq
    have hae2 : ∀ᵐ x ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Icc (0:ℝ) 1)),
        (P x - f x) ^ 2 = (S x - P x) ^ 2 := by
      filter_upwards [hComplete] with x hx
      simp only [hx, S]; ring
    exact le_of_eq (MeasureTheory.integral_congr_ae hae2)
  exact le_trans hL2_rewrite hTail

/-- Square integrability of the approximation error: under mild regularity of `f`, the
squared difference between the truncated Fourier sum and `f` is integrable on `[0,1]`. -/
theorem approx_error_integrableOn
    (M : ℕ) (_hM : 0 < M)
    (β Q : ℝ) (_hβ : 0 < β) (_hQ : 0 < Q)
    (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (_hθstar : ∀ j, θstar j = fourierCoeff f j)
    (_hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
    (hf_meas : Measurable f)
    (hf_sq_int : IntegrableOn (fun x => f x ^ 2) (Set.Icc 0 1)) :
    IntegrableOn (fun x =>
      ((∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) - f x) ^ 2)
      (Set.Icc 0 1) := by

  have continuous_trigBasis : ∀ j : ℕ, Continuous (trigBasis j) := by
    intro j; unfold trigBasis; split_ifs <;> fun_prop
  have hsum_cont : Continuous (fun x =>
      ∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) :=
    continuous_finset_sum _ (fun j _ => continuous_const.mul (continuous_trigBasis _))
  have hdiff_meas : Measurable (fun x =>
      (∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) - f x) :=
    hsum_cont.measurable.sub hf_meas
  have hbound : ∀ x : ℝ,
      ((∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) - f x) ^ 2 ≤
      2 * ((∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) ^ 2 + f x ^ 2) := by
    intro x; nlinarith [sq_nonneg ((∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) + f x)]
  have hsum_sq_int : IntegrableOn (fun x =>
      (∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) ^ 2) (Set.Icc 0 1) :=
    (hsum_cont.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hbnd_int : IntegrableOn (fun x =>
      2 * ((∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) ^ 2 + f x ^ 2))
      (Set.Icc 0 1) := (hsum_sq_int.add hf_sq_int).const_mul 2
  exact Integrable.mono' hbnd_int
    ((hdiff_meas.pow_const 2).aestronglyMeasurable.restrict)
    (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hbound x))

/-- Triangle-like inequality for the squared `L²`-norm: `‖g+h‖² ≤ 2(‖g‖² + ‖h‖²)`. -/
lemma L2normSq_add_le (g h : ℝ → ℝ)
    (hg : IntegrableOn (fun x => g x ^ 2) (Set.Icc 0 1))
    (hh : IntegrableOn (fun x => h x ^ 2) (Set.Icc 0 1)) :
    L2normSq (fun x => g x + h x) ≤ 2 * (L2normSq g + L2normSq h) := by
  unfold L2normSq; simp only
  have key : ∀ x : ℝ, (g x + h x) ^ 2 ≤ 2 * (g x ^ 2 + h x ^ 2) := by
    intro x; nlinarith [sq_nonneg (g x - h x)]
  have hgh_int : IntegrableOn (fun x => g x ^ 2 + h x ^ 2) (Set.Icc 0 1) := hg.add hh
  have step1 : ∫ x in Set.Icc (0:ℝ) 1, (g x + h x) ^ 2 ≤
      ∫ x in Set.Icc (0:ℝ) 1, 2 * (g x ^ 2 + h x ^ 2) := by
    apply integral_mono_of_nonneg
    · exact ae_of_all _ (fun x => sq_nonneg (g x + h x))
    · exact hgh_int.const_mul 2
    · exact ae_of_all _ key
  have step2a : ∫ x in Set.Icc (0:ℝ) 1, 2 * (g x ^ 2 + h x ^ 2) =
      2 * (∫ x in Set.Icc (0:ℝ) 1, (g x ^ 2 + h x ^ 2)) := by
    rw [show (fun x => 2 * (g x ^ 2 + h x ^ 2)) = (fun x => (2 : ℝ) • (g x ^ 2 + h x ^ 2))
      from by ext x; simp [mul_comm]]
    rw [integral_smul (2 : ℝ)]
    simp [smul_eq_mul]
  have step2b : (∫ x in Set.Icc (0:ℝ) 1, (g x ^ 2 + h x ^ 2)) =
      (∫ x in Set.Icc (0:ℝ) 1, g x ^ 2) + (∫ x in Set.Icc (0:ℝ) 1, h x ^ 2) :=
    integral_add hg hh
  linarith

/-- Intermediate combined bound: with probability `≥ 1 - δ`,
`‖φ_{θ̂} - f‖²_{L²} ≤ C (M^{-2β} + n^{1-2β} + (M + σ² log(1/δ))/n)`,
obtained by combining the oracle inequality with the approximation error bound. -/
theorem thm_3_15_combined_intermediate
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    (β : ℝ) (hβ_pos : 1/2 < β)
    (Q : ℝ) (hQ : 0 < Q)
    (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (hθstar : ∀ j, θstar j = fourierCoeff f j)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
    (σ : ℝ) (hσ : 0 < σ) (hσ_le : σ ^ 2 ≤ 1)
    (ε : Ω → Fin n → ℝ)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
    (Y : Ω → Fin n → ℝ)
    (hModel : ∀ ω i, Y ω i = f ((i : ℝ) / (n : ℝ)) + ε ω i)
    (M : ℕ) (hM_pos : 0 < M) (hM_le : M ≤ n - 1)
    (θhat : Ω → Fin M → ℝ)
    (hLS : IsLSEstimator Y θhat)
    (hθstar_emp : ∀ j : Fin M, θstar j.val = (1 / (n : ℝ)) *
      ∑ i : Fin n, f ((i : ℝ) / (n : ℝ)) * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)))
    (hf_meas : Measurable f)
    (hf_sq_int : IntegrableOn (fun x => f x ^ 2) (Set.Icc 0 1)) :
    ∃ (C : ℝ), 0 < C ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
    μ {ω | L2normSq (fun x => trigLinComb M (θhat ω) x - f x) ≤
            C * ((M : ℝ) ^ (-(2 * β)) + (n : ℝ) ^ (1 - 2 * β) +
                  ((M : ℝ) + σ ^ 2 * Real.log (1 / δ)) / (n : ℝ))}
      ≥ ENNReal.ofReal (1 - δ) := by


  have hβ_pos' : 0 < β := by linarith
  obtain ⟨C₁, hC₁_pos, hOracle⟩ := oracle_inequality_L2_form hn β hβ_pos' Q hQ f
    θstar hθstar hSobolev σ hσ hσ_le ε hsubG Y hModel M hM_pos hM_le θhat hLS hθstar_emp


  set C := max (2 * C₁) (max (2 * Q) 1) with hC_def
  refine ⟨C, by positivity, ?_⟩
  intro δ hδ_pos hδ_le

  apply le_trans (hOracle δ hδ_pos hδ_le)
  apply MeasureTheory.measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢


  set g := fun x => trigLinComb M (θhat ω) x -
    ∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x
  set h := fun x => (∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x) - f x
  have hFunc_eq : (fun x => trigLinComb M (θhat ω) x - f x) = (fun x => g x + h x) := by
    ext x; simp only [g, h]; ring


  have continuous_trigBasis : ∀ j : ℕ, Continuous (trigBasis j) := by
    intro j; unfold trigBasis; split_ifs <;> fun_prop
  have hg_cont : Continuous g := by
    show Continuous (fun x => trigLinComb M (θhat ω) x -
      ∑ j ∈ Finset.range M, θstar j * trigBasis (j + 1) x)
    apply Continuous.sub
    · exact continuous_finset_sum _ (fun j _ => continuous_const.mul (continuous_trigBasis _))
    · exact continuous_finset_sum _ (fun j _ => continuous_const.mul (continuous_trigBasis _))
  have hg_int : IntegrableOn (fun x => g x ^ 2) (Set.Icc 0 1) :=
    (hg_cont.pow 2).continuousOn.integrableOn_compact isCompact_Icc


  have hh_int : IntegrableOn (fun x => h x ^ 2) (Set.Icc 0 1) :=
    approx_error_integrableOn M hM_pos β Q hβ_pos' hQ f θstar hθstar hSobolev hf_meas hf_sq_int
  have hTriangle := L2normSq_add_le g h hg_int hh_int

  have hApprox := approx_error_L2_form M hM_pos β Q hβ_pos hQ f θstar hθstar hSobolev


  have step1 : L2normSq g + L2normSq h ≤
      C₁ * ((n : ℝ) ^ (1 - 2 * β) + σ ^ 2 * ((M : ℝ) + Real.log (1 / δ)) / (n : ℝ)) +
      Q * (M : ℝ) ^ (-(2 * β)) := add_le_add hω hApprox

  have step3 : L2normSq (fun x => trigLinComb M (θhat ω) x - f x) ≤
      2 * (C₁ * ((n : ℝ) ^ (1 - 2 * β) + σ ^ 2 * ((M : ℝ) + Real.log (1 / δ)) / (n : ℝ)) +
           Q * (M : ℝ) ^ (-(2 * β))) := by
    rw [hFunc_eq]
    exact le_trans hTriangle (by linarith [step1])


  have hC_ge_2C₁ : C ≥ 2 * C₁ := le_max_left _ _
  have hC_ge_2Q : C ≥ 2 * Q := le_trans (le_max_left _ _) (le_max_right _ _)

  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hlog_nn : 0 ≤ Real.log (1 / δ) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ_pos]; linarith)
  have hM_nn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M

  have hσ_bound : σ ^ 2 * ((M : ℝ) + Real.log (1 / δ)) ≤
      (M : ℝ) + σ ^ 2 * Real.log (1 / δ) := by
    have : σ ^ 2 * ((M : ℝ) + Real.log (1 / δ)) =
        σ ^ 2 * (M : ℝ) + σ ^ 2 * Real.log (1 / δ) := by ring
    rw [this]
    have : σ ^ 2 * (M : ℝ) ≤ (M : ℝ) := by nlinarith [hσ_le, hM_nn]
    linarith

  have hσ_div : σ ^ 2 * ((M : ℝ) + Real.log (1 / δ)) / (n : ℝ) ≤
      ((M : ℝ) + σ ^ 2 * Real.log (1 / δ)) / (n : ℝ) :=
    div_le_div_of_nonneg_right hσ_bound hn_pos.le

  have oracle_le : 2 * C₁ * ((n : ℝ) ^ (1 - 2 * β) +
      σ ^ 2 * ((M : ℝ) + Real.log (1 / δ)) / (n : ℝ)) ≤
      C * ((n : ℝ) ^ (1 - 2 * β) + ((M : ℝ) + σ ^ 2 * Real.log (1 / δ)) / (n : ℝ)) := by
    have h1 : 0 ≤ (n : ℝ) ^ (1 - 2 * β) := rpow_nonneg hn_pos.le _
    have h2 : 0 ≤ σ ^ 2 * ((M : ℝ) + Real.log (1 / δ)) / (n : ℝ) :=
      div_nonneg (mul_nonneg (sq_nonneg σ) (by linarith [hlog_nn, hM_nn])) hn_pos.le
    have h3 : 0 ≤ ((M : ℝ) + σ ^ 2 * Real.log (1 / δ)) / (n : ℝ) :=
      div_nonneg (by nlinarith [sq_nonneg σ, hlog_nn, hM_nn]) hn_pos.le
    calc 2 * C₁ * ((n : ℝ) ^ (1 - 2 * β) + σ ^ 2 * ((M : ℝ) + Real.log (1 / δ)) / (n : ℝ))
        ≤ 2 * C₁ * ((n : ℝ) ^ (1 - 2 * β) + ((M : ℝ) + σ ^ 2 * Real.log (1 / δ)) / (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          linarith
      _ ≤ C * ((n : ℝ) ^ (1 - 2 * β) + ((M : ℝ) + σ ^ 2 * Real.log (1 / δ)) / (n : ℝ)) := by
          apply mul_le_mul_of_nonneg_right hC_ge_2C₁
          linarith

  have hM_rpow_nn : 0 ≤ (M : ℝ) ^ (-(2 * β)) := rpow_nonneg hM_nn _
  have approx_le : 2 * Q * (M : ℝ) ^ (-(2 * β)) ≤ C * (M : ℝ) ^ (-(2 * β)) :=
    mul_le_mul_of_nonneg_right hC_ge_2Q hM_rpow_nn

  calc L2normSq (fun x => trigLinComb M (θhat ω) x - f x)
      ≤ 2 * (C₁ * ((n : ℝ) ^ (1 - 2 * β) + σ ^ 2 * ((M : ℝ) + Real.log (1 / δ)) / (n : ℝ)) +
           Q * (M : ℝ) ^ (-(2 * β))) := step3
    _ = 2 * C₁ * ((n : ℝ) ^ (1 - 2 * β) + σ ^ 2 * ((M : ℝ) + Real.log (1 / δ)) / (n : ℝ)) +
        2 * Q * (M : ℝ) ^ (-(2 * β)) := by ring
    _ ≤ C * ((n : ℝ) ^ (1 - 2 * β) + ((M : ℝ) + σ ^ 2 * Real.log (1 / δ)) / (n : ℝ)) +
        C * (M : ℝ) ^ (-(2 * β)) := add_le_add oracle_le approx_le
    _ = C * ((M : ℝ) ^ (-(2 * β)) + (n : ℝ) ^ (1 - 2 * β) +
            ((M : ℝ) + σ ^ 2 * Real.log (1 / δ)) / (n : ℝ)) := by ring

/-- Rate computation: for `β ≥ (1+√5)/4` and the optimal choice `M ≈ n^{1/(2β+1)}`,
the upper bound `M^{-2β} + n^{1-2β} + (M + σ² log(1/δ))/n` simplifies to the
minimax rate `n^{-2β/(2β+1)} + σ² log(1/δ)/n` up to constants. -/
lemma thm_3_15_rate_computation
    (n : ℕ) (hn : 0 < n)
    (β : ℝ) (hβ_pos : 0 < β)
    (hβ_lower : β ≥ (1 + Real.sqrt 5) / 4)
    (M : ℕ) (_hM_pos : 0 < M)
    (hM_choice : (n : ℝ) ^ ((1 : ℝ) / (2 * β + 1)) ≤ (M : ℝ) ∧
                 (M : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / (2 * β + 1)) + 1)
    (σ : ℝ) (_hσ : 0 < σ) :
    ∃ (C' : ℝ), 0 < C' ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
    (M : ℝ) ^ (-(2 * β)) + (n : ℝ) ^ (1 - 2 * β) +
      ((M : ℝ) + σ ^ 2 * Real.log (1 / δ)) / (n : ℝ) ≤
    C' * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) +
    C' * σ ^ 2 * Real.log (1 / δ) / (n : ℝ) := by

  refine ⟨4, by norm_num, ?_⟩
  intro δ hδ_pos hδ_le
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h2β1_pos : (0 : ℝ) < 2 * β + 1 := by linarith
  have hMn_lb := hM_choice.1
  have hMn_ub := hM_choice.2
  set rate := (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) with rate_def
  set tail := σ ^ 2 * Real.log (1 / δ) / (n : ℝ) with tail_def

  have h1 : (M : ℝ) ^ (-(2 * β)) ≤ rate := by
    have hn1 : 0 < (n : ℝ) ^ ((1:ℝ) / (2*β+1)) := rpow_pos_of_pos hn_pos _
    calc (M : ℝ) ^ (-(2*β))
        ≤ ((n : ℝ) ^ ((1:ℝ) / (2*β+1))) ^ (-(2*β)) :=
          rpow_le_rpow_of_nonpos hn1 hMn_lb (by linarith)
      _ = rate := by rw [rate_def, ← rpow_mul hn_pos.le]; ring_nf


  have h2 : (n : ℝ) ^ (1 - 2 * β) ≤ rate := by
    rw [rate_def]
    apply rpow_le_rpow_of_exponent_le hn_ge1
    rw [le_div_iff₀ h2β1_pos]
    have h4β : 4 * β - 1 ≥ Real.sqrt 5 := by linarith
    have h4βsq : (4 * β - 1) ^ 2 ≥ (Real.sqrt 5) ^ 2 :=
      sq_le_sq' (by linarith [Real.sqrt_nonneg 5]) h4β
    rw [Real.sq_sqrt (show (5:ℝ) ≥ 0 by norm_num)] at h4βsq
    nlinarith [h4βsq]


  have h3 : (M : ℝ) / (n : ℝ) ≤ 2 * rate := by
    have step1 : (M : ℝ) / (n : ℝ) ≤ ((n : ℝ) ^ ((1:ℝ) / (2*β+1)) + 1) / (n : ℝ) :=
      div_le_div_of_nonneg_right hMn_ub hn_pos.le
    rw [add_div] at step1
    have key1 : (n : ℝ) ^ ((1:ℝ) / (2*β+1)) / (n : ℝ) = rate := by
      rw [rate_def, div_eq_mul_inv, ← rpow_neg_one (n : ℝ), ← rpow_add hn_pos]
      congr 1; field_simp; ring
    have key2 : 1 / (n : ℝ) ≤ rate := by
      rw [one_div, ← rpow_neg_one (n : ℝ), rate_def]
      apply rpow_le_rpow_of_exponent_le hn_ge1
      rw [neg_div, neg_le_neg_iff, div_le_one h2β1_pos]
      linarith
    linarith [step1, key1, key2]

  have hsplit : ((M : ℝ) + σ ^ 2 * Real.log (1 / δ)) / (n : ℝ) =
      (M : ℝ) / (n : ℝ) + tail := by rw [tail_def, add_div]
  rw [hsplit]
  have htail_nn : 0 ≤ tail := by
    rw [tail_def]
    exact div_nonneg (mul_nonneg (sq_nonneg σ)
      (Real.log_nonneg (by rw [le_div_iff₀ hδ_pos]; linarith))) hn_pos.le
  have hrhs : 4 * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) +
      4 * σ ^ 2 * Real.log (1 / δ) / (n : ℝ) = 4 * rate + 4 * tail := by
    rw [rate_def, tail_def]; ring
  rw [hrhs]
  linarith

/-- High-probability part of Theorem 3.15: for `β ≥ (1+√5)/4`, Sobolev class `Θ(β, Q)`,
sub-Gaussian noise with `σ² ≤ 1`, and `M ≈ n^{1/(2β+1)}`, the LS estimator with
trigonometric basis satisfies, with probability at least `1 - δ`,
`‖φ_{θ̂^{LS}} - f‖²_{L²} ≤ C n^{-2β/(2β+1)} + C σ² log(1/δ)/n`. -/
theorem thm_3_15_high_prob
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)

    (β : ℝ) (hβ_pos : 0 < β)
    (hβ_lower : β ≥ (1 + Real.sqrt 5) / 4)
    (Q : ℝ) (hQ : 0 < Q)

    (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (hθstar : ∀ j, θstar j = fourierCoeff f j)

    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)

    (σ : ℝ) (hσ : 0 < σ) (hσ_le : σ ^ 2 ≤ 1)
    (ε : Ω → Fin n → ℝ)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)

    (Y : Ω → Fin n → ℝ)
    (hModel : ∀ ω i, Y ω i = f ((i : ℝ) / (n : ℝ)) + ε ω i)

    (M : ℕ) (hM_pos : 0 < M) (hM_le : M ≤ n - 1)
    (hM_choice : (n : ℝ) ^ ((1 : ℝ) / (2 * β + 1)) ≤ (M : ℝ) ∧
                 (M : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / (2 * β + 1)) + 1)

    (θhat : Ω → Fin M → ℝ)
    (hLS : IsLSEstimator Y θhat)
    (hθstar_emp : ∀ j : Fin M, θstar j.val = (1 / (n : ℝ)) *
      ∑ i : Fin n, f ((i : ℝ) / (n : ℝ)) * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)))

    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (hf_meas : Measurable f)
    (hf_sq_int : IntegrableOn (fun x => f x ^ 2) (Set.Icc 0 1)) :

    ∃ (C : ℝ), 0 < C ∧
    μ {ω | L2normSq (fun x => trigLinComb M (θhat ω) x - f x) ≤
            C * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) +
            C * σ ^ 2 * Real.log (1 / δ) / (n : ℝ)}
      ≥ ENNReal.ofReal (1 - δ) := by


  have hβ_half : 1/2 < β := by
    have : Real.sqrt 5 > 1 := by
      rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  obtain ⟨C₁, hC₁_pos, hC₁_bound⟩ := thm_3_15_combined_intermediate hn β hβ_half Q hQ f
    θstar hθstar hSobolev σ hσ hσ_le ε hsubG Y hModel M hM_pos hM_le θhat hLS hθstar_emp
    hf_meas hf_sq_int

  obtain ⟨C', hC'_pos, hrate⟩ := thm_3_15_rate_computation n hn β hβ_pos hβ_lower
    M hM_pos hM_choice σ hσ

  refine ⟨C₁ * C', mul_pos hC₁_pos hC'_pos, ?_⟩

  apply le_trans (hC₁_bound δ hδ_pos hδ_le)
  apply MeasureTheory.measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢

  calc L2normSq (fun x => trigLinComb M (θhat ω) x - f x)
      ≤ C₁ * ((M : ℝ) ^ (-(2 * β)) + (n : ℝ) ^ (1 - 2 * β) +
            ((M : ℝ) + σ ^ 2 * Real.log (1 / δ)) / (n : ℝ)) := hω
    _ ≤ C₁ * (C' * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) +
            C' * σ ^ 2 * Real.log (1 / δ) / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (hrate δ hδ_pos hδ_le) (le_of_lt hC₁_pos)
    _ = C₁ * C' * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) +
        C₁ * C' * σ ^ 2 * Real.log (1 / δ) / (n : ℝ) := by ring

/-- Converting an exponential tail bound into an expectation bound: if
`P(X ≤ A + B log(1/δ)) ≥ 1 - δ` for all `δ ∈ (0,1]`, then `E[X] ≤ A + B`. -/
theorem expectation_from_exponential_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX_meas : Measurable X) (_hX_nn : ∀ ω, 0 ≤ X ω)
    {A B : ℝ} (_hA : 0 ≤ A) (hB : 0 < B)
    (htail : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      μ {ω | X ω ≤ A + B * Real.log (1 / δ)} ≥ ENNReal.ofReal (1 - δ)) :
    ∫ ω, X ω ∂μ ≤ A + B := by
  by_cases hInt : Integrable X μ
  ·
    have step1 : ∫ ω, X ω ∂μ = ∫ ω, (X ω - A) ∂μ + A := by
      rw [integral_sub hInt (integrable_const A), integral_const]
      simp [Measure.real, measure_univ]
    rw [step1]
    suffices h : ∫ ω, (X ω - A) ∂μ ≤ B by linarith

    have hIntXA : Integrable (fun ω => X ω - A) μ := hInt.sub (integrable_const A)
    have hIntMax : Integrable (fun ω => max (X ω - A) 0) μ := hIntXA.pos_part

    have hMeasMax : AEStronglyMeasurable (fun ω => max (X ω - A) 0) μ :=
      ((hX_meas.sub measurable_const).max measurable_const).aestronglyMeasurable

    have hlint : ∫⁻ ω, ENNReal.ofReal (max (X ω - A) 0) ∂μ ≤ ENNReal.ofReal B := by
      rw [lintegral_eq_lintegral_meas_lt μ
        (by filter_upwards with ω; exact le_max_right _ _)
        ((hX_meas.sub measurable_const).max measurable_const).aemeasurable]
      calc ∫⁻ (t : ℝ) in Set.Ioi 0, μ {a | t < max (X a - A) 0}
          ≤ ∫⁻ (t : ℝ) in Set.Ioi 0, ENNReal.ofReal (Real.exp ((-1/B) * t)) := by
            apply lintegral_mono_ae
            filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
            simp only [Set.mem_Ioi] at ht
            have hset : {a | t < max (X a - A) 0} = {a | A + t < X a} := by
              ext a; simp only [Set.mem_setOf_eq, max_def]; split_ifs with h
              · constructor; intro h2; linarith; intro h2; linarith
              · push Not at h; constructor; intro h2; linarith; intro h2; linarith
            rw [hset]

            set δ := Real.exp ((-1/B) * t)
            have hδ_pos : 0 < δ := exp_pos _
            have hδ_le : δ ≤ 1 := exp_le_one_iff.mpr
              (mul_nonpos_of_nonpos_of_nonneg
                (div_nonpos_of_nonpos_of_nonneg (by norm_num) hB.le) ht.le)
            have hTail' := htail δ hδ_pos hδ_le
            have key : A + B * Real.log (1 / δ) = A + t := by
              congr 1; rw [one_div, Real.log_inv, Real.log_exp]; field_simp
            rw [key] at hTail'
            have hms : MeasurableSet {ω | X ω ≤ A + t} := hX_meas measurableSet_Iic
            rw [show {a | A + t < X a} = {ω | X ω ≤ A + t}ᶜ from by
              ext ω; simp [not_le]]
            rw [measure_compl hms (measure_ne_top μ _), measure_univ]
            calc (1 : ENNReal) - μ {ω | X ω ≤ A + t}
                ≤ 1 - ENNReal.ofReal (1 - δ) := tsub_le_tsub_left hTail' _
              _ = ENNReal.ofReal δ := by
                  rw [show (1:ENNReal) = ENNReal.ofReal 1 from by simp]
                  rw [← ENNReal.ofReal_sub 1 (by linarith)]
                  congr 1; ring
        _ = ENNReal.ofReal B := by
            rw [← ofReal_integral_eq_lintegral_ofReal
              (integrableOn_exp_mul_Ioi (div_neg_of_neg_of_pos (by norm_num) hB) 0)
              (by filter_upwards with t; exact (exp_pos _).le)]
            congr 1
            rw [integral_exp_mul_Ioi (div_neg_of_neg_of_pos (by norm_num) hB)]
            simp [mul_zero, exp_zero]

    calc ∫ ω, (X ω - A) ∂μ
        ≤ ∫ ω, max (X ω - A) 0 ∂μ := by
          exact integral_mono_ae hIntXA hIntMax
            (by filter_upwards with ω; exact le_max_left _ _)
      _ = (∫⁻ ω, ENNReal.ofReal (max (X ω - A) 0) ∂μ).toReal := by
          exact integral_eq_lintegral_of_nonneg_ae
            (by filter_upwards with ω; exact le_max_right _ _) hMeasMax
      _ ≤ B := by
          rw [← ENNReal.toReal_ofReal hB.le]
          exact ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hlint
  · rw [integral_undef hInt]; linarith

/-- Uniform-in-`δ` form of the high-probability bound from Theorem 3.15: there is a
single constant `C` such that for every `δ ∈ (0,1]`, the high-probability bound holds. -/
theorem thm_3_15_uniform_high_prob
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    (β : ℝ) (hβ_pos : 0 < β)
    (hβ_lower : β ≥ (1 + Real.sqrt 5) / 4)
    (Q : ℝ) (hQ : 0 < Q)
    (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (hθstar : ∀ j, θstar j = fourierCoeff f j)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
    (σ : ℝ) (hσ : 0 < σ) (hσ_le : σ ^ 2 ≤ 1)
    (ε : Ω → Fin n → ℝ)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
    (Y : Ω → Fin n → ℝ)
    (hModel : ∀ ω i, Y ω i = f ((i : ℝ) / (n : ℝ)) + ε ω i)
    (M : ℕ) (hM_pos : 0 < M) (hM_le : M ≤ n - 1)
    (hM_choice : (n : ℝ) ^ ((1 : ℝ) / (2 * β + 1)) ≤ (M : ℝ) ∧
                 (M : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / (2 * β + 1)) + 1)
    (θhat : Ω → Fin M → ℝ)
    (hLS : IsLSEstimator Y θhat)
    (hθstar_emp : ∀ j : Fin M, θstar j.val = (1 / (n : ℝ)) *
      ∑ i : Fin n, f ((i : ℝ) / (n : ℝ)) * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)))
    (hf_meas : Measurable f)
    (hf_sq_int : IntegrableOn (fun x => f x ^ 2) (Set.Icc 0 1)) :
    ∃ (C : ℝ), 0 < C ∧ ∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
    μ {ω | L2normSq (fun x => trigLinComb M (θhat ω) x - f x) ≤
            C * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) +
            C * σ ^ 2 * Real.log (1 / δ) / (n : ℝ)}
      ≥ ENNReal.ofReal (1 - δ) := by

  have hβ_half : 1/2 < β := by
    have : Real.sqrt 5 > 1 := by
      rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  obtain ⟨C₀, hC₀_pos, hcomb⟩ := thm_3_15_combined_intermediate hn β hβ_half Q hQ f
    θstar hθstar hSobolev σ hσ hσ_le ε hsubG Y hModel M hM_pos hM_le θhat hLS hθstar_emp
    hf_meas hf_sq_int
  obtain ⟨C', hC'_pos, hrate⟩ := thm_3_15_rate_computation n hn β hβ_pos hβ_lower
    M hM_pos hM_choice σ hσ
  refine ⟨C₀ * C', mul_pos hC₀_pos hC'_pos, ?_⟩
  intro δ hδ_pos hδ_le
  apply le_trans (hcomb δ hδ_pos hδ_le)
  apply MeasureTheory.measure_mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  calc L2normSq (fun x => trigLinComb M (θhat ω) x - f x)
      ≤ C₀ * ((M : ℝ) ^ (-(2 * β)) + (n : ℝ) ^ (1 - 2 * β) +
            ((M : ℝ) + σ ^ 2 * Real.log (1 / δ)) / (n : ℝ)) := hω
    _ ≤ C₀ * (C' * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) +
            C' * σ ^ 2 * Real.log (1 / δ) / (n : ℝ)) :=
        mul_le_mul_of_nonneg_left (hrate δ hδ_pos hδ_le) (le_of_lt hC₀_pos)
    _ = C₀ * C' * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) +
        C₀ * C' * σ ^ 2 * Real.log (1 / δ) / (n : ℝ) := by ring

/-- Expectation version of Theorem 3.15 (derived from the tail bound):
`E ‖φ_{θ̂^{LS}} - f‖²_{L²} ≤ C n^{-2β/(2β+1)}`. -/
theorem thm_3_15_expectation_from_tail
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    (β : ℝ) (hβ_pos : 0 < β)
    (hβ_lower : β ≥ (1 + Real.sqrt 5) / 4)
    (Q : ℝ) (hQ : 0 < Q)
    (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (hθstar : ∀ j, θstar j = fourierCoeff f j)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
    (σ : ℝ) (hσ : 0 < σ) (hσ_le : σ ^ 2 ≤ 1)
    (ε : Ω → Fin n → ℝ)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
    (Y : Ω → Fin n → ℝ)
    (hModel : ∀ ω i, Y ω i = f ((i : ℝ) / (n : ℝ)) + ε ω i)
    (M : ℕ) (hM_pos : 0 < M) (hM_le : M ≤ n - 1)
    (hM_choice : (n : ℝ) ^ ((1 : ℝ) / (2 * β + 1)) ≤ (M : ℝ) ∧
                 (M : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / (2 * β + 1)) + 1)
    (θhat : Ω → Fin M → ℝ)
    (hLS : IsLSEstimator Y θhat)
    (hθstar_emp : ∀ j : Fin M, θstar j.val = (1 / (n : ℝ)) *
      ∑ i : Fin n, f ((i : ℝ) / (n : ℝ)) * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)))
    (hMeas : Measurable (fun ω => L2normSq (fun x => trigLinComb M (θhat ω) x - f x)))
    (hf_meas : Measurable f)
    (hf_sq_int : IntegrableOn (fun x => f x ^ 2) (Set.Icc 0 1)) :
    ∃ (C : ℝ), 0 < C ∧
    ∫ ω, L2normSq (fun x => trigLinComb M (θhat ω) x - f x) ∂μ ≤
      C * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) := by


  obtain ⟨C₀, hC₀_pos, hHP⟩ := thm_3_15_uniform_high_prob hn β hβ_pos hβ_lower Q hQ f
    θstar hθstar hSobolev σ hσ hσ_le ε hsubG Y hModel M hM_pos hM_le hM_choice
    θhat hLS hθstar_emp hf_meas hf_sq_int
  set rate := (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) with rate_def
  set X := fun ω => L2normSq (fun x => trigLinComb M (θhat ω) x - f x) with X_def
  have hn_pos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hrate_nn : 0 ≤ rate := rpow_nonneg hn_pos.le _

  have hX_nn : ∀ ω, 0 ≤ X ω := by
    intro ω; simp only [X_def, L2normSq]
    exact integral_nonneg (fun x => sq_nonneg _)


  have hB_pos : 0 < C₀ * σ ^ 2 / (n : ℝ) := by positivity
  have htail : ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      μ {ω | X ω ≤ C₀ * rate + C₀ * σ ^ 2 / (n : ℝ) * Real.log (1 / δ)} ≥
        ENNReal.ofReal (1 - δ) := by
    intro δ hδ_pos hδ_le
    have key := hHP δ hδ_pos hδ_le
    have h_eq : C₀ * σ ^ 2 * Real.log (1 / δ) / (n : ℝ) =
        C₀ * σ ^ 2 / (n : ℝ) * Real.log (1 / δ) := by ring
    apply le_trans key
    apply MeasureTheory.measure_mono
    intro ω hω; simp only [Set.mem_setOf_eq, X_def] at hω ⊢
    linarith [hω, h_eq]

  have hEX := expectation_from_exponential_tail_bound hMeas hX_nn
    (by positivity : 0 ≤ C₀ * rate) hB_pos htail


  have h_inv_n_le_rate : 1 / (n : ℝ) ≤ rate := by
    rw [one_div, ← rpow_neg_one (n : ℝ), rate_def]
    apply rpow_le_rpow_of_exponent_le hn_ge1
    rw [neg_div, neg_le_neg_iff, div_le_one (by linarith : (0 : ℝ) < 2 * β + 1)]
    linarith
  have hσ_inv_n : C₀ * σ ^ 2 / (n : ℝ) ≤ C₀ * rate := by
    calc C₀ * σ ^ 2 / (n : ℝ) ≤ C₀ * 1 / (n : ℝ) := by
          apply div_le_div_of_nonneg_right _ hn_pos.le
          exact mul_le_mul_of_nonneg_left hσ_le hC₀_pos.le
      _ = C₀ / (n : ℝ) := by ring_nf
      _ = C₀ * (1 / (n : ℝ)) := by ring
      _ ≤ C₀ * rate := by
          apply mul_le_mul_of_nonneg_left h_inv_n_le_rate hC₀_pos.le

  refine ⟨2 * C₀, by positivity, ?_⟩
  calc ∫ ω, X ω ∂μ ≤ C₀ * rate + C₀ * σ ^ 2 / (n : ℝ) := hEX
    _ ≤ C₀ * rate + C₀ * rate := by linarith [hσ_inv_n]
    _ = 2 * C₀ * rate := by ring

/-- **Theorem 3.15 (Sobolev nonparametric rate).** Fix `β ≥ (1+√5)/4 ≃ 0.81`. Under the
regression model `Y_i = f(i/n) + ε_i` with `f ∈ Θ(β, Q)` and `ε ~ subG_n(σ²)`, `σ² ≤ 1`, the
least squares estimator with trigonometric basis and `M = ⌈n^{1/(2β+1)}⌉` satisfies, with
probability `1 - δ`:
`‖φ_{θ̂^{LS}} - f‖²_{L²} ≲ n^{-2β/(2β+1)} + σ² log(1/δ)/n`,
and in expectation,
`E ‖φ_{θ̂^{LS}} - f‖²_{L²} ≲ n^{-2β/(2β+1)}`. -/
theorem thm_3_15
    {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n)
    (β : ℝ) (hβ_pos : 0 < β)
    (hβ_lower : β ≥ (1 + Real.sqrt 5) / 4)
    (Q : ℝ) (hQ : 0 < Q)
    (f : ℝ → ℝ)
    (θstar : ℕ → ℝ)
    (hθstar : ∀ j, θstar j = fourierCoeff f j)
    (hSobolev : ∀ (K : ℕ),
      ∑ j : Fin K, (sobolevCoeff β (j.val + 1)) ^ 2 * (θstar j.val) ^ 2 ≤ Q)
    (σ : ℝ) (hσ : 0 < σ) (hσ_le : σ ^ 2 ≤ 1)
    (ε : Ω → Fin n → ℝ)
    (hsubG : IsSubGaussianNoiseVec ε (σ ^ 2) μ)
    (Y : Ω → Fin n → ℝ)
    (hModel : ∀ ω i, Y ω i = f ((i : ℝ) / (n : ℝ)) + ε ω i)
    (M : ℕ) (hM_pos : 0 < M) (hM_le : M ≤ n - 1)
    (hM_choice : (n : ℝ) ^ ((1 : ℝ) / (2 * β + 1)) ≤ (M : ℝ) ∧
                 (M : ℝ) ≤ (n : ℝ) ^ ((1 : ℝ) / (2 * β + 1)) + 1)
    (θhat : Ω → Fin M → ℝ)
    (hLS : IsLSEstimator Y θhat)
    (hθstar_emp : ∀ j : Fin M, θstar j.val = (1 / (n : ℝ)) *
      ∑ i : Fin n, f ((i : ℝ) / (n : ℝ)) * trigBasis (j.val + 1) ((i : ℝ) / (n : ℝ)))
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (hMeas : Measurable (fun ω => L2normSq (fun x => trigLinComb M (θhat ω) x - f x)))
    (hf_meas : Measurable f)
    (hf_sq_int : IntegrableOn (fun x => f x ^ 2) (Set.Icc 0 1)) :

    (∃ (C : ℝ), 0 < C ∧
      μ {ω | L2normSq (fun x => trigLinComb M (θhat ω) x - f x) ≤
              C * (n : ℝ) ^ (-(2 * β) / (2 * β + 1)) +
              C * σ ^ 2 * Real.log (1 / δ) / (n : ℝ)}
        ≥ ENNReal.ofReal (1 - δ))
    ∧

    (∃ (C : ℝ), 0 < C ∧
      ∫ ω, L2normSq (fun x => trigLinComb M (θhat ω) x - f x) ∂μ ≤
        C * (n : ℝ) ^ (-(2 * β) / (2 * β + 1))) :=
  ⟨thm_3_15_high_prob hn β hβ_pos hβ_lower Q hQ f θstar hθstar hSobolev
      σ hσ hσ_le ε hsubG Y hModel M hM_pos hM_le hM_choice θhat hLS hθstar_emp δ hδ_pos hδ_le
      hf_meas hf_sq_int,
   thm_3_15_expectation_from_tail hn β hβ_pos hβ_lower Q hQ f
      θstar hθstar hSobolev σ hσ hσ_le ε hsubG Y hModel M hM_pos hM_le hM_choice
      θhat hLS hθstar_emp hMeas hf_meas hf_sq_int⟩

end Chapter3
