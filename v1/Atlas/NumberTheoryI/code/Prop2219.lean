/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.NumberTheoryI.code.Ch22WeberLFunction
import Atlas.NumberTheoryI.code.AnalyticClassNumber
import Atlas.NumberTheoryI.code.Cor1838
noncomputable section

open scoped NumberField
open Complex Finset Section19

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

def halfPlane (K : Type u) [Field K] [NumberField K] : Set ℂ :=
  {s : ℂ | 1 - 1 / (Module.finrank ℚ K : ℝ) < s.re}

noncomputable def nonzeroIdealToFracIdealCoprime (K : Type*) [Field K] [NumberField K]
    (𝔪 : Modulus K) (I : Ideal (𝓞 K)) (_hI : I ≠ ⊥)
    (hcop : IsCoprime I 𝔪.finitePartIdeal) : FracIdealsCoprime K 𝔪 :=
  toFracIdealsCoprime I hcop

def idealInRayClass (𝔪 : Modulus K) (I : Ideal (𝓞 K)) : RayClassGroup K 𝔪 := by
  classical
  exact if h : I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal then
    toRayClass K 𝔪 (nonzeroIdealToFracIdealCoprime K 𝔪 I h.1 h.2)
  else 1

def rayClassPartialZeta_coeffs {𝔪 : Modulus K}
    (γ : RayClassGroup K 𝔪) : ℕ → ℂ :=
  fun n => if n = 0 then 0
    else (Nat.card {I : Ideal (𝓞 K) //
      I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧ Ideal.absNorm I = n ∧ idealInRayClass 𝔪 I = γ} : ℂ)

def rayClassPartialZeta {𝔪 : Modulus K}
    (γ : RayClassGroup K 𝔪) : ℂ → ℂ :=
  LSeries (rayClassPartialZeta_coeffs γ)

def rayClassPartialZeta_residue_val {𝔪 : Modulus K}
    (_γ : RayClassGroup K 𝔪) : ℂ :=
  (NumberField.dedekindZeta_residue K : ℂ) / (Fintype.card (RayClassGroup K 𝔪) : ℂ)

theorem rayClassPartialZeta_residue_val_ne_zero {𝔪 : Modulus K}
    (γ : RayClassGroup K 𝔪) : rayClassPartialZeta_residue_val γ ≠ 0 := by
  unfold rayClassPartialZeta_residue_val
  apply div_ne_zero
  · exact_mod_cast NumberField.dedekindZeta_residue_ne_zero K
  · exact_mod_cast Fintype.card_ne_zero

set_option checkBinderAnnotations false in
theorem ray_class_lattice_data (K : Type*) [Field K] [NumberField K]
    {𝔪 : Modulus K} (γ : RayClassGroup K 𝔪) :
    ∃ (Λ : Submodule ℤ (Fin (Module.finrank ℚ K) → ℝ)),
      ∃ (_ : DiscreteTopology Λ) (_ : IsZLattice ℝ Λ),
      ∃ (S : Set (Fin (Module.finrank ℚ K) → ℝ)),
        MeasurableSet S ∧
        IsLipschitzParametrizable (frontier S) (Module.finrank ℚ K - 1) ∧
        (∃ (w_𝔪 : ℕ), 0 < w_𝔪 ∧
          ∀ᶠ (t : ℝ) in Filter.atTop,
            ↑w_𝔪 * (Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧
              (Ideal.absNorm I : ℝ) ≤ t ∧ idealInRayClass 𝔪 I = γ} : ℝ) =
            (Nat.card {x : Λ | (x : Fin (Module.finrank ℚ K) → ℝ) ∈
              (fun v => (t ^ ((1 : ℝ) / (Module.finrank ℚ K : ℝ))) • v) '' S} : ℝ)) ∧
        ((MeasureTheory.volume S).toReal / ZLattice.covolume Λ =
          NumberField.dedekindZeta_residue K /
          Fintype.card (RayClassGroup K 𝔪)) ∧
        MeasureTheory.volume S ≠ ⊤ ∧
        Bornology.IsBounded S := by sorry

lemma rayClassPartialZeta_coeffs_sum_eq_count {𝔪 : Modulus K}
    (γ : RayClassGroup K 𝔪) (t : ℕ) :
    ∑ i ∈ Finset.range t, rayClassPartialZeta_coeffs γ (i + 1) =
    (Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧
      Ideal.absNorm I ≤ t ∧ idealInRayClass 𝔪 I = γ} : ℂ) := by

  simp only [rayClassPartialZeta_coeffs, Nat.succ_ne_zero, ↓reduceIte]

  rw [← Nat.cast_sum]
  congr 1


  have h_absNorm_pos : ∀ (I : Ideal (𝓞 K)), I ≠ ⊥ → 1 ≤ Ideal.absNorm I := by
    intro I hI
    have := (Ideal.absNorm_eq_zero_iff.not.mpr hI)
    omega

  have h_fiber_finite : ∀ (n : ℕ),
      Finite {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧
        Ideal.absNorm I = n ∧ idealInRayClass 𝔪 I = γ} := by
    intro n
    have hfin := Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n
    haveI : Finite {I : Ideal (𝓞 K) | Ideal.absNorm I = n} := hfin.to_subtype
    exact Finite.of_injective
      (fun (x : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧
          Ideal.absNorm I = n ∧ idealInRayClass 𝔪 I = γ}) =>
        (⟨x.val, x.prop.2.2.1⟩ : {I : Ideal (𝓞 K) | Ideal.absNorm I = n}))
      (fun ⟨I₁, _⟩ ⟨I₂, _⟩ heq => by
        simp only [Subtype.mk.injEq] at heq; exact Subtype.ext heq)


  symm


  have h_equiv : {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧
          Ideal.absNorm I ≤ t ∧ idealInRayClass 𝔪 I = γ} ≃
      (Σ (k : Fin t), {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧
          Ideal.absNorm I = k.val + 1 ∧ idealInRayClass 𝔪 I = γ}) :=
    { toFun := fun ⟨I, hne, hcop, hle, hclass⟩ =>
        ⟨⟨Ideal.absNorm I - 1, by have := h_absNorm_pos I hne; omega⟩,
          ⟨I, hne, hcop,
            (by have hpos := h_absNorm_pos I hne; simp only [Fin.val_mk]; omega),

            hclass⟩⟩
      invFun := fun ⟨k, I, hne, hcop, hnorm, hclass⟩ =>
        ⟨I, hne, hcop, by omega, hclass⟩
      left_inv := fun ⟨I, hne, hcop, hle, hclass⟩ => by simp
      right_inv := fun ⟨⟨k, hk⟩, ⟨I, hne, hcop, hnorm, hclass⟩⟩ => by
        simp only [Fin.val_mk] at hnorm
        have hkey : Ideal.absNorm I - 1 = k := by omega
        subst hkey
        simp }


  calc Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧
          Ideal.absNorm I ≤ t ∧ idealInRayClass 𝔪 I = γ}
      = Nat.card (Σ (k : Fin t), {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧
          Ideal.absNorm I = k.val + 1 ∧ idealInRayClass 𝔪 I = γ}) :=
        Nat.card_congr h_equiv
    _ = ∑ k : Fin t, Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧
          Ideal.absNorm I = k.val + 1 ∧ idealInRayClass 𝔪 I = γ} := by
        haveI : ∀ (a : Fin t), Finite {I : Ideal (𝓞 K) // I ≠ ⊥ ∧
            IsCoprime I 𝔪.finitePartIdeal ∧
            Ideal.absNorm I = a.val + 1 ∧ idealInRayClass 𝔪 I = γ} :=
          fun a => h_fiber_finite (a.val + 1)
        rw [Nat.card_sigma]
    _ = ∑ x ∈ Finset.range t, Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧
          Ideal.absNorm I = x + 1 ∧ idealInRayClass 𝔪 I = γ} :=
        Fin.sum_univ_eq_sum_range (fun x => Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧
          Ideal.absNorm I = x + 1 ∧ idealInRayClass 𝔪 I = γ}) t

set_option checkBinderAnnotations false in
theorem ray_class_count_error {K : Type u} [Field K] [NumberField K]
    {𝔪 : Modulus K} (γ : RayClassGroup K 𝔪) :
    ∃ (C : ℝ), 0 ≤ C ∧ ∀ (t : ℕ),
      ‖(Nat.card {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧
        Ideal.absNorm I ≤ t ∧ idealInRayClass 𝔪 I = γ} : ℂ) -
       rayClassPartialZeta_residue_val γ * (t : ℂ)‖ ≤
      C * (t : ℝ) ^ ((1 : ℝ) - 1 / (Module.finrank ℚ K : ℝ)) := by sorry

theorem rayClassPartialZeta_asymptotic {𝔪 : Modulus K}
    (γ : RayClassGroup K 𝔪) :
    ∃ C : ℝ, ∀ t : ℕ,
      ‖∑ i ∈ Finset.range t, rayClassPartialZeta_coeffs γ (i + 1) -
        rayClassPartialZeta_residue_val γ * t‖ ≤
      C * (t : ℝ) ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := by
  obtain ⟨C, hC_nonneg, hC⟩ := ray_class_count_error γ
  exact ⟨C, fun t => by rw [rayClassPartialZeta_coeffs_sum_eq_count]; exact hC t⟩

def rayClassPartialZeta_ext {𝔪 : Modulus K}
    (γ : RayClassGroup K 𝔪) : ℂ → ℂ :=
  dirichletSeriesContinuation (rayClassPartialZeta_coeffs γ) (rayClassPartialZeta_residue_val γ)

theorem rayClassPartialZeta_summable {𝔪 : Modulus K}
    (γ : RayClassGroup K 𝔪) (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (rayClassPartialZeta_coeffs γ) s := by
  apply LSeriesSummable_of_sum_norm_bigO (r := 1) _ zero_le_one hs
  obtain ⟨C, hC⟩ := rayClassPartialZeta_asymptotic γ
  set a := rayClassPartialZeta_coeffs γ with ha_def
  set ρ := rayClassPartialZeta_residue_val γ
  set σ : ℝ := 1 - 1 / (Module.finrank ℚ K : ℝ) with hσ_def

  have ha_im : ∀ k, (a k).im = 0 := by
    intro k; simp only [ha_def, rayClassPartialZeta_coeffs]; split_ifs <;> simp
  have ha_re_nonneg : ∀ k, 0 ≤ (a k).re := by
    intro k; simp only [ha_def, rayClassPartialZeta_coeffs]
    split_ifs <;> simp [Nat.cast_nonneg]
  have ha_norm_re : ∀ k, ‖a k‖ = (a k).re := by
    intro k
    have hz : a k = ↑(a k).re := by
      apply Complex.ext
      · exact (Complex.ofReal_re (a k).re).symm
      · simp [ha_im k]
    conv_lhs => rw [hz]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (ha_re_nonneg k)]

  have hIcc_range : ∀ m : ℕ,
      ∑ k ∈ Finset.Icc 1 m, ‖a k‖ = (∑ i ∈ Finset.range m, a (i + 1)).re := by
    intro m
    have hIcc_img : Finset.Icc 1 m = (Finset.range m).image (· + 1) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · intro ⟨hk1, hk2⟩; exact ⟨k - 1, by omega, by omega⟩
      · rintro ⟨j, hj, rfl⟩; omega
    rw [hIcc_img]
    conv_lhs => rw [Finset.sum_image (by intro i _ j _ h; omega : ∀ i ∈ Finset.range m,
      ∀ j ∈ Finset.range m, i + 1 = j + 1 → i = j)]
    simp_rw [ha_norm_re]
    rw [Complex.re_sum]

  rw [show (1 : ℝ) = (1 : ℝ) from rfl]
  rw [Asymptotics.isBigO_iff]
  refine ⟨‖ρ‖ + |C| + 1, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  rw [hIcc_range, Real.rpow_one]

  have hS_nonneg : 0 ≤ (∑ i ∈ Finset.range n, a (i + 1)).re := by
    rw [Complex.re_sum]; exact Finset.sum_nonneg (fun i _ => ha_re_nonneg _)
  rw [Real.norm_of_nonneg hS_nonneg]

  have hcast : (n : ℂ) = ↑(n : ℝ) := by push_cast; rfl

  have hS_bound : (∑ i ∈ Finset.range n, a (i + 1)).re ≤ ‖ρ‖ * ↑n + C * (↑n) ^ σ := by
    have hCn := hC n
    rw [hcast] at hCn

    have h_rho_re : (ρ * (↑(n : ℝ) : ℂ)).re ≤ ‖ρ‖ * ↑n := by
      calc (ρ * (↑(n : ℝ) : ℂ)).re ≤ |(ρ * (↑(n : ℝ) : ℂ)).re| := le_abs_self _
        _ ≤ ‖ρ * (↑(n : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
        _ = ‖ρ‖ * ‖(↑(n : ℝ) : ℂ)‖ := norm_mul ρ _
        _ = ‖ρ‖ * ↑n := by rw [Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Nat.cast_nonneg n)]

    have h_diff_re : (∑ i ∈ Finset.range n, a (i + 1) - ρ * ↑(n : ℝ)).re ≤
        C * (↑n) ^ σ := by
      calc _ ≤ |_| := le_abs_self _
        _ ≤ ‖∑ i ∈ Finset.range n, a (i + 1) - ρ * ↑(n : ℝ)‖ :=
            Complex.abs_re_le_norm _
        _ ≤ C * (↑n) ^ σ := hCn

    have hdecomp : (∑ i ∈ Finset.range n, a (i + 1)).re =
        (∑ i ∈ Finset.range n, a (i + 1) - ρ * ↑(n : ℝ)).re +
        (ρ * (↑(n : ℝ) : ℂ)).re := by
      simp only [Complex.sub_re]; ring
    linarith

  have hn_pos : (0 : ℝ) ≤ (↑n : ℝ) := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ (↑n : ℝ) := by exact_mod_cast hn
  have hσ_le_1 : σ ≤ 1 := by
    rw [hσ_def]
    have hn_field : (0 : ℝ) < Module.finrank ℚ K :=
      Nat.cast_pos.mpr Module.finrank_pos
    linarith [div_pos one_pos hn_field]
  have hpow_le : (↑n : ℝ) ^ σ ≤ (↑n : ℝ) := by
    calc (↑n : ℝ) ^ σ ≤ (↑n : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1 hσ_le_1
      _ = ↑n := Real.rpow_one _

  suffices h : (∑ i ∈ Finset.range n, a (i + 1)).re ≤ (‖ρ‖ + |C| + 1) * (↑n : ℝ) by
    calc (∑ i ∈ Finset.range n, a (i + 1)).re ≤ _ := h
      _ = _ := by
          congr 1
          rw [Real.norm_of_nonneg hn_pos]
  calc (∑ i ∈ Finset.range n, a (i + 1)).re
      ≤ ‖ρ‖ * ↑n + C * (↑n) ^ σ := hS_bound
    _ ≤ ‖ρ‖ * ↑n + |C| * ↑n := by
        have : C * (↑n) ^ σ ≤ |C| * ↑n := by
          calc C * (↑n) ^ σ ≤ |C| * (↑n) ^ σ := by
                nlinarith [le_abs_self C, Real.rpow_nonneg hn_pos σ]
            _ ≤ |C| * ↑n := by nlinarith [abs_nonneg C]
        linarith
    _ = (‖ρ‖ + |C|) * ↑n := by ring
    _ ≤ (‖ρ‖ + |C| + 1) * ↑n := by nlinarith

theorem rayClassPartialZeta_ext_eq {𝔪 : Modulus K}
    (γ : RayClassGroup K 𝔪) (s : ℂ) (hs : 1 < s.re) :
    rayClassPartialZeta_ext γ s = rayClassPartialZeta γ s := by
  unfold rayClassPartialZeta_ext rayClassPartialZeta dirichletSeriesContinuation

  set a := rayClassPartialZeta_coeffs γ
  set ρ := rayClassPartialZeta_residue_val γ

  have ha_sub_sum : LSeriesSummable (fun n => a n - ρ) s := by
    have ha_sum := rayClassPartialZeta_summable γ s hs
    have hconst_sum : LSeriesSummable (fun (_ : ℕ) => ρ) s := by
      rw [show (fun (_ : ℕ) => ρ) = ρ • (1 : ℕ → ℂ) from by ext; simp]
      exact (LSeriesSummable_one_iff.mpr hs).smul ρ
    exact ha_sum.sub hconst_sum


  have hO_sub : (fun n => ∑ k ∈ Finset.Icc 1 n, (a k - ρ)) =O[Filter.atTop]
      fun n => (n : ℝ) ^ (1 : ℝ) := by

    obtain ⟨C, hC⟩ := rayClassPartialZeta_asymptotic γ

    have hC' : ∀ t : ℕ, ‖∑ i ∈ Finset.range t, a (i + 1) - ρ * ↑t‖ ≤
        C * (↑t : ℝ) ^ (1 - 1 / (Module.finrank ℚ K : ℝ)) := hC

    have h_reindex : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, (a k - ρ) =
        ∑ i ∈ Finset.range n, a (i + 1) - ρ * ↑n := by
      intro n
      have hIcc_img : Finset.Icc 1 n = (Finset.range n).image (· + 1) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
        constructor
        · intro ⟨hk1, hk2⟩; exact ⟨k - 1, by omega, by omega⟩
        · rintro ⟨j, hj, rfl⟩; omega
      rw [hIcc_img, Finset.sum_image (by intro i _ j _ h; omega :
        ∀ i ∈ Finset.range n, ∀ j ∈ Finset.range n, i + 1 = j + 1 → i = j)]
      rw [Finset.sum_sub_distrib]
      simp [Finset.card_range, mul_comm]


    have hC_nonneg : 0 ≤ C := by
      have h1 := hC' 1; simp at h1; exact le_trans (norm_nonneg _) h1
    rw [Asymptotics.isBigO_iff]
    refine ⟨C, ?_⟩
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    rw [h_reindex, Real.rpow_one, Real.norm_of_nonneg (Nat.cast_nonneg n)]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hσ_le : (1 : ℝ) - 1 / (Module.finrank ℚ K : ℝ) ≤ 1 := by
      have : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.mpr Module.finrank_pos
      linarith [div_pos one_pos this]
    have hpow_le : (n : ℝ) ^ ((1 : ℝ) - 1 / (Module.finrank ℚ K : ℝ)) ≤ (n : ℝ) := by
      calc (n : ℝ) ^ ((1 : ℝ) - 1 / ↑(Module.finrank ℚ K)) ≤ (n : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hn1 hσ_le
        _ = (n : ℝ) := Real.rpow_one _
    calc ‖∑ i ∈ Finset.range n, a (i + 1) - ρ * ↑n‖
        ≤ C * (n : ℝ) ^ ((1 : ℝ) - 1 / ↑(Module.finrank ℚ K)) := hC' n
      _ ≤ C * (n : ℝ) := mul_le_mul_of_nonneg_left hpow_le hC_nonneg
  have h_bridge := dirichletSeriesAbel_eq_LSeries (fun n => a n - ρ) s ha_sub_sum
    zero_le_one hs hO_sub
  rw [h_bridge]


  rw [← LSeries_one_eq_riemannZeta hs]

  rw [← LSeries_smul 1 ρ s]


  have hρ_sum : LSeriesSummable (ρ • (1 : ℕ → ℂ)) s := by
    exact (LSeriesSummable_one_iff.mpr hs).smul ρ
  rw [← LSeries_add hρ_sum ha_sub_sum]
  congr 1
  ext n
  simp [Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_one, add_sub_cancel]

lemma halfPlane_exponent_nonneg :
    (0 : ℝ) ≤ 1 - 1 / (Module.finrank ℚ K : ℝ) := by
  have hn : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.mpr Module.finrank_pos
  have h1 : 1 / (Module.finrank ℚ K : ℝ) ≤ 1 := by
    rw [div_le_one hn]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp Module.finrank_pos)
  linarith

lemma halfPlane_exponent_lt_one :
    1 - 1 / (Module.finrank ℚ K : ℝ) < 1 := by
  have hn : (0 : ℝ) < Module.finrank ℚ K := Nat.cast_pos.mpr Module.finrank_pos
  linarith [div_pos one_pos hn]

theorem rayClassPartialZeta_ext_meromorphicOn {𝔪 : Modulus K}
    (γ : RayClassGroup K 𝔪) :
    MeromorphicOn (rayClassPartialZeta_ext γ) (halfPlane K) := by
  exact dirichlet_series_meromorphicOn
    (rayClassPartialZeta_coeffs γ)
    (1 - 1 / (Module.finrank ℚ K : ℝ))
    halfPlane_exponent_nonneg
    halfPlane_exponent_lt_one
    (rayClassPartialZeta_residue_val γ)
    (rayClassPartialZeta_residue_val_ne_zero γ)
    (rayClassPartialZeta_asymptotic γ)

theorem rayClassPartialZeta_ext_residue {𝔪 : Modulus K}
    (γ : RayClassGroup K 𝔪) :
    Filter.Tendsto (fun s : ℂ => (s - 1) * rayClassPartialZeta_ext γ s)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) (nhds (rayClassPartialZeta_residue_val γ)) := by
  exact dirichlet_series_residue_complex
    (rayClassPartialZeta_coeffs γ)
    (1 - 1 / (Module.finrank ℚ K : ℝ))
    halfPlane_exponent_nonneg
    halfPlane_exponent_lt_one
    (rayClassPartialZeta_residue_val γ)
    (rayClassPartialZeta_residue_val_ne_zero γ)
    (rayClassPartialZeta_asymptotic γ)

def rayClassPartialZeta_residue (𝔪 : Modulus K) : ℂ :=
  (NumberField.dedekindZeta_residue K : ℂ) / (Fintype.card (RayClassGroup K 𝔪) : ℂ)

def rayClassPartialZeta_regularPart {𝔪 : Modulus K}
    (γ : RayClassGroup K 𝔪) : ℂ → ℂ :=
  dirichletSeriesAbel
    (fun n => rayClassPartialZeta_coeffs γ n - rayClassPartialZeta_residue_val γ)

theorem rayClassPartialZeta_regularPart_analyticAt {𝔪 : Modulus K}
    (γ : RayClassGroup K 𝔪) :
    AnalyticAt ℂ (rayClassPartialZeta_regularPart γ) 1 := by
  have h1mem : (1 : ℂ) ∈ {s : ℂ | (1 - 1 / (Module.finrank ℚ K : ℝ) : ℝ) < s.re} := by
    simp only [Set.mem_setOf_eq, Complex.one_re]; exact halfPlane_exponent_lt_one (K := K)
  exact dirichlet_series_remainder_holomorphic
    (rayClassPartialZeta_coeffs γ)
    (1 - 1 / (Module.finrank ℚ K : ℝ))
    (rayClassPartialZeta_residue_val γ)
    (rayClassPartialZeta_asymptotic γ) 1 h1mem

theorem rayClassPartialZeta_ext_eq_decomp {𝔪 : Modulus K}
    (γ : RayClassGroup K 𝔪) :
    ∀ᶠ s in nhds (1 : ℂ),
      rayClassPartialZeta_ext γ s =
        rayClassPartialZeta_residue 𝔪 * riemannZeta s +
          rayClassPartialZeta_regularPart γ s := by
  apply Filter.Eventually.of_forall
  intro s
  simp only [rayClassPartialZeta_regularPart, rayClassPartialZeta_ext,
    dirichletSeriesContinuation, rayClassPartialZeta_residue_val, rayClassPartialZeta_residue]

def weberLFunction_combinedCoeffs {𝔪 : Modulus K}
    (χ : RayClassChar K 𝔪) : ℕ → ℂ :=
  fun n => ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) • (rayClassPartialZeta_coeffs γ n)

lemma weberLFunction_combinedCoeffs_eq_sum {𝔪 : Modulus K}
    (χ : RayClassChar K 𝔪) :
    weberLFunction_combinedCoeffs χ =
      ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) • (rayClassPartialZeta_coeffs γ) := by
  ext n
  simp [weberLFunction_combinedCoeffs, Finset.sum_apply]

lemma evalIdealExt_eq_char_idealInRayClass
    {K : Type u} [Field K] [NumberField K]
    {𝔪 : Modulus K} (χ : RayClassChar K 𝔪)
    (I : Ideal (𝓞 K)) (hne : I ≠ ⊥) (hcop : IsCoprime I 𝔪.finitePartIdeal) :
    χ.evalIdealExt I = ↑(χ (idealInRayClass 𝔪 I)) := by
  classical
  simp only [RayClassChar.evalIdealExt, dif_pos hcop, RayClassChar.evalIdeal]
  congr 1
  unfold idealInRayClass
  rw [dif_pos ⟨hne, hcop⟩]
  simp only [nonzeroIdealToFracIdealCoprime]


open Classical in
lemma summand_fiber_eq {K : Type u} [Field K] [NumberField K]
    {𝔪 : Modulus K} (χ : RayClassChar K 𝔪)
    (γ : RayClassGroup K 𝔪) (s : ℂ)
    (𝔞 : {I : Ideal (𝓞 K) // I ≠ ⊥})
    (hmem : idealInRayClass 𝔪 𝔞.val = γ) :
    χ.evalIdealExt 𝔞.val * (↑(Ideal.absNorm 𝔞.val) : ℂ) ^ (-s) =
    if IsCoprime 𝔞.val 𝔪.finitePartIdeal
    then (χ γ : ℂ) * (↑(Ideal.absNorm 𝔞.val) : ℂ) ^ (-s)
    else 0 := by
  split_ifs with hcop
  · rw [evalIdealExt_eq_char_idealInRayClass χ 𝔞.val 𝔞.prop hcop, hmem]
  · rw [RayClassChar.evalIdealExt_eq_zero_of_not_coprime χ 𝔞.val hcop, zero_mul]

set_option maxHeartbeats 400000 in
lemma fiber_tsum_eq_LSeries {K : Type u} [Field K] [NumberField K]
    {𝔪 : Modulus K} (γ : RayClassGroup K 𝔪) (s : ℂ) :
    ∑' (𝔞 : {I : Ideal (𝓞 K) //
      I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧ idealInRayClass 𝔪 I = γ}),
      (↑(Ideal.absNorm 𝔞.val) : ℂ) ^ (-s) =
    LSeries (rayClassPartialZeta_coeffs γ) s := by
  classical
  set A := {I : Ideal (𝓞 K) //
    I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧ idealInRayClass 𝔪 I = γ}
  set g : A → ℕ := fun a => Ideal.absNorm a.val


  set H : (Σ n, {a : A // g a = n}) → ℂ := fun c => (↑c.1 : ℂ) ^ (-s)
  have hHF : ∀ c, H c = (fun a : A => (↑(g a) : ℂ) ^ (-s)) ((Equiv.sigmaFiberEquiv g) c) := by
    intro ⟨n, a, ha⟩
    simp [H, Equiv.sigmaFiberEquiv, ha]

  have hLHS : ∑' (a : A), (↑(Ideal.absNorm a.val) : ℂ) ^ (-s) = ∑' c, H c := by
    rw [← Equiv.tsum_eq (Equiv.sigmaFiberEquiv g)]
    congr 1; ext c
    exact (hHF c).symm
  rw [hLHS]


  by_cases hSH : Summable H
  · rw [hSH.tsum_sigma]


    unfold LSeries
    congr 1; ext n
    by_cases hn : n = 0
    ·
      subst hn
      simp only [LSeries.term_zero]
      convert tsum_empty using 1
      rw [isEmpty_iff]
      intro ⟨⟨I, hI⟩, hgI⟩
      simp only [g] at hgI
      exact hI.1 (Ideal.absNorm_eq_zero_iff.mp hgI)
    ·
      rw [LSeries.term_of_ne_zero hn]
      haveI : Finite {a : A // g a = n} := by
        have hfin := Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n
        haveI : Finite {I : Ideal (𝓞 K) | Ideal.absNorm I = n} := hfin.to_subtype
        exact Finite.of_injective
          (fun (x : {a : A // g a = n}) =>
            (⟨x.val.val, x.prop⟩ : {I : Ideal (𝓞 K) | Ideal.absNorm I = n}))
          (fun ⟨⟨I₁, _⟩, _⟩ ⟨⟨I₂, _⟩, _⟩ heq => by
            simp only [Subtype.mk.injEq] at heq; exact Subtype.ext (Subtype.ext heq))
      haveI : Fintype {a : A // g a = n} := Fintype.ofFinite _
      rw [tsum_fintype]
      simp only [H, Finset.sum_const, nsmul_eq_mul]
      simp only [rayClassPartialZeta_coeffs, if_neg hn]
      rw [div_eq_mul_inv, cpow_neg]
      congr 1

      rw [Nat.cast_inj]
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]

      apply Nat.card_congr
      exact {
        toFun := fun ⟨⟨I, hne, hcop, hclass⟩, hnorm⟩ => ⟨I, hne, hcop, hnorm, hclass⟩
        invFun := fun ⟨I, hne, hcop, hnorm, hclass⟩ => ⟨⟨I, hne, hcop, hclass⟩, hnorm⟩
        left_inv := fun ⟨⟨I, hne, hcop, hclass⟩, hnorm⟩ => rfl
        right_inv := fun ⟨I, hne, hcop, hnorm, hclass⟩ => rfl
      }

  ·
    rw [tsum_eq_zero_of_not_summable hSH]


    symm
    rw [LSeries, tsum_eq_zero_of_not_summable]
    intro hLS
    apply hSH


    set f := rayClassPartialZeta_coeffs γ
    apply Summable.of_norm

    rw [show (fun c : (Σ n, {a : A // g a = n}) => ‖H c‖) =
          (fun c : (Σ n, {a : A // g a = n}) => ‖(↑c.1 : ℂ) ^ (-s)‖) from rfl]

    rw [summable_sigma_of_nonneg (fun _ => norm_nonneg _)]
    constructor
    ·
      intro n
      by_cases hn : n = 0
      ·
        subst hn
        have : IsEmpty {a : A // g a = 0} := by
          rw [isEmpty_iff]
          intro ⟨⟨I, hI⟩, hgI⟩
          simp only [g] at hgI
          exact hI.1 (Ideal.absNorm_eq_zero_iff.mp hgI)
        exact summable_of_ne_finset_zero (s := ∅) (fun x => isEmptyElim x)
      ·
        haveI : Finite {a : A // g a = n} := by
          have hfin := Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n
          haveI : Finite {I : Ideal (𝓞 K) | Ideal.absNorm I = n} := hfin.to_subtype
          exact Finite.of_injective
            (fun (x : {a : A // g a = n}) =>
              (⟨x.val.val, x.prop⟩ : {I : Ideal (𝓞 K) | Ideal.absNorm I = n}))
            (fun ⟨⟨I₁, _⟩, _⟩ ⟨⟨I₂, _⟩, _⟩ heq => by
              simp only [Subtype.mk.injEq] at heq; exact Subtype.ext (Subtype.ext heq))
        haveI : Fintype {a : A // g a = n} := Fintype.ofFinite _
        exact (hasSum_fintype _).summable
    ·

      apply Summable.of_nonneg_of_le
        (fun n => tsum_nonneg (fun _ => norm_nonneg _))
        (fun n => ?_)
        hLS.norm

      by_cases hn : n = 0
      · subst hn
        have : IsEmpty {a : A // g a = 0} := by
          rw [isEmpty_iff]
          intro ⟨⟨I, hI⟩, hgI⟩
          simp only [g] at hgI
          exact hI.1 (Ideal.absNorm_eq_zero_iff.mp hgI)
        simp [tsum_empty]
      · haveI : Finite {a : A // g a = n} := by
          have hfin := Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n
          haveI : Finite {I : Ideal (𝓞 K) | Ideal.absNorm I = n} := hfin.to_subtype
          exact Finite.of_injective
            (fun (x : {a : A // g a = n}) =>
              (⟨x.val.val, x.prop⟩ : {I : Ideal (𝓞 K) | Ideal.absNorm I = n}))
            (fun ⟨⟨I₁, _⟩, _⟩ ⟨⟨I₂, _⟩, _⟩ heq => by
              simp only [Subtype.mk.injEq] at heq; exact Subtype.ext (Subtype.ext heq))
        haveI : Fintype {a : A // g a = n} := Fintype.ofFinite _
        rw [tsum_fintype]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [LSeries.term_of_ne_zero hn, norm_div]


        rw [show ‖(↑n : ℂ) ^ s‖ = ‖(↑n : ℂ) ^ s‖ from rfl]

        rw [show ‖(↑n : ℂ) ^ (-s)‖ = (‖(↑n : ℂ) ^ s‖)⁻¹ from by
          rw [Complex.cpow_neg, norm_inv]]


        rw [div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (norm_nonneg _))


        simp only [f, rayClassPartialZeta_coeffs, if_neg hn]
        rw [Complex.norm_natCast]

        rw [Nat.cast_le]
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
        haveI : Finite { I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧ Ideal.absNorm I = n ∧ idealInRayClass 𝔪 I = γ } := by
          have hfin := Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n
          haveI : Finite {I : Ideal (𝓞 K) | Ideal.absNorm I = n} := hfin.to_subtype
          exact Finite.of_injective
            (fun (x : { I : Ideal (𝓞 K) // I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧ Ideal.absNorm I = n ∧ idealInRayClass 𝔪 I = γ }) =>
              (⟨x.val, x.prop.2.2.1⟩ : {I : Ideal (𝓞 K) | Ideal.absNorm I = n}))
            (fun ⟨I₁, _⟩ ⟨I₂, _⟩ heq => by
              simp only [Subtype.mk.injEq] at heq; exact Subtype.ext heq)
        exact Nat.card_le_card_of_injective
          (fun ⟨⟨I, hne, hcop, hclass⟩, hnorm⟩ => ⟨I, hne, hcop, hnorm, hclass⟩)
          (fun ⟨⟨I₁, _, _, _⟩, _⟩ ⟨⟨I₂, _, _, _⟩, _⟩ heq => by
            simp only [Subtype.mk.injEq] at heq; exact Subtype.ext (Subtype.ext heq))

set_option maxHeartbeats 400000 in
theorem dirichletSeries_eq_sum_rayClass_LSeries
    (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) (χ : RayClassChar K 𝔪) (s : ℂ) (hs : 1 < s.re) :
    ∑' (𝔞 : {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥}),
      χ.evalIdealExt (𝔞 : Ideal (NumberField.RingOfIntegers K)) *
      (↑(Ideal.absNorm (𝔞 : Ideal (NumberField.RingOfIntegers K))) : ℂ) ^ (-s) =
    ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) * LSeries (rayClassPartialZeta_coeffs γ) s := by
  classical

  set f : {I : Ideal (𝓞 K) // I ≠ ⊥} → ℂ :=
    fun 𝔞 => χ.evalIdealExt 𝔞.val * (↑(Ideal.absNorm 𝔞.val) : ℂ) ^ (-s) with hf_def
  set fiberMap : {I : Ideal (𝓞 K) // I ≠ ⊥} → RayClassGroup K 𝔪 :=
    fun 𝔞 => idealInRayClass 𝔪 𝔞.val with hfiberMap_def

  have hHasSum := WeberLFunction_eulerProduct_hasSum K 𝔪 χ s hs

  have hFiber := hHasSum.tsum_fiberwise fiberMap


  have hLHS := hHasSum.tsum_eq
  have hRHS := hFiber.tsum_eq
  rw [tsum_fintype] at hRHS

  rw [hLHS, ← hRHS]

  congr 1
  ext γ

  show ∑' (𝔞 : ↑(fiberMap ⁻¹' {γ})), f (𝔞 : {I : Ideal (𝓞 K) // I ≠ ⊥}) =
    (χ γ : ℂ) * LSeries (rayClassPartialZeta_coeffs γ) s
  simp only [hf_def]


  have hterm_eq : ∀ (𝔞 : ↑(fiberMap ⁻¹' {γ})),
      χ.evalIdealExt 𝔞.val.val * (↑(Ideal.absNorm 𝔞.val.val) : ℂ) ^ (-s) =
      if IsCoprime (𝔞.val.val : Ideal (𝓞 K)) 𝔪.finitePartIdeal
      then (χ γ : ℂ) * (↑(Ideal.absNorm 𝔞.val.val) : ℂ) ^ (-s)
      else 0 := by
    intro ⟨𝔞, h𝔞⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h𝔞
    exact summand_fiber_eq χ γ s 𝔞 h𝔞
  simp_rw [hterm_eq]

  set S : Set ↑(fiberMap ⁻¹' {γ}) :=
    {𝔞 | IsCoprime (𝔞.val.val : Ideal (𝓞 K)) 𝔪.finitePartIdeal}
  have hind : ∀ 𝔞, (if IsCoprime (𝔞.val.val : Ideal (𝓞 K)) 𝔪.finitePartIdeal
      then (χ γ : ℂ) * (↑(Ideal.absNorm (𝔞.val.val : Ideal (𝓞 K))) : ℂ) ^ (-s)
      else 0) =
    S.indicator (fun 𝔞 => (χ γ : ℂ) *
      (↑(Ideal.absNorm (𝔞.val.val : Ideal (𝓞 K))) : ℂ) ^ (-s)) 𝔞 := by
    intro 𝔞; simp [Set.indicator_apply, S]
  simp_rw [hind]
  rw [← _root_.tsum_subtype S (fun (𝔞 : ↑(fiberMap ⁻¹' {γ})) => (χ γ : ℂ) *
    (↑(Ideal.absNorm (𝔞.val.val : Ideal (𝓞 K))) : ℂ) ^ (-s))]

  simp_rw [tsum_mul_left]

  congr 1


  rw [← fiber_tsum_eq_LSeries γ s]

  let A := {I : Ideal (𝓞 K) //
    I ≠ ⊥ ∧ IsCoprime I 𝔪.finitePartIdeal ∧ idealInRayClass 𝔪 I = γ}
  let hequiv : ↑S ≃ A := {
    toFun := fun ⟨⟨⟨I, hne⟩, hfib⟩, hcop⟩ => ⟨I, hne, hcop, by
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hfiberMap_def] at hfib; exact hfib⟩
    invFun := fun ⟨I, hne, hcop, hfib⟩ => ⟨⟨⟨I, hne⟩, by
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hfiberMap_def]; exact hfib⟩, hcop⟩
    left_inv := fun ⟨⟨⟨I, hne⟩, hfib⟩, hcop⟩ => rfl
    right_inv := fun ⟨I, hne, hcop, hfib⟩ => rfl
  }
  exact Equiv.tsum_eq hequiv (fun a => (↑(Ideal.absNorm a.val) : ℂ) ^ (-s))

theorem WeberLFunction_eq_LSeries_combinedCoeffs
    (𝔪 : Modulus K) (χ : RayClassChar K 𝔪) (s : ℂ) (hs : 1 < s.re) :
    WeberLFunction K 𝔪 χ s =
      LSeries (weberLFunction_combinedCoeffs χ) s := by


  suffices h : WeberLFunction K 𝔪 χ s =
      ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) * LSeries (rayClassPartialZeta_coeffs γ) s by
    rw [h, weberLFunction_combinedCoeffs_eq_sum]
    rw [LSeries_sum (fun γ _ => (rayClassPartialZeta_summable γ s hs).smul (χ γ : ℂ))]
    congr 1; ext γ
    exact (LSeries_smul (rayClassPartialZeta_coeffs γ) (χ γ : ℂ) s).symm


  rw [WeberLFunction_eq_dirichletSeries K 𝔪 χ s hs]
  exact dirichletSeries_eq_sum_rayClass_LSeries K 𝔪 χ s hs

theorem rayClassPartialZeta_coeffs_summable
    {𝔪 : Modulus K} (γ : RayClassGroup K 𝔪) (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (rayClassPartialZeta_coeffs γ) s :=
  rayClassPartialZeta_summable γ s hs

theorem WeberLFunction_eq_sum_rayClassPartialZeta
    (𝔪 : Modulus K) (χ : RayClassChar K 𝔪) (s : ℂ) (hs : 1 < s.re) :
    WeberLFunction K 𝔪 χ s =
      ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) * rayClassPartialZeta γ s := by

  rw [WeberLFunction_eq_LSeries_combinedCoeffs 𝔪 χ s hs]

  rw [weberLFunction_combinedCoeffs_eq_sum]

  rw [LSeries_sum (fun γ _ => (rayClassPartialZeta_coeffs_summable γ s hs).smul (χ γ : ℂ))]

  congr 1
  ext γ
  exact LSeries_smul (rayClassPartialZeta_coeffs γ) (χ γ : ℂ) s

theorem sum_nonprincipal_char_eq_zero
    {𝔪 : Modulus K} (χ : RayClassChar K 𝔪)
    (hχ : ¬χ.IsPrincipal) :
    ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) = 0 := by

  simp only [RayClassChar.IsPrincipal, not_forall] at hχ
  obtain ⟨g₀, hg₀⟩ := hχ

  have key : (χ g₀ : ℂ) * ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) =
      ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) := by
    rw [Finset.mul_sum]
    have heq : (fun γ : RayClassGroup K 𝔪 => (χ g₀ : ℂ) * (χ γ : ℂ)) =
        (fun γ : RayClassGroup K 𝔪 => (χ (g₀ * γ) : ℂ)) := by
      ext γ
      simp only [map_mul, Units.val_mul]
    rw [heq]
    exact Fintype.sum_bijective (fun γ => g₀ * γ) (Group.mulLeft_bijective g₀) _ _ (fun γ => rfl)

  have hne : (χ g₀ : ℂ) ≠ 1 := by
    intro h
    apply hg₀
    exact Units.ext h

  have hsub : ((χ g₀ : ℂ) - 1) * ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) = 0 := by
    rw [sub_mul, one_mul, key, sub_self]
  exact (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hne)

theorem WeberLFunction_ext_continuousAt_one_of_nonprincipal
    {𝔪 : Modulus K} (χ : RayClassChar K 𝔪) (hχ : ¬χ.IsPrincipal) :
    ContinuousAt (fun s => ∑ γ : RayClassGroup K 𝔪,
      (χ γ : ℂ) * rayClassPartialZeta_ext γ s) 1 := by

  have hG : AnalyticAt ℂ (fun s => ∑ γ : RayClassGroup K 𝔪,
      (χ γ : ℂ) * rayClassPartialZeta_regularPart γ s) 1 := by
    apply Finset.analyticAt_fun_sum
    intro γ _
    exact analyticAt_const.mul (rayClassPartialZeta_regularPart_analyticAt γ)

  have hfg : ∀ᶠ s in nhds (1 : ℂ),
      ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) * rayClassPartialZeta_ext γ s =
      ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) * rayClassPartialZeta_regularPart γ s := by

    have hdecomp : ∀ᶠ s in nhds (1 : ℂ), ∀ γ : RayClassGroup K 𝔪,
        rayClassPartialZeta_ext γ s =
          rayClassPartialZeta_residue 𝔪 * riemannZeta s +
            rayClassPartialZeta_regularPart γ s := by
      rw [Filter.eventually_all]
      exact fun γ => rayClassPartialZeta_ext_eq_decomp γ
    filter_upwards [hdecomp] with s hs
    simp_rw [hs]
    simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, ← mul_assoc,
      sum_nonprincipal_char_eq_zero χ hχ, zero_mul, zero_add]

  exact hG.continuousAt.congr (Filter.EventuallyEq.symm hfg)

structure WeberLFunction_MeromorphicExtension
    (𝔪 : Modulus K) (χ : RayClassChar K 𝔪) where
  toFun : ℂ → ℂ
  eq_on_convergence : ∀ s : ℂ, 1 < s.re →
    toFun s = WeberLFunction K 𝔪 χ s
  meromorphicOn : MeromorphicOn toFun (halfPlane K)
  simple_pole_at_one : ∃ v : ℂ,
    AnalyticAt ℂ (Function.update (fun s => (s - 1) * toFun s) 1 v) 1

  holomorphic_at_one_of_nonprincipal : ¬χ.IsPrincipal → AnalyticAt ℂ toFun 1

def WeberLFunction_ext {𝔪 : Modulus K} (χ : RayClassChar K 𝔪) (s : ℂ) : ℂ :=
  ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) * rayClassPartialZeta_ext γ s

theorem WeberLFunction_ext_eq {𝔪 : Modulus K} (χ : RayClassChar K 𝔪)
    (s : ℂ) (hs : 1 < s.re) :
    WeberLFunction_ext χ s = WeberLFunction K 𝔪 χ s := by
  unfold WeberLFunction_ext
  rw [WeberLFunction_eq_sum_rayClassPartialZeta 𝔪 χ s hs]
  congr 1
  ext γ
  rw [rayClassPartialZeta_ext_eq γ s hs]

theorem WeberLFunction_ext_meromorphicOn {𝔪 : Modulus K} (χ : RayClassChar K 𝔪) :
    MeromorphicOn (WeberLFunction_ext χ) (halfPlane K) := by
  intro s hs
  show MeromorphicAt (fun s => ∑ γ ∈ Finset.univ, (↑(χ γ) : ℂ) * rayClassPartialZeta_ext γ s) s
  apply MeromorphicAt.fun_sum
  intro γ _
  exact (MeromorphicAt.const (↑(χ γ) : ℂ) s).mul
    (rayClassPartialZeta_ext_meromorphicOn γ s hs)

theorem WeberLFunction_ext_simple_pole {𝔪 : Modulus K} (χ : RayClassChar K 𝔪) :
    ∃ v : ℂ,
      AnalyticAt ℂ (Function.update (fun s => (s - 1) * WeberLFunction_ext χ s) 1 v) 1 := by

  refine ⟨∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) * rayClassPartialZeta_residue_val γ, ?_⟩
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  ·
    have h1_in : (1 : ℂ) ∈ {s : ℂ | (1 - 1 / (Module.finrank ℚ K : ℝ) : ℝ) < s.re} := by
      simp only [Set.mem_setOf_eq, Complex.one_re]; exact halfPlane_exponent_lt_one (K := K)
    have hopen : IsOpen {s : ℂ | (1 - 1 / (Module.finrank ℚ K : ℝ) : ℝ) < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hmem : {s : ℂ | (1 - 1 / (Module.finrank ℚ K : ℝ) : ℝ) < s.re} ∈ nhds (1 : ℂ) :=
      hopen.mem_nhds h1_in
    rw [eventually_nhdsWithin_iff]
    filter_upwards [hmem] with z hz hne
    have heq : Function.update (fun s => (s - 1) * WeberLFunction_ext χ s) 1
        (∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) * rayClassPartialZeta_residue_val γ) =ᶠ[nhds z]
        (fun s => (s - 1) * WeberLFunction_ext χ s) := by
      filter_upwards [isOpen_ne.mem_nhds hne] with w hw
      exact Function.update_of_ne hw _ _
    rw [heq.differentiableAt_iff]


    apply DifferentiableAt.mul
    · exact differentiableAt_id.sub (differentiableAt_const _)
    · show DifferentiableAt ℂ (WeberLFunction_ext χ) z
      unfold WeberLFunction_ext
      apply DifferentiableAt.fun_sum
      intro γ _
      exact (differentiableAt_const _).mul
        (dirichlet_series_analyticAt_off_pole
          (rayClassPartialZeta_coeffs γ)
          (1 - 1 / (Module.finrank ℚ K : ℝ))
          (rayClassPartialZeta_residue_val γ)
          (rayClassPartialZeta_asymptotic γ) z hz hne).differentiableAt
  ·
    rw [continuousAt_update_same]

    have heq_fn : (fun s : ℂ => (s - 1) * WeberLFunction_ext χ s) =
        (fun s => ∑ γ : RayClassGroup K 𝔪, (χ γ : ℂ) * ((s - 1) * rayClassPartialZeta_ext γ s)) := by
      ext s; simp only [WeberLFunction_ext, Finset.mul_sum]; congr 1; ext γ; ring
    rw [heq_fn]
    apply tendsto_finset_sum
    intro γ _
    exact Filter.Tendsto.const_mul _
      (rayClassPartialZeta_ext_residue γ)

theorem WeberLFunction_ext_holomorphic_at_one_of_nonprincipal
    {𝔪 : Modulus K} (χ : RayClassChar K 𝔪) (hχ : ¬χ.IsPrincipal) :
    AnalyticAt ℂ (WeberLFunction_ext χ) 1 := by

  have h_mero : MeromorphicAt (WeberLFunction_ext χ) 1 :=
    WeberLFunction_ext_meromorphicOn χ 1 (by
      show 1 - 1 / (Module.finrank ℚ K : ℝ) < (1 : ℂ).re
      simp only [Complex.one_re]; exact halfPlane_exponent_lt_one (K := K))


  have h_cont : ContinuousAt (WeberLFunction_ext χ) 1 :=
    WeberLFunction_ext_continuousAt_one_of_nonprincipal χ hχ

  exact h_mero.analyticAt h_cont

def Proposition_22_19 (𝔪 : Modulus K) (χ : RayClassChar K 𝔪) :
    WeberLFunction_MeromorphicExtension 𝔪 χ :=
  { toFun := WeberLFunction_ext χ
    eq_on_convergence := fun s hs => WeberLFunction_ext_eq χ s hs
    meromorphicOn := WeberLFunction_ext_meromorphicOn χ
    simple_pole_at_one := WeberLFunction_ext_simple_pole χ
    holomorphic_at_one_of_nonprincipal := fun hχ =>
      WeberLFunction_ext_holomorphic_at_one_of_nonprincipal χ hχ }

end RayClassField
