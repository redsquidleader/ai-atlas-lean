/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.GrothendieckGroupO

noncomputable section

universe u

variable {R : Type u} [CommRing R]
         {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

def IsDominantCorootNonneg {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) [LinearOrder R] [IsStrictOrderedRing R]
    (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ α ∈ rd.posRoots, (0 : R) ≤ rd.corootPairing lam α

variable {Δ : TriangularDecomposition R 𝔤}
variable (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)

theorem normSq_diff_factorization
    (B : WeightBilinForm wg)
    (lam phi alpha : Δ.𝔥 →ₗ[R] R) (n : ℕ)
    (halpha_pos : alpha ∈ rd.posRoots)
    (hpair : rd.corootPairing phi alpha = (n : R)) :
    B.normSq (lam - phi + n • alpha) - B.normSq (lam - phi) =
    (n : R) * rd.corootPairing lam alpha * B.form alpha alpha := by
  sorry

theorem form_posRoot_pos_of_WeightBilinForm [LinearOrder R] [IsStrictOrderedRing R]
    (B : WeightBilinForm wg) (alpha : Δ.𝔥 →ₗ[R] R) (halpha_pos : alpha ∈ rd.posRoots) :
    (0 : R) < B.form alpha alpha :=
  B.form_posRoot_pos rd alpha halpha_pos

theorem normSq_le_of_single_step [LinearOrder R] [IsStrictOrderedRing R]
    (B : WeightBilinForm wg)
    (lam a b : Δ.𝔥 →ₗ[R] R)
    (hlam_dom : IsDominantCorootNonneg rd lam)
    (hstep : ∃ α, ReflectionLT rd α a b) :
    B.normSq (lam - b) ≤ B.normSq (lam - a) := by
  obtain ⟨α, hα_pos, n, hn_pos, hpair, hab⟩ := hstep

  have hkey : lam - a = lam - b + n • α := by rw [hab]; abel
  rw [hkey]


  have hdiff := normSq_diff_factorization rd wg B lam b α n hα_pos hpair
  have hn_pos_R : (0 : R) < (n : R) := Nat.cast_pos.mpr hn_pos
  have hlam_nonneg : (0 : R) ≤ rd.corootPairing lam α := hlam_dom α hα_pos
  have haa_pos : (0 : R) < B.form α α := form_posRoot_pos_of_WeightBilinForm rd wg B α hα_pos
  have hprod_nonneg : (0 : R) ≤ (n : R) * rd.corootPairing lam α * B.form α α :=
    mul_nonneg (mul_nonneg (le_of_lt hn_pos_R) hlam_nonneg) (le_of_lt haa_pos)
  linarith

theorem corootPairing_lam_eq_zero_of_normSq_eq [LinearOrder R] [IsStrictOrderedRing R]
    (B : WeightBilinForm wg)
    (lam b alpha : Δ.𝔥 →ₗ[R] R) (n : ℕ)
    (halpha_pos : alpha ∈ rd.posRoots)
    (hn_pos : 0 < n)
    (hpair : rd.corootPairing b alpha = (n : R))
    (h_eq : B.normSq (lam - b) = B.normSq (lam - b + n • alpha)) :
    rd.corootPairing lam alpha = 0 := by
  have hdiff := normSq_diff_factorization rd wg B lam b alpha n halpha_pos hpair
  have h_diff_zero : B.normSq (lam - b + n • alpha) - B.normSq (lam - b) = 0 := by linarith
  have hprod_zero : (n : R) * rd.corootPairing lam alpha * B.form alpha alpha = 0 := by linarith
  have hn_pos_R : (0 : R) < (n : R) := Nat.cast_pos.mpr hn_pos
  have haa_pos : (0 : R) < B.form alpha alpha :=
    form_posRoot_pos_of_WeightBilinForm rd wg B alpha halpha_pos
  have hn_ne : (n : R) ≠ 0 := ne_of_gt hn_pos_R
  have haa_ne : B.form alpha alpha ≠ 0 := ne_of_gt haa_pos

  have hna_ne : (n : R) * B.form alpha alpha ≠ 0 := mul_ne_zero hn_ne haa_ne
  have h_factored : (n : R) * B.form alpha alpha * rd.corootPairing lam alpha = 0 := by
    ring_nf; linarith
  exact mul_left_cancel₀ hna_ne (by rw [h_factored, mul_zero])

theorem weylStab_of_normSq_eq_single_step [LinearOrder R] [IsStrictOrderedRing R]
    (rs : RootSystemWithReflections rd wg)
    (B : WeightBilinForm wg)
    (lam a b : Δ.𝔥 →ₗ[R] R)
    (_hlam_dom : IsDominantCorootNonneg rd lam)
    (hstep : ∃ α, ReflectionLT rd α a b)
    (h_eq : B.normSq (lam - b) = B.normSq (lam - a)) :
    ∃ (w : wg.W), w ∈ WeylStabilizer rd wg lam ∧
      wg.dualAction w b = a := by
  obtain ⟨α, hα_pos, n, hn_pos, hpair, hab⟩ := hstep

  have hkey : lam - a = lam - b + n • α := by rw [hab]; abel
  rw [hkey] at h_eq

  have hlam_zero : rd.corootPairing lam α = 0 :=
    corootPairing_lam_eq_zero_of_normSq_eq rd wg B lam b α n hα_pos hn_pos hpair h_eq

  have hα_root : α ∈ rs.allRoots := rs.posRoots_sub α hα_pos

  have hcompat_lam : lam (rs.coroot α) = (0 : R) := by
    rw [← rs.corootPairing_eq_eval α hα_root lam]
    exact hlam_zero
  have hrefl_lam : wg.dualAction (rs.reflection α) lam = lam := by
    rw [rs.reflection_formula α hα_root lam, hcompat_lam, zero_smul, sub_zero]

  have hcompat_b : b (rs.coroot α) = (n : R) := by
    rw [← rs.corootPairing_eq_eval α hα_root b]
    exact hpair
  have hrefl_b : wg.dualAction (rs.reflection α) b = a := by
    rw [rs.reflection_formula α hα_root b, hcompat_b]
    rw [Nat.cast_smul_eq_nsmul R n α]
    exact hab.symm
  exact ⟨rs.reflection α, hrefl_lam, hrefl_b⟩

theorem normSq_le_of_bruhatLE [LinearOrder R] [IsStrictOrderedRing R]
    (B : WeightBilinForm wg)
    (lam phi psi : Δ.𝔥 →ₗ[R] R)
    (hlam_dom : IsDominantCorootNonneg rd lam)
    (hBruhat : BruhatLE rd psi phi) :
    B.normSq (lam - phi) ≤ B.normSq (lam - psi) := by
  induction hBruhat with
  | refl => exact le_rfl
  | @tail b c _hab hbc ih =>
    exact le_trans (normSq_le_of_single_step rd wg B lam b c hlam_dom hbc) ih

end
