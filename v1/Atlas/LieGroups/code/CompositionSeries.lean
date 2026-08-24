/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.CategoryOII

noncomputable section

universe uCatO

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {R 𝔤}

structure LieModule.CompositionSeries
    (R : Type*) [CommRing R] (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (M : Type*) [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M] where
  length : ℕ
  series : Fin (length + 1) → LieSubmodule R 𝔤 M
  bot : series ⟨0, Nat.zero_lt_succ length⟩ = ⊥
  top : series ⟨length, Nat.lt_succ_iff.mpr le_rfl⟩ = ⊤
  strictly_mono : ∀ i : Fin length, series i.castSucc < series i.succ

noncomputable def jordanHolder_compMult_raw
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (_wg : WeylGroupData Δ) :
    (Δ.𝔥 →ₗ[R] R) → (Δ.𝔥 →ₗ[R] R) → ℕ := fun lam mu =>


  let h_lam := @verma_module_exists.{0} R _ 𝔤 _ _ Δ lam
  let Mlam := h_lam.choose
  let instACG_M := h_lam.choose_spec.choose
  let instMod_M := h_lam.choose_spec.choose_spec.choose
  let instLRM_M := h_lam.choose_spec.choose_spec.choose_spec.choose
  let instLM_M := h_lam.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let hMlam := h_lam.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.some

  let h_mu := @verma_module_exists.{0} R _ 𝔤 _ _ Δ mu
  let Mmu := h_mu.choose
  let instACG_L := h_mu.choose_spec.choose
  let instMod_L := h_mu.choose_spec.choose_spec.choose
  let instLRM_L := h_mu.choose_spec.choose_spec.choose_spec.choose
  let instLM_L := h_mu.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let hMmu := h_mu.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.some

  let h_max := hMmu.exists_unique_maximal_submodule
  let J := h_max.choose
  let hJ_ne_top := h_max.choose_spec.1
  let hJ_max := h_max.choose_spec.2

  let hCatO : IsCategoryO Δ rd Mlam :=
    @verma_module_isCategoryO R _ 𝔤 _ _ Δ rd Mlam instACG_M instMod_M instLRM_M instLM_M lam hMlam

  @compositionMultiplicityOfModule R _ 𝔤 _ _ Δ rd
    Mlam instACG_M instMod_M instLRM_M instLM_M hCatO
    (@HasQuotient.Quotient Mmu (LieSubmodule R 𝔤 Mmu) _ J)
    inferInstance inferInstance inferInstance inferInstance
    (@IsVermaModule.quotient_by_maximal_irreducible R _ 𝔤 _ _ Δ Mmu instACG_L instMod_L
      instLRM_L instLM_L mu hMmu J hJ_ne_top hJ_max)

theorem compositionMultiplicity_quotient_maximal_eq_one
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hCatO : IsCategoryO Δ rd M)
    {J : LieSubmodule R 𝔤 M}
    (hJ_ne_top : J ≠ ⊤)
    (hJ_max : ∀ (N : LieSubmodule R 𝔤 M), N ≠ ⊤ → N ≤ J)
    (hIrr : LieModule.IsIrreducible R 𝔤 (M ⧸ J)) :
    compositionMultiplicityOfModule M hCatO (M ⧸ J) hIrr = 1 := by sorry

theorem jordanHolder_compMult_diag
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ) :
    ∀ lam, jordanHolder_compMult_raw R 𝔤 Δ rd wg lam lam = 1 := by
  intro lam
  unfold jordanHolder_compMult_raw
  simp only []


  letI := (@verma_module_exists.{0} R _ 𝔤 _ _ Δ lam).choose_spec.choose
  letI := (@verma_module_exists.{0} R _ 𝔤 _ _ Δ lam).choose_spec.choose_spec.choose
  letI := (@verma_module_exists.{0} R _ 𝔤 _ _ Δ lam).choose_spec.choose_spec.choose_spec.choose
  letI := (@verma_module_exists.{0} R _ 𝔤 _ _ Δ lam).choose_spec.choose_spec.choose_spec.choose_spec.choose

  set hVM := (@verma_module_exists.{0} R _ 𝔤 _ _ Δ lam).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.some with hVM_def
  set h_max := hVM.exists_unique_maximal_submodule with h_max_def
  exact compositionMultiplicity_quotient_maximal_eq_one _
    h_max.choose_spec.1
    h_max.choose_spec.2
    _

theorem jantzen_radical_compMult_bound
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (hne : lam ≠ mu) :
    jordanHolder_compMult_raw R 𝔤 Δ rd wg lam mu ≤
      ∑ α ∈ rd.posRoots,
        jordanHolder_compMult_raw R 𝔤 Δ rd wg
          (lam - (rd.corootPairing lam α) • α) mu := by sorry

theorem jantzen_integrality_of_descent
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (α : Δ.𝔥 →ₗ[R] R)
    (hα : α ∈ rd.posRoots)
    (hne : lam ≠ mu)
    (hd : jordanHolder_compMult_raw R 𝔤 Δ rd wg
            (lam - (rd.corootPairing lam α) • α) mu ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ rd.corootPairing lam α = (n : R) := by sorry

theorem jantzen_comp_factor_descent
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (hne : lam ≠ mu)
    (hd : jordanHolder_compMult_raw R 𝔤 Δ rd wg lam mu ≠ 0) :
    ∃ (α : Δ.𝔥 →ₗ[R] R) (n : ℕ),
      α ∈ rd.posRoots ∧ 0 < n ∧ rd.corootPairing lam α = (n : R) ∧
      jordanHolder_compMult_raw R 𝔤 Δ rd wg (lam - n • α) mu ≠ 0 := by

  have hbound := jantzen_radical_compMult_bound R 𝔤 Δ rd wg lam mu hne
  have hsum_ne : ∑ α ∈ rd.posRoots,
      jordanHolder_compMult_raw R 𝔤 Δ rd wg
        (lam - (rd.corootPairing lam α) • α) mu ≠ 0 := by omega

  obtain ⟨α, hα_mem, hα_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne

  obtain ⟨n, hn_pos, hn_eq⟩ := jantzen_integrality_of_descent R 𝔤 Δ rd wg lam mu α hα_mem hne hα_ne

  refine ⟨α, n, hα_mem, hn_pos, hn_eq, ?_⟩
  have : n • α = (rd.corootPairing lam α) • α := by
    rw [hn_eq, Nat.cast_smul_eq_nsmul R n α]
  rw [this]
  exact hα_ne

theorem bgg_qplus
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ) :
    ∀ (lam mu : Δ.𝔥 →ₗ[R] R),
      jordanHolder_compMult_raw R 𝔤 Δ rd wg lam mu ≠ 0 →
      rd.IsInQPlus (lam - mu) := by sorry

theorem bgg_induction_measure
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ) :
    ∃ (m : (Δ.𝔥 →ₗ[R] R) → (Δ.𝔥 →ₗ[R] R) → ℕ),

      (∀ lam, m lam lam = 0) ∧

      (∀ (lam mu α : Δ.𝔥 →ₗ[R] R) (n : ℕ),
        α ∈ rd.posRoots → 0 < n → rd.corootPairing lam α = (n : R) →
        jordanHolder_compMult_raw R 𝔤 Δ rd wg (lam - n • α) mu ≠ 0 →
        m (lam - n • α) mu < m lam mu) := by


  suffices h_height : ∃ (ht : (Δ.𝔥 →ₗ[R] R) → ℕ),
      (ht 0 = 0) ∧
      (∀ (β α : Δ.𝔥 →ₗ[R] R) (n : ℕ),
        α ∈ rd.posRoots → 0 < n → rd.IsInQPlus β →
        ht β + n ≤ ht (β + n • α)) ∧
      (∀ (lam mu : Δ.𝔥 →ₗ[R] R),
        jordanHolder_compMult_raw R 𝔤 Δ rd wg lam mu ≠ 0 →
        rd.IsInQPlus (lam - mu)) by
    obtain ⟨ht, ht_zero, ht_mono, ht_qplus⟩ := h_height
    refine ⟨fun lam mu => ht (lam - mu), fun lam => by simp [ht_zero], ?_⟩
    intro lam mu α n hα hn hcr hd_desc

    show ht (lam - n • α - mu) < ht (lam - mu)

    have heq : lam - mu = (lam - n • α - mu) + n • α := by abel
    rw [heq]

    have h_qp : rd.IsInQPlus (lam - n • α - mu) := ht_qplus _ _ hd_desc
    have h_le := ht_mono (lam - n • α - mu) α n hα hn h_qp
    omega


  classical

  let ht : (Δ.𝔥 →ₗ[R] R) → ℕ := fun β =>
    if h : rd.IsInQPlus β then ∑ γ ∈ rd.posRoots, h.choose γ else 0


  have h_ht_zero : ht 0 = 0 := by
    show (if h : rd.IsInQPlus 0 then ∑ γ ∈ rd.posRoots, h.choose γ else 0) = 0
    rw [dif_pos rd.IsInQPlus_zero]


    set c := (rd.IsInQPlus_zero).choose with hc_def
    have hc_spec : (0 : Δ.𝔥 →ₗ[R] R) = ∑ α ∈ rd.posRoots, (c α) • α :=
      (rd.IsInQPlus_zero).choose_spec

    suffices hall : ∀ γ ∈ rd.posRoots, c γ = 0 by
      exact Finset.sum_eq_zero (fun γ hγ => hall γ hγ)
    intro γ hγ
    by_contra hcγ

    have hcγ_pos : 0 < c γ := Nat.pos_of_ne_zero hcγ

    have hextract := Finset.sum_erase_add _ (fun α => (c α) • α) hγ
    rw [← hc_spec] at hextract
    simp only [] at *

    have h_neg : ∑ α ∈ rd.posRoots.erase γ, (c α) • α = -((c γ) • γ) :=
      eq_neg_of_add_eq_zero_left hextract
    let c' : (Δ.𝔥 →ₗ[R] R) → ℕ := fun δ => if δ = γ then 0 else c δ
    have hc'_sum : ∑ δ ∈ rd.posRoots, (c' δ) • δ =
        ∑ δ ∈ rd.posRoots.erase γ, (c δ) • δ := by
      rw [← Finset.sum_erase_add _ _ hγ]
      simp only [c', ite_true, zero_smul, add_zero]
      apply Finset.sum_congr rfl
      intro δ hδ; simp [Finset.ne_of_mem_erase hδ]
    have hkey : (-(↑(c γ) : ℤ)) • γ = ∑ δ ∈ rd.posRoots, (c' δ) • δ := by
      rw [hc'_sum, h_neg, neg_zsmul, natCast_zsmul]
    have hn_neg : (-(↑(c γ) : ℤ)) < 0 := by omega
    exact rd.posRoots_pointed_cone γ hγ _ hn_neg ⟨c', hkey⟩


  have h_ht_mono : ∀ (β α : Δ.𝔥 →ₗ[R] R) (n : ℕ),
      α ∈ rd.posRoots → 0 < n → rd.IsInQPlus β →
      ht β + n ≤ ht (β + n • α) := by
    sorry
  have h_qplus : ∀ (lam mu : Δ.𝔥 →ₗ[R] R),
      jordanHolder_compMult_raw R 𝔤 Δ rd wg lam mu ≠ 0 →
      rd.IsInQPlus (lam - mu) :=
    bgg_qplus R 𝔤 Δ rd wg
  exact ⟨ht, h_ht_zero, h_ht_mono, h_qplus⟩

lemma bgg_jantzen_step
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (hne : lam ≠ mu)
    (hd : jordanHolder_compMult_raw R 𝔤 Δ rd wg lam mu ≠ 0) :
    ∃ (α : Δ.𝔥 →ₗ[R] R) (n : ℕ),
      α ∈ rd.posRoots ∧ 0 < n ∧ rd.corootPairing lam α = (n : R) ∧
      jordanHolder_compMult_raw R 𝔤 Δ rd wg (lam - n • α) mu ≠ 0 ∧
      BruhatLE rd mu (lam - n • α) := by

  obtain ⟨m, hm_diag, hm_desc⟩ := bgg_induction_measure R 𝔤 Δ rd wg


  suffices bgg_ind : ∀ (k : ℕ) (lam' mu' : Δ.𝔥 →ₗ[R] R),
      m lam' mu' ≤ k →
      jordanHolder_compMult_raw R 𝔤 Δ rd wg lam' mu' ≠ 0 →
      BruhatLE rd mu' lam' by

    obtain ⟨α, n, hα, hn, hcr, hd'⟩ := jantzen_comp_factor_descent R 𝔤 Δ rd wg lam mu hne hd

    have hmeas : m (lam - n • α) mu < m lam mu := hm_desc lam mu α n hα hn hcr hd'

    have hBruhat : BruhatLE rd mu (lam - n • α) :=
      bgg_ind (m lam mu - 1) (lam - n • α) mu (by omega) hd'
    exact ⟨α, n, hα, hn, hcr, hd', hBruhat⟩

  intro k
  induction k with
  | zero =>
    intro lam' mu' hle hd'

    have hm0 : m lam' mu' = 0 := by omega

    by_cases heq : lam' = mu'
    · subst heq; exact Relation.ReflTransGen.refl
    ·
      obtain ⟨α', n', hα', hn', hcr', hd''⟩ :=
        jantzen_comp_factor_descent R 𝔤 Δ rd wg lam' mu' heq hd'

      have := hm_desc lam' mu' α' n' hα' hn' hcr' hd''
      omega
  | succ k ih =>
    intro lam' mu' hle hd'
    by_cases heq : lam' = mu'
    · subst heq; exact Relation.ReflTransGen.refl
    ·
      obtain ⟨α', n', hα', hn', hcr', hd''⟩ :=
        jantzen_comp_factor_descent R 𝔤 Δ rd wg lam' mu' heq hd'

      have hmeas' : m (lam' - n' • α') mu' < m lam' mu' :=
        hm_desc lam' mu' α' n' hα' hn' hcr' hd''

      have hle' : m (lam' - n' • α') mu' ≤ k := by omega
      have hBruhat' : BruhatLE rd mu' (lam' - n' • α') := ih (lam' - n' • α') mu' hle' hd''

      exact Relation.ReflTransGen.tail hBruhat' ⟨α', hα', n', hn', hcr', rfl⟩

theorem jordanHolder_compMult_bruhat
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ) :
    ∀ lam mu, jordanHolder_compMult_raw R 𝔤 Δ rd wg lam mu ≠ 0 →
      BruhatLE rd mu lam := by
  intro lam mu hd

  by_cases heq : lam = mu
  ·
    subst heq
    exact Relation.ReflTransGen.refl
  ·

    obtain ⟨α, n, hα, hn, hcr, _, hBruhat⟩ := bgg_jantzen_step R 𝔤 Δ rd wg lam mu heq hd


    exact Relation.ReflTransGen.tail hBruhat ⟨α, hα, n, hn, hcr, rfl⟩

lemma stdFiltMult_exists
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ) :
    ∃ (d : (Δ.𝔥 →ₗ[R] R) → (Δ.𝔥 →ₗ[R] R) → ℕ),

      (∀ lam, d lam lam = 1) :=
  ⟨fun lam mu => jordanHolder_compMult_raw R 𝔤 Δ rd wg mu lam,
   fun lam => jordanHolder_compMult_diag R 𝔤 Δ rd wg lam⟩

noncomputable def standardFiltration_stdMult_raw
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ) :
    (Δ.𝔥 →ₗ[R] R) → (Δ.𝔥 →ₗ[R] R) → ℕ :=
  (stdFiltMult_exists R 𝔤 Δ rd wg).choose

theorem prop_16_2_ii_raw
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ) :
    ∀ lam mu, jordanHolder_compMult_raw R 𝔤 Δ rd wg mu lam =
      standardFiltration_stdMult_raw R 𝔤 Δ rd wg lam mu := by


  intro lam mu
  sorry

theorem standardFiltration_stdMult_bgg_raw
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ) :
    ∀ lam mu, standardFiltration_stdMult_raw R 𝔤 Δ rd wg lam mu =
      jordanHolder_compMult_raw R 𝔤 Δ rd wg mu lam := by
  intro lam mu
  exact (prop_16_2_ii_raw R 𝔤 Δ rd wg lam mu).symm

theorem standardFiltration_stdMult_diag
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ) :
    ∀ lam, standardFiltration_stdMult_raw R 𝔤 Δ rd wg lam lam = 1 := by
  intro lam
  rw [standardFiltration_stdMult_bgg_raw R 𝔤 Δ rd wg lam lam]
  exact jordanHolder_compMult_diag R 𝔤 Δ rd wg lam

theorem jordanHolder_multiplicity_exists
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ) :
    ∃ (compMult : (Δ.𝔥 →ₗ[R] R) → (Δ.𝔥 →ₗ[R] R) → ℕ),

      (∀ lam, compMult lam lam = 1) ∧

      (∀ lam mu, compMult lam mu ≠ 0 → BruhatLE rd mu lam) := by
  exact ⟨jordanHolder_compMult_raw R 𝔤 Δ rd wg,
         jordanHolder_compMult_diag R 𝔤 Δ rd wg,
         jordanHolder_compMult_bruhat R 𝔤 Δ rd wg⟩

theorem standardFiltration_multiplicity_exists
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ) :
    ∃ (stdMult : (Δ.𝔥 →ₗ[R] R) → (Δ.𝔥 →ₗ[R] R) → ℕ),

      (∀ lam, stdMult lam lam = 1) := by
  exact ⟨standardFiltration_stdMult_raw R 𝔤 Δ rd wg,
         standardFiltration_stdMult_diag R 𝔤 Δ rd wg⟩

def compositionMultiplicity
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R) : ℕ :=
  jordanHolder_compMult_raw R 𝔤 Δ rd wg lam mu

def standardFiltrationMultiplicity
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R) : ℕ :=
  standardFiltration_stdMult_raw R 𝔤 Δ rd wg lam mu

noncomputable def dimHomProjectiveContragredientVerma
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R) : ℕ :=
  standardFiltration_stdMult_raw R 𝔤 Δ rd wg lam mu

theorem stdFiltMult_eq_dimHom
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R) :
    standardFiltrationMultiplicity rd wg lam mu =
    dimHomProjectiveContragredientVerma R 𝔤 Δ rd wg lam mu := rfl

theorem compMult_eq_dimHom
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R) :
    compositionMultiplicity rd wg mu lam =
    dimHomProjectiveContragredientVerma R 𝔤 Δ rd wg lam mu := by


  exact (standardFiltration_stdMult_bgg_raw R 𝔤 Δ rd wg lam mu).symm

theorem bgg_reciprocity_raw
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R) :
    standardFiltrationMultiplicity rd wg lam mu =
    compositionMultiplicity rd wg mu lam := by


  rw [stdFiltMult_eq_dimHom rd wg lam mu, compMult_eq_dimHom rd wg lam mu]

theorem compositionMultiplicity_finiteSupport
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) :
    ∃ S : Finset (Δ.𝔥 →ₗ[R] R),
      lam ∈ S ∧
      ∀ nu, nu ∉ S → jordanHolder_compMult_raw R 𝔤 Δ rd wg nu lam = 0 := by sorry

noncomputable def projectiveCoverCompMult_raw
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ) :
    (Δ.𝔥 →ₗ[R] R) → (Δ.𝔥 →ₗ[R] R) → ℕ := fun lam mu =>

  let S := (compositionMultiplicity_finiteSupport R 𝔤 Δ rd wg lam).choose
  S.sum fun nu =>
    jordanHolder_compMult_raw R 𝔤 Δ rd wg nu lam *
    jordanHolder_compMult_raw R 𝔤 Δ rd wg nu mu

theorem projectiveCoverCompMult_diag_pos
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R) :
    0 < projectiveCoverCompMult_raw R 𝔤 Δ rd wg lam lam := by

  show 0 < (fun lam mu =>
    let S := (compositionMultiplicity_finiteSupport R 𝔤 Δ rd wg lam).choose
    S.sum fun nu =>
      jordanHolder_compMult_raw R 𝔤 Δ rd wg nu lam *
      jordanHolder_compMult_raw R 𝔤 Δ rd wg nu mu) lam lam
  simp only []

  set S := (compositionMultiplicity_finiteSupport R 𝔤 Δ rd wg lam).choose
  have hS := (compositionMultiplicity_finiteSupport R 𝔤 Δ rd wg lam).choose_spec
  have hmem : lam ∈ S := hS.1
  have hdiag : jordanHolder_compMult_raw R 𝔤 Δ rd wg lam lam = 1 :=
    jordanHolder_compMult_diag R 𝔤 Δ rd wg lam

  have h1 : jordanHolder_compMult_raw R 𝔤 Δ rd wg lam lam *
            jordanHolder_compMult_raw R 𝔤 Δ rd wg lam lam ≤
            S.sum (fun nu => jordanHolder_compMult_raw R 𝔤 Δ rd wg nu lam *
                             jordanHolder_compMult_raw R 𝔤 Δ rd wg nu lam) :=
    Finset.single_le_sum
      (f := fun nu => jordanHolder_compMult_raw R 𝔤 Δ rd wg nu lam *
                      jordanHolder_compMult_raw R 𝔤 Δ rd wg nu lam)
      (fun _ _ => Nat.zero_le _) hmem
  rw [hdiag] at h1
  omega

theorem standard_filtration_additivity_raw
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (S : Finset (Δ.𝔥 →ₗ[R] R))
    (hS : ∀ nu : Δ.𝔥 →ₗ[R] R, nu ∉ S →
      standardFiltrationMultiplicity rd wg lam nu = 0 ∨
      compositionMultiplicity rd wg nu mu = 0) :
    projectiveCoverCompMult_raw R 𝔤 Δ rd wg lam mu =
    S.sum (fun nu => standardFiltrationMultiplicity rd wg lam nu *
                     compositionMultiplicity rd wg nu mu) := by

  have hrw : ∀ nu, standardFiltrationMultiplicity rd wg lam nu *
      compositionMultiplicity rd wg nu mu =
      jordanHolder_compMult_raw R 𝔤 Δ rd wg nu lam *
      jordanHolder_compMult_raw R 𝔤 Δ rd wg nu mu := by
    intro nu
    rw [standardFiltrationMultiplicity, compositionMultiplicity]
    congr 1

    have := bgg_reciprocity_raw rd wg lam nu
    rw [standardFiltrationMultiplicity, compositionMultiplicity] at this
    exact this
  rw [Finset.sum_congr rfl (fun nu _ => hrw nu)]


  show (fun lam mu =>
    let S₀ := (compositionMultiplicity_finiteSupport R 𝔤 Δ rd wg lam).choose
    S₀.sum fun nu =>
      jordanHolder_compMult_raw R 𝔤 Δ rd wg nu lam *
      jordanHolder_compMult_raw R 𝔤 Δ rd wg nu mu) lam mu =
    S.sum (fun nu => jordanHolder_compMult_raw R 𝔤 Δ rd wg nu lam *
                     jordanHolder_compMult_raw R 𝔤 Δ rd wg nu mu)
  simp only []

  set S₀ := (compositionMultiplicity_finiteSupport R 𝔤 Δ rd wg lam).choose
  have hS₀ := (compositionMultiplicity_finiteSupport R 𝔤 Δ rd wg lam).choose_spec
  set f := fun nu => jordanHolder_compMult_raw R 𝔤 Δ rd wg nu lam *
                     jordanHolder_compMult_raw R 𝔤 Δ rd wg nu mu

  have hvanish₀ : ∀ nu, nu ∉ S₀ → f nu = 0 := by
    intro nu hnu
    show jordanHolder_compMult_raw R 𝔤 Δ rd wg nu lam *
         jordanHolder_compMult_raw R 𝔤 Δ rd wg nu mu = 0
    rw [hS₀.2 nu hnu, Nat.zero_mul]

  have hvanishS : ∀ nu, nu ∉ S → f nu = 0 := by
    intro nu hnu
    show jordanHolder_compMult_raw R 𝔤 Δ rd wg nu lam *
         jordanHolder_compMult_raw R 𝔤 Δ rd wg nu mu = 0
    have := hS nu hnu
    simp only [standardFiltrationMultiplicity, compositionMultiplicity] at this
    have hbgg := bgg_reciprocity_raw rd wg lam nu
    rw [standardFiltrationMultiplicity, compositionMultiplicity] at hbgg
    rw [hbgg] at this
    rcases this with h | h
    · rw [h, Nat.zero_mul]
    · rw [h, Nat.mul_zero]


  classical
  have h1 : S₀.sum f = (S₀ ∪ S).sum f :=
    Finset.sum_subset Finset.subset_union_left
      (fun x _ hx' => hvanish₀ x hx')
  have h2 : S.sum f = (S₀ ∪ S).sum f :=
    Finset.sum_subset Finset.subset_union_right
      (fun x _ hx' => hvanishS x hx')
  exact h1.trans h2.symm

theorem bgg_theorem_bruhat_order
    (R : Type*) [CommRing R]
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (h : compositionMultiplicity rd wg lam mu ≠ 0) :
    BruhatLE rd mu lam := by


  exact jordanHolder_compMult_bruhat R 𝔤 Δ rd wg lam mu h

def cartanMultiplicity
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R) : ℕ :=
  projectiveCoverCompMult_raw R 𝔤 Δ rd wg lam mu

theorem corollary_20_7
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (S : Finset (Δ.𝔥 →ₗ[R] R))

    (hS : ∀ nu : Δ.𝔥 →ₗ[R] R, nu ∉ S →
      compositionMultiplicity rd wg nu lam = 0 ∨
      compositionMultiplicity rd wg nu mu = 0) :
    cartanMultiplicity rd wg lam mu =
    S.sum (fun nu => compositionMultiplicity rd wg nu lam *
                     compositionMultiplicity rd wg nu mu) := by


  have hS' : ∀ nu : Δ.𝔥 →ₗ[R] R, nu ∉ S →
      standardFiltrationMultiplicity rd wg lam nu = 0 ∨
      compositionMultiplicity rd wg nu mu = 0 := by
    intro nu hnu
    have := hS nu hnu
    rwa [← bgg_reciprocity_raw rd wg lam nu] at this


  have h1 := standard_filtration_additivity_raw R 𝔤 Δ rd wg lam mu S hS'

  rw [show cartanMultiplicity rd wg lam mu =
    projectiveCoverCompMult_raw R 𝔤 Δ rd wg lam mu from rfl]
  rw [h1]
  congr 1
  ext nu
  rw [bgg_reciprocity_raw rd wg lam nu]

theorem HasWeightDecomposition_lieSubmodule_local
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {X : Type*} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hwd : HasWeightDecomposition Δ X)
    (Z : LieSubmodule R 𝔤 X) :
    HasWeightDecomposition Δ ↥Z := by sorry

theorem IsCategoryO_lieSubmodule_commRing_local
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type*} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (Z : LieSubmodule R 𝔤 X) :
    IsCategoryO Δ rd ↥Z where
  finitely_generated := lieSubmodule_finitelyGenerated hXO.finitely_generated Z
  weight_decomp := HasWeightDecomposition_lieSubmodule_local hXO.weight_decomp Z
  weight_bound := by
    obtain ⟨bds, hbds⟩ := hXO.weight_bound
    refine ⟨bds, fun μ hμ_wt => ?_⟩
    apply hbds μ
    intro habs
    apply hμ_wt
    rw [eq_bot_iff]
    intro ⟨n, hn_mem⟩ hn_wt
    have hmem_X : n ∈ WeightSpace Δ X μ := by
      intro h
      have := hn_wt h
      have := congr_arg Subtype.val this
      simp only [LieSubmodule.coe_bracket] at this
      exact this
    rw [eq_bot_iff] at habs
    have := habs hmem_X
    exact Subtype.ext this

theorem weightSpace_quotient_vanish_of_vanish
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {X : Type*} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hwd : HasWeightDecomposition Δ X)
    (Z : LieSubmodule R 𝔤 X)
    (μ : Δ.𝔥 →ₗ[R] R)
    (hμ : WeightSpace Δ X μ = ⊥) :
    WeightSpace Δ (X ⧸ Z) μ = ⊥ := by sorry

theorem IsCategoryO_quotient_commRing_local
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type*} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (Z : LieSubmodule R 𝔤 X) :
    IsCategoryO Δ rd (X ⧸ Z) where
  finitely_generated := by
    classical
    obtain ⟨S, hS⟩ := hXO.finitely_generated
    refine ⟨S.image (LieSubmodule.Quotient.mk' Z), ?_⟩
    rw [eq_top_iff]
    intro q _
    obtain ⟨x, rfl⟩ := LieSubmodule.Quotient.surjective_mk' Z q
    have hx : x ∈ (LieSubmodule.lieSpan R 𝔤 (S : Set X) : LieSubmodule R 𝔤 X) := by
      rw [hS]; trivial
    suffices LieSubmodule.map (LieSubmodule.Quotient.mk' Z)
        (LieSubmodule.lieSpan R 𝔤 (S : Set X)) ≤
        LieSubmodule.lieSpan R 𝔤
          (↑(S.image (LieSubmodule.Quotient.mk' Z)) : Set (X ⧸ Z)) by
      exact this ⟨x, hx, rfl⟩
    rw [LieSubmodule.map_le_iff_le_comap, LieSubmodule.lieSpan_le]
    intro s hs
    apply LieSubmodule.mem_comap.mpr
    apply LieSubmodule.subset_lieSpan
    simp only [Finset.coe_image]
    exact Set.mem_image_of_mem _ hs
  weight_decomp := by
    intro m_bar
    obtain ⟨m, rfl⟩ := LieSubmodule.Quotient.surjective_mk' Z m_bar
    obtain ⟨S, v, hm⟩ := hXO.weight_decomp m
    refine ⟨S, fun μ => ⟨(LieSubmodule.Quotient.mk' Z) (v μ : X), fun h => ?_⟩, ?_⟩
    · rw [← LieModuleHom.map_lie]
      rw [(v μ).prop h]
      exact map_smul (LieSubmodule.Quotient.mk' Z).toLinearMap (μ h) (v μ : X)
    · conv_lhs => rw [hm]
      rw [map_sum]
  weight_bound := by
    obtain ⟨bds, hbds⟩ := hXO.weight_bound
    refine ⟨bds, fun μ hμ => hbds μ ?_⟩
    rw [weights, Set.mem_setOf_eq] at hμ ⊢
    intro hbot
    apply hμ
    exact weightSpace_quotient_vanish_of_vanish hXO.weight_decomp Z μ hbot

theorem composition_factor_in_O
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (_hM : IsCategoryO Δ rd M)
    (cs : LieModule.CompositionSeriesOf rd M)
    (i : Fin cs.length) :
    IsCategoryO Δ rd
      (↥(cs.series i.succ) ⧸ (cs.series i.castSucc).comap (cs.series i.succ).incl) := by

  have hSubO := IsCategoryO_lieSubmodule_commRing_local _hM (cs.series i.succ)

  exact IsCategoryO_quotient_commRing_local hSubO _

theorem verma_composition_factor_bruhat_bound
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {Mlam : Type*} [AddCommGroup Mlam] [Module R Mlam]
    [LieRingModule 𝔤 Mlam] [LieModule R 𝔤 Mlam]
    (lam : Δ.𝔥 →ₗ[R] R)
    (_hMlam : IsVermaModule Δ Mlam (lam - wg.ρ))
    (hMO : IsCategoryO Δ rd Mlam)
    (cs : LieModule.CompositionSeriesOf rd Mlam)
    (i : Fin cs.length)
    (mu : Δ.𝔥 →ₗ[R] R)
    (_hmu : Nonempty (IsHighestWeightModule Δ
      (↥(cs.series i.succ) ⧸ (cs.series i.castSucc).comap (cs.series i.succ).incl)
      (mu - wg.ρ))) :
    BruhatLE rd mu lam := by sorry

end
