/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.InfinitesimalEquivalenceCore

noncomputable section

theorem norm_of_inner_preserving
    {V₁ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
    {V₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂]
    (S₁ : Submodule ℂ V₁) (S₂ : Submodule ℂ V₂)
    (A : S₁ ≃ₗ[ℂ] S₂)
    (h_inner : ∀ (x y : S₁),
      @inner ℂ V₂ _ (S₂.subtype (A x)) (S₂.subtype (A y)) =
      @inner ℂ V₁ _ (S₁.subtype x) (S₁.subtype y)) :
    ∀ x : S₁, ‖S₂.subtype (A x)‖ = ‖S₁.subtype x‖ := by
  intro x
  have h := h_inner x x
  have h1 := inner_self_eq_norm_sq (𝕜 := ℂ) (S₂.subtype (A x))
  have h2 := inner_self_eq_norm_sq (𝕜 := ℂ) (S₁.subtype x)
  have h3 : RCLike.re (@inner ℂ V₂ _ (S₂.subtype (A x)) (S₂.subtype (A x))) =
    RCLike.re (@inner ℂ V₁ _ (S₁.subtype x) (S₁.subtype x)) := by rw [h]
  rw [h1, h2] at h3
  have ha : (0 : ℝ) ≤ ‖S₂.subtype (A x)‖ := norm_nonneg _
  have hb : (0 : ℝ) ≤ ‖S₁.subtype x‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖S₂.subtype (A x)‖ - ‖S₁.subtype x‖)]

theorem dixmier_schur_sesquilinear
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [InnerProductSpace ℂ F₂] [CompleteSpace F₂]
    (π₁ : ContinuousRep G F₁) (π₂ : ContinuousRep G F₂)
    (K_sub : Subgroup G)
    [hK_compact : CompactSpace K_sub]
    (hunit₁ : π₁.IsUnitary) (hunit₂ : π₂.IsUnitary)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [LieRingModule 𝔤 ↥(π₁.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π₁.kFiniteSubspace K_sub)]
    [LieRingModule 𝔤 ↥(π₂.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π₂.kFiniteSubspace K_sub)]
    (A : ↥(π₁.kFiniteSubspace K_sub) ≃ₗ[ℂ] ↥(π₂.kFiniteSubspace K_sub))
    (hA_lie : ∀ (X : 𝔤) (v : ↥(π₁.kFiniteSubspace K_sub)),
      A ⁅X, v⁆ = ⁅X, A v⁆)
    (hA_K : ∀ (k : K_sub) (v : ↥(π₁.kFiniteSubspace K_sub)),
      A ((kFiniteSubspace_kAction π₁ K_sub) k v) =
        (kFiniteSubspace_kAction π₂ K_sub) k (A v)) :
    ∃ (c : ℂ),
      ∀ (x y : ↥(π₁.kFiniteSubspace K_sub)),
        @inner ℂ F₂ _ ((π₂.kFiniteSubspace K_sub).subtype (A x))
          ((π₂.kFiniteSubspace K_sub).subtype (A y)) =
        c * @inner ℂ F₁ _ ((π₁.kFiniteSubspace K_sub).subtype x)
          ((π₁.kFiniteSubspace K_sub).subtype y) := by


  sorry

theorem pullback_inner_product_proportional
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [InnerProductSpace ℂ F₂] [CompleteSpace F₂]
    (π₁ : ContinuousRep G F₁) (π₂ : ContinuousRep G F₂)
    (K_sub : Subgroup G)
    [hK_compact : CompactSpace K_sub]
    (hunit₁ : π₁.IsUnitary) (hunit₂ : π₂.IsUnitary)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [LieRingModule 𝔤 ↥(π₁.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π₁.kFiniteSubspace K_sub)]
    [LieRingModule 𝔤 ↥(π₂.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π₂.kFiniteSubspace K_sub)]
    (A : ↥(π₁.kFiniteSubspace K_sub) ≃ₗ[ℂ] ↥(π₂.kFiniteSubspace K_sub))
    (hA_lie : ∀ (X : 𝔤) (v : ↥(π₁.kFiniteSubspace K_sub)),
      A ⁅X, v⁆ = ⁅X, A v⁆)
    (hA_K : ∀ (k : K_sub) (v : ↥(π₁.kFiniteSubspace K_sub)),
      A ((kFiniteSubspace_kAction π₁ K_sub) k v) =
        (kFiniteSubspace_kAction π₂ K_sub) k (A v)) :
    ∃ (c : ℝ), 0 < c ∧
      ∀ (x y : ↥(π₁.kFiniteSubspace K_sub)),
        @inner ℂ F₂ _ ((π₂.kFiniteSubspace K_sub).subtype (A x))
          ((π₂.kFiniteSubspace K_sub).subtype (A y)) =
        (↑c : ℂ) * @inner ℂ F₁ _ ((π₁.kFiniteSubspace K_sub).subtype x)
          ((π₁.kFiniteSubspace K_sub).subtype y) := by

  obtain ⟨c_cpx, hc_prop⟩ := dixmier_schur_sesquilinear π₁ π₂ K_sub hunit₁ hunit₂ 𝔤 A hA_lie hA_K

  by_cases htriv : ∀ (v : ↥(π₁.kFiniteSubspace K_sub)), v = 0
  ·
    refine ⟨1, one_pos, fun x y => ?_⟩
    simp only [htriv x, htriv y, map_zero, Submodule.coe_zero, inner_zero_left, mul_zero]
  ·
    push_neg at htriv
    obtain ⟨v₀, hv₀⟩ := htriv

    have hv₀_val : ((π₁.kFiniteSubspace K_sub).subtype v₀ : F₁) ≠ 0 := by
      intro h
      exact hv₀ (Subtype.val_injective h)

    have hAv₀ : A v₀ ≠ 0 := by
      intro h
      exact hv₀ (A.injective (h.trans (map_zero A).symm))
    have hAv₀_val : ((π₂.kFiniteSubspace K_sub).subtype (A v₀) : F₂) ≠ 0 := by
      intro h
      exact hAv₀ (Subtype.val_injective h)

    have hinner₁ : @inner ℂ F₁ _ ((π₁.kFiniteSubspace K_sub).subtype v₀)
        ((π₁.kFiniteSubspace K_sub).subtype v₀) ≠ 0 :=
      inner_self_ne_zero.mpr hv₀_val

    have h_at_v₀ := hc_prop v₀ v₀

    have hc_eq : c_cpx = @inner ℂ F₂ _ ((π₂.kFiniteSubspace K_sub).subtype (A v₀))
        ((π₂.kFiniteSubspace K_sub).subtype (A v₀)) /
        @inner ℂ F₁ _ ((π₁.kFiniteSubspace K_sub).subtype v₀)
        ((π₁.kFiniteSubspace K_sub).subtype v₀) := by
      rw [eq_div_iff hinner₁]
      exact h_at_v₀.symm


    have hpos₁ : 0 < RCLike.re (@inner ℂ F₁ _ ((π₁.kFiniteSubspace K_sub).subtype v₀)
        ((π₁.kFiniteSubspace K_sub).subtype v₀)) :=
      re_inner_self_pos.mpr hv₀_val
    have hpos₂ : 0 < RCLike.re (@inner ℂ F₂ _ ((π₂.kFiniteSubspace K_sub).subtype (A v₀))
        ((π₂.kFiniteSubspace K_sub).subtype (A v₀))) :=
      re_inner_self_pos.mpr hAv₀_val

    set r₁ := RCLike.re (@inner ℂ F₁ _ ((π₁.kFiniteSubspace K_sub).subtype v₀)
        ((π₁.kFiniteSubspace K_sub).subtype v₀))
    set r₂ := RCLike.re (@inner ℂ F₂ _ ((π₂.kFiniteSubspace K_sub).subtype (A v₀))
        ((π₂.kFiniteSubspace K_sub).subtype (A v₀)))

    have hre₁ : @inner ℂ F₁ _ ((π₁.kFiniteSubspace K_sub).subtype v₀)
        ((π₁.kFiniteSubspace K_sub).subtype v₀) = ↑r₁ :=
      (inner_self_ofReal_re _).symm
    have hre₂ : @inner ℂ F₂ _ ((π₂.kFiniteSubspace K_sub).subtype (A v₀))
        ((π₂.kFiniteSubspace K_sub).subtype (A v₀)) = ↑r₂ :=
      (inner_self_ofReal_re _).symm

    have hc_cpx_eq : c_cpx = ↑(r₂ / r₁) := by
      rw [hc_eq, hre₁, hre₂]
      push_cast
      ring
    have hc_pos : 0 < r₂ / r₁ := div_pos hpos₂ hpos₁

    exact ⟨r₂ / r₁, hc_pos, fun x y => by rw [hc_prop x y, hc_cpx_eq]⟩

theorem schur_inner_product_preservation
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [InnerProductSpace ℂ F₂] [CompleteSpace F₂]
    (π₁ : ContinuousRep G F₁) (π₂ : ContinuousRep G F₂)
    (K_sub : Subgroup G)
    [hK_compact : CompactSpace K_sub]
    (hunit₁ : π₁.IsUnitary) (hunit₂ : π₂.IsUnitary)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [LieRingModule 𝔤 ↥(π₁.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π₁.kFiniteSubspace K_sub)]
    [LieRingModule 𝔤 ↥(π₂.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π₂.kFiniteSubspace K_sub)]
    (A : ↥(π₁.kFiniteSubspace K_sub) ≃ₗ[ℂ] ↥(π₂.kFiniteSubspace K_sub))
    (hA_lie : ∀ (X : 𝔤) (v : ↥(π₁.kFiniteSubspace K_sub)),
      A ⁅X, v⁆ = ⁅X, A v⁆)
    (hA_K : ∀ (k : K_sub) (v : ↥(π₁.kFiniteSubspace K_sub)),
      A ((kFiniteSubspace_kAction π₁ K_sub) k v) =
        (kFiniteSubspace_kAction π₂ K_sub) k (A v)) :
    ∃ (B : ↥(π₁.kFiniteSubspace K_sub) ≃ₗ[ℂ] ↥(π₂.kFiniteSubspace K_sub)),
      (∀ (X : 𝔤) (v : ↥(π₁.kFiniteSubspace K_sub)),
        B ⁅X, v⁆ = ⁅X, B v⁆) ∧
      (∀ (k : K_sub) (v : ↥(π₁.kFiniteSubspace K_sub)),
        B ((kFiniteSubspace_kAction π₁ K_sub) k v) =
          (kFiniteSubspace_kAction π₂ K_sub) k (B v)) ∧
      (∀ (x y : ↥(π₁.kFiniteSubspace K_sub)),
        @inner ℂ F₂ _ ((π₂.kFiniteSubspace K_sub).subtype (B x))
          ((π₂.kFiniteSubspace K_sub).subtype (B y)) =
        @inner ℂ F₁ _ ((π₁.kFiniteSubspace K_sub).subtype x)
          ((π₁.kFiniteSubspace K_sub).subtype y)) := by

  obtain ⟨c, hc_pos, hc_prop⟩ :=
    pullback_inner_product_proportional π₁ π₂ K_sub hunit₁ hunit₂ 𝔤 A hA_lie hA_K

  set s : ℝ := (Real.sqrt c)⁻¹ with hs_def
  set sc : ℂ := (↑s : ℂ) with hsc_def
  have hc_ne : c ≠ 0 := ne_of_gt hc_pos
  have hsqrt_pos : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc_pos
  have hsqrt_ne : Real.sqrt c ≠ 0 := ne_of_gt hsqrt_pos
  have hs_ne : s ≠ 0 := inv_ne_zero hsqrt_ne
  have hsc_ne : sc ≠ 0 := Complex.ofReal_ne_zero.mpr hs_ne

  let B : ↥(π₁.kFiniteSubspace K_sub) ≃ₗ[ℂ] ↥(π₂.kFiniteSubspace K_sub) :=
    { toFun := fun v => sc • A v
      invFun := fun w => A.symm (sc⁻¹ • w)
      left_inv := fun v => by
        simp only [LinearEquiv.symm_apply_apply, smul_smul,
          inv_mul_cancel₀ hsc_ne, one_smul]
      right_inv := fun w => by
        simp only [map_smul, LinearEquiv.apply_symm_apply, smul_smul,
          mul_inv_cancel₀ hsc_ne, one_smul]
      map_add' := fun x y => by simp [smul_add, map_add]
      map_smul' := fun r x => by
        simp only [map_smul, RingHom.id_apply, smul_comm sc r] }

  refine ⟨B, ?_, ?_, ?_⟩

  · intro X v
    show sc • A ⁅X, v⁆ = ⁅X, sc • A v⁆
    rw [hA_lie, lie_smul]

  · intro k v
    show sc • A ((kFiniteSubspace_kAction π₁ K_sub) k v) =
      (kFiniteSubspace_kAction π₂ K_sub) k (sc • A v)
    rw [hA_K, map_smul]

  · intro x y

    show @inner ℂ F₂ _ ((π₂.kFiniteSubspace K_sub).subtype (sc • A x))
        ((π₂.kFiniteSubspace K_sub).subtype (sc • A y)) =
      @inner ℂ F₁ _ ((π₁.kFiniteSubspace K_sub).subtype x)
        ((π₁.kFiniteSubspace K_sub).subtype y)
    simp only [map_smul]
    rw [inner_smul_left, inner_smul_right, hc_prop, Complex.conj_ofReal]


    have hfactor : sc * (sc * ((↑c : ℂ) *
        @inner ℂ F₁ _ ((π₁.kFiniteSubspace K_sub).subtype x)
          ((π₁.kFiniteSubspace K_sub).subtype y))) =
        (sc * sc * (↑c : ℂ)) *
        @inner ℂ F₁ _ ((π₁.kFiniteSubspace K_sub).subtype x)
          ((π₁.kFiniteSubspace K_sub).subtype y) := by ring
    rw [hfactor]

    have hone : sc * sc * (↑c : ℂ) = 1 := by
      rw [hsc_def, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
      norm_cast
      rw [hs_def, ← sq (Real.sqrt c)⁻¹, inv_pow, Real.sq_sqrt hc_pos.le,
        inv_mul_cancel₀ hc_ne]
    rw [hone, one_mul]

theorem schur_norm_preservation
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [InnerProductSpace ℂ F₂] [CompleteSpace F₂]
    (π₁ : ContinuousRep G F₁) (π₂ : ContinuousRep G F₂)
    (K_sub : Subgroup G)
    [hK_compact : CompactSpace K_sub]
    (hunit₁ : π₁.IsUnitary) (hunit₂ : π₂.IsUnitary)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [LieRingModule 𝔤 ↥(π₁.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π₁.kFiniteSubspace K_sub)]
    [LieRingModule 𝔤 ↥(π₂.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π₂.kFiniteSubspace K_sub)]
    (A : ↥(π₁.kFiniteSubspace K_sub) ≃ₗ[ℂ] ↥(π₂.kFiniteSubspace K_sub))
    (hA_lie : ∀ (X : 𝔤) (v : ↥(π₁.kFiniteSubspace K_sub)),
      A ⁅X, v⁆ = ⁅X, A v⁆)
    (hA_K : ∀ (k : K_sub) (v : ↥(π₁.kFiniteSubspace K_sub)),
      A ((kFiniteSubspace_kAction π₁ K_sub) k v) =
        (kFiniteSubspace_kAction π₂ K_sub) k (A v)) :
    ∃ (B : ↥(π₁.kFiniteSubspace K_sub) ≃ₗ[ℂ] ↥(π₂.kFiniteSubspace K_sub)),
      (∀ (X : 𝔤) (v : ↥(π₁.kFiniteSubspace K_sub)),
        B ⁅X, v⁆ = ⁅X, B v⁆) ∧
      (∀ (k : K_sub) (v : ↥(π₁.kFiniteSubspace K_sub)),
        B ((kFiniteSubspace_kAction π₁ K_sub) k v) =
          (kFiniteSubspace_kAction π₂ K_sub) k (B v)) ∧
      (∀ x : ↑(π₁.kFiniteSubspace K_sub),
          ‖(π₂.kFiniteSubspace K_sub).subtype (B x)‖ =
          ‖(π₁.kFiniteSubspace K_sub).subtype x‖) := by

  obtain ⟨B, hB_lie, hB_K, hB_inner⟩ :=
    schur_inner_product_preservation π₁ π₂ K_sub hunit₁ hunit₂ 𝔤 A hA_lie hA_K

  exact ⟨B, hB_lie, hB_K,
    norm_of_inner_preserving (π₁.kFiniteSubspace K_sub) (π₂.kFiniteSubspace K_sub) B hB_inner⟩


theorem analytic_cross_space_intertwining
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [InnerProductSpace ℂ F₂] [CompleteSpace F₂]
    (π₁ : ContinuousRep G F₁) (π₂ : ContinuousRep G F₂)
    (K_sub : Subgroup G) [CompactSpace K_sub]
    (_hadm₁ : π₁.IsAdmissible K_sub) (_hadm₂ : π₂.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (ι₁ : 𝔤 →ₗ⁅ℂ⁆ (F₁ →ₗ[ℂ] F₁))
    (ι₂ : 𝔤 →ₗ⁅ℂ⁆ (F₂ →ₗ[ℂ] F₂))
    (T : F₁ ≃ₗᵢ[ℂ] F₂)
    (v : F₁) (_hv : v ∈ π₁.kFiniteSubspace K_sub)
    (_hTv : T v ∈ π₂.kFiniteSubspace K_sub)
    (h : F₂ →L[ℂ] ℂ)
    (hiter_eq : ∀ (Xs : List 𝔤),
      h (T (iterLieAction ι₁ Xs v)) = h (iterLieAction ι₂ Xs (T v)))
    (g : G) : h (T (π₁.toMonoidHom g v)) = h (π₂.toMonoidHom g (T v)) := by
  sorry

theorem hc_equivariance_kfinite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H' : Type*} [TopologicalSpace H']
    (I : ModelWithCorners ℝ E H')
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [InnerProductSpace ℂ F₂] [CompleteSpace F₂]
    (π₁ : ContinuousRep G F₁) (π₂ : ContinuousRep G F₂)
    (K_sub : Subgroup G)
    [hK_compact : CompactSpace K_sub]
    (hunit₁ : π₁.IsUnitary) (hunit₂ : π₂.IsUnitary)
    (hadm₁ : π₁.IsAdmissible K_sub) (hadm₂ : π₂.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [LieRingModule 𝔤 ↥(π₁.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π₁.kFiniteSubspace K_sub)]
    [LieRingModule 𝔤 ↥(π₂.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π₂.kFiniteSubspace K_sub)]
    (ι₁ : 𝔤 →ₗ⁅ℂ⁆ (F₁ →ₗ[ℂ] F₁))
    (ι₂ : 𝔤 →ₗ⁅ℂ⁆ (F₂ →ₗ[ℂ] F₂))
    (hι₁_compat : ∀ (X : 𝔤) (v : ↥(π₁.kFiniteSubspace K_sub)),
      (ι₁ X) ((π₁.kFiniteSubspace K_sub).subtype v) =
      (π₁.kFiniteSubspace K_sub).subtype ⁅X, v⁆)
    (hι₂_compat : ∀ (X : 𝔤) (v : ↥(π₂.kFiniteSubspace K_sub)),
      (ι₂ X) ((π₂.kFiniteSubspace K_sub).subtype v) =
      (π₂.kFiniteSubspace K_sub).subtype ⁅X, v⁆)
    (A : ↥(π₁.kFiniteSubspace K_sub) ≃ₗ[ℂ] ↥(π₂.kFiniteSubspace K_sub))
    (hA_lie : ∀ (X : 𝔤) (v : ↥(π₁.kFiniteSubspace K_sub)),
      A ⁅X, v⁆ = ⁅X, A v⁆)
    (hA_K : ∀ (k : K_sub) (v : ↥(π₁.kFiniteSubspace K_sub)),
      A ((kFiniteSubspace_kAction π₁ K_sub) k v) =
        (kFiniteSubspace_kAction π₂ K_sub) k (A v))
    (h_dense₁ : DenseRange (π₁.kFiniteSubspace K_sub).subtype)
    (h_dense₂ : DenseRange (π₂.kFiniteSubspace K_sub).subtype)
    (h_norm : ∀ x : ↑(π₁.kFiniteSubspace K_sub),
        ‖(π₂.kFiniteSubspace K_sub).subtype (A x)‖ =
        ‖(π₁.kFiniteSubspace K_sub).subtype x‖)
    (hι₁_stable : ∀ (X : 𝔤) (v : F₁), v ∈ π₁.kFiniteSubspace K_sub →
      (ι₁ X) v ∈ π₁.kFiniteSubspace K_sub)
    (hι₂_stable : ∀ (X : 𝔤) (v : F₂), v ∈ π₂.kFiniteSubspace K_sub →
      (ι₂ X) v ∈ π₂.kFiniteSubspace K_sub) :
    ∀ (g : G) (x : ↑(π₁.kFiniteSubspace K_sub)),
      (A.extendOfIsometry (π₁.kFiniteSubspace K_sub).subtype
        (π₂.kFiniteSubspace K_sub).subtype h_dense₁ h_dense₂ h_norm)
        (π₁.toMonoidHom g ((π₁.kFiniteSubspace K_sub).subtype x)) =
      π₂.toMonoidHom g
        ((A.extendOfIsometry (π₁.kFiniteSubspace K_sub).subtype
          (π₂.kFiniteSubspace K_sub).subtype h_dense₁ h_dense₂ h_norm)
          ((π₁.kFiniteSubspace K_sub).subtype x)) := by

  set T := A.extendOfIsometry (π₁.kFiniteSubspace K_sub).subtype
    (π₂.kFiniteSubspace K_sub).subtype h_dense₁ h_dense₂ h_norm with hT_def

  have hT_on_kfin : ∀ y : ↥(π₁.kFiniteSubspace K_sub),
      T ((π₁.kFiniteSubspace K_sub).subtype y) =
      (π₂.kFiniteSubspace K_sub).subtype (A y) :=
    fun y => A.extendOfIsometry_eq (π₁.kFiniteSubspace K_sub).subtype
      (π₂.kFiniteSubspace K_sub).subtype h_dense₁ h_dense₂ h_norm y
  intro g x

  rw [NormedSpace.eq_iff_forall_dual_eq ℂ]
  intro h

  have hv_kfin : (π₁.kFiniteSubspace K_sub).subtype x ∈ π₁.kFiniteSubspace K_sub :=
    Submodule.coe_mem x
  have hTv_kfin : T ((π₁.kFiniteSubspace K_sub).subtype x) ∈ π₂.kFiniteSubspace K_sub := by
    rw [hT_on_kfin x]
    exact Submodule.coe_mem (A x)
  apply analytic_cross_space_intertwining I π₁ π₂ K_sub hadm₁ hadm₂ 𝔤 ι₁ ι₂
    T ((π₁.kFiniteSubspace K_sub).subtype x) hv_kfin hTv_kfin h


  have hT_iter : ∀ (Xs : List 𝔤),
      T (iterLieAction ι₁ Xs ((π₁.kFiniteSubspace K_sub).subtype x)) =
      iterLieAction ι₂ Xs (T ((π₁.kFiniteSubspace K_sub).subtype x)) := by
    intro Xs
    induction Xs with
    | nil => simp [iterLieAction]
    | cons X Xs ih =>

      show T ((ι₁ X) (iterLieAction ι₁ Xs ((π₁.kFiniteSubspace K_sub).subtype x))) =
        (ι₂ X) (iterLieAction ι₂ Xs (T ((π₁.kFiniteSubspace K_sub).subtype x)))

      have h_mem₁ : iterLieAction ι₁ Xs ((π₁.kFiniteSubspace K_sub).subtype x) ∈
          π₁.kFiniteSubspace K_sub :=
        iterLieAction_mem_kFiniteSubspace I π₁ K_sub 𝔤 ι₁ hι₁_stable Xs _ hv_kfin

      set w₁ := (⟨iterLieAction ι₁ Xs ((π₁.kFiniteSubspace K_sub).subtype x), h_mem₁⟩ :
          ↥(π₁.kFiniteSubspace K_sub))

      have hw₁_eq : (π₁.kFiniteSubspace K_sub).subtype w₁ =
          iterLieAction ι₁ Xs ((π₁.kFiniteSubspace K_sub).subtype x) := rfl

      rw [← hw₁_eq, hι₁_compat X w₁, hT_on_kfin ⁅X, w₁⁆]

      rw [hA_lie X w₁]

      rw [← hι₂_compat X (A w₁)]

      rw [← hT_on_kfin w₁, hw₁_eq, ih]

  intro Xs
  exact congr_arg h (hT_iter Xs)

theorem proposition_7_1_schur_and_analytic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H' : Type*} [TopologicalSpace H']
    (I : ModelWithCorners ℝ E H')
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [InnerProductSpace ℂ F₂] [CompleteSpace F₂]
    (π₁ : ContinuousRep G F₁) (π₂ : ContinuousRep G F₂)
    (K_sub : Subgroup G)
    [hK_compact : CompactSpace K_sub]
    (hunit₁ : π₁.IsUnitary) (hunit₂ : π₂.IsUnitary)
    (hadm₁ : π₁.IsAdmissible K_sub) (hadm₂ : π₂.IsAdmissible K_sub)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [LieRingModule 𝔤 ↥(π₁.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π₁.kFiniteSubspace K_sub)]
    [LieRingModule 𝔤 ↥(π₂.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π₂.kFiniteSubspace K_sub)]
    (ι₁ : 𝔤 →ₗ⁅ℂ⁆ (F₁ →ₗ[ℂ] F₁))
    (ι₂ : 𝔤 →ₗ⁅ℂ⁆ (F₂ →ₗ[ℂ] F₂))
    (hι₁_compat : ∀ (X : 𝔤) (v : ↥(π₁.kFiniteSubspace K_sub)),
      (ι₁ X) ((π₁.kFiniteSubspace K_sub).subtype v) =
      (π₁.kFiniteSubspace K_sub).subtype ⁅X, v⁆)
    (hι₂_compat : ∀ (X : 𝔤) (v : ↥(π₂.kFiniteSubspace K_sub)),
      (ι₂ X) ((π₂.kFiniteSubspace K_sub).subtype v) =
      (π₂.kFiniteSubspace K_sub).subtype ⁅X, v⁆)
    (A : ↥(π₁.kFiniteSubspace K_sub) ≃ₗ[ℂ] ↥(π₂.kFiniteSubspace K_sub))
    (hA_lie : ∀ (X : 𝔤) (v : ↥(π₁.kFiniteSubspace K_sub)),
      A ⁅X, v⁆ = ⁅X, A v⁆)
    (hA_K : ∀ (k : K_sub) (v : ↥(π₁.kFiniteSubspace K_sub)),
      A ((kFiniteSubspace_kAction π₁ K_sub) k v) =
        (kFiniteSubspace_kAction π₂ K_sub) k (A v))
    (h_dense₁ : DenseRange (π₁.kFiniteSubspace K_sub).subtype)
    (h_dense₂ : DenseRange (π₂.kFiniteSubspace K_sub).subtype)
    (hι₁_stable : ∀ (X : 𝔤) (v : F₁), v ∈ π₁.kFiniteSubspace K_sub →
      (ι₁ X) v ∈ π₁.kFiniteSubspace K_sub)
    (hι₂_stable : ∀ (X : 𝔤) (v : F₂), v ∈ π₂.kFiniteSubspace K_sub →
      (ι₂ X) v ∈ π₂.kFiniteSubspace K_sub) :
    ∃ (B : ↥(π₁.kFiniteSubspace K_sub) ≃ₗ[ℂ] ↥(π₂.kFiniteSubspace K_sub))
      (hB_lie : ∀ (X : 𝔤) (v : ↥(π₁.kFiniteSubspace K_sub)),
        B ⁅X, v⁆ = ⁅X, B v⁆)
      (hB_K : ∀ (k : K_sub) (v : ↥(π₁.kFiniteSubspace K_sub)),
        B ((kFiniteSubspace_kAction π₁ K_sub) k v) =
          (kFiniteSubspace_kAction π₂ K_sub) k (B v))
      (h_norm : ∀ x : ↑(π₁.kFiniteSubspace K_sub),
          ‖(π₂.kFiniteSubspace K_sub).subtype (B x)‖ =
          ‖(π₁.kFiniteSubspace K_sub).subtype x‖),
    ∀ (g : G) (x : ↑(π₁.kFiniteSubspace K_sub)),
      (B.extendOfIsometry (π₁.kFiniteSubspace K_sub).subtype
        (π₂.kFiniteSubspace K_sub).subtype h_dense₁ h_dense₂ h_norm)
        (π₁.toMonoidHom g ((π₁.kFiniteSubspace K_sub).subtype x)) =
      π₂.toMonoidHom g
        ((B.extendOfIsometry (π₁.kFiniteSubspace K_sub).subtype
          (π₂.kFiniteSubspace K_sub).subtype h_dense₁ h_dense₂ h_norm)
          ((π₁.kFiniteSubspace K_sub).subtype x)) := by

  obtain ⟨B, hB_lie, hB_K, h_norm⟩ :=
    schur_norm_preservation π₁ π₂ K_sub hunit₁ hunit₂ 𝔤 A hA_lie hA_K

  exact ⟨B, hB_lie, hB_K, h_norm, hc_equivariance_kfinite I π₁ π₂ K_sub hunit₁ hunit₂ hadm₁ hadm₂ 𝔤
    ι₁ ι₂ hι₁_compat hι₂_compat B hB_lie hB_K h_dense₁ h_dense₂ h_norm hι₁_stable hι₂_stable⟩

theorem equivariance_extends_from_dense
    {G : Type*} [Group G] [TopologicalSpace G]
    {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [InnerProductSpace ℂ F₂] [CompleteSpace F₂]
    (π₁ : ContinuousRep G F₁) (π₂ : ContinuousRep G F₂)
    (T : F₁ ≃ₗᵢ[ℂ] F₂)
    {S : Type*} [TopologicalSpace S]
    (ι : S → F₁) (h_dense : DenseRange ι)
    (h_agree : ∀ (g : G) (s : S),
      T (π₁.toMonoidHom g (ι s)) = π₂.toMonoidHom g (T (ι s))) :
    ∀ (g : G) (v : F₁),
      T (π₁.toMonoidHom g v) = π₂.toMonoidHom g (T v) := by
  intro g
  have hT_cont : Continuous T := T.continuous
  have hπ₁g_cont : Continuous (π₁.toMonoidHom g) := (π₁.toMonoidHom g).continuous
  have hπ₂g_cont : Continuous (π₂.toMonoidHom g) := (π₂.toMonoidHom g).continuous
  have h_lhs_cont : Continuous (fun v => T (π₁.toMonoidHom g v)) :=
    hT_cont.comp hπ₁g_cont
  have h_rhs_cont : Continuous (fun v => π₂.toMonoidHom g (T v)) :=
    hπ₂g_cont.comp hT_cont
  have h_eq_on_dense :
      (fun v => T (π₁.toMonoidHom g v)) ∘ ι =
      (fun v => π₂.toMonoidHom g (T v)) ∘ ι :=
    funext (fun s => h_agree g s)
  exact fun v => congr_fun
    (DenseRange.equalizer h_dense h_lhs_cont h_rhs_cont h_eq_on_dense) v

theorem proposition_7_1
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H' : Type*} [TopologicalSpace H']
    (I : ModelWithCorners ℝ E H')
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H' G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F₁ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
    {F₂ : Type*} [NormedAddCommGroup F₂] [InnerProductSpace ℂ F₂] [CompleteSpace F₂]
    (π₁ : ContinuousRep G F₁) (π₂ : ContinuousRep G F₂)
    (K_sub : Subgroup G)
    [hK_compact : CompactSpace K_sub]

    (hunit₁ : π₁.IsUnitary) (hunit₂ : π₂.IsUnitary)
    (hadm₁ : π₁.IsAdmissible K_sub) (hadm₂ : π₂.IsAdmissible K_sub)

    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    [LieRingModule 𝔤 ↥(π₁.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π₁.kFiniteSubspace K_sub)]
    [LieRingModule 𝔤 ↥(π₂.kFiniteSubspace K_sub)]
    [LieModule ℂ 𝔤 ↥(π₂.kFiniteSubspace K_sub)]
    (ι₁ : 𝔤 →ₗ⁅ℂ⁆ (F₁ →ₗ[ℂ] F₁))
    (ι₂ : 𝔤 →ₗ⁅ℂ⁆ (F₂ →ₗ[ℂ] F₂))
    (hι₁_compat : ∀ (X : 𝔤) (v : ↥(π₁.kFiniteSubspace K_sub)),
      (ι₁ X) ((π₁.kFiniteSubspace K_sub).subtype v) =
      (π₁.kFiniteSubspace K_sub).subtype ⁅X, v⁆)
    (hι₂_compat : ∀ (X : 𝔤) (v : ↥(π₂.kFiniteSubspace K_sub)),
      (ι₂ X) ((π₂.kFiniteSubspace K_sub).subtype v) =
      (π₂.kFiniteSubspace K_sub).subtype ⁅X, v⁆)


    (A : ↥(π₁.kFiniteSubspace K_sub) ≃ₗ[ℂ] ↥(π₂.kFiniteSubspace K_sub))
    (hA_lie : ∀ (X : 𝔤) (v : ↥(π₁.kFiniteSubspace K_sub)),
      A ⁅X, v⁆ = ⁅X, A v⁆)
    (hA_K : ∀ (k : K_sub) (v : ↥(π₁.kFiniteSubspace K_sub)),
      A ((kFiniteSubspace_kAction π₁ K_sub) k v) =
        (kFiniteSubspace_kAction π₂ K_sub) k (A v))
    (hι₁_stable : ∀ (X : 𝔤) (v : F₁), v ∈ π₁.kFiniteSubspace K_sub →
      (ι₁ X) v ∈ π₁.kFiniteSubspace K_sub)
    (hι₂_stable : ∀ (X : 𝔤) (v : F₂), v ∈ π₂.kFiniteSubspace K_sub →
      (ι₂ X) v ∈ π₂.kFiniteSubspace K_sub) :

    Nonempty (UnitaryRepEquiv π₁ π₂) := by


  have h_dense₁ : DenseRange (π₁.kFiniteSubspace K_sub).subtype :=
    (ContinuousRep.kFiniteSubspace_dense π₁ K_sub).denseRange_val
  have h_dense₂ : DenseRange (π₂.kFiniteSubspace K_sub).subtype :=
    (ContinuousRep.kFiniteSubspace_dense π₂ K_sub).denseRange_val


  obtain ⟨B, _hB_lie, _hB_K, h_norm, h_equiv_kfin⟩ :=
    proposition_7_1_schur_and_analytic I π₁ π₂ K_sub hunit₁ hunit₂ hadm₁ hadm₂ 𝔤
      ι₁ ι₂ hι₁_compat hι₂_compat A hA_lie hA_K h_dense₁ h_dense₂ hι₁_stable hι₂_stable

  let T := B.extendOfIsometry (π₁.kFiniteSubspace K_sub).subtype
    (π₂.kFiniteSubspace K_sub).subtype h_dense₁ h_dense₂ h_norm


  have h_equiv : ∀ (g : G) (v : F₁),
      T (π₁.toMonoidHom g v) = π₂.toMonoidHom g (T v) :=
    equivariance_extends_from_dense π₁ π₂ T
      (π₁.kFiniteSubspace K_sub).subtype h_dense₁
      (fun g x => h_equiv_kfin g x)
  exact ⟨{
    toContinuousLinearEquiv := T.toContinuousLinearEquiv
    intertwines := fun g => ContinuousLinearMap.ext (fun v => h_equiv g v)
    inner_preserving := fun v w => LinearIsometryEquiv.inner_map_map T v w
  }⟩

end
