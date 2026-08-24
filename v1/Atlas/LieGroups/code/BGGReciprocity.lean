/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.CompositionSeries
import Atlas.LieGroups.code.DualityFunctorDefs

noncomputable section

universe uCatO

variable (R : Type*) [CommRing R]
variable (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {R 𝔤}

def HasStandardFiltration
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (V : Type uCatO) [AddCommGroup V] [Module R V]
    [LieRingModule 𝔤 V] [LieModule R 𝔤 V]
    (_hV : IsCategoryO Δ rd V) : Prop :=
  ∃ (n : ℕ) (F : Fin (n + 1) → LieSubmodule R 𝔤 V),
    F ⟨0, Nat.zero_lt_succ n⟩ = ⊥ ∧
    F ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ = ⊤ ∧
    (∀ i : Fin n, F i.castSucc < F i.succ) ∧


    (∀ i : Fin n, ∃ (lam_i : Δ.𝔥 →ₗ[R] R)
      (Q : Type uCatO) (_ : AddCommGroup Q) (_ : Module R Q)
      (_ : LieRingModule 𝔤 Q) (_ : LieModule R 𝔤 Q)
      (_ : IsVermaModule Δ Q lam_i)
      (π : ↥(F i.succ) →ₗ⁅R, 𝔤⁆ Q),
      Function.Surjective π ∧
      (∀ x : ↥(F i.succ), π x = 0 ↔ (x : V) ∈ F i.castSucc))

def Ext1VanishingForContragredientVerma
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (X : Type uCatO) [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (_hXO : IsCategoryO Δ rd X) : Prop :=
  ∀ (lam : Δ.𝔥 →ₗ[R] R)
    (MlamDual : Type uCatO) [AddCommGroup MlamDual] [Module R MlamDual]
    [LieRingModule 𝔤 MlamDual] [LieModule R 𝔤 MlamDual]
    (hMlamDualO : IsCategoryO Δ rd MlamDual)
    (_hContra : IsContragredientVerma rd MlamDual lam hMlamDualO)
    (E : Type uCatO) [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    (_hEO : IsCategoryO Δ rd E)
    (i : MlamDual →ₗ⁅R, 𝔤⁆ E) (_hi : Function.Injective i)
    (p : E →ₗ⁅R, 𝔤⁆ X) (_hp : Function.Surjective p)

    (_hexact : ∀ e : E, p e = 0 ↔ ∃ m : MlamDual, i m = e),
    ∃ (s : X →ₗ⁅R, 𝔤⁆ E), ∀ x, p (s x) = x

noncomputable def CategoryO.compositionLengthO
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (X : Type uCatO) [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X) : ℕ :=
  (Classical.choice (categoryO_has_composition_series hXO)).length

theorem CategoryO.subsingleton_of_compositionLengthO_zero
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (X : Type uCatO) [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hlen : CategoryO.compositionLengthO X hXO = 0) :
    ∀ (x : X), x = 0 := by
  set cs := Classical.choice (categoryO_has_composition_series hXO) with hcs_def
  have h_len_eq : cs.length = 0 := hlen
  have h_bot := cs.bot
  have h_top := cs.top
  have h_idx : (⟨0, Nat.zero_lt_succ cs.length⟩ : Fin (cs.length + 1)) =
               ⟨cs.length, Nat.lt_succ_iff.mpr le_rfl⟩ := by
    ext; simp [h_len_eq]
  have h_eq : (⊤ : LieSubmodule R 𝔤 X) = ⊥ := by
    rw [← h_top, ← h_bot, h_idx]
  intro x
  have hx : x ∈ (⊤ : LieSubmodule R 𝔤 X) := LieSubmodule.mem_top x
  rw [h_eq] at hx
  exact (LieSubmodule.mem_bot (R := R) x).mp hx

theorem CategoryO.maximal_weight_hwv_exists
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hlen : CategoryO.compositionLengthO X hXO ≠ 0) :
    ∃ (lam : Δ.𝔥 →ₗ[R] R) (v : X),
      v ≠ 0 ∧
      (∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = lam h • v) ∧
      (∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v⁆ = 0) := by

  haveI : Nontrivial X := by
    by_contra h
    haveI : Subsingleton X := not_nontrivial_iff_subsingleton.mp h
    apply hlen

    have hall : ∀ (x : X), x = 0 := fun x => Subsingleton.elim x 0
    have htop_eq_bot : (⊤ : LieSubmodule R 𝔤 X) = ⊥ := by
      ext x; constructor
      · intro _; exact (LieSubmodule.mem_bot (R := R) x).mpr (hall x)
      · intro _; exact LieSubmodule.mem_top x

    show (Classical.choice (categoryO_has_composition_series hXO)).length = 0
    set cs := Classical.choice (categoryO_has_composition_series hXO)

    by_contra hlen0
    have hlen_pos : 0 < cs.length := Nat.pos_of_ne_zero hlen0
    have hstrict := cs.strictly_increasing ⟨0, hlen_pos⟩
    have h0 : cs.series ⟨0, Nat.zero_lt_succ cs.length⟩ = ⊥ := cs.bot
    have h1_le : cs.series (Fin.succ ⟨0, hlen_pos⟩) ≤ ⊥ := by
      calc cs.series (Fin.succ ⟨0, hlen_pos⟩) ≤ ⊤ := le_top
        _ = ⊥ := htop_eq_bot
    have h1_eq : cs.series (Fin.succ ⟨0, hlen_pos⟩) = ⊥ :=
      le_antisymm h1_le bot_le
    have h0_eq : cs.series (Fin.castSucc ⟨0, hlen_pos⟩) = ⊥ := by
      have : Fin.castSucc (⟨0, hlen_pos⟩ : Fin cs.length) = ⟨0, Nat.zero_lt_succ cs.length⟩ :=
        Fin.ext rfl
      rw [this]; exact h0
    rw [h0_eq, h1_eq] at hstrict
    exact lt_irrefl _ hstrict

  obtain ⟨v, lam, hv_ne, hv_wt, hv_killed⟩ := CategoryO.exists_singular_vector hXO
  exact ⟨lam, v, hv_ne, hv_wt, hv_killed⟩

theorem CategoryO.ext_vanishing_verma_iso
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hlen : CategoryO.compositionLengthO X hXO ≠ 0)
    (hExt : Ext1VanishingForContragredientVerma rd X hXO)
    (lam : Δ.𝔥 →ₗ[R] R) (v : X)
    (hv_ne : v ≠ 0)
    (hv_wt : ∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = lam h • v)
    (hv_npos : ∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v⁆ = 0) :
    ∃ (Z : LieSubmodule R 𝔤 X)
      (Q : Type uCatO) (_ : AddCommGroup Q) (_ : Module R Q)
      (_ : LieRingModule 𝔤 Q) (_ : LieModule R 𝔤 Q)
      (_ : IsVermaModule Δ Q lam)
      (π : ↥Z →ₗ⁅R, 𝔤⁆ Q),
      v ∈ Z ∧
      Function.Surjective π ∧
      (∀ x : ↥Z, π x = 0 ↔ (x : X) ∈ (⊥ : LieSubmodule R 𝔤 X)) ∧
      Z ≠ ⊤ := by

  sorry

theorem CategoryO.maximal_weight_verma_submodule
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hlen : CategoryO.compositionLengthO X hXO ≠ 0)
    (hExt : Ext1VanishingForContragredientVerma rd X hXO) :
    ∃ (Z : LieSubmodule R 𝔤 X)
      (lam_step : Δ.𝔥 →ₗ[R] R)
      (Q : Type uCatO) (_ : AddCommGroup Q) (_ : Module R Q)
      (_ : LieRingModule 𝔤 Q) (_ : LieModule R 𝔤 Q)
      (_ : IsVermaModule Δ Q lam_step)
      (π : ↥Z →ₗ⁅R, 𝔤⁆ Q),
      Function.Surjective π ∧
      (∀ x : ↥Z, π x = 0 ↔ (x : X) ∈ (⊥ : LieSubmodule R 𝔤 X)) ∧
      Z ≠ ⊤ := by

  obtain ⟨lam, v, hv_ne, hv_wt, hv_npos⟩ :=
    CategoryO.maximal_weight_hwv_exists hXO hlen

  obtain ⟨Z, Q, instQ1, instQ2, instQ3, instQ4, hVerma, π, _, hπ_surj, hπ_ker, hZ_ne_top⟩ :=
    CategoryO.ext_vanishing_verma_iso hXO hlen hExt lam v hv_ne hv_wt hv_npos
  exact ⟨Z, lam, Q, instQ1, instQ2, instQ3, instQ4, hVerma, π, hπ_surj, hπ_ker, hZ_ne_top⟩


theorem HasWeightDecomposition_lieSubmodule
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {X : Type*} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hwd : HasWeightDecomposition Δ X)
    (Z : LieSubmodule R 𝔤 X) :
    HasWeightDecomposition Δ ↥Z := by

  sorry

theorem IsCategoryO_lieSubmodule_commRing
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
  weight_decomp := HasWeightDecomposition_lieSubmodule hXO.weight_decomp Z
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

theorem jordanHolder_length_independent
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (cs₁ cs₂ : LieModule.CompositionSeriesOf rd M) :
    cs₁.length = cs₂.length := by

  sorry

theorem compositionSeries_ses_concat
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type*} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (Z : LieSubmodule R 𝔤 X)
    (csZ : LieModule.CompositionSeriesOf rd ↥Z)
    (csQ : LieModule.CompositionSeriesOf rd (X ⧸ Z)) :
    ∃ (csX : LieModule.CompositionSeriesOf rd X),
      csX.length = csZ.length + csQ.length := by

  sorry

theorem compositionLengthO_additive_ses
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type*} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (Z : LieSubmodule R 𝔤 X)
    (hZO : IsCategoryO Δ rd ↥Z)
    (hQO : IsCategoryO Δ rd (X ⧸ Z)) :
    CategoryO.compositionLengthO X hXO =
      CategoryO.compositionLengthO ↥Z hZO + CategoryO.compositionLengthO (X ⧸ Z) hQO := by

  set csX := Classical.choice (categoryO_has_composition_series hXO)
  set csZ := Classical.choice (categoryO_has_composition_series hZO)
  set csQ := Classical.choice (categoryO_has_composition_series hQO)

  obtain ⟨csX', hcsX'_len⟩ := compositionSeries_ses_concat Z csZ csQ

  have h_len_eq := jordanHolder_length_independent csX csX'


  show csX.length = csZ.length + csQ.length
  linarith

theorem compositionLengthO_pos_of_ne_bot
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type*} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (Z : LieSubmodule R 𝔤 X)
    (hZO : IsCategoryO Δ rd ↥Z)
    (hZ_ne_bot : Z ≠ ⊥) :
    0 < CategoryO.compositionLengthO ↥Z hZO := by
  by_contra h
  simp only [not_lt, Nat.le_zero] at h
  have hall := CategoryO.subsingleton_of_compositionLengthO_zero ↥Z hZO h
  apply hZ_ne_bot
  rw [LieSubmodule.eq_bot_iff]
  intro m hm
  have h_zero := hall ⟨m, hm⟩
  simpa [Subtype.ext_iff, ZeroMemClass.coe_zero] using h_zero

theorem compositionLengthO_quotient_lt
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type*} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (Z : LieSubmodule R 𝔤 X)
    (hZ_ne_top : Z ≠ ⊤)
    (hZ_ne_bot : Z ≠ ⊥)
    (hQO : IsCategoryO Δ rd (X ⧸ Z)) :
    CategoryO.compositionLengthO (X ⧸ Z) hQO < CategoryO.compositionLengthO X hXO := by
  have hZO : IsCategoryO Δ rd ↥Z := IsCategoryO_lieSubmodule_commRing hXO Z
  have h_add := compositionLengthO_additive_ses hXO Z hZO hQO
  have h_pos := compositionLengthO_pos_of_ne_bot hXO Z hZO hZ_ne_bot
  omega

theorem CategoryO.quotient_in_O_smaller_length
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (Z : LieSubmodule R 𝔤 X)
    (hZ_ne_top : Z ≠ ⊤)
    (hZ_ne_bot : Z ≠ ⊥) :
    ∃ (Y : Type uCatO) (_ : AddCommGroup Y) (_ : Module R Y)
      (_ : LieRingModule 𝔤 Y) (_ : LieModule R 𝔤 Y)
      (hYO : IsCategoryO Δ rd Y)
      (q : X →ₗ⁅R, 𝔤⁆ Y),
      Function.Surjective q ∧
      (∀ x : X, q x = 0 ↔ x ∈ Z) ∧
      CategoryO.compositionLengthO Y hYO < CategoryO.compositionLengthO X hXO := by

  have hQO : IsCategoryO Δ rd (X ⧸ Z) := IsCategoryO_quotient hXO Z
  refine ⟨X ⧸ Z, inferInstance, inferInstance, inferInstance, inferInstance, hQO,
         LieSubmodule.Quotient.mk' Z,
         LieSubmodule.Quotient.surjective_mk' Z, ?_,
         compositionLengthO_quotient_lt hXO Z hZ_ne_top hZ_ne_bot hQO⟩
  intro x
  rw [LieSubmodule.Quotient.mk'_apply]
  exact LieSubmodule.Quotient.mk_eq_zero'

theorem bilinear_vanishing_on_hwv'
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {MmuDual : Type uCatO} [AddCommGroup MmuDual] [Module R MmuDual]
    [LieRingModule 𝔤 MmuDual] [LieModule R 𝔤 MmuDual]
    {Mmu_inner : Type uCatO} [AddCommGroup Mmu_inner] [Module R Mmu_inner]
    [LieRingModule 𝔤 Mmu_inner] [LieModule R 𝔤 Mmu_inner]
    (mu : Δ.𝔥 →ₗ[R] R)
    (hVerma : IsVermaModule Δ Mmu_inner mu)
    (β : MmuDual →ₗ[R] Mmu_inner →ₗ[R] R)
    (hβ_contra : ∀ (x : 𝔤) (m : MmuDual) (m' : Mmu_inner), (β ⁅x, m⁆) m' + (β m) ⁅x, m'⁆ = 0)
    (lam : Δ.𝔥 →ₗ[R] R) (hmu : lam ≠ mu)
    (w : MmuDual)
    (hw_cartan : ∀ (h : Δ.𝔥), ⁅(↑h : 𝔤), w⁆ = lam h • w)
    (hw_npos : ∀ (e : Δ.𝔫_pos), ⁅(↑e : 𝔤), w⁆ = 0)
    (w' : MmuDual)
    (hw' : w' ∈ LieSubmodule.lieSpan R 𝔤 {w}) :
    (β w') hVerma.highestWeightVec = 0 := by

  sorry

theorem contragredient_verma_no_hwv_of_ne'
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (mu : Δ.𝔥 →ₗ[R] R)
    (MmuDual : Type uCatO) [AddCommGroup MmuDual] [Module R MmuDual]
    [LieRingModule 𝔤 MmuDual] [LieModule R 𝔤 MmuDual]
    (hMmuDualO : IsCategoryO Δ rd MmuDual)
    (hContra : IsContragredientVerma rd MmuDual mu hMmuDualO)
    (lam : Δ.𝔥 →ₗ[R] R) (hmu : lam ≠ mu)
    (w : MmuDual)
    (hw_cartan : ∀ (h : Δ.𝔥), ⁅(↑h : 𝔤), w⁆ = lam h • w)
    (hw_npos : ∀ (e : Δ.𝔫_pos), ⁅(↑e : 𝔤), w⁆ = 0) :
    w = 0 := by

  obtain ⟨Mmu_inner, _inst_acg, _inst_mod, _inst_lrm, _inst_lm,
         ⟨hVerma_ne⟩, _hMmuO_inner, β, hβ_contra, hβ_left_nd, _hβ_right_nd⟩ := hContra

  apply hβ_left_nd
  intro m'

  set N_w := LieSubmodule.lieSpan R 𝔤 ({w} : Set MmuDual) with hN_w_def

  have hw_mem : w ∈ N_w := LieSubmodule.subset_lieSpan (Set.mem_singleton w)

  suffices h_strong : ∀ w' ∈ N_w, (β w') m' = 0 from h_strong w hw_mem

  have hm'_mem : m' ∈ LieSubmodule.lieSpan R 𝔤 ({hVerma_ne.highestWeightVec} : Set Mmu_inner) := by
    rw [hVerma_ne.generates]; trivial

  revert m'
  intro m' hm'_mem
  refine LieSubmodule.lieSpan_induction R 𝔤
    (p := fun m'' _ => ∀ w' ∈ N_w, (β w') m'' = 0) ?mem ?zero ?add ?smul ?lie hm'_mem
  case mem =>
    intro m'' hm''
    rw [Set.mem_singleton_iff] at hm''
    subst hm''
    intro w' hw'
    exact bilinear_vanishing_on_hwv' mu hVerma_ne β hβ_contra lam hmu w hw_cartan hw_npos w' hw'
  case zero =>
    intro w' _
    exact map_zero (β w')
  case add =>
    intro x y _ _ hx hy w' hw'
    rw [map_add, hx w' hw', hy w' hw', add_zero]
  case smul =>
    intro a x _ hx w' hw'
    rw [map_smul, hx w' hw', smul_zero]
  case lie =>
    intro x y _ hy w' hw'
    have hc := hβ_contra x w' y
    have : (β w') ⁅x, y⁆ = -((β ⁅x, w'⁆) y) := eq_neg_of_add_eq_zero_right hc
    rw [this]
    have hxw'_mem : ⁅x, w'⁆ ∈ N_w := N_w.lie_mem hw'
    rw [hy ⁅x, w'⁆ hxw'_mem, neg_zero]

theorem hom_vanishing_verma_contragredientVerma_neq
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (Z : LieSubmodule R 𝔤 X)
    (lam_step : Δ.𝔥 →ₗ[R] R)
    (Q : Type uCatO) [AddCommGroup Q] [Module R Q]
    [LieRingModule 𝔤 Q] [LieModule R 𝔤 Q]
    (_ : IsVermaModule Δ Q lam_step)
    (π : ↥Z →ₗ⁅R, 𝔤⁆ Q)
    (_hπ_surj : Function.Surjective π)
    (_hπ_ker : ∀ x : ↥Z, π x = 0 ↔ (x : X) ∈ (⊥ : LieSubmodule R 𝔤 X))
    (mu : Δ.𝔥 →ₗ[R] R)
    (hmu_ne : mu ≠ lam_step)
    (MmuDual : Type uCatO) [AddCommGroup MmuDual] [Module R MmuDual]
    [LieRingModule 𝔤 MmuDual] [LieModule R 𝔤 MmuDual]
    (hMmuDualO : IsCategoryO Δ rd MmuDual)
    (_hContra : IsContragredientVerma rd MmuDual mu hMmuDualO)
    (f : ↥Z →ₗ⁅R, 𝔤⁆ MmuDual) : f = 0 := by


  have hVerma := ‹IsVermaModule Δ Q lam_step›

  obtain ⟨z₀, hz₀⟩ := _hπ_surj hVerma.highestWeightVec

  have π_inj : ∀ (a b : ↥Z), π a = π b → a = b := by
    intro a b hab
    have h1 : π (a - b) = 0 := by rw [map_sub, hab, sub_self]
    have h2 := (_hπ_ker (a - b)).mp h1
    rw [LieSubmodule.mem_bot] at h2
    exact sub_eq_zero.mp (Subtype.ext h2)

  have hfz₀ : f z₀ = 0 := by
    apply contragredient_verma_no_hwv_of_ne' mu MmuDual hMmuDualO _hContra lam_step (Ne.symm hmu_ne)
    ·
      intro h
      rw [← f.map_lie]
      have hlie : π ⁅(↑h : 𝔤), z₀⁆ = π (lam_step h • z₀) := by
        rw [π.map_lie, hz₀, hVerma.cartan_action, map_smul, hz₀]
      rw [π_inj _ _ hlie, map_smul]
    ·
      intro e
      rw [← f.map_lie]
      have hlie : π ⁅(↑e : 𝔤), z₀⁆ = 0 := by
        rw [π.map_lie, hz₀, hVerma.npos_action]
      have h_ker := (_hπ_ker ⁅(↑e : 𝔤), z₀⁆).mp hlie
      rw [LieSubmodule.mem_bot] at h_ker
      rw [show ⁅(↑e : 𝔤), z₀⁆ = (0 : ↥Z) from Subtype.ext h_ker, map_zero]


  have hgen : LieSubmodule.lieSpan R 𝔤 ({z₀} : Set ↥Z) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hπz_mem : π z ∈ LieSubmodule.lieSpan R 𝔤 ({hVerma.highestWeightVec} : Set Q) := by
      rw [hVerma.generates]; trivial
    suffices h : ∀ q ∈ LieSubmodule.lieSpan R 𝔤 ({hVerma.highestWeightVec} : Set Q),
      ∀ z : ↥Z, π z = q → z ∈ LieSubmodule.lieSpan R 𝔤 ({z₀} : Set ↥Z) by
      exact h (π z) hπz_mem z rfl
    intro q hq
    refine LieSubmodule.lieSpan_induction R 𝔤
      (p := fun q _ => ∀ z : ↥Z, π z = q → z ∈ LieSubmodule.lieSpan R 𝔤 ({z₀} : Set ↥Z))
      ?mem ?zero ?add ?smul ?lie hq
    case mem =>
      intro q' hq' z' hπz'
      rw [Set.mem_singleton_iff] at hq'
      subst hq'
      rw [show z' = z₀ from π_inj _ _ (by rw [hπz', hz₀])]
      exact LieSubmodule.subset_lieSpan (Set.mem_singleton z₀)
    case zero =>
      intro z' hπz'
      have := (_hπ_ker z').mp hπz'
      rw [LieSubmodule.mem_bot] at this
      rw [show z' = (0 : ↥Z) from Subtype.ext this]
      exact zero_mem _
    case add =>
      intro a b _ _ ha hb z' hπz'
      obtain ⟨za, hza⟩ := _hπ_surj a
      obtain ⟨zb, hzb⟩ := _hπ_surj b
      rw [show z' = za + zb from π_inj _ _ (by rw [map_add, hza, hzb, hπz'])]
      exact add_mem (ha za hza) (hb zb hzb)
    case smul =>
      intro r' a _ ha z' hπz'
      obtain ⟨za, hza⟩ := _hπ_surj a
      rw [show z' = r' • za from π_inj _ _ (by rw [map_smul, hza, hπz'])]
      exact SMulMemClass.smul_mem r' (ha za hza)
    case lie =>
      intro x a _ ha z' hπz'
      obtain ⟨za, hza⟩ := _hπ_surj a
      rw [show z' = ⁅x, za⁆ from π_inj _ _ (by rw [π.map_lie, hza, hπz'])]
      exact LieSubmodule.lie_mem _ (ha za hza)

  ext z
  have hz_mem : z ∈ LieSubmodule.lieSpan R 𝔤 ({z₀} : Set ↥Z) := by
    rw [hgen]; trivial
  refine LieSubmodule.lieSpan_induction R 𝔤
    (p := fun z' _ => f z' = 0) ?mem ?zero ?add ?smul ?lie hz_mem
  case mem =>
    intro z' hz'
    rw [Set.mem_singleton_iff] at hz'
    subst hz'; exact hfz₀
  case zero => simp [map_zero]
  case add =>
    intro a b _ _ ha hb
    rw [map_add, ha, hb, add_zero]
  case smul =>
    intro r' a _ ha
    rw [map_smul, ha, smul_zero]
  case lie =>
    intro x a _ ha
    rw [f.map_lie, ha, lie_zero]

theorem ses_weight_space_surjective
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    {A : Type*} [AddCommGroup A] [Module R A]
    [LieRingModule 𝔤 A] [LieModule R 𝔤 A]
    (hA : HasWeightDecomposition Δ A)
    {B : Type*} [AddCommGroup B] [Module R B]
    [LieRingModule 𝔤 B] [LieModule R 𝔤 B]
    (j : A →ₗ⁅R, 𝔤⁆ B) (hj : Function.Injective j)
    {C : Type*} [AddCommGroup C] [Module R C]
    [LieRingModule 𝔤 C] [LieModule R 𝔤 C]
    (q : B →ₗ⁅R, 𝔤⁆ C) (hq : Function.Surjective q)
    (hexact : ∀ b, q b = 0 ↔ ∃ a, j a = b)
    (μ : Δ.𝔥 →ₗ[R] R) (c : C)
    (hc : c ∈ WeightSpace Δ C μ) :
    ∃ b' : B, b' ∈ WeightSpace Δ B μ ∧ q b' = c := by

  sorry

theorem HasWeightDecomposition_of_ses
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {A : Type*} [AddCommGroup A] [Module R A]
    [LieRingModule 𝔤 A] [LieModule R 𝔤 A]
    (hA : HasWeightDecomposition Δ A)
    {C : Type*} [AddCommGroup C] [Module R C]
    [LieRingModule 𝔤 C] [LieModule R 𝔤 C]
    (hC : HasWeightDecomposition Δ C)
    {B : Type*} [AddCommGroup B] [Module R B]
    [LieRingModule 𝔤 B] [LieModule R 𝔤 B]
    (j : A →ₗ⁅R, 𝔤⁆ B) (hj : Function.Injective j)
    (q : B →ₗ⁅R, 𝔤⁆ C) (hq : Function.Surjective q)
    (hexact : ∀ b, q b = 0 ↔ ∃ a, j a = b) :
    HasWeightDecomposition Δ B := by
  classical

  have hj_weight : ∀ (ν : Δ.𝔥 →ₗ[R] R) (a' : WeightSpace Δ A ν),
      (j (a' : A) : B) ∈ WeightSpace Δ B ν := by
    intro ν a' h
    show ⁅(h : 𝔤), j (a' : A)⁆ = ν h • j (a' : A)
    rw [← LieModuleHom.map_lie, a'.prop h, map_smul]
  intro b

  obtain ⟨SC, vC, hqb_eq⟩ := hC (q b)


  have hlift : ∀ μ, ∃ b' : B, b' ∈ WeightSpace Δ B μ ∧ q b' = (vC μ : C) :=
    fun μ => ses_weight_space_surjective Δ hA j hj q hq hexact μ (vC μ) (vC μ).prop
  let liftC : (μ : Δ.𝔥 →ₗ[R] R) → B := fun μ => (hlift μ).choose
  have hliftC_wt : ∀ μ, liftC μ ∈ WeightSpace Δ B μ :=
    fun μ => (hlift μ).choose_spec.1
  have hliftC_q : ∀ μ, q (liftC μ) = (vC μ : C) :=
    fun μ => (hlift μ).choose_spec.2

  have hker : q (b - ∑ μ ∈ SC, liftC μ) = 0 := by
    rw [map_sub, map_sum]
    simp only [hliftC_q, hqb_eq, sub_self]
  obtain ⟨a, ha⟩ := (hexact _).mp hker

  obtain ⟨SA, vA, ha_eq⟩ := hA a


  refine ⟨SA ∪ SC, fun ν =>
    ⟨(if ν ∈ SA then j (vA ν : A) else 0) + (if ν ∈ SC then liftC ν else 0),
     (WeightSpace Δ B ν).add_mem
       (by split_ifs with h; exact hj_weight ν (vA ν); exact (WeightSpace Δ B ν).zero_mem)
       (by split_ifs with h; exact hliftC_wt ν; exact (WeightSpace Δ B ν).zero_mem)⟩, ?_⟩


  have hb_eq : b = j a + ∑ μ ∈ SC, liftC μ := by
    rw [← sub_eq_iff_eq_add]; exact ha.symm

  have hja_eq : j a = ∑ ν ∈ SA, j (vA ν : A) := by
    rw [ha_eq, map_sum]
  rw [hb_eq, hja_eq]

  simp only []

  rw [Finset.sum_add_distrib]
  congr 1
  ·
    rw [Finset.sum_ite_mem, Finset.union_inter_cancel_left]
  ·
    rw [Finset.sum_ite_mem, Finset.union_inter_cancel_right]

theorem IsCategoryO_of_extension
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {A : Type*} [AddCommGroup A] [Module R A]
    [LieRingModule 𝔤 A] [LieModule R 𝔤 A]
    (hA : IsCategoryO Δ rd A)
    {C : Type*} [AddCommGroup C] [Module R C]
    [LieRingModule 𝔤 C] [LieModule R 𝔤 C]
    (hC : IsCategoryO Δ rd C)
    {B : Type*} [AddCommGroup B] [Module R B]
    [LieRingModule 𝔤 B] [LieModule R 𝔤 B]
    (j : A →ₗ⁅R, 𝔤⁆ B) (hj : Function.Injective j)
    (q : B →ₗ⁅R, 𝔤⁆ C) (hq : Function.Surjective q)
    (hexact : ∀ b, q b = 0 ↔ ∃ a, j a = b) :
    IsCategoryO Δ rd B where
  finitely_generated := by
    classical
    obtain ⟨SA, hSA⟩ := hA.finitely_generated
    obtain ⟨SC, hSC⟩ := hC.finitely_generated
    choose liftB hliftB using (fun c : C => hq c)
    let SB := SA.image j ∪ SC.image liftB
    refine ⟨SB, ?_⟩
    rw [eq_top_iff]
    intro b _

    have hmap_surj : LieSubmodule.lieSpan R 𝔤 (SC : Set C) ≤
        LieSubmodule.map q (LieSubmodule.lieSpan R 𝔤 (↑SB : Set B)) := by
      rw [LieSubmodule.lieSpan_le]
      intro c hc
      refine ⟨liftB c, LieSubmodule.subset_lieSpan ?_, hliftB c⟩
      show liftB c ∈ (↑SB : Set B)
      simp only [SB, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image]
      exact Or.inr ⟨c, hc, rfl⟩

    have hqb : q b ∈ LieSubmodule.map q (LieSubmodule.lieSpan R 𝔤 (↑SB : Set B)) := by
      apply hmap_surj; rw [hSC]; trivial
    obtain ⟨b', hb'_span, hb'_eq⟩ := hqb

    have hq_diff : q (b - b') = 0 := by
      rw [map_sub]; exact sub_eq_zero.mpr hb'_eq.symm
    obtain ⟨a, ha⟩ := (hexact (b - b')).mp hq_diff

    have hja_span : j a ∈ LieSubmodule.lieSpan R 𝔤 (↑SB : Set B) := by
      have ha_top : a ∈ LieSubmodule.lieSpan R 𝔤 (SA : Set A) := by
        rw [hSA]; trivial


      have hj_gen : (j '' (SA : Set A)) ⊆ (↑SB : Set B) := by
        intro x hx
        obtain ⟨a', ha', rfl⟩ := hx
        simp only [SB, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image]
        exact Or.inl ⟨a', ha', rfl⟩
      have : LieSubmodule.map j (LieSubmodule.lieSpan R 𝔤 (SA : Set A)) ≤
          LieSubmodule.lieSpan R 𝔤 (↑SB : Set B) := by
        rw [LieSubmodule.map_le_iff_le_comap, LieSubmodule.lieSpan_le]
        intro s hs
        apply LieSubmodule.mem_comap.mpr
        exact LieSubmodule.subset_lieSpan (hj_gen ⟨s, hs, rfl⟩)
      exact this ⟨a, ha_top, rfl⟩

    have hb_eq : b = j a + b' := by
      rw [← sub_eq_iff_eq_add]; exact ha.symm
    rw [hb_eq]
    exact (LieSubmodule.lieSpan R 𝔤 (↑SB : Set B)).add_mem hja_span hb'_span
  weight_decomp :=
    HasWeightDecomposition_of_ses hA.weight_decomp hC.weight_decomp j hj q hq hexact
  weight_bound := by
    classical
    obtain ⟨bdsA, hbdsA⟩ := hA.weight_bound
    obtain ⟨bdsC, hbdsC⟩ := hC.weight_bound
    refine ⟨bdsA ∪ bdsC, fun μ hμ => ?_⟩
    rw [weights, Set.mem_setOf_eq] at hμ
    by_cases hC_wt : WeightSpace Δ C μ = ⊥
    ·
      have hA_wt : μ ∈ weights Δ A := by
        rw [weights, Set.mem_setOf_eq]
        intro hbot
        apply hμ; clear hμ
        rw [eq_bot_iff]
        intro b hb

        have hqb_wt : q b ∈ WeightSpace Δ C μ := by
          intro h
          rw [← LieModuleHom.map_lie]
          rw [hb h]
          exact map_smul q.toLinearMap (μ h) b
        rw [hC_wt] at hqb_wt
        simp only [Submodule.mem_bot] at hqb_wt
        obtain ⟨a, ha⟩ := (hexact b).mp hqb_wt

        have ha_wt : a ∈ WeightSpace Δ A μ := by
          intro h


          apply hj
          rw [map_smul, LieModuleHom.map_lie, ha, hb h]
        rw [hbot] at ha_wt
        simp only [Submodule.mem_bot] at ha_wt
        rw [← ha, ha_wt, map_zero]
        exact Submodule.zero_mem ⊥
      obtain ⟨wt, hwt_mem, hwt_bound⟩ := hbdsA μ hA_wt
      exact ⟨wt, Finset.mem_union_left _ hwt_mem, hwt_bound⟩
    ·
      have hC_wt' : μ ∈ weights Δ C := by
        rw [weights, Set.mem_setOf_eq]; exact hC_wt
      obtain ⟨wt, hwt_mem, hwt_bound⟩ := hbdsC μ hC_wt'
      exact ⟨wt, Finset.mem_union_right _ hwt_mem, hwt_bound⟩

theorem ext1_vanishing_of_hom_vanishing_and_ext_vanishing_for_X
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (_hXO : IsCategoryO Δ rd X)
    {Y : Type uCatO} [AddCommGroup Y] [Module R Y]
    [LieRingModule 𝔤 Y] [LieModule R 𝔤 Y]
    (_hYO : IsCategoryO Δ rd Y)
    (q : X →ₗ⁅R, 𝔤⁆ Y)
    (_hq_surj : Function.Surjective q)
    (Z : LieSubmodule R 𝔤 X)
    (_hq_ker : ∀ x : X, q x = 0 ↔ x ∈ Z)

    {N : Type uCatO} [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (hNO : IsCategoryO Δ rd N)
    (hhom_vanish : ∀ (f : ↥Z →ₗ⁅R, 𝔤⁆ N), f = 0)

    (hExt_X : ∀ (E' : Type uCatO) [AddCommGroup E'] [Module R E']
      [LieRingModule 𝔤 E'] [LieModule R 𝔤 E']
      (_hE'O : IsCategoryO Δ rd E')
      (i' : N →ₗ⁅R, 𝔤⁆ E') (_hi' : Function.Injective i')
      (p' : E' →ₗ⁅R, 𝔤⁆ X) (_hp' : Function.Surjective p')
      (_hexact' : ∀ e : E', p' e = 0 ↔ ∃ m : N, i' m = e),
      ∃ (s : X →ₗ⁅R, 𝔤⁆ E'), ∀ x, p' (s x) = x)

    (E : Type uCatO) [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    (_hEO : IsCategoryO Δ rd E)
    (i : N →ₗ⁅R, 𝔤⁆ E) (_hi : Function.Injective i)
    (p : E →ₗ⁅R, 𝔤⁆ Y) (_hp : Function.Surjective p)
    (hexact : ∀ e : E, p e = 0 ↔ ∃ m : N, i m = e) :
    ∃ (s : Y →ₗ⁅R, 𝔤⁆ E), ∀ x, p (s x) = x := by


  letI prodLRM : LieRingModule 𝔤 (E × X) :=
    { bracket := fun x ex => (⁅x, ex.1⁆, ⁅x, ex.2⁆)
      add_lie := fun x y ex => by ext <;> exact add_lie x y _
      lie_add := fun x ex1 ex2 => by ext <;> exact lie_add x _ _
      leibniz_lie := fun x y ex => by
        ext
        · exact leibniz_lie x y ex.1
        · exact leibniz_lie x y ex.2 }
  letI prodLM : LieModule R 𝔤 (E × X) :=
    { smul_lie := fun r x ex => by
        ext
        · exact smul_lie r x ex.1
        · exact smul_lie r x ex.2
      lie_smul := fun r x ex => by
        ext
        · exact lie_smul r x ex.1
        · exact lie_smul r x ex.2 }

  let PB : LieSubmodule R 𝔤 (E × X) :=
    { carrier := {ex | p ex.1 = q ex.2}
      add_mem' := by
        intro a b ha hb
        show p (a.1 + b.1) = q (a.2 + b.2)
        rw [map_add, map_add, ha, hb]
      zero_mem' := by show p 0 = q 0; rw [map_zero, map_zero]
      smul_mem' := by
        intro r a ha
        show p (r • a.1) = q (r • a.2)
        rw [map_smul, map_smul, ha]
      lie_mem := by
        intro x a (ha : p a.1 = q a.2)
        show p ⁅x, a.1⁆ = q ⁅x, a.2⁆
        rw [LieModuleHom.map_lie, LieModuleHom.map_lie, ha] }

  let π₂ : ↥PB →ₗ⁅R, 𝔤⁆ X :=
    { toFun := fun ex => ex.1.2
      map_add' := fun a b => rfl
      map_smul' := fun r a => rfl
      map_lie' := fun {x m} => rfl }

  have hπ₂_surj : Function.Surjective π₂ := by
    intro x
    obtain ⟨e, he⟩ := _hp (q x)
    exact ⟨⟨(e, x), he⟩, rfl⟩

  have h_pi_zero : ∀ n : N, p (i n) = q (0 : X) := by
    intro n
    rw [map_zero]
    exact (hexact (i n)).mpr ⟨n, rfl⟩
  let ι : N →ₗ⁅R, 𝔤⁆ ↥PB :=
    { toFun := fun n => ⟨(i n, 0), h_pi_zero n⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        show (i (a + b), (0 : X)) = (i a + i b, 0 + 0)
        simp [map_add]
      map_smul' := by
        intro r a
        apply Subtype.ext
        show (i (r • a), (0 : X)) = (r • i a, r • 0)
        simp [map_smul]
      map_lie' := fun {g n} => by
        apply Subtype.ext
        show (i ⁅g, n⁆, (0 : X)) = (⁅g, i n⁆, ⁅g, (0 : X)⁆)
        simp [LieModuleHom.map_lie, lie_zero] }

  have hι_inj : Function.Injective ι := by
    intro a b hab
    have h := Subtype.ext_iff.mp hab
    have h1 : (i a, (0 : X)).1 = (i b, (0 : X)).1 := congr_arg Prod.fst h
    exact _hi h1

  have h_exact_PB : ∀ ex : ↥PB, π₂ ex = 0 ↔ ∃ m : N, ι m = ex := by
    intro ⟨⟨e, x⟩, hex⟩
    constructor
    · intro hx

      have hx' : x = 0 := hx

      have hpe : p e = 0 := by
        have : p e = q x := hex
        rw [hx', map_zero] at this
        exact this

      obtain ⟨m, hm⟩ := (hexact e).mp hpe
      refine ⟨m, Subtype.ext ?_⟩
      exact Prod.ext hm hx'.symm
    · intro ⟨m, hm⟩

      have h := Subtype.ext_iff.mp hm
      exact (congr_arg Prod.snd h : (0 : X) = x).symm


  have hPBO : IsCategoryO Δ rd ↥PB :=
    IsCategoryO_of_extension hNO _hXO ι hι_inj π₂ hπ₂_surj h_exact_PB


  obtain ⟨s', hs'⟩ := hExt_X ↥PB hPBO ι hι_inj π₂ hπ₂_surj h_exact_PB


  let π₁ : ↥PB →ₗ⁅R, 𝔤⁆ E :=
    { toFun := fun ex => ex.1.1
      map_add' := fun a b => rfl
      map_smul' := fun r a => rfl
      map_lie' := fun {x m} => rfl }
  let t : X →ₗ⁅R, 𝔤⁆ E := π₁.comp s'

  have ht : ∀ x, p (t x) = q x := by
    intro x
    have hmem : p (s' x).1.1 = q (s' x).1.2 := (s' x).2
    show p (s' x).1.1 = q x
    rw [hmem, show (s' x).1.2 = π₂ (s' x) from rfl, hs']


  have ht_on_Z : ∀ z : ↥Z, ∃ n : N, i n = t (z : X) := by
    intro z
    have hz : q (z : X) = 0 := (_hq_ker (z : X)).mpr z.2
    have : p (t (z : X)) = 0 := by rw [ht]; exact hz
    exact (hexact (t (z : X))).mp this

  let f_Z : ↥Z → N := fun z => (ht_on_Z z).choose
  have hf_Z : ∀ z : ↥Z, i (f_Z z) = t (z : X) := fun z => (ht_on_Z z).choose_spec

  let f_Z_hom : ↥Z →ₗ⁅R, 𝔤⁆ N :=
    { toFun := f_Z
      map_add' := by
        intro a b
        apply _hi
        rw [map_add, hf_Z, hf_Z, hf_Z]
        exact (map_add t (a : X) (b : X)).symm ▸ rfl
      map_smul' := by
        intro r a
        apply _hi
        rw [map_smul, hf_Z, hf_Z]
        exact (map_smul t r (a : X)).symm ▸ rfl
      map_lie' := fun {g w} => by
        apply _hi
        rw [LieModuleHom.map_lie, hf_Z, hf_Z]
        exact (LieModuleHom.map_lie t g (w : X)).symm ▸ rfl }

  have hf_Z_zero : f_Z_hom = 0 := hhom_vanish f_Z_hom

  have ht_zero_on_Z : ∀ z : ↥Z, t (z : X) = 0 := by
    intro z
    have hfz : f_Z z = 0 := by
      have := congr_arg (·.toFun z) hf_Z_zero
      exact this
    rw [← hf_Z z, hfz, map_zero]

  have ht_factors : ∀ x₁ x₂ : X, q x₁ = q x₂ → t x₁ = t x₂ := by
    intro x₁ x₂ hq
    have hq_diff : q (x₁ - x₂) = 0 := by rw [map_sub]; exact sub_eq_zero.mpr hq
    have h_mem : x₁ - x₂ ∈ Z := (_hq_ker (x₁ - x₂)).mp hq_diff
    have ht_diff : t (x₁ - x₂) = 0 := ht_zero_on_Z ⟨x₁ - x₂, h_mem⟩
    have : t x₁ - t x₂ = 0 := by rw [← map_sub]; exact ht_diff
    exact sub_eq_zero.mp this

  let s_fun : Y → E := fun y => t ((_hq_surj y).choose)
  have hs_fun : ∀ y, p (s_fun y) = y := by
    intro y
    calc p (s_fun y) = q ((_hq_surj y).choose) := ht _
      _ = y := (_hq_surj y).choose_spec

  have hs_add : ∀ a b : Y, s_fun (a + b) = s_fun a + s_fun b := by
    intro a b
    have h1 : t ((_hq_surj (a + b)).choose) = t ((_hq_surj a).choose + (_hq_surj b).choose) := by
      apply ht_factors
      rw [(_hq_surj (a + b)).choose_spec, map_add,
          (_hq_surj a).choose_spec, (_hq_surj b).choose_spec]
    rw [show s_fun (a + b) = t ((_hq_surj (a + b)).choose) from rfl, h1, map_add]
  have hs_smul : ∀ (r : R) (a : Y), s_fun (r • a) = r • s_fun a := by
    intro r a
    have h1 : t ((_hq_surj (r • a)).choose) = t (r • (_hq_surj a).choose) := by
      apply ht_factors
      rw [(_hq_surj (r • a)).choose_spec, map_smul, (_hq_surj a).choose_spec]
    rw [show s_fun (r • a) = t ((_hq_surj (r • a)).choose) from rfl, h1, map_smul]
  have hs_lie : ∀ (x : 𝔤) (m : Y), s_fun ⁅x, m⁆ = ⁅x, s_fun m⁆ := by
    intro x m
    have h1 : t ((_hq_surj ⁅x, m⁆).choose) = t ⁅x, (_hq_surj m).choose⁆ := by
      apply ht_factors
      rw [(_hq_surj ⁅x, m⁆).choose_spec, LieModuleHom.map_lie, (_hq_surj m).choose_spec]
    rw [show s_fun ⁅x, m⁆ = t ((_hq_surj ⁅x, m⁆).choose) from rfl, h1,
        LieModuleHom.map_lie]
  let s : Y →ₗ⁅R, 𝔤⁆ E :=
    { toFun := s_fun
      map_add' := hs_add
      map_smul' := hs_smul
      map_lie' := fun {x m} => hs_lie x m }
  exact ⟨s, hs_fun⟩

theorem ext_vanishing_transfer_neq
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hExt : Ext1VanishingForContragredientVerma rd X hXO)
    {Y : Type uCatO} [AddCommGroup Y] [Module R Y]
    [LieRingModule 𝔤 Y] [LieModule R 𝔤 Y]
    (hYO : IsCategoryO Δ rd Y)
    (q : X →ₗ⁅R, 𝔤⁆ Y)
    (hq_surj : Function.Surjective q)
    (Z : LieSubmodule R 𝔤 X)
    (hq_ker : ∀ x : X, q x = 0 ↔ x ∈ Z)
    (lam_step : Δ.𝔥 →ₗ[R] R)
    (Q : Type uCatO) [AddCommGroup Q] [Module R Q]
    [LieRingModule 𝔤 Q] [LieModule R 𝔤 Q]
    (_ : IsVermaModule Δ Q lam_step)
    (π : ↥Z →ₗ⁅R, 𝔤⁆ Q)
    (hπ_surj : Function.Surjective π)
    (hπ_ker : ∀ x : ↥Z, π x = 0 ↔ (x : X) ∈ (⊥ : LieSubmodule R 𝔤 X))

    (mu : Δ.𝔥 →ₗ[R] R)
    (hmu_ne : mu ≠ lam_step)
    (MmuDual : Type uCatO) [AddCommGroup MmuDual] [Module R MmuDual]
    [LieRingModule 𝔤 MmuDual] [LieModule R 𝔤 MmuDual]
    (hMmuDualO : IsCategoryO Δ rd MmuDual)
    (_hContra : IsContragredientVerma rd MmuDual mu hMmuDualO)
    (E : Type uCatO) [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    (_hEO : IsCategoryO Δ rd E)
    (i : MmuDual →ₗ⁅R, 𝔤⁆ E) (_hi : Function.Injective i)
    (p : E →ₗ⁅R, 𝔤⁆ Y) (_hp : Function.Surjective p)
    (hexact : ∀ e : E, p e = 0 ↔ ∃ m : MmuDual, i m = e) :
    ∃ (s : Y →ₗ⁅R, 𝔤⁆ E), ∀ x, p (s x) = x := by

  have hhom_vanish : ∀ (f : ↥Z →ₗ⁅R, 𝔤⁆ MmuDual), f = 0 :=
    fun f => hom_vanishing_verma_contragredientVerma_neq Z lam_step Q ‹_› π hπ_surj hπ_ker
      mu hmu_ne MmuDual hMmuDualO _hContra f

  have hExt_X := hExt mu MmuDual hMmuDualO _hContra

  exact ext1_vanishing_of_hom_vanishing_and_ext_vanishing_for_X
    hXO hYO q hq_surj Z hq_ker hMmuDualO hhom_vanish hExt_X E _hEO i _hi p _hp hexact

theorem contragredientVerma_injective_in_O
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (lam : Δ.𝔥 →ₗ[R] R)
    (MlamDual : Type uCatO) [AddCommGroup MlamDual] [Module R MlamDual]
    [LieRingModule 𝔤 MlamDual] [LieModule R 𝔤 MlamDual]
    (_hMlamDualO : IsCategoryO Δ rd MlamDual)
    (_hContra : IsContragredientVerma rd MlamDual lam _hMlamDualO)
    (E : Type uCatO) [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    (_hEO : IsCategoryO Δ rd E)
    (_i : MlamDual →ₗ⁅R, 𝔤⁆ E) (_hi : Function.Injective _i) :
    ∃ (r : E →ₗ⁅R, 𝔤⁆ MlamDual), ∀ m, r (_i m) = m := by

  sorry

theorem contragredientVerma_ses_splits
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (_hXO : IsCategoryO Δ rd X)
    (lam : Δ.𝔥 →ₗ[R] R)
    (MlamDual : Type uCatO) [AddCommGroup MlamDual] [Module R MlamDual]
    [LieRingModule 𝔤 MlamDual] [LieModule R 𝔤 MlamDual]
    (_hMlamDualO : IsCategoryO Δ rd MlamDual)
    (_hContra : IsContragredientVerma rd MlamDual lam _hMlamDualO)
    (E : Type uCatO) [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    (_hEO : IsCategoryO Δ rd E)
    (_i : MlamDual →ₗ⁅R, 𝔤⁆ E) (_hi : Function.Injective _i)
    (p : E →ₗ⁅R, 𝔤⁆ X) (_hp : Function.Surjective p)
    (hexact : ∀ e : E, p e = 0 ↔ ∃ m : MlamDual, _i m = e) :
    ∃ (s : X →ₗ⁅R, 𝔤⁆ E), ∀ x, p (s x) = x := by

  obtain ⟨r, hr⟩ := contragredientVerma_injective_in_O
    lam MlamDual _hMlamDualO _hContra E _hEO _i _hi

  have hpi : ∀ m : MlamDual, p (_i m) = 0 :=
    fun m => (hexact (_i m)).mpr ⟨m, rfl⟩

  have hwd : ∀ e₁ e₂ : E, p e₁ = p e₂ → e₁ - _i (r e₁) = e₂ - _i (r e₂) := by
    intro e₁ e₂ heq
    have hdiff : p (e₁ - e₂) = 0 := by rw [map_sub, heq, sub_self]
    obtain ⟨m, hm⟩ := (hexact _).mp hdiff
    have h1 : _i (r (e₁ - e₂)) = e₁ - e₂ := by rw [← hm, hr, hm]
    have h2 : _i (r e₁) - _i (r e₂) = _i (r (e₁ - e₂)) := by simp only [map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mp (by rw [h2, h1])

  let pick : X → E := fun x => Classical.choose (_hp x)
  have hpick : ∀ x, p (pick x) = x := fun x => Classical.choose_spec (_hp x)
  let s_fun : X → E := fun x => pick x - _i (r (pick x))

  have hs_sec : ∀ x, p (s_fun x) = x := by
    intro x; simp only [s_fun, map_sub, hpi, sub_zero, hpick]

  have hs_add : ∀ x₁ x₂ : X, s_fun (x₁ + x₂) = s_fun x₁ + s_fun x₂ := by
    intro x₁ x₂
    have hpsum : p (pick x₁ + pick x₂) = x₁ + x₂ := by simp [map_add, hpick]
    have key : s_fun (x₁ + x₂) = (pick x₁ + pick x₂) - _i (r (pick x₁ + pick x₂)) :=
      hwd _ _ (by simp [hpick, hpsum])
    rw [key]; simp only [s_fun, map_add]; abel

  have hs_smul : ∀ (c : R) (x : X), s_fun (c • x) = c • s_fun x := by
    intro c x
    have hps : p (c • pick x) = c • x := by simp [map_smul, hpick]
    have key : s_fun (c • x) = (c • pick x) - _i (r (c • pick x)) :=
      hwd _ _ (by simp [hpick, hps])
    rw [key]; simp only [s_fun, map_smul, smul_sub]

  have hs_lie : ∀ (g : 𝔤) (x : X), s_fun (⁅g, x⁆) = ⁅g, s_fun x⁆ := by
    intro g x
    have hpl : p (⁅g, pick x⁆) = ⁅g, x⁆ := by rw [LieModuleHom.map_lie, hpick]
    have key : s_fun (⁅g, x⁆) = ⁅g, pick x⁆ - _i (r ⁅g, pick x⁆) :=
      hwd _ _ (by simp [hpick, hpl])
    rw [key]; simp only [s_fun, LieModuleHom.map_lie, lie_sub]

  exact ⟨{ toFun := s_fun, map_add' := hs_add, map_smul' := hs_smul,
            map_lie' := fun {g} {x} => hs_lie g x }, hs_sec⟩

theorem frobenius_reciprocity_coinduction_splitting
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (_hXO : IsCategoryO Δ rd X)
    (lam : Δ.𝔥 →ₗ[R] R)
    (MlamDual : Type uCatO) [AddCommGroup MlamDual] [Module R MlamDual]
    [LieRingModule 𝔤 MlamDual] [LieModule R 𝔤 MlamDual]
    (_hMlamDualO : IsCategoryO Δ rd MlamDual)
    (_hContra : IsContragredientVerma rd MlamDual lam _hMlamDualO)
    (E : Type uCatO) [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    (_hEO : IsCategoryO Δ rd E)
    (_i : MlamDual →ₗ⁅R, 𝔤⁆ E) (_hi : Function.Injective _i)
    (p : E →ₗ⁅R, 𝔤⁆ X) (_hp : Function.Surjective p)
    (hexact : ∀ e : E, p e = 0 ↔ ∃ m : MlamDual, _i m = e) :
    ∃ (s : X →ₗ⁅R, 𝔤⁆ E), ∀ x, p (s x) = x :=

  contragredientVerma_ses_splits
    _hXO lam MlamDual _hMlamDualO _hContra E _hEO _i _hi p _hp hexact

theorem frobenius_reciprocity_ext_vanishing_eq_case
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {Y : Type uCatO} [AddCommGroup Y] [Module R Y]
    [LieRingModule 𝔤 Y] [LieModule R 𝔤 Y]
    (_hYO : IsCategoryO Δ rd Y)
    (lam : Δ.𝔥 →ₗ[R] R)
    (MlamDual : Type uCatO) [AddCommGroup MlamDual] [Module R MlamDual]
    [LieRingModule 𝔤 MlamDual] [LieModule R 𝔤 MlamDual]
    (hMlamDualO : IsCategoryO Δ rd MlamDual)
    (_hContra : IsContragredientVerma rd MlamDual lam hMlamDualO)
    (E : Type uCatO) [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    (_hEO : IsCategoryO Δ rd E)
    (_i : MlamDual →ₗ⁅R, 𝔤⁆ E) (_hi : Function.Injective _i)
    (p : E →ₗ⁅R, 𝔤⁆ Y) (_hp : Function.Surjective p)
    (hexact : ∀ e : E, p e = 0 ↔ ∃ m : MlamDual, _i m = e) :
    ∃ (s : Y →ₗ⁅R, 𝔤⁆ E), ∀ x, p (s x) = x := by

  exact frobenius_reciprocity_coinduction_splitting _hYO lam MlamDual hMlamDualO
    _hContra E _hEO _i _hi p _hp hexact

theorem ext_vanishing_transfer_eq
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    {Y : Type uCatO} [AddCommGroup Y] [Module R Y]
    [LieRingModule 𝔤 Y] [LieModule R 𝔤 Y]
    (hYO : IsCategoryO Δ rd Y)
    (q : X →ₗ⁅R, 𝔤⁆ Y)
    (hq_surj : Function.Surjective q)
    (Z : LieSubmodule R 𝔤 X)
    (hq_ker : ∀ x : X, q x = 0 ↔ x ∈ Z)
    (lam_step : Δ.𝔥 →ₗ[R] R)
    (Q : Type uCatO) [AddCommGroup Q] [Module R Q]
    [LieRingModule 𝔤 Q] [LieModule R 𝔤 Q]
    (_ : IsVermaModule Δ Q lam_step)
    (π : ↥Z →ₗ⁅R, 𝔤⁆ Q)
    (hπ_surj : Function.Surjective π)
    (hπ_ker : ∀ x : ↥Z, π x = 0 ↔ (x : X) ∈ (⊥ : LieSubmodule R 𝔤 X))

    (MlamDual : Type uCatO) [AddCommGroup MlamDual] [Module R MlamDual]
    [LieRingModule 𝔤 MlamDual] [LieModule R 𝔤 MlamDual]
    (hMlamDualO : IsCategoryO Δ rd MlamDual)
    (_hContra : IsContragredientVerma rd MlamDual lam_step hMlamDualO)
    (E : Type uCatO) [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    (_hEO : IsCategoryO Δ rd E)
    (i : MlamDual →ₗ⁅R, 𝔤⁆ E) (_hi : Function.Injective i)
    (p : E →ₗ⁅R, 𝔤⁆ Y) (_hp : Function.Surjective p)
    (hexact : ∀ e : E, p e = 0 ↔ ∃ m : MlamDual, i m = e) :
    ∃ (s : Y →ₗ⁅R, 𝔤⁆ E), ∀ x, p (s x) = x := by


  exact frobenius_reciprocity_ext_vanishing_eq_case hYO lam_step
    MlamDual hMlamDualO _hContra E _hEO i _hi p _hp hexact

theorem CategoryO.ext_vanishing_transfer
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hExt : Ext1VanishingForContragredientVerma rd X hXO)
    {Y : Type uCatO} [AddCommGroup Y] [Module R Y]
    [LieRingModule 𝔤 Y] [LieModule R 𝔤 Y]
    (hYO : IsCategoryO Δ rd Y)
    (q : X →ₗ⁅R, 𝔤⁆ Y)
    (hq_surj : Function.Surjective q)
    (Z : LieSubmodule R 𝔤 X)
    (hq_ker : ∀ x : X, q x = 0 ↔ x ∈ Z)

    (lam_step : Δ.𝔥 →ₗ[R] R)
    (Q : Type uCatO) [AddCommGroup Q] [Module R Q]
    [LieRingModule 𝔤 Q] [LieModule R 𝔤 Q]
    (hQ : IsVermaModule Δ Q lam_step)
    (π : ↥Z →ₗ⁅R, 𝔤⁆ Q)
    (hπ_surj : Function.Surjective π)
    (hπ_ker : ∀ x : ↥Z, π x = 0 ↔ (x : X) ∈ (⊥ : LieSubmodule R 𝔤 X)) :
    Ext1VanishingForContragredientVerma rd Y hYO := by


  intro mu MmuDual inst1 inst2 inst3 inst4 hMmuDualO hContra
        E inst5 inst6 inst7 inst8 hEO i hi p hp hexact


  by_cases hmu : mu = lam_step
  ·

    exact ext_vanishing_transfer_eq (wg := wg) hXO hYO q hq_surj Z hq_ker
      lam_step Q hQ π hπ_surj hπ_ker MmuDual hMmuDualO (hmu ▸ hContra)
      E hEO i hi p hp hexact

  ·
    exact ext_vanishing_transfer_neq (wg := wg) hXO hExt hYO q hq_surj Z hq_ker
      lam_step Q hQ π hπ_surj hπ_ker mu hmu MmuDual hMmuDualO hContra
      E hEO i hi p hp hexact

theorem CategoryO.ext_vanishing_step
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hlen : CategoryO.compositionLengthO X hXO ≠ 0)
    (hExt : Ext1VanishingForContragredientVerma rd X hXO) :

    ∃ (Z : LieSubmodule R 𝔤 X)
      (lam_step : Δ.𝔥 →ₗ[R] R)
      (Q : Type uCatO) (_ : AddCommGroup Q) (_ : Module R Q)
      (_ : LieRingModule 𝔤 Q) (_ : LieModule R 𝔤 Q)
      (_ : IsVermaModule Δ Q lam_step)
      (π : ↥Z →ₗ⁅R, 𝔤⁆ Q),
      Function.Surjective π ∧
      (∀ x : ↥Z, π x = 0 ↔ (x : X) ∈ (⊥ : LieSubmodule R 𝔤 X)) ∧

      ∃ (Y : Type uCatO) (_ : AddCommGroup Y) (_ : Module R Y)
        (_ : LieRingModule 𝔤 Y) (_ : LieModule R 𝔤 Y)
        (hYO : IsCategoryO Δ rd Y)

        (q : X →ₗ⁅R, 𝔤⁆ Y),
        Function.Surjective q ∧
        (∀ x : X, q x = 0 ↔ x ∈ Z) ∧

        CategoryO.compositionLengthO Y hYO < CategoryO.compositionLengthO X hXO ∧

        Ext1VanishingForContragredientVerma rd Y hYO := by

  obtain ⟨Z, lam_step, Q, instQ1, instQ2, instQ3, instQ4, hVerma, π,
          hπ_surj, hπ_ker, hZ_ne_top⟩ :=
    CategoryO.maximal_weight_verma_submodule hXO hlen hExt


  have hZ_ne_bot : Z ≠ ⊥ := by
    intro hZ_bot


    letI := instQ1; letI := instQ2; letI := instQ3; letI := instQ4
    obtain ⟨z, hz⟩ := hπ_surj hVerma.highestWeightVec

    have hz_mem_bot : (z : X) ∈ (⊥ : LieSubmodule R 𝔤 X) := hZ_bot ▸ z.2

    have hπz : π z = 0 := (hπ_ker z).mpr hz_mem_bot

    exact hVerma.hwv_ne_zero (hz ▸ hπz)

  obtain ⟨Y, instY1, instY2, instY3, instY4, hYO, q, hq_surj, hq_ker, hY_lt⟩ :=
    CategoryO.quotient_in_O_smaller_length hXO Z hZ_ne_top hZ_ne_bot

  letI := instQ1; letI := instQ2; letI := instQ3; letI := instQ4
  letI := instY1; letI := instY2; letI := instY3; letI := instY4
  have hY_ext : Ext1VanishingForContragredientVerma rd Y hYO :=
    CategoryO.ext_vanishing_transfer (wg := wg) hXO hExt hYO q hq_surj Z hq_ker
      lam_step Q hVerma π hπ_surj hπ_ker

  exact ⟨Z, lam_step, Q, instQ1, instQ2, instQ3, instQ4, hVerma, π,
         hπ_surj, hπ_ker,
         Y, instY1, instY2, instY3, instY4, hYO, q,
         hq_surj, hq_ker, hY_lt, hY_ext⟩

theorem standard_filtration_gluing
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)

    (Z : LieSubmodule R 𝔤 X)
    (lam : Δ.𝔥 →ₗ[R] R)
    (Q : Type uCatO) [AddCommGroup Q] [Module R Q]
    [LieRingModule 𝔤 Q] [LieModule R 𝔤 Q]
    (_ : IsVermaModule Δ Q lam)
    (π : ↥Z →ₗ⁅R, 𝔤⁆ Q)
    (hπ_surj : Function.Surjective π)
    (hπ_ker : ∀ x : ↥Z, π x = 0 ↔ (x : X) ∈ (⊥ : LieSubmodule R 𝔤 X))

    {Y : Type uCatO} [AddCommGroup Y] [Module R Y]
    [LieRingModule 𝔤 Y] [LieModule R 𝔤 Y]
    (hYO : IsCategoryO Δ rd Y)
    (q : X →ₗ⁅R, 𝔤⁆ Y)
    (hq_surj : Function.Surjective q)
    (hq_ker : ∀ x : X, q x = 0 ↔ x ∈ Z)

    (hY_sf : HasStandardFiltration rd Y hYO) :
    HasStandardFiltration rd X hXO := by

  obtain ⟨n, G, hG_bot, hG_top, hG_strict, hG_verma⟩ := hY_sf

  have hcomap_bot : LieSubmodule.comap q ⊥ = Z := by
    ext x; simp only [LieSubmodule.mem_comap, LieSubmodule.mem_bot]; exact hq_ker x

  have hcomap_top : LieSubmodule.comap q ⊤ = ⊤ := by
    ext x; simp [LieSubmodule.mem_comap]

  have hcomap_G0 : LieSubmodule.comap q (G ⟨0, Nat.zero_lt_succ n⟩) = Z := by
    rw [hG_bot]; exact hcomap_bot

  have hcomap_Gn : LieSubmodule.comap q (G ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩) = ⊤ := by
    rw [hG_top]; exact hcomap_top

  have hcomap_strict : StrictMono (LieSubmodule.comap (f := q)) := by
    intro A B hAB
    refine lt_of_le_of_ne ((LieSubmodule.gc_map_comap q).monotone_u hAB.le) ?_
    intro heq
    have h_surj_map : ∀ N', LieSubmodule.map q (LieSubmodule.comap q N') = N' := by
      intro N'
      ext y; constructor
      · rintro ⟨x, hx, rfl⟩; exact LieSubmodule.mem_comap.mp hx
      · intro hy; obtain ⟨x, rfl⟩ := hq_surj y; exact ⟨x, LieSubmodule.mem_comap.mpr hy, rfl⟩
    have := congr_arg (LieSubmodule.map q) heq
    rw [h_surj_map, h_surj_map] at this
    exact (ne_of_lt hAB) this


  let F : Fin (n + 1 + 1) → LieSubmodule R 𝔤 X := fun ⟨k, hk⟩ =>
    if hk0 : k = 0 then ⊥
    else LieSubmodule.comap q (G ⟨k - 1, by omega⟩)

  have hF_bot : F ⟨0, Nat.zero_lt_succ (n + 1)⟩ = ⊥ := by
    simp only [F, dif_pos rfl]

  have hF_top : F ⟨n + 1, Nat.lt_succ_iff.mpr le_rfl⟩ = ⊤ := by
    simp only [F, dif_neg (Nat.succ_ne_zero n)]
    simp only [show n + 1 - 1 = n from rfl]
    exact hcomap_Gn

  have hF_strict : ∀ i : Fin (n + 1), F i.castSucc < F i.succ := by
    intro ⟨i, hi⟩

    simp only [Fin.castSucc_mk, Fin.succ_mk, F]

    simp only [dif_neg (Nat.succ_ne_zero i)]
    simp only [show i + 1 - 1 = i from rfl]
    by_cases hi0 : i = 0
    ·
      subst hi0
      show ⊥ < LieSubmodule.comap q (G ⟨0, _⟩)
      rw [bot_lt_iff_ne_bot, hcomap_G0]

      intro hZ_bot
      have hVerma := ‹IsVermaModule Δ Q lam›
      obtain ⟨z, hz⟩ := hπ_surj hVerma.highestWeightVec
      have : (z : X) ∈ (⊥ : LieSubmodule R 𝔤 X) := hZ_bot ▸ z.2
      have : π z = 0 := (hπ_ker z).mpr this
      exact hVerma.hwv_ne_zero (hz ▸ this)

    ·
      simp only [dif_neg hi0]
      apply hcomap_strict
      have hi' : i - 1 < n := by omega
      have := hG_strict ⟨i - 1, hi'⟩
      simp only [Fin.castSucc_mk, Fin.succ_mk] at this
      convert this using 1
      exact congr_arg G (Fin.ext (by simp; omega))


  have hF_verma : ∀ i : Fin (n + 1), ∃ (lam_i : Δ.𝔥 →ₗ[R] R)
      (Q_i : Type uCatO) (_ : AddCommGroup Q_i) (_ : Module R Q_i)
      (_ : LieRingModule 𝔤 Q_i) (_ : LieModule R 𝔤 Q_i)
      (_ : IsVermaModule Δ Q_i lam_i)
      (π_i : ↥(F i.succ) →ₗ⁅R, 𝔤⁆ Q_i),
      Function.Surjective π_i ∧
      (∀ x : ↥(F i.succ), π_i x = 0 ↔ (x : X) ∈ F i.castSucc) := by
    intro ⟨i, hi⟩
    by_cases hi0 : i = 0
    ·
      subst hi0
      have hF1_eq : F ⟨1, by omega⟩ = Z := by
        simp only [F, dif_neg one_ne_zero]
        simp only [show 1 - 1 = 0 from rfl]
        exact hcomap_G0

      have hF1_le_Z : F ⟨1, by omega⟩ ≤ Z := hF1_eq ▸ le_refl _
      have hZ_le_F1 : Z ≤ F ⟨1, by omega⟩ := hF1_eq ▸ le_refl _

      let π₀ : ↥(F ⟨1, by omega⟩) →ₗ⁅R, 𝔤⁆ Q :=
        { toFun := fun x => π ⟨x.1, hF1_le_Z x.2⟩
          map_add' := fun a b => by
            have : (⟨(a + b).1, hF1_le_Z (a + b).2⟩ : ↥Z) =
                ⟨a.1, hF1_le_Z a.2⟩ + ⟨b.1, hF1_le_Z b.2⟩ := Subtype.ext rfl
            simp only [this, map_add]
          map_smul' := fun r x => by
            have : (⟨(r • x).1, hF1_le_Z (r • x).2⟩ : ↥Z) =
                r • ⟨x.1, hF1_le_Z x.2⟩ := Subtype.ext rfl
            simp only [this, map_smul, RingHom.id_apply]
          map_lie' := fun {g x} => by
            have : (⟨(⁅g, x⁆ : ↥(F ⟨1, by omega⟩)).1, hF1_le_Z (⁅g, x⁆ : ↥(F ⟨1, by omega⟩)).2⟩ : ↥Z) =
                ⁅g, (⟨x.1, hF1_le_Z x.2⟩ : ↥Z)⁆ := Subtype.ext rfl
            simp only [this, LieModuleHom.map_lie] }
      refine ⟨lam, Q, inferInstance, inferInstance, inferInstance, inferInstance,
        ‹IsVermaModule Δ Q lam›, π₀, ?_, ?_⟩
      ·
        intro y
        obtain ⟨z, hz⟩ := hπ_surj y
        exact ⟨⟨z.1, hZ_le_F1 z.2⟩, hz⟩
      ·
        intro x
        show π ⟨x.1, hF1_le_Z x.2⟩ = 0 ↔ (x : X) ∈ F ⟨0, by omega⟩
        rw [hF_bot, hπ_ker]
    ·
      have hi1 : i - 1 < n := by omega
      obtain ⟨lam_j, Q_j, instQa, instQb, instQc, instQd, hVerma_j, π_j,
              hπj_surj, hπj_ker⟩ := hG_verma ⟨i - 1, hi1⟩
      letI := instQa; letI := instQb; letI := instQc; letI := instQd

      have hFsucc : F ⟨i + 1, by omega⟩ =
          LieSubmodule.comap q (G (⟨i - 1, hi1⟩ : Fin n).succ) := by
        simp only [F, dif_neg (Nat.succ_ne_zero i)]
        exact congr_arg (LieSubmodule.comap q) (congr_arg G (Fin.ext (by simp [Fin.succ_mk]; omega)))

      have hFcast : F ⟨i, by omega⟩ =
          LieSubmodule.comap q (G (⟨i - 1, hi1⟩ : Fin n).castSucc) := by
        simp only [F, dif_neg hi0, Fin.castSucc_mk]

      have hFsucc_le : F ⟨i + 1, by omega⟩ ≤
          LieSubmodule.comap q (G (⟨i - 1, hi1⟩ : Fin n).succ) := hFsucc ▸ le_refl _

      let πComp : ↥(F ⟨i + 1, by omega⟩) →ₗ⁅R, 𝔤⁆ Q_j :=
        { toFun := fun x =>
            π_j ⟨q x.1, LieSubmodule.mem_comap.mp (hFsucc_le x.2)⟩
          map_add' := fun a b => by
            have h1 : (⟨q (a + b).1, LieSubmodule.mem_comap.mp (hFsucc_le (a + b).2)⟩ :
                ↥(G (⟨i - 1, hi1⟩ : Fin n).succ)) =
                ⟨q a.1, LieSubmodule.mem_comap.mp (hFsucc_le a.2)⟩ +
                ⟨q b.1, LieSubmodule.mem_comap.mp (hFsucc_le b.2)⟩ :=
              Subtype.ext (map_add q a.1 b.1)
            simp only [h1, map_add]
          map_smul' := fun r x => by
            have h1 : (⟨q (r • x).1, LieSubmodule.mem_comap.mp (hFsucc_le (r • x).2)⟩ :
                ↥(G (⟨i - 1, hi1⟩ : Fin n).succ)) =
                r • ⟨q x.1, LieSubmodule.mem_comap.mp (hFsucc_le x.2)⟩ :=
              Subtype.ext (map_smul q r x.1)
            simp only [h1, map_smul, RingHom.id_apply]
          map_lie' := fun {g x} => by
            have h1 : (⟨q (⁅g, x⁆ : ↥(F ⟨i + 1, by omega⟩)).1,
                LieSubmodule.mem_comap.mp (hFsucc_le (⁅g, x⁆ : ↥(F ⟨i + 1, by omega⟩)).2)⟩ :
                ↥(G (⟨i - 1, hi1⟩ : Fin n).succ)) =
                ⁅g, (⟨q x.1, LieSubmodule.mem_comap.mp (hFsucc_le x.2)⟩ :
                  ↥(G (⟨i - 1, hi1⟩ : Fin n).succ))⁆ :=
              Subtype.ext (LieModuleHom.map_lie q g x.1)
            simp only [h1, LieModuleHom.map_lie] }
      refine ⟨lam_j, Q_j, instQa, instQb, instQc, instQd, hVerma_j, πComp, ?_, ?_⟩
      ·
        intro y
        obtain ⟨g, hg⟩ := hπj_surj y
        obtain ⟨x, hx⟩ := hq_surj (g : Y)
        have hx_mem : x ∈ F ⟨i + 1, by omega⟩ := by
          rw [hFsucc]; exact LieSubmodule.mem_comap.mpr (hx ▸ g.2)
        refine ⟨⟨x, hx_mem⟩, ?_⟩
        show π_j ⟨q x, LieSubmodule.mem_comap.mp (hFsucc_le hx_mem)⟩ = y
        have hqx_eq : (⟨q x, LieSubmodule.mem_comap.mp (hFsucc_le hx_mem)⟩ :
            ↥(G (⟨i - 1, hi1⟩ : Fin n).succ)) = g :=
          Subtype.ext hx
        rw [hqx_eq, hg]
      ·
        intro x
        show π_j ⟨q x.1, _⟩ = 0 ↔ (x : X) ∈ F ⟨i, by omega⟩
        rw [hπj_ker, hFcast]
        simp [LieSubmodule.mem_comap]

  exact ⟨n + 1, F, hF_bot, hF_top, hF_strict, hF_verma⟩

theorem standard_filtration_of_ext_vanishing
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hExt : Ext1VanishingForContragredientVerma rd X hXO) :
    HasStandardFiltration rd X hXO := by


  sorry


lemma UEA_induction_on_gen
    {R : Type*} [CommRing R]
    {L : Type*} [LieRing L] [LieAlgebra R L]
    {C : UniversalEnvelopingAlgebra R L → Prop}
    (u : UniversalEnvelopingAlgebra R L)
    (h_alg : ∀ r : R, C (algebraMap R _ r))
    (h_ι : ∀ x : L, C (UniversalEnvelopingAlgebra.ι R x))
    (h_mul : ∀ a b, C a → C b → C (a * b))
    (h_add : ∀ a b, C a → C b → C (a + b)) :
    C u := by
  obtain ⟨t, rfl⟩ := RingQuot.mkAlgHom_surjective R
    (UniversalEnvelopingAlgebra.Rel R L) u
  change C ((UniversalEnvelopingAlgebra.mkAlgHom R L) t)
  induction t using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact h_alg r
  | ι x => exact h_ι x
  | mul a b ha hb => rw [map_mul]; exact h_mul _ _ ha hb
  | add a b ha hb => rw [map_add]; exact h_add _ _ ha hb


lemma lieModuleHom_ueaSubalg_compat_gen
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M N : Type*} [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (f : M →ₗ⁅R, 𝔤⁆ N)
    (u : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) (m : M) :
    f ((ueaSubalgAction Δ.𝔫_neg M u) m) = (ueaSubalgAction Δ.𝔫_neg N u) (f m) := by
  suffices h : ∀ m, f ((ueaSubalgAction Δ.𝔫_neg M u) m) =
      (ueaSubalgAction Δ.𝔫_neg N u) (f m) from h m
  induction u using UEA_induction_on_gen with
  | h_alg r =>
    intro m
    simp only [ueaSubalgAction, Algebra.algebraMap_eq_smul_one]
    simp [LinearMap.smul_apply, map_smul]
  | h_ι x =>
    intro m
    simp only [ueaSubalgAction, UniversalEnvelopingAlgebra.lift_ι_apply,
      LieModule.toEnd_apply_apply]
    exact f.map_lie x m
  | h_mul a b ha hb =>
    intro m
    simp only [map_mul]
    change f ((ueaSubalgAction Δ.𝔫_neg M a).comp (ueaSubalgAction Δ.𝔫_neg M b) m) =
           (ueaSubalgAction Δ.𝔫_neg N a).comp (ueaSubalgAction Δ.𝔫_neg N b) (f m)
    simp only [LinearMap.comp_apply]
    rw [ha ((ueaSubalgAction Δ.𝔫_neg M b) m)]
    congr 1
    exact hb m
  | h_add a b ha hb =>
    intro m
    simp only [map_add, LinearMap.add_apply, map_add]
    rw [ha m, hb m]


lemma Module.Free.of_right_split_ses
    {S : Type*} [Ring S]
    {A M B : Type*} [AddCommGroup A] [AddCommGroup M] [AddCommGroup B]
    [Module S A] [Module S M] [Module S B]
    (j : A →ₗ[S] M) (g : M →ₗ[S] B) (s : B →ₗ[S] M)
    (hj_inj : Function.Injective j)
    (hexact : LinearMap.range j = LinearMap.ker g)
    (hgs : g.comp s = LinearMap.id)
    (hA : Module.Free S A) (hB : Module.Free S B) :
    Module.Free S M := by
  haveI := hA; haveI := hB
  let φ : A × B →ₗ[S] M := j.coprod s
  have hg_j : ∀ a, g (j a) = 0 := by
    intro a
    have : j a ∈ LinearMap.range j := ⟨a, rfl⟩
    rw [hexact] at this; exact this
  have hg_s : ∀ b, g (s b) = b := fun b => LinearMap.ext_iff.mp hgs b
  have φ_bij : Function.Bijective φ := by
    constructor
    · intro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ h
      have h' : j a₁ + s b₁ = j a₂ + s b₂ := h
      have hg1 : g (j a₁ + s b₁) = g (j a₂ + s b₂) := congr_arg g h'
      rw [map_add, map_add, hg_j, hg_j, zero_add, zero_add, hg_s, hg_s] at hg1
      subst hg1
      have hja : j a₁ = j a₂ := by rwa [add_right_cancel_iff] at h'
      exact Prod.ext (hj_inj hja) rfl
    · intro m
      have hmsg : m - s (g m) ∈ LinearMap.ker g := by
        rw [LinearMap.mem_ker, map_sub, hg_s, sub_self]
      rw [← hexact] at hmsg
      obtain ⟨a, ha⟩ := hmsg
      exact ⟨⟨a, g m⟩, show j a + s (g m) = m from by rw [ha, sub_add_cancel]⟩
  exact Module.Free.of_equiv' (Module.Free.prod S A B)
    (LinearEquiv.ofBijective φ φ_bij)


noncomputable def lieModuleHomToUEALinearMap_gen
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    {N : Type*} [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (f : M →ₗ⁅R, 𝔤⁆ N) :
    letI := instModuleUEASubalg Δ.𝔫_neg M
    letI := instModuleUEASubalg Δ.𝔫_neg N
    M →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] N := by
  letI := instModuleUEASubalg Δ.𝔫_neg M
  letI := instModuleUEASubalg Δ.𝔫_neg N
  exact {
    toFun := f
    map_add' := f.toLinearMap.map_add
    map_smul' := fun r m => lieModuleHom_ueaSubalg_compat_gen f r m

  }

theorem standard_filtration_free_nminus_helper
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hSF : HasStandardFiltration rd X hXO) :
    letI := instModuleUEASubalg Δ.𝔫_neg X
    Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) X := by
  letI instX := instModuleUEASubalg Δ.𝔫_neg X

  obtain ⟨n, F, hbot, htop, hmono, hverma⟩ := hSF

  suffices hfree : ∀ (k : ℕ) (hk : k ≤ n),
      letI := instModuleUEASubalg Δ.𝔫_neg ↥(F ⟨k, Nat.lt_succ_of_le hk⟩)
      Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) ↥(F ⟨k, Nat.lt_succ_of_le hk⟩) by

    have h_Fn_free := hfree n le_rfl
    letI := instModuleUEASubalg Δ.𝔫_neg ↥(F ⟨n, Nat.lt_succ_of_le le_rfl⟩)
    haveI := h_Fn_free


    have hFn_top : F ⟨n, Nat.lt_succ_of_le le_rfl⟩ = ⊤ := htop


    let incl : ↥(F ⟨n, Nat.lt_succ_of_le le_rfl⟩) →ₗ⁅R, 𝔤⁆ X :=
      (F ⟨n, Nat.lt_succ_of_le le_rfl⟩).incl
    have incl_bij : Function.Bijective incl := by
      constructor
      · exact Subtype.val_injective
      · intro x
        have : x ∈ (F ⟨n, Nat.lt_succ_of_le le_rfl⟩ : LieSubmodule R 𝔤 X) := by
          rw [hFn_top]; trivial
        exact ⟨⟨x, this⟩, rfl⟩
    let incl_U := lieModuleHomToUEALinearMap_gen (Δ := Δ) incl
    let e : ↥(F ⟨n, Nat.lt_succ_of_le le_rfl⟩) ≃ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] X :=
      LinearEquiv.ofBijective incl_U incl_bij
    exact Module.Free.of_equiv' h_Fn_free e

  intro k
  induction k with
  | zero =>
    intro hk
    letI := instModuleUEASubalg Δ.𝔫_neg ↥(F ⟨0, Nat.lt_succ_of_le hk⟩)

    have hF0 : F ⟨0, Nat.lt_succ_of_le hk⟩ = ⊥ := by
      convert hbot using 2
    haveI : Subsingleton ↥(F ⟨0, Nat.lt_succ_of_le hk⟩) := by
      rw [hF0]
      exact subsingleton_of_forall_eq 0 (fun ⟨x, hx⟩ => by
        ext; simp only [LieSubmodule.mem_bot] at hx; exact hx)
    exact Module.Free.of_subsingleton _ _

  | succ k ih =>
    intro hk

    have hk' : k ≤ n := Nat.le_of_succ_le hk
    have ih_free := ih hk'

    have hkn : k < n := Nat.lt_of_succ_le hk


    letI := instModuleUEASubalg Δ.𝔫_neg ↥(F ⟨k + 1, Nat.lt_succ_of_le hk⟩)
    letI := instModuleUEASubalg Δ.𝔫_neg ↥(F ⟨k, Nat.lt_succ_of_le hk'⟩)

    obtain ⟨lam_k, Q, instACG_Q, instMod_Q, instLRM_Q, instLM_Q, hVerma_Q, π, hπ_surj, hπ_ker⟩ :=
      hverma ⟨k, hkn⟩

    letI := instACG_Q; letI := instMod_Q; letI := instLRM_Q; letI := instLM_Q
    letI := instModuleUEASubalg Δ.𝔫_neg Q

    have hQ_free : Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) Q := by
      obtain ⟨φ, _⟩ := hVerma_Q.free_over_nminus
      exact Module.Free.of_equiv' (Module.Free.self _) φ
    haveI : Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) Q := hQ_free
    haveI : Module.Projective (UniversalEnvelopingAlgebra R Δ.𝔫_neg) Q :=
      Module.Projective.of_free

    letI := instModuleUEASubalg Δ.𝔫_neg ↥(F (⟨k, hkn⟩ : Fin n).succ)
    letI := instModuleUEASubalg Δ.𝔫_neg ↥(F (⟨k, hkn⟩ : Fin n).castSucc)

    let π_U := lieModuleHomToUEALinearMap_gen (Δ := Δ) π

    obtain ⟨sect, hsect⟩ := Module.projective_lifting_property π_U LinearMap.id hπ_surj

    have hle : F (⟨k, hkn⟩ : Fin n).castSucc ≤ F (⟨k, hkn⟩ : Fin n).succ :=
      le_of_lt (hmono ⟨k, hkn⟩)
    let j_lie := LieSubmodule.inclusion hle
    let j_U := lieModuleHomToUEALinearMap_gen (Δ := Δ) j_lie

    have hj_inj : Function.Injective j_U := by
      intro ⟨a, ha⟩ ⟨b, hb⟩ h
      have : (j_U ⟨a, ha⟩ : ↥(F (⟨k, hkn⟩ : Fin n).succ)).val =
             (j_U ⟨b, hb⟩ : ↥(F (⟨k, hkn⟩ : Fin n).succ)).val := congr_arg Subtype.val h
      exact Subtype.ext this

    have hexact : LinearMap.range j_U = LinearMap.ker π_U := by
      ext ⟨x, hx⟩
      simp only [LinearMap.mem_range, LinearMap.mem_ker]
      constructor
      · rintro ⟨⟨y, hy⟩, heq⟩
        have : π (j_lie ⟨y, hy⟩) = 0 := (hπ_ker (j_lie ⟨y, hy⟩)).mpr hy


        rw [← heq]
        exact this
      · intro hmem
        have hx_in_cast : (⟨x, hx⟩ : ↥(F (⟨k, hkn⟩ : Fin n).succ)).val ∈
            F (⟨k, hkn⟩ : Fin n).castSucc := by
          exact (hπ_ker ⟨x, hx⟩).mp hmem
        exact ⟨⟨x, hx_in_cast⟩, Subtype.ext rfl⟩

    exact Module.Free.of_right_split_ses j_U π_U sect hj_inj hexact hsect ih_free hQ_free


lemma UEA_induction_on_local
    {R : Type*} [CommRing R]
    {L : Type*} [LieRing L] [LieAlgebra R L]
    {C : UniversalEnvelopingAlgebra R L → Prop}
    (u : UniversalEnvelopingAlgebra R L)
    (h_alg : ∀ r : R, C (algebraMap R _ r))
    (h_ι : ∀ x : L, C (UniversalEnvelopingAlgebra.ι R x))
    (h_mul : ∀ a b, C a → C b → C (a * b))
    (h_add : ∀ a b, C a → C b → C (a + b)) :
    C u := by
  obtain ⟨t, rfl⟩ := RingQuot.mkAlgHom_surjective R
    (UniversalEnvelopingAlgebra.Rel R L) u
  change C ((UniversalEnvelopingAlgebra.mkAlgHom R L) t)
  induction t using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact h_alg r
  | ι x => exact h_ι x
  | mul a b ha hb => rw [map_mul]; exact h_mul _ _ ha hb
  | add a b ha hb => rw [map_add]; exact h_add _ _ ha hb


lemma lieModuleHom_ueaSubalg_compat_local
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M N : Type*} [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (f : M →ₗ⁅R, 𝔤⁆ N)
    (u : UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg) (m : M) :
    f ((ueaSubalgAction Δ.𝔫_neg M u) m) = (ueaSubalgAction Δ.𝔫_neg N u) (f m) := by
  suffices h : ∀ m, f ((ueaSubalgAction Δ.𝔫_neg M u) m) =
      (ueaSubalgAction Δ.𝔫_neg N u) (f m) from h m
  induction u using UEA_induction_on_local with
  | h_alg r =>
    intro m
    simp only [ueaSubalgAction, Algebra.algebraMap_eq_smul_one]
    simp [LinearMap.smul_apply, map_smul]
  | h_ι x =>
    intro m
    simp only [ueaSubalgAction, UniversalEnvelopingAlgebra.lift_ι_apply,
      LieModule.toEnd_apply_apply]
    exact f.map_lie x m
  | h_mul a b ha hb =>
    intro m
    simp only [map_mul]
    change f ((ueaSubalgAction Δ.𝔫_neg M a).comp (ueaSubalgAction Δ.𝔫_neg M b) m) =
           (ueaSubalgAction Δ.𝔫_neg N a).comp (ueaSubalgAction Δ.𝔫_neg N b) (f m)
    simp only [LinearMap.comp_apply]
    rw [ha ((ueaSubalgAction Δ.𝔫_neg M b) m)]
    congr 1
    exact hb m
  | h_add a b ha hb =>
    intro m
    simp only [map_add, LinearMap.add_apply, map_add]
    rw [ha m, hb m]


noncomputable def lieModuleHomToUEALinearMap_local
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M N : Type uCatO} [AddCommGroup M] [Module R M] [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    [AddCommGroup N] [Module R N] [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (f : M →ₗ⁅R, 𝔤⁆ N) :
    letI := instModuleUEASubalg Δ.𝔫_neg M
    letI := instModuleUEASubalg Δ.𝔫_neg N
    M →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] N := by
  letI := instModuleUEASubalg Δ.𝔫_neg M
  letI := instModuleUEASubalg Δ.𝔫_neg N
  exact {
    toFun := f
    map_add' := f.toLinearMap.map_add
    map_smul' := fun r m => lieModuleHom_ueaSubalg_compat_local f r m
  }

theorem free_nminus_is_projective
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXfree : letI := instModuleUEASubalg Δ.𝔫_neg X;
              Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) X) :
    letI := instModuleUEASubalg Δ.𝔫_neg X;
    Module.Projective (UniversalEnvelopingAlgebra R Δ.𝔫_neg) X := by
  letI := instModuleUEASubalg Δ.𝔫_neg X
  haveI := hXfree
  exact Module.Projective.of_free

theorem projective_nminus_gives_section
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    {E : Type uCatO} [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    (p : E →ₗ⁅R, 𝔤⁆ X) (hp : Function.Surjective p)
    (hXproj : letI := instModuleUEASubalg Δ.𝔫_neg X;
              Module.Projective (UniversalEnvelopingAlgebra R Δ.𝔫_neg) X) :
    letI := instModuleUEASubalg Δ.𝔫_neg X;
    letI := instModuleUEASubalg Δ.𝔫_neg E;
    ∃ (s₀ : X →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] E),
      ∀ x, p (s₀ x) = x := by
  letI := instModuleUEASubalg Δ.𝔫_neg X
  letI := instModuleUEASubalg Δ.𝔫_neg E
  haveI := hXproj

  let p_U : E →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] X :=
    lieModuleHomToUEALinearMap_local p

  have hp_surj : Function.Surjective p_U := hp
  obtain ⟨s₀, hs₀⟩ := Module.projective_lifting_property p_U LinearMap.id hp_surj
  exact ⟨s₀, fun x => by
    have := LinearMap.ext_iff.mp hs₀ x
    simp [p_U, LinearMap.comp_apply, LinearMap.id_apply] at this
    exact this⟩

theorem frobenius_reciprocity_borel_neg_to_g_section
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (_hXO : IsCategoryO Δ rd X)
    {E : Type uCatO} [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    (_hEO : IsCategoryO Δ rd E)
    (lam : Δ.𝔥 →ₗ[R] R)
    (p : E →ₗ⁅R, 𝔤⁆ X) (_hp : Function.Surjective p)
    (_hKerContra : ∃ (MlamDual : Type uCatO) (_ : AddCommGroup MlamDual) (_ : Module R MlamDual)
      (_ : LieRingModule 𝔤 MlamDual) (_ : LieModule R 𝔤 MlamDual)
      (hMlamDualO : IsCategoryO Δ rd MlamDual)
      (_ : IsContragredientVerma rd MlamDual lam hMlamDualO)
      (i : MlamDual →ₗ⁅R, 𝔤⁆ E),
      Function.Injective i ∧ (∀ e : E, p e = 0 ↔ ∃ m : MlamDual, i m = e))

    (_s₀ : letI := instModuleUEASubalg Δ.𝔫_neg X;
           letI := instModuleUEASubalg Δ.𝔫_neg E;
           X →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] E)
    (_hs₀ : ∀ x, p (_s₀ x) = x)

    (_hs₀_weight : ∀ (h : Δ.𝔥) (x : X),
      _s₀ (⁅(h : 𝔤), x⁆) = ⁅(h : 𝔤), _s₀ x⁆) :
    ∃ (s : X →ₗ⁅R, 𝔤⁆ E), ∀ x, p (s x) = x := by


  obtain ⟨MlamDual, instACG, instMod, instLRM, instLM, hMlamDualO, hContra, i, hi, hexact⟩ :=
    _hKerContra
  exact frobenius_reciprocity_coinduction_splitting _hXO lam MlamDual hMlamDualO
    hContra E _hEO i hi p _hp hexact

noncomputable def weightSpaceProjector
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hw : HasWeightDecomposition Δ M)
    (μ : Δ.𝔥 →ₗ[R] R) : M →ₗ[R] M :=

  sorry

theorem weightSpaceProjector_mem
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hw : HasWeightDecomposition Δ M)
    (μ : Δ.𝔥 →ₗ[R] R) (m : M) :
    weightSpaceProjector hw μ m ∈ WeightSpace Δ M μ := by

  sorry

theorem weightSpaceProjector_sum
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hw : HasWeightDecomposition Δ M)
    (m : M) : ∃ (S : Finset (Δ.𝔥 →ₗ[R] R)),
    m = ∑ μ ∈ S, weightSpaceProjector hw μ m := by

  sorry

theorem weightSpaceProjector_idempotent
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hw : HasWeightDecomposition Δ M)
    (μ : Δ.𝔥 →ₗ[R] R) (m : M) :
    weightSpaceProjector hw μ (weightSpaceProjector hw μ m) =
    weightSpaceProjector hw μ m := by

  sorry

theorem weightSpaceProjector_naturality
    {R : Type*} [CommRing R] {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {E : Type*} [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    {X : Type*} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hwE : HasWeightDecomposition Δ E)
    (hwX : HasWeightDecomposition Δ X)
    (f : E →ₗ⁅R, 𝔤⁆ X)
    (μ : Δ.𝔥 →ₗ[R] R) (e : E) :
    f (weightSpaceProjector hwE μ e) = weightSpaceProjector hwX μ (f e) := by

  sorry

theorem weightSpaceProjector_diag_uea_map
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {X : Type*} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    {E : Type*} [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    (hwX : HasWeightDecomposition Δ X)
    (hwE : HasWeightDecomposition Δ E)
    (s₀ : letI := instModuleUEASubalg Δ.𝔫_neg X;
          letI := instModuleUEASubalg Δ.𝔫_neg E;
          X →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] E) :
    ∃ (s₁ : letI := instModuleUEASubalg Δ.𝔫_neg X;
            letI := instModuleUEASubalg Δ.𝔫_neg E;
            X →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] E),
      (∀ (μ : Δ.𝔥 →ₗ[R] R) (x : X),
        x ∈ WeightSpace Δ X μ → s₁ x = weightSpaceProjector hwE μ (s₀ x)) ∧
      (∀ (h : Δ.𝔥) (x : X), s₁ (⁅(h : 𝔤), x⁆) = ⁅(h : 𝔤), s₁ x⁆) := by

  sorry

theorem categoryO_weight_diag_section_ax
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    {E : Type uCatO} [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    (hEO : IsCategoryO Δ rd E)
    (p : E →ₗ⁅R, 𝔤⁆ X) (_hp : Function.Surjective p)
    (s₀ : letI := instModuleUEASubalg Δ.𝔫_neg X;
          letI := instModuleUEASubalg Δ.𝔫_neg E;
          X →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] E)
    (hs₀ : ∀ x, p (s₀ x) = x) :
    ∃ (s₁ : letI := instModuleUEASubalg Δ.𝔫_neg X;
            letI := instModuleUEASubalg Δ.𝔫_neg E;
            X →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] E),
      (∀ x, p (s₁ x) = x) ∧
      (∀ (h : Δ.𝔥) (x : X), s₁ (⁅(h : 𝔤), x⁆) = ⁅(h : 𝔤), s₁ x⁆) := by

  obtain ⟨s₁, hs₁_diag, hs₁_equiv⟩ := weightSpaceProjector_diag_uea_map
    hXO.weight_decomp hEO.weight_decomp s₀
  refine ⟨s₁, ?_, ?_⟩

  · intro x

    obtain ⟨S, hS⟩ := weightSpaceProjector_sum hXO.weight_decomp x

    conv_lhs => rw [hS]
    rw [map_sum, map_sum]

    conv_rhs => rw [hS]

    apply Finset.sum_congr rfl
    intro μ _
    have hμ_mem : weightSpaceProjector hXO.weight_decomp μ x ∈ WeightSpace Δ X μ :=
      weightSpaceProjector_mem hXO.weight_decomp μ x

    rw [hs₁_diag μ _ hμ_mem]

    rw [weightSpaceProjector_naturality hEO.weight_decomp hXO.weight_decomp p μ]

    rw [hs₀]

    exact weightSpaceProjector_idempotent hXO.weight_decomp μ x

  · exact hs₁_equiv

theorem nminus_section_to_borel_neg_section
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    {E : Type uCatO} [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    (hEO : IsCategoryO Δ rd E)
    (p : E →ₗ⁅R, 𝔤⁆ X) (_hp : Function.Surjective p)
    (s₀ : letI := instModuleUEASubalg Δ.𝔫_neg X;
          letI := instModuleUEASubalg Δ.𝔫_neg E;
          X →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] E)
    (hs₀ : ∀ x, p (s₀ x) = x) :
    ∃ (s₁ : letI := instModuleUEASubalg Δ.𝔫_neg X;
            letI := instModuleUEASubalg Δ.𝔫_neg E;
            X →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] E),
      (∀ x, p (s₁ x) = x) ∧
      (∀ (h : Δ.𝔥) (x : X), s₁ (⁅(h : 𝔤), x⁆) = ⁅(h : 𝔤), s₁ x⁆) := by
  exact categoryO_weight_diag_section_ax hXO hEO p _hp s₀ hs₀

theorem frobenius_reciprocity_section_lift
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (_hXO : IsCategoryO Δ rd X)
    {E : Type uCatO} [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    (_hEO : IsCategoryO Δ rd E)
    (lam : Δ.𝔥 →ₗ[R] R)
    (p : E →ₗ⁅R, 𝔤⁆ X) (_hp : Function.Surjective p)
    (_hKerContra : ∃ (MlamDual : Type uCatO) (_ : AddCommGroup MlamDual) (_ : Module R MlamDual)
      (_ : LieRingModule 𝔤 MlamDual) (_ : LieModule R 𝔤 MlamDual)
      (hMlamDualO : IsCategoryO Δ rd MlamDual)
      (_ : IsContragredientVerma rd MlamDual lam hMlamDualO)
      (i : MlamDual →ₗ⁅R, 𝔤⁆ E),
      Function.Injective i ∧ (∀ e : E, p e = 0 ↔ ∃ m : MlamDual, i m = e))
    (_s₀ : letI := instModuleUEASubalg Δ.𝔫_neg X;
           letI := instModuleUEASubalg Δ.𝔫_neg E;
           X →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] E)
    (_hs₀ : ∀ x, p (_s₀ x) = x) :
    ∃ (s : X →ₗ⁅R, 𝔤⁆ E), ∀ x, p (s x) = x := by


  obtain ⟨s₁, hs₁_sect, hs₁_weight⟩ :=
    nminus_section_to_borel_neg_section _hXO _hEO p _hp _s₀ _hs₀


  exact frobenius_reciprocity_borel_neg_to_g_section _hXO _hEO lam
    p _hp _hKerContra s₁ hs₁_sect hs₁_weight

theorem nminus_section_lifts_to_g_section
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (_hXO : IsCategoryO Δ rd X)
    {E : Type uCatO} [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    (_hEO : IsCategoryO Δ rd E)
    (lam : Δ.𝔥 →ₗ[R] R)
    {MlamDual : Type uCatO} [AddCommGroup MlamDual] [Module R MlamDual]
    [LieRingModule 𝔤 MlamDual] [LieModule R 𝔤 MlamDual]
    (_hMlamDualO : IsCategoryO Δ rd MlamDual)
    (_hContra : IsContragredientVerma rd MlamDual lam _hMlamDualO)
    (i : MlamDual →ₗ⁅R, 𝔤⁆ E) (_hi : Function.Injective i)
    (p : E →ₗ⁅R, 𝔤⁆ X) (_hp : Function.Surjective p)
    (_hexact : ∀ e : E, p e = 0 ↔ ∃ m : MlamDual, i m = e)
    (_s₀ : letI := instModuleUEASubalg Δ.𝔫_neg X;
           letI := instModuleUEASubalg Δ.𝔫_neg E;
           X →ₗ[UniversalEnvelopingAlgebra R ↥Δ.𝔫_neg] E)
    (_hs₀ : ∀ x, p (_s₀ x) = x) :
    ∃ (s : X →ₗ⁅R, 𝔤⁆ E), ∀ x, p (s x) = x := by


  exact frobenius_reciprocity_section_lift _hXO _hEO lam
    p _hp
    ⟨MlamDual, inferInstance, inferInstance, inferInstance, inferInstance,
     _hMlamDualO, _hContra, i, _hi, _hexact⟩
    _s₀ _hs₀

theorem ext1_vanishing_free_nminus_axiom
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hXfree : letI := instModuleUEASubalg Δ.𝔫_neg X;
              Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) X) :
    Ext1VanishingForContragredientVerma rd X hXO := by

  intro lam MlamDual _ _ _ _ hMlamDualO hContra E _ _ _ _ hEO i hi p hp _hexact

  have hXproj := free_nminus_is_projective hXfree

  obtain ⟨s₀, hs₀⟩ := projective_nminus_gives_section p hp hXproj

  exact nminus_section_lifts_to_g_section hXO hEO lam hMlamDualO hContra i hi p hp _hexact s₀ hs₀

theorem free_nminus_splits_contragredient_verma_ses
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hXfree : letI := instModuleUEASubalg Δ.𝔫_neg X;
              Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) X)
    (lam : Δ.𝔥 →ₗ[R] R)
    (MlamDual : Type uCatO) [AddCommGroup MlamDual] [Module R MlamDual]
    [LieRingModule 𝔤 MlamDual] [LieModule R 𝔤 MlamDual]
    (hMlamDualO : IsCategoryO Δ rd MlamDual)
    (hContra : IsContragredientVerma rd MlamDual lam hMlamDualO)
    (E : Type uCatO) [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    (hEO : IsCategoryO Δ rd E)
    (i : MlamDual →ₗ⁅R, 𝔤⁆ E) (hi : Function.Injective i)
    (p : E →ₗ⁅R, 𝔤⁆ X) (hp : Function.Surjective p)
    (hexact : ∀ e : E, p e = 0 ↔ ∃ m : MlamDual, i m = e) :
    ∃ (s : X →ₗ⁅R, 𝔤⁆ E), ∀ x, p (s x) = x := by
  exact ext1_vanishing_free_nminus_axiom hXO hXfree lam MlamDual hMlamDualO hContra E hEO i hi p hp hexact

theorem ext_vanishing_of_standard_filtration_splitting
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hSF : HasStandardFiltration rd X hXO)
    (lam : Δ.𝔥 →ₗ[R] R)
    (MlamDual : Type uCatO) [AddCommGroup MlamDual] [Module R MlamDual]
    [LieRingModule 𝔤 MlamDual] [LieModule R 𝔤 MlamDual]
    (hMlamDualO : IsCategoryO Δ rd MlamDual)
    (hContra : IsContragredientVerma rd MlamDual lam hMlamDualO)
    (E : Type uCatO) [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    (hEO : IsCategoryO Δ rd E)
    (i : MlamDual →ₗ⁅R, 𝔤⁆ E) (hi : Function.Injective i)
    (p : E →ₗ⁅R, 𝔤⁆ X) (hp : Function.Surjective p)
    (hexact : ∀ e : E, p e = 0 ↔ ∃ m : MlamDual, i m = e) :
    ∃ (s : X →ₗ⁅R, 𝔤⁆ E), ∀ x, p (s x) = x := by

  have hXfree := standard_filtration_free_nminus_helper hXO hSF

  exact free_nminus_splits_contragredient_verma_ses hXO hXfree lam MlamDual
    hMlamDualO hContra E hEO i hi p hp hexact

theorem ext_vanishing_of_standard_filtration
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hSF : HasStandardFiltration rd X hXO) :
    Ext1VanishingForContragredientVerma rd X hXO := by


  intro lam MlamDual _ _ _ _ hMlamDualO hContra E _ _ _ _ hEO i hi p hp hexact
  exact ext_vanishing_of_standard_filtration_splitting hXO hSF lam MlamDual
    hMlamDualO hContra E hEO i hi p hp hexact

theorem standard_filtration_iff_ext_vanishing
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X) :
    HasStandardFiltration rd X hXO ↔
    Ext1VanishingForContragredientVerma rd X hXO :=
  ⟨ext_vanishing_of_standard_filtration hXO,
   standard_filtration_of_ext_vanishing hXO⟩


def IsFreeOverNMinus
    {Δ : TriangularDecomposition R 𝔤}
    (X : Type*) [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X] : Prop :=
  letI := instModuleUEASubalg Δ.𝔫_neg X
  Module.Free (UniversalEnvelopingAlgebra R Δ.𝔫_neg) X

theorem ext1_splits_free_nminus
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hXfree : IsFreeOverNMinus (Δ := Δ) X)
    (lam : Δ.𝔥 →ₗ[R] R)
    (MlamDual : Type uCatO) [AddCommGroup MlamDual] [Module R MlamDual]
    [LieRingModule 𝔤 MlamDual] [LieModule R 𝔤 MlamDual]
    (hMlamDualO : IsCategoryO Δ rd MlamDual)
    (_hContra : IsContragredientVerma rd MlamDual lam hMlamDualO)
    (E : Type uCatO) [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    (_hEO : IsCategoryO Δ rd E)
    (i : MlamDual →ₗ⁅R, 𝔤⁆ E) (_hi : Function.Injective i)
    (p : E →ₗ⁅R, 𝔤⁆ X) (hp : Function.Surjective p)
    (hexact : ∀ e : E, p e = 0 ↔ ∃ m : MlamDual, i m = e) :
    ∃ (s : X →ₗ⁅R, 𝔤⁆ E), ∀ x, p (s x) = x := by


  unfold IsFreeOverNMinus at hXfree
  exact free_nminus_splits_contragredient_verma_ses hXO hXfree lam MlamDual
    hMlamDualO _hContra E _hEO i _hi p hp hexact

theorem free_nminus_has_standard_filtration
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {X : Type uCatO} [AddCommGroup X] [Module R X]
    [LieRingModule 𝔤 X] [LieModule R 𝔤 X]
    (hXO : IsCategoryO Δ rd X)
    (hXfree : IsFreeOverNMinus (Δ := Δ) X) :
    HasStandardFiltration rd X hXO := by
  apply standard_filtration_of_ext_vanishing hXO
  intro lam MlamDual _ _ _ _ hMlamDualO hContra E _ _ _ _ hEO i hi p hp hexact
  exact ext1_splits_free_nminus hXO hXfree lam MlamDual hMlamDualO hContra E hEO i hi p hp hexact

theorem projective_has_standard_filtration
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {P : Type uCatO} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (hPO : IsCategoryO Δ rd P)
    (hPproj : IsProjectiveInO rd P hPO) :
    HasStandardFiltration rd P hPO := by


  apply standard_filtration_of_ext_vanishing hPO
  intro lam MlamDual _ _ _ _ hMlamDualO _hContra E _ _ _ _ hEO i _hi p hp _hexact


  exact hPproj E hEO P hPO p hp (LieModuleHom.id : P →ₗ⁅R, 𝔤⁆ P)

theorem projective_in_O_is_free_U_nminus
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {wg : WeylGroupData Δ}
    {P : Type uCatO} [AddCommGroup P] [Module R P]
    [LieRingModule 𝔤 P] [LieModule R 𝔤 P]
    (hPO : IsCategoryO Δ rd P)
    (hPproj : IsProjectiveInO rd P hPO) :
    letI := instModuleUEASubalg Δ.𝔫_neg P
    Module.Free (UniversalEnvelopingAlgebra R ↥(Δ.𝔫_neg)) P := by

  have hSF : HasStandardFiltration rd P hPO :=
    projective_has_standard_filtration (wg := wg) hPO hPproj

  exact standard_filtration_free_nminus_helper hPO hSF

theorem bgg_reciprocity
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R) :
    standardFiltrationMultiplicity rd wg lam mu =
    compositionMultiplicity rd wg mu lam :=
  bgg_reciprocity_raw rd wg lam mu

theorem pushout_ses_in_categoryO
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {K : Type uCatO} [AddCommGroup K] [Module R K]
    [LieRingModule 𝔤 K] [LieModule R 𝔤 K]
    (hKO : IsCategoryO Δ rd K)
    {Z : Type uCatO} [AddCommGroup Z] [Module R Z]
    [LieRingModule 𝔤 Z] [LieModule R 𝔤 Z]
    (hZO : IsCategoryO Δ rd Z)
    {M : Type uCatO} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hMO : IsCategoryO Δ rd M)
    {N : Type uCatO} [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (i : K →ₗ⁅R, 𝔤⁆ N)
    (hi : Function.Injective i)
    (p : N →ₗ⁅R, 𝔤⁆ Z)
    (hp : Function.Surjective p)
    (hexact : ∀ n, p n = 0 ↔ ∃ k, i k = n)
    (f : K →ₗ⁅R, 𝔤⁆ M) :
    ∃ (P : Type uCatO)
      (_ : AddCommGroup P) (_ : Module R P)
      (_ : LieRingModule 𝔤 P) (_ : LieModule R 𝔤 P)
      (_ : IsCategoryO Δ rd P)
      (j : M →ₗ⁅R, 𝔤⁆ P) (_ : Function.Injective j)
      (qP : P →ₗ⁅R, 𝔤⁆ Z) (_ : Function.Surjective qP)
      (emb : N →ₗ⁅R, 𝔤⁆ P),
      (∀ k, emb (i k) = j (f k)) ∧
      (∀ n, qP (emb n) = p n) ∧
      (∀ v, qP v = 0 → ∃ m, j m = v) := by

  letI prodLRM : LieRingModule 𝔤 (M × N) :=
    { bracket := fun x mn => (⁅x, mn.1⁆, ⁅x, mn.2⁆)
      add_lie := fun x y mn => by ext <;> exact add_lie x y _
      lie_add := fun x mn1 mn2 => by ext <;> exact lie_add x _ _
      leibniz_lie := fun x y mn => by
        ext
        · show ⁅x, ⁅y, mn.1⁆⁆ = ⁅⁅x, y⁆, mn.1⁆ + ⁅y, ⁅x, mn.1⁆⁆
          exact leibniz_lie x y mn.1
        · show ⁅x, ⁅y, mn.2⁆⁆ = ⁅⁅x, y⁆, mn.2⁆ + ⁅y, ⁅x, mn.2⁆⁆
          exact leibniz_lie x y mn.2 }
  letI prodLM : LieModule R 𝔤 (M × N) :=
    { smul_lie := fun r x mn => by
        ext
        · show ⁅r • x, mn.1⁆ = r • ⁅x, mn.1⁆; exact smul_lie r x mn.1
        · show ⁅r • x, mn.2⁆ = r • ⁅x, mn.2⁆; exact smul_lie r x mn.2
      lie_smul := fun r x mn => by
        ext
        · show ⁅x, r • mn.1⁆ = r • ⁅x, mn.1⁆; exact lie_smul r x mn.1
        · show ⁅x, r • mn.2⁆ = r • ⁅x, mn.2⁆; exact lie_smul r x mn.2 }

  let S : LieSubmodule R 𝔤 (M × N) :=
    { carrier := {mn | ∃ k : K, mn = (f k, -i k)}
      add_mem' := by
        rintro _ _ ⟨k1, rfl⟩ ⟨k2, rfl⟩
        exact ⟨k1 + k2, by ext <;> simp [map_add, add_comm]⟩
      zero_mem' := ⟨0, by ext <;> simp⟩
      smul_mem' := by
        rintro r _ ⟨k, rfl⟩
        exact ⟨r • k, by ext <;> simp [map_smul, smul_neg]⟩
      lie_mem := by
        rintro x _ ⟨k, rfl⟩
        exact ⟨⁅x, k⁆, by
          ext
          · show ⁅x, f k⁆ = f ⁅x, k⁆; rw [LieModuleHom.map_lie]
          · show ⁅x, -i k⁆ = -i ⁅x, k⁆; rw [lie_neg, LieModuleHom.map_lie]⟩ }

  let P := (M × N) ⧸ S
  let mkP : (M × N) →ₗ⁅R, 𝔤⁆ P := LieSubmodule.Quotient.mk' S

  let jPre : M →ₗ⁅R, 𝔤⁆ (M × N) :=
    { toFun := fun m => (m, 0)
      map_add' := fun a b => by ext <;> simp
      map_smul' := fun r m => by ext <;> simp
      map_lie' := fun {x m} => by
        ext
        · rfl
        · show 0 = ⁅x, (0 : N)⁆; rw [lie_zero] }
  let j : M →ₗ⁅R, 𝔤⁆ P := mkP.comp jPre

  let embPre : N →ₗ⁅R, 𝔤⁆ (M × N) :=
    { toFun := fun n => (0, n)
      map_add' := fun a b => by ext <;> simp
      map_smul' := fun r n => by ext <;> simp
      map_lie' := fun {x n} => by
        ext
        · show 0 = ⁅x, (0 : M)⁆; rw [lie_zero]
        · rfl }
  let emb : N →ₗ⁅R, 𝔤⁆ P := mkP.comp embPre


  have hS_ker : ∀ mn ∈ S, p mn.2 = 0 := by
    rintro ⟨m, n⟩ ⟨k, hk⟩
    have := (Prod.mk.inj hk).2
    simp only at this
    rw [this, map_neg, neg_eq_zero]
    exact (hexact (i k)).mpr ⟨k, rfl⟩

  let qPlin : P →ₗ[R] Z :=
    S.toSubmodule.liftQ (p.toLinearMap.comp (LinearMap.snd R M N)) (by
      intro mn hmn
      simp only [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.snd_apply]
      exact hS_ker mn hmn)

  have qP_lie : ∀ (x : 𝔤) (v : P), qPlin ⁅x, v⁆ = ⁅x, qPlin v⁆ := by
    intro x v
    obtain ⟨mn, rfl⟩ := LieSubmodule.Quotient.surjective_mk' S v
    show qPlin (mkP ⁅x, mn⁆) = ⁅x, qPlin (mkP mn)⁆


    change Submodule.liftQ _ _ _ (Submodule.Quotient.mk ⁅x, mn⁆) =
      ⁅x, Submodule.liftQ _ _ _ (Submodule.Quotient.mk mn)⁆
    simp only [Submodule.liftQ_apply]
    show p ⁅x, mn.2⁆ = ⁅x, p mn.2⁆
    rw [LieModuleHom.map_lie]
  let qP : P →ₗ⁅R, 𝔤⁆ Z :=
    { qPlin with
      map_lie' := fun {x v} => qP_lie x v }


  have hj_inj : Function.Injective j := by
    intro m1 m2 hm
    change mkP (jPre m1) = mkP (jPre m2) at hm
    rw [← sub_eq_zero, ← map_sub] at hm
    have hmem : jPre m1 - jPre m2 ∈ S := by
      rwa [LieSubmodule.Quotient.mk_eq_zero] at hm
    obtain ⟨k, hk⟩ := hmem
    have hk2 : (0 : N) - 0 = -i k := (Prod.mk.inj hk).2
    simp only [sub_self] at hk2
    have hik0 : i k = 0 := neg_eq_zero.mp (hk2.symm)
    have hk0 : k = 0 := hi (by rw [map_zero]; exact hik0)
    have hk1 : m1 - m2 = f k := (Prod.mk.inj hk).1
    rw [hk0, map_zero] at hk1
    exact sub_eq_zero.mp hk1
  have hqP_surj : Function.Surjective qP := by
    intro z
    obtain ⟨n, hn⟩ := hp z
    exact ⟨emb n, by
      show qP (mkP (0, n)) = z
      change Submodule.liftQ _ _ _ (Submodule.Quotient.mk (0, n)) = z
      simp only [Submodule.liftQ_apply, LinearMap.comp_apply, LinearMap.snd_apply]
      exact hn⟩
  have hqP_exact : ∀ v, qP v = 0 ↔ ∃ m, j m = v := by
    intro v
    constructor
    · intro hv
      obtain ⟨⟨m, n⟩, rfl⟩ := LieSubmodule.Quotient.surjective_mk' S v
      have hpn : p n = 0 := by
        change Submodule.liftQ _ _ _ (Submodule.Quotient.mk (m, n)) = 0 at hv
        simp only [Submodule.liftQ_apply, LinearMap.comp_apply, LinearMap.snd_apply] at hv
        exact hv
      obtain ⟨k, hk⟩ := (hexact n).mp hpn
      refine ⟨m + f k, ?_⟩
      show mkP (m + f k, 0) = mkP (m, n)
      rw [← sub_eq_zero, ← map_sub]
      rw [LieSubmodule.Quotient.mk_eq_zero]
      show (m + f k, 0) - (m, n) ∈ S
      exact ⟨k, by ext <;> simp [← hk]⟩
    · rintro ⟨m, rfl⟩
      show qP (mkP (m, 0)) = 0
      change Submodule.liftQ _ _ _ (Submodule.Quotient.mk (m, 0)) = 0
      simp only [Submodule.liftQ_apply, LinearMap.comp_apply, LinearMap.snd_apply, map_zero]

  have hPO : IsCategoryO Δ rd P :=
    IsCategoryO_of_extension hMO hZO j hj_inj qP hqP_surj hqP_exact

  refine ⟨P, inferInstance, inferInstance, inferInstance, inferInstance, hPO,
         j, ?_, qP, ?_, emb, ?_, ?_, ?_⟩

  · exact hj_inj

  · exact hqP_surj

  · intro k
    show mkP (0, i k) = mkP (f k, 0)
    rw [← sub_eq_zero, ← map_sub]
    rw [LieSubmodule.Quotient.mk_eq_zero]
    show (0, i k) - (f k, 0) ∈ S
    refine ⟨-k, ?_⟩
    ext <;> simp [map_neg]

  · intro n
    show qP (mkP (0, n)) = p n
    change Submodule.liftQ _ _ _ (Submodule.Quotient.mk (0, n)) = p n
    simp only [Submodule.liftQ_apply, LinearMap.comp_apply, LinearMap.snd_apply]
    rfl

  · intro v hv
    exact (hqP_exact v).mp hv

theorem les_restriction_surjective
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {E : Type uCatO} [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    [Module.Finite R E] [LieModule.IsTrivial 𝔤 E]
    {Mlam : Type uCatO} [AddCommGroup Mlam] [Module R Mlam]
    [LieRingModule 𝔤 Mlam] [LieModule R 𝔤 Mlam]
    (hMlamO : IsCategoryO Δ rd Mlam)
    {K : Type uCatO} [AddCommGroup K] [Module R K]
    [LieRingModule 𝔤 K] [LieModule R 𝔤 K]
    (hKO : IsCategoryO Δ rd K)
    {Z : Type uCatO} [AddCommGroup Z] [Module R Z]
    [LieRingModule 𝔤 Z] [LieModule R 𝔤 Z]
    (hZO : IsCategoryO Δ rd Z)
    (i : K →ₗ⁅R, 𝔤⁆ (TensorProduct R E Mlam))
    (hi : Function.Injective i)
    (p : (TensorProduct R E Mlam) →ₗ⁅R, 𝔤⁆ Z)
    (hp : Function.Surjective p)
    (hexact : ∀ (m : TensorProduct R E Mlam), p m = 0 ↔ ∃ k : K, i k = m)
    (mu : Δ.𝔥 →ₗ[R] R)
    (MmuDual : Type uCatO) [AddCommGroup MmuDual] [Module R MmuDual]
    [LieRingModule 𝔤 MmuDual] [LieModule R 𝔤 MmuDual]
    (hMmuDualO : IsCategoryO Δ rd MmuDual)
    (_ : IsContragredientVerma rd MmuDual mu hMmuDualO)
    (hExtZ : ∀ (E' : Type uCatO) [AddCommGroup E'] [Module R E']
      [LieRingModule 𝔤 E'] [LieModule R 𝔤 E']
      (_ : IsCategoryO Δ rd E')
      (j : MmuDual →ₗ⁅R, 𝔤⁆ E') (_ : Function.Injective j)
      (q : E' →ₗ⁅R, 𝔤⁆ Z) (_ : Function.Surjective q),
      ∃ (s : Z →ₗ⁅R, 𝔤⁆ E'), ∀ z, q (s z) = z)
    (f : K →ₗ⁅R, 𝔤⁆ MmuDual) :
    ∃ (g : (TensorProduct R E Mlam) →ₗ⁅R, 𝔤⁆ MmuDual), ∀ k, f k = g (i k) := by


  obtain ⟨P, instACG_P, instMod_P, instLRM_P, instLM_P, instCatO_P,
         j, hj_inj, qP, hqP_surj, emb,
         h_comm, h_q_emb, h_ker_qP⟩ :=
    pushout_ses_in_categoryO hKO hZO hMmuDualO i hi p hp hexact f

  obtain ⟨s, hs⟩ := hExtZ P instCatO_P j hj_inj qP hqP_surj


  have hmem : ∀ n, ∃ m, j m = emb n - s (p n) := by
    intro n
    apply h_ker_qP
    simp only [map_sub, h_q_emb, hs, sub_self]

  let g_fun : TensorProduct R E Mlam → MmuDual := fun n => (hmem n).choose
  have hg_spec : ∀ n, j (g_fun n) = emb n - s (p n) :=
    fun n => (hmem n).choose_spec

  have g_add : ∀ a b, g_fun (a + b) = g_fun a + g_fun b := by
    intro a b; apply hj_inj
    simp only [hg_spec, map_add]; abel

  have g_smul : ∀ (r : R) a, g_fun (r • a) = r • g_fun a := by
    intro r a; apply hj_inj
    simp only [hg_spec, map_smul, smul_sub]

  have g_lie : ∀ (x : 𝔤) a, g_fun ⁅x, a⁆ = ⁅x, g_fun a⁆ := by
    intro x a; apply hj_inj

    rw [hg_spec]

    rw [LieModuleHom.map_lie j]

    rw [hg_spec]

    rw [lie_sub]

    rw [← LieModuleHom.map_lie emb]

    congr 1

    rw [← LieModuleHom.map_lie s, ← LieModuleHom.map_lie p]


  refine ⟨{ toFun := g_fun, map_add' := g_add, map_smul' := g_smul,
             map_lie' := fun {x n} => g_lie x n }, fun k => ?_⟩

  apply hj_inj
  simp only [LieModuleHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hg_spec]
  have hpi : p (i k) = 0 := (hexact (i k)).mpr ⟨k, rfl⟩
  rw [hpi, map_zero, sub_zero]
  exact (h_comm k).symm

theorem bilinear_vanishing_on_hwv
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {MmuDual : Type uCatO} [AddCommGroup MmuDual] [Module R MmuDual]
    [LieRingModule 𝔤 MmuDual] [LieModule R 𝔤 MmuDual]
    {Mmu_inner : Type uCatO} [AddCommGroup Mmu_inner] [Module R Mmu_inner]
    [LieRingModule 𝔤 Mmu_inner] [LieModule R 𝔤 Mmu_inner]
    (mu : Δ.𝔥 →ₗ[R] R)
    (hVerma : IsVermaModule Δ Mmu_inner mu)
    (β : MmuDual →ₗ[R] Mmu_inner →ₗ[R] R)
    (hβ_contra : ∀ (x : 𝔤) (m : MmuDual) (m' : Mmu_inner), (β ⁅x, m⁆) m' + (β m) ⁅x, m'⁆ = 0)
    (lam : Δ.𝔥 →ₗ[R] R) (hmu : lam ≠ mu)
    (w : MmuDual)
    (hw_cartan : ∀ (h : Δ.𝔥), ⁅(↑h : 𝔤), w⁆ = lam h • w)
    (hw_npos : ∀ (e : Δ.𝔫_pos), ⁅(↑e : 𝔤), w⁆ = 0)
    (w' : MmuDual)
    (hw' : w' ∈ LieSubmodule.lieSpan R 𝔤 {w}) :
    (β w') hVerma.highestWeightVec = 0 := by
  exact bilinear_vanishing_on_hwv' mu hVerma β hβ_contra lam hmu w hw_cartan hw_npos w' hw'

theorem contragredient_verma_no_hwv_of_ne
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (mu : Δ.𝔥 →ₗ[R] R)
    (MmuDual : Type uCatO) [AddCommGroup MmuDual] [Module R MmuDual]
    [LieRingModule 𝔤 MmuDual] [LieModule R 𝔤 MmuDual]
    (hMmuDualO : IsCategoryO Δ rd MmuDual)
    (hContra : IsContragredientVerma rd MmuDual mu hMmuDualO)
    (lam : Δ.𝔥 →ₗ[R] R) (hmu : lam ≠ mu)
    (w : MmuDual)
    (hw_cartan : ∀ (h : Δ.𝔥), ⁅(↑h : 𝔤), w⁆ = lam h • w)
    (hw_npos : ∀ (e : Δ.𝔫_pos), ⁅(↑e : 𝔤), w⁆ = 0) :
    w = 0 := by

  obtain ⟨Mmu_inner, _inst_acg, _inst_mod, _inst_lrm, _inst_lm,
         ⟨hVerma_ne⟩, _hMmuO_inner, β, hβ_contra, hβ_left_nd, _hβ_right_nd⟩ := hContra

  apply hβ_left_nd
  intro m'

  set N_w := LieSubmodule.lieSpan R 𝔤 ({w} : Set MmuDual) with hN_w_def

  have hw_mem : w ∈ N_w := LieSubmodule.subset_lieSpan (Set.mem_singleton w)


  suffices h_strong : ∀ w' ∈ N_w, (β w') m' = 0 from h_strong w hw_mem

  have hm'_mem : m' ∈ LieSubmodule.lieSpan R 𝔤 ({hVerma_ne.highestWeightVec} : Set Mmu_inner) := by
    rw [hVerma_ne.generates]; trivial

  revert m'
  intro m' hm'_mem
  refine LieSubmodule.lieSpan_induction R 𝔤
    (p := fun m'' _ => ∀ w' ∈ N_w, (β w') m'' = 0) ?mem ?zero ?add ?smul ?lie hm'_mem
  case mem =>

    intro m'' hm''
    rw [Set.mem_singleton_iff] at hm''
    subst hm''


    intro w' hw'
    exact bilinear_vanishing_on_hwv mu hVerma_ne β hβ_contra lam hmu w hw_cartan hw_npos w' hw'
  case zero =>

    intro w' _
    exact map_zero (β w')
  case add =>

    intro x y _ _ hx hy w' hw'
    rw [map_add, hx w' hw', hy w' hw', add_zero]
  case smul =>

    intro a x _ hx w' hw'
    rw [map_smul, hx w' hw', smul_zero]
  case lie =>

    intro x y _ hy w' hw'

    have hc := hβ_contra x w' y

    have : (β w') ⁅x, y⁆ = -((β ⁅x, w'⁆) y) := eq_neg_of_add_eq_zero_right hc
    rw [this]

    have hxw'_mem : ⁅x, w'⁆ ∈ N_w := N_w.lie_mem hw'

    rw [hy ⁅x, w'⁆ hxw'_mem, neg_zero]

theorem tensor_hom_vanishing_ne
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {E : Type uCatO} [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    [Module.Finite R E] [LieModule.IsTrivial 𝔤 E]
    {Mlam : Type uCatO} [AddCommGroup Mlam] [Module R Mlam]
    [LieRingModule 𝔤 Mlam] [LieModule R 𝔤 Mlam]
    (hMlamO : IsCategoryO Δ rd Mlam)
    (lam : Δ.𝔥 →ₗ[R] R)
    (hMlam_verma : IsVermaModule Δ Mlam lam)
    (mu : Δ.𝔥 →ₗ[R] R) (hmu : lam ≠ mu)

    (MmuDual : Type uCatO) [AddCommGroup MmuDual] [Module R MmuDual]
    [LieRingModule 𝔤 MmuDual] [LieModule R 𝔤 MmuDual]
    (hMmuDualO : IsCategoryO Δ rd MmuDual)
    (hContra : IsContragredientVerma rd MmuDual mu hMmuDualO)
    (g : (TensorProduct R E Mlam) →ₗ⁅R, 𝔤⁆ MmuDual) :
    g = 0 := by


  ext x

  induction x using TensorProduct.induction_on with
  | zero => simp [map_zero]
  | tmul e m =>


    have hw : g (e ⊗ₜ[R] hMlam_verma.highestWeightVec) = 0 := by
      apply contragredient_verma_no_hwv_of_ne mu MmuDual hMmuDualO hContra lam hmu
      ·
        intro h
        have : g ⁅(↑h : 𝔤), e ⊗ₜ[R] hMlam_verma.highestWeightVec⁆ =
            ⁅(↑h : 𝔤), g (e ⊗ₜ[R] hMlam_verma.highestWeightVec)⁆ :=
          g.map_lie' (x := ↑h)
        rw [← this]

        have htrivial : ⁅(↑h : 𝔤), e⁆ = (0 : E) :=
          LieModule.IsTrivial.trivial (↑h : 𝔤) e
        rw [TensorProduct.LieModule.lie_tmul_right (↑h : 𝔤) e hMlam_verma.highestWeightVec,
            htrivial, TensorProduct.zero_tmul, zero_add,
            hMlam_verma.cartan_action h, TensorProduct.tmul_smul, map_smul]
      ·
        intro n
        have : g ⁅(↑n : 𝔤), e ⊗ₜ[R] hMlam_verma.highestWeightVec⁆ =
            ⁅(↑n : 𝔤), g (e ⊗ₜ[R] hMlam_verma.highestWeightVec)⁆ :=
          g.map_lie' (x := ↑n)
        rw [← this]
        have htrivial : ⁅(↑n : 𝔤), e⁆ = (0 : E) :=
          LieModule.IsTrivial.trivial (↑n : 𝔤) e
        rw [TensorProduct.LieModule.lie_tmul_right (↑n : 𝔤) e hMlam_verma.highestWeightVec,
            htrivial, TensorProduct.zero_tmul, zero_add,
            hMlam_verma.npos_action n, TensorProduct.tmul_zero, map_zero]


    have f_e_eq : ∀ (m : Mlam), g (e ⊗ₜ[R] m) = 0 := by

      let f_e : Mlam →ₗ⁅R, 𝔤⁆ MmuDual :=
        { toLinearMap := (g : TensorProduct R E Mlam →ₗ[R] MmuDual).comp
            (TensorProduct.mk R E Mlam e)
          map_lie' := fun {x m'} => by
            show g ((TensorProduct.mk R E Mlam e) ⁅x, m'⁆) = ⁅x, g ((TensorProduct.mk R E Mlam e) m')⁆
            simp only [TensorProduct.mk_apply]
            have := g.map_lie' (x := x) (m := e ⊗ₜ[R] m')
            rw [TensorProduct.LieModule.lie_tmul_right,
                LieModule.IsTrivial.trivial x e,
                TensorProduct.zero_tmul, zero_add] at this
            exact this }

      have hf_eq_zero : f_e = 0 := by
        apply hMlam_verma.universal_unique
        simp [f_e, TensorProduct.mk_apply, hw]

      intro m'
      have := LieModuleHom.congr_fun hf_eq_zero m'
      simpa [f_e, TensorProduct.mk_apply] using this
    exact f_e_eq m
  | add x y hx hy =>
    simp [map_add, hx, hy]

theorem les_lemma_20_1_hom_vanishing_ne
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {E : Type uCatO} [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    [Module.Finite R E] [LieModule.IsTrivial 𝔤 E]
    {Mlam : Type uCatO} [AddCommGroup Mlam] [Module R Mlam]
    [LieRingModule 𝔤 Mlam] [LieModule R 𝔤 Mlam]
    (hMlamO : IsCategoryO Δ rd Mlam)
    (lam : Δ.𝔥 →ₗ[R] R)
    (hMlam_verma : IsVermaModule Δ Mlam lam)
    {K : Type uCatO} [AddCommGroup K] [Module R K]
    [LieRingModule 𝔤 K] [LieModule R 𝔤 K]
    (hKO : IsCategoryO Δ rd K)
    {Z : Type uCatO} [AddCommGroup Z] [Module R Z]
    [LieRingModule 𝔤 Z] [LieModule R 𝔤 Z]
    (hZO : IsCategoryO Δ rd Z)
    (i : K →ₗ⁅R, 𝔤⁆ (TensorProduct R E Mlam))
    (hi : Function.Injective i)
    (p : (TensorProduct R E Mlam) →ₗ⁅R, 𝔤⁆ Z)
    (hp : Function.Surjective p)
    (hexact : ∀ (m : TensorProduct R E Mlam), p m = 0 ↔ ∃ k : K, i k = m)
    (hExtZ : ∀ (mu : Δ.𝔥 →ₗ[R] R)
      (MmuDual : Type uCatO) [AddCommGroup MmuDual] [Module R MmuDual]
      [LieRingModule 𝔤 MmuDual] [LieModule R 𝔤 MmuDual]
      (hMmuDualO : IsCategoryO Δ rd MmuDual)
      (_ : IsContragredientVerma rd MmuDual mu hMmuDualO)
      (E' : Type uCatO) [AddCommGroup E'] [Module R E']
      [LieRingModule 𝔤 E'] [LieModule R 𝔤 E']
      (_ : IsCategoryO Δ rd E')
      (j : MmuDual →ₗ⁅R, 𝔤⁆ E') (_ : Function.Injective j)
      (q : E' →ₗ⁅R, 𝔤⁆ Z) (_ : Function.Surjective q),
      ∃ (s : Z →ₗ⁅R, 𝔤⁆ E'), ∀ z, q (s z) = z)
    (mu : Δ.𝔥 →ₗ[R] R) (hmu : mu ≠ lam)
    (MmuDual : Type uCatO) [AddCommGroup MmuDual] [Module R MmuDual]
    [LieRingModule 𝔤 MmuDual] [LieModule R 𝔤 MmuDual]
    (hMmuDualO : IsCategoryO Δ rd MmuDual)
    (hContra : IsContragredientVerma rd MmuDual mu hMmuDualO)
    (f : K →ₗ⁅R, 𝔤⁆ MmuDual) :
    f = 0 := by


  have hExtZ_mu := hExtZ mu MmuDual hMmuDualO hContra
  obtain ⟨g, hg⟩ := les_restriction_surjective hMlamO hKO hZO i hi p hp hexact
    mu MmuDual hMmuDualO hContra hExtZ_mu f

  have hg_zero : g = 0 :=
    tensor_hom_vanishing_ne hMlamO lam hMlam_verma mu hmu.symm MmuDual hMmuDualO hContra g

  ext k
  rw [hg k, hg_zero]
  simp

theorem CategoryO.exists_singular_vector_in_submodule
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (hM : IsCategoryO Δ rd M)
    (N : LieSubmodule R 𝔤 M) (hN : N ≠ ⊥) :
    ∃ (v : M) (mu : Δ.𝔥 →ₗ[R] R),
      v ∈ N ∧ v ≠ 0 ∧
      (∀ (h : Δ.𝔥), ⁅(h : 𝔤), v⁆ = mu h • v) ∧
      (∀ (e : Δ.𝔫_pos), ⁅(e : 𝔤), v⁆ = 0) := by

  have hNO : IsCategoryO Δ rd N := IsCategoryO_lieSubmodule hM N

  haveI : Nontrivial N := (LieSubmodule.nontrivial_iff_ne_bot R 𝔤 M).mpr hN

  obtain ⟨v, mu, hv_ne, hv_cartan, hv_npos⟩ :=
    CategoryO.exists_singular_vector hNO

  refine ⟨(v : M), mu, v.property, ?_, ?_, ?_⟩
  ·
    intro h; apply hv_ne; exact_mod_cast h
  ·
    intro h; exact_mod_cast hv_cartan h
  ·
    intro e; exact_mod_cast hv_npos e

theorem contragredient_verma_socle
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (lam : Δ.𝔥 →ₗ[R] R)
    (MlamDual : Type uCatO) [AddCommGroup MlamDual] [Module R MlamDual]
    [LieRingModule 𝔤 MlamDual] [LieModule R 𝔤 MlamDual]
    (_hMlamDualO : IsCategoryO Δ rd MlamDual)
    (_ : IsContragredientVerma rd MlamDual lam _hMlamDualO)
    (N : LieSubmodule R 𝔤 MlamDual)
    (hN : N ≠ ⊥) :
    ∃ (v : MlamDual), v ∈ N ∧ v ∈ WeightSpace Δ MlamDual lam ∧ v ≠ 0 := by

  obtain ⟨v, mu, hv_N, hv_ne, hv_cartan, hv_npos⟩ :=
    CategoryO.exists_singular_vector_in_submodule _hMlamDualO N hN

  by_cases hmu : lam = mu
  ·
    refine ⟨v, hv_N, ?_, hv_ne⟩

    intro h
    rw [hmu]
    exact hv_cartan h
  ·
    exfalso
    apply hv_ne
    exact contragredient_verma_no_hwv_of_ne lam MlamDual _hMlamDualO ‹_› mu (Ne.symm hmu) v hv_cartan hv_npos

lemma lie_hom_preserves_weight_space
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {K : Type*} [AddCommGroup K] [Module R K]
    [LieRingModule 𝔤 K] [LieModule R 𝔤 K]
    {N : Type*} [AddCommGroup N] [Module R N]
    [LieRingModule 𝔤 N] [LieModule R 𝔤 N]
    (f : K →ₗ⁅R, 𝔤⁆ N) (μ : Δ.𝔥 →ₗ[R] R)
    {k : K} (hk : k ∈ WeightSpace Δ K μ) :
    f k ∈ WeightSpace Δ N μ := by
  intro h
  rw [← LieModuleHom.map_lie, hk h, map_smul]

theorem weight_space_sum_disjoint
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : Type*} [AddCommGroup M] [Module R M]
    [LieRingModule 𝔤 M] [LieModule R 𝔤 M]
    (lam : Δ.𝔥 →ₗ[R] R)
    (S : Finset (Δ.𝔥 →ₗ[R] R))
    (hlamS : lam ∉ S)
    (v : (μ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ M μ)
    (m : M) (hm : m ∈ WeightSpace Δ M lam)
    (hm_sum : m = ∑ μ ∈ S, (v μ : M)) :
    m = 0 := by
  classical

  let w : (μ : Δ.𝔥 →ₗ[R] R) → WeightSpace Δ M μ := fun μ =>
    if h : μ = lam then
      ⟨-m, h ▸ (WeightSpace Δ M lam).neg_mem hm⟩
    else
      v μ

  have hsum : ∑ μ ∈ Finset.cons lam S hlamS, (w μ : M) = 0 := by
    rw [Finset.sum_cons]
    simp only [w, dif_pos rfl]
    have hsumS : ∑ μ ∈ S, (w μ : M) = ∑ μ ∈ S, (v μ : M) := by
      apply Finset.sum_congr rfl
      intro μ hμ
      have hne : μ ≠ lam := fun h => hlamS (h ▸ hμ)
      show (w μ : M) = (v μ : M)
      simp only [w, dif_neg hne]
    rw [hsumS, ← hm_sum, neg_add_cancel]

  have hw_lam := weightSpace_sum_eq_zero_components
    (Finset.cons lam S hlamS) w hsum lam (Finset.mem_cons_self lam S)

  simp only [w, dif_pos rfl] at hw_lam
  exact neg_eq_zero.mp hw_lam

theorem contragredient_verma_socle_weight_preimage
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (lam : Δ.𝔥 →ₗ[R] R)
    {K : Type uCatO} [AddCommGroup K] [Module R K]
    [LieRingModule 𝔤 K] [LieModule R 𝔤 K]
    (_hKO : IsCategoryO Δ rd K)
    (MlamDual : Type uCatO) [AddCommGroup MlamDual] [Module R MlamDual]
    [LieRingModule 𝔤 MlamDual] [LieModule R 𝔤 MlamDual]
    (_hMlamDualO : IsCategoryO Δ rd MlamDual)
    (hContra : IsContragredientVerma rd MlamDual lam _hMlamDualO)
    (f : K →ₗ⁅R, 𝔤⁆ MlamDual)
    (hf : f ≠ 0) :
    ∃ (k : K), k ∈ WeightSpace Δ K lam ∧ k ≠ 0 := by
  classical

  have hrange : f.range ≠ ⊥ := by
    intro h; apply hf; ext m
    have : f m ∈ f.range := (LieModuleHom.mem_range f (f m)).2 ⟨m, rfl⟩
    rw [h] at this; simp [LieSubmodule.mem_bot] at this; simp [this]

  obtain ⟨v, hv_range, hv_wt, hv_ne⟩ :=
    contragredient_verma_socle lam MlamDual _hMlamDualO hContra f.range hrange

  rw [LieModuleHom.mem_range] at hv_range
  obtain ⟨k, hk⟩ := hv_range

  obtain ⟨S, w, hk_decomp⟩ := _hKO.weight_decomp k


  have hfw : ∀ μ, f (w μ : K) ∈ WeightSpace Δ MlamDual μ :=
    fun μ => lie_hom_preserves_weight_space f μ (w μ).property

  have hfk_sum : f k = ∑ μ ∈ S, f (w μ : K) := by
    rw [hk_decomp]; simp [map_sum]

  by_contra h_no_wt
  push Not at h_no_wt


  have hw_lam_zero : (w lam : K) = 0 := h_no_wt (w lam) (w lam).property

  have hfw_lam_zero : f (w lam : K) = 0 := by rw [hw_lam_zero, map_zero]


  by_cases hlam : lam ∈ S
  ·
    have hv_sum : v = ∑ μ ∈ S.erase lam, f (w μ : K) := by
      rw [← hk, hfk_sum]
      rw [← Finset.add_sum_erase S _ hlam, hfw_lam_zero, zero_add]

    exact hv_ne (weight_space_sum_disjoint lam (S.erase lam) (Finset.notMem_erase lam S)
      (fun μ => ⟨f (w μ : K), hfw μ⟩) v hv_wt hv_sum)
  ·
    exact hv_ne (weight_space_sum_disjoint lam S hlam
      (fun μ => ⟨f (w μ : K), hfw μ⟩) v hv_wt (by rw [← hk, hfk_sum]))

theorem nonzero_hom_into_contragredient_gives_weight
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (lam : Δ.𝔥 →ₗ[R] R)
    {K : Type uCatO} [AddCommGroup K] [Module R K]
    [LieRingModule 𝔤 K] [LieModule R 𝔤 K]
    (_hKO : IsCategoryO Δ rd K)
    (MlamDual : Type uCatO) [AddCommGroup MlamDual] [Module R MlamDual]
    [LieRingModule 𝔤 MlamDual] [LieModule R 𝔤 MlamDual]
    (_hMlamDualO : IsCategoryO Δ rd MlamDual)
    (hContra : IsContragredientVerma rd MlamDual lam _hMlamDualO)
    (f : K →ₗ⁅R, 𝔤⁆ MlamDual)
    (hf : f ≠ 0) :
    WeightSpace Δ K lam ≠ ⊥ := by

  obtain ⟨k, hk_wt, hk_ne⟩ := contragredient_verma_socle_weight_preimage lam _hKO MlamDual _hMlamDualO hContra f hf

  intro h_bot
  rw [Submodule.eq_bot_iff] at h_bot
  exact hk_ne (h_bot k hk_wt)

theorem socle_hom_vanishing_eq
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (lam : Δ.𝔥 →ₗ[R] R)
    {K : Type uCatO} [AddCommGroup K] [Module R K]
    [LieRingModule 𝔤 K] [LieModule R 𝔤 K]
    (hKO : IsCategoryO Δ rd K)
    (hK_lam : WeightSpace Δ K lam = ⊥)
    (MlamDual : Type uCatO) [AddCommGroup MlamDual] [Module R MlamDual]
    [LieRingModule 𝔤 MlamDual] [LieModule R 𝔤 MlamDual]
    (hMlamDualO : IsCategoryO Δ rd MlamDual)
    (hContra : IsContragredientVerma rd MlamDual lam hMlamDualO)
    (f : K →ₗ⁅R, 𝔤⁆ MlamDual) :
    f = 0 := by

  by_contra hf
  exact absurd hK_lam
    (nonzero_hom_into_contragredient_gives_weight lam hKO MlamDual hMlamDualO hContra f hf)


theorem CategoryO.has_simple_quotient
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    {K : Type uCatO} [AddCommGroup K] [Module R K]
    [LieRingModule 𝔤 K] [LieModule R 𝔤 K]
    (hKO : IsCategoryO Δ rd K) [Nontrivial K] :
    ∃ (mu : Δ.𝔥 →ₗ[R] R)
      (Lmu : Type uCatO) (_ : AddCommGroup Lmu) (_ : Module R Lmu)
      (_ : LieRingModule 𝔤 Lmu) (_ : LieModule R 𝔤 Lmu)
      (hLmuO : IsCategoryO Δ rd Lmu)
      (_ : LieModule.IsIrreducible R 𝔤 Lmu)
      (_ : IsHighestWeightModule Δ Lmu mu)
      (q : K →ₗ⁅R, 𝔤⁆ Lmu),
      Function.Surjective q ∧ q ≠ 0 := by

  obtain ⟨cs⟩ := categoryO_has_composition_series hKO

  have hlen_pos : 0 < cs.length := by
    by_contra h
    simp only [not_lt, Nat.le_zero] at h
    have hlen_zero : cs.length = 0 := h
    have h_bot := cs.bot
    have h_top := cs.top
    have h_idx_eq : (⟨0, Nat.zero_lt_succ cs.length⟩ : Fin (cs.length + 1)) =
        ⟨cs.length, Nat.lt_succ_iff.mpr le_rfl⟩ := by
      ext; simp [hlen_zero]
    rw [h_idx_eq] at h_bot
    rw [h_bot] at h_top

    have hx : ∀ x : K, x = 0 := by
      intro x
      have hx_top : x ∈ (⊤ : LieSubmodule R 𝔤 K) := trivial
      rw [h_top.symm] at hx_top
      exact (LieSubmodule.mem_bot (R := R) x).mp hx_top

    obtain ⟨a, b, hab⟩ := exists_pair_ne (α := K)
    exact hab (by rw [hx a, hx b])

  set n := cs.length
  have hn_sub : n - 1 < n := Nat.sub_one_lt_of_lt hlen_pos
  set i_last : Fin n := ⟨n - 1, hn_sub⟩
  set Z := cs.series i_last.castSucc

  have hZ_lt_top : Z < ⊤ := by
    have h_strict := cs.strictly_increasing i_last
    have h_succ_val : (i_last.succ : Fin (n + 1)).val = n := by
      simp [i_last]; omega
    have h_eq : cs.series i_last.succ = cs.series ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ := by
      congr 1; ext; exact h_succ_val
    rw [h_eq, cs.top] at h_strict
    exact h_strict
  have hZ_ne_top : Z ≠ ⊤ := ne_of_lt hZ_lt_top

  have hQO : IsCategoryO Δ rd (K ⧸ Z) := IsCategoryO_quotient hKO Z


  have hQirr : LieModule.IsIrreducible R 𝔤 (K ⧸ Z) := by


    have hirr := cs.quotients_irreducible i_last

    have h_succ_eq_top : cs.series i_last.succ = ⊤ := by
      have h_succ_val : (i_last.succ : Fin (n + 1)).val = n := by
        simp [i_last]; omega
      have h_eq : cs.series i_last.succ = cs.series ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ := by
        congr 1; ext; exact h_succ_val
      rw [h_eq]; exact cs.top

    have hirr' : LieModule.IsIrreducible R 𝔤
        (↥(⊤ : LieSubmodule R 𝔤 K) ⧸ Z.comap (⊤ : LieSubmodule R 𝔤 K).incl) :=
      h_succ_eq_top ▸ hirr

    let f := LieModuleEquiv.ofTop R 𝔤 K
    let P := Z.comap (⊤ : LieSubmodule R 𝔤 K).incl
    have hfP : Submodule.map f.toLinearEquiv.toLinearMap P.toSubmodule = Z.toSubmodule := by
      ext x
      simp only [Submodule.mem_map, LieSubmodule.mem_toSubmodule]
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [LieSubmodule.mem_comap] at hy; convert hy using 1
      · intro hx
        exact ⟨⟨x, trivial⟩, by rwa [LieSubmodule.mem_comap],
          LieModuleEquiv.ofTop_apply K ⟨x, trivial⟩⟩
    let e_lin := Submodule.Quotient.equiv P.toSubmodule Z.toSubmodule f.toLinearEquiv hfP
    let e : (↥(⊤ : LieSubmodule R 𝔤 K) ⧸ P) ≃ₗ⁅R, 𝔤⁆ (K ⧸ Z) := {
      e_lin with
      map_lie' := by
        intro x m
        induction m using Quotient.inductionOn' with
        | h a =>
          show e_lin (Submodule.Quotient.mk ⁅x, a⁆) =
            Submodule.Quotient.mk ⁅x, f.toLinearEquiv a⁆
          rw [Submodule.Quotient.equiv_apply, Submodule.mapQ_apply]
          congr 1
    }

    exact ((LieSubmodule.orderIsoMapComap e).isSimpleOrder_iff).mp hirr'

  obtain ⟨mu, ⟨hHW⟩⟩ := CategoryO.simple_objects_are_highest_weight hQO hQirr

  refine ⟨mu, K ⧸ Z, inferInstance, inferInstance, inferInstance, inferInstance, hQO,
          hQirr, hHW,
          LieSubmodule.Quotient.mk' Z, LieSubmodule.Quotient.surjective_mk' Z, ?_⟩

  intro h
  apply hZ_ne_top
  ext x
  simp only [LieSubmodule.mem_top, iff_true]
  have : (LieSubmodule.Quotient.mk' Z) x = 0 := by simp [h]
  rw [LieSubmodule.Quotient.mk'_apply] at this
  rwa [LieSubmodule.Quotient.mk_eq_zero'] at this

theorem CategoryO.simple_embeds_in_contragredient_verma
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (ci : CartanInvolution rd)
    (mu : Δ.𝔥 →ₗ[R] R)
    (Lmu : Type uCatO) [AddCommGroup Lmu] [Module R Lmu]
    [LieRingModule 𝔤 Lmu] [LieModule R 𝔤 Lmu]
    (hLmuO : IsCategoryO Δ rd Lmu)
    (hIrr : LieModule.IsIrreducible R 𝔤 Lmu)
    (hHW : IsHighestWeightModule Δ Lmu mu) :
    ∃ (MmuDual : Type uCatO) (_ : AddCommGroup MmuDual) (_ : Module R MmuDual)
      (_ : LieRingModule 𝔤 MmuDual) (_ : LieModule R 𝔤 MmuDual)
      (hMmuDualO : IsCategoryO Δ rd MmuDual)
      (_ : IsContragredientVerma rd MmuDual mu hMmuDualO)
      (ι : Lmu →ₗ⁅R, 𝔤⁆ MmuDual),
      Function.Injective ι := by

  obtain ⟨Mmu, instACG_M, instMod_M, instLRM_M, instLM_M, ⟨hVM⟩⟩ :=
    verma_module_exists (R := R) (𝔤 := 𝔤) Δ mu
  letI := instACG_M; letI := instMod_M; letI := instLRM_M; letI := instLM_M

  have hMmuO : IsCategoryO Δ rd Mmu :=
    @verma_module_isCategoryO R _ 𝔤 _ _ Δ rd Mmu instACG_M instMod_M instLRM_M instLM_M mu hVM

  obtain ⟨η, _hη_gen⟩ := hVM.universal_map Lmu hHW.highestWeightVec
    hHW.cartan_action hHW.npos_action


  have hη_surj : Function.Surjective η := by


    rw [← LieModuleHom.range_eq_top]
    haveI : LieModule.IsIrreducible R 𝔤 Lmu := hIrr

    have h_mem : hHW.highestWeightVec ∈ η.range := by
      rw [LieModuleHom.mem_range]
      exact ⟨hVM.highestWeightVec, _hη_gen⟩
    haveI : Nontrivial ↥η.range := by
      refine ⟨⟨⟨hHW.highestWeightVec, h_mem⟩, 0, ?_⟩⟩
      intro h
      have := congr_arg Subtype.val h
      simp only [ZeroMemClass.coe_zero] at this
      exact hHW.hwv_ne_zero this
    exact LieSubmodule.eq_top_of_isIrreducible R 𝔤 Lmu η.range

  have dM : DualInO ci Mmu hMmuO := dualInO ci hMmuO
  have dL : DualInO ci Lmu hLmuO := dualInO ci hLmuO

  have hContra : IsContragredientVerma rd dM.Xdual mu dM.isCategoryO :=
    verma_dual_is_contragredient ci mu hVM hMmuO dM

  obtain ⟨fdual, hfdual_surj_inj, _⟩ :=
    duality_functor_contravariant ci hMmuO hLmuO η dM dL
  have hfdual_inj : Function.Injective fdual := hfdual_surj_inj hη_surj

  obtain ⟨_, _, iso_L_to_Ldual, hiso_bij⟩ :=
    simple_module_self_dual ci mu hLmuO hIrr hHW dL

  refine ⟨dM.Xdual, dM.instAddCommGroup, dM.instModule,
         dM.instLieRingModule, dM.instLieModule,
         dM.isCategoryO, hContra,
         LieModuleHom.comp fdual iso_L_to_Ldual,
         hfdual_inj.comp hiso_bij.1⟩

theorem CategoryO.nontrivial_has_hom_to_contragredient_verma_aux
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (ci : CartanInvolution rd)
    {K : Type uCatO} [AddCommGroup K] [Module R K]
    [LieRingModule 𝔤 K] [LieModule R 𝔤 K]
    (hKO : IsCategoryO Δ rd K) [Nontrivial K] :
    ∃ (mu : Δ.𝔥 →ₗ[R] R)

      (Lmu : Type uCatO) (_ : AddCommGroup Lmu) (_ : Module R Lmu)
      (_ : LieRingModule 𝔤 Lmu) (_ : LieModule R 𝔤 Lmu)

      (MmuDual : Type uCatO) (_ : AddCommGroup MmuDual) (_ : Module R MmuDual)
      (_ : LieRingModule 𝔤 MmuDual) (_ : LieModule R 𝔤 MmuDual)
      (hMmuDualO : IsCategoryO Δ rd MmuDual)
      (_ : IsContragredientVerma rd MmuDual mu hMmuDualO)

      (q : K →ₗ⁅R, 𝔤⁆ Lmu)
      (ι : Lmu →ₗ⁅R, 𝔤⁆ MmuDual),

      Function.Surjective q ∧

      Function.Injective ι ∧

      q ≠ 0 := by

  obtain ⟨mu, Lmu, instACG_L, instMod_L, instLRM_L, instLM_L, hLmuO,
          hIrr, hHW, q, hq_surj, hq_ne⟩ :=
    CategoryO.has_simple_quotient hKO

  obtain ⟨MmuDual, instACG_M, instMod_M, instLRM_M, instLM_M,
          hMmuDualO, hContra, ι, hι_inj⟩ :=
    CategoryO.simple_embeds_in_contragredient_verma ci mu Lmu hLmuO hIrr hHW

  exact ⟨mu, Lmu, instACG_L, instMod_L, instLRM_L, instLM_L,
         MmuDual, instACG_M, instMod_M, instLRM_M, instLM_M,
         hMmuDualO, hContra, q, ι, hq_surj, hι_inj, hq_ne⟩

theorem CategoryO.nonzero_admits_hom_to_contragredient_verma
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (ci : CartanInvolution rd)
    {K : Type uCatO} [AddCommGroup K] [Module R K]
    [LieRingModule 𝔤 K] [LieModule R 𝔤 K]
    (hKO : IsCategoryO Δ rd K) [Nontrivial K] :
    ∃ (mu : Δ.𝔥 →ₗ[R] R)
      (MmuDual : Type uCatO) (_ : AddCommGroup MmuDual) (_ : Module R MmuDual)
      (_ : LieRingModule 𝔤 MmuDual) (_ : LieModule R 𝔤 MmuDual)
      (hMmuDualO : IsCategoryO Δ rd MmuDual)
      (_ : IsContragredientVerma rd MmuDual mu hMmuDualO)
      (f : K →ₗ⁅R, 𝔤⁆ MmuDual), f ≠ 0 := by

  obtain ⟨mu, Lmu, instACG, instMod, instLRM, instLM,
         MmuDual, instACG', instMod', instLRM', instLM',
         hMmuDualO, hContra,
         q, ι, hq_surj, hι_inj, hq_ne⟩ :=
    CategoryO.nontrivial_has_hom_to_contragredient_verma_aux ci hKO


  refine ⟨mu, MmuDual, instACG', instMod', instLRM', instLM', hMmuDualO, hContra,
         ι.comp q, ?_⟩

  intro h_zero
  apply hq_ne
  ext k

  have h1 : ι (q k) = 0 := by
    have := LieModuleHom.congr_fun h_zero k
    simpa using this
  have h2 : ι (q k) = ι 0 := by rw [h1, map_zero]
  exact hι_inj h2

theorem finite_length_hom_vanishing_implies_zero
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (ci : CartanInvolution rd)
    {K : Type uCatO} [AddCommGroup K] [Module R K]
    [LieRingModule 𝔤 K] [LieModule R 𝔤 K]
    (hKO : IsCategoryO Δ rd K)
    (hHomVanish : ∀ (mu : Δ.𝔥 →ₗ[R] R)
      (MmuDual : Type uCatO) [AddCommGroup MmuDual] [Module R MmuDual]
      [LieRingModule 𝔤 MmuDual] [LieModule R 𝔤 MmuDual]
      (hMmuDualO : IsCategoryO Δ rd MmuDual)
      (_ : IsContragredientVerma rd MmuDual mu hMmuDualO),
      ∀ (f : K →ₗ⁅R, 𝔤⁆ MmuDual), f = 0) :
    ∀ (k : K), k = 0 := by

  by_contra h
  push Not at h

  obtain ⟨k, hk⟩ := h
  haveI : Nontrivial K := ⟨⟨k, 0, hk⟩⟩

  obtain ⟨mu, MmuDual, inst1, inst2, inst3, inst4, hMmuDualO, hContra, f, hf_ne⟩ :=
    CategoryO.nonzero_admits_hom_to_contragredient_verma ci hKO

  exact hf_ne (@hHomVanish mu MmuDual inst1 inst2 inst3 inst4 hMmuDualO hContra f)

theorem lemma_20_4_kernel_zero
    {R : Type*} [Field R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {rd : PositiveRootData Δ}
    (ci : CartanInvolution rd)
    {wg : WeylGroupData Δ}
    {E : Type uCatO} [AddCommGroup E] [Module R E]
    [LieRingModule 𝔤 E] [LieModule R 𝔤 E]
    [Module.Finite R E] [LieModule.IsTrivial 𝔤 E]
    {Mlam : Type uCatO} [AddCommGroup Mlam] [Module R Mlam]
    [LieRingModule 𝔤 Mlam] [LieModule R 𝔤 Mlam]
    (hMlamO : IsCategoryO Δ rd Mlam)
    (lam : Δ.𝔥 →ₗ[R] R)
    (hMlam_verma : IsVermaModule Δ Mlam lam)
    {K : Type uCatO} [AddCommGroup K] [Module R K]
    [LieRingModule 𝔤 K] [LieModule R 𝔤 K]
    (hKO : IsCategoryO Δ rd K)
    {Z : Type uCatO} [AddCommGroup Z] [Module R Z]
    [LieRingModule 𝔤 Z] [LieModule R 𝔤 Z]
    (hZO : IsCategoryO Δ rd Z)
    (i : K →ₗ⁅R, 𝔤⁆ (TensorProduct R E Mlam))
    (hi : Function.Injective i)
    (p : (TensorProduct R E Mlam) →ₗ⁅R, 𝔤⁆ Z)
    (hp : Function.Surjective p)
    (hexact : ∀ (m : TensorProduct R E Mlam), p m = 0 ↔ ∃ k : K, i k = m)
    (hK_lam : WeightSpace Δ K lam = ⊥)
    (hExtZ : ∀ (mu : Δ.𝔥 →ₗ[R] R)
      (MmuDual : Type uCatO) [AddCommGroup MmuDual] [Module R MmuDual]
      [LieRingModule 𝔤 MmuDual] [LieModule R 𝔤 MmuDual]
      (hMmuDualO : IsCategoryO Δ rd MmuDual)
      (_ : IsContragredientVerma rd MmuDual mu hMmuDualO)
      (E' : Type uCatO) [AddCommGroup E'] [Module R E']
      [LieRingModule 𝔤 E'] [LieModule R 𝔤 E']
      (_ : IsCategoryO Δ rd E')
      (j : MmuDual →ₗ⁅R, 𝔤⁆ E') (_ : Function.Injective j)
      (q : E' →ₗ⁅R, 𝔤⁆ Z) (_ : Function.Surjective q),
      ∃ (s : Z →ₗ⁅R, 𝔤⁆ E'), ∀ z, q (s z) = z) :
    ∀ (k : K), k = 0 := by


  have step1_hom_vanishing_ne : ∀ (mu : Δ.𝔥 →ₗ[R] R),
      mu ≠ lam →
      ∀ (MmuDual : Type uCatO) [inst1 : AddCommGroup MmuDual] [inst2 : Module R MmuDual]
        [inst3 : LieRingModule 𝔤 MmuDual] [inst4 : LieModule R 𝔤 MmuDual]
        (hMmuDualO : IsCategoryO Δ rd MmuDual)
        (_ : IsContragredientVerma rd MmuDual mu hMmuDualO),
        ∀ (f : K →ₗ⁅R, 𝔤⁆ MmuDual), f = 0 := by

    intro mu hmu MmuDual inst1 inst2 inst3 inst4 hMmuDualO hContra f
    exact les_lemma_20_1_hom_vanishing_ne hMlamO lam hMlam_verma hKO hZO i hi p hp
      hexact hExtZ mu hmu MmuDual hMmuDualO hContra f


  have step2_hom_vanishing_eq : ∀ (MlamDual : Type uCatO)
      [inst1 : AddCommGroup MlamDual] [inst2 : Module R MlamDual]
      [inst3 : LieRingModule 𝔤 MlamDual] [inst4 : LieModule R 𝔤 MlamDual]
      (hMlamDualO : IsCategoryO Δ rd MlamDual)
      (_ : IsContragredientVerma rd MlamDual lam hMlamDualO),
      ∀ (f : K →ₗ⁅R, 𝔤⁆ MlamDual), f = 0 := by

    intro MlamDual inst1 inst2 inst3 inst4 hMlamDualO hContra f
    exact socle_hom_vanishing_eq lam hKO hK_lam MlamDual hMlamDualO hContra f


  have step3_K_zero_of_hom_vanishing :
      (∀ (mu : Δ.𝔥 →ₗ[R] R)
        (MmuDual : Type uCatO) [inst1 : AddCommGroup MmuDual] [inst2 : Module R MmuDual]
        [inst3 : LieRingModule 𝔤 MmuDual] [inst4 : LieModule R 𝔤 MmuDual]
        (hMmuDualO : IsCategoryO Δ rd MmuDual)
        (_ : IsContragredientVerma rd MmuDual mu hMmuDualO),
        ∀ (f : K →ₗ⁅R, 𝔤⁆ MmuDual), f = 0) →
      ∀ (k : K), k = 0 := by

    intro hHomVanish
    exact finite_length_hom_vanishing_implies_zero ci hKO hHomVanish

  apply step3_K_zero_of_hom_vanishing
  intro mu MmuDual inst1 inst2 inst3 inst4 hMmuDualO hContra
  by_cases hmu : mu = lam
  · subst hmu
    exact step2_hom_vanishing_eq MmuDual hMmuDualO hContra
  · exact step1_hom_vanishing_ne mu hmu MmuDual hMmuDualO hContra

def cartanMatrixEntry
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R) : ℕ :=
  cartanMultiplicity rd wg lam mu

theorem cartan_standard_filtration_decomposition
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (S : Finset (Δ.𝔥 →ₗ[R] R))
    (hS : ∀ nu : Δ.𝔥 →ₗ[R] R, nu ∉ S →
      standardFiltrationMultiplicity rd wg lam nu = 0 ∨
      compositionMultiplicity rd wg nu mu = 0) :
    cartanMatrixEntry rd wg lam mu =
    S.sum (fun nu => standardFiltrationMultiplicity rd wg lam nu *
                     compositionMultiplicity rd wg nu mu) := by
  have hS' : ∀ nu : Δ.𝔥 →ₗ[R] R, nu ∉ S →
      compositionMultiplicity rd wg nu lam = 0 ∨
      compositionMultiplicity rd wg nu mu = 0 := by
    intro nu hnu
    have h := hS nu hnu
    rwa [bgg_reciprocity_raw rd wg lam nu] at h
  change cartanMultiplicity rd wg lam mu = _
  rw [corollary_20_7 rd wg lam mu S hS']
  congr 1
  ext nu
  rw [bgg_reciprocity_raw rd wg lam nu]

theorem cartan_matrix_factorization
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (S : Finset (Δ.𝔥 →ₗ[R] R))
    (hS : ∀ nu : Δ.𝔥 →ₗ[R] R, nu ∉ S →
      compositionMultiplicity rd wg nu lam = 0 ∨
      compositionMultiplicity rd wg nu mu = 0) :
    cartanMatrixEntry rd wg lam mu =
    S.sum (fun nu => compositionMultiplicity rd wg nu lam *
                     compositionMultiplicity rd wg nu mu) := by
  have hS' : ∀ nu : Δ.𝔥 →ₗ[R] R, nu ∉ S →
      standardFiltrationMultiplicity rd wg lam nu = 0 ∨
      compositionMultiplicity rd wg nu mu = 0 := by
    intro nu hnu
    have h := hS nu hnu
    rwa [← bgg_reciprocity_raw rd wg lam nu] at h
  rw [cartan_standard_filtration_decomposition rd wg lam mu S hS']
  congr 1
  ext nu
  rw [bgg_reciprocity_raw rd wg lam nu]

theorem bgg_theorem
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (hcomp : compositionMultiplicity rd wg lam mu ≠ 0) :
    BruhatLE rd mu lam :=
  bgg_theorem_bruhat_order R 𝔤 Δ rd wg lam mu hcomp

end
