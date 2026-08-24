/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.SL2Representations

theorem SL2IrredGKModule.Realization.exists'
    (μ : SL2IrredGKModule)
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)) :
    Nonempty (SL2IrredGKModule.Realization μ 𝔤 K 𝔨 Ad) :=
  sl2IrredGKModule_realization_exists μ 𝔤 K 𝔨 Ad

noncomputable section

open Complex

theorem GKModule.isIrreducibleGKModule_of_iso
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    {K : Type*} [Group K]
    {𝔨 : LieSubalgebra ℂ 𝔤}
    {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    [LieRingModule 𝔤 W] [LieModule ℂ 𝔤 W]
    {M : GKModule 𝔤 K 𝔨 Ad V} {N : GKModule 𝔤 K 𝔨 Ad W}
    (hiso : M.IsIsomorphicGK N) (hirr : M.IsIrreducibleGKModule) :
    N.IsIrreducibleGKModule := by
  obtain ⟨φ, hφ⟩ := hiso
  let e := LinearEquiv.ofBijective φ.toLinearMap hφ
  intro U hU

  let U' := U.comap e.toLinearMap

  have hU' : M.IsSubmodule U' := by
    constructor
    ·
      intro X v (hv : e.toLinearMap v ∈ U)
      show e.toLinearMap ⁅X, v⁆ ∈ U
      rw [show e.toLinearMap ⁅X, v⁆ = φ.toLinearMap ⁅X, v⁆ from rfl, φ.lie_comm]
      exact hU.lie_invariant X (e.toLinearMap v) hv
    ·
      intro k v (hv : e.toLinearMap v ∈ U)
      show e.toLinearMap (M.σ k v) ∈ U
      rw [show e.toLinearMap (M.σ k v) = φ.toLinearMap (M.σ k v) from rfl, φ.group_comm]
      exact hU.group_invariant k (e.toLinearMap v) hv

  rcases hirr U' hU' with h | h
  ·
    left
    rw [Submodule.eq_bot_iff] at h ⊢
    intro w hw
    have hew : e.symm w ∈ U' := by
      change e.toLinearMap (e.symm w) ∈ U
      simp [hw]
    have h0 := h (e.symm w) hew
    have : w = 0 := by
      have : e (e.symm w) = e 0 := by rw [h0]
      simp at this
      exact this
    exact this
  ·
    right
    rw [Submodule.eq_top_iff'] at h ⊢
    intro w
    have : e.symm w ∈ U' := h (e.symm w)
    show w ∈ U
    have : e.toLinearMap (e.symm w) ∈ U := this
    rwa [show e.toLinearMap (e.symm w) = w from e.apply_symm_apply w] at this

def IsOddInteger (s : ℂ) : Prop := ∃ k : ℤ, s = 2 * (k : ℂ) + 1

def IsEvenInteger (s : ℂ) : Prop := ∃ k : ℤ, s = 2 * (k : ℂ)

inductive SL2SimpleModule where
  | finiteDim (m : ℕ)
  | discreteSeriesMinus (m : ℕ) (hm : m ≥ 1)
  | discreteSeriesPlus (m : ℕ) (hm : m ≥ 1)
  | principalSeriesEven (s : ℂ) (hs : ¬ IsOddInteger s)
  | principalSeriesOdd (s : ℂ) (hs : ¬ IsEvenInteger s)

namespace SL2SimpleModule

def kTypes : SL2SimpleModule → Set ℤ
  | finiteDim m => { n : ℤ | n.natAbs ≤ m ∧ (n : ℤ) % 2 = (m : ℤ) % 2 }
  | discreteSeriesMinus m _ => { n : ℤ | n ≥ (m : ℤ) ∧ (n - (m : ℤ)) % 2 = 0 }
  | discreteSeriesPlus m _ => { n : ℤ | n ≤ -(m : ℤ) ∧ (n + (m : ℤ)) % 2 = 0 }
  | principalSeriesEven _ _ => { n : ℤ | n % 2 = 0 }
  | principalSeriesOdd _ _ => { n : ℤ | n % 2 = 1 ∨ n % 2 = -1 }

def casimirEigenvalue : SL2SimpleModule → ℂ
  | finiteDim m => ((m : ℂ) * ((m : ℂ) + 2)) / 4
  | discreteSeriesMinus m _ => ((m : ℂ) * ((m : ℂ) - 2)) / 4
  | discreteSeriesPlus m _ => ((m : ℂ) * ((m : ℂ) - 2)) / 4
  | principalSeriesEven s _ => (s ^ 2 - 1) / 4
  | principalSeriesOdd s _ => (s ^ 2 - 1) / 4

def IsIsomorphic : SL2SimpleModule → SL2SimpleModule → Prop
  | finiteDim m₁, finiteDim m₂ => m₁ = m₂
  | discreteSeriesMinus m₁ _, discreteSeriesMinus m₂ _ => m₁ = m₂
  | discreteSeriesPlus m₁ _, discreteSeriesPlus m₂ _ => m₁ = m₂
  | principalSeriesEven s₁ _, principalSeriesEven s₂ _ => s₁ = s₂ ∨ s₁ = -s₂
  | principalSeriesOdd s₁ _, principalSeriesOdd s₂ _ => s₁ = s₂ ∨ s₁ = -s₂
  | _, _ => False

end SL2SimpleModule
open SL2SimpleModule

theorem sl2_classification_existence
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    [LieRingModule 𝔤 V] [LieModule ℂ 𝔤 V]
    (M : GKModule 𝔤 K 𝔨 Ad V)
    (M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V)
    (hirr : M.IsIrreducibleGKModule)
    (hadm : M.IsAdmissible) :
    ∃ (μ : SL2SimpleModule),
      ∃ (R : SL2IrredGKModule.Realization.{_, _, 0} (match μ with
        | .finiteDim m => .finiteDim m
        | .discreteSeriesMinus m _hm =>
          if h2 : m ≥ 2 then .discreteSeriesMinus m h2 else .limitDiscreteMinus
        | .discreteSeriesPlus m _hm =>
          if h2 : m ≥ 2 then .discreteSeriesPlus m h2 else .limitDiscretePlus
        | .principalSeriesEven s _ => .principalSeries s 0
        | .principalSeriesOdd s _ => .principalSeries s 1) 𝔤 K 𝔨 Ad),
        M.IsIsomorphicGK R.gkmod := by

  obtain ⟨μ₀, R₀, hiso₀⟩ := sl2_gk_classification 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm

  match μ₀ with
  | .finiteDim n =>
    exact ⟨.finiteDim n, R₀, hiso₀⟩
  | .principalSeries ν ε =>

    by_cases hε : ε = 0
    ·
      by_cases hν : IsOddInteger ν
      ·

        subst hε
        exact absurd (GKModule.isIrreducibleGKModule_of_iso hiso₀ hirr)
          (principalSeries_even_reducible ν hν R₀)
      ·
        subst hε
        exact ⟨.principalSeriesEven ν hν, R₀, hiso₀⟩
    ·
      have hε1 : ε = 1 := by
        have : ε = 0 ∨ ε = 1 := by
          fin_cases ε
          · left; rfl
          · right; rfl
        exact this.resolve_left hε
      by_cases hν : IsEvenInteger ν
      ·

        subst hε1
        exact absurd (GKModule.isIrreducibleGKModule_of_iso hiso₀ hirr)
          (principalSeries_odd_reducible ν hν R₀)

      ·
        subst hε1
        exact ⟨.principalSeriesOdd ν hν, R₀, hiso₀⟩
  | .discreteSeriesPlus n hn =>
    refine ⟨.discreteSeriesPlus n (by omega), ⟨R₀.W, R₀.gkmod, R₀.casimirScalar, ?_⟩, hiso₀⟩
    rw [R₀.casimir_eq]; simp [hn]
  | .discreteSeriesMinus n hn =>
    refine ⟨.discreteSeriesMinus n (by omega), ⟨R₀.W, R₀.gkmod, R₀.casimirScalar, ?_⟩, hiso₀⟩
    rw [R₀.casimir_eq]; simp [hn]
  | .limitDiscretePlus =>
    refine ⟨.discreteSeriesPlus 1 (by omega), ⟨R₀.W, R₀.gkmod, R₀.casimirScalar, ?_⟩, hiso₀⟩
    rw [R₀.casimir_eq]; simp [show ¬ (1 : ℕ) ≥ 2 from by omega]
  | .limitDiscreteMinus =>
    refine ⟨.discreteSeriesMinus 1 (by omega), ⟨R₀.W, R₀.gkmod, R₀.casimirScalar, ?_⟩, hiso₀⟩
    rw [R₀.casimir_eq]; simp [show ¬ (1 : ℕ) ≥ 2 from by omega]

theorem sl2_principalSeriesEven_neg_iso
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (s : ℂ) (hs : ¬ IsOddInteger s) (hs' : ¬ IsOddInteger (-s))
    (R₁ : SL2IrredGKModule.Realization (.principalSeries s 0) 𝔤 K 𝔨 Ad)
    (R₂ : SL2IrredGKModule.Realization (.principalSeries (-s) 0) 𝔤 K 𝔨 Ad) :
    R₁.gkmod.IsIsomorphicGK R₂.gkmod :=
  principalSeries_neg_iso s 0 R₁ R₂

theorem sl2_principalSeriesOdd_neg_iso
    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (s : ℂ) (hs : ¬ IsEvenInteger s) (hs' : ¬ IsEvenInteger (-s))
    (R₁ : SL2IrredGKModule.Realization (.principalSeries s 1) 𝔤 K 𝔨 Ad)
    (R₂ : SL2IrredGKModule.Realization (.principalSeries (-s) 1) 𝔤 K 𝔨 Ad) :
    R₁.gkmod.IsIsomorphicGK R₂.gkmod :=
  principalSeries_neg_iso s 1 R₁ R₂

def SL2SimpleModule.toIrredGK : SL2SimpleModule → SL2IrredGKModule
  | .finiteDim m => .finiteDim m
  | .discreteSeriesMinus m _ =>
    if h2 : m ≥ 2 then .discreteSeriesMinus m h2 else .limitDiscreteMinus
  | .discreteSeriesPlus m _ =>
    if h2 : m ≥ 2 then .discreteSeriesPlus m h2 else .limitDiscretePlus
  | .principalSeriesEven s _ => .principalSeries s 0
  | .principalSeriesOdd s _ => .principalSeries s 1

theorem sl2_classification_uniqueness

    (𝔤 : Type*) [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
    (K : Type*) [Group K]
    (𝔨 : LieSubalgebra ℂ 𝔤)
    (Ad : K →* (𝔤 →ₗ[ℂ] 𝔤))
    (μ ν : SL2SimpleModule)
    (Rμ : SL2IrredGKModule.Realization (match μ with
        | .finiteDim m => .finiteDim m
        | .discreteSeriesMinus m hm =>
          if h2 : m ≥ 2 then .discreteSeriesMinus m h2 else .limitDiscreteMinus
        | .discreteSeriesPlus m hm =>
          if h2 : m ≥ 2 then .discreteSeriesPlus m h2 else .limitDiscretePlus
        | .principalSeriesEven s _ => .principalSeries s 0
        | .principalSeriesOdd s _ => .principalSeries s 1) 𝔤 K 𝔨 Ad)
    (Rν : SL2IrredGKModule.Realization (match ν with
        | .finiteDim m => .finiteDim m
        | .discreteSeriesMinus m hm =>
          if h2 : m ≥ 2 then .discreteSeriesMinus m h2 else .limitDiscreteMinus
        | .discreteSeriesPlus m hm =>
          if h2 : m ≥ 2 then .discreteSeriesPlus m h2 else .limitDiscretePlus
        | .principalSeriesEven s _ => .principalSeries s 0
        | .principalSeriesOdd s _ => .principalSeries s 1) 𝔤 K 𝔨 Ad)
    (hiso : Rμ.gkmod.IsIsomorphicGK Rν.gkmod) :
    μ.IsIsomorphic ν := by

  have hmatch := sl2_iso_implies_label_match μ.toIrredGK ν.toIrredGK Rμ Rν hiso
  rcases hmatch with heq | ⟨s', ε', hμ_ps, hν_ps⟩
  ·

    cases μ with
    | finiteDim m =>
      cases ν with
      | finiteDim m' => simp [toIrredGK] at heq; exact heq
      | discreteSeriesMinus m' hm' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | discreteSeriesPlus m' hm' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | principalSeriesEven s' hs' => simp [toIrredGK] at heq
      | principalSeriesOdd s' hs' => simp [toIrredGK] at heq
    | discreteSeriesMinus m hm =>
      cases ν with
      | finiteDim m' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | discreteSeriesMinus m' hm' =>
        simp only [toIrredGK] at heq; split_ifs at heq with h1 h2 <;>
          (simp only [IsIsomorphic]; try simp_all [SL2IrredGKModule.noConfusion]) <;> omega
      | discreteSeriesPlus m' hm' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | principalSeriesEven s' hs' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | principalSeriesOdd s' hs' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
    | discreteSeriesPlus m hm =>
      cases ν with
      | finiteDim m' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | discreteSeriesMinus m' hm' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | discreteSeriesPlus m' hm' =>
        simp only [toIrredGK] at heq; split_ifs at heq with h1 h2 <;>
          (simp only [IsIsomorphic]; try simp_all [SL2IrredGKModule.noConfusion]) <;> omega
      | principalSeriesEven s' hs' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | principalSeriesOdd s' hs' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
    | principalSeriesEven sμ hsμ =>
      cases ν with
      | finiteDim m' => simp [toIrredGK] at heq
      | discreteSeriesMinus m' hm' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | discreteSeriesPlus m' hm' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | principalSeriesEven s' hs' =>
        simp only [toIrredGK] at heq
        simp only [IsIsomorphic]
        left; exact (SL2IrredGKModule.principalSeries.inj heq).1
      | principalSeriesOdd s' hs' => simp [toIrredGK] at heq
    | principalSeriesOdd sμ hsμ =>
      cases ν with
      | finiteDim m' => simp [toIrredGK] at heq
      | discreteSeriesMinus m' hm' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | discreteSeriesPlus m' hm' =>
        simp [toIrredGK] at heq; split_ifs at heq <;> simp_all [SL2IrredGKModule.noConfusion]
      | principalSeriesEven s' hs' => simp [toIrredGK] at heq
      | principalSeriesOdd s' hs' =>
        simp only [toIrredGK] at heq
        simp only [IsIsomorphic]
        left; exact (SL2IrredGKModule.principalSeries.inj heq).1
  ·
    cases μ with
    | finiteDim m => simp [toIrredGK] at hμ_ps
    | discreteSeriesMinus m hm =>
      simp [toIrredGK] at hμ_ps; split_ifs at hμ_ps <;> simp_all [SL2IrredGKModule.noConfusion]
    | discreteSeriesPlus m hm =>
      simp [toIrredGK] at hμ_ps; split_ifs at hμ_ps <;> simp_all [SL2IrredGKModule.noConfusion]
    | principalSeriesEven sμ hsμ =>
      cases ν with
      | finiteDim m' => simp [toIrredGK] at hν_ps
      | discreteSeriesMinus m' hm' =>
        simp [toIrredGK] at hν_ps; split_ifs at hν_ps <;> simp_all [SL2IrredGKModule.noConfusion]
      | discreteSeriesPlus m' hm' =>
        simp [toIrredGK] at hν_ps; split_ifs at hν_ps <;> simp_all [SL2IrredGKModule.noConfusion]
      | principalSeriesEven sν hsν =>
        simp only [toIrredGK] at hμ_ps hν_ps
        simp only [IsIsomorphic]
        obtain ⟨rfl, rfl⟩ := SL2IrredGKModule.principalSeries.inj hμ_ps
        obtain ⟨h_neg, _⟩ := SL2IrredGKModule.principalSeries.inj hν_ps
        right; rw [h_neg]; ring
      | principalSeriesOdd sν hsν =>
        simp only [toIrredGK] at hμ_ps hν_ps
        have h1 := SL2IrredGKModule.principalSeries.inj hμ_ps
        have h2 := SL2IrredGKModule.principalSeries.inj hν_ps
        exact absurd (h1.2.trans h2.2.symm) (by decide)
    | principalSeriesOdd sμ hsμ =>
      cases ν with
      | finiteDim m' => simp [toIrredGK] at hν_ps
      | discreteSeriesMinus m' hm' =>
        simp [toIrredGK] at hν_ps; split_ifs at hν_ps <;> simp_all [SL2IrredGKModule.noConfusion]
      | discreteSeriesPlus m' hm' =>
        simp [toIrredGK] at hν_ps; split_ifs at hν_ps <;> simp_all [SL2IrredGKModule.noConfusion]
      | principalSeriesEven sν hsν =>
        simp only [toIrredGK] at hμ_ps hν_ps
        have h1 := SL2IrredGKModule.principalSeries.inj hμ_ps
        have h2 := SL2IrredGKModule.principalSeries.inj hν_ps
        exact absurd (h1.2.trans h2.2.symm) (by decide)
      | principalSeriesOdd sν hsν =>
        simp only [toIrredGK] at hμ_ps hν_ps
        simp only [IsIsomorphic]
        obtain ⟨rfl, rfl⟩ := SL2IrredGKModule.principalSeries.inj hμ_ps
        obtain ⟨h_neg, _⟩ := SL2IrredGKModule.principalSeries.inj hν_ps
        right; rw [h_neg]; ring

end
