/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Atlas.DifferentialGeometry.code.Manifolds
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Convex
import Atlas.DifferentialGeometry.code.Intrinsic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.SetTheory.Cardinal.Finite
import Atlas.DifferentialGeometry.code.GaussMap

open MeasureTheory intervalIntegral Hypersurface Finset
open scoped InnerProductSpace BigOperators

noncomputable section

namespace Geodesics

def IsGeodesic {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hM : IsHypersurface M)
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) : Prop :=
  ContDiff ℝ ⊤ γ ∧
  (∀ t, γ t ∈ M) ∧
  (∀ t, ∀ ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
    IsLocalDefiningFunction ψ M (γ t) →
    ∀ v ∈ Hypersurface.tangentSpace ψ (γ t), ⟪deriv (deriv γ) t, v⟫_ℝ = 0)

lemma deriv_mem_tangentSpace {n : ℕ} {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))}
    {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hsmooth : ContDiff ℝ ⊤ γ) (hM : ∀ t, γ t ∈ M)
    {t : ℝ} (hψ : IsLocalDefiningFunction ψ M (γ t)) :
    deriv γ t ∈ Hypersurface.tangentSpace ψ (γ t) := by
  rw [mem_tangentSpace_iff]
  obtain ⟨U, hUo, hγtU, _, hψM⟩ := hψ.exists_open_nhd
  have hγcont : Continuous γ := hsmooth.continuous
  have hPreOpen : IsOpen (γ ⁻¹' U) := hγcont.isOpen_preimage U hUo
  have htInPre : t ∈ γ ⁻¹' U := hγtU

  have hconst : ∀ᶠ s in nhds t, ψ (γ s) = 0 :=
    hPreOpen.eventually_mem htInPre |>.mono fun s hs => (hψM (γ s) hs).mp (hM s)

  have hderivComp : deriv (fun s => ψ (γ s)) t = 0 := by
    have : (fun s => ψ (γ s)) =ᶠ[nhds t] (fun _ => (0 : ℝ)) :=
      hconst.mono (fun s hs => by simp [hs])
    rw [Filter.EventuallyEq.deriv_eq this]
    simp

  have hγDiff : DifferentiableAt ℝ γ t :=
    (hsmooth.differentiable (by simp)).differentiableAt
  have hψDiff : DifferentiableAt ℝ ψ (γ t) := hψ.differentiableAt
  have hchain : HasDerivAt (fun s => ψ (γ s)) (fderiv ℝ ψ (γ t) (deriv γ t)) t :=
    (hψDiff.hasFDerivAt).comp_hasDerivAt t (hγDiff.hasDerivAt)
  linarith [hchain.deriv]

theorem geodesic_constant_speed {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hHyp : IsHypersurface M)
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (hγ : IsGeodesic M hHyp γ) :
    ∃ c : ℝ, ∀ t, ‖deriv γ t‖ = c := by
  obtain ⟨hsmooth, hM, hperp⟩ := hγ

  have h_inner_zero : ∀ t, ⟪deriv (deriv γ) t, deriv γ t⟫_ℝ = 0 := by
    intro t

    obtain ⟨ψ, hψ⟩ := hHyp (γ t) (hM t)
    exact hperp t ψ hψ (deriv γ t) (deriv_mem_tangentSpace hsmooth hM hψ)

  have hγ2 : ContDiff ℝ 2 γ := hsmooth.of_le le_top
  have hderiv_diff : Differentiable ℝ (deriv γ) := hγ2.differentiable_deriv_two
  have hderiv_diffAt : ∀ t, DifferentiableAt ℝ (deriv γ) t :=
    fun t => hderiv_diff.differentiableAt

  have h_norm_sq_deriv : ∀ t, deriv (fun t => ⟪deriv γ t, deriv γ t⟫_ℝ) t = 0 := by
    intro t
    rw [deriv_inner_apply ℝ (hderiv_diffAt t) (hderiv_diffAt t)]

    have h1 := real_inner_comm (deriv γ t) (deriv (deriv γ) t)
    linarith [h_inner_zero t]

  have h_norm_sq_diff : Differentiable ℝ (fun t => ⟪deriv γ t, deriv γ t⟫_ℝ) :=
    fun t => (hderiv_diffAt t).inner ℝ (hderiv_diffAt t)

  have h_norm_sq_const : ∀ s t, ⟪deriv γ s, deriv γ s⟫_ℝ = ⟪deriv γ t, deriv γ t⟫_ℝ :=
    is_const_of_deriv_eq_zero h_norm_sq_diff h_norm_sq_deriv

  have h_norm_const : ∀ s t, ‖deriv γ s‖ = ‖deriv γ t‖ := by
    intro s t
    have hsq : ‖deriv γ s‖ ^ 2 = ‖deriv γ t‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
      exact h_norm_sq_const s t
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  exact ⟨‖deriv γ 0‖, fun t => h_norm_const t 0⟩

def energy {n : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖deriv γ t‖ ^ 2

structure SmoothVariation {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (a b : ℝ) where
  Γ : ℝ → ℝ → EuclideanSpace ℝ (Fin (n + 1))
  smooth : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => Γ p.1 p.2)
  base : ∀ t, Γ 0 t = γ t
  left_fixed : ∀ s, Γ s a = γ a
  right_fixed : ∀ s, Γ s b = γ b
  maps_to : ∀ s t, Γ s t ∈ M

def firstVariationEnergy {n : ℕ} {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))} {a b : ℝ}
    (V : SmoothVariation M γ a b) : ℝ :=
  deriv (fun s => energy (V.Γ s) a b) 0

def variationField {n : ℕ} {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))} {a b : ℝ}
    (V : SmoothVariation M γ a b) (t : ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  deriv (fun s => V.Γ s t) 0

lemma variationField_mem_tangentSpace {n : ℕ}
    {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))} {a b : ℝ}
    (V : SmoothVariation M γ a b)
    {ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    {t : ℝ} (hψ : IsLocalDefiningFunction ψ M (γ t)) :
    variationField V t ∈ Hypersurface.tangentSpace ψ (γ t) := by
  rw [mem_tangentSpace_iff]

  obtain ⟨U, hUo, hγtU, _, hψM⟩ := hψ.exists_open_nhd

  have hΓcont : Continuous (fun s => V.Γ s t) := by
    have : (fun s => V.Γ s t) = (fun p : ℝ × ℝ => V.Γ p.1 p.2) ∘ (fun s => (s, t)) := by
      ext s; simp
    rw [this]
    exact V.smooth.continuous.comp (Continuous.prodMk_left t)


  have hbase : V.Γ 0 t ∈ U := by rw [V.base t]; exact hγtU
  have hPreOpen : IsOpen ((fun s => V.Γ s t) ⁻¹' U) := hΓcont.isOpen_preimage U hUo
  have h0InPre : (0 : ℝ) ∈ (fun s => V.Γ s t) ⁻¹' U := hbase

  have hconst : ∀ᶠ s in nhds (0 : ℝ), ψ (V.Γ s t) = 0 :=
    hPreOpen.eventually_mem h0InPre |>.mono fun s hs => (hψM (V.Γ s t) hs).mp (V.maps_to s t)

  have hderivComp : deriv (fun s => ψ (V.Γ s t)) 0 = 0 := by
    have : (fun s => ψ (V.Γ s t)) =ᶠ[nhds 0] (fun _ => (0 : ℝ)) :=
      hconst.mono (fun s hs => by simp [hs])
    rw [Filter.EventuallyEq.deriv_eq this]
    simp

  have hΓDiff : DifferentiableAt ℝ (fun s => V.Γ s t) 0 := by
    have : (fun s => V.Γ s t) = (fun p : ℝ × ℝ => V.Γ p.1 p.2) ∘ (fun s => (s, t)) := by
      ext s; simp
    rw [this]
    exact (V.smooth.differentiable (by simp)).differentiableAt.comp _
      (Differentiable.prodMk differentiable_id (differentiable_const t)).differentiableAt

  have hψDiff : DifferentiableAt ℝ ψ (V.Γ 0 t) := by
    rw [V.base t]; exact hψ.differentiableAt
  have hchain : HasDerivAt (fun s => ψ (V.Γ s t))
      (fderiv ℝ ψ (V.Γ 0 t) (deriv (fun s => V.Γ s t) 0)) 0 :=
    (hψDiff.hasFDerivAt).comp_hasDerivAt 0 (hΓDiff.hasDerivAt)
  have := hchain.deriv
  rw [V.base t] at this
  change fderiv ℝ ψ (γ t) (variationField V t) = 0
  change deriv (fun s => ψ (V.Γ s t)) 0 = (fderiv ℝ ψ (γ t)) (variationField V t) at this
  linarith [hderivComp, this]

theorem first_variation_formula
    {n : ℕ}
    {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))} {a b : ℝ}
    (V : SmoothVariation M γ a b)
    (hγ_smooth : ContDiff ℝ ⊤ γ) :
    firstVariationEnergy V = -2 * ∫ t in a..b, ⟪deriv (deriv γ) t, variationField V t⟫_ℝ := by sorry

theorem critical_energy_implies_geodesic
    {n : ℕ}
    (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hM : IsHypersurface M)
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (a b : ℝ) (hab : a < b)
    (hγ_smooth : ContDiff ℝ ⊤ γ) (hγ_in : ∀ t, γ t ∈ M)
    (hcrit : ∀ V : SmoothVariation M γ a b, firstVariationEnergy V = 0) :
    IsGeodesic M hM γ := by sorry

theorem geodesic_iff_critical_energy
    {n : ℕ}
    (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hM : IsHypersurface M)
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (a b : ℝ) (hab : a < b)
    (hγ_smooth : ContDiff ℝ ⊤ γ) (hγ_in : ∀ t, γ t ∈ M) :
    IsGeodesic M hM γ ↔
    ∀ V : SmoothVariation M γ a b, firstVariationEnergy V = 0 := by
  constructor
  ·
    intro hgeo V
    obtain ⟨_, _, hperp⟩ := hgeo
    rw [first_variation_formula V hγ_smooth]

    have h_integrand_zero : ∀ t, ⟪deriv (deriv γ) t, variationField V t⟫_ℝ = 0 := by
      intro t
      obtain ⟨ψ, hψ⟩ := hM (γ t) (hγ_in t)
      exact hperp t ψ hψ (variationField V t) (variationField_mem_tangentSpace V hψ)
    simp [h_integrand_zero]
  ·


    intro hcrit
    exact critical_energy_implies_geodesic M hM γ a b hab hγ_smooth hγ_in hcrit

def IsEnergyMinimizer {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (a b : ℝ) : Prop :=
  ∀ V : SmoothVariation M γ a b, ∀ s : ℝ, energy γ a b ≤ energy (V.Γ s) a b

theorem energy_differentiableAt_variation
    {n : ℕ}
    {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))} {a b : ℝ}
    (V : SmoothVariation M γ a b) :
    DifferentiableAt ℝ (fun s => energy (V.Γ s) a b) 0 := by sorry

theorem geodesic_of_energy_minimizer
    {n : ℕ}
    (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hM : IsHypersurface M)
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (a b : ℝ) (hab : a < b)
    (hγ_smooth : ContDiff ℝ ⊤ γ) (hγ_in : ∀ t, γ t ∈ M)
    (hmin : IsEnergyMinimizer M γ a b) :
    IsGeodesic M hM γ := by
  rw [geodesic_iff_critical_energy M hM γ a b hab hγ_smooth hγ_in]
  intro V

  have hfun_eq : V.Γ 0 = γ := funext V.base
  have hbase_eq : energy (V.Γ 0) a b = energy γ a b := by
    unfold energy; rw [hfun_eq]
  have hmin_s : IsLocalMin (fun s => energy (V.Γ s) a b) 0 :=
    Filter.Eventually.of_forall (fun s => by
      simp only
      linarith [hmin V s, hbase_eq])

  have hdiff := energy_differentiableAt_variation V
  exact IsLocalMin.hasDerivAt_eq_zero hmin_s hdiff.hasDerivAt

def IsGeodesicOn {n : ℕ} (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hM : IsHypersurface M)
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (I : Set ℝ) : Prop :=
  ContDiff ℝ ⊤ γ ∧
  (∀ t ∈ I, γ t ∈ M) ∧
  (∀ t ∈ I, ∀ ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
    IsLocalDefiningFunction ψ M (γ t) →
    ∀ v ∈ Hypersurface.tangentSpace ψ (γ t), ⟪deriv (deriv γ) t, v⟫_ℝ = 0)

theorem geodesic_local_agreement
    {n : ℕ}
    {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {hM : IsHypersurface M}
    {γ γ' : ℝ → EuclideanSpace ℝ (Fin (n + 1))}
    (hγ : IsGeodesic M hM γ) (hγ' : IsGeodesic M hM γ')
    (t₀ : ℝ) (h_pos : γ t₀ = γ' t₀) (h_vel : deriv γ t₀ = deriv γ' t₀) :
    ∀ᶠ t in nhds t₀, γ t = γ' t ∧ deriv γ t = deriv γ' t := by sorry

theorem geodesic_uniqueness
    {n : ℕ}
    (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hM : IsHypersurface M)
    (γ γ' : ℝ → EuclideanSpace ℝ (Fin (n + 1)))
    (hγ : IsGeodesic M hM γ) (hγ' : IsGeodesic M hM γ')
    (h_pos : γ 0 = γ' 0)
    (h_vel : deriv γ 0 = deriv γ' 0) :
    ∀ t, γ t = γ' t := by

  set S : Set ℝ := {t | γ t = γ' t ∧ deriv γ t = deriv γ' t}

  have h0S : (0 : ℝ) ∈ S := ⟨h_pos, h_vel⟩

  have hγ_smooth : ContDiff ℝ ⊤ γ := hγ.1
  have hγ'_smooth : ContDiff ℝ ⊤ γ' := hγ'.1

  have hS_closed : IsClosed S := by
    have h1 : IsClosed {t | γ t = γ' t} :=
      isClosed_eq hγ_smooth.continuous hγ'_smooth.continuous
    have h2 : IsClosed {t | deriv γ t = deriv γ' t} :=
      isClosed_eq (hγ_smooth.continuous_deriv le_top) (hγ'_smooth.continuous_deriv le_top)
    exact h1.inter h2

  have hS_open : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t₀ ht₀
    exact geodesic_local_agreement hγ hγ' t₀ ht₀.1 ht₀.2

  have hS_clopen : IsClopen S := ⟨hS_closed, hS_open⟩
  have hS_univ : S = Set.univ := by
    rcases isClopen_iff.mp hS_clopen with h | h
    · exact absurd h (Set.nonempty_iff_ne_empty.mp ⟨0, h0S⟩)
    · exact h

  intro t
  have ht : t ∈ S := hS_univ ▸ Set.mem_univ t
  exact ht.1

theorem geodesic_existence
    {n : ℕ}
    (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hM : IsHypersurface M)
    (y : EuclideanSpace ℝ (Fin (n + 1))) (hy : y ∈ M)
    (ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hψ : IsLocalDefiningFunction ψ M y)
    (Y : EuclideanSpace ℝ (Fin (n + 1))) (hY : Y ∈ Hypersurface.tangentSpace ψ y) :
    ∃ (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))), IsGeodesic M hM γ ∧ γ 0 = y ∧ deriv γ 0 = Y := by sorry

theorem path_length_eq_distance_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [StrictConvexSpace ℝ E]
    (γ : ℝ → E) (a b : ℝ) (hab : a < b) (hγ : ContDiff ℝ ⊤ γ) :
    ∫ t in a..b, ‖deriv γ t‖ = ‖γ b - γ a‖ ↔
      ∀ t ∈ Set.Icc a b, ∃ c : ℝ, 0 ≤ c ∧ deriv γ t = c • (γ b - γ a) := by sorry

def SatisfiesGeodesicEquation {n : ℕ} (patch : HypersurfacePatch n)
    (c : ℝ → Fin n → ℝ) : Prop :=
  ContDiff ℝ ⊤ c ∧
  (∀ t, c t ∈ patch.domain) ∧
  (∀ t, ∀ k : Fin n,
    (deriv (deriv c) t) k +
      ∑ i : Fin n, ∑ j : Fin n,
        ChristoffelSymbols.christoffelSymbol patch (c t) i j k *
          (deriv c t i) * (deriv c t j) = 0)

theorem patch_partialDeriv_mem_tangentSpace {n : ℕ}
    (patch : HypersurfacePatch n)
    (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hpatch_in_M : ∀ x ∈ patch.domain,
      (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f x) ∈ M)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain)
    (ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hψ : IsLocalDefiningFunction ψ M ((WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f x)))
    (s : Fin n) :
    (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.partialDeriv x s) ∈
      Hypersurface.tangentSpace ψ ((WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f x)) := by sorry

lemma metric_christoffel_identity {n : ℕ} (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) (i j s : Fin n) :
    ∑ k : Fin n, firstFundamentalForm patch x s k *
      ChristoffelSymbols.christoffelSymbol patch x i j k =
    (ChristoffelSymbols.secondPartialDeriv patch x i j) ⬝ᵥ
      (patch.partialDeriv x s) := by

  have hG := firstFundamentalForm_posDef patch x hx
  have hdet : IsUnit (firstFundamentalForm patch x).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hG.isUnit

  let v : Fin n → ℝ := fun l =>
    (ChristoffelSymbols.secondPartialDeriv patch x i j) ⬝ᵥ (patch.partialDeriv x l)
  have hcancel : (firstFundamentalForm patch x).mulVec
      ((firstFundamentalForm patch x)⁻¹.mulVec v) = v := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]


  simp only [ChristoffelSymbols.christoffelSymbol, Matrix.mulVec, dotProduct]
  change (∑ x_1, firstFundamentalForm patch x s x_1 *
    ∑ x_2, (firstFundamentalForm patch x)⁻¹ x_1 x_2 * v x_2) = v s
  have := congr_fun hcancel s
  simp only [Matrix.mulVec, dotProduct] at this
  exact this

theorem second_deriv_inner_product_eq {n : ℕ}
    (patch : HypersurfacePatch n)
    (c : ℝ → Fin n → ℝ)
    (hc_smooth : ContDiff ℝ ⊤ c)
    (hc_domain : ∀ t, c t ∈ patch.domain)
    (t : ℝ) (s : Fin n) :
    ⟪deriv (deriv (fun t =>
      (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f (c t)))) t,
      (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.partialDeriv (c t) s)⟫_ℝ =
    ∑ i : Fin n, ∑ j : Fin n,
      ((ChristoffelSymbols.secondPartialDeriv patch (c t) i j) ⬝ᵥ
        (patch.partialDeriv (c t) s)) *
        (deriv c t i) * (deriv c t j) +
    ∑ k : Fin n, ((patch.partialDeriv (c t) k) ⬝ᵥ
      (patch.partialDeriv (c t) s)) * ((deriv (deriv c) t) k) := by sorry

theorem geodesic_inner_product_formula {n : ℕ}
    (patch : HypersurfacePatch n)
    (c : ℝ → Fin n → ℝ)
    (hc_smooth : ContDiff ℝ ⊤ c)
    (hc_domain : ∀ t, c t ∈ patch.domain)
    (t : ℝ) (s : Fin n) :
    ⟪deriv (deriv (fun t =>
      (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f (c t)))) t,
      (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.partialDeriv (c t) s)⟫_ℝ =
    ∑ k : Fin n, firstFundamentalForm patch (c t) s k *
      ((deriv (deriv c) t) k +
        ∑ i : Fin n, ∑ j : Fin n,
          ChristoffelSymbols.christoffelSymbol patch (c t) i j k *
            (deriv c t i) * (deriv c t j)) := by

  rw [second_deriv_inner_product_eq patch c hc_smooth hc_domain t s]


  have hmetric := metric_christoffel_identity patch (c t) (hc_domain t)


  simp_rw [mul_add, Finset.sum_add_distrib]


  have hG : ∀ k, patch.partialDeriv (c t) k ⬝ᵥ patch.partialDeriv (c t) s =
    firstFundamentalForm patch (c t) s k := by
    intro k
    simp only [firstFundamentalForm, Matrix.of_apply, HypersurfacePatch.partialDeriv]
    exact (dotProduct_comm _ _)

  rw [add_comm]
  congr 1
  ·
    congr 1; ext k; rw [hG]
  ·

    have hlhs : ∀ i j : Fin n,
        (ChristoffelSymbols.secondPartialDeriv patch (c t) i j ⬝ᵥ
          patch.partialDeriv (c t) s) * deriv c t i * deriv c t j =
        ∑ k, firstFundamentalForm patch (c t) s k *
          ChristoffelSymbols.christoffelSymbol patch (c t) i j k *
            deriv c t i * deriv c t j := by
      intro i j; rw [← hmetric i j s, Finset.sum_mul, Finset.sum_mul]
    simp_rw [hlhs]


    conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    congr 1; ext k
    rw [Finset.mul_sum]; congr 1; ext i
    rw [Finset.mul_sum]; congr 1; ext j; ring

theorem firstFundamentalForm_mulVec_injective {n : ℕ}
    (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain) :
    Function.Injective (firstFundamentalForm patch x).mulVec := by sorry

theorem patch_comp_smooth {n : ℕ}
    (patch : HypersurfacePatch n)
    (c : ℝ → Fin n → ℝ)
    (hc_smooth : ContDiff ℝ ⊤ c)
    (hc_domain : ∀ t, c t ∈ patch.domain) :
    ContDiff ℝ ⊤ (fun t => (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f (c t))) := by sorry

theorem tangentSpace_mem_span_partialDerivs {n : ℕ}
    (patch : HypersurfacePatch n)
    (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hM : Hypersurface.IsHypersurface M)
    (hpatch_in_M : ∀ x ∈ patch.domain,
      (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f x) ∈ M)
    (x : Fin n → ℝ) (hx : x ∈ patch.domain)
    (ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hψ : IsLocalDefiningFunction ψ M ((WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f x)))
    (v : EuclideanSpace ℝ (Fin (n + 1)))
    (hv : v ∈ Hypersurface.tangentSpace ψ ((WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f x))) :
    ∃ a : Fin n → ℝ, v = ∑ s : Fin n, a s •
      (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.partialDeriv x s) := by sorry

theorem geodesic_ortho_from_ode {n : ℕ}
    (patch : HypersurfacePatch n)
    (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hM : Hypersurface.IsHypersurface M)
    (c : ℝ → Fin n → ℝ)
    (hc_smooth : ContDiff ℝ ⊤ c)
    (hc_domain : ∀ t, c t ∈ patch.domain)
    (hpatch_in_M : ∀ x ∈ patch.domain,
      (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f x) ∈ M)
    (hode : ∀ t k, (deriv (deriv c) t) k +
      ∑ i, ∑ j, ChristoffelSymbols.christoffelSymbol patch (c t) i j k *
        (deriv c t i) * (deriv c t j) = 0)
    (t : ℝ) (ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hψ : IsLocalDefiningFunction ψ M ((WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f (c t))))
    (v : EuclideanSpace ℝ (Fin (n + 1)))
    (hv : v ∈ Hypersurface.tangentSpace ψ ((WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f (c t)))) :
    ⟪deriv (deriv (fun t => (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f (c t)))) t, v⟫_ℝ = 0 := by

  have hinner_zero : ∀ s : Fin n,
      ⟪deriv (deriv (fun t =>
        (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f (c t)))) t,
        (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.partialDeriv (c t) s)⟫_ℝ = 0 := by
    intro s
    rw [geodesic_inner_product_formula patch c hc_smooth hc_domain t s]

    have hzero : ∀ k : Fin n, (deriv (deriv c) t) k +
        ∑ i, ∑ j, ChristoffelSymbols.christoffelSymbol patch (c t) i j k *
          (deriv c t i) * (deriv c t j) = 0 := hode t
    simp only [hzero, mul_zero, Finset.sum_const_zero]

  obtain ⟨a, hv_eq⟩ := tangentSpace_mem_span_partialDerivs patch M hM hpatch_in_M
    (c t) (hc_domain t) ψ hψ v hv

  rw [hv_eq, inner_sum]
  apply Finset.sum_eq_zero
  intro s _
  rw [real_inner_smul_right, hinner_zero s, mul_zero]

theorem geodesic_equation_coordinates
    {n : ℕ}
    (patch : HypersurfacePatch n)
    (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hM : Hypersurface.IsHypersurface M)
    (c : ℝ → Fin n → ℝ)
    (hc_smooth : ContDiff ℝ ⊤ c)
    (hc_domain : ∀ t, c t ∈ patch.domain)
    (hpatch_in_M : ∀ x ∈ patch.domain,
      (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f x) ∈ M) :
    IsGeodesic M hM (fun t => (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f (c t))) ↔
    SatisfiesGeodesicEquation patch c := by
  constructor
  ·
    intro ⟨hγ_smooth, hγ_in_M, hperp⟩
    refine ⟨hc_smooth, hc_domain, fun t k => ?_⟩

    have hinner_zero : ∀ s : Fin n,
        ⟪deriv (deriv (fun t =>
          (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f (c t)))) t,
          (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.partialDeriv (c t) s)⟫_ℝ = 0 := by
      intro s
      obtain ⟨ψ, hψ⟩ := hM _ (hγ_in_M t)
      exact hperp t ψ hψ _ (patch_partialDeriv_mem_tangentSpace patch M hpatch_in_M
        (c t) (hc_domain t) ψ hψ s)

    have hGv_zero : ∀ s, ∑ k : Fin n, firstFundamentalForm patch (c t) s k *
        ((deriv (deriv c) t) k +
          ∑ i, ∑ j, ChristoffelSymbols.christoffelSymbol patch (c t) i j k *
            (deriv c t i) * (deriv c t j)) = 0 := by
      intro s
      rw [← geodesic_inner_product_formula patch c hc_smooth hc_domain t s]
      exact hinner_zero s

    have hGmul : (firstFundamentalForm patch (c t)).mulVec
        (fun k => (deriv (deriv c) t) k +
          ∑ i, ∑ j, ChristoffelSymbols.christoffelSymbol patch (c t) i j k *
            (deriv c t i) * (deriv c t j)) = 0 := by
      ext s; simp only [Matrix.mulVec, Pi.zero_apply]; exact hGv_zero s

    have hv : (fun k => (deriv (deriv c) t) k +
        ∑ i, ∑ j, ChristoffelSymbols.christoffelSymbol patch (c t) i j k *
          (deriv c t i) * (deriv c t j)) = 0 :=
      firstFundamentalForm_mulVec_injective patch (c t) (hc_domain t)
        (hGmul.trans (Matrix.mulVec_zero _).symm)

    exact congr_fun hv k
  ·
    intro ⟨_, _, hode⟩
    exact ⟨patch_comp_smooth patch c hc_smooth hc_domain,
           fun t => hpatch_in_M (c t) (hc_domain t),
           fun t ψ hψ v hv => geodesic_ortho_from_ode patch M hM c hc_smooth
             hc_domain hpatch_in_M hode t ψ hψ v hv⟩

section GeodesicDistance

variable {n : ℕ}

structure SmoothPathIn (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (p q : EuclideanSpace ℝ (Fin (n + 1))) where
  toFun : ℝ → EuclideanSpace ℝ (Fin (n + 1))
  smooth : ∀ (m : ℕ∞), ContDiff ℝ m toFun
  source : toFun 0 = p
  target : toFun 1 = q
  maps_to : ∀ t, toFun t ∈ M

def pathLength {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))} (γ : SmoothPathIn M p q) : ℝ :=
  ∫ t in (0 : ℝ)..1, ‖deriv γ.toFun t‖

def reversePath {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))} (γ : SmoothPathIn M p q) :
    SmoothPathIn M q p where
  toFun := fun t => γ.toFun (1 - t)
  smooth := fun m => (γ.smooth m).comp (by fun_prop)
  source := by simp [γ.target]
  target := by simp [γ.source]
  maps_to := fun t => γ.maps_to _

theorem pathLength_reverse {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))} (γ : SmoothPathIn M p q) :
    pathLength (reversePath γ) = pathLength γ := by
  simp only [pathLength, reversePath]
  have hd : ∀ t, deriv (fun t => γ.toFun (1 - t)) t = -(deriv γ.toFun (1 - t)) := by
    intro t
    have hda : DifferentiableAt ℝ γ.toFun (1 - t) :=
      ((γ.smooth 1).differentiable (by simp)).differentiableAt
    have hd1 : HasDerivAt (fun t => (1 : ℝ) - t) (-1) t := by
      have := (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
      simp at this
      exact this
    have hcomp := hda.hasDerivAt.scomp t hd1
    have heq : (fun t => γ.toFun (1 - t)) = γ.toFun ∘ HSub.hSub 1 := rfl
    rw [heq, hcomp.deriv]
    simp
  simp_rw [hd, norm_neg]
  rw [intervalIntegral.integral_comp_sub_left (fun t => ‖deriv γ.toFun t‖) 1]
  simp

def geodesicDist (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (p q : EuclideanSpace ℝ (Fin (n + 1))) : ℝ :=
  sInf {l | ∃ γ : SmoothPathIn M p q, pathLength γ = l}

def IsSmoothOnHypersurface {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (M : Set E) (f : ↥M → ℝ) : Prop :=
  ∀ (y : E) (hy : y ∈ M), ∃ (V : Set E) (hV : IsOpen V) (hyV : y ∈ V)
    (f_ext : E → ℝ), ContDiffOn ℝ ⊤ f_ext V ∧
    ∀ z (hzM : z ∈ M) (_ : z ∈ V), f_ext z = f ⟨z, hzM⟩

structure ConnectedHypersurface (n : ℕ) where
  carrier : Set (EuclideanSpace ℝ (Fin (n + 1)))
  isHypersurface : IsHypersurface carrier
  connected : ∀ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ),
    (∀ y ∈ carrier, ContDiffAt ℝ ⊤ φ y) →
    (∀ y ∈ carrier, ∀ ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      IsLocalDefiningFunction ψ carrier y →
      ∀ v ∈ tangentSpace ψ y, fderiv ℝ φ y v = 0) →
    (∀ y₁ ∈ carrier, ∀ y₂ ∈ carrier, φ y₁ = φ y₂)

structure ConnectedHypersurfaceWithPaths (n : ℕ) extends ConnectedHypersurface n where
  pathConnected : ∀ p q : EuclideanSpace ℝ (Fin (n + 1)),
    p ∈ carrier → q ∈ carrier → Nonempty (SmoothPathIn carrier p q)

end GeodesicDistance

theorem compact_connected_hypersurface_orientable
    {n : ℕ}
    (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hM : IsHypersurface M)
    (hconn : IsConnected M)
    (hcpt : IsCompact M) :
    IsOrientable M := by sorry

theorem smooth_concat_exists_path {n : ℕ}
    (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    {p q r : EuclideanSpace ℝ (Fin (n + 1))}
    (α : SmoothPathIn M p q) (β : SmoothPathIn M q r) :
    ∃ δ : SmoothPathIn M p r, pathLength δ ≤ pathLength α + pathLength β := by sorry

section GeodesicDistance
variable {n : ℕ}

theorem geodesicDist_self (M : ConnectedHypersurfaceWithPaths n)
    (p : EuclideanSpace ℝ (Fin (n + 1))) (hp : p ∈ M.carrier) :
    geodesicDist M.carrier p p = 0 := by
  apply le_antisymm
  · apply csInf_le
    · exact ⟨0, fun l ⟨γ, hγ⟩ => hγ ▸
        intervalIntegral.integral_nonneg (by norm_num) (fun t _ => norm_nonneg _)⟩
    · exact ⟨⟨fun _ => p, fun _ => contDiff_const, rfl, rfl, fun _ => hp⟩, by
        simp [pathLength, deriv_const]⟩
  · apply le_csInf
    · exact ⟨_, ⟨fun _ => p, fun _ => contDiff_const, rfl, rfl, fun _ => hp⟩, rfl⟩
    · intro l ⟨γ, hγ⟩
      rw [← hγ]
      exact intervalIntegral.integral_nonneg (by norm_num) (fun t _ => norm_nonneg _)

theorem geodesicDist_comm (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (p q : EuclideanSpace ℝ (Fin (n + 1))) :
    geodesicDist M p q = geodesicDist M q p := by
  simp only [geodesicDist]
  congr 1
  ext l
  simp only [Set.mem_setOf_eq]
  exact ⟨fun ⟨γ, hγ⟩ => ⟨reversePath γ, by rw [pathLength_reverse, hγ]⟩,
         fun ⟨γ, hγ⟩ => ⟨reversePath γ, by rw [pathLength_reverse, hγ]⟩⟩

theorem geodesicDist_triangle (M : ConnectedHypersurfaceWithPaths n)
    (p q r : EuclideanSpace ℝ (Fin (n + 1)))
    (hp : p ∈ M.carrier) (hq : q ∈ M.carrier) (hr : r ∈ M.carrier) :
    geodesicDist M.carrier p r ≤
      geodesicDist M.carrier p q + geodesicDist M.carrier q r := by
  have hkey : ∀ (α : SmoothPathIn M.carrier p q) (β : SmoothPathIn M.carrier q r),
      geodesicDist M.carrier p r ≤ pathLength α + pathLength β := by
    intro α β
    have ⟨δ, hδ⟩ := smooth_concat_exists_path M.carrier α β
    calc geodesicDist M.carrier p r
        ≤ pathLength δ := by
          apply csInf_le
          · exact ⟨0, fun l ⟨γ, hγ⟩ => hγ ▸
              intervalIntegral.integral_nonneg (by norm_num) (fun t _ => norm_nonneg _)⟩
          · exact ⟨δ, rfl⟩
      _ ≤ pathLength α + pathLength β := hδ
  have h1 : ∀ α : SmoothPathIn M.carrier p q,
      geodesicDist M.carrier p r ≤ pathLength α + geodesicDist M.carrier q r := by
    intro α
    suffices geodesicDist M.carrier p r - pathLength α ≤ geodesicDist M.carrier q r by
      linarith
    apply le_csInf
    · exact ⟨pathLength (M.pathConnected q r hq hr).some, (M.pathConnected q r hq hr).some, rfl⟩
    · intro l ⟨β, hβ⟩
      rw [← hβ]
      linarith [hkey α β]
  suffices geodesicDist M.carrier p r - geodesicDist M.carrier q r ≤
      geodesicDist M.carrier p q by linarith
  apply le_csInf
  · exact ⟨pathLength (M.pathConnected p q hp hq).some, (M.pathConnected p q hp hq).some, rfl⟩
  · intro l ⟨α, hα⟩
    rw [← hα]
    linarith [h1 α]

theorem geodesicDist_eq_zero_iff (M : ConnectedHypersurfaceWithPaths n)
    (p q : EuclideanSpace ℝ (Fin (n + 1))) (hp : p ∈ M.carrier) (hq : q ∈ M.carrier)
    (heq : geodesicDist M.carrier p q = 0) : p = q := by
  by_contra hne
  have hpos : 0 < ‖q - p‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr (Ne.symm hne)
  have hle : ‖q - p‖ ≤ geodesicDist M.carrier p q := by
    apply le_csInf
    · exact ⟨pathLength (M.pathConnected p q hp hq).some, (M.pathConnected p q hp hq).some, rfl⟩
    · intro l ⟨γ, hγ⟩
      rw [← hγ]
      have hdiff : ∀ x ∈ Set.uIcc (0 : ℝ) 1, DifferentiableAt ℝ γ.toFun x :=
        fun x _ => ((γ.smooth 1).differentiable (by simp)).differentiableAt
      have hint : IntervalIntegrable (deriv γ.toFun) volume 0 1 :=
        ((γ.smooth 1).continuous_deriv (by simp)).continuousOn.intervalIntegrable
      have hftc : ∫ t in (0 : ℝ)..1, deriv γ.toFun t = γ.toFun 1 - γ.toFun 0 :=
        integral_deriv_eq_sub hdiff hint
      calc ‖q - p‖ = ‖γ.toFun 1 - γ.toFun 0‖ := by rw [γ.target, γ.source]
        _ = ‖∫ t in (0 : ℝ)..1, deriv γ.toFun t‖ := by rw [hftc]
        _ ≤ ∫ t in (0 : ℝ)..1, ‖deriv γ.toFun t‖ := norm_integral_le_integral_norm (by norm_num)
  linarith

theorem geodesicDist_metric (M : ConnectedHypersurfaceWithPaths n)
    (p q r : EuclideanSpace ℝ (Fin (n + 1)))
    (hp : p ∈ M.carrier) (hq : q ∈ M.carrier) (hr : r ∈ M.carrier) :
    geodesicDist M.carrier p p = 0 ∧
    geodesicDist M.carrier p q = geodesicDist M.carrier q p ∧
    geodesicDist M.carrier p r ≤
      geodesicDist M.carrier p q + geodesicDist M.carrier q r ∧
    (geodesicDist M.carrier p q = 0 → p = q) :=
  ⟨geodesicDist_self M p hp,
   geodesicDist_comm M.carrier p q,
   geodesicDist_triangle M p q r hp hq hr,
   geodesicDist_eq_zero_iff M p q hp hq⟩

end GeodesicDistance

theorem cauchy_schwarz_integral
    (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) (hab : a < b) :
    (∫ t in a..b, f t ≤ Real.sqrt (b - a) * Real.sqrt (∫ t in a..b, (f t) ^ 2)) ∧
    ((∫ t in a..b, f t = Real.sqrt (b - a) * Real.sqrt (∫ t in a..b, (f t) ^ 2)) ↔
      (∃ c : ℝ, ∀ t, t ∈ Set.Icc a b → f t = c)) := by sorry

theorem cauchy_schwarz_integral_eq_iff
    (f : ℝ → ℝ) (hf : Continuous f) (hf_nn : ∀ t, 0 ≤ f t) (a b : ℝ) (hab : a < b) :
    (∫ t in a..b, f t = Real.sqrt (b - a) * Real.sqrt (∫ t in a..b, (f t) ^ 2)) ↔
    (∃ c, ∀ t ∈ Set.Icc a b, f t = c) := by sorry

def lengthAB {n : ℕ} (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖deriv γ t‖

theorem energy_ge_length_sq_div {n : ℕ}
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (a b : ℝ) (hab : a < b)
    (hγ : ContDiff ℝ ⊤ γ) :
    (energy γ a b ≥ lengthAB γ a b ^ 2 / (b - a)) ∧
    (energy γ a b = lengthAB γ a b ^ 2 / (b - a) ↔
      ∃ c, ∀ t ∈ Set.Icc a b, ‖deriv γ t‖ = c) := by
  have hd : (0 : ℝ) < b - a := sub_pos.mpr hab

  have hf_cont : Continuous (fun t => ‖deriv γ t‖) :=
    (hγ.continuous_deriv le_top).norm

  have hCS := (cauchy_schwarz_integral (fun t => ‖deriv γ t‖) hf_cont a b hab).1


  have hL_nn : 0 ≤ lengthAB γ a b :=
    intervalIntegral.integral_nonneg hab.le (fun t _ => norm_nonneg _)

  have hE_nn : 0 ≤ energy γ a b :=
    intervalIntegral.integral_nonneg hab.le (fun t _ => sq_nonneg _)

  have h_sq : lengthAB γ a b ^ 2 ≤ (b - a) * energy γ a b := by
    have h2 : lengthAB γ a b ^ 2 ≤ (Real.sqrt (b - a) * Real.sqrt (energy γ a b)) ^ 2 :=
      pow_le_pow_left₀ hL_nn hCS 2
    rw [mul_pow, Real.sq_sqrt hd.le, Real.sq_sqrt hE_nn] at h2
    exact h2
  refine ⟨?_, ?_⟩
  ·
    show lengthAB γ a b ^ 2 / (b - a) ≤ energy γ a b
    rw [div_le_iff₀ hd]
    linarith [mul_comm (b - a) (energy γ a b)]
  ·

    have hCS_eq := cauchy_schwarz_integral_eq_iff (fun t => ‖deriv γ t‖) hf_cont
      (fun t => norm_nonneg _) a b hab

    have key : (lengthAB γ a b = Real.sqrt (b - a) * Real.sqrt (energy γ a b)) ↔
        (∃ c, ∀ t ∈ Set.Icc a b, ‖deriv γ t‖ = c) := by
      change (∫ t in a..b, ‖deriv γ t‖ =
        Real.sqrt (b - a) * Real.sqrt (∫ t in a..b, ‖deriv γ t‖ ^ 2)) ↔ _
      exact hCS_eq

    have equiv_eq : (energy γ a b = lengthAB γ a b ^ 2 / (b - a)) ↔
        (lengthAB γ a b = Real.sqrt (b - a) * Real.sqrt (energy γ a b)) := by
      constructor
      · intro heq
        have hL_sq : lengthAB γ a b ^ 2 = (b - a) * energy γ a b := by
          field_simp at heq ⊢; linarith
        have hRHS_nn : 0 ≤ Real.sqrt (b - a) * Real.sqrt (energy γ a b) :=
          mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        nlinarith [Real.sq_sqrt hd.le, Real.sq_sqrt hE_nn,
          sq_nonneg (lengthAB γ a b - Real.sqrt (b - a) * Real.sqrt (energy γ a b))]
      · intro heq
        have hL_sq : lengthAB γ a b ^ 2 = (b - a) * energy γ a b := by
          rw [heq, mul_pow, Real.sq_sqrt hd.le, Real.sq_sqrt hE_nn]
        field_simp
        linarith
    exact equiv_eq.trans key

section EnergyLengthEquivalence

variable {n : ℕ}

def pathEnergy {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))} (γ : SmoothPathIn M p q) : ℝ :=
  ∫ t in (0 : ℝ)..1, ‖deriv γ.toFun t‖ ^ 2

def IsConstantSpeed {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))} (γ : SmoothPathIn M p q) : Prop :=
  ∃ c : ℝ, ∀ t, ‖deriv γ.toFun t‖ = c

def IsAbsoluteLengthMinimizer {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))} (γ : SmoothPathIn M p q) : Prop :=
  ∀ σ : SmoothPathIn M p q, pathLength γ ≤ pathLength σ

def IsAbsoluteEnergyMinimizer {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))} (γ : SmoothPathIn M p q) : Prop :=
  ∀ σ : SmoothPathIn M p q, pathEnergy γ ≤ pathEnergy σ

theorem energy_ge_length_sq
    {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))}
    (γ : SmoothPathIn M p q) :
    pathLength γ ^ 2 ≤ pathEnergy γ := by sorry

theorem energy_eq_length_sq_iff_constant_speed
    {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))}
    (γ : SmoothPathIn M p q) :
    pathEnergy γ = pathLength γ ^ 2 ↔ IsConstantSpeed γ := by sorry

theorem exists_constant_speed_reparametrization
    {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))}
    (σ : SmoothPathIn M p q) :
    ∃ σ' : SmoothPathIn M p q, IsConstantSpeed σ' ∧ pathLength σ' = pathLength σ := by sorry

theorem energy_minimizer_of_length_minimizer_constant_speed
    {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))}
    (γ : SmoothPathIn M p q)
    (hlen : IsAbsoluteLengthMinimizer γ)
    (hcs : IsConstantSpeed γ) :
    IsAbsoluteEnergyMinimizer γ := by
  intro σ

  have hγ_eq : pathEnergy γ = pathLength γ ^ 2 :=
    (energy_eq_length_sq_iff_constant_speed γ).mpr hcs

  have hσ_ineq : pathLength σ ^ 2 ≤ pathEnergy σ := energy_ge_length_sq σ

  have hlen_ineq : pathLength γ ≤ pathLength σ := hlen σ

  have h_γ_nonneg : 0 ≤ pathLength γ := by
    unfold pathLength
    exact intervalIntegral.integral_nonneg (by norm_num) (fun t _ => norm_nonneg _)
  have hlen_sq : pathLength γ ^ 2 ≤ pathLength σ ^ 2 :=
    pow_le_pow_left₀ h_γ_nonneg hlen_ineq 2

  linarith

theorem length_minimizer_constant_speed_of_energy_minimizer
    {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))}
    (γ : SmoothPathIn M p q)
    (hmin : IsAbsoluteEnergyMinimizer γ) :
    IsAbsoluteLengthMinimizer γ ∧ IsConstantSpeed γ := by


  have h_energy_le_length_sq : ∀ σ : SmoothPathIn M p q, pathEnergy γ ≤ pathLength σ ^ 2 := by
    intro σ
    obtain ⟨σ', hcs', hlen'⟩ := exists_constant_speed_reparametrization σ
    have hσ'_eq : pathEnergy σ' = pathLength σ' ^ 2 :=
      (energy_eq_length_sq_iff_constant_speed σ').mpr hcs'
    calc pathEnergy γ ≤ pathEnergy σ' := hmin σ'
      _ = pathLength σ' ^ 2 := hσ'_eq
      _ = pathLength σ ^ 2 := by rw [hlen']

  have h_cs : pathLength γ ^ 2 ≤ pathEnergy γ := energy_ge_length_sq γ


  have h_length_min : IsAbsoluteLengthMinimizer γ := by
    intro σ
    have h1 : pathLength γ ^ 2 ≤ pathLength σ ^ 2 :=
      le_trans h_cs (h_energy_le_length_sq σ)
    have h_σ_nonneg : 0 ≤ pathLength σ := by
      unfold pathLength
      exact intervalIntegral.integral_nonneg (by norm_num) (fun t _ => norm_nonneg _)
    exact le_of_sq_le_sq h1 h_σ_nonneg

  have h_energy_eq : pathEnergy γ = pathLength γ ^ 2 := by
    have h_le : pathEnergy γ ≤ pathLength γ ^ 2 := h_energy_le_length_sq γ
    linarith

  have h_cs_γ : IsConstantSpeed γ :=
    (energy_eq_length_sq_iff_constant_speed γ).mp h_energy_eq
  exact ⟨h_length_min, h_cs_γ⟩

theorem energy_minimizer_iff_length_minimizer_constant_speed
    {M : Set (EuclideanSpace ℝ (Fin (n + 1)))}
    {p q : EuclideanSpace ℝ (Fin (n + 1))}
    (γ : SmoothPathIn M p q) :
    IsAbsoluteEnergyMinimizer γ ↔
      (IsAbsoluteLengthMinimizer γ ∧ IsConstantSpeed γ) := by
  constructor
  · exact length_minimizer_constant_speed_of_energy_minimizer γ
  · intro ⟨hlen, hcs⟩
    exact energy_minimizer_of_length_minimizer_constant_speed γ hlen hcs

end EnergyLengthEquivalence

def IsMetricGeodesic {X : Type*} [MetricSpace X] (γ : ℝ → X) (a b : ℝ) : Prop :=
  Continuous γ ∧ ∀ s t, s ∈ Set.Icc a b → t ∈ Set.Icc a b → dist (γ s) (γ t) = |s - t|

def IsGlobalMetricGeodesic {X : Type*} [MetricSpace X] (γ : ℝ → X) : Prop :=
  ∀ s t : ℝ, dist (γ s) (γ t) = |s - t|

section Hadamard

variable {n : ℕ}

structure CompactPositiveGaussCurvature (n : ℕ) where
  carrier : Set (EuclideanSpace ℝ (Fin (n + 1)))
  isHypersurface : IsHypersurface carrier
  isCompact : IsCompact carrier
  isConnected : IsConnected carrier
  gaussCurvaturePos : ∀ (patch : HypersurfacePatch n) (x : Fin n → ℝ),
    x ∈ patch.domain →
    (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f x) ∈ carrier →
    0 < gaussCurvature patch x

theorem gauss_map_injective_of_positive_curvature
    (M : CompactPositiveGaussCurvature n)
    (hn : 2 ≤ n)
    (ν : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hν_maps : ∀ y ∈ M.carrier, ν y ∈ GaussMap.unitSphere n)
    (hν_smooth : ContDiffOn ℝ ⊤ ν M.carrier)
    (hν_gauss_map : ∀ (patch : HypersurfacePatch n) (x : Fin n → ℝ),
      x ∈ patch.domain →
      (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f x) ∈ M.carrier →
      ν ((WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f x)) =
        (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (gaussNormal patch x)) :
    ∀ y ∈ M.carrier, ∀ ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      Hypersurface.IsLocalDefiningFunction ψ M.carrier y →
        ∀ v ∈ Hypersurface.tangentSpace ψ y, fderiv ℝ ν y v = 0 → v = 0 := by sorry

theorem convex_of_bijective_gauss_map
    (M : CompactPositiveGaussCurvature n)
    (hn : 2 ≤ n)
    (ν : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hν_maps : ∀ y ∈ M.carrier, ν y ∈ GaussMap.unitSphere n)
    (hν_bij : Function.Bijective (fun (y : M.carrier) =>
      (⟨ν y, hν_maps y y.2⟩ : GaussMap.unitSphere n))) :
    Hypersurface.IsConvexHypersurface M.carrier := by sorry

theorem hadamard_convexity
    (M : CompactPositiveGaussCurvature n)
    (hn : 2 ≤ n)
    (ν : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1)))
    (hν_maps : ∀ y ∈ M.carrier, ν y ∈ GaussMap.unitSphere n)
    (hν_smooth : ContDiffOn ℝ ⊤ ν M.carrier)
    (hν_gauss_map : ∀ (patch : HypersurfacePatch n) (x : Fin n → ℝ),
      x ∈ patch.domain →
      (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f x) ∈ M.carrier →
      ν ((WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (patch.f x)) =
        (WithLp.equiv 2 (Fin (n + 1) → ℝ)).symm (gaussNormal patch x)) :
    Hypersurface.IsConvexHypersurface M.carrier := by

  have h_inj := gauss_map_injective_of_positive_curvature M hn ν hν_maps hν_smooth hν_gauss_map

  have h_bij : Function.Bijective (fun (y : M.carrier) =>
      (⟨ν y, hν_maps y y.2⟩ : GaussMap.unitSphere n)) :=
    GaussMap.smooth_local_diffeo_compact_to_sphere_bijective
      M.carrier M.isHypersurface M.isCompact M.isConnected hn ν hν_maps hν_smooth h_inj

  exact convex_of_bijective_gauss_map M hn ν hν_maps h_bij

end Hadamard

section HopfRinow

variable {n : ℕ}

def IsRiemannianGeodesicallyComplete (M : ConnectedHypersurface n) : Prop :=
  ∀ (y : EuclideanSpace ℝ (Fin (n + 1))) (hy : y ∈ M.carrier)
    (ψ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hψ : IsLocalDefiningFunction ψ M.carrier y)
    (Y : EuclideanSpace ℝ (Fin (n + 1))) (hY : Y ∈ Hypersurface.tangentSpace ψ y),
    ∃ γ : ℝ → EuclideanSpace ℝ (Fin (n + 1)),
      IsGeodesic M.carrier M.isHypersurface γ ∧ γ 0 = y ∧ deriv γ 0 = Y

def IsMetricallyComplete (M : ConnectedHypersurface n) : Prop :=
  ∀ (x : ℕ → EuclideanSpace ℝ (Fin (n + 1))),
    (∀ i, x i ∈ M.carrier) →
    (∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ k ≥ N, geodesicDist M.carrier (x m) (x k) < ε) →
    ∃ p ∈ M.carrier, ∀ ε > 0, ∃ N, ∀ m ≥ N, geodesicDist M.carrier (x m) p < ε

def IsMinimizingGeodesic (M : ConnectedHypersurface n)
    (p q : EuclideanSpace ℝ (Fin (n + 1)))
    (γ : ℝ → EuclideanSpace ℝ (Fin (n + 1)))
    (a b : ℝ) : Prop :=
  IsGeodesic M.carrier M.isHypersurface γ ∧
  γ a = p ∧ γ b = q ∧
    ∀ σ : ℝ → EuclideanSpace ℝ (Fin (n + 1)),
      ContDiff ℝ ⊤ σ → (∀ t, σ t ∈ M.carrier) → σ a = p → σ b = q →
      energy γ a b ≤ energy σ a b

theorem hopf_rinow_minimizing_geodesic
    (M : ConnectedHypersurface n)
    (hM : IsClosed M.carrier)
    (p q : EuclideanSpace ℝ (Fin (n + 1)))
    (hp : p ∈ M.carrier) (hq : q ∈ M.carrier)
    (a b : ℝ) (hab : a < b) :
    ∃ γ : ℝ → EuclideanSpace ℝ (Fin (n + 1)), IsMinimizingGeodesic M p q γ a b := by sorry

end HopfRinow

def IsGeodesicSpace (X : Type*) [MetricSpace X] : Prop :=
  ∀ (p q : X), ∃ (γ : ℝ → X),
    IsMetricGeodesic γ 0 (dist p q) ∧ γ 0 = p ∧ γ (dist p q) = q

def IsCATZeroSpace (X : Type*) [MetricSpace X] : Prop :=
  IsGeodesicSpace X ∧
  ∀ (p₁ p₂ p₃ : X)
    (γ₁₂ γ₁₃ γ₂₃ : ℝ → X),

    IsMetricGeodesic γ₁₂ 0 (dist p₁ p₂) →
    γ₁₂ 0 = p₁ → γ₁₂ (dist p₁ p₂) = p₂ →
    IsMetricGeodesic γ₁₃ 0 (dist p₁ p₃) →
    γ₁₃ 0 = p₁ → γ₁₃ (dist p₁ p₃) = p₃ →
    IsMetricGeodesic γ₂₃ 0 (dist p₂ p₃) →
    γ₂₃ 0 = p₂ → γ₂₃ (dist p₂ p₃) = p₃ →

    ∀ (q₁ q₂ q₃ : EuclideanSpace ℝ (Fin 2)),
    dist q₁ q₂ = dist p₁ p₂ →
    dist q₁ q₃ = dist p₁ p₃ →
    dist q₂ q₃ = dist p₂ p₃ →

    ∀ (t : ℝ) (s : ℝ),
    t ∈ Set.Icc 0 (dist p₁ p₂) →
    s ∈ Set.Icc 0 (dist p₁ p₃) →

    dist (γ₁₂ t) (γ₁₃ s) ≤
      dist ((1 - t / dist p₁ p₂) • q₁ + (t / dist p₁ p₂) • q₂)
           ((1 - s / dist p₁ p₃) • q₁ + (s / dist p₁ p₃) • q₃)

class IsBusemannSpace (X : Type*) [MetricSpace X] : Prop where
  isGeodesicSpace : IsGeodesicSpace X
  busemann_inequality : ∀ (l : ℝ) (hl : 0 < l)
    (γ₁ γ₂ : ℝ → X)
    (hγ₁ : IsMetricGeodesic γ₁ 0 l) (hγ₂ : IsMetricGeodesic γ₂ 0 l)
    (h_start : γ₁ 0 = γ₂ 0)
    (t : ℝ) (ht : t ∈ Set.Icc 0 l),
    dist (γ₁ t) (γ₂ t) ≤ (t / l) * dist (γ₁ l) (γ₂ l)

theorem busemann_unique_geodesic
    {X : Type*} [MetricSpace X] [IsBusemannSpace X]
    (p q : X) :
    (∃ γ : ℝ → X, IsMetricGeodesic γ 0 (dist p q) ∧ γ 0 = p ∧ γ (dist p q) = q) ∧
    (∀ γ₁ γ₂ : ℝ → X,
      IsMetricGeodesic γ₁ 0 (dist p q) → γ₁ 0 = p → γ₁ (dist p q) = q →
      IsMetricGeodesic γ₂ 0 (dist p q) → γ₂ 0 = p → γ₂ (dist p q) = q →
      ∀ t ∈ Set.Icc 0 (dist p q), γ₁ t = γ₂ t) := by
  constructor
  ·
    exact IsBusemannSpace.isGeodesicSpace p q
  ·
    intro γ₁ γ₂ hγ₁ hγ₁p hγ₁q hγ₂ hγ₂p hγ₂q t ht
    by_cases hpq : dist p q = 0
    ·
      have ht0 : t = 0 := le_antisymm (by linarith [ht.2, hpq.symm ▸ ht.2]) ht.1
      rw [ht0, hγ₁p, hγ₂p]
    ·
      have hd_pos : 0 < dist p q := by positivity
      have h_bus := IsBusemannSpace.busemann_inequality (dist p q) hd_pos
        γ₁ γ₂ hγ₁ hγ₂ (by rw [hγ₁p, hγ₂p]) t ht
      rw [hγ₁q, hγ₂q, dist_self, mul_zero] at h_bus
      exact dist_le_zero.mp h_bus

theorem cauchy_schwarz_energy_length {n : ℕ}
    (σ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (a b : ℝ) (hab : a < b)
    (hσ : ContDiff ℝ ⊤ σ) :
    (∫ t in a..b, ‖deriv σ t‖) ^ 2 ≤ (b - a) * ∫ t in a..b, ‖deriv σ t‖ ^ 2 := by sorry

theorem geodesic_locally_minimizes_length {n : ℕ}
    (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hM : IsHypersurface M)
    (γ σ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (a b : ℝ) (hab : a < b)
    (hγ_geo : IsGeodesic M hM γ)
    (hγ_unit : ∀ t, ‖deriv γ t‖ = 1)
    (hσ : ContDiff ℝ ⊤ σ) (hσ_in : ∀ t, σ t ∈ M)
    (hendpoints : σ a = γ a ∧ σ b = γ b) :
    ∫ t in a..b, ‖deriv σ t‖ ≥ b - a := by sorry

theorem geodesic_arclength_minimizes_energy_locally {n : ℕ}
    (M : Set (EuclideanSpace ℝ (Fin (n + 1))))
    (hM : IsHypersurface M)
    (γ σ : ℝ → EuclideanSpace ℝ (Fin (n + 1))) (a b : ℝ) (hab : a < b)
    (hγ_geo : IsGeodesic M hM γ)
    (hγ_unit : ∀ t, ‖deriv γ t‖ = 1)
    (hσ : ContDiff ℝ ⊤ σ) (hσ_in : ∀ t, σ t ∈ M)
    (hendpoints : σ a = γ a ∧ σ b = γ b) :
    energy σ a b ≥ energy γ a b := by

  have h_length_min : ∫ t in a..b, ‖deriv σ t‖ ≥ b - a :=
    geodesic_locally_minimizes_length M hM γ σ a b hab hγ_geo hγ_unit hσ hσ_in hendpoints
  have hCS : (∫ t in a..b, ‖deriv σ t‖) ^ 2 ≤ (b - a) * ∫ t in a..b, ‖deriv σ t‖ ^ 2 :=
    cauchy_schwarz_energy_length σ a b hab hσ

  unfold energy
  have hEγ : ∫ t in a..b, ‖deriv γ t‖ ^ 2 = b - a := by
    have h1 : ∀ t, ‖deriv γ t‖ ^ 2 = (1 : ℝ) := fun t => by rw [hγ_unit t]; norm_num
    simp_rw [h1]; simp
  rw [hEγ]

  have hba_pos : (0 : ℝ) < b - a := sub_pos.mpr hab
  have h1 : (b - a) * ∫ t in a..b, ‖deriv σ t‖ ^ 2 ≥ (b - a) ^ 2 :=
    calc (b - a) * ∫ t in a..b, ‖deriv σ t‖ ^ 2
        ≥ (∫ t in a..b, ‖deriv σ t‖) ^ 2 := hCS
      _ ≥ (b - a) ^ 2 := sq_le_sq' (by linarith) h_length_min
  nlinarith [sq_nonneg (b - a)]

end Geodesics
