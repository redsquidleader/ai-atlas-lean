/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.ProjectiveFunctors
import Atlas.LieGroups.code.HeckeKL

noncomputable section

universe u

variable {R : Type u} [CommRing R] [IsDomain R]
variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
variable {Δ : TriangularDecomposition R 𝔤}
variable (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)

def IsInXi0_23_7
    (rd : PositiveRootData Δ) (mu lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∃ (c : (Δ.𝔥 →ₗ[R] R) → ℤ),
    lam - mu = ∑ α ∈ rd.posRoots, (c α) • α

def WeylStabilizer_23_7
    (wg : WeylGroupData Δ) (lam : Δ.𝔥 →ₗ[R] R) : Set wg.W :=
  {w | wg.dualAction w lam = lam}

def BruhatLE_23_7
    (rd : PositiveRootData Δ) (mu nu : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∃ (c : (Δ.𝔥 →ₗ[R] R) → ℕ),
    nu - mu = ∑ α ∈ rd.posRoots, (c α) • α

def IsDominant_23_7
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ) (lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∀ (w : wg.W), BruhatLE_23_7 rd (wg.dualAction w lam) lam

structure IsProperRep_23_7
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (mu lam : Δ.𝔥 →ₗ[R] R) : Prop where
  lam_dominant : IsDominant_23_7 rd wg lam
  in_xi0 : IsInXi0_23_7 rd mu lam
  mu_minimal : ∀ (w : wg.W), w ∈ WeylStabilizer_23_7 wg lam →
    BruhatLE_23_7 rd mu (wg.dualAction w mu)

def WeylOrbitPair_23_7
    (wg : WeylGroupData Δ) (mu lam : Δ.𝔥 →ₗ[R] R) :
    Set ((Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R)) :=
  {p | ∃ w : wg.W, p = (wg.dualAction w mu, wg.dualAction w lam)}

structure BilinFormData_23_7
    (wg : WeylGroupData Δ) [LE R] where
  normSq : (Δ.𝔥 →ₗ[R] R) → R
  weyl_invariant : ∀ (w : wg.W) (v : Δ.𝔥 →ₗ[R] R),
    normSq (wg.dualAction w v) = normSq v
  normSq_sub_weyl_invariant : ∀ (w : wg.W) (a b : Δ.𝔥 →ₗ[R] R),
    normSq (wg.dualAction w a - wg.dualAction w b) = normSq (a - b)

structure SupportData_23_7
    (wg : WeylGroupData Δ) where
  support : Set ((Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R))
  weyl_equivariant : ∀ (w : wg.W) (p : (Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R)),
    p ∈ support → (wg.dualAction w p.1, wg.dualAction w p.2) ∈ support

def maximalSupport_23_7 [LE R]
    {wg : WeylGroupData Δ} (B : BilinFormData_23_7 wg) (S : SupportData_23_7 wg) :
    Set ((Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R)) :=
  {p | p ∈ S.support ∧
    ∀ q ∈ S.support, B.normSq (q.2 - q.1) ≤ B.normSq (p.2 - p.1)}

theorem theorem_20_13_bruhat_lower_bound
    (S : SupportData_23_7 wg)
    (mu lam : Δ.𝔥 →ₗ[R] R)
    (phi : Δ.𝔥 →ₗ[R] R)

    (_h_mu_in_S : (mu, lam) ∈ S.support)
    (_h_phi_in_S : (phi, lam) ∈ S.support) :
    BruhatLE_23_7 rd mu phi := by sorry

theorem lemma_23_4_i_extracted [LinearOrder R]
    (B : BilinFormData_23_7 wg)
    (lam phi mu : Δ.𝔥 →ₗ[R] R)
    (_hlam_dom : IsDominant_23_7 rd wg lam)
    (_hmu_le_phi : BruhatLE_23_7 rd mu phi)
    (_hphi_le_lam : BruhatLE_23_7 rd phi lam) :
    B.normSq (lam - phi) ≤ B.normSq (lam - mu) := by sorry

theorem lemma_23_4_ii_extracted [LinearOrder R]
    (B : BilinFormData_23_7 wg)
    (lam phi mu : Δ.𝔥 →ₗ[R] R)
    (_hlam_dom : IsDominant_23_7 rd wg lam)
    (_hmu_le_phi : BruhatLE_23_7 rd mu phi)
    (_hphi_le_lam : BruhatLE_23_7 rd phi lam)
    (_hnorm_eq : B.normSq (lam - phi) = B.normSq (lam - mu)) :
    ∃ (w : wg.W), w ∈ WeylStabilizer_23_7 wg lam ∧
      wg.dualAction w phi = mu := by sorry

theorem support_in_xi0
    (S : SupportData_23_7 wg)
    (mu lam : Δ.𝔥 →ₗ[R] R)
    (_h_in_S : (mu, lam) ∈ S.support) :
    IsInXi0_23_7 rd mu lam := by sorry

theorem support_decomposition
    (S : SupportData_23_7 wg)
    (lam : Δ.𝔥 →ₗ[R] R)
    (p : (Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R))
    (_hp : p ∈ S.support)

    (_hblock : ∀ q ∈ S.support, ∃ w : wg.W, q.2 = wg.dualAction w lam) :
    ∃ (w : wg.W) (phi : Δ.𝔥 →ₗ[R] R),
      (phi, lam) ∈ S.support ∧
      p = (wg.dualAction w phi, wg.dualAction w lam) := by sorry

theorem theorem_20_13_upper_bound
    (S : SupportData_23_7 wg)
    (lam phi : Δ.𝔥 →ₗ[R] R)
    (_h_in_S : (phi, lam) ∈ S.support) :
    BruhatLE_23_7 rd phi lam := by sorry

theorem lemma_23_7_maximal_support [LinearOrder R] [IsStrictOrderedRing R]
    (B : BilinFormData_23_7 wg)
    (S : SupportData_23_7 wg)
    (mu lam : Δ.𝔥 →ₗ[R] R)

    (hlam_dom : IsDominant_23_7 rd wg lam)

    (hmu_in_S : (mu, lam) ∈ S.support)

    (hmu_max : ∀ q ∈ S.support, B.normSq (q.2 - q.1) ≤ B.normSq (lam - mu))

    (hblock : ∀ q ∈ S.support, ∃ w : wg.W, q.2 = wg.dualAction w lam) :

    maximalSupport_23_7 B S = WeylOrbitPair_23_7 wg mu lam ∧

    IsProperRep_23_7 rd wg mu lam := by

  have hmu_in_max : (mu, lam) ∈ maximalSupport_23_7 B S := ⟨hmu_in_S, hmu_max⟩
  constructor
  ·
    ext p
    simp only [maximalSupport_23_7, WeylOrbitPair_23_7, Set.mem_setOf_eq]
    constructor
    ·
      intro ⟨hp_supp, hp_max⟩

      obtain ⟨w, phi, hphi_supp, hp_eq⟩ :=
        support_decomposition wg S lam p hp_supp hblock

      have hmu_le_phi : BruhatLE_23_7 rd mu phi :=
        theorem_20_13_bruhat_lower_bound rd wg S mu lam phi hmu_in_S hphi_supp

      have hphi_le_lam : BruhatLE_23_7 rd phi lam :=
        theorem_20_13_upper_bound rd wg S lam phi hphi_supp

      have hnorm_le : B.normSq (lam - phi) ≤ B.normSq (lam - mu) :=
        lemma_23_4_i_extracted rd wg B lam phi mu hlam_dom hmu_le_phi hphi_le_lam

      have hnorm_ge : B.normSq (lam - mu) ≤ B.normSq (p.2 - p.1) :=
        hp_max (mu, lam) hmu_in_S

      have hnorm_eq_p : B.normSq (p.2 - p.1) = B.normSq (lam - phi) := by
        subst hp_eq

        exact B.normSq_sub_weyl_invariant w lam phi

      have hnorm_eq : B.normSq (lam - phi) = B.normSq (lam - mu) :=
        le_antisymm hnorm_le (hnorm_eq_p ▸ hnorm_ge)

      obtain ⟨w₁, hw₁_stab, hw₁_act⟩ :=
        lemma_23_4_ii_extracted rd wg B lam phi mu hlam_dom hmu_le_phi hphi_le_lam hnorm_eq


      refine ⟨w * w₁⁻¹, ?_⟩
      rw [hp_eq]


      have hphi_eq : phi = wg.dualAction w₁⁻¹ mu := by
        have h := hw₁_act

        calc phi = wg.dualAction 1 phi := (wg.dualAction_one phi).symm
          _ = wg.dualAction (w₁⁻¹ * w₁) phi := by rw [inv_mul_cancel]
          _ = wg.dualAction w₁⁻¹ (wg.dualAction w₁ phi) := wg.dualAction_mul w₁⁻¹ w₁ phi
          _ = wg.dualAction w₁⁻¹ mu := by rw [h]
      have hw₁_fix_lam : wg.dualAction w₁ lam = lam := hw₁_stab
      have hw₁_inv_fix : wg.dualAction w₁⁻¹ lam = lam := by
        calc wg.dualAction w₁⁻¹ lam
            = wg.dualAction w₁⁻¹ (wg.dualAction w₁ lam) := by rw [hw₁_fix_lam]
          _ = wg.dualAction (w₁⁻¹ * w₁) lam := (wg.dualAction_mul w₁⁻¹ w₁ lam).symm
          _ = wg.dualAction 1 lam := by rw [inv_mul_cancel]
          _ = lam := wg.dualAction_one lam
      exact Prod.ext
        (by rw [hphi_eq, ← wg.dualAction_mul w w₁⁻¹ mu])
        (by rw [wg.dualAction_mul w w₁⁻¹ lam, hw₁_inv_fix])
    ·
      intro ⟨w, hp_eq⟩
      rw [hp_eq]
      constructor
      ·
        exact S.weyl_equivariant w (mu, lam) hmu_in_S
      ·
        intro q hq


        calc B.normSq (q.2 - q.1) ≤ B.normSq (lam - mu) := hmu_max q hq
          _ = B.normSq (wg.dualAction w lam - wg.dualAction w mu) :=
              (B.normSq_sub_weyl_invariant w lam mu).symm
  ·
    exact {
      lam_dominant := hlam_dom
      in_xi0 := support_in_xi0 rd wg S mu lam hmu_in_S
      mu_minimal := by


        intro w hw_stab
        have hwmu_in_S : (wg.dualAction w mu, lam) ∈ S.support := by
          have h := S.weyl_equivariant w (mu, lam) hmu_in_S


          rwa [hw_stab] at h
        exact theorem_20_13_bruhat_lower_bound rd wg S mu lam
          (wg.dualAction w mu) hmu_in_S hwmu_in_S
    }

end
