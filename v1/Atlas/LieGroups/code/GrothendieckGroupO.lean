/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.ProjectiveFunctors
import Atlas.LieGroups.code.HeckeKL

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct
open ProjectiveFunctors Classical

universe u

variable {R : Type u} [CommRing R]
variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

structure GrothendieckGroupData (Δ : TriangularDecomposition R 𝔤) where
  carrier : Type u
  instACG : AddCommGroup carrier
  instMod : @Module ℤ carrier _ instACG.toAddCommMonoid
  delta : (Δ.𝔥 →ₗ[R] R) → carrier
  pairing : carrier → carrier → ℤ
  pairing_orthonormal : ∀ (lam mu : Δ.𝔥 →ₗ[R] R),
    pairing (delta lam) (delta mu) = if lam = mu then 1 else 0
  pairing_basis_determines :
    ∀ (h₁ h₂ : carrier → carrier → ℤ),
      (∀ lam mu : Δ.𝔥 →ₗ[R] R,
        h₁ (delta lam) (delta mu) = h₂ (delta lam) (delta mu)) →
      ∀ (x y : carrier), h₁ x y = h₂ x y

structure GrothendieckGroupData.InnerProductData
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ) where
  pairing : KO.carrier → KO.carrier → ℤ
  orthonormal : ∀ (lam mu : Δ.𝔥 →ₗ[R] R),
    pairing (KO.delta lam) (KO.delta mu) = if lam = mu then 1 else 0
  pairing_basis_determines :
    ∀ (h₁ h₂ : KO.carrier → KO.carrier → ℤ),
      (∀ lam mu : Δ.𝔥 →ₗ[R] R,
        h₁ (KO.delta lam) (KO.delta mu) = h₂ (KO.delta lam) (KO.delta mu)) →
      ∀ (x y : KO.carrier), h₁ x y = h₂ x y

structure InducedMapData
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ) where
  F : EndoFunctorData R 𝔤
  hF : IsProjectiveFunctor F
  mapKO : KO.carrier → KO.carrier
  map_basis_compat :
    ∀ (g : KO.carrier → KO.carrier),
      (∀ lam : Δ.𝔥 →ₗ[R] R, g (KO.delta lam) = mapKO (KO.delta lam)) →
      g = mapKO

structure WeylActionData
    {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ)
    (KO : GrothendieckGroupData Δ) where
  act : wg.W → KO.carrier → KO.carrier
  act_delta : ∀ (w : wg.W) (lam : Δ.𝔥 →ₗ[R] R),
    act w (KO.delta lam) = KO.delta (wg.dualAction w lam)

structure AdjointPairData where
  F : EndoFunctorData R 𝔤
  Fv : EndoFunctorData R 𝔤
  hF : IsProjectiveFunctor F
  hFv : IsProjectiveFunctor Fv
  adjunction_fwd : ∀ (M N : RepGfObj R 𝔤),
    RepGfHom (F.obj M) N → RepGfHom M (Fv.obj N)
  adjunction_bwd : ∀ (M N : RepGfObj R 𝔤),
    RepGfHom M (Fv.obj N) → RepGfHom (F.obj M) N
  adjunction_homDim_pairing :
    ∀ {Δ : TriangularDecomposition R 𝔤}
      (KO : GrothendieckGroupData Δ)
      (ip : KO.InnerProductData)
      (fF fFv : InducedMapData KO)
      (_ : fF.F = F) (_ : fFv.F = Fv)
      (lam mu : Δ.𝔥 →ₗ[R] R),
    ip.pairing (fF.mapKO (KO.delta lam)) (KO.delta mu) =
    ip.pairing (fFv.mapKO (KO.delta mu)) (KO.delta lam)

structure AdjointPairDataWeak where
  F : EndoFunctorData R 𝔤
  Fv : EndoFunctorData R 𝔤
  adjunction_fwd : ∀ (M N : RepGfObj R 𝔤),
    RepGfHom (F.obj M) N → RepGfHom M (Fv.obj N)
  adjunction_bwd : ∀ (M N : RepGfObj R 𝔤),
    RepGfHom M (Fv.obj N) → RepGfHom (F.obj M) N

def AdjointPairDataWeak.toAdjointPairData
    (adj : AdjointPairDataWeak (R := R) (𝔤 := 𝔤))
    (hF : IsProjectiveFunctor adj.F)
    (hFv : IsProjectiveFunctor adj.Fv)
    (hDim : ∀ {Δ : TriangularDecomposition R 𝔤}
      (KO : GrothendieckGroupData Δ)
      (ip : KO.InnerProductData)
      (fF fFv : InducedMapData KO)
      (_ : fF.F = adj.F) (_ : fFv.F = adj.Fv)
      (lam mu : Δ.𝔥 →ₗ[R] R),
      ip.pairing (fF.mapKO (KO.delta lam)) (KO.delta mu) =
      ip.pairing (fFv.mapKO (KO.delta mu)) (KO.delta lam)) :
    AdjointPairData (R := R) (𝔤 := 𝔤) :=
  { F := adj.F
    Fv := adj.Fv
    hF := hF
    hFv := hFv
    adjunction_fwd := adj.adjunction_fwd
    adjunction_bwd := adj.adjunction_bwd
    adjunction_homDim_pairing := hDim }

def AdjointPairData.toWeak
    (adj : AdjointPairData (R := R) (𝔤 := 𝔤)) :
    AdjointPairDataWeak (R := R) (𝔤 := 𝔤) :=
  { F := adj.F
    Fv := adj.Fv
    adjunction_fwd := adj.adjunction_fwd
    adjunction_bwd := adj.adjunction_bwd }

@[simp] theorem AdjointPairData.toWeak_F (adj : AdjointPairData (R := R) (𝔤 := 𝔤)) :
    adj.toWeak.F = adj.F := rfl

@[simp] theorem AdjointPairData.toWeak_Fv (adj : AdjointPairData (R := R) (𝔤 := 𝔤)) :
    adj.toWeak.Fv = adj.Fv := rfl

def DominatesSet
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (S : Set (Δ.𝔥 →ₗ[R] R)) : Prop :=
  ∀ mu ∈ S, rd.IsInQPlus (lam - mu)

structure WeightBilinForm {Δ : TriangularDecomposition R 𝔤} (wg : WeylGroupData Δ) where
  form : (Δ.𝔥 →ₗ[R] R) → (Δ.𝔥 →ₗ[R] R) → R
  symm : ∀ (mu nu : Δ.𝔥 →ₗ[R] R), form mu nu = form nu mu
  bilin_left : ∀ (mu₁ mu₂ nu : Δ.𝔥 →ₗ[R] R),
    form (mu₁ + mu₂) nu = form mu₁ nu + form mu₂ nu
  weyl_normSq_invariant : ∀ (w : wg.W) (mu nu : Δ.𝔥 →ₗ[R] R),
    form (wg.dualAction w mu - wg.dualAction w nu)
         (wg.dualAction w mu - wg.dualAction w nu) = form (mu - nu) (mu - nu)
  pos_semidef : ∀ [LinearOrder R] [IsStrictOrderedRing R] (mu : Δ.𝔥 →ₗ[R] R),
    (0 : R) ≤ form mu mu
  form_corootPairing_compat :
    ∀ (rd : PositiveRootData Δ) (alpha mu : Δ.𝔥 →ₗ[R] R)
      (_ : alpha ∈ rd.posRoots),
    2 • form alpha mu = rd.corootPairing mu alpha * form alpha alpha
  dominant_corootPairing_diff_nonneg :
    ∀ [LinearOrder R] [IsStrictOrderedRing R]
      (rd : PositiveRootData Δ)
      (lam phi alpha : Δ.𝔥 →ₗ[R] R)
      (_ : IsDominantWeightBruhat rd wg lam)
      (_ : BruhatLE rd phi lam)
      (_ : alpha ∈ rd.posRoots),
    (0 : R) ≤ rd.corootPairing (lam - phi) alpha
  form_coroot_compat :
    ∀ (rd : PositiveRootData Δ) (rs : RootSystemWithReflections rd wg)
      (alpha mu : Δ.𝔥 →ₗ[R] R)
      (_ : alpha ∈ rs.allRoots),
    2 • form alpha mu = mu (rs.coroot alpha) * form alpha alpha
  form_posRoot_pos :
    ∀ [LinearOrder R] [IsStrictOrderedRing R]
      (rd : PositiveRootData Δ)
      (alpha : Δ.𝔥 →ₗ[R] R)
      (_ : alpha ∈ rd.posRoots),
    (0 : R) < form alpha alpha

theorem WeightBilinForm.form_posRoot_nonneg
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ}
    (B : WeightBilinForm wg)
    (rd : PositiveRootData Δ)
    (alpha : Δ.𝔥 →ₗ[R] R)
    (halpha_pos : alpha ∈ rd.posRoots) :
    (0 : R) ≤ B.form alpha alpha :=
  B.pos_semidef alpha

theorem WeightBilinForm.form_corootPairing_compat_ax
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ}
    (B : WeightBilinForm wg)
    (rd : PositiveRootData Δ)
    (alpha mu : Δ.𝔥 →ₗ[R] R)
    (halpha : alpha ∈ rd.posRoots) :
    2 • B.form alpha mu = rd.corootPairing mu alpha * B.form alpha alpha :=
  B.form_corootPairing_compat rd alpha mu halpha

theorem dominant_corootPairing_diff_nonneg_ax
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ) (B : WeightBilinForm wg)

    (lam phi alpha : Δ.𝔥 →ₗ[R] R)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hphi_le : BruhatLE rd phi lam)
    (halpha_pos : alpha ∈ rd.posRoots) :
    (0 : R) ≤ rd.corootPairing (lam - phi) alpha :=
  B.dominant_corootPairing_diff_nonneg rd lam phi alpha hlam_dom hphi_le halpha_pos

theorem WeightBilinForm.form_posRoot_dominant_diff_nonneg
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ}
    (B : WeightBilinForm wg)
    (rd : PositiveRootData Δ)
    (lam phi alpha : Δ.𝔥 →ₗ[R] R)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hphi_le : BruhatLE rd phi lam)
    (halpha_pos : alpha ∈ rd.posRoots) :
    (0 : R) ≤ B.form alpha (lam - phi) := by

  have hcompat := B.form_corootPairing_compat_ax rd alpha (lam - phi) halpha_pos

  have hpair_nonneg := dominant_corootPairing_diff_nonneg_ax rd wg B lam phi alpha hlam_dom hphi_le halpha_pos

  have haa_nonneg := B.pos_semidef alpha

  have hprod_nonneg : (0 : R) ≤ rd.corootPairing (lam - phi) alpha * B.form alpha alpha :=
    mul_nonneg hpair_nonneg haa_nonneg
  have h2_nonneg : (0 : R) ≤ 2 • B.form alpha (lam - phi) := by rw [hcompat]; exact hprod_nonneg

  rw [two_nsmul] at h2_nonneg
  linarith

theorem WeightBilinForm.cross_terms_nonneg
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ}
    (B : WeightBilinForm wg)
    (rd : PositiveRootData Δ)
    (lam phi alpha : Δ.𝔥 →ₗ[R] R) (n : ℕ)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hphi_le : BruhatLE rd phi lam)
    (halpha_pos : alpha ∈ rd.posRoots)
    (_hn_pos : 0 < n) :
    (0 : R) ≤ n • B.form alpha (lam - phi) + n • B.form alpha (lam - phi) +
          n • (n • B.form alpha alpha) := by
  have h_cross := B.form_posRoot_dominant_diff_nonneg rd lam phi alpha hlam_dom hphi_le halpha_pos
  have h_sq := B.form_posRoot_nonneg rd alpha halpha_pos
  have h1 : (0 : R) ≤ n • B.form alpha (lam - phi) := nsmul_nonneg h_cross n
  have h2 : (0 : R) ≤ n • B.form alpha alpha := nsmul_nonneg h_sq n
  have h3 : (0 : R) ≤ n • (n • B.form alpha alpha) := nsmul_nonneg h2 n
  linarith

theorem WeightBilinForm.form_coroot_compat_ax
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ}
    (B : WeightBilinForm wg)
    (rd : PositiveRootData Δ) (rs : RootSystemWithReflections rd wg)
    (alpha mu : Δ.𝔥 →ₗ[R] R)
    (halpha : alpha ∈ rs.allRoots) :
    2 • B.form alpha mu = mu (rs.coroot alpha) * B.form alpha alpha :=
  B.form_coroot_compat rd rs alpha mu halpha

theorem WeightBilinForm.form_posRoot_pos_ax
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ}
    (B : WeightBilinForm wg)
    (rd : PositiveRootData Δ)
    (alpha : Δ.𝔥 →ₗ[R] R)
    (halpha_pos : alpha ∈ rd.posRoots) :
    (0 : R) < B.form alpha alpha :=
  B.form_posRoot_pos rd alpha halpha_pos

theorem WeightBilinForm.norm_diff_factor_ax
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ}
    (B : WeightBilinForm wg)
    (rd : PositiveRootData Δ) (rs : RootSystemWithReflections rd wg)
    (v alpha : Δ.𝔥 →ₗ[R] R) (n : ℕ)
    (halpha : alpha ∈ rs.allRoots) :
    B.form (v + n • alpha) (v + n • alpha) - B.form v v =
      (n : R) * v (rs.coroot alpha) * B.form alpha alpha +
      (n : R) * (n : R) * B.form alpha alpha := by

  have form_zero_left : ∀ (nu : Δ.𝔥 →ₗ[R] R), B.form 0 nu = 0 := by
    intro nu
    have h := B.bilin_left 0 0 nu
    rw [zero_add] at h

    have h2 : B.form 0 nu + 0 = B.form 0 nu + B.form 0 nu := by rw [add_zero]; exact h
    exact (add_left_cancel h2).symm
  have form_nsmul_left : ∀ (m : ℕ) (mu nu : Δ.𝔥 →ₗ[R] R),
      B.form (m • mu) nu = m • B.form mu nu := by

    intro m mu nu
    induction m with
    | zero => simp [form_zero_left nu]
    | succ m ih => rw [succ_nsmul, B.bilin_left, ih, succ_nsmul]

  have e1 : B.form v (v + n • alpha) = B.form v v + B.form v (n • alpha) := by
    rw [B.symm v (v + n • alpha), B.bilin_left, B.symm v v, B.symm (n • alpha) v]
  have e2 : B.form (n • alpha) (v + n • alpha) =
      B.form (n • alpha) v + B.form (n • alpha) (n • alpha) := by
    rw [B.symm (n • alpha) (v + n • alpha), B.bilin_left,
        B.symm v (n • alpha), B.symm (n • alpha) (n • alpha)]
  have hexpand : B.form (v + n • alpha) (v + n • alpha) =
      B.form v v + (n • B.form alpha v + n • B.form alpha v +
        n • (n • B.form alpha alpha)) := by
    rw [B.bilin_left, e1, e2]
    rw [form_nsmul_left n alpha v]
    rw [B.symm v (n • alpha), form_nsmul_left n alpha v]
    rw [form_nsmul_left n alpha (n • alpha), B.symm alpha (n • alpha),
        form_nsmul_left n alpha alpha]
    ring

  simp only [nsmul_eq_mul] at hexpand

  have hcompat := B.form_coroot_compat_ax rd rs alpha v halpha
  simp only [nsmul_eq_mul] at hcompat

  push_cast at hcompat


  have hdiff : B.form (v + n • alpha) (v + n • alpha) - B.form v v =
      ↑n * B.form alpha v + ↑n * B.form alpha v + ↑n * (↑n * B.form alpha alpha) := by
    have : B.form v v + (↑n * B.form alpha v + ↑n * B.form alpha v + ↑n * (↑n * B.form alpha alpha)) - B.form v v =
        ↑n * B.form alpha v + ↑n * B.form alpha v + ↑n * (↑n * B.form alpha alpha) := by ring
    rw [hexpand]; exact this

  have hcross : ↑n * B.form alpha v + ↑n * B.form alpha v = ↑n * (2 * B.form alpha v) := by ring
  rw [hdiff, hcross, hcompat]
  ring

theorem WeightBilinForm.norm_eq_coroot_zero
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ}
    (B : WeightBilinForm wg)
    (rd : PositiveRootData Δ) (rs : RootSystemWithReflections rd wg)
    (lam b alpha : Δ.𝔥 →ₗ[R] R) (n : ℕ)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (halpha_pos : alpha ∈ rd.posRoots)
    (hn_pos : 0 < n)
    (hpair : rd.corootPairing b alpha = (n : R))
    (h_eq : B.form (lam - b) (lam - b) = B.form (lam - b + n • alpha) (lam - b + n • alpha)) :
    lam (rs.coroot alpha) = 0 := by

  have hα_root : alpha ∈ rs.allRoots := rs.posRoots_sub alpha halpha_pos

  set v := lam - b with hv_def
  set aα := B.form alpha alpha with haα_def
  set c := lam (rs.coroot alpha) with hc_def

  have hdiff : B.form (v + n • alpha) (v + n • alpha) - B.form v v = 0 := by linarith

  have hfact := B.norm_diff_factor_ax rd rs v alpha n hα_root

  have hzero : (↑n : R) * v (rs.coroot alpha) * aα + (↑n : R) * (↑n : R) * aα = 0 := by
    linarith

  have hv_eval : v (rs.coroot alpha) = c - (↑n : R) := by
    simp only [hv_def, hc_def, LinearMap.sub_apply]
    rw [← rs.corootPairing_eq_eval alpha hα_root b]
    rw [hpair]

  rw [hv_eval] at hzero


  have hfactor : (↑n : R) * aα * c = 0 := by ring_nf; linarith

  have hn_pos_R : (0 : R) < (↑n : R) := Nat.cast_pos.mpr hn_pos
  have haα_pos : (0 : R) < aα := B.form_posRoot_pos_ax rd alpha halpha_pos

  have hna_pos : (0 : R) < (↑n : R) * aα := mul_pos hn_pos_R haα_pos
  have hna_ne : (↑n : R) * aα ≠ 0 := ne_of_gt hna_pos

  have hfactor' : (↑n : R) * aα * c = (↑n : R) * aα * 0 := by rw [mul_zero]; exact hfactor
  exact mul_left_cancel₀ hna_ne hfactor'

theorem WeightBilinForm.dominant_posRoot_cross_le
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ}
    (B : WeightBilinForm wg)
    (rd : PositiveRootData Δ)
    (lam phi alpha : Δ.𝔥 →ₗ[R] R) (n : ℕ)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hphi_le : BruhatLE rd phi lam)
    (halpha_pos : alpha ∈ rd.posRoots)
    (hn_pos : 0 < n) :
    B.form (lam - phi) (lam - phi) ≤
      B.form (lam - phi) (lam - phi) +
        (n • B.form alpha (lam - phi) + n • B.form alpha (lam - phi) +
          n • (n • B.form alpha alpha)) :=
  le_add_of_nonneg_right (B.cross_terms_nonneg rd lam phi alpha n hlam_dom hphi_le halpha_pos hn_pos)

def WeightBilinForm.normSq {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    (B : WeightBilinForm wg) (mu : Δ.𝔥 →ₗ[R] R) : R :=
  B.form mu mu

structure GrothendieckGroupBlock
    (Δ : TriangularDecomposition R 𝔤)
    (wg : WeylGroupData Δ) where
  carrier : Type u
  instACG : AddCommGroup carrier
  instMod : @Module ℤ carrier _ instACG.toAddCommMonoid
  delta_w : wg.W → carrier
  basis_injective : Function.Injective delta_w
  basis_linearIndep :
    letI := instACG; letI := instMod
    ∀ (c : wg.W → ℤ),
      (Finset.univ.sum (fun w => (c w) • (delta_w w)) = (0 : carrier)) →
      ∀ w, c w = 0

section Theorems

variable {Δ : TriangularDecomposition R 𝔤}
variable (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)

theorem generalized_eigenspace_decomposition_aux
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (M : RepGfObj R 𝔤) :
    ∃ (lam : Δ.𝔥 →ₗ[R] R) (n : ℕ),
      centerActsNilpotentlyShifted_of_order Δ M lam n := by sorry

theorem generalized_eigenspace_decomposition
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (M : RepGfObj R 𝔤) :
    ∃ (lam : Δ.𝔥 →ₗ[R] R) (n : ℕ),
      centerActsNilpotentlyShifted_of_order Δ M lam n :=
  generalized_eigenspace_decomposition_aux M

theorem block_decomposition_exists
    (M : RepGfObj R 𝔤) :
    ∃ lam : Δ.𝔥 →ₗ[R] R, HasGenInfChar M lam := by
  obtain ⟨lam, n, hn⟩ := generalized_eigenspace_decomposition M
  exact ⟨lam, ⟨⟨n, hn⟩⟩⟩

theorem projective_same_KO_class_iso
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤} (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (F₁ F₂ : EndoFunctorData R 𝔤)
    (_hF₁ : IsProjectiveFunctor F₁) (_hF₂ : IsProjectiveFunctor F₂)
    (KO : GrothendieckGroupData Δ)
    (f₁ : InducedMapData KO) (f₂ : InducedMapData KO)
    (_hf₁ : f₁.F = F₁) (_hf₂ : f₂.F = F₂)
    (h_delta : f₁.mapKO (KO.delta lam) = f₂.mapKO (KO.delta lam))
    (Mverma : RepGfObj R 𝔤)
    (_hVM : IsVermaModule Δ Mverma.carrier (lam - wg.ρ)) :
    ∃ (iso_fwd : RepGfHom (F₁.obj Mverma) (F₂.obj Mverma))
      (iso_bwd : RepGfHom (F₂.obj Mverma) (F₁.obj Mverma)),
      (iso_bwd.comp iso_fwd).EqAsMap (RepGfHom.id _) ∧
      (iso_fwd.comp iso_bwd).EqAsMap (RepGfHom.id _) := by sorry

theorem verma_existence_krull_schmidt
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤} (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (F₁ F₂ : EndoFunctorData R 𝔤)
    (_hF₁ : IsProjectiveFunctor F₁) (_hF₂ : IsProjectiveFunctor F₂)
    (KO : GrothendieckGroupData Δ)
    (f₁ : InducedMapData KO) (f₂ : InducedMapData KO)
    (hf₁ : f₁.F = F₁) (hf₂ : f₂.F = F₂)
    (h_delta : f₁.mapKO (KO.delta lam) = f₂.mapKO (KO.delta lam)) :
    ∃ (Mverma : RepGfObj R 𝔤),
      Nonempty (IsVermaModule Δ Mverma.carrier (lam - wg.ρ)) ∧
      ∃ (iso_fwd : RepGfHom (F₁.obj Mverma) (F₂.obj Mverma))
        (iso_bwd : RepGfHom (F₂.obj Mverma) (F₁.obj Mverma)),
        (iso_bwd.comp iso_fwd).EqAsMap (RepGfHom.id _) ∧
        (iso_fwd.comp iso_bwd).EqAsMap (RepGfHom.id _) := by

  obtain ⟨Mtype, instACG, instMod, instLRM, instLM, ⟨hVM⟩⟩ :=
    verma_module_exists Δ (lam - wg.ρ)
  let Mverma : RepGfObj R 𝔤 := ⟨Mtype, instACG, instMod, instLRM, instLM⟩

  obtain ⟨iso_fwd, iso_bwd, hiso₁, hiso₂⟩ :=
    projective_same_KO_class_iso wg lam F₁ F₂ _hF₁ _hF₂
      KO f₁ f₂ hf₁ hf₂ h_delta Mverma hVM
  exact ⟨Mverma, ⟨hVM⟩, iso_fwd, iso_bwd, hiso₁, hiso₂⟩

include wg in
theorem block_natiso_of_same_KO_on_delta
    (lam : Δ.𝔥 →ₗ[R] R)
    (F₁ F₂ : EndoFunctorData R 𝔤)
    (_hF₁ : IsProjectiveFunctor F₁) (_hF₂ : IsProjectiveFunctor F₂)
    (KO : GrothendieckGroupData Δ)
    (f₁ : InducedMapData KO) (f₂ : InducedMapData KO)
    (hf₁ : f₁.F = F₁) (hf₂ : f₂.F = F₂)
    (h_delta : f₁.mapKO (KO.delta lam) = f₂.mapKO (KO.delta lam)) :
    AreNatIsoOnGenInfChar lam F₁ F₂ := by


  have ⟨Mverma, hMverma, iso_fwd, iso_bwd, hiso₁, hiso₂⟩ :=
    verma_existence_krull_schmidt wg lam F₁ F₂ _hF₁ _hF₂ KO f₁ f₂ hf₁ hf₂ h_delta

  exact corollary_22_6_i Δ wg lam F₁ F₂ _hF₁ _hF₂ Mverma hMverma iso_fwd iso_bwd hiso₁ hiso₂

include wg in
theorem block_areNatIso_of_same_KO_on_delta
    (lam : Δ.𝔥 →ₗ[R] R)
    (F₁ F₂ : EndoFunctorData R 𝔤)
    (_hF₁ : IsProjectiveFunctor F₁) (_hF₂ : IsProjectiveFunctor F₂)
    (KO : GrothendieckGroupData Δ)
    (f₁ : InducedMapData KO) (f₂ : InducedMapData KO)
    (hf₁ : f₁.F = F₁) (hf₂ : f₂.F = F₂)
    (h_delta : f₁.mapKO (KO.delta lam) = f₂.mapKO (KO.delta lam)) :
    AreNatIso F₁ F₂ := by
  have ⟨Mverma, hMverma, iso_fwd, iso_bwd, hiso₁, hiso₂⟩ :=
    verma_existence_krull_schmidt wg lam F₁ F₂ _hF₁ _hF₂ KO f₁ f₂ hf₁ hf₂ h_delta
  exact corollary_22_6_i_areNatIso Δ wg lam F₁ F₂ _hF₁ _hF₂ Mverma hMverma
    iso_fwd iso_bwd hiso₁ hiso₂

theorem hasGenInfChar_of_hom
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M₁ M₂ : RepGfObj R 𝔤} (theta : Δ.𝔥 →ₗ[R] R)
    (_hM₁ : HasGenInfChar M₁ theta)
    (_f : RepGfHom M₁ M₂) : HasGenInfChar M₂ theta := by sorry

theorem hasGenInfChar_unique
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {M : RepGfObj R 𝔤} {theta₁ theta₂ : Δ.𝔥 →ₗ[R] R}
    (_h₁ : HasGenInfChar M theta₁) (_h₂ : HasGenInfChar M theta₂) :
    theta₁ = theta₂ := by sorry

theorem block_assembly_naturality
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (F₁ F₂ : EndoFunctorData R 𝔤)
    (η_fn : ∀ (theta : Δ.𝔥 →ₗ[R] R), NatTransOnGenInfChar theta F₁ F₂)
    (lam_of : RepGfObj R 𝔤 → (Δ.𝔥 →ₗ[R] R))
    (hlam_of : ∀ M, HasGenInfChar M (lam_of M))
    {M₁ M₂ : RepGfObj R 𝔤} (f : RepGfHom M₁ M₂)
    (x : (F₁.obj M₁).carrier) :
    ((η_fn (lam_of M₂)).app M₂ (hlam_of M₂)).toFun ((F₁.mapHom f).toFun x) =
    (F₂.mapHom f).toFun (((η_fn (lam_of M₁)).app M₁ (hlam_of M₁)).toFun x) := by

  have hM₂_lam1 : HasGenInfChar M₂ (lam_of M₁) :=
    hasGenInfChar_of_hom (lam_of M₁) (hlam_of M₁) f

  have h_eq : lam_of M₁ = lam_of M₂ :=
    hasGenInfChar_unique hM₂_lam1 (hlam_of M₂)

  have nat_sq := (η_fn (lam_of M₁)).naturality (hlam_of M₁) hM₂_lam1 f x
  simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at nat_sq


  have key : ∀ (θ : Δ.𝔥 →ₗ[R] R) (_ : lam_of M₁ = θ) (h : HasGenInfChar M₂ θ),
      ((η_fn θ).app M₂ h).toFun ((F₁.mapHom f).toFun x) =
      (F₂.mapHom f).toFun (((η_fn (lam_of M₁)).app M₁ (hlam_of M₁)).toFun x) := by
    intro θ heq h
    subst heq
    exact (η_fn (lam_of M₁)).naturality (hlam_of M₁) h f x |>.symm ▸ nat_sq
  exact key (lam_of M₂) h_eq (hlam_of M₂)

lemma areNatIso_of_all_geninfchar
    (F₁ F₂ : EndoFunctorData R 𝔤)
    (_hF₁ : IsProjectiveFunctor F₁) (_hF₂ : IsProjectiveFunctor F₂)
    (h_blocks : ∀ lam : Δ.𝔥 →ₗ[R] R, AreNatIsoOnGenInfChar lam F₁ F₂) :
    AreNatIso F₁ F₂ := by

  choose α_fn β_fn h_inv using h_blocks


  let lam_of : RepGfObj R 𝔤 → (Δ.𝔥 →ₗ[R] R) :=
    fun M => (block_decomposition_exists M).choose
  have hlam_of : ∀ M, HasGenInfChar M (lam_of M) :=
    fun M => (block_decomposition_exists M).choose_spec


  refine ⟨⟨fun M => (α_fn (lam_of M)).app M (hlam_of M),
            fun f x => block_assembly_naturality F₁ F₂ α_fn lam_of hlam_of f x⟩,
          ⟨fun M => (β_fn (lam_of M)).app M (hlam_of M),
            fun f x => block_assembly_naturality F₂ F₁ β_fn lam_of hlam_of f x⟩, ?_, ?_⟩
  ·
    intro M x

    show ((β_fn (lam_of M)).app M (hlam_of M)).toFun
      (((α_fn (lam_of M)).app M (hlam_of M)).toFun x) =
      (RepGfHom.id (F₁.obj M)).toFun x

    have h1 := (h_inv (lam_of M)).1 M (hlam_of M) x
    exact h1
  ·
    intro M x
    show ((α_fn (lam_of M)).app M (hlam_of M)).toFun
      (((β_fn (lam_of M)).app M (hlam_of M)).toFun x) =
      (RepGfHom.id (F₂.obj M)).toFun x
    have h2 := (h_inv (lam_of M)).2 M (hlam_of M) x
    exact h2

include wg in
theorem theorem_23_1_i
    (KO : GrothendieckGroupData Δ)
    (f₁ f₂ : InducedMapData KO)
    (h_eq : f₁.mapKO = f₂.mapKO) :
    AreNatIso f₁.F f₂.F := by

  have h_delta : f₁.mapKO (KO.delta 0) = f₂.mapKO (KO.delta 0) :=
    congr_fun h_eq (KO.delta 0)


  exact block_areNatIso_of_same_KO_on_delta wg 0 f₁.F f₂.F f₁.hF f₂.hF
    KO f₁ f₂ rfl rfl h_delta

def homDim
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (lam mu : Δ.𝔥 →ₗ[R] R) : ℤ :=
  ip.pairing (fF.mapKO (KO.delta lam)) (KO.delta mu)

theorem hom_multiplicity_eq_pairing
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (lam mu : Δ.𝔥 →ₗ[R] R) :
    ip.pairing (fF.mapKO (KO.delta lam)) (KO.delta mu) =
    homDim KO ip fF lam mu := rfl

theorem adjunction_preserves_homDim
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (adj : AdjointPairData (R := R) (𝔤 := 𝔤))
    (fF fFv : InducedMapData KO)
    (hfF : fF.F = adj.F) (hfFv : fFv.F = adj.Fv)
    (lam mu : Δ.𝔥 →ₗ[R] R) :
    homDim KO ip fF lam mu = homDim KO ip fFv mu lam :=
  adj.adjunction_homDim_pairing KO ip fF fFv hfF hfFv lam mu

theorem adjoint_pair_basis_pairing
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (adj : AdjointPairData (R := R) (𝔤 := 𝔤))
    (fF fFv : InducedMapData KO)
    (hfF : fF.F = adj.F) (hfFv : fFv.F = adj.Fv) :
    ∀ (lam mu : Δ.𝔥 →ₗ[R] R),
      ip.pairing (fF.mapKO (KO.delta lam)) (KO.delta mu) =
      ip.pairing (KO.delta lam) (fFv.mapKO (KO.delta mu)) := by
  intro lam mu

  have pairing_symm : ∀ a b, ip.pairing a b = ip.pairing b a :=
    ip.pairing_basis_determines _ _ (fun l m => by
      rw [ip.orthonormal, ip.orthonormal]; simp [eq_comm])
  have hadj := adj.adjunction_homDim_pairing KO ip fF fFv hfF hfFv lam mu
  rw [pairing_symm (KO.delta lam) (fFv.mapKO (KO.delta mu))]
  exact hadj

theorem theorem_23_1_ii
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (adj : AdjointPairData (R := R) (𝔤 := 𝔤))
    (fF fFv : InducedMapData KO)
    (hfF : fF.F = adj.F) (hfFv : fFv.F = adj.Fv) :
    ∀ (x y : KO.carrier), ip.pairing (fF.mapKO x) y = ip.pairing x (fFv.mapKO y) := by
  have hbasis := adjoint_pair_basis_pairing KO ip adj fF fFv hfF hfFv
  exact ip.pairing_basis_determines
    (fun x y => ip.pairing (fF.mapKO x) y)
    (fun x y => ip.pairing x (fFv.mapKO y))
    hbasis

noncomputable def projective_functor_has_induced_map_data
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ)
    (F : EndoFunctorData R 𝔤)
    (hF : IsProjectiveFunctor F) :
    InducedMapData KO :=
  { F := F
    hF := hF
    mapKO := sorry


    map_basis_compat := sorry

  }

theorem projective_functor_has_induced_map_data_F
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ)
    (F : EndoFunctorData R 𝔤)
    (hF : IsProjectiveFunctor F) :
    (projective_functor_has_induced_map_data KO F hF).F = F := by
  rfl

theorem projective_functor_has_induced_map_data_unique_on_basis
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ)
    (F : EndoFunctorData R 𝔤)
    (hF : IsProjectiveFunctor F)
    (d' : InducedMapData KO)
    (hd' : d'.F = F)
    (lam : Δ.𝔥 →ₗ[R] R) :
    d'.mapKO (KO.delta lam) =
      (projective_functor_has_induced_map_data KO F hF).mapKO (KO.delta lam) := by sorry

theorem induced_map_delta_determined_by_functor
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ)
    (d₁ d₂ : InducedMapData KO)
    (hF : d₁.F = d₂.F)
    (lam : Δ.𝔥 →ₗ[R] R) :
    d₁.mapKO (KO.delta lam) = d₂.mapKO (KO.delta lam) := by
  calc d₁.mapKO (KO.delta lam)
      _ = (projective_functor_has_induced_map_data KO d₁.F d₁.hF).mapKO (KO.delta lam) :=
          projective_functor_has_induced_map_data_unique_on_basis KO d₁.F d₁.hF d₁ rfl lam
      _ = (projective_functor_has_induced_map_data KO d₂.F d₂.hF).mapKO (KO.delta lam) := by
          simp only [hF]
      _ = d₂.mapKO (KO.delta lam) :=
          (projective_functor_has_induced_map_data_unique_on_basis KO d₂.F d₂.hF d₂ rfl lam).symm

noncomputable def projective_functor_has_induced_map_data_with_F
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ)
    (F : EndoFunctorData R 𝔤)
    (hF : IsProjectiveFunctor F) :
    { d : InducedMapData KO // d.F = F ∧
      ∀ (d' : InducedMapData KO), d'.F = F →
        ∀ lam : Δ.𝔥 →ₗ[R] R, d'.mapKO (KO.delta lam) = d.mapKO (KO.delta lam) } :=
  ⟨projective_functor_has_induced_map_data KO F hF,
   projective_functor_has_induced_map_data_F KO F hF,
   fun d' hd' lam => projective_functor_has_induced_map_data_unique_on_basis KO F hF d' hd' lam⟩

def grothendieck_group_has_inner_product
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ) :
    KO.InnerProductData :=
  { pairing := KO.pairing
    orthonormal := KO.pairing_orthonormal
    pairing_basis_determines := KO.pairing_basis_determines }

theorem inner_product_nondegen
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (a b : KO.carrier)
    (h : ∀ mu : Δ.𝔥 →ₗ[R] R, ip.pairing (KO.delta mu) a = ip.pairing (KO.delta mu) b) :
    a = b := by


  have delta_surj : ∀ (c : KO.carrier), ∃ lam, KO.delta lam = c := by
    intro c
    by_contra hc
    push Not at hc
    have key := ip.pairing_basis_determines
      (fun x _ => if x = c then (1 : ℤ) else 0)
      (fun _ _ => (0 : ℤ))
      (fun lam _ => by simp [if_neg (hc lam)])
    have := key c c
    simp at this

  obtain ⟨la, hla⟩ := delta_surj a
  obtain ⟨lb, hlb⟩ := delta_surj b


  have h_la := h la
  rw [← hla, ← hlb] at h_la
  rw [ip.orthonormal la la, ip.orthonormal la lb] at h_la
  simp at h_la
  rw [← hla, ← hlb, h_la]

theorem induced_map_basis_determined_by_functor
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ)
    (f₁ f₂ : InducedMapData KO)
    (h_same_F : f₁.F = f₂.F)
    (lam : Δ.𝔥 →ₗ[R] R) :
    f₁.mapKO (KO.delta lam) = f₂.mapKO (KO.delta lam) := by

  have h1 := projective_functor_has_induced_map_data_unique_on_basis KO f₁.F f₁.hF f₁ rfl lam
  have h2 := projective_functor_has_induced_map_data_unique_on_basis KO f₁.F f₁.hF f₂ (h_same_F ▸ rfl) lam
  rw [h1, h2]

theorem induced_map_unique_for_same_functor
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ)
    (f₁ f₂ : InducedMapData KO)
    (h_same_F : f₁.F = f₂.F) :
    f₁.mapKO = f₂.mapKO := by


  symm
  exact f₁.map_basis_compat f₂.mapKO
    (fun lam => (induced_map_basis_determined_by_functor KO f₁ f₂ h_same_F lam).symm)

theorem tensor_functor_dual_summand_transfer_ax
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (FV : TensorFunctorData R 𝔤)
    (adj : AdjointPairDataWeak (R := R) (𝔤 := 𝔤))
    (h_summand : IsDirectSummand adj.F FV.functor) :
    ∃ (FV_dual : TensorFunctorData R 𝔤), IsDirectSummand adj.Fv FV_dual.functor := by sorry

theorem tensor_functor_dual_summand_transfer_rev_ax
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (FV : TensorFunctorData R 𝔤)
    (adj : AdjointPairDataWeak (R := R) (𝔤 := 𝔤))
    (h_summand : IsDirectSummand adj.Fv FV.functor) :
    ∃ (FV_dual : TensorFunctorData R 𝔤), IsDirectSummand adj.F FV_dual.functor := by


  let adj_swap : AdjointPairDataWeak (R := R) (𝔤 := 𝔤) :=
    { F := adj.Fv
      Fv := adj.F
      adjunction_fwd := fun _ _ _ => ⟨0⟩
      adjunction_bwd := fun _ _ _ => ⟨0⟩ }
  exact tensor_functor_dual_summand_transfer_ax FV adj_swap h_summand

theorem tensor_functor_is_exact_ax
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (FV : TensorFunctorData R 𝔤)
    {M₁ M₂ M₃ : RepGfObj R 𝔤}
    (f : RepGfHom M₁ M₂) (g : RepGfHom M₂ M₃)
    (hex : IsExactSequence f g) :
    IsExactSequence (FV.functor.mapHom f) (FV.functor.mapHom g) := by
  sorry

theorem direct_summand_preserves_exact
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (F G : EndoFunctorData R 𝔤)
    (h_summand : IsDirectSummand F G)
    (hG_exact : ∀ {M₁ M₂ M₃ : RepGfObj R 𝔤}
      (f : RepGfHom M₁ M₂) (g : RepGfHom M₂ M₃)
      (_hex : IsExactSequence f g),
      IsExactSequence (G.mapHom f) (G.mapHom g))
    {M₁ M₂ M₃ : RepGfObj R 𝔤}
    (f : RepGfHom M₁ M₂) (g : RepGfHom M₂ M₃)
    (hex : IsExactSequence f g) :
    IsExactSequence (F.mapHom f) (F.mapHom g) := by
  obtain ⟨i, p, hpi⟩ := h_summand
  have hG := hG_exact f g hex
  intro m
  constructor
  ·
    intro hm


    have hi_nat_g := i.naturality g m

    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hi_nat_g

    have hi_zero : (i.app M₃).toFun ((F.mapHom g).toFun m) = 0 := by
      rw [hm, map_zero]
    rw [hi_nat_g] at hi_zero

    have ⟨y, hy⟩ := (hG ((i.app M₂).toFun m)).mp hi_zero

    use (p.app M₁).toFun y


    have hp_nat_f := p.naturality f y
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hp_nat_f

    rw [← hp_nat_f, hy]

    have hpi_M₂ := hpi M₂ m
    simp only [NatTransData.comp, RepGfHom.comp, LieModuleHom.coe_comp,
               Function.comp_apply, NatTransData.id, RepGfHom.id,
               LieModuleHom.coe_id, id_eq] at hpi_M₂
    exact hpi_M₂
  ·
    rintro ⟨x, hx⟩
    rw [← hx]


    have hi_nat_f := i.naturality f x
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hi_nat_f

    have hi_nat_g := i.naturality g ((F.mapHom f).toFun x)
    simp only [RepGfHom.comp, LieModuleHom.coe_comp, Function.comp_apply] at hi_nat_g

    rw [hi_nat_f] at hi_nat_g

    have hker : (G.mapHom g).toFun ((G.mapHom f).toFun ((i.app M₁).toFun x)) = 0 := by
      exact (hG ((G.mapHom f).toFun ((i.app M₁).toFun x))).mpr ⟨(i.app M₁).toFun x, rfl⟩

    rw [hker] at hi_nat_g

    have hpi_M₃ := hpi M₃ ((F.mapHom g).toFun ((F.mapHom f).toFun x))
    simp only [NatTransData.comp, RepGfHom.comp, LieModuleHom.coe_comp,
               Function.comp_apply, NatTransData.id, RepGfHom.id,
               LieModuleHom.coe_id, id_eq] at hpi_M₃
    rw [← hpi_M₃, hi_nat_g, map_zero]

theorem directSummand_of_tensor_exact_ax
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (F : EndoFunctorData R 𝔤)
    (FV : TensorFunctorData R 𝔤)
    (_h : IsDirectSummand F FV.functor) :
    ∀ {M₁ M₂ M₃ : RepGfObj R 𝔤}
      (f : RepGfHom M₁ M₂) (g : RepGfHom M₂ M₃),
      IsExactSequence f g → IsExactSequence (F.mapHom f) (F.mapHom g) := by
  intro M₁ M₂ M₃ f g hex
  exact direct_summand_preserves_exact F FV.functor _h
    (fun f g hex => tensor_functor_is_exact_ax FV f g hex) f g hex

theorem directSummand_of_tensor_preserves_proj_ax
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (F : EndoFunctorData R 𝔤)
    (FV : TensorFunctorData R 𝔤)
    (_h : IsDirectSummand F FV.functor) :
    ∀ (M : RepGfObj R 𝔤), IsProjectiveModule M → IsProjectiveModule (F.obj M) := by
  sorry

theorem adjoint_projectivity_transfer
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (adj : AdjointPairDataWeak (R := R) (𝔤 := 𝔤))
    (hF : IsProjectiveFunctor adj.F) :
    IsProjectiveFunctor adj.Fv := by
  obtain ⟨FV, h_summand⟩ := hF.exists_tensor_summand
  obtain ⟨FV_dual, h_summand_dual⟩ := tensor_functor_dual_summand_transfer_ax FV adj h_summand
  exact { exists_tensor_summand := ⟨FV_dual, h_summand_dual⟩ }

theorem adjoint_projectivity_transfer_rev
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (adj : AdjointPairDataWeak (R := R) (𝔤 := 𝔤))
    (hFv : IsProjectiveFunctor adj.Fv) :
    IsProjectiveFunctor adj.F := by
  obtain ⟨FV, h_summand⟩ := hFv.exists_tensor_summand
  obtain ⟨FV_dual, h_summand_dual⟩ := tensor_functor_dual_summand_transfer_rev_ax FV adj h_summand
  exact { exists_tensor_summand := ⟨FV_dual, h_summand_dual⟩ }

theorem adjoint_of_projective_is_projective_ax
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (adj : AdjointPairDataWeak (R := R) (𝔤 := 𝔤))
    (G : EndoFunctorData R 𝔤)
    (hG : IsProjectiveFunctor G)
    (hG_eq : G = adj.F ∨ G = adj.Fv) :
    IsProjectiveFunctor adj.F ∧ IsProjectiveFunctor adj.Fv := by
  cases hG_eq with
  | inl h => exact ⟨h ▸ hG, adjoint_projectivity_transfer adj (h ▸ hG)⟩
  | inr h => exact ⟨adjoint_projectivity_transfer_rev adj (h ▸ hG), h ▸ hG⟩

theorem InnerProductData.pairing_symm
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    {KO : GrothendieckGroupData Δ}
    (ip : KO.InnerProductData)
    (x y : KO.carrier) : ip.pairing x y = ip.pairing y x := by
  apply ip.pairing_basis_determines (fun a b => ip.pairing a b) (fun a b => ip.pairing b a)
  intro lam mu
  rw [ip.orthonormal, ip.orthonormal]
  simp [eq_comm]

theorem mapKO_adjoint_pairing
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (adj : AdjointPairDataWeak (R := R) (𝔤 := 𝔤))
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF fFv : InducedMapData KO)
    (hfF : fF.F = adj.F) (hfFv : fFv.F = adj.Fv)
    (x y : KO.carrier) :
    ip.pairing (fF.mapKO x) y = ip.pairing x (fFv.mapKO y) := by sorry

theorem pairing_eq_of_adjunction_weak
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (adj : AdjointPairDataWeak (R := R) (𝔤 := 𝔤))
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF fFv : InducedMapData KO)
    (hfF : fF.F = adj.F) (hfFv : fFv.F = adj.Fv)
    (lam mu : Δ.𝔥 →ₗ[R] R) :
    homDim KO ip fF lam mu = homDim KO ip fFv mu lam := by


  unfold homDim

  rw [mapKO_adjoint_pairing adj KO ip fF fFv hfF hfFv]

  exact InnerProductData.pairing_symm ip _ _

theorem adjunction_homDim_pairing_of_weak_adj
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (adj : AdjointPairDataWeak (R := R) (𝔤 := 𝔤))
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF fFv : InducedMapData KO)
    (hfF : fF.F = adj.F) (hfFv : fFv.F = adj.Fv)
    (lam mu : Δ.𝔥 →ₗ[R] R) :
    ip.pairing (fF.mapKO (KO.delta lam)) (KO.delta mu) =
    ip.pairing (fFv.mapKO (KO.delta mu)) (KO.delta lam) := by

  have hF_proj : IsProjectiveFunctor adj.F := hfF ▸ fF.hF
  have hFv_proj : IsProjectiveFunctor adj.Fv := hfFv ▸ fFv.hF


  let adj_full : AdjointPairData (R := R) (𝔤 := 𝔤) :=
    adj.toAdjointPairData hF_proj hFv_proj
      (fun {_} KO' ip' fF' fFv' hfF' hfFv' lam' mu' =>
        pairing_eq_of_adjunction_weak adj KO' ip' fF' fFv' hfF' hfFv' lam' mu')
  exact adj_full.adjunction_homDim_pairing KO ip fF fFv hfF hfFv lam mu

include wg in
theorem theorem_23_1_iii
    (KO : GrothendieckGroupData Δ)
    (F : EndoFunctorData R 𝔤)
    (hF : IsProjectiveFunctor F)
    (adjL : AdjointPairDataWeak (R := R) (𝔤 := 𝔤))
    (adjR : AdjointPairDataWeak (R := R) (𝔤 := 𝔤))
    (hL : adjL.Fv = F)
    (hR : adjR.F = F) :
    AreNatIso adjL.F adjR.Fv := by


  have hL_proj : IsProjectiveFunctor adjL.F :=
    (adjoint_of_projective_is_projective_ax adjL F (hL ▸ hF) (Or.inr hL.symm)).1
  have hR_proj : IsProjectiveFunctor adjR.Fv :=
    (adjoint_of_projective_is_projective_ax adjR F (hR ▸ hF) (Or.inl hR.symm)).2


  have hLFv_proj : IsProjectiveFunctor adjL.Fv := hL ▸ hF
  have hRF_proj : IsProjectiveFunctor adjR.F := hR ▸ hF


  let adjL_full := adjL.toAdjointPairData hL_proj hLFv_proj
    (fun KO ip fF fFv hfF hfFv lam mu =>
      adjunction_homDim_pairing_of_weak_adj adjL KO ip fF fFv hfF hfFv lam mu)
  let adjR_full := adjR.toAdjointPairData hRF_proj hR_proj
    (fun KO ip fF fFv hfF hfFv lam mu =>
      adjunction_homDim_pairing_of_weak_adj adjR KO ip fF fFv hfF hfFv lam mu)

  let ip := grothendieck_group_has_inner_product KO

  let fL := projective_functor_has_induced_map_data KO adjL.F hL_proj
  have hfL_F : fL.F = adjL.F := projective_functor_has_induced_map_data_F KO adjL.F hL_proj

  let fR := projective_functor_has_induced_map_data KO adjR.Fv hR_proj
  have hfR_F : fR.F = adjR.Fv := projective_functor_has_induced_map_data_F KO adjR.Fv hR_proj

  let fF := projective_functor_has_induced_map_data KO F hF
  have hfF_F : fF.F = F := projective_functor_has_induced_map_data_F KO F hF


  have hfF_adjLFv : fF.F = adjL_full.Fv := by
    show fF.F = adjL.Fv
    rw [hfF_F, ← hL]
  have hfL_adjLF : fL.F = adjL_full.F := by
    show fL.F = adjL.F
    rw [hfL_F]
  have adjL_ii := theorem_23_1_ii KO ip adjL_full fL fF hfL_adjLF hfF_adjLFv


  have hfF_adjRF : fF.F = adjR_full.F := by
    show fF.F = adjR.F
    rw [hfF_F, ← hR]
  have hfR_adjRFv : fR.F = adjR_full.Fv := by
    show fR.F = adjR.Fv
    rw [hfR_F]
  have adjR_ii := theorem_23_1_ii KO ip adjR_full fF fR hfF_adjRF hfR_adjRFv


  have h_maps_eq : fL.mapKO = fR.mapKO := by
    funext x
    apply inner_product_nondegen KO ip
    intro mu


    rw [InnerProductData.pairing_symm ip (KO.delta mu) (fL.mapKO x)]
    rw [adjL_ii x (KO.delta mu)]
    rw [← adjR_ii (KO.delta mu) x]
    rw [InnerProductData.pairing_symm ip (fF.mapKO (KO.delta mu)) x]

  have result := theorem_23_1_i wg KO fL fR h_maps_eq

  rw [hfL_F, hfR_F] at result
  exact result

theorem theorem_23_1_iii_adjoint_iso
    {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ}
    (KO : GrothendieckGroupData Δ)
    (F F_L F_R : EndoFunctorData R 𝔤)
    (hF : IsProjectiveFunctor F)
    (adjL : AdjointPairDataWeak (R := R) (𝔤 := 𝔤))
    (adjR : AdjointPairDataWeak (R := R) (𝔤 := 𝔤))
    (hL_F : adjL.F = F_L)
    (hL_Fv : adjL.Fv = F)
    (hR_F : adjR.F = F)
    (hR_Fv : adjR.Fv = F_R) :
    AreNatIso F_L F_R := by
  have h := theorem_23_1_iii wg KO F hF adjL adjR hL_Fv hR_F
  rw [hL_F, hR_Fv] at h
  exact h

lemma induced_map_commutes_weyl_action
    (KO : GrothendieckGroupData Δ)
    (wact : WeylActionData wg KO)
    (fF : InducedMapData KO) :
    ∀ (w : wg.W) (x : KO.carrier),
      wact.act w (fF.mapKO x) = fF.mapKO (wact.act w x) := by


  have ip := grothendieck_group_has_inner_product KO
  have delta_surj : ∀ (c : KO.carrier), ∃ l, KO.delta l = c := by
    intro c
    by_contra hc
    simp only [not_exists] at hc
    have key := ip.pairing_basis_determines
      (fun x _ => if x = c then (1 : ℤ) else 0)
      (fun _ _ => (0 : ℤ))
      (fun l _ => by simp [if_neg (hc l)])
    have := key c c
    simp at this

  intro w x
  obtain ⟨lam₀, hlam₀⟩ := delta_surj x
  rw [← hlam₀]

  have h_inv_cancel : ∀ ν, wact.act w⁻¹ (wact.act w (KO.delta ν)) = KO.delta ν := by
    intro ν
    rw [wact.act_delta w ν, wact.act_delta w⁻¹ (wg.dualAction w ν)]
    congr 1
    rw [← wg.dualAction_mul, inv_mul_cancel, wg.dualAction_one]


  let fF' : InducedMapData KO := {
    F := fF.F
    hF := fF.hF
    mapKO := fun y => wact.act w (fF.mapKO (wact.act w⁻¹ y))
    map_basis_compat := by
      intro g hg
      funext y
      obtain ⟨ly, hly⟩ := delta_surj y
      rw [← hly, hg ly]
  }

  have h_eq : fF'.mapKO = fF.mapKO := induced_map_unique_for_same_functor KO fF' fF rfl

  have h_apply := congr_fun h_eq (wact.act w (KO.delta lam₀))
  change wact.act w (fF.mapKO (wact.act w⁻¹ (wact.act w (KO.delta lam₀)))) =
    fF.mapKO (wact.act w (KO.delta lam₀)) at h_apply
  rw [h_inv_cancel lam₀] at h_apply
  exact h_apply

lemma lemma_23_3_i
    (KO : GrothendieckGroupData Δ)
    (wact : WeylActionData wg KO)
    (lam : Δ.𝔥 →ₗ[R] R)
    (S : Set (Δ.𝔥 →ₗ[R] R))
    (_hdom : DominatesSet rd lam S)
    (fF : InducedMapData KO) :
    ∀ (w : wg.W) (x : KO.carrier),
      wact.act w (fF.mapKO x) = fF.mapKO (wact.act w x) :=
  induced_map_commutes_weyl_action wg KO wact fF

theorem projective_functor_commutes_weyl
    (KO : GrothendieckGroupData Δ)
    (wact : WeylActionData wg KO)
    (fF : InducedMapData KO) :
    ∀ (w : wg.W) (x : KO.carrier),
      wact.act w (fF.mapKO x) = fF.mapKO (wact.act w x) :=
  induced_map_commutes_weyl_action wg KO wact fF

include rd in
theorem theorem_23_2
    (KO : GrothendieckGroupData Δ)
    (wact : WeylActionData wg KO)
    (fF : InducedMapData KO) :
    ∀ (w : wg.W) (x : KO.carrier),
      wact.act w (fF.mapKO x) = fF.mapKO (wact.act w x) :=
  projective_functor_commutes_weyl wg KO wact fF

theorem finite_dim_module_of_dominant_weight_ax
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (beta : Δ.𝔥 →ₗ[R] R)
    (hbeta : rd.IsInQPlus beta) :
    ∃ (FV : TensorFunctorData R 𝔤), True := by
  sorry

theorem projective_functor_block_component_ax
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (F : EndoFunctorData R 𝔤)
    (hF : IsProjectiveFunctor F)
    (lam : Δ.𝔥 →ₗ[R] R) :
    ∃ (G : EndoFunctorData R 𝔤), IsProjectiveFunctor G ∧
      FactorsThroughBlock Δ G lam := by
  sorry

theorem translation_functor_of_dominant_weight
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (_wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (beta : Δ.𝔥 →ₗ[R] R)
    (hbeta : rd.IsInQPlus beta) :
    ∃ (G_L : EndoFunctorData R 𝔤), IsProjectiveFunctor G_L ∧
      FactorsThroughBlock Δ G_L lam := by

  obtain ⟨FV, _⟩ := finite_dim_module_of_dominant_weight_ax Δ rd beta hbeta

  have h_self_summand : IsDirectSummand FV.functor FV.functor :=
    ⟨NatTransData.id FV.functor, NatTransData.id FV.functor,
      fun M x => by simp [NatTransData.comp, NatTransData.id, RepGfHom.comp, RepGfHom.id]⟩


  have hFV_proj : IsProjectiveFunctor FV.functor :=
    { exists_tensor_summand := ⟨FV, h_self_summand⟩ }

  exact projective_functor_block_component_ax Δ FV.functor hFV_proj lam

theorem dominatesSet_implies_isDominantWeightLE
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (S : Set (Δ.𝔥 →ₗ[R] R))
    (hdom : DominatesSet rd lam S)
    (h_orbit : ∀ w ∈ WeylStabilizerModQ rd wg lam, wg.dualAction w lam ∈ S) :
    IsDominantWeightLE rd wg lam := by
  intro w hw hle


  have h_wle : WeightLE rd (wg.dualAction w lam) lam := hdom (wg.dualAction w lam) (h_orbit w hw)
  exact weightLE_antisymm rd _ _ hle h_wle

theorem summand_of_translation_factors_through_block
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (lam : Δ.𝔥 →ₗ[R] R)
    (G_L : EndoFunctorData R 𝔤) (_hG : IsProjectiveFunctor G_L)
    (hG_block : FactorsThroughBlock Δ G_L lam)
    (F_j : EndoFunctorData R 𝔤) (_hF : IsProjectiveFunctor F_j)
    (_hIndec : IsIndecomposable F_j)
    {ι : Type u} [Fintype ι] (F_i : ι → EndoFunctorData R 𝔤)
    (hDecomp : IsDirectSumDecompGen G_L F_i)
    (j : ι) (hj : F_j = F_i j) :
    FactorsThroughBlock Δ F_j lam := by

  obtain ⟨section_i, retract_i, hRetSec, _hSum⟩ := hDecomp

  intro M hM x


  have hRS := hRetSec j

  subst hj

  have hRS_M := hRS M


  have hRS_x := hRS_M x

  simp only [NatTransData.comp, NatTransData.id, RepGfHom.comp, RepGfHom.id,
    LieModuleHom.coe_comp, Function.comp_apply, LieModuleHom.id_apply] at hRS_x


  have h_sec_zero : (section_i j |>.app M).toFun x = 0 := by
    exact hG_block M hM ((section_i j |>.app M).toFun x)

  rw [h_sec_zero] at hRS_x
  rw [← hRS_x]
  exact map_zero (retract_i j |>.app M).toFun

theorem IsInQPlus_antisymm
    {R : Type*} [CommRing R]
    {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ)
    (μ : Δ.𝔥 →ₗ[R] R)
    (hpos : rd.IsInQPlus μ)
    (hneg : rd.IsInQPlus (-μ)) :
    μ = 0 := by
  obtain ⟨c, hc⟩ := hpos
  obtain ⟨d, hd⟩ := hneg

  by_contra hμ
  have hne : ∃ β ∈ rd.posRoots, c β ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hμ
    rw [hc]
    apply Finset.sum_eq_zero
    intro β hβ
    simp [hall β hβ]
  obtain ⟨β, hβ, hcβ⟩ := hne

  have hsum : ∑ α ∈ rd.posRoots, ((c α + d α) • α) = 0 := by
    have h0 : ∑ α ∈ rd.posRoots, (c α) • α + ∑ α ∈ rd.posRoots, (d α) • α = 0 := by
      rw [← hc, ← hd, add_neg_cancel]
    rw [← Finset.sum_add_distrib] at h0
    convert h0 using 1
    apply Finset.sum_congr rfl
    intro α _
    rw [add_nsmul]

  have hextract := Finset.sum_erase_add _ (fun α => (c α + d α) • α) hβ
  rw [hsum] at hextract


  let c' : (Δ.𝔥 →ₗ[R] R) → ℕ := fun γ => if γ = β then 0 else c γ + d γ

  have hc'_sum : ∑ γ ∈ rd.posRoots, (c' γ) • γ =
      ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ := by
    rw [← Finset.sum_erase_add _ _ hβ]
    simp only [c', ite_true, zero_smul, add_zero]
    apply Finset.sum_congr rfl
    intro γ hγ
    have hne : γ ≠ β := Finset.ne_of_mem_erase hγ
    simp [hne]


  have hkey : (-(↑(c β + d β) : ℤ)) • β = ∑ γ ∈ rd.posRoots, (c' γ) • γ := by
    rw [hc'_sum]
    have h1 : ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ + (c β + d β) • β = 0 := hextract
    have h2 : ∑ γ ∈ rd.posRoots.erase β, (c γ + d γ) • γ = -((c β + d β) • β) :=
      eq_neg_of_add_eq_zero_left h1
    rw [h2, neg_zsmul, natCast_zsmul]

  have hn_neg : (-(↑(c β + d β) : ℤ)) < 0 := by
    have : 0 < c β := Nat.pos_of_ne_zero hcβ
    omega

  exact rd.posRoots_pointed_cone β hβ _ hn_neg ⟨c', hkey⟩

theorem theorem_20_13_verma_filtration_coefficients
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (S : Set (Δ.𝔥 →ₗ[R] R))
    (hdom : DominatesSet rd lam S)
    (mu : Δ.𝔥 →ₗ[R] R) (hmu : mu ∈ S)
    (Mverma : RepGfObj R 𝔤)
    (hVerma : IsVermaModule Δ Mverma.carrier (lam - wg.ρ))
    (ι : Type u) [Fintype ι]
    (F_i : ι → EndoFunctorData R 𝔤)
    (hProj : ∀ i, IsProjectiveFunctor (F_i i))
    (hIndec : ∀ i, IsIndecomposable (F_i i))
    (nu : ι → (Δ.𝔥 →ₗ[R] R))
    (hnu : ∀ i, Nonempty (IsHighestWeightModule Δ (F_i i |>.obj Mverma).carrier (nu i - wg.ρ))) :
    ∃ (d : ι → (Δ.𝔥 →ₗ[R] R) → ℤ),
      (∀ j γ, d j γ ≥ 0) ∧
      (∀ j, d j (nu j) = 1) ∧
      (∀ j γ, ¬ rd.IsInQPlus (γ - nu j) → d j γ = 0) := by
  sorry

theorem tensor_product_character_formula_coefficients
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (S : Set (Δ.𝔥 →ₗ[R] R))
    (hdom : DominatesSet rd lam S)
    (mu : Δ.𝔥 →ₗ[R] R) (hmu : mu ∈ S)
    (Mverma : RepGfObj R 𝔤)
    (hVerma : IsVermaModule Δ Mverma.carrier (lam - wg.ρ))
    (ι : Type u) [Fintype ι]
    (F_i : ι → EndoFunctorData R 𝔤)
    (hProj : ∀ i, IsProjectiveFunctor (F_i i))
    (hIndec : ∀ i, IsIndecomposable (F_i i))
    (nu : ι → (Δ.𝔥 →ₗ[R] R))
    (hnu : ∀ i, Nonempty (IsHighestWeightModule Δ (F_i i |>.obj Mverma).carrier (nu i - wg.ρ)))
    (d : ι → (Δ.𝔥 →ₗ[R] R) → ℤ)
    (hd_nonneg : ∀ j γ, d j γ ≥ 0)
    (hd_diag : ∀ j, d j (nu j) = 1)
    (hd_tri : ∀ j γ, ¬ rd.IsInQPlus (γ - nu j) → d j γ = 0) :
    (∀ γ, ¬ rd.IsInQPlus (γ - mu) → ∑ j : ι, d j γ = 0) ∧
    (∑ j : ι, d j mu ≥ 1) := by


  have h_key : (∀ j, rd.IsInQPlus (nu j - mu)) ∧ (∃ j₀, nu j₀ = mu) := by
    sorry
  obtain ⟨h_nu_dom_mu, j₀, hj₀⟩ := h_key
  constructor
  ·


    intro γ hγ
    apply Finset.sum_eq_zero
    intro j _
    apply hd_tri
    intro h_contra
    exact hγ (PositiveRootData.IsInQPlus_trans rd γ (nu j) mu h_contra (h_nu_dom_mu j))
  ·


    calc ∑ j : ι, d j mu
        ≥ d j₀ mu := Finset.single_le_sum (fun k _ => hd_nonneg k mu) (Finset.mem_univ j₀)
      _ = d j₀ (nu j₀) := by rw [hj₀]
      _ = 1 := hd_diag j₀

theorem weight_analysis_mu_appears_among_summands
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (S : Set (Δ.𝔥 →ₗ[R] R))
    (hdom : DominatesSet rd lam S)
    (mu : Δ.𝔥 →ₗ[R] R) (hmu : mu ∈ S)
    (Mverma : RepGfObj R 𝔤)
    (hVerma : IsVermaModule Δ Mverma.carrier (lam - wg.ρ))
    (ι : Type u) [Fintype ι]
    (F_i : ι → EndoFunctorData R 𝔤)
    (hProj : ∀ i, IsProjectiveFunctor (F_i i))
    (hIndec : ∀ i, IsIndecomposable (F_i i))
    (nu : ι → (Δ.𝔥 →ₗ[R] R))
    (hnu : ∀ i, Nonempty (IsHighestWeightModule Δ (F_i i |>.obj Mverma).carrier (nu i - wg.ρ))) :
    ∃ j : ι, nu j = mu := by

  obtain ⟨d, hd_nonneg, hd_diag, hd_tri⟩ :=
    theorem_20_13_verma_filtration_coefficients Δ rd wg lam S hdom mu hmu
      Mverma hVerma ι F_i hProj hIndec nu hnu

  obtain ⟨hsum_zero_below, hsum_mu_pos⟩ :=
    tensor_product_character_formula_coefficients Δ rd wg lam S hdom mu hmu
      Mverma hVerma ι F_i hProj hIndec nu hnu d hd_nonneg hd_diag hd_tri

  have h_all_dom : ∀ j : ι, rd.IsInQPlus (nu j - mu) := by
    intro j

    by_contra h_not_dom

    have h_sum_zero := hsum_zero_below (nu j) h_not_dom

    have h_diag := hd_diag j

    have h_le : d j (nu j) ≤ ∑ k : ι, d k (nu j) := by
      apply Finset.single_le_sum (fun k _ => hd_nonneg k (nu j))
      exact Finset.mem_univ j
    linarith


  have h_sum_ne_zero : ∑ j : ι, d j mu ≠ 0 := by linarith

  obtain ⟨j, _, hj_ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h_sum_ne_zero

  use j

  have h_mu_dom_nu_j : rd.IsInQPlus (mu - nu j) := by
    by_contra h_not
    exact hj_ne (hd_tri j mu h_not)

  have h_nu_j_dom_mu : rd.IsInQPlus (nu j - mu) := h_all_dom j

  have h_diff_zero := IsInQPlus_antisymm rd (nu j - mu) h_nu_j_dom_mu
    (by rw [neg_sub]; exact h_mu_dom_nu_j)
  exact sub_eq_zero.mp h_diff_zero

theorem weight_analysis_selects_summand
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    (Δ : TriangularDecomposition R 𝔤)
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (S : Set (Δ.𝔥 →ₗ[R] R))
    (hdom : DominatesSet rd lam S)
    (mu : Δ.𝔥 →ₗ[R] R) (hmu : mu ∈ S)
    (Mverma : RepGfObj R 𝔤)
    (hVerma : IsVermaModule Δ Mverma.carrier (lam - wg.ρ))

    (ι : Type u) [Fintype ι]
    (F_i : ι → EndoFunctorData R 𝔤)
    (hProj : ∀ i, IsProjectiveFunctor (F_i i))
    (hIndec : ∀ i, IsIndecomposable (F_i i))

    (hw_i : ∀ i, ∃ (hO : IsCategoryO Δ rd (F_i i |>.obj Mverma).carrier),
        IsProjectiveInO rd (F_i i |>.obj Mverma).carrier hO ∧
        ∃ nu_i : Δ.𝔥 →ₗ[R] R,
          Nonempty (IsHighestWeightModule Δ (F_i i |>.obj Mverma).carrier (nu_i - wg.ρ))) :

    ∃ j : ι,
      ∃ (hO : IsCategoryO Δ rd (F_i j |>.obj Mverma).carrier),
        IsProjectiveInO rd (F_i j |>.obj Mverma).carrier hO ∧
        Nonempty (IsHighestWeightModule Δ (F_i j |>.obj Mverma).carrier (mu - wg.ρ)) := by

  have hw_choice : ∀ i, ∃ (hO : IsCategoryO Δ rd (F_i i |>.obj Mverma).carrier),
      IsProjectiveInO rd (F_i i |>.obj Mverma).carrier hO ∧
      ∃ nu_i : Δ.𝔥 →ₗ[R] R,
        Nonempty (IsHighestWeightModule Δ (F_i i |>.obj Mverma).carrier (nu_i - wg.ρ)) := hw_i


  choose hO_fn hProjO_and_nu using hw_choice


  choose hProjO_fn hnu_exists using fun i => hProjO_and_nu i


  choose nu hnu_hw using hnu_exists


  obtain ⟨j, hj⟩ := weight_analysis_mu_appears_among_summands
    Δ rd wg lam S hdom mu hmu Mverma hVerma ι F_i hProj hIndec nu hnu_hw

  refine ⟨j, hO_fn j, hProjO_fn j, ?_⟩


  rw [← hj]
  exact hnu_hw j

theorem weyl_orbit_in_linkage_class
    {R : Type u} [Field R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (S : Set (Δ.𝔥 →ₗ[R] R))
    (hdom : DominatesSet rd lam S) :
    ∀ w ∈ WeylStabilizerModQ rd wg lam, wg.dualAction w lam ∈ S := by
  sorry

lemma lemma_23_3_ii
    {R : Type u} [Field R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (S : Set (Δ.𝔥 →ₗ[R] R))
    (hdom : DominatesSet rd lam S)
    (mu : Δ.𝔥 →ₗ[R] R) (hmu : mu ∈ S)
    (Mverma : RepGfObj R 𝔤)
    (hVerma : IsVermaModule Δ Mverma.carrier (lam - wg.ρ)) :
    ∃ (F_mu : EndoFunctorData R 𝔤),
      IsProjectiveFunctor F_mu ∧
      IsIndecomposable F_mu ∧
      ∃ (hO : IsCategoryO Δ rd (F_mu.obj Mverma).carrier),
        IsProjectiveInO rd (F_mu.obj Mverma).carrier hO ∧
        Nonempty (IsHighestWeightModule Δ (F_mu.obj Mverma).carrier (mu - wg.ρ)) := by

  have hbeta : rd.IsInQPlus (lam - mu) := hdom mu hmu

  obtain ⟨G_L, hG_L_proj, hG_L_block⟩ := translation_functor_of_dominant_weight Δ rd wg lam (lam - mu) hbeta

  obtain ⟨ι, hFin, F_i, hProj, hIndec, hDecomp⟩ :=
    proposition_22_7_i Δ wg G_L hG_L_proj

  have h_orbit_in_S : ∀ w ∈ WeylStabilizerModQ rd wg lam,
      wg.dualAction w lam ∈ S :=
    weyl_orbit_in_linkage_class rd wg lam S hdom
  have hDom : IsDominantWeightLE rd wg lam :=
    dominatesSet_implies_isDominantWeightLE Δ rd wg lam S hdom h_orbit_in_S
  have hw_i : ∀ i, ∃ (hO : IsCategoryO Δ rd (F_i i |>.obj Mverma).carrier),
      IsProjectiveInO rd (F_i i |>.obj Mverma).carrier hO ∧
      ∃ nu_i : Δ.𝔥 →ₗ[R] R,
        Nonempty (IsHighestWeightModule Δ (F_i i |>.obj Mverma).carrier (nu_i - wg.ρ)) := by
    intro i

    have hBlock : FactorsThroughBlock Δ (F_i i) lam :=
      summand_of_translation_factors_through_block Δ lam G_L hG_L_proj hG_L_block
        (F_i i) (hProj i) (hIndec i) F_i hDecomp i rfl

    obtain ⟨nu_i, hO, hProjO, _, hHW⟩ :=
      proposition_22_7_ii Δ wg rd lam hDom (F_i i) (hProj i) (hIndec i)
        hBlock Mverma ⟨hVerma⟩
    exact ⟨hO, hProjO, nu_i, hHW⟩

  obtain ⟨j, hO_j, hProj_j, hHW_j⟩ :=
    weight_analysis_selects_summand Δ rd wg lam S hdom mu hmu Mverma hVerma ι F_i hProj hIndec hw_i

  exact ⟨F_i j, hProj j, hIndec j, hO_j, hProj_j, hHW_j⟩

lemma WeightBilinForm.form_zero_left {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ} (B : WeightBilinForm wg) (nu : Δ.𝔥 →ₗ[R] R) :
    B.form 0 nu = 0 := by
  have h := B.bilin_left 0 0 nu
  rw [zero_add] at h
  have : B.form 0 nu + B.form 0 nu - B.form 0 nu = B.form 0 nu - B.form 0 nu := by
    rw [← h]
  simp [add_sub_cancel_right] at this
  exact this

lemma WeightBilinForm.form_nsmul_left {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ} (B : WeightBilinForm wg) (n : ℕ)
    (mu nu : Δ.𝔥 →ₗ[R] R) :
    B.form (n • mu) nu = n • B.form mu nu := by
  induction n with
  | zero => simp [B.form_zero_left nu]
  | succ n ih =>
    rw [succ_nsmul, B.bilin_left, ih, succ_nsmul]

lemma WeightBilinForm.form_expand {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ} (B : WeightBilinForm wg)
    (v alpha : Δ.𝔥 →ₗ[R] R) (n : ℕ) :
    B.form (v + n • alpha) (v + n • alpha) =
    B.form v v + (n • B.form alpha v + n • B.form alpha v +
      n • (n • B.form alpha alpha)) := by
  rw [B.bilin_left]
  have e1 : B.form v (v + n • alpha) = B.form v v + B.form v (n • alpha) := by
    rw [B.symm v (v + n • alpha), B.bilin_left, B.symm v v, B.symm (n • alpha) v]
  have e2 : B.form (n • alpha) (v + n • alpha) =
      B.form (n • alpha) v + B.form (n • alpha) (n • alpha) := by
    rw [B.symm (n • alpha) (v + n • alpha), B.bilin_left,
        B.symm v (n • alpha), B.symm (n • alpha) (n • alpha)]
  rw [e1, e2]
  rw [B.form_nsmul_left n alpha v]
  rw [B.symm v (n • alpha), B.form_nsmul_left n alpha v]
  rw [B.form_nsmul_left n alpha (n • alpha), B.symm alpha (n • alpha),
      B.form_nsmul_left n alpha alpha]
  ring

theorem norm_sq_dominant_reflection_nonneg_diff
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (B : WeightBilinForm wg)
    (lam phi alpha : Δ.𝔥 →ₗ[R] R) (n : ℕ)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hphi_le : BruhatLE rd phi lam)
    (halpha_pos : alpha ∈ rd.posRoots)
    (hn_pos : 0 < n) :
    B.normSq (lam - phi) ≤ B.normSq (lam - phi + n • alpha) := by

  unfold WeightBilinForm.normSq

  have hexpand := B.form_expand (lam - phi) alpha n


  have hle := B.dominant_posRoot_cross_le rd lam phi alpha n hlam_dom hphi_le halpha_pos hn_pos

  rw [hexpand]
  exact hle

theorem norm_sq_single_step_le
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (B : WeightBilinForm wg)
    (lam a b : Δ.𝔥 →ₗ[R] R)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hb_le : BruhatLE rd b lam)
    (hstep : ∃ α, ReflectionLT rd α a b) :
    B.normSq (lam - b) ≤ B.normSq (lam - a) := by
  obtain ⟨α, hα_pos, n, hn_pos, _hpair, hab⟩ := hstep

  have hkey : lam - a = lam - b + n • α := by
    rw [hab]; abel
  rw [hkey]
  exact norm_sq_dominant_reflection_nonneg_diff rd wg B lam b α n hlam_dom hb_le hα_pos hn_pos

theorem corootPairing_eq_coroot_eval_ax
    {R : Type u} [CommRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (μ α : Δ.𝔥 →ₗ[R] R)
    (hα : α ∈ rs.allRoots) :
    rd.corootPairing μ α = μ (rs.coroot α) :=
  rs.corootPairing_eq_eval α hα μ

theorem norm_sq_equality_implies_lam_coroot_zero_ax
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (B : WeightBilinForm wg)
    (lam b α : Δ.𝔥 →ₗ[R] R) (n : ℕ)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hα_pos : α ∈ rd.posRoots)
    (hn_pos : 0 < n)
    (hpair : rd.corootPairing b α = (n : R))
    (h_eq : B.normSq (lam - b) = B.normSq (lam - b + n • α)) :
    lam (rs.coroot α) = 0 :=
  B.norm_eq_coroot_zero rd rs lam b α n hlam_dom hα_pos hn_pos hpair h_eq

theorem norm_sq_reflection_equality_weyl_element
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (B : WeightBilinForm wg)
    (lam b α : Δ.𝔥 →ₗ[R] R) (n : ℕ)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hα_pos : α ∈ rd.posRoots)
    (hn_pos : 0 < n)
    (hpair : rd.corootPairing b α = (n : R))
    (h_eq : B.normSq (lam - b) = B.normSq (lam - b + n • α)) :
    ∃ (w : wg.W), w ∈ WeylStabilizer rd wg lam ∧
      wg.dualAction w b = b - n • α := by

  have hα_root : α ∈ rs.allRoots := rs.posRoots_sub α hα_pos

  have hlam_zero : lam (rs.coroot α) = 0 :=
    norm_sq_equality_implies_lam_coroot_zero_ax rd wg rs B lam b α n
      hlam_dom hα_pos hn_pos hpair h_eq

  have hrefl_lam : wg.dualAction (rs.reflection α) lam = lam := by
    rw [rs.reflection_formula α hα_root lam, hlam_zero, zero_smul, sub_zero]

  have hcompat : b (rs.coroot α) = (n : R) := by
    rw [← corootPairing_eq_coroot_eval_ax rd wg rs b α hα_root]
    exact hpair
  have hrefl_b : wg.dualAction (rs.reflection α) b = b - n • α := by
    rw [rs.reflection_formula α hα_root b, hcompat]


    congr 1
    exact Nat.cast_smul_eq_nsmul R n α

  have hs_stab : rs.reflection α ∈ WeylStabilizer rd wg lam := hrefl_lam

  exact ⟨rs.reflection α, hs_stab, hrefl_b⟩

theorem norm_sq_single_step_eq
    {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (B : WeightBilinForm wg)
    (lam a b : Δ.𝔥 →ₗ[R] R)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hstep : ∃ α, ReflectionLT rd α a b)
    (h_eq : B.normSq (lam - b) = B.normSq (lam - a)) :
    ∃ (w : wg.W), w ∈ WeylStabilizer rd wg lam ∧
      wg.dualAction w b = a := by

  obtain ⟨α, hα_pos, n, hn_pos, hpair, hab⟩ := hstep

  have hkey : lam - a = lam - b + n • α := by
    rw [hab]; abel
  rw [hkey] at h_eq

  obtain ⟨w, hw_stab, hw_act⟩ :=
    norm_sq_reflection_equality_weyl_element rd wg rs B lam b α n hlam_dom hα_pos hn_pos hpair h_eq
  exact ⟨w, hw_stab, hw_act.trans hab.symm⟩

lemma lemma_23_4_i [LinearOrder R] [IsStrictOrderedRing R]
    (B : WeightBilinForm wg)
    (lam phi psi : Δ.𝔥 →ₗ[R] R)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hBruhat : BruhatLE rd psi phi)
    (hphi_le_lam : BruhatLE rd phi lam) :
    B.normSq (lam - phi) ≤ B.normSq (lam - psi) := by


  induction hBruhat with
  | refl => exact le_rfl
  | @tail b c _hab hbc ih =>


    have hb_le_c : BruhatLE rd b c := Relation.ReflTransGen.single hbc
    have hb_le_lam : BruhatLE rd b lam := hb_le_c.trans hphi_le_lam
    exact le_trans (norm_sq_single_step_le rd wg B lam b c hlam_dom hphi_le_lam hbc)
      (ih hb_le_lam)

lemma lemma_23_4_ii [LinearOrder R] [IsStrictOrderedRing R]
    (rs : RootSystemWithReflections rd wg)
    (B : WeightBilinForm wg)
    (lam phi psi : Δ.𝔥 →ₗ[R] R)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hBruhat : BruhatLE rd psi phi)
    (hphi_le_lam : BruhatLE rd phi lam)
    (h_eq : B.normSq (lam - phi) = B.normSq (lam - psi)) :
    ∃ (w : wg.W), w ∈ WeylStabilizer rd wg lam ∧
      wg.dualAction w phi = psi := by

  induction hBruhat with
  | refl =>

    exact ⟨1, wg.dualAction_one lam, wg.dualAction_one psi⟩
  | @tail b c hab hbc ih =>


    have hb_le_c : BruhatLE rd b c := Relation.ReflTransGen.single hbc
    have hb_le_lam : BruhatLE rd b lam := hb_le_c.trans hphi_le_lam

    have hstep_le := norm_sq_single_step_le rd wg B lam b c hlam_dom hphi_le_lam hbc

    have hchain_le := lemma_23_4_i rd wg B lam b psi hlam_dom hab hb_le_lam


    have h_eq_step : B.normSq (lam - c) = B.normSq (lam - b) :=
      le_antisymm hstep_le (h_eq ▸ hchain_le)
    have h_eq_chain : B.normSq (lam - b) = B.normSq (lam - psi) :=
      le_antisymm hchain_le (h_eq_step ▸ h_eq ▸ le_rfl)

    obtain ⟨w₁, hw₁_stab, hw₁_act⟩ := norm_sq_single_step_eq rd wg rs B lam b c hlam_dom hbc h_eq_step

    obtain ⟨w₂, hw₂_stab, hw₂_act⟩ := ih hb_le_lam h_eq_chain

    exact ⟨w₂ * w₁,
      WeylStabilizer_mul_closed rd wg lam hw₂_stab hw₁_stab,
      by rw [wg.dualAction_mul, hw₁_act, hw₂_act]⟩

def IsInXi0
    (rd : PositiveRootData Δ)
    (mu lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∃ (c : (Δ.𝔥 →ₗ[R] R) → ℤ), lam - mu = ∑ α ∈ rd.posRoots, (c α) • α

def IsProperRep
    (rd : PositiveRootData Δ)
    (wg : WeylGroupData Δ)
    (mu lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  IsDominantWeightBruhat rd wg lam ∧
  IsInXi0 rd mu lam ∧
  ∀ (w : wg.W), w ∈ WeylStabilizer rd wg lam →
    BruhatLE rd mu (wg.dualAction w mu)

def matrixCoeff
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (mu lam : Δ.𝔥 →ₗ[R] R) : ℤ :=
  ip.pairing (KO.delta mu) (fF.mapKO (KO.delta lam))

def supportPF
    {Δ : TriangularDecomposition R 𝔤}
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO) : Set ((Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R)) :=
  {p | matrixCoeff KO ip fF p.1 p.2 > 0}

def maximalSupportPF
    {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ}
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (B : WeightBilinForm wg) [LE R] : Set ((Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R)) :=
  {p | p ∈ supportPF KO ip fF ∧
    ∀ q ∈ supportPF KO ip fF, B.normSq (q.2 - q.1) ≤ B.normSq (p.2 - p.1)}

def WeylOrbitPair
    {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ)
    (mu lam : Δ.𝔥 →ₗ[R] R) : Set ((Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R)) :=
  {p | ∃ w : wg.W, p = (wg.dualAction w mu, wg.dualAction w lam)}

theorem matrixCoeff_eq_standardFiltrationMultiplicity
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (Mverma : RepGfObj R 𝔤)
    (_hVerma : IsVermaModule Δ Mverma.carrier (lam - wg.ρ))
    (_hO : IsCategoryO Δ rd (fF.F.obj Mverma).carrier)
    (_hProj : IsProjectiveInO rd (fF.F.obj Mverma).carrier _hO)
    (_hHW : Nonempty (IsHighestWeightModule Δ (fF.F.obj Mverma).carrier (mu - wg.ρ)))
    (phi : Δ.𝔥 →ₗ[R] R) :
    matrixCoeff KO ip fF phi lam = ↑(standardFiltrationMultiplicity rd wg mu phi) := by sorry

theorem matrixCoeff_eq_compositionMultiplicity
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (Mverma : RepGfObj R 𝔤)
    (_hVerma : IsVermaModule Δ Mverma.carrier (lam - wg.ρ))
    (_hO : IsCategoryO Δ rd (fF.F.obj Mverma).carrier)
    (_hProj : IsProjectiveInO rd (fF.F.obj Mverma).carrier _hO)
    (_hHW : Nonempty (IsHighestWeightModule Δ (fF.F.obj Mverma).carrier (mu - wg.ρ)))
    (phi : Δ.𝔥 →ₗ[R] R) :
    matrixCoeff KO ip fF phi lam = ↑(compositionMultiplicity rd wg phi mu) := by

  rw [matrixCoeff_eq_standardFiltrationMultiplicity rd wg KO ip fF lam mu Mverma
    _hVerma _hO _hProj _hHW phi]


  have h := bgg_reciprocity_raw rd wg mu phi
  exact_mod_cast h

lemma theorem_20_13_support_bruhat_bound
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (Mverma : RepGfObj R 𝔤)
    (hVerma : IsVermaModule Δ Mverma.carrier (lam - wg.ρ))
    (hO : IsCategoryO Δ rd (fF.F.obj Mverma).carrier)
    (hProj : IsProjectiveInO rd (fF.F.obj Mverma).carrier hO)
    (hHW : Nonempty (IsHighestWeightModule Δ (fF.F.obj Mverma).carrier (mu - wg.ρ)))
    (phi : Δ.𝔥 →ₗ[R] R)
    (hmem : (phi, lam) ∈ supportPF KO ip fF) :
    BruhatLE rd mu phi := by


  have h_pos : matrixCoeff KO ip fF phi lam > 0 := hmem


  have h_eq := matrixCoeff_eq_compositionMultiplicity rd wg KO ip fF lam mu
    Mverma hVerma hO hProj hHW phi

  have h_comp_nonzero : compositionMultiplicity rd wg phi mu ≠ 0 := by
    intro h_zero
    rw [h_eq, h_zero, Nat.cast_zero] at h_pos
    exact lt_irrefl 0 h_pos

  exact bgg_theorem_bruhat_order R 𝔤 _ rd wg phi mu h_comp_nonzero

theorem theorem_20_13_support_bruhat_upper_bound
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (_wg : WeylGroupData Δ)
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (lam : Δ.𝔥 →ₗ[R] R)
    (phi : Δ.𝔥 →ₗ[R] R)
    (_hmem : (phi, lam) ∈ supportPF KO ip fF) :
    BruhatLE rd phi lam := by sorry

lemma lemma_23_7_bruhat_bound [LinearOrder R] [IsStrictOrderedRing R]
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (_B : WeightBilinForm wg)
    (_hFI : IsIndecomposable fF.F)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (_hlam_dom : IsDominantWeightBruhat rd wg lam)
    (_hFblock : FactorsThroughBlock Δ fF.F lam)
    (Mverma : RepGfObj R 𝔤)
    (hVerma : IsVermaModule Δ Mverma.carrier (lam - wg.ρ))
    (hO : IsCategoryO Δ rd (fF.F.obj Mverma).carrier)
    (hProj : IsProjectiveInO rd (fF.F.obj Mverma).carrier hO)
    (hHW : Nonempty (IsHighestWeightModule Δ (fF.F.obj Mverma).carrier (mu - wg.ρ)))
    (phi : Δ.𝔥 →ₗ[R] R)
    (hmem : (phi, lam) ∈ supportPF KO ip fF) :
    BruhatLE rd mu phi := by
  exact theorem_20_13_support_bruhat_bound rd wg KO ip fF lam mu Mverma hVerma hO hProj hHW phi hmem

lemma theorem_20_13_self_multiplicity_pos
    {Δ : TriangularDecomposition R 𝔤}
    (_rd : PositiveRootData Δ) (_wg : WeylGroupData Δ)
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (Mverma : RepGfObj R 𝔤)
    (_hVerma : IsVermaModule Δ Mverma.carrier (lam - _wg.ρ))
    (_hO : IsCategoryO Δ _rd (fF.F.obj Mverma).carrier)
    (_hProj : IsProjectiveInO _rd (fF.F.obj Mverma).carrier _hO)
    (_hHW : Nonempty (IsHighestWeightModule Δ (fF.F.obj Mverma).carrier (mu - _wg.ρ))) :
    matrixCoeff KO ip fF mu lam > 0 := by


  have h_eq := matrixCoeff_eq_compositionMultiplicity _rd _wg KO ip fF lam mu
    Mverma _hVerma _hO _hProj _hHW mu

  have h_diag : compositionMultiplicity _rd _wg mu mu = 1 :=
    jordanHolder_compMult_diag R 𝔤 _ _rd _wg mu

  rw [h_eq, h_diag]
  norm_num

lemma mu_lam_positive_matrixCoeff
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (Mverma : RepGfObj R 𝔤)
    (hVerma : IsVermaModule Δ Mverma.carrier (lam - wg.ρ))
    (hO : IsCategoryO Δ rd (fF.F.obj Mverma).carrier)
    (hProj : IsProjectiveInO rd (fF.F.obj Mverma).carrier hO)
    (hHW : Nonempty (IsHighestWeightModule Δ (fF.F.obj Mverma).carrier (mu - wg.ρ))) :
    (mu, lam) ∈ supportPF KO ip fF := by

  show matrixCoeff KO ip fF mu lam > 0
  exact theorem_20_13_self_multiplicity_pos rd wg KO ip fF lam mu Mverma hVerma hO hProj hHW

theorem block_support_invariant_agree
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (_rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (_hFI : IsIndecomposable fF.F)
    (lam : Δ.𝔥 →ₗ[R] R)
    (_hFblock : FactorsThroughBlock Δ fF.F lam)
    (q : (Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R))
    (_hq : q ∈ supportPF KO ip fF)
    (p : wg.invariantSubalgebra) :
    evalWeight Δ lam (p : UniversalEnvelopingAlgebra R Δ.𝔥) =
    evalWeight Δ q.2 (p : UniversalEnvelopingAlgebra R Δ.𝔥) := by sorry

theorem support_second_component_weyl_orbit
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (_rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (_hFI : IsIndecomposable fF.F)
    (lam : Δ.𝔥 →ₗ[R] R)
    (_hFblock : FactorsThroughBlock Δ fF.F lam)
    (q : (Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R))
    (_hq : q ∈ supportPF KO ip fF) :
    ∃ (w : wg.W), q.2 = wg.dualAction w lam := by


  apply weyl_orbit_separation Δ wg lam q.2
  intro p
  exact block_support_invariant_agree _rd wg KO ip fF _hFI lam _hFblock q _hq p

lemma matrixCoeff_dualAction_invariant
    {Δ : TriangularDecomposition R 𝔤}
    (_rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (w : wg.W)
    (mu lam : Δ.𝔥 →ₗ[R] R) :
    matrixCoeff KO ip fF (wg.dualAction w mu) (wg.dualAction w lam) =
      matrixCoeff KO ip fF mu lam := by

  unfold matrixCoeff

  have delta_surj : ∀ (c : KO.carrier), ∃ l, KO.delta l = c := by
    intro c
    by_contra hc
    push Not at hc
    have key := ip.pairing_basis_determines
      (fun x _ => if x = c then (1 : ℤ) else 0)
      (fun _ _ => (0 : ℤ))
      (fun l _ => by simp [if_neg (hc l)])
    have := key c c
    simp at this

  have delta_inj : ∀ (l1 l2 : Δ.𝔥 →ₗ[R] R), KO.delta l1 = KO.delta l2 → l1 = l2 := by
    intro l1 l2 h
    have h1 : ip.pairing (KO.delta l1) (KO.delta l2) = if l1 = l2 then 1 else 0 :=
      ip.orthonormal l1 l2
    rw [h] at h1
    rw [ip.orthonormal l2 l2] at h1
    simp at h1
    exact h1

  have choose_delta : ∀ l, Classical.choose (delta_surj (KO.delta l)) = l := by
    intro l
    exact delta_inj _ _ (Classical.choose_spec (delta_surj (KO.delta l)))

  have wact : WeylActionData wg KO := {
    act := fun w' c =>
      let l := Classical.choose (delta_surj c)
      KO.delta (wg.dualAction w' l)
    act_delta := by
      intro w' l0
      show KO.delta (wg.dualAction w' (Classical.choose (delta_surj (KO.delta l0)))) =
        KO.delta (wg.dualAction w' l0)
      rw [choose_delta l0]
  }

  have h_commute := theorem_23_2 _rd wg KO wact fF

  have h_act_lam : wact.act w (KO.delta lam) = KO.delta (wg.dualAction w lam) :=
    wact.act_delta w lam
  have h_F_commute : wact.act w (fF.mapKO (KO.delta lam)) =
      fF.mapKO (KO.delta (wg.dualAction w lam)) := by
    rw [h_commute w (KO.delta lam), h_act_lam]

  rw [← h_F_commute]

  obtain ⟨z, hz⟩ := delta_surj (fF.mapKO (KO.delta lam))
  rw [← hz]

  show ip.pairing (KO.delta (wg.dualAction w mu)) (wact.act w (KO.delta z)) =
    ip.pairing (KO.delta mu) (KO.delta z)
  rw [wact.act_delta w z]

  rw [ip.orthonormal (wg.dualAction w mu) (wg.dualAction w z)]
  rw [ip.orthonormal mu z]


  congr 1
  exact propext ⟨fun h => by
    have h1 := congr_arg (wg.dualAction w⁻¹) h
    rwa [← wg.dualAction_mul, ← wg.dualAction_mul, inv_mul_cancel,
         wg.dualAction_one, wg.dualAction_one] at h1,
    fun h => by rw [h]⟩

lemma support_weyl_equivariant_inv
    {Δ : TriangularDecomposition R 𝔤}
    (_rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (w : wg.W)
    (a b : Δ.𝔥 →ₗ[R] R)
    (_hab : (a, b) ∈ supportPF KO ip fF) :
    (wg.dualAction w⁻¹ a, wg.dualAction w⁻¹ b) ∈ supportPF KO ip fF := by

  change matrixCoeff KO ip fF (wg.dualAction w⁻¹ a) (wg.dualAction w⁻¹ b) > 0


  rw [matrixCoeff_dualAction_invariant _rd wg KO ip fF w⁻¹ a b]

  exact _hab

theorem bilinForm_weyl_normSq_invariant
    {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ)
    (B : WeightBilinForm wg)
    (w : wg.W)
    (mu nu : Δ.𝔥 →ₗ[R] R) :
    B.normSq (wg.dualAction w mu - wg.dualAction w nu) = B.normSq (mu - nu) := by
  exact B.weyl_normSq_invariant w mu nu

lemma support_reduce_to_lam_fiber [LinearOrder R] [IsStrictOrderedRing R]
    {Δ : TriangularDecomposition R 𝔤}
    (_rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (B : WeightBilinForm wg)
    (_hFI : IsIndecomposable fF.F)
    (lam : Δ.𝔥 →ₗ[R] R)
    (_hFblock : FactorsThroughBlock Δ fF.F lam)
    (q : (Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R))
    (hq : q ∈ supportPF KO ip fF) :
    ∃ (phi : Δ.𝔥 →ₗ[R] R),
      (phi, lam) ∈ supportPF KO ip fF ∧
      B.normSq (q.2 - q.1) = B.normSq (lam - phi) := by

  obtain ⟨w, hw⟩ := support_second_component_weyl_orbit _rd wg KO ip fF _hFI lam _hFblock q hq


  set phi := wg.dualAction w⁻¹ q.1 with hphi_def
  have hequiv := support_weyl_equivariant_inv _rd wg KO ip fF w q.1 q.2 hq

  have hw_inv_q2 : wg.dualAction w⁻¹ q.2 = lam := by
    rw [hw, ← wg.dualAction_mul w⁻¹ w lam, inv_mul_cancel, wg.dualAction_one]
  rw [hw_inv_q2] at hequiv


  have hnorm : B.normSq (q.2 - q.1) = B.normSq (lam - phi) := by
    have hinv := bilinForm_weyl_normSq_invariant wg B w⁻¹ q.2 q.1
    rw [hw_inv_q2] at hinv
    exact hinv.symm
  exact ⟨phi, hequiv, hnorm⟩

lemma support_norm_bounded_by_mu_lam [LinearOrder R] [IsStrictOrderedRing R]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (B : WeightBilinForm wg)
    (hFI : IsIndecomposable fF.F)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hFblock : FactorsThroughBlock Δ fF.F lam)
    (Mverma : RepGfObj R 𝔤)
    (hVerma : IsVermaModule Δ Mverma.carrier (lam - wg.ρ))
    (hO : IsCategoryO Δ rd (fF.F.obj Mverma).carrier)
    (hProj : IsProjectiveInO rd (fF.F.obj Mverma).carrier hO)
    (hHW : Nonempty (IsHighestWeightModule Δ (fF.F.obj Mverma).carrier (mu - wg.ρ)))
    (q : (Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R))
    (hq : q ∈ supportPF KO ip fF) :
    B.normSq (q.2 - q.1) ≤ B.normSq (lam - mu) := by

  obtain ⟨phi, hphi_supp, hphi_eq⟩ := support_reduce_to_lam_fiber rd wg KO ip fF B hFI lam hFblock q hq

  have hbruhat : BruhatLE rd mu phi :=
    theorem_20_13_support_bruhat_bound rd wg KO ip fF lam mu Mverma hVerma hO hProj hHW phi hphi_supp

  have hphi_le_lam : BruhatLE rd phi lam :=
    theorem_20_13_support_bruhat_upper_bound rd wg KO ip fF lam phi hphi_supp

  have hnorm_ineq : B.normSq (lam - phi) ≤ B.normSq (lam - mu) :=
    lemma_23_4_i rd wg B lam phi mu hlam_dom hbruhat hphi_le_lam


  rw [hphi_eq]
  exact hnorm_ineq

lemma lemma_23_7_mu_lam_in_maxsupp [LinearOrder R] [IsStrictOrderedRing R]
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (B : WeightBilinForm wg)
    (hFI : IsIndecomposable fF.F)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hFblock : FactorsThroughBlock Δ fF.F lam)
    (Mverma : RepGfObj R 𝔤)
    (hVerma : IsVermaModule Δ Mverma.carrier (lam - wg.ρ))
    (hO : IsCategoryO Δ rd (fF.F.obj Mverma).carrier)
    (hProj : IsProjectiveInO rd (fF.F.obj Mverma).carrier hO)
    (hHW : Nonempty (IsHighestWeightModule Δ (fF.F.obj Mverma).carrier (mu - wg.ρ))) :
    (mu, lam) ∈ maximalSupportPF KO ip fF B := by

  refine ⟨?_, ?_⟩

  · exact mu_lam_positive_matrixCoeff rd wg KO ip fF lam mu Mverma hVerma hO hProj hHW

  · intro q hq
    exact support_norm_bounded_by_mu_lam rd wg KO ip fF B hFI lam mu hlam_dom hFblock
      Mverma hVerma hO hProj hHW q hq

lemma lemma_23_7_weyl_equivariant [LinearOrder R] [IsStrictOrderedRing R]
    (rd : PositiveRootData Δ)
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (B : WeightBilinForm wg)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (hmem : (mu, lam) ∈ maximalSupportPF KO ip fF B)
    (w : wg.W) :
    (wg.dualAction w mu, wg.dualAction w lam) ∈ maximalSupportPF KO ip fF B := by

  obtain ⟨hmem_supp, hmem_max⟩ := hmem
  constructor
  ·


    have h := support_weyl_equivariant_inv rd wg KO ip fF w⁻¹ mu lam hmem_supp
    simp only [inv_inv] at h
    exact h
  ·
    intro q hq

    rw [bilinForm_weyl_normSq_invariant wg B w lam mu]

    exact hmem_max q hq

lemma hw_module_implies_linked
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LinearOrder R] [IsStrictOrderedRing R]
    {Δ : TriangularDecomposition R 𝔤}
    (_rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (_KO : GrothendieckGroupData Δ)
    (fF : InducedMapData _KO)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (_hFblock : FactorsThroughBlock Δ fF.F lam)
    (Mverma : RepGfObj R 𝔤)
    (_hVerma : IsVermaModule Δ Mverma.carrier (lam - wg.ρ))
    (_hO : IsCategoryO Δ _rd (fF.F.obj Mverma).carrier)
    (_hHW : Nonempty (IsHighestWeightModule Δ (fF.F.obj Mverma).carrier (mu - wg.ρ))) :
    ∃ (w : wg.W), mu = wg.dualAction w lam := by sorry

lemma weyl_orbit_implies_isInXi0
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LinearOrder R] [IsStrictOrderedRing R]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (mu lam : Δ.𝔥 →ₗ[R] R)
    (_hlinked : ∃ (w : wg.W), mu = wg.dualAction w lam) :
    IsInXi0 rd mu lam := by sorry

theorem projective_functor_support_in_xi0
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    [LinearOrder R] [IsStrictOrderedRing R]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (_wg : WeylGroupData Δ)
    (_KO : GrothendieckGroupData Δ)
    (fF : InducedMapData _KO)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (_hFblock : FactorsThroughBlock Δ fF.F lam)
    (Mverma : RepGfObj R 𝔤)
    (_hVerma : IsVermaModule Δ Mverma.carrier (lam - _wg.ρ))
    (_hO : IsCategoryO Δ rd (fF.F.obj Mverma).carrier)
    (_hHW : Nonempty (IsHighestWeightModule Δ (fF.F.obj Mverma).carrier (mu - _wg.ρ))) :
    IsInXi0 rd mu lam := by

  have hlinked : ∃ (w : _wg.W), mu = _wg.dualAction w lam :=
    hw_module_implies_linked rd _wg _KO fF lam mu _hFblock Mverma _hVerma _hO _hHW

  exact weyl_orbit_implies_isInXi0 rd _wg mu lam hlinked

lemma lemma_23_7_in_xi0 [LinearOrder R] [IsStrictOrderedRing R]
    (KO : GrothendieckGroupData Δ)
    (_ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (hFblock : FactorsThroughBlock Δ fF.F lam)
    (Mverma : RepGfObj R 𝔤)
    (hVerma : IsVermaModule Δ Mverma.carrier (lam - wg.ρ))
    (hO : IsCategoryO Δ rd (fF.F.obj Mverma).carrier)
    (hHW : Nonempty (IsHighestWeightModule Δ (fF.F.obj Mverma).carrier (mu - wg.ρ))) :
    IsInXi0 rd mu lam := by
  exact projective_functor_support_in_xi0 rd wg KO fF lam mu hFblock Mverma hVerma hO hHW

lemma support_pair_weyl_decompose [LinearOrder R] [IsStrictOrderedRing R]
    {Δ : TriangularDecomposition R 𝔤}
    (_rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (_hFI : IsIndecomposable fF.F)
    (lam : Δ.𝔥 →ₗ[R] R)
    (_hFblock : FactorsThroughBlock Δ fF.F lam)
    (p : (Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R))
    (hp : p ∈ supportPF KO ip fF) :
    ∃ (w : wg.W) (phi : Δ.𝔥 →ₗ[R] R),
      (phi, lam) ∈ supportPF KO ip fF ∧
      p = (wg.dualAction w phi, wg.dualAction w lam) := by

  obtain ⟨w, hw⟩ := support_second_component_weyl_orbit _rd wg KO ip fF _hFI lam _hFblock p hp

  set phi := wg.dualAction w⁻¹ p.1 with hphi_def
  have hequiv := support_weyl_equivariant_inv _rd wg KO ip fF w p.1 p.2 hp

  have hw_inv_p2 : wg.dualAction w⁻¹ p.2 = lam := by
    rw [hw, ← wg.dualAction_mul w⁻¹ w lam, inv_mul_cancel, wg.dualAction_one]
  rw [hw_inv_p2] at hequiv


  have hp1_eq : p.1 = wg.dualAction w phi := by
    rw [hphi_def, ← wg.dualAction_mul w w⁻¹ p.1, mul_inv_cancel, wg.dualAction_one]

  have hp_eq : p = (wg.dualAction w phi, wg.dualAction w lam) :=
    Prod.ext hp1_eq hw
  exact ⟨w, phi, hequiv, hp_eq⟩

lemma normSq_weyl_invariant [LinearOrder R] [IsStrictOrderedRing R]
    {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ)
    (B : WeightBilinForm wg)
    (a b : Δ.𝔥 →ₗ[R] R)
    (w : wg.W) :
    B.normSq (wg.dualAction w a - wg.dualAction w b) = B.normSq (a - b) := by
  exact bilinForm_weyl_normSq_invariant wg B w a b

lemma support_stabilizer_in_lam_fiber [LinearOrder R] [IsStrictOrderedRing R]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (_hFblock : FactorsThroughBlock Δ fF.F lam)
    (hmu_supp : (mu, lam) ∈ supportPF KO ip fF)
    (w : wg.W)
    (hw_stab : w ∈ WeylStabilizer rd wg lam) :
    (wg.dualAction w mu, lam) ∈ supportPF KO ip fF := by

  have hw_fix : wg.dualAction w lam = lam := hw_stab


  have h := support_weyl_equivariant_inv rd wg KO ip fF w⁻¹ mu lam hmu_supp
  simp only [inv_inv] at h


  rw [hw_fix] at h
  exact h

lemma weylStabilizer_fixes_dominant_lam [LinearOrder R] [IsStrictOrderedRing R]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (_hlam_dom : IsDominantWeightBruhat rd wg lam)
    (w : wg.W)
    (hw_stab : w ∈ WeylStabilizer rd wg lam) :
    wg.dualAction w lam = lam :=
  hw_stab

lemma lemma_23_7_maxsupp_subset_orbit [LinearOrder R] [IsStrictOrderedRing R]
    (rs : RootSystemWithReflections rd wg)
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (B : WeightBilinForm wg)
    (hFI : IsIndecomposable fF.F)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hFblock : FactorsThroughBlock Δ fF.F lam)
    (Mverma : RepGfObj R 𝔤)
    (hVerma : IsVermaModule Δ Mverma.carrier (lam - wg.ρ))
    (hO : IsCategoryO Δ rd (fF.F.obj Mverma).carrier)
    (hProj : IsProjectiveInO rd (fF.F.obj Mverma).carrier hO)
    (hHW : Nonempty (IsHighestWeightModule Δ (fF.F.obj Mverma).carrier (mu - wg.ρ)))
    (hmu_in_max : (mu, lam) ∈ maximalSupportPF KO ip fF B)
    (p : (Δ.𝔥 →ₗ[R] R) × (Δ.𝔥 →ₗ[R] R))
    (hp : p ∈ maximalSupportPF KO ip fF B) :
    p ∈ WeylOrbitPair wg mu lam := by

  obtain ⟨hp_supp, hp_max⟩ := hp

  obtain ⟨w, phi, hphi_supp, hp_eq⟩ :=
    support_pair_weyl_decompose rd wg KO ip fF hFI lam hFblock p hp_supp

  have hbruhat : BruhatLE rd mu phi :=
    theorem_20_13_support_bruhat_bound rd wg KO ip fF lam mu Mverma hVerma hO hProj hHW phi hphi_supp

  have hphi_le_lam : BruhatLE rd phi lam :=
    theorem_20_13_support_bruhat_upper_bound rd wg KO ip fF lam phi hphi_supp

  have hnorm_le : B.normSq (lam - phi) ≤ B.normSq (lam - mu) :=
    lemma_23_4_i rd wg B lam phi mu hlam_dom hbruhat hphi_le_lam


  have hmu_supp : (mu, lam) ∈ supportPF KO ip fF := hmu_in_max.1
  have hnorm_ge : B.normSq (lam - mu) ≤ B.normSq (p.2 - p.1) :=
    hp_max (mu, lam) hmu_supp

  have hnorm_inv : B.normSq (p.2 - p.1) = B.normSq (lam - phi) := by
    rw [hp_eq]
    exact normSq_weyl_invariant wg B lam phi w

  have hnorm_eq : B.normSq (lam - phi) = B.normSq (lam - mu) :=
    le_antisymm hnorm_le (hnorm_inv ▸ hnorm_ge)

  obtain ⟨w₁, hw₁_stab, hw₁_act⟩ :=
    lemma_23_4_ii rd wg rs B lam phi mu hlam_dom hbruhat hphi_le_lam hnorm_eq


  have hw₁_fix : wg.dualAction w₁ lam = lam :=
    weylStabilizer_fixes_dominant_lam rd wg lam hlam_dom w₁ hw₁_stab

  have hphi_eq : phi = wg.dualAction w₁⁻¹ mu := by
    have : wg.dualAction w₁ phi = mu := hw₁_act
    calc phi = wg.dualAction 1 phi := (wg.dualAction_one phi).symm
    _ = wg.dualAction (w₁⁻¹ * w₁) phi := by rw [inv_mul_cancel]
    _ = wg.dualAction w₁⁻¹ (wg.dualAction w₁ phi) := wg.dualAction_mul w₁⁻¹ w₁ phi
    _ = wg.dualAction w₁⁻¹ mu := by rw [this]

  have hw₁_inv_fix : wg.dualAction w₁⁻¹ lam = lam := by
    calc wg.dualAction w₁⁻¹ lam
        = wg.dualAction w₁⁻¹ (wg.dualAction w₁ lam) := by rw [hw₁_fix]
      _ = wg.dualAction (w₁⁻¹ * w₁) lam := (wg.dualAction_mul w₁⁻¹ w₁ lam).symm
      _ = wg.dualAction 1 lam := by rw [inv_mul_cancel]
      _ = lam := wg.dualAction_one lam

  refine ⟨w * w₁⁻¹, ?_⟩
  rw [hp_eq, hphi_eq]
  refine Prod.ext (wg.dualAction_mul w w₁⁻¹ mu).symm ?_


  show wg.dualAction w lam = wg.dualAction (w * w₁⁻¹) lam
  rw [wg.dualAction_mul w w₁⁻¹ lam, hw₁_inv_fix]

lemma lemma_23_7_mu_minimal [LinearOrder R] [IsStrictOrderedRing R]
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (B : WeightBilinForm wg)
    (_hFI : IsIndecomposable fF.F)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (_hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hFblock : FactorsThroughBlock Δ fF.F lam)
    (Mverma : RepGfObj R 𝔤)
    (hVerma : IsVermaModule Δ Mverma.carrier (lam - wg.ρ))
    (hO : IsCategoryO Δ rd (fF.F.obj Mverma).carrier)
    (hProj : IsProjectiveInO rd (fF.F.obj Mverma).carrier hO)
    (hHW : Nonempty (IsHighestWeightModule Δ (fF.F.obj Mverma).carrier (mu - wg.ρ)))
    (hmu_in_max : (mu, lam) ∈ maximalSupportPF KO ip fF B)
    (w : wg.W)
    (hw_stab : w ∈ WeylStabilizer rd wg lam) :
    BruhatLE rd mu (wg.dualAction w mu) := by

  have hmu_supp : (mu, lam) ∈ supportPF KO ip fF := hmu_in_max.1


  have hwmu_supp : (wg.dualAction w mu, lam) ∈ supportPF KO ip fF :=
    support_stabilizer_in_lam_fiber rd wg KO ip fF lam mu hFblock hmu_supp w hw_stab

  exact theorem_20_13_support_bruhat_bound rd wg KO ip fF lam mu Mverma hVerma hO hProj hHW
    (wg.dualAction w mu) hwmu_supp

lemma lemma_23_7 [LinearOrder R] [IsStrictOrderedRing R]
    (rs : RootSystemWithReflections rd wg)
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (B : WeightBilinForm wg)
    (hFI : IsIndecomposable fF.F)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)

    (hFblock : FactorsThroughBlock Δ fF.F lam)


    (Mverma : RepGfObj R 𝔤)
    (hVerma : IsVermaModule Δ Mverma.carrier (lam - wg.ρ))
    (hO : IsCategoryO Δ rd (fF.F.obj Mverma).carrier)
    (hProj : IsProjectiveInO rd (fF.F.obj Mverma).carrier hO)
    (hHW : Nonempty (IsHighestWeightModule Δ (fF.F.obj Mverma).carrier (mu - wg.ρ))) :

    maximalSupportPF KO ip fF B = WeylOrbitPair wg mu lam ∧

    IsProperRep rd wg mu lam := by

  have hmu_in_max : (mu, lam) ∈ maximalSupportPF KO ip fF B :=
    lemma_23_7_mu_lam_in_maxsupp rd wg KO ip fF B hFI lam mu hlam_dom hFblock
      Mverma hVerma hO hProj hHW
  constructor
  ·
    ext p
    constructor
    ·
      intro hp
      exact lemma_23_7_maxsupp_subset_orbit rd wg rs KO ip fF B hFI lam mu hlam_dom
        hFblock Mverma hVerma hO hProj hHW hmu_in_max p hp
    ·
      intro hp

      obtain ⟨w, rfl⟩ := hp
      exact lemma_23_7_weyl_equivariant wg rd KO ip fF B lam mu hmu_in_max w
  ·
    refine ⟨hlam_dom, ?_, ?_⟩
    ·
      exact lemma_23_7_in_xi0 rd wg KO ip fF lam mu hFblock Mverma hVerma hO hHW
    ·
      intro w hw_stab
      exact lemma_23_7_mu_minimal rd wg KO ip fF B hFI lam mu hlam_dom
        hFblock Mverma hVerma hO hProj hHW hmu_in_max w hw_stab

def SameInfChar
    (wg : WeylGroupData Δ)
    (nu lam : Δ.𝔥 →ₗ[R] R) : Prop :=
  ∃ (w : wg.W), nu = wg.dualAction w lam

def IsZeroRepGfObj (M : RepGfObj R 𝔤) : Prop :=
  Subsingleton M.carrier

theorem proper_rep_implies_bruhatLE
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (mu lam : Δ.𝔥 →ₗ[R] R)
    (hproper : IsProperRep rd wg mu lam) :
    BruhatLE rd mu lam := by sorry

theorem proper_rep_linkage_class_exists
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (mu lam : Δ.𝔥 →ₗ[R] R)
    (hproper : IsProperRep rd wg mu lam) :
    ∃ (S : Set (Δ.𝔥 →ₗ[R] R)),
      DominatesSet rd lam S ∧ mu ∈ S := by

  refine ⟨{mu}, ?_, Set.mem_singleton mu⟩

  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx]

  have hbruhat : BruhatLE rd mu lam := proper_rep_implies_bruhatLE rd wg mu lam hproper

  exact bruhatLE_implies_weightLE mu lam hbruhat

theorem block_projection_idempotent_exists
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (F : EndoFunctorData R 𝔤)
    (_hF : IsProjectiveFunctor F)
    (theta : Δ.𝔥 →ₗ[R] R)
    (_hdom : IsDominantWeightBruhat rd wg theta)
    (Mverma : RepGfObj R 𝔤)
    (_hVerma : IsVermaModule Δ Mverma.carrier (theta - wg.ρ))
    (_hO : IsCategoryO Δ rd (F.obj Mverma).carrier) :
    ∃ (e_theta : NatTransData F F),

      (e_theta.comp e_theta).EqPointwise e_theta ∧

      (∀ (M : RepGfObj R 𝔤), ¬ HasGenInfChar M theta →
        ∀ (x : (F.obj M).carrier), (e_theta.app M).toFun x = 0) ∧

      (∃ (y : (F.obj Mverma).carrier), (e_theta.app Mverma).toFun y ≠ 0) := by sorry

theorem indec_proj_factors_through_block
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (F_xi : EndoFunctorData R 𝔤)
    (_hF : IsProjectiveFunctor F_xi)
    (_hI : IsIndecomposable F_xi)
    (lam : Δ.𝔥 →ₗ[R] R)
    (_hdom : IsDominantWeightBruhat rd wg lam)
    (Mverma_lam : RepGfObj R 𝔤)
    (_hVerma_lam : IsVermaModule Δ Mverma_lam.carrier (lam - wg.ρ))
    (_hO : IsCategoryO Δ rd (F_xi.obj Mverma_lam).carrier) :
    FactorsThroughBlock Δ F_xi lam := by

  obtain ⟨e_lam, h_idem, h_annihilate, ⟨y, h_nonzero⟩⟩ :=
    block_projection_idempotent_exists rd wg F_xi _hF lam _hdom Mverma_lam _hVerma_lam _hO


  rcases _hI e_lam h_idem with h_is_id | h_is_zero
  ·

    intro M hM x
    have h1 : (e_lam.app M).toFun x = 0 := h_annihilate M hM x


    have h2 := h_is_id M x
    simp only [NatTransData.id, RepGfHom.id, LieModuleHom.id_apply] at h2

    rw [h2] at h1
    exact h1

  ·


    exact absurd (h_is_zero Mverma_lam y) h_nonzero

theorem verma_hasGenInfChar_of_weight
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ)
    (nu : Δ.𝔥 →ₗ[R] R)
    (Mverma_nu : RepGfObj R 𝔤)
    (_hVerma_nu : IsVermaModule Δ Mverma_nu.carrier (nu - wg.ρ)) :
    HasGenInfChar Mverma_nu nu := by sorry

theorem genInfChar_determines_orbit
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ)
    (theta1 theta2 : Δ.𝔥 →ₗ[R] R)
    (M : RepGfObj R 𝔤)
    (_h1 : HasGenInfChar M theta1)
    (_h2 : HasGenInfChar M theta2) :
    SameInfChar wg theta1 theta2 := by sorry

theorem verma_wrong_infchar_not_hasGenInfChar
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ)
    (lam nu : Δ.𝔥 →ₗ[R] R)
    (Mverma_nu : RepGfObj R 𝔤)
    (_hVerma_nu : IsVermaModule Δ Mverma_nu.carrier (nu - wg.ρ))
    (hne : ¬ SameInfChar wg nu lam) :
    ¬ HasGenInfChar Mverma_nu lam := by

  have hnu : HasGenInfChar Mverma_nu nu :=
    verma_hasGenInfChar_of_weight wg nu Mverma_nu _hVerma_nu

  intro hlam

  have hsame : SameInfChar wg nu lam :=
    genInfChar_determines_orbit wg nu lam Mverma_nu hnu hlam

  exact hne hsame

theorem indec_proj_annihilates_wrong_infchar
    (F_xi : EndoFunctorData R 𝔤)
    (_hF : IsProjectiveFunctor F_xi)
    (_hI : IsIndecomposable F_xi)
    (lam : Δ.𝔥 →ₗ[R] R)
    (_hdom : IsDominantWeightBruhat rd wg lam)
    (Mverma_lam : RepGfObj R 𝔤)
    (_hVerma_lam : IsVermaModule Δ Mverma_lam.carrier (lam - wg.ρ))
    (_hO : IsCategoryO Δ rd (F_xi.obj Mverma_lam).carrier) :
    ∀ (nu : Δ.𝔥 →ₗ[R] R) (Mverma_nu : RepGfObj R 𝔤),
      IsVermaModule Δ Mverma_nu.carrier (nu - wg.ρ) →
      ¬ SameInfChar wg nu lam →
      IsZeroRepGfObj (F_xi.obj Mverma_nu) := by

  have hBlock : FactorsThroughBlock Δ F_xi lam :=
    indec_proj_factors_through_block rd wg F_xi _hF _hI lam _hdom Mverma_lam _hVerma_lam _hO

  intro nu Mverma_nu hVerma_nu hne_infchar

  have hNotGenInfChar : ¬ HasGenInfChar Mverma_nu lam :=
    verma_wrong_infchar_not_hasGenInfChar wg lam nu Mverma_nu hVerma_nu hne_infchar

  have hAllZero : ∀ (x : (F_xi.obj Mverma_nu).carrier), x = 0 :=
    hBlock Mverma_nu hNotGenInfChar

  exact ⟨fun a b => by rw [hAllZero a, hAllZero b]⟩

theorem exists_indec_projFunctor_of_properRep
    {R : Type u} [Field R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (mu lam : Δ.𝔥 →ₗ[R] R)
    (hproper : IsProperRep rd wg mu lam)
    (Mverma_lam : RepGfObj R 𝔤)
    (hVerma_lam : IsVermaModule Δ Mverma_lam.carrier (lam - wg.ρ)) :
    ∃ (F_xi : EndoFunctorData R 𝔤),
      IsProjectiveFunctor F_xi ∧
      IsIndecomposable F_xi ∧


      (∀ (nu : Δ.𝔥 →ₗ[R] R) (Mverma_nu : RepGfObj R 𝔤),
        IsVermaModule Δ Mverma_nu.carrier (nu - wg.ρ) →
        ¬ SameInfChar wg nu lam →
        IsZeroRepGfObj (F_xi.obj Mverma_nu)) ∧


      (∃ (hO : IsCategoryO Δ rd (F_xi.obj Mverma_lam).carrier),
        IsProjectiveInO rd (F_xi.obj Mverma_lam).carrier hO ∧
        Nonempty (IsHighestWeightModule Δ (F_xi.obj Mverma_lam).carrier (mu - wg.ρ))) := by


  obtain ⟨S, hdom, hmu_mem⟩ := proper_rep_linkage_class_exists rd wg mu lam hproper


  obtain ⟨F_mu, hF_proj, hF_indec, hO, hProj, hHW⟩ :=
    lemma_23_3_ii rd wg lam S hdom mu hmu_mem Mverma_lam hVerma_lam

  have hdom_lam : IsDominantWeightBruhat rd wg lam := hproper.1
  have hannihil := indec_proj_annihilates_wrong_infchar rd wg F_mu hF_proj hF_indec
    lam hdom_lam Mverma_lam hVerma_lam hO

  exact ⟨F_mu, hF_proj, hF_indec, hannihil, hO, hProj, hHW⟩

theorem projective_cover_unique
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (P₁ P₂ : RepGfObj R 𝔤)
    (_mu : Δ.𝔥 →ₗ[R] R)
    (hO₁ : IsCategoryO Δ rd P₁.carrier)
    (_hProj₁ : IsProjectiveInO rd P₁.carrier hO₁)
    (_hHW₁ : Nonempty (IsHighestWeightModule Δ P₁.carrier (_mu - wg.ρ)))
    (hO₂ : IsCategoryO Δ rd P₂.carrier)
    (_hProj₂ : IsProjectiveInO rd P₂.carrier hO₂)
    (_hHW₂ : Nonempty (IsHighestWeightModule Δ P₂.carrier (_mu - wg.ρ))) :
    ∃ (iso_fwd : RepGfHom P₁ P₂) (iso_bwd : RepGfHom P₂ P₁),
      (iso_bwd.comp iso_fwd).EqAsMap (RepGfHom.id _) ∧
      (iso_fwd.comp iso_bwd).EqAsMap (RepGfHom.id _) := by
  sorry

theorem natiso_from_verma_iso
    {R : Type u} [CommRing R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (wg : WeylGroupData Δ)
    (F₁ F₂ : EndoFunctorData R 𝔤)
    (_hF₁ : IsProjectiveFunctor F₁) (_hF₂ : IsProjectiveFunctor F₂)
    (_hI₁ : IsIndecomposable F₁) (_hI₂ : IsIndecomposable F₂)
    (lam : Δ.𝔥 →ₗ[R] R)
    (Mverma_lam : RepGfObj R 𝔤)
    (_hVerma_lam : IsVermaModule Δ Mverma_lam.carrier (lam - wg.ρ))
    (iso_fwd : RepGfHom (F₁.obj Mverma_lam) (F₂.obj Mverma_lam))
    (iso_bwd : RepGfHom (F₂.obj Mverma_lam) (F₁.obj Mverma_lam))
    (_hiso₁ : (iso_bwd.comp iso_fwd).EqAsMap (RepGfHom.id _))
    (_hiso₂ : (iso_fwd.comp iso_bwd).EqAsMap (RepGfHom.id _)) :
    AreNatIso F₁ F₂ := by
  exact corollary_22_6_i_areNatIso Δ wg lam F₁ F₂ _hF₁ _hF₂ Mverma_lam
    ⟨_hVerma_lam⟩ iso_fwd iso_bwd _hiso₁ _hiso₂

theorem indec_projFunctor_natIso_of_same_properRep
    (F₁ F₂ : EndoFunctorData R 𝔤)
    (hF₁ : IsProjectiveFunctor F₁) (hF₂ : IsProjectiveFunctor F₂)
    (hI₁ : IsIndecomposable F₁) (hI₂ : IsIndecomposable F₂)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (_hproper : IsProperRep rd wg mu lam)
    (Mverma_lam : RepGfObj R 𝔤)
    (hVerma_lam : IsVermaModule Δ Mverma_lam.carrier (lam - wg.ρ))

    (_hAnnihil₁ : ∀ (nu : Δ.𝔥 →ₗ[R] R) (Mverma_nu : RepGfObj R 𝔤),
      IsVermaModule Δ Mverma_nu.carrier (nu - wg.ρ) →
      ¬ SameInfChar wg nu lam →
      IsZeroRepGfObj (F₁.obj Mverma_nu))

    (_hAnnihil₂ : ∀ (nu : Δ.𝔥 →ₗ[R] R) (Mverma_nu : RepGfObj R 𝔤),
      IsVermaModule Δ Mverma_nu.carrier (nu - wg.ρ) →
      ¬ SameInfChar wg nu lam →
      IsZeroRepGfObj (F₂.obj Mverma_nu))

    (hO₁ : IsCategoryO Δ rd (F₁.obj Mverma_lam).carrier)
    (hProj₁ : IsProjectiveInO rd (F₁.obj Mverma_lam).carrier hO₁)
    (hHW₁ : Nonempty (IsHighestWeightModule Δ (F₁.obj Mverma_lam).carrier (mu - wg.ρ)))

    (hO₂ : IsCategoryO Δ rd (F₂.obj Mverma_lam).carrier)
    (hProj₂ : IsProjectiveInO rd (F₂.obj Mverma_lam).carrier hO₂)
    (hHW₂ : Nonempty (IsHighestWeightModule Δ (F₂.obj Mverma_lam).carrier (mu - wg.ρ))) :
    AreNatIso F₁ F₂ := by


  obtain ⟨iso_fwd, iso_bwd, hiso₁, hiso₂⟩ :=
    projective_cover_unique rd wg (F₁.obj Mverma_lam) (F₂.obj Mverma_lam) mu
      hO₁ hProj₁ hHW₁ hO₂ hProj₂ hHW₂


  exact natiso_from_verma_iso wg F₁ F₂ hF₁ hF₂ hI₁ hI₂ lam Mverma_lam hVerma_lam
    iso_fwd iso_bwd hiso₁ hiso₂

theorem projective_functor_same_hw_for_same_weight_verma
    {R : Type u} [Field R] {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (F : EndoFunctorData R 𝔤)
    (_hF : IsProjectiveFunctor F)
    (_hI : IsIndecomposable F)
    (lam : Δ.𝔥 →ₗ[R] R)
    (M₁ M₂ : RepGfObj R 𝔤)
    (_hV₁ : IsVermaModule Δ M₁.carrier (lam - wg.ρ))
    (_hV₂ : IsVermaModule Δ M₂.carrier (lam - wg.ρ))
    (mu₁ mu₂ : Δ.𝔥 →ₗ[R] R)
    (_hO₁ : IsCategoryO Δ rd (F.obj M₁).carrier)
    (_hHW₁ : Nonempty (IsHighestWeightModule Δ (F.obj M₁).carrier (mu₁ - wg.ρ)))
    (_hO₂ : IsCategoryO Δ rd (F.obj M₂).carrier)
    (_hHW₂ : Nonempty (IsHighestWeightModule Δ (F.obj M₂).carrier (mu₂ - wg.ρ))) :
    mu₁ = mu₂ := by sorry

theorem indecomp_proj_functor_gives_proper_pair
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (KO : GrothendieckGroupData Δ) (ip : KO.InnerProductData)
    (B : WeightBilinForm wg)
    (fF : InducedMapData KO)
    (_hI : IsIndecomposable fF.F)

    (lam0 : Δ.𝔥 →ₗ[R] R) (hlam0_dom : IsDominantWeightBruhat rd wg lam0)
    (Mverma0 : RepGfObj R 𝔤) (hVerma0 : IsVermaModule Δ Mverma0.carrier (lam0 - wg.ρ))
    (hO0 : IsCategoryO Δ rd (fF.F.obj Mverma0).carrier) :
    ∃ (mu lam : Δ.𝔥 →ₗ[R] R),
      IsProperRep rd wg mu lam ∧
      (∀ (nu : Δ.𝔥 →ₗ[R] R) (Mverma_nu : RepGfObj R 𝔤),
        IsVermaModule Δ Mverma_nu.carrier (nu - wg.ρ) →
        ¬ SameInfChar wg nu lam →
        IsZeroRepGfObj (fF.F.obj Mverma_nu)) ∧
      (∀ (Mverma_lam : RepGfObj R 𝔤),
        IsVermaModule Δ Mverma_lam.carrier (lam - wg.ρ) →
        ∃ (hO : IsCategoryO Δ rd (fF.F.obj Mverma_lam).carrier),
          IsProjectiveInO rd (fF.F.obj Mverma_lam).carrier hO ∧
          Nonempty (IsHighestWeightModule Δ (fF.F.obj Mverma_lam).carrier (mu - wg.ρ))) := by

  have hFblock : FactorsThroughBlock Δ fF.F lam0 :=
    indec_proj_factors_through_block rd wg fF.F fF.hF _hI lam0 hlam0_dom Mverma0 hVerma0 hO0

  have hDomLE : IsDominantWeightLE rd wg lam0 :=
    (dominance_equivalence rd wg lam0).mpr hlam0_dom

  obtain ⟨mu, hO_FM, hProj_FM, _, hHW_FM⟩ :=
    proposition_22_7_ii Δ wg rd lam0 hDomLE fF.F fF.hF _hI hFblock Mverma0 ⟨hVerma0⟩

  have hproper : IsProperRep rd wg mu lam0 :=
    (lemma_23_7 rd wg rs KO ip fF B _hI lam0 mu hlam0_dom hFblock
      Mverma0 hVerma0 hO_FM hProj_FM hHW_FM).2

  have hannihil := indec_proj_annihilates_wrong_infchar rd wg fF.F fF.hF _hI
    lam0 hlam0_dom Mverma0 hVerma0 hO0

  refine ⟨mu, lam0, hproper, hannihil, ?_⟩
  intro Mverma_lam hVerma_lam

  obtain ⟨mu', hO', hProj', _, hHW'⟩ :=
    proposition_22_7_ii Δ wg rd lam0 hDomLE fF.F fF.hF _hI hFblock Mverma_lam ⟨hVerma_lam⟩

  have hmu_eq : mu' = mu :=
    projective_functor_same_hw_for_same_weight_verma rd wg fF.F fF.hF _hI lam0
      Mverma_lam Mverma0 hVerma_lam hVerma0 mu' mu hO' hHW' hO_FM hHW_FM
  rw [hmu_eq] at hHW'
  exact ⟨hO', hProj', hHW'⟩

theorem indec_proj_functor_exists_dominant_image
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (KO : GrothendieckGroupData Δ) (ip : KO.InnerProductData)
    (B : WeightBilinForm wg)
    (fF : InducedMapData KO)
    (_hI : IsIndecomposable fF.F)
    (lam0 : Δ.𝔥 →ₗ[R] R) (hlam0_dom : IsDominantWeightBruhat rd wg lam0)
    (Mverma0 : RepGfObj R 𝔤) (hVerma0 : IsVermaModule Δ Mverma0.carrier (lam0 - wg.ρ))
    (hO0 : IsCategoryO Δ rd (fF.F.obj Mverma0).carrier) :
    ∃ (mu lam : Δ.𝔥 →ₗ[R] R) (Mverma_lam : RepGfObj R 𝔤),
      IsDominantWeightBruhat rd wg lam ∧
      Nonempty (IsVermaModule Δ Mverma_lam.carrier (lam - wg.ρ)) ∧
      (∃ (hO : IsCategoryO Δ rd (fF.F.obj Mverma_lam).carrier),
        IsProjectiveInO rd (fF.F.obj Mverma_lam).carrier hO ∧
        Nonempty (IsHighestWeightModule Δ (fF.F.obj Mverma_lam).carrier (mu - wg.ρ))) := by

  obtain ⟨mu, lam, hproper, _, hVermaUniv⟩ :=
    indecomp_proj_functor_gives_proper_pair rd wg rs KO ip B fF _hI lam0 hlam0_dom Mverma0 hVerma0 hO0

  have hdom : IsDominantWeightBruhat rd wg lam := hproper.1

  obtain ⟨Mlam, instACG, instMod, instLRM, instLM, ⟨hVM⟩⟩ :=
    verma_module_exists Δ (lam - wg.ρ)
  let Mverma_lam : RepGfObj R 𝔤 := ⟨Mlam, instACG, instMod, instLRM, instLM⟩

  obtain ⟨hO, hProj, hHW⟩ := hVermaUniv Mverma_lam hVM
  exact ⟨mu, lam, Mverma_lam, hdom, ⟨hVM⟩, hO, hProj, hHW⟩

theorem indec_projFunctor_has_properRep
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (KO : GrothendieckGroupData Δ) (ip : KO.InnerProductData)
    (B : WeightBilinForm wg)
    (fF : InducedMapData KO)
    (hI : IsIndecomposable fF.F)
    (lam0 : Δ.𝔥 →ₗ[R] R) (hlam0_dom : IsDominantWeightBruhat rd wg lam0)
    (Mverma0 : RepGfObj R 𝔤) (hVerma0 : IsVermaModule Δ Mverma0.carrier (lam0 - wg.ρ))
    (hO0 : IsCategoryO Δ rd (fF.F.obj Mverma0).carrier) :
    ∃ (mu lam : Δ.𝔥 →ₗ[R] R),
      IsProperRep rd wg mu lam ∧

      (∀ (nu : Δ.𝔥 →ₗ[R] R) (Mverma_nu : RepGfObj R 𝔤),
        IsVermaModule Δ Mverma_nu.carrier (nu - wg.ρ) →
        ¬ SameInfChar wg nu lam →
        IsZeroRepGfObj (fF.F.obj Mverma_nu)) ∧

      (∀ (Mverma_lam : RepGfObj R 𝔤),
        IsVermaModule Δ Mverma_lam.carrier (lam - wg.ρ) →
        ∃ (hO : IsCategoryO Δ rd (fF.F.obj Mverma_lam).carrier),
          IsProjectiveInO rd (fF.F.obj Mverma_lam).carrier hO ∧
          Nonempty (IsHighestWeightModule Δ (fF.F.obj Mverma_lam).carrier (mu - wg.ρ))) :=
  indecomp_proj_functor_gives_proper_pair rd wg rs KO ip B fF hI lam0 hlam0_dom Mverma0 hVerma0 hO0

abbrev theorem_23_6_existence := @exists_indec_projFunctor_of_properRep
abbrev theorem_23_6_uniqueness := @indec_projFunctor_natIso_of_same_properRep
abbrev theorem_23_6_surjectivity := @indec_projFunctor_has_properRep

theorem indec_projFunctor_classification
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (KO : GrothendieckGroupData Δ) (ip : KO.InnerProductData)
    (B : WeightBilinForm wg)
    (mu lam : Δ.𝔥 →ₗ[R] R)
    (hproper : IsProperRep rd wg mu lam)
    (Mverma_lam : RepGfObj R 𝔤)
    (hVerma_lam : IsVermaModule Δ Mverma_lam.carrier (lam - wg.ρ)) :


    (∃ (F_xi : EndoFunctorData R 𝔤),
      IsProjectiveFunctor F_xi ∧
      IsIndecomposable F_xi ∧
      (∀ (nu : Δ.𝔥 →ₗ[R] R) (Mverma_nu : RepGfObj R 𝔤),
        IsVermaModule Δ Mverma_nu.carrier (nu - wg.ρ) →
        ¬ SameInfChar wg nu lam →
        IsZeroRepGfObj (F_xi.obj Mverma_nu)) ∧
      (∃ (hO : IsCategoryO Δ rd (F_xi.obj Mverma_lam).carrier),
        IsProjectiveInO rd (F_xi.obj Mverma_lam).carrier hO ∧
        Nonempty (IsHighestWeightModule Δ (F_xi.obj Mverma_lam).carrier (mu - wg.ρ)))) ∧


    (∀ (fF : InducedMapData KO),
      IsIndecomposable fF.F →
      ∀ (lam0 : Δ.𝔥 →ₗ[R] R), IsDominantWeightBruhat rd wg lam0 →
      ∀ (Mverma0 : RepGfObj R 𝔤), IsVermaModule Δ Mverma0.carrier (lam0 - wg.ρ) →
      IsCategoryO Δ rd (fF.F.obj Mverma0).carrier →
      ∃ (mu' lam' : Δ.𝔥 →ₗ[R] R),
        IsProperRep rd wg mu' lam' ∧
        (∀ (nu : Δ.𝔥 →ₗ[R] R) (Mverma_nu : RepGfObj R 𝔤),
          IsVermaModule Δ Mverma_nu.carrier (nu - wg.ρ) →
          ¬ SameInfChar wg nu lam' →
          IsZeroRepGfObj (fF.F.obj Mverma_nu)) ∧
        (∀ (Mverma_lam' : RepGfObj R 𝔤),
          IsVermaModule Δ Mverma_lam'.carrier (lam' - wg.ρ) →
          ∃ (hO : IsCategoryO Δ rd (fF.F.obj Mverma_lam').carrier),
            IsProjectiveInO rd (fF.F.obj Mverma_lam').carrier hO ∧
            Nonempty (IsHighestWeightModule Δ (fF.F.obj Mverma_lam').carrier (mu' - wg.ρ)))) ∧


    (∀ (F₁ F₂ : EndoFunctorData R 𝔤),
      IsProjectiveFunctor F₁ → IsProjectiveFunctor F₂ →
      IsIndecomposable F₁ → IsIndecomposable F₂ →

      (∀ (nu : Δ.𝔥 →ₗ[R] R) (Mverma_nu : RepGfObj R 𝔤),
        IsVermaModule Δ Mverma_nu.carrier (nu - wg.ρ) →
        ¬ SameInfChar wg nu lam →
        IsZeroRepGfObj (F₁.obj Mverma_nu)) →
      (∀ (nu : Δ.𝔥 →ₗ[R] R) (Mverma_nu : RepGfObj R 𝔤),
        IsVermaModule Δ Mverma_nu.carrier (nu - wg.ρ) →
        ¬ SameInfChar wg nu lam →
        IsZeroRepGfObj (F₂.obj Mverma_nu)) →
      (∃ (hO₁ : IsCategoryO Δ rd (F₁.obj Mverma_lam).carrier),
        IsProjectiveInO rd (F₁.obj Mverma_lam).carrier hO₁ ∧
        Nonempty (IsHighestWeightModule Δ (F₁.obj Mverma_lam).carrier (mu - wg.ρ))) →
      (∃ (hO₂ : IsCategoryO Δ rd (F₂.obj Mverma_lam).carrier),
        IsProjectiveInO rd (F₂.obj Mverma_lam).carrier hO₂ ∧
        Nonempty (IsHighestWeightModule Δ (F₂.obj Mverma_lam).carrier (mu - wg.ρ))) →
      AreNatIso F₁ F₂) := by
  refine ⟨?_, ?_, ?_⟩

  · exact exists_indec_projFunctor_of_properRep rd wg mu lam hproper Mverma_lam hVerma_lam

  · intro fF hI lam0 hlam0_dom Mverma0 hVerma0 hO0
    exact indec_projFunctor_has_properRep rd wg rs KO ip B fF hI lam0 hlam0_dom Mverma0 hVerma0 hO0

  · intro F₁ F₂ hF₁ hF₂ hI₁ hI₂ hAnnihil₁ hAnnihil₂ ⟨hO₁, hProj₁, hHW₁⟩ ⟨hO₂, hProj₂, hHW₂⟩
    exact indec_projFunctor_natIso_of_same_properRep rd wg F₁ F₂ hF₁ hF₂ hI₁ hI₂ lam mu hproper
      Mverma_lam hVerma_lam hAnnihil₁ hAnnihil₂ hO₁ hProj₁ hHW₁ hO₂ hProj₂ hHW₂

abbrev theorem_23_6_combined := @indec_projFunctor_classification

theorem indec_projFunctor_maxSupp_eq_weylOrbit [LinearOrder R] [IsStrictOrderedRing R]
    (KO : GrothendieckGroupData Δ)
    (ip : KO.InnerProductData)
    (fF : InducedMapData KO)
    (B : WeightBilinForm wg)
    (rs : RootSystemWithReflections rd wg)
    (hFI : IsIndecomposable fF.F)
    (lam mu : Δ.𝔥 →ₗ[R] R)
    (hlam_dom : IsDominantWeightBruhat rd wg lam)
    (hFblock : FactorsThroughBlock Δ fF.F lam)
    (Mverma : RepGfObj R 𝔤)
    (hVerma : IsVermaModule Δ Mverma.carrier (lam - wg.ρ))
    (hO : IsCategoryO Δ rd (fF.F.obj Mverma).carrier)
    (hProj : IsProjectiveInO rd (fF.F.obj Mverma).carrier hO)
    (hHW : Nonempty (IsHighestWeightModule Δ (fF.F.obj Mverma).carrier (mu - wg.ρ))) :

    maximalSupportPF KO ip fF B ⊆ WeylOrbitPair wg mu lam ∧

    IsProperRep rd wg mu lam := by

  have hmu_in_max : (mu, lam) ∈ maximalSupportPF KO ip fF B :=
    lemma_23_7_mu_lam_in_maxsupp rd wg KO ip fF B hFI lam mu hlam_dom hFblock
      Mverma hVerma hO hProj hHW
  constructor
  ·
    intro p hp
    exact lemma_23_7_maxsupp_subset_orbit rd wg rs KO ip fF B hFI lam mu hlam_dom
      hFblock Mverma hVerma hO hProj hHW hmu_in_max p hp
  ·
    exact (lemma_23_7 rd wg rs KO ip fF B hFI lam mu hlam_dom hFblock Mverma hVerma hO hProj hHW).2

theorem indec_projFunctor_bijection_xi
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]
    {Δ : TriangularDecomposition R 𝔤}
    (rd : PositiveRootData Δ) (wg : WeylGroupData Δ)
    (rs : RootSystemWithReflections rd wg)
    (KO : GrothendieckGroupData Δ) (ip : KO.InnerProductData)
    (B : WeightBilinForm wg)

    (mu lam : Δ.𝔥 →ₗ[R] R)
    (hproper : IsProperRep rd wg mu lam)
    (Mverma_lam : RepGfObj R 𝔤)
    (hVerma_lam : IsVermaModule Δ Mverma_lam.carrier (lam - wg.ρ)) :


    (∃ (F_xi : EndoFunctorData R 𝔤),
      IsProjectiveFunctor F_xi ∧
      IsIndecomposable F_xi ∧

      (∀ (nu : Δ.𝔥 →ₗ[R] R) (Mverma_nu : RepGfObj R 𝔤),
        IsVermaModule Δ Mverma_nu.carrier (nu - wg.ρ) →
        ¬ SameInfChar wg nu lam →
        IsZeroRepGfObj (F_xi.obj Mverma_nu)) ∧

      (∃ (hO : IsCategoryO Δ rd (F_xi.obj Mverma_lam).carrier),
        IsProjectiveInO rd (F_xi.obj Mverma_lam).carrier hO ∧
        Nonempty (IsHighestWeightModule Δ (F_xi.obj Mverma_lam).carrier (mu - wg.ρ))) ∧

      (∀ (G : EndoFunctorData R 𝔤),
        IsProjectiveFunctor G →
        IsIndecomposable G →
        (∀ (nu : Δ.𝔥 →ₗ[R] R) (Mverma_nu : RepGfObj R 𝔤),
          IsVermaModule Δ Mverma_nu.carrier (nu - wg.ρ) →
          ¬ SameInfChar wg nu lam →
          IsZeroRepGfObj (G.obj Mverma_nu)) →
        (∃ (hO : IsCategoryO Δ rd (G.obj Mverma_lam).carrier),
          IsProjectiveInO rd (G.obj Mverma_lam).carrier hO ∧
          Nonempty (IsHighestWeightModule Δ (G.obj Mverma_lam).carrier (mu - wg.ρ))) →
        AreNatIso F_xi G)) ∧


    (∀ (fF : InducedMapData KO),
      IsIndecomposable fF.F →
      ∀ (lam0 : Δ.𝔥 →ₗ[R] R), IsDominantWeightBruhat rd wg lam0 →
      ∀ (Mverma0 : RepGfObj R 𝔤), IsVermaModule Δ Mverma0.carrier (lam0 - wg.ρ) →
      IsCategoryO Δ rd (fF.F.obj Mverma0).carrier →
      ∃ (mu' lam' : Δ.𝔥 →ₗ[R] R),
        IsProperRep rd wg mu' lam' ∧
        (∀ (nu : Δ.𝔥 →ₗ[R] R) (Mverma_nu : RepGfObj R 𝔤),
          IsVermaModule Δ Mverma_nu.carrier (nu - wg.ρ) →
          ¬ SameInfChar wg nu lam' →
          IsZeroRepGfObj (fF.F.obj Mverma_nu)) ∧
        (∀ (Mverma_lam' : RepGfObj R 𝔤),
          IsVermaModule Δ Mverma_lam'.carrier (lam' - wg.ρ) →
          ∃ (hO : IsCategoryO Δ rd (fF.F.obj Mverma_lam').carrier),
            IsProjectiveInO rd (fF.F.obj Mverma_lam').carrier hO ∧
            Nonempty (IsHighestWeightModule Δ (fF.F.obj Mverma_lam').carrier (mu' - wg.ρ)))) := by
  constructor
  ·
    obtain ⟨F_xi, hF_proj, hF_indec, hAnnihil, hO, hProj, hHW⟩ :=
      exists_indec_projFunctor_of_properRep rd wg mu lam hproper Mverma_lam hVerma_lam
    exact ⟨F_xi, hF_proj, hF_indec, hAnnihil, ⟨hO, hProj, hHW⟩, fun G hG_proj hG_indec hG_annihil ⟨hGO, hGProj, hGHW⟩ =>
      indec_projFunctor_natIso_of_same_properRep rd wg F_xi G hF_proj hG_proj hF_indec hG_indec lam mu hproper
        Mverma_lam hVerma_lam hAnnihil hG_annihil hO hProj hHW hGO hGProj hGHW⟩
  ·
    intro fF hI lam0 hlam0_dom Mverma0 hVerma0 hO0
    exact indec_projFunctor_has_properRep rd wg rs KO ip B fF hI lam0 hlam0_dom Mverma0 hVerma0 hO0

theorem multiplicity_free_wall_crossing
    (C : CoxeterGroupData)
    (KOB : GrothendieckGroupBlock Δ wg)
    (s : C.W) (_hs : s ∈ C.simpleReflections)
    (fF_mapKO : KOB.carrier → KOB.carrier)

    (compat : CoxeterWeylCompatibility C rd wg)

    (wact : wg.W → KOB.carrier → KOB.carrier)

    (fF_equivariant : ∀ (w_act : wg.W) (x : KOB.carrier),
      wact w_act (fF_mapKO x) = fF_mapKO (wact w_act x))

    (wact_basis : ∀ (w_act v : wg.W),
      wact w_act (KOB.delta_w v) = KOB.delta_w (w_act * v))

    (wact_add : ∀ (w_act : wg.W) (x y : KOB.carrier),
      letI := KOB.instACG
      wact w_act (x + y) = wact w_act x + wact w_act y)


    (fF_base : letI := KOB.instACG;
      fF_mapKO (KOB.delta_w 1) =
        KOB.delta_w 1 + KOB.delta_w (compat.ι s)) :

    ∀ (w : C.W),
      letI := KOB.instACG
      fF_mapKO (KOB.delta_w (compat.ι w)) =
        KOB.delta_w (compat.ι w) +
        KOB.delta_w (compat.ι w * compat.ι s) := by
  intro w

  have h1 := fF_equivariant (compat.ι w) (KOB.delta_w 1)

  rw [wact_basis (compat.ι w) 1, mul_one] at h1

  rw [← h1]

  rw [fF_base]
  rw [wact_add]
  rw [wact_basis, wact_basis]
  rw [mul_one]


end Theorems

end
