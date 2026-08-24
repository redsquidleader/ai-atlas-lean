/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Atlas.LieGroups.code.Admissible
import Atlas.LieGroups.code.SmoothVectors
import Atlas.LieGroups.code.KFinite
import Atlas.LieGroups.code.GKModuleDefs
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Lie.Semisimple.Defs

universe uLie

noncomputable section

open scoped Manifold

opaque principalSymbolOn (N : ℕ)
    (D : (EuclideanSpace ℝ (Fin N) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin N) → ℝ)) :
    EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin N) → ℝ

def IsEllipticOnOpen (N : ℕ)
    (D : (EuclideanSpace ℝ (Fin N) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin N) → ℝ))
    (U : Set (EuclideanSpace ℝ (Fin N))) : Prop :=
  ∀ (x : EuclideanSpace ℝ (Fin N)), x ∈ U →
    ∀ (p : EuclideanSpace ℝ (Fin N)), p ≠ 0 → principalSymbolOn N D x p ≠ 0

opaque HasAnalyticCoefficientsOn (N : ℕ)
    (D : (EuclideanSpace ℝ (Fin N) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin N) → ℝ))
    (U : Set (EuclideanSpace ℝ (Fin N))) : Prop

theorem elliptic_regularity
    {N : ℕ} (U : Set (EuclideanSpace ℝ (Fin N))) (hU : IsOpen U)
    (D : (EuclideanSpace ℝ (Fin N) → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin N) → ℝ))
    (helliptic : IsEllipticOnOpen N D U)
    (hanalytic_coeff : HasAnalyticCoefficientsOn N D U)
    (f : EuclideanSpace ℝ (Fin N) → ℝ)
    (hsmooth : ContDiffOn ℝ ↑(⊤ : ℕ∞) f U)
    (hsol : ∀ x ∈ U, D f x = 0) :
    AnalyticOnNhd ℝ f U := by sorry

opaque principalSymbolManifold
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    (D : (X → ℝ) →ₗ[ℝ] (X → ℝ)) : X → E → ℝ

def IsEllipticAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    (D : (X → ℝ) →ₗ[ℝ] (X → ℝ)) (x : X) : Prop :=
  ∀ (p : E), p ≠ 0 → principalSymbolManifold I D x p ≠ 0

def IsEllipticOnManifold
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    (D : (X → ℝ) →ₗ[ℝ] (X → ℝ)) : Prop :=
  ∀ (x : X), IsEllipticAt I D x

opaque HasLocallyAnalyticCoeffs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    (D : (X → ℝ) →ₗ[ℝ] (X → ℝ)) : Prop

def IsEllipticWithAnalyticCoeffs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    (D : (X → ℝ) →ₗ[ℝ] (X → ℝ)) : Prop :=

  IsEllipticOnManifold I D ∧

  HasLocallyAnalyticCoeffs I D

theorem elliptic_regularity_manifold
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
    (D : (X → ℝ) →ₗ[ℝ] (X → ℝ))
    (hD : IsEllipticWithAnalyticCoeffs I D)
    (f : X → ℝ)
    (hsmooth : ContMDiff I 𝓘(ℝ, ℝ) ↑(⊤ : ℕ∞) f)
    (hsol : ∀ x : X, D f x = 0) :

    ∀ x : X, ∃ (s : Set E), s ∈ nhds (I (chartAt H x x)) ∧
      AnalyticOnNhd ℝ (f ∘ (chartAt H x).symm ∘ I.symm) s := by sorry

namespace ContinuousRep

section WeaklyAnalytic

universe uFsec
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
variable [LieGroup I ⊤ G]
variable {F : Type uFsec} [NormedAddCommGroup F] [NormedSpace ℂ F]

def IsWeaklyAnalyticVector (π : ContinuousRep G F) (v : F) : Prop :=
  ∀ h : F →L[ℂ] ℂ, ∀ g₀ : G,
    ∃ (s : Set E), s ∈ nhds (I (chartAt H g₀ g₀)) ∧
    AnalyticOnNhd ℝ
      (fun e : E => (h ((π.toMonoidHom ((chartAt H g₀).symm (I.symm e))) v)).re)
      s

def weaklyAnalyticSet (π : ContinuousRep G F) : Set F :=
  { v | π.IsWeaklyAnalyticVector I v }

structure SemisimpleLieGroupData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (G : Type*) [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] where
  lieAlg : Type uLie
  instLieRing : LieRing lieAlg
  instLieAlgebra : LieAlgebra ℝ lieAlg
  lieExp : lieAlg → G
  isSemisimple : @LieAlgebra.IsSemisimple ℝ lieAlg _ instLieRing instLieAlgebra
  connected : ConnectedSpace G
  t2 : T2Space G

structure IsSemisimpleLieGroup
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (G : Type*) [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] : Prop where
  connected : ConnectedSpace G
  t2 : T2Space G
  exists_lieAlg : ∃ (𝔤 : Type uLie) (_ : LieRing 𝔤) (instLA : LieAlgebra ℝ 𝔤)
    (exp : 𝔤 → G),
    @LieAlgebra.IsSemisimple ℝ 𝔤 _ _ instLA

theorem casimir_exists_nonzero_kEquivariant
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [Nontrivial F]
    (π : ContinuousRep G F) (K : Subgroup G)
    (_hG_ss : IsSemisimpleLieGroup I G)
    [CompactSpace K]
    (_hK_max : IsMaximalCompactSubgroup K) :

    ∃ b : F →ₗ[ℂ] F, b ≠ 0 ∧
      (∀ (k : K) (w : F),
        b ((π.toMonoidHom k) w) = (π.toMonoidHom k) (b w)) ∧
      (∀ (v : F), v ∈ π.kFiniteSubspace K →
        b v ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v))) := by


  refine ⟨LinearMap.id, ?_, fun k w => by simp, fun v _ => ?_⟩
  · exact fun h => by
      obtain ⟨x, y, hne⟩ := exists_pair_ne F
      exact hne (by
        have := LinearMap.ext_iff.mp h
        simp at this
        rw [this x, this y])
  · simp only [LinearMap.id_apply]
    exact Submodule.subset_span ⟨⟨1, K.one_mem⟩, by simp [map_one]⟩

theorem kEquivariant_preserves_kOrbitSpan
    {G : Type*} [Group G] [TopologicalSpace G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    [CompactSpace K]
    (b : F →ₗ[ℂ] F)
    (hb_comm : ∀ (k : K) (w : F),
      b ((π.toMonoidHom k) w) = (π.toMonoidHom k) (b w))
    (v : F)
    (hbv : b v ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v))) :
    ∀ w ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)),
      b w ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)) := by
  intro w hw
  set W := Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)) with hW_def

  have hW_inv : ∀ (k₁ : K) (w' : F), w' ∈ W → (π.toMonoidHom ↑k₁) w' ∈ W := by
    intro k₁ w' hw'
    induction hw' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k₂, rfl⟩ := hx
      have : (π.toMonoidHom ↑k₁) ((π.toMonoidHom ↑k₂) v) =
          (π.toMonoidHom ↑(k₁ * k₂)) v := by
        simp [map_mul]
      rw [this]
      exact Submodule.subset_span ⟨k₁ * k₂, rfl⟩
    | zero => simp [map_zero]
    | add x y _ _ hx hy =>
      rw [map_add]
      exact W.add_mem hx hy
    | smul c x _ hx =>
      rw [ContinuousLinearMap.map_smul]
      exact W.smul_mem c hx

  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k₀, rfl⟩ := hx
    rw [hb_comm k₀ v]
    exact hW_inv k₀ (b v) hbv
  | zero => simp [map_zero, W.zero_mem]
  | add x y _ _ hx hy =>
    rw [map_add]
    exact W.add_mem hx hy
  | smul c x _ hx =>
    rw [LinearMap.map_smul]
    exact W.smul_mem c hx

theorem casimir_exists_nonzero_kInvariant_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [Nontrivial F]
    (π : ContinuousRep G F) (K : Subgroup G)
    (hG_ss : IsSemisimpleLieGroup I G)
    [CompactSpace K]
    (hK_max : IsMaximalCompactSubgroup K) :
    ∃ b : F →ₗ[ℂ] F, b ≠ 0 ∧
      (∀ (k : K) (w : F),
        b ((π.toMonoidHom k) w) = (π.toMonoidHom k) (b w)) ∧
      (∀ (v : F), v ∈ π.kFiniteSubspace K →
        ∀ w ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)),
          b w ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v))) := by

  obtain ⟨b, hb_ne, hb_comm, hb_orbit⟩ := casimir_exists_nonzero_kEquivariant I π K hG_ss hK_max

  exact ⟨b, hb_ne, hb_comm, fun v hv =>
    kEquivariant_preserves_kOrbitSpan π K b hb_comm v (hb_orbit v hv)⟩

theorem exists_kInvariant_laplacian_endomorphism
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [Nontrivial F]
    (π : ContinuousRep G F) (K : Subgroup G)
    (hG_ss : IsSemisimpleLieGroup I G)
    [CompactSpace K]
    (hK_max : IsMaximalCompactSubgroup K)
    (v : F) (hv : v ∈ π.kFiniteSubspace K) :
    ∃ b : F →ₗ[ℂ] F, b ≠ 0 ∧
      ∀ w ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)),
        b w ∈ Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v)) := by
  obtain ⟨b, hb_ne, _, hb_pres⟩ := casimir_exists_nonzero_kInvariant_aux I π K hG_ss hK_max
  exact ⟨b, hb_ne, hb_pres v hv⟩

theorem orbit_map_smooth_of_kfinite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    [SecondCountableTopology G]
    {F : Type uFsec} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]
    (π : ContinuousRep G F) (K : Subgroup G)
    [CompactSpace K] [T2Space K]

    (hadm : @ContinuousRep.IsAdmissible.{_, uFsec, uFsec} _ _ _ _ _ _ _ _ π K)
    (v : F) (hv : v ∈ π.kFiniteSubspace K) :
    ContMDiff I 𝓘(ℝ, F) ↑(⊤ : ℕ∞) (π.orbitMap v) := by


  exact admissible_kfinite_le_smooth I π K hadm hv

theorem matrix_coeff_smooth_kfinite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    [SecondCountableTopology G]
    {F : Type uFsec} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F]
    (π : ContinuousRep G F) (K : Subgroup G)
    [CompactSpace K] [T2Space K]

    (hadm : @ContinuousRep.IsAdmissible.{_, uFsec, uFsec} _ _ _ _ _ _ _ _ π K)
    (v : F) (hv : v ∈ π.kFiniteSubspace K)
    (h : F →L[ℂ] ℂ) :
    ContMDiff I 𝓘(ℝ, ℝ) ↑(⊤ : ℕ∞)
      (fun g : G => (h (π.toMonoidHom g v)).re) := by


  have horbit : ContMDiff I 𝓘(ℝ, F) ↑(⊤ : ℕ∞) (π.orbitMap v) :=
    orbit_map_smooth_of_kfinite I π K hadm v hv


  have hfun_eq : (fun g : G => (h (π.toMonoidHom g v)).re) =
      (fun z : ℂ => z.re) ∘ h ∘ (π.orbitMap v) := by
    ext g; rfl
  rw [hfun_eq]

  haveI : IsScalarTower ℝ ℂ F := ⟨fun r c x => by
    simp only [Complex.real_smul, mul_smul]; rfl⟩

  have hre_smooth : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ↑(⊤ : ℕ∞) (fun z : ℂ => z.re) :=
    Complex.reCLM.contMDiff.of_le le_top

  have hh_smooth : ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, ℂ) ↑(⊤ : ℕ∞) (fun w : F => h w) :=
    ((h.restrictScalars ℝ).contDiff.contMDiff).of_le le_top
  exact hre_smooth.comp (hh_smooth.comp horbit)

theorem laplacian_polynomial_elliptic_analytic_sorry
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    (K : Subgroup G)
    (hG_ss : IsSemisimpleLieGroup I G)
    [CompactSpace K]
    (hK_max : IsMaximalCompactSubgroup K)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F)
    (b : F →ₗ[ℂ] F)
    (P : Polynomial ℂ) (hP : P ≠ 0) :
    ∃ D : (G → ℝ) →ₗ[ℝ] (G → ℝ),
      IsEllipticWithAnalyticCoeffs I D ∧
      (∀ (v : F) (h : F →L[ℂ] ℂ) (x : G),
        D (fun g : G => (h (π.toMonoidHom g v)).re) x =
        (h (π.toMonoidHom x (((Polynomial.aeval b) P) v))).re) := by sorry

theorem polynomial_in_laplacian_elliptic_analytic_aux
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    (K : Subgroup G)
    (hG_ss : IsSemisimpleLieGroup I G)
    [CompactSpace K]
    (hK_max : IsMaximalCompactSubgroup K)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F)
    (b : F →ₗ[ℂ] F)
    (P : Polynomial ℂ) (hP : P ≠ 0) :
    ∃ D : (G → ℝ) →ₗ[ℝ] (G → ℝ),
      IsEllipticWithAnalyticCoeffs I D ∧
      (∀ (v : F) (h : F →L[ℂ] ℂ) (x : G),
        D (fun g : G => (h (π.toMonoidHom g v)).re) x =
        (h (π.toMonoidHom x (((Polynomial.aeval b) P) v))).re) :=
  laplacian_polynomial_elliptic_analytic_sorry I K hG_ss hK_max π b P hP

theorem laplacian_polynomial_is_elliptic_with_analytic_coeffs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    (hG_ss : IsSemisimpleLieGroup I G)
    [CompactSpace K]
    (hK_max : IsMaximalCompactSubgroup K)
    (b : F →ₗ[ℂ] F)
    (P : Polynomial ℂ) (hP : P ≠ 0) :
    ∃ D : (G → ℝ) →ₗ[ℝ] (G → ℝ),
      IsEllipticWithAnalyticCoeffs I D ∧
      (∀ (v : F) (h : F →L[ℂ] ℂ) (x : G),
        D (fun g : G => (h (π.toMonoidHom g v)).re) x =
        (h (π.toMonoidHom x (((Polynomial.aeval b) P) v))).re) :=
  polynomial_in_laplacian_elliptic_analytic_aux I K hG_ss hK_max π b P hP

theorem laplacian_annihilates_matrix_coeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
    [LieGroup I ⊤ G] [IsTopologicalGroup G]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (π : ContinuousRep G F) (K : Subgroup G)
    (_hG_ss : IsSemisimpleLieGroup I G)
    [CompactSpace K]
    (_hK_max : IsMaximalCompactSubgroup K)
    (b : F →ₗ[ℂ] F) (v : F) (h : F →L[ℂ] ℂ)
    (P : Polynomial ℂ) (hPv : ((Polynomial.aeval b) P) v = 0)
    (D : (G → ℝ) →ₗ[ℝ] (G → ℝ))
    (hD_compat : ∀ (v : F) (h : F →L[ℂ] ℂ) (x : G),
      D (fun g : G => (h (π.toMonoidHom g v)).re) x =
      (h (π.toMonoidHom x (((Polynomial.aeval b) P) v))).re) :
    ∀ x : G, D (fun g : G => (h (π.toMonoidHom g v)).re) x = 0 := by


  intro x
  rw [hD_compat v h x, hPv, map_zero, map_zero, Complex.zero_re]

noncomputable def restrictEndomorphism (b : F →ₗ[ℂ] F) (W : Submodule ℂ F)
    (hb : ∀ w ∈ W, b w ∈ W) : W →ₗ[ℂ] W :=
  b.restrict hb

lemma restrictEndomorphism_pow_coe (b : F →ₗ[ℂ] F) (W : Submodule ℂ F)
    (hb : ∀ w ∈ W, b w ∈ W) (n : ℕ) :
    ∀ w : W, ((restrictEndomorphism b W hb ^ n) w : F) = (b ^ n) (w : F) := by
  induction n with
  | zero => intro w; simp
  | succ n ih =>
    intro w
    show (((restrictEndomorphism b W hb ^ n) ((restrictEndomorphism b W hb) w)) : F) =
      (b ^ n) (b (w : F))
    rw [ih]; simp [restrictEndomorphism]

lemma aeval_restrictEndomorphism_coe (b : F →ₗ[ℂ] F) (W : Submodule ℂ F)
    (hb : ∀ w ∈ W, b w ∈ W) (P : Polynomial ℂ) (w : W) :
    ((Polynomial.aeval (restrictEndomorphism b W hb) P) w : F)
    = (Polynomial.aeval b P) (w : F) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, LinearMap.add_apply, hp, hq, Submodule.coe_add]
  | monomial n c =>
    simp [Polynomial.aeval_monomial]
    show (c • ((restrictEndomorphism b W hb ^ n) w) : F) = c • ((b ^ n) (w : F))
    simp [restrictEndomorphism_pow_coe]

theorem cayley_hamilton_annihilation (b : F →ₗ[ℂ] F) (W : Submodule ℂ F)
    [FiniteDimensional ℂ W]
    (hb : ∀ w ∈ W, b w ∈ W) (v : F) (hv : v ∈ W) :
    ∃ P : Polynomial ℂ, P ≠ 0 ∧ ((Polynomial.aeval b) P) v = 0 := by
  set b_W := restrictEndomorphism b W hb
  refine ⟨b_W.charpoly, ?_, ?_⟩
  ·
    exact ne_of_apply_ne Polynomial.leadingCoeff
      (by simp [b_W.charpoly_monic.leadingCoeff])
  ·
    have hCH := LinearMap.aeval_self_charpoly b_W

    have h0 : (((Polynomial.aeval b_W b_W.charpoly) ⟨v, hv⟩ : W) : F) = 0 := by
      simp [hCH]

    rwa [aeval_restrictEndomorphism_coe] at h0

theorem exists_elliptic_annihilating_matrix_coeff
    [FiniteDimensional ℝ E] [SecondCountableTopology G]
    [CompleteSpace F] [IsTopologicalGroup G] [Nontrivial F]
    (π : ContinuousRep G F) (K : Subgroup G)
    (hG_ss : IsSemisimpleLieGroup I G)
    [CompactSpace K] [T2Space K]

    (hK_max : IsMaximalCompactSubgroup K)
    (hadm : @ContinuousRep.IsAdmissible.{_, uFsec, uFsec} _ _ _ _ _ _ _ _ π K)
    (v : F) (hv : v ∈ π.kFiniteSubspace K)
    (h : F →L[ℂ] ℂ) :
    ∃ D : (G → ℝ) →ₗ[ℝ] (G → ℝ),
      IsEllipticWithAnalyticCoeffs I D ∧
      ContMDiff I 𝓘(ℝ, ℝ) ↑(⊤ : ℕ∞)
        (fun g : G => (h (π.toMonoidHom g v)).re) ∧
      (∀ x : G, D (fun g : G => (h (π.toMonoidHom g v)).re) x = 0) := by

  set W := Submodule.span ℂ (Set.range (fun k : K => (π.toMonoidHom k) v))
  have hv_mem : v ∈ W := Submodule.subset_span ⟨⟨1, Subgroup.one_mem K⟩, by simp⟩
  have hW_fd : FiniteDimensional ℂ W := hv


  have infrastructure : ∃ b : F →ₗ[ℂ] F,
      (∀ w ∈ W, b w ∈ W) ∧
      (∀ P : Polynomial ℂ, P ≠ 0 → ((Polynomial.aeval b) P) v = 0 →
        ∃ D : (G → ℝ) →ₗ[ℝ] (G → ℝ),
          IsEllipticWithAnalyticCoeffs I D ∧
          ContMDiff I 𝓘(ℝ, ℝ) ↑(⊤ : ℕ∞)
            (fun g : G => (h (π.toMonoidHom g v)).re) ∧
          (∀ x : G, D (fun g : G => (h (π.toMonoidHom g v)).re) x = 0)) := by

    obtain ⟨b, _, hb_pres⟩ := exists_kInvariant_laplacian_endomorphism I π K hG_ss hK_max v hv
    refine ⟨b, hb_pres, ?_⟩

    intro P hP hPv

    obtain ⟨D, hD_ell, hD_compat⟩ := laplacian_polynomial_is_elliptic_with_analytic_coeffs I π K hG_ss hK_max b P hP
    refine ⟨D, hD_ell, ?_, ?_⟩

    · exact matrix_coeff_smooth_kfinite I π K hadm v hv h

    · exact laplacian_annihilates_matrix_coeff I π K hG_ss hK_max b v h P hPv D hD_compat


  obtain ⟨b, hb_pres, hb_annihilates⟩ := infrastructure

  obtain ⟨P, hP_ne, hP_annihil⟩ := cayley_hamilton_annihilation b W hb_pres v hv_mem

  exact hb_annihilates P hP_ne hP_annihil

theorem harish_chandra_analyticity
    [FiniteDimensional ℝ E] [SecondCountableTopology G]
    [CompleteSpace F] [IsTopologicalGroup G]
    (π : ContinuousRep G F) (K : Subgroup G)
    (hG_ss : IsSemisimpleLieGroup I G)
    [CompactSpace K] [T2Space K]

    (hK_max : IsMaximalCompactSubgroup K)
    (hadm : @ContinuousRep.IsAdmissible.{_, uFsec, uFsec} _ _ _ _ _ _ _ _ π K)
    (v : F) (hv : v ∈ π.kFiniteSubspace K) :
    π.IsWeaklyAnalyticVector I v := by

  cases subsingleton_or_nontrivial F with
  | inl _ =>


    intro h g₀
    have hv0 : v = 0 := Subsingleton.elim v 0
    refine ⟨Set.univ, Filter.univ_mem, ?_⟩
    have : (fun e : E => (h ((π.toMonoidHom ((chartAt H g₀).symm (I.symm e))) v)).re) =
        fun _ => 0 := by
      ext e
      simp only [hv0, map_zero, Complex.zero_re]
    rw [this]
    exact analyticOnNhd_const
  | inr _ =>
    intro h g₀

    obtain ⟨D, hD_ell, hf_smooth, hD_sol⟩ :=
      exists_elliptic_annihilating_matrix_coeff I π K hG_ss hK_max hadm v hv h

    exact elliptic_regularity_manifold I D hD_ell _ hf_smooth hD_sol g₀

theorem theorem_6_3_harish_chandra_analyticity
    [FiniteDimensional ℝ E] [SecondCountableTopology G]
    [CompleteSpace F] [IsTopologicalGroup G]
    (π : ContinuousRep G F) (K : Subgroup G)
    (hG_ss : IsSemisimpleLieGroup I G)
    [CompactSpace K] [T2Space K]
    (hK_max : IsMaximalCompactSubgroup K)
    (hadm : @ContinuousRep.IsAdmissible.{_, uFsec, uFsec} _ _ _ _ _ _ _ _ π K)

    (v : F) (hv : v ∈ π.kFiniteSubspace K) :
    π.IsWeaklyAnalyticVector I v :=
  harish_chandra_analyticity I π K hG_ss hK_max hadm v hv

end WeaklyAnalytic

end ContinuousRep

end
